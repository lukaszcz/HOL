structure blastSearch :> blastSearch =
struct

(* Faithful search port from Isabelle src/Provers/blast.ML.
   Branches and initialization map lines 93--99 and 1179--1184.
   Equality maps lines 692--790; closers map lines 797--815.
   Child md flags map lines 817--826.  Backtracking and pruning map
   lines 829--874; addLit maps lines 876--894; the penalty and recursive
   check map lines 897--915.

   The five prv clauses map lines 938--940, 941--1064, 1065--1072,
   1073--1174, and 1175--1176.  Within clause 2, safe expansion maps
   lines 953--1006, closing maps lines 1008--1031, and the committed
   equality/close/safe/defer cascade maps lines 1032--1063.  Clause 3's
   level merge maps lines 1065--1072.  Clause 4's children, gamma
   requeue, recursive-level sharing, penalty, mayUndo, and kill-all map
   lines 1082--1160; its literal fallback maps lines 1167--1173.
   Replay-failure re-entry maps lines 1254--1277.  deepenGoal maps the
   DEEPEN call at lines 1284--1292.
*)

open blastTerm

infix 9 $

type pterm = blastTerm.term
type var = blastTerm.var
type goal = Abbrev.goal
type claset = clasetLib.claset
type tableau_rule = blastRule.tableau_rule

type level =
  (pterm * bool) list * (pterm * bool) list

type branch =
  {pairs : level list,
   lits : pterm list,
   vars : var list,
   lim : int}

datatype script_step =
    HypSubst
  | CloseAssume
  | CloseContradiction
  | SafeRule of {rule : tableau_rule, updated : bool}
  | DeferGoal
  | UnsafeRule of
      {rule : tableau_rule, updated : bool, duplicate : bool}

type script = script_step list

type proof =
  {script : script,
   trace : branch list list,
   depth : int,
   branches_created : int,
   branches_closed : int,
   choices_pruned : int}

type statistics =
  {configured_depth : int,
   maximum_resource_cost : int,
   inferences_performed : int,
   branches_created : int,
   branches_closed : int,
   choices_pruned : int,
   rule_cache_hits : int,
   rule_conversions : int,
   emergency_cleanup_assignments : int,
   remaining_trail_assignments : int,
   cooperative_checkpoints : int,
   candidate_rules_enumerated : int,
   candidate_conversions_attempted : int,
   safe_rule_attempts : int,
   unsafe_rule_attempts : int,
   rule_unification_attempts : int,
   rule_unification_successes : int,
   equality_substitution_attempts : int,
   equality_substitution_successes : int,
   literal_close_attempts : int,
   literal_close_successes : int}

datatype completion = Completed | Interrupted

type 'a measured_result =
  {completion : completion,
   fullTrace : branch list list,
   result : 'a option,
   statistics : statistics}

type debug_result =
  {fullTrace : branch list list,
   result : proof option}

val depth_limit = ref 20

exception PROOF_FAILED
exception PROVE
exception DEST_EQ
exception NEWBRANCHES
exception CLOSEF

datatype choice = Choice of int * int * exn

val not_name = const_name {Thy = "bool", Name = "~"}
val equality_name = const_name {Thy = "min", Name = "="}

fun first (left, _) = left

fun negate formula = Const (not_name, []) $ formula

fun isNot (Const (name, _) $ _) = name = not_name
  | isNot _ = false

fun negOfGoal formula =
  if isGoal formula then negate (rand formula) else formula

fun negOfPair (formula, md) = (negOfGoal formula, md)

fun negOfGoals pairs =
  map (fn (safe, unsafe) => (map negOfPair safe, unsafe)) pairs

fun negOfGoalsMeasured checkpoint pairs =
  let
    fun negate_pairs [] = []
      | negate_pairs (pair :: rest) =
          (checkpoint (); negOfPair pair :: negate_pairs rest)
    fun negate_levels [] = []
      | negate_levels ((safe, unsafe) :: rest) =
          (checkpoint ();
           (negate_pairs safe, unsafe) :: negate_levels rest)
  in
    negate_levels pairs
  end

fun hasSkolem (Skolem _) = true
  | hasSkolem (Abs (_, body)) = hasSkolem body
  | hasSkolem (left $ right) =
      hasSkolem left orelse hasSkolem right
  | hasSkolem _ = false

fun joinMd _ [] = []
  | joinMd md (formula :: formulas) =
      (formula, hasSkolem formula orelse md) :: joinMd md formulas

fun joinMdMeasured checkpoint md formulas =
  let
    fun has term =
      (checkpoint ();
       case term of
           Skolem _ => true
         | Abs (_, body) => has body
         | left $ right => has left orelse has right
         | _ => false)
    fun join [] = []
      | join (formula :: rest) =
          (checkpoint ();
           (formula, has formula orelse md) :: join rest)
  in
    join formulas
  end

fun initBranch (formulas, lim) =
  {pairs = [(map (fn formula => (formula, true)) formulas, [])],
   lits = [],
   vars = add_terms_vars (formulas, []),
   lim = lim}

fun initBranchMeasured checkpoint (formulas, lim) =
  let
    fun pairs [] = []
      | pairs (formula :: rest) =
          (checkpoint (); (formula, true) :: pairs rest)
    val vars = add_terms_vars_measured checkpoint (formulas, [])
  in
    {pairs = [(pairs formulas, [])], lits = [], vars = vars, lim = lim}
  end

fun appendMeasured checkpoint [] right = right
  | appendMeasured checkpoint (item :: items) right =
      (checkpoint (); item :: appendMeasured checkpoint items right)

fun lengthMeasured checkpoint values =
  let
    fun count [] n = n
      | count (_ :: rest) n =
          (checkpoint (); count rest (n + 1))
  in
    count values 0
  end

fun mapFirstMeasured checkpoint values =
  let
    fun project [] = []
      | project (pair :: rest) =
          (checkpoint (); first pair :: project rest)
  in
    project values
  end

fun sameVars ([], []) = true
  | sameVars (left :: lefts, right :: rights) =
      left = right andalso sameVars (lefts, rights)
  | sameVars _ = false

fun sameVarsMeasured checkpoint ([], []) = true
  | sameVarsMeasured checkpoint (left :: lefts, right :: rights) =
      (checkpoint ();
       left = right andalso
       sameVarsMeasured checkpoint (lefts, rights))
  | sameVarsMeasured checkpoint _ = false

fun log4 n = if n < 4 then 0 else 1 + log4 (n div 4)

fun instantiationPenalty n = 1 + log4 n

fun match (Var _) _ = true
  | match (Const (a, ats)) (Const (b, bts)) =
      (a = goal_name andalso b = not_name) orelse
      (a = not_name andalso b = goal_name) orelse
      (a = b andalso matchs (ats, bts))
  | match (Free a) (Free b) = a = b
  | match (Bound i) (Bound j) = i = j
  | match (Abs (_, left)) (Abs (_, right)) = match left right
  | match (f $ x) (g $ y) = match f g andalso match x y
  | match _ _ = false

and matchs ([], []) = true
  | matchs (left :: lefts, right :: rights) =
      match left right andalso matchs (lefts, rights)
  | matchs _ = false

fun recursivePremise pattern premise =
  List.exists (fn formula => match pattern formula) premise

fun recursivePremiseMeasured checkpoint pattern premise =
  let
    fun matches (Var _) _ = (checkpoint (); true)
      | matches (Const (a, ats)) (Const (b, bts)) =
          (checkpoint ();
           (a = goal_name andalso b = not_name) orelse
           (a = not_name andalso b = goal_name) orelse
           (a = b andalso match_lists (ats, bts)))
      | matches (Free a) (Free b) = (checkpoint (); a = b)
      | matches (Bound i) (Bound j) = (checkpoint (); i = j)
      | matches (Abs (_, left)) (Abs (_, right)) =
          (checkpoint (); matches left right)
      | matches (f $ x) (g $ y) =
          (checkpoint (); matches f g andalso matches x y)
      | matches _ _ = (checkpoint (); false)
    and match_lists ([], []) = true
      | match_lists (left :: lefts, right :: rights) =
          (checkpoint ();
           matches left right andalso match_lists (lefts, rights))
      | match_lists _ = false
    fun any [] = false
      | any (formula :: rest) =
          (checkpoint ();
           matches pattern formula orelse any rest)
  in
    any premise
  end

fun requeueGamma (formula, md) remaining duplicate =
  if duplicate then remaining @ [(negOfGoal formula, md)]
  else remaining

fun requeueGammaMeasured checkpoint (formula, md) remaining duplicate =
  if not duplicate then remaining
  else
    let
      fun append [] = [(negOfGoal formula, md)]
        | append (item :: items) =
            (checkpoint (); item :: append items)
    in
      append remaining
    end

fun killsAllAlternatives limit prems =
  limit < 0 andalso not (null prems)

fun mayUndo {other_rules, updated, old_vars, new_vars} =
  other_rules orelse updated orelse sameVars (old_vars, new_vars)

fun mayUndoMeasured checkpoint
      {other_rules, updated, old_vars, new_vars} =
  other_rules orelse updated orelse
  sameVarsMeasured checkpoint (old_vars, new_vars)

(* The trail is newest first.  As in blast.ML:831--838, assignments in
   instantiations of next_vars count as clashes too. *)
fun clashVar [] _ = false
  | clashVar vars (n, trail) =
      let
        fun clash (0, _) = false
          | clash (_, []) = false
          | clash (left, variable :: variables) =
              List.exists
                (fn next => varOccur variable (Var next)) vars orelse
              clash (left - 1, variables)
      in
        clash (n, trail)
      end

fun drop (0, values) = values
  | drop (_, []) = []
  | drop (n, _ :: values) = drop (n - 1, values)

(* Pure projection of prune, exported so its clash/no-clash boundary can be
   regression-tested without manufacturing exception values. *)
fun prunePlan
      {branches, next_vars, trail_mark, trail, choices} =
  if branches = 1 then choices
  else
    let
      fun scan (last, _, _, []) = last
        | scan (last, mark, current, (oldmark, oldbrs) :: older) =
            if oldbrs < branches then last
            else if oldbrs > branches then
              scan (last, mark, current, older)
            else if clashVar next_vars (mark - oldmark, current) then
              last
            else
              scan (older, oldmark,
                    drop (mark - oldmark, current), older)
    in
      scan (choices, trail_mark, trail, choices)
    end

fun choiceMark (Choice (mark, branches, _)) = (mark, branches)

fun prune state pruned (branches, next_vars, choices) =
  if branches = 1 then choices
  else
    let
      val marks = map choiceMark choices
      val remaining =
        prunePlan
          {branches = branches,
           next_vars = next_vars,
           trail_mark = trailSize state,
           trail = trailVars state,
           choices = marks}
      val removed = length choices - length remaining
      val _ = pruned := !pruned + removed
    in
      drop (removed, choices)
    end

fun pruneMeasured checkpoint state pruned
      (branches, next_vars, choices) =
  if branches = 1 then choices
  else
    let
      fun occurs_in _ [] = false
        | occurs_in variable (next :: rest) =
            (checkpoint ();
             varOccurMeasured checkpoint variable (Var next) orelse
             occurs_in variable rest)
      fun clash _ (0, _) = false
        | clash _ (_, []) = false
        | clash vars (left, variable :: variables) =
            (checkpoint ();
             occurs_in variable vars orelse
             clash vars (left - 1, variables))
      fun drop_m (0, values) = values
        | drop_m (_, []) = []
        | drop_m (n, _ :: values) =
            (checkpoint (); drop_m (n - 1, values))
      fun marks [] = []
        | marks (choice :: rest) =
            (checkpoint (); choiceMark choice :: marks rest)
      fun scan (last, _, _, []) = last
        | scan (last, mark, current, (oldmark, oldbrs) :: older) =
            (checkpoint ();
             if oldbrs < branches then last
             else if oldbrs > branches then
               scan (last, mark, current, older)
             else if clash next_vars (mark - oldmark, current) then last
             else
               scan (older, oldmark,
                     drop_m (mark - oldmark, current), older))
      val all_marks = marks choices
      val remaining =
        scan (all_marks, trailSize state, trailVars state, all_marks)
      val removed =
        lengthMeasured checkpoint choices -
        lengthMeasured checkpoint remaining
      val _ = pruned := !pruned + removed
    in
      drop_m (removed, choices)
    end

fun nextVars ({vars, ...} : branch) = vars

fun remainingVars [] = []
  | remainingVars (branch :: _) = nextVars branch

fun backtrack [] = raise PROVE
  | backtrack (Choice (_, _, jump) :: _) = raise jump

fun addLit (Const (name, args) $ formula, lits) =
      if name <> goal_name then
        ins_term (Const (name, args) $ formula, lits)
      else
        let
          fun bad (Const (head, _) $ other) =
                head = goal_name orelse
                (head = not_name andalso aconv (formula, other))
            | bad _ = false
          fun change [] = []
            | change (lit :: rest) =
                (case lit of
                     Const (head, _) $ other =>
                       if head = goal_name orelse head = not_name then
                         if aconv (formula, other) then change rest
                         else negate other :: change rest
                       else lit :: change rest
                   | _ => lit :: change rest)
          val rest =
            if List.exists bad lits then change lits else lits
        in
          Const (goal_name, args) $ formula :: rest
        end
  | addLit (formula, lits) = ins_term (formula, lits)

fun addLitMeasured checkpoint (original, lits) =
  let
    fun ins term =
      let
        fun member [] = false
          | member (other :: rest) =
              (checkpoint ();
               aconvMeasured checkpoint (term, other) orelse member rest)
      in
        if member lits then lits else term :: lits
      end
  in
    case original of
        Const (name, args) $ formula =>
          if name <> goal_name then ins original
          else
            let
              fun bad (Const (head, _) $ other) =
                    head = goal_name orelse
                    (head = not_name andalso
                     aconvMeasured checkpoint (formula, other))
                | bad _ = false
              fun exists [] = false
                | exists (lit :: rest) =
                    (checkpoint (); bad lit orelse exists rest)
              fun change [] = []
                | change (lit :: rest) =
                    (checkpoint ();
                     case lit of
                         Const (head, _) $ other =>
                           if head = goal_name orelse head = not_name then
                             if aconvMeasured checkpoint
                                  (formula, other) then
                               change rest
                             else negate other :: change rest
                           else lit :: change rest
                       | _ => lit :: change rest)
              val rest = if exists lits then change lits else lits
            in
              Const (goal_name, args) $ formula :: rest
            end
      | formula => ins formula
  end

fun substAtomic (old, replacement) term =
  let
    fun subst (Var variable) =
          (case !variable of
               SOME value => subst value
             | NONE =>
                 if aconv (Var variable, old) then replacement
                 else Var variable)
      | subst (Abs (name, body)) = Abs (name, subst body)
      | subst (left $ right) = subst left $ subst right
      | subst value =
          if aconv (value, old) then replacement else value
  in
    subst term
  end

fun substAtomicMeasured checkpoint (old, replacement) term =
  let
    fun subst value =
      (checkpoint ();
       case value of
           Var variable =>
             (case !variable of
                  SOME assigned => subst assigned
                | NONE =>
                    if aconv (Var variable, old) then replacement
                    else Var variable)
         | Abs (name, body) => Abs (name, subst body)
         | left $ right => subst left $ subst right
         | _ => if aconv (value, old) then replacement else value)
  in
    subst term
  end

fun etaContractAtom original =
  case original of
      Abs (name, body) =>
        (case etaContract2 body of
             f $ Bound 0 =>
               if List.exists (fn i => i = 0) (loose_bnos f) then
                 original
               else etaContractAtom (incr_boundvars ~1 f)
           | _ => original)
    | _ => original

and etaContract2 (left $ right) =
      left $ etaContractAtom right
  | etaContract2 term = etaContractAtom term

fun substOccur target =
  let
    val allowed =
      case target of
          Skolem (_, variables) => variables
        | _ => []
    fun occursEqual value =
      aconv (target, value) orelse occurs value
    and occurs (Var variable) =
          (case !variable of
               SOME value => occursEqual value
             | NONE => not (mem_var (variable, allowed)))
      | occurs (Abs (_, body)) = occursEqual body
      | occurs (left $ right) =
          occursEqual right orelse occursEqual left
      | occurs _ = false
  in
    occursEqual
  end

fun destEq (Const (name, _) $ left $ right) =
      if name = equality_name then
        (etaContractAtom left, etaContractAtom right)
      else raise DEST_EQ
  | destEq _ = raise DEST_EQ

fun checked (old, replacement) =
  if substOccur old replacement then raise DEST_EQ
  else (old, replacement)

fun orientGoal (left, right) =
  case (left, right) of
      (Skolem _, _) => checked (left, right)
    | (_, Skolem _) => checked (right, left)
    | (Free _, _) => checked (left, right)
    | (_, Free _) => checked (right, left)
    | _ => raise DEST_EQ

fun orientGoalMeasured checkpoint (left0, right0) =
  let
    fun member_zero [] = false
      | member_zero (i :: rest) =
          (checkpoint (); i = 0 orelse member_zero rest)
    fun loose term =
      let
        fun insert value [] = [value]
          | insert value (item :: items) =
              (checkpoint ();
               if value = item then item :: items
               else item :: insert value items)
        fun add (Bound i, level, values) =
              (checkpoint ();
               if i < level then values
               else insert (i - level) values)
          | add (Abs (_, body), level, values) =
              (checkpoint (); add (body, level + 1, values))
          | add (f $ x, level, values) =
              (checkpoint ();
               add (f, level, add (x, level, values)))
          | add (_, _, values) = (checkpoint (); values)
      in
        add (term, 0, [])
      end
    fun decrement term =
      let
        fun dec level item =
          (checkpoint ();
           case item of
               Bound i => if i >= level then Bound (i - 1) else item
             | Abs (name, body) => Abs (name, dec (level + 1) body)
             | f $ x => dec level f $ dec level x
             | _ => item)
      in
        dec 0 term
      end
    fun contract original =
      (checkpoint ();
       case original of
           Abs (name, body) =>
             (case contract2 body of
                  f $ Bound 0 =>
                    if member_zero (loose f) then original
                    else contract (decrement f)
                | _ => original)
         | _ => original)
    and contract2 (left $ right) =
          (checkpoint (); left $ contract right)
      | contract2 term = (checkpoint (); contract term)

    fun occurs target =
      let
        val allowed =
          case target of Skolem (_, variables) => variables | _ => []
        fun member _ [] = false
          | member variable (item :: items) =
              (checkpoint ();
               variable = item orelse member variable items)
        fun equal value =
          aconvMeasured checkpoint (target, value) orelse visit value
        and visit value =
          (checkpoint ();
           case value of
               Var variable =>
                 (case !variable of
                      SOME assigned => equal assigned
                    | NONE => not (member variable allowed))
             | Abs (_, body) => equal body
             | left $ right => equal right orelse equal left
             | _ => false)
      in
        equal
      end

    fun checked_measured (old, replacement) =
      if occurs old replacement then raise DEST_EQ
      else (old, replacement)
    val left = contract left0
    val right = contract right0
  in
    case (left, right) of
        (Skolem _, _) => checked_measured (left, right)
      | (_, Skolem _) => checked_measured (right, left)
      | (Free _, _) => checked_measured (left, right)
      | (_, Free _) => checked_measured (right, left)
      | _ => raise DEST_EQ
  end

fun destEqMeasured checkpoint (Const (name, _) $ left $ right) =
      (checkpoint ();
       if name = equality_name then
         orientGoalMeasured checkpoint (left, right)
       else raise DEST_EQ)
  | destEqMeasured checkpoint _ = (checkpoint (); raise DEST_EQ)

fun equalSubst
      (formula,
       {pairs, lits, vars, lim} : branch) =
  let
    val (old, replacement) = orientGoal (destEq formula)
    val subst = substAtomic (old, replacement)
    fun subForm ((item, md), (changed, unchanged)) =
      let val result = subst item
      in
        if aconv (result, item) then
          (changed, (item, md) :: unchanged)
        else ((result, md) :: changed, unchanged)
      end
    fun subFrame ((safe, unsafe), (changed, frames)) =
      let
        val (changed', safe') =
          List.foldr subForm (changed, []) safe
        val (changed'', unsafe') =
          List.foldr subForm (changed', []) unsafe
      in
        (changed'', (safe', unsafe') :: frames)
      end
    fun subLit (lit, (changed, unchanged)) =
      let val result = subst lit
      in
        if aconv (result, lit) then
          (changed, result :: unchanged)
        else ((result, true) :: changed, unchanged)
      end
    val (changed, lits') = List.foldr subLit ([], []) lits
    val (changed', pairs') =
      List.foldr subFrame (changed, []) pairs
  in
    {pairs = (changed', []) :: pairs',
     lits = lits', vars = vars, lim = lim}
  end

fun equalSubstMeasured checkpoint
      (formula,
       {pairs, lits, vars, lim} : branch) =
  let
    val (old, replacement) = destEqMeasured checkpoint formula
    val subst = substAtomicMeasured checkpoint (old, replacement)
    fun subForm ((item, md), (changed, unchanged)) =
      let
        val _ = checkpoint ()
        val result = subst item
      in
        if aconvMeasured checkpoint (result, item) then
          (changed, (item, md) :: unchanged)
        else ((result, md) :: changed, unchanged)
      end
    fun subFrame ((safe, unsafe), (changed, frames)) =
      let
        val _ = checkpoint ()
        val (changed', safe') =
          List.foldr subForm (changed, []) safe
        val (changed'', unsafe') =
          List.foldr subForm (changed', []) unsafe
      in
        (changed'', (safe', unsafe') :: frames)
      end
    fun subLit (lit, (changed, unchanged)) =
      let
        val _ = checkpoint ()
        val result = subst lit
      in
        if aconvMeasured checkpoint (result, lit) then
          (changed, result :: unchanged)
        else ((result, true) :: changed, unchanged)
      end
    val (changed, lits') = List.foldr subLit ([], []) lits
    val (changed', pairs') =
      List.foldr subFrame (changed, []) pairs
    val _ = checkpoint ()
  in
    {pairs = (changed', []) :: pairs',
     lits = lits', vars = vars, lim = lim}
  end

fun tryClose state (formula, literal) =
  let
    fun close (left, right, step) =
      if unify state ([], left, right) then SOME step else NONE
  in
    if isGoal formula then
      close (rand formula, literal, CloseAssume)
    else if isGoal literal then
      close (formula, rand literal, CloseAssume)
    else if isNot formula then
      close (rand formula, literal, CloseContradiction)
    else if isNot literal then
      close (formula, rand literal, CloseContradiction)
    else NONE
  end

fun tryCloseMeasured cleanup checkpoint state (formula, literal) =
  let
    fun close (left, right, step) =
      if unifyMeasuredWith cleanup checkpoint state ([], left, right)
      then SOME step
      else NONE
  in
    if isGoal formula then
      close (rand formula, literal, CloseAssume)
    else if isGoal literal then
      close (formula, rand literal, CloseAssume)
    else if isNot formula then
      close (rand formula, literal, CloseContradiction)
    else if isNot literal then
      close (formula, rand literal, CloseContradiction)
    else NONE
  end

fun foldPremVars prems vars =
  List.foldr
    (fn (premise, accumulated) =>
       add_terms_vars (premise, accumulated))
    vars prems

fun foldPremVarsMeasured checkpoint prems vars =
  let
    fun fold [] accumulated = accumulated
      | fold (premise :: rest) accumulated =
          (checkpoint ();
           fold rest
             (add_terms_vars_measured checkpoint
                (premise, accumulated)))
  in
    fold (rev prems) vars
  end

fun termString term =
  case term of
      Const (name, []) => name
    | Const (name, args) =>
        name ^ "{" ^ String.concatWith "," (map termString args) ^ "}"
    | Skolem (name, variables) =>
        name ^ "[" ^ Int.toString (length variables) ^ "]"
    | Free name => name
    | Var variable =>
        (case !variable of
             SOME value => termString value
           | NONE => "?")
    | Bound index => "B" ^ Int.toString index
    | Abs (name, body) => "(\\" ^ name ^ ". " ^ termString body ^ ")"
    | left $ right =>
        "(" ^ termString left ^ " " ^ termString right ^ ")"

fun pairString (formula, md) =
  termString formula ^ (if md then "+" else "-")

fun levelString (safe, unsafe) =
  "S[" ^ String.concatWith ", " (map pairString safe) ^ "] U[" ^
  String.concatWith ", " (map pairString unsafe) ^ "]"

fun branchString ({pairs, lits, vars, lim} : branch) =
  "{lim=" ^ Int.toString lim ^ ", vars=" ^
  Int.toString (length vars) ^ ", lits=[" ^
  String.concatWith ", " (map termString lits) ^ "], levels=[" ^
  String.concatWith "; " (map levelString pairs) ^ "]}"

fun traceState depth branches =
  if Feedback.current_trace "blast" >= 3 then
    Feedback.HOL_MESG
      ("Blast trace at depth " ^ Int.toString depth ^ ":\n" ^
       String.concatWith "\n" (map branchString branches))
  else ()

datatype instrumentation =
    Off
  | Stats
  | On of {debug : bool, stop : unit -> bool}

type phase_statistics =
  {emergency_cleanup_assignments : int,
   cooperative_checkpoints : int,
   candidate_rules_enumerated : int,
   candidate_conversions_attempted : int,
   safe_rule_attempts : int,
   unsafe_rule_attempts : int,
   rule_unification_attempts : int,
   rule_unification_successes : int,
   equality_substitution_attempts : int,
   equality_substitution_successes : int,
   literal_close_attempts : int,
   literal_close_successes : int}

val zero_phase_statistics : phase_statistics =
  {emergency_cleanup_assignments = 0,
   cooperative_checkpoints = 0,
   candidate_rules_enumerated = 0,
   candidate_conversions_attempted = 0,
   safe_rule_attempts = 0,
   unsafe_rule_attempts = 0,
   rule_unification_attempts = 0,
   rule_unification_successes = 0,
   equality_substitution_attempts = 0,
   equality_substitution_successes = 0,
   literal_close_attempts = 0,
   literal_close_successes = 0}

type phase_monitor =
  {checkpoint : unit -> unit,
   checkpointRollback : int -> unit,
   cleanupException : exn -> blastTerm.state -> int -> unit,
   rule_monitor : blastRule.monitor,
   noteSafeRuleAttempt : unit -> unit,
   noteUnsafeRuleAttempt : unit -> unit,
   noteUnificationSuccess : unit -> unit,
   noteEqualityAttempt : unit -> unit,
   noteEqualitySuccess : unit -> unit,
   noteLiteralAttempt : unit -> unit,
   noteLiteralSuccess : unit -> unit}

datatype search_input =
    FormulaTerms of pterm list
  | GoalTerms of goal

datatype interruption_cleanup = Restore | AbandonOwned

fun runTerms cleanup_policy instrumentation claset depth input cont =
  let
    exception INTERRUPTED
    exception STOP_EXCEPTION of exn
    val state = newState ()
    val rule_cache = blastRule.newCache ()
    val closed = ref 0
    val created = ref 1
    val pruned = ref 0
    (* Phase counters and the monitor record exist only in the SOME arm.
       Off and Stats select only the ordinary inner workers below.  This does
       not claim that the shared reporting tuple itself allocates nothing. *)
    val (instrumentEntry, noteInference, noteRuleInference,
         phaseMonitor, instrumentationResult) =
      case instrumentation of
          Off =>
            (traceState depth, fn () => (), fn _ => (),
             NONE,
             fn () => (0, 0, [], zero_phase_statistics))
        | Stats =>
            let
              val inferences = ref 0
              val maximum_resource_cost = ref 0
              fun inference () = inferences := !inferences + 1
              fun ruleInference lim =
                (inferences := !inferences + 1;
                 maximum_resource_cost :=
                   Int.max (!maximum_resource_cost, depth - lim))
              fun result () =
                (!inferences, !maximum_resource_cost, [],
                 zero_phase_statistics)
            in
              (traceState depth, inference, ruleInference, NONE, result)
            end
        | On {debug, stop} =>
            let
              val inferences = ref 0
              val maximum_resource_cost = ref 0
              val fullTrace = ref ([] : branch list list)
              val checkpoints = ref 0
              val candidates = ref 0
              val conversions = ref 0
              val safe_attempts = ref 0
              val unsafe_attempts = ref 0
              val unify_attempts = ref 0
              val unify_successes = ref 0
              val equality_attempts = ref 0
              val equality_successes = ref 0
              val literal_attempts = ref 0
              val literal_successes = ref 0
              val emergency_cleanups = ref 0

              fun checkpoint () =
                let
                  val _ = checkpoints := !checkpoints + 1
                  val requested =
                    stop () handle exn => raise STOP_EXCEPTION exn
                in
                  if requested then raise INTERRUPTED else ()
                end

              fun entry brs =
                (checkpoint ();
                 if debug then
                    (fullTrace := brs :: !fullTrace;
                     traceState depth brs)
                 else traceState depth brs)
              fun inference () = inferences := !inferences + 1
              fun ruleInference lim =
                (inferences := !inferences + 1;
                 maximum_resource_cost :=
                   Int.max (!maximum_resource_cost, depth - lim))

              fun candidate () =
                candidates := !candidates + 1
              fun conversion () =
                conversions := !conversions + 1
              val rule_monitor : blastRule.monitor =
                {candidate = candidate, conversion = conversion,
                 checkpoint = checkpoint}

              fun ruleAttempt attempts () =
                (attempts := !attempts + 1;
                 unify_attempts := !unify_attempts + 1)
              fun unificationSuccess () =
                unify_successes := !unify_successes + 1
              fun equalityAttempt () =
                equality_attempts := !equality_attempts + 1
              fun equalitySuccess () =
                equality_successes := !equality_successes + 1
              fun literalAttempt () =
                literal_attempts := !literal_attempts + 1
              fun literalSuccess () =
                literal_successes := !literal_successes + 1

              fun emergencyCleanup () =
                emergency_cleanups := !emergency_cleanups + 1

              (* Only INTERRUPTED may abandon state, and only because the
                 goal entry point created every prototerm reachable from the
                 search.  Predicate and continuation exceptions restore. *)
              fun cleanupException exn cleanup_state mark =
                case exn of
                    INTERRUPTED =>
                      (case cleanup_policy of
                           Restore =>
                             clearToWith emergencyCleanup cleanup_state mark
                         | AbandonOwned => ())
                  | _ =>
                      clearToWith emergencyCleanup cleanup_state mark

              fun checkpointRollback mark =
                checkpoint ()
                handle exn =>
                  (cleanupException exn state mark; raise exn)

              fun phaseResult () : phase_statistics =
                {emergency_cleanup_assignments = !emergency_cleanups,
                 cooperative_checkpoints = !checkpoints,
                 candidate_rules_enumerated = !candidates,
                 candidate_conversions_attempted = !conversions,
                 safe_rule_attempts = !safe_attempts,
                 unsafe_rule_attempts = !unsafe_attempts,
                 rule_unification_attempts = !unify_attempts,
                 rule_unification_successes = !unify_successes,
                 equality_substitution_attempts = !equality_attempts,
                 equality_substitution_successes = !equality_successes,
                 literal_close_attempts = !literal_attempts,
                 literal_close_successes = !literal_successes}
              fun result () =
                (!inferences, !maximum_resource_cost,
                 if debug then rev (!fullTrace) else [], phaseResult ())
            in
              (entry, inference, ruleInference,
               SOME
                 {checkpoint = checkpoint,
                  checkpointRollback = checkpointRollback,
                  cleanupException = cleanupException,
                  rule_monitor = rule_monitor,
                  noteSafeRuleAttempt = ruleAttempt safe_attempts,
                  noteUnsafeRuleAttempt = ruleAttempt unsafe_attempts,
                  noteUnificationSuccess = unificationSuccess,
                  noteEqualityAttempt = equalityAttempt,
                  noteEqualitySuccess = equalitySuccess,
                  noteLiteralAttempt = literalAttempt,
                  noteLiteralSuccess = literalSuccess},
               result)
            end

    val prepared =
      SOME
        (case input of
             FormulaTerms terms => terms
           | GoalTerms goal =>
               (case phaseMonitor of
                    SOME monitor =>
                      let
                        val branch =
                          blastRule.initialBranchMeasured
                            (#checkpoint monitor) goal
                      in
                        mapFirstMeasured (#checkpoint monitor) branch
                      end
                  | NONE => map first (blastRule.initialBranch goal)))
      handle INTERRUPTED => NONE
           | STOP_EXCEPTION exn => raise exn

    fun proofOf (tacs, trace) =
      {script = rev tacs,
       trace = rev trace,
       depth = depth,
       branches_created = !created,
       branches_closed = !closed,
       choices_pruned = !pruned}

    fun prv (tacs, trace, choices, brs) =
      let
        val _ = instrumentEntry brs
      in
      case brs of
          [] =>
            ((cont (proofOf (tacs, trace)))
             handle PROOF_FAILED =>
               (if Feedback.current_trace "blast" >= 1 then
                  Feedback.HOL_MESG
                    ("PROOF FAILED for depth " ^ Int.toString depth)
                else ();
                backtrack choices))
        | brs0 as
            ({pairs = (((formula, md) :: safe, unsafe) :: pairs),
              lits, vars, lim} : branch) :: brs =>
            let
              exception PRV
              val mark = trailSize state
              val branches =
                (case phaseMonitor of
                     NONE => length brs0
                   | SOME monitor =>
                       lengthMeasured
                         (fn () => #checkpointRollback monitor mark)
                         brs0)
              val next_vars = remainingVars brs
              val formula =
                (case phaseMonitor of
                     SOME monitor =>
                       normMeasured
                         (fn () => #checkpointRollback monitor mark)
                         formula
                   | NONE => norm formula)
              val rules =
                (case phaseMonitor of
                     SOME monitor =>
                       blastRule.safeRulesMeasured
                         (#rule_monitor monitor)
                         rule_cache claset vars formula
                   | NONE =>
                       blastRule.safeRules rule_cache claset vars formula)
              val rule_count =
                (case phaseMonitor of
                     NONE => length rules
                   | SOME monitor =>
                       lengthMeasured
                         (fn () => #checkpointRollback monitor mark)
                         rules)

              fun newBranches (vars', lim') prems =
                map
                  (fn premise =>
                     (if List.exists isGoal premise then
                        {pairs =
                           (joinMd md premise, []) ::
                           negOfGoals ((safe, unsafe) :: pairs),
                         lits = map negOfGoal lits,
                         vars = vars', lim = lim'}
                      else
                        {pairs =
                           (joinMd md premise, []) ::
                           (safe, unsafe) :: pairs,
                         lits = lits, vars = vars', lim = lim'}))
                  prems @ brs

              fun deeperOrd [] = raise NEWBRANCHES
                | deeperOrd ((rule : tableau_rule) :: other) =
                    let
                      val pattern = #pattern rule
                      val prems = #premises rule
                      val rule_vars = add_term_vars (pattern, [])
                    in
                      if not (unify state (rule_vars, pattern, formula)) then
                        deeperOrd other
                      else
                        let
                          val updated = mark < trailSize state
                          val lim' =
                            if updated then
                              lim - instantiationPenalty rule_count
                            else lim
                          val vars0 = vars_in_vars vars
                          val vars' = foldPremVars prems vars0
                          val choices' =
                            Choice (mark, branches, PRV) :: choices
                          val tacs' =
                            SafeRule {rule = rule, updated = updated} :: tacs

                          fun descend () =
                            if null prems then
                              (closed := !closed + 1;
                               noteRuleInference lim';
                               prv
                                 (tacs', brs0 :: trace,
                                  prune state pruned
                                    (branches, next_vars, choices'),
                                  brs))
                            else if lim' < 0 then
                              (clearTo state mark; raise NEWBRANCHES)
                            else
                              (created := !created + length prems - 1;
                               noteRuleInference lim';
                               prv
                                 (tacs', brs0 :: trace, choices',
                                  newBranches (vars', lim') prems))
                        in
                          descend ()
                          handle PRV =>
                            if updated then
                              (clearTo state mark; deeperOrd other)
                            else backtrack choices
                        end
                    end

              fun closeFOrd [] = raise CLOSEF
                | closeFOrd (literal :: literals) =
                    (case tryClose state (formula, literal) of
                         NONE => closeFOrd literals
                       | SOME step =>
                           let
                             val choices' =
                               prune state pruned
                                 (branches, next_vars,
                                  Choice (mark, branches, PRV) :: choices)
                           in
                             closed := !closed + 1;
                             noteInference ();
                             (prv
                                (step :: tacs, brs0 :: trace,
                                 choices', brs)
                              handle PRV =>
                                (clearTo state mark;
                                 closeFOrd literals))
                           end)

              fun closeLevelsOrd [] = raise CLOSEF
                | closeLevelsOrd ((safe, unsafe) :: rest) =
                    (closeFOrd (map first safe)
                     handle CLOSEF =>
                       (closeFOrd (map first unsafe)
                        handle CLOSEF => closeLevelsOrd rest))

              fun cascadeOrd () =
                if lim < 0 then backtrack choices
                else
                  (let
                     val substituted =
                       equalSubst
                         (formula,
                          {pairs = (safe, unsafe) :: pairs,
                           lits = lits, vars = vars, lim = lim})
                     val _ = noteInference ()
                   in
                     prv
                       (HypSubst :: tacs, brs0 :: trace, choices,
                        substituted :: brs)
                   end
                   handle DEST_EQ =>
                     (closeFOrd lits
                      handle CLOSEF =>
                        (closeLevelsOrd ((safe, unsafe) :: pairs)
                         handle CLOSEF => deeperOrd rules)))

            in
              case phaseMonitor of
                  NONE =>
                    (cascadeOrd ()
                     handle NEWBRANCHES =>
                       (case blastRule.unsafeRules
                               rule_cache claset vars formula of
                            [] =>
                              prv
                                (tacs, brs0 :: trace, choices,
                                 {pairs = (safe, unsafe) :: pairs,
                                  lits = addLit (formula, lits),
                                  vars = vars, lim = lim} :: brs)
                          | _ =>
                              prv
                                ((if isGoal formula then
                                    DeferGoal :: tacs
                                  else tacs),
                                 brs0 :: trace, choices,
                                 {pairs =
                                    (safe,
                                     unsafe @
                                       [(negOfGoal formula, md)]) ::
                                    pairs,
                                  lits = lits, vars = vars,
                                  lim = lim} :: brs)))
                | SOME monitor =>
                    let
                      fun checkpoint () =
                        #checkpointRollback monitor mark

                      fun rollback () =
                        clearToMeasuredWith (#cleanupException monitor)
                          (#checkpoint monitor) state mark

                      fun newBranchesMeasured (vars', lim') prems =
                        let
                          fun contains_goal [] = false
                            | contains_goal (item :: items) =
                                (checkpoint ();
                                 isGoal item orelse contains_goal items)
                          fun map_checked _ [] = []
                            | map_checked f (item :: items) =
                                (checkpoint ();
                                 f item :: map_checked f items)
                          fun make [] = brs
                            | make (premise :: rest) =
                                let
                                  val _ = checkpoint ()
                                  val joined =
                                    joinMdMeasured checkpoint md premise
                                  val branch =
                                    if contains_goal premise then
                                      {pairs =
                                         (joined, []) ::
                                         negOfGoalsMeasured checkpoint
                                           ((safe, unsafe) :: pairs),
                                       lits =
                                         map_checked negOfGoal lits,
                                       vars = vars', lim = lim'}
                                    else
                                      {pairs =
                                         (joined, []) ::
                                         (safe, unsafe) :: pairs,
                                       lits = lits, vars = vars',
                                       lim = lim'}
                                in
                                  branch :: make rest
                                end
                        in
                          make prems
                        end

                      fun deeper [] = raise NEWBRANCHES
                        | deeper ((rule : tableau_rule) :: other) =
                            let
                              val _ = checkpoint ()
                              val pattern = #pattern rule
                              val prems = #premises rule
                              val rule_vars =
                                add_term_vars_measured checkpoint
                                  (pattern, [])
                              val _ = checkpoint ()
                              val _ = #noteSafeRuleAttempt monitor ()
                            in
                              if not
                                   (unifyMeasuredWith
                                      (#cleanupException monitor)
                                      checkpoint state
                                      (rule_vars, pattern, formula)) then
                                deeper other
                              else
                                let
                                  val _ =
                                    #noteUnificationSuccess monitor ()
                                  val _ = checkpoint ()
                                  val updated = mark < trailSize state
                                  val lim' =
                                    if updated then
                                      lim -
                                        instantiationPenalty rule_count
                                    else lim
                                  val vars0 =
                                    vars_in_vars_measured checkpoint vars
                                  val vars' =
                                    foldPremVarsMeasured checkpoint
                                      prems vars0
                                  val choices' =
                                    Choice (mark, branches, PRV) :: choices
                                  val tacs' =
                                    SafeRule
                                      {rule = rule, updated = updated} ::
                                    tacs

                                  fun descend () =
                                    if null prems then
                                      (closed := !closed + 1;
                                       noteRuleInference lim';
                                       prv
                                         (tacs', brs0 :: trace,
                                          pruneMeasured checkpoint state
                                            pruned
                                            (branches, next_vars,
                                             choices'),
                                          brs))
                                    else if lim' < 0 then
                                      (rollback (); raise NEWBRANCHES)
                                    else
                                      (created :=
                                         !created +
                                         lengthMeasured checkpoint prems -
                                         1;
                                       noteRuleInference lim';
                                       prv
                                         (tacs', brs0 :: trace, choices',
                                          newBranchesMeasured
                                            (vars', lim') prems))
                                in
                                  descend ()
                                  handle PRV =>
                                    if updated then
                                      (rollback (); deeper other)
                                    else backtrack choices
                                end
                            end

                      fun closeF [] = raise CLOSEF
                        | closeF (literal :: literals) =
                            let
                              val _ = checkpoint ()
                              val _ = #noteLiteralAttempt monitor ()
                            in
                              case tryCloseMeasured
                                     (#cleanupException monitor)
                                     checkpoint state
                                     (formula, literal) of
                                  NONE => closeF literals
                                | SOME step =>
                                    let
                                      val _ =
                                        #noteLiteralSuccess monitor ()
                                      val _ = checkpoint ()
                                      val choices' =
                                        pruneMeasured checkpoint state
                                          pruned
                                          (branches, next_vars,
                                           Choice
                                             (mark, branches, PRV) ::
                                           choices)
                                    in
                                      closed := !closed + 1;
                                      noteInference ();
                                      (prv
                                         (step :: tacs, brs0 :: trace,
                                          choices', brs)
                                       handle PRV =>
                                         (rollback (); closeF literals))
                                    end
                            end

                      fun closeLevels [] = raise CLOSEF
                        | closeLevels ((level_safe, level_unsafe) :: rest) =
                            (checkpoint ();
                             closeF
                               (mapFirstMeasured checkpoint level_safe)
                             handle CLOSEF =>
                               (closeF
                                  (mapFirstMeasured checkpoint
                                     level_unsafe)
                                handle CLOSEF => closeLevels rest))

                      fun cascade () =
                        if lim < 0 then backtrack choices
                        else
                          (let
                             val _ = checkpoint ()
                             val _ = #noteEqualityAttempt monitor ()
                             val substituted =
                               equalSubstMeasured checkpoint
                                 (formula,
                                  {pairs = (safe, unsafe) :: pairs,
                                   lits = lits, vars = vars,
                                   lim = lim})
                             val _ = #noteEqualitySuccess monitor ()
                             val _ = noteInference ()
                           in
                             prv
                               (HypSubst :: tacs, brs0 :: trace,
                                choices, substituted :: brs)
                           end
                           handle DEST_EQ =>
                             (closeF lits
                              handle CLOSEF =>
                                (closeLevels ((safe, unsafe) :: pairs)
                                 handle CLOSEF => deeper rules)))

                      fun fallback () =
                        case blastRule.unsafeRulesMeasured
                               (#rule_monitor monitor) rule_cache claset
                               vars formula of
                            [] =>
                              prv
                                (tacs, brs0 :: trace, choices,
                                 {pairs = (safe, unsafe) :: pairs,
                                  lits =
                                    addLitMeasured checkpoint
                                      (formula, lits),
                                  vars = vars, lim = lim} :: brs)
                          | _ =>
                              prv
                                ((if isGoal formula then
                                    DeferGoal :: tacs
                                  else tacs),
                                 brs0 :: trace, choices,
                                 {pairs =
                                    (safe,
                                     appendMeasured checkpoint unsafe
                                       [(negOfGoal formula, md)]) ::
                                    pairs,
                                  lits = lits, vars = vars,
                                  lim = lim} :: brs)
                    in
                      cascade () handle NEWBRANCHES => fallback ()
                    end
            end
        | ({pairs = ([], unsafe) :: (safe, unsafe') :: pairs,
            lits, vars, lim} : branch) :: brs =>
            let
              val merged =
                case phaseMonitor of
                    NONE => unsafe @ unsafe'
                  | SOME monitor =>
                      appendMeasured (#checkpoint monitor) unsafe unsafe'
            in
              prv
                (tacs, trace, choices,
                 {pairs = (safe, merged) :: pairs,
                  lits = lits, vars = vars, lim = lim} :: brs)
            end
        | brs0 as
            ({pairs = [([], (formula, md) :: unsafe)],
              lits, vars, lim} : branch) :: brs =>
            let
              exception PRV
              val mark = trailSize state
              val formula =
                (case phaseMonitor of
                     SOME monitor =>
                       normMeasured
                         (fn () => #checkpointRollback monitor mark)
                         formula
                   | NONE => norm formula)
              val rules =
                (case phaseMonitor of
                     SOME monitor =>
                       blastRule.unsafeRulesMeasured
                         (#rule_monitor monitor)
                         rule_cache claset vars formula
                   | NONE =>
                       blastRule.unsafeRules rule_cache claset vars formula)
              val rule_count =
                (case phaseMonitor of
                     NONE => length rules
                   | SOME monitor =>
                       lengthMeasured
                         (fn () => #checkpointRollback monitor mark)
                         rules)
              val branches =
                (case phaseMonitor of
                     NONE => length brs0
                   | SOME monitor =>
                       lengthMeasured
                         (fn () => #checkpointRollback monitor mark)
                         brs0)

              fun newPremise
                    (vars', pattern, duplicate, lim') premise =
                let
                  val safe = map (fn item => (item, false)) premise
                  val unsafe' =
                    requeueGamma (formula, md) unsafe duplicate
                  val lits' =
                    if List.exists isGoal premise then
                      map negOfGoal lits
                    else lits
                  val pairs =
                    if recursivePremise pattern premise then
                      [(safe, unsafe')]
                    else [(safe, []), ([], unsafe')]
                in
                  {pairs = pairs, lits = lits',
                   vars = vars', lim = lim'}
                end

              fun newBranches arguments prems =
                map (newPremise arguments) prems @ brs

              fun deeperOrd [] = raise NEWBRANCHES
                | deeperOrd ((rule : tableau_rule) :: other) =
                    let
                      val pattern = #pattern rule
                      val prems = #premises rule
                      val rule_vars = add_term_vars (pattern, [])
                    in
                      if not (unify state (rule_vars, pattern, formula)) then
                        deeperOrd other
                      else
                        let
                          val updated = mark < trailSize state
                          val old_vars = vars_in_vars vars
                          val new_vars = foldPremVars prems old_vars
                          val duplicate = md
                          val lim' =
                            if updated then
                              lim - instantiationPenalty rule_count
                            else lim - 1
                          val undo =
                            mayUndo
                              {other_rules = not (null other),
                               updated = updated,
                               old_vars = old_vars,
                               new_vars = new_vars}
                          val step =
                            UnsafeRule
                              {rule = rule, updated = updated,
                               duplicate = duplicate}

                          fun descend () =
                            if killsAllAlternatives lim' prems then
                              (clearTo state mark; raise NEWBRANCHES)
                            else
                              (if null prems then
                                 closed := !closed + 1
                               else
                                 created := !created + length prems - 1;
                               noteRuleInference lim';
                               prv
                                 (step :: tacs, brs0 :: trace,
                                  Choice (mark, branches, PRV) :: choices,
                                  newBranches
                                    (new_vars, pattern, duplicate, lim')
                                    prems))
                        in
                          descend ()
                          handle PRV =>
                            if undo then
                              (clearTo state mark; deeperOrd other)
                            else backtrack choices
                        end
                    end

            in
              if lim < 1 then backtrack choices
              else
                (case phaseMonitor of
                     NONE =>
                       (deeperOrd rules
                        handle NEWBRANCHES =>
                          prv
                            (tacs, brs0 :: trace, choices,
                             {pairs = [([], unsafe)],
                              lits = formula :: lits,
                              vars = vars, lim = lim} :: brs))
                   | SOME monitor =>
                       let
                         fun checkpoint () =
                           #checkpointRollback monitor mark

                         fun rollback () =
                           clearToMeasuredWith (#cleanupException monitor)
                             (#checkpoint monitor) state mark

                         fun map_checked _ [] = []
                           | map_checked f (item :: items) =
                               (checkpoint ();
                                f item :: map_checked f items)
                         fun contains_goal [] = false
                           | contains_goal (item :: items) =
                               (checkpoint ();
                                isGoal item orelse contains_goal items)

                         fun newPremise
                               (vars', pattern, duplicate, lim') premise =
                           let
                             val _ = checkpoint ()
                             val safe' =
                               map_checked (fn item => (item, false))
                                 premise
                             val unsafe' =
                               requeueGammaMeasured checkpoint
                                 (formula, md) unsafe duplicate
                             val lits' =
                               if contains_goal premise then
                                 map_checked negOfGoal lits
                               else lits
                             val pairs' =
                               if recursivePremiseMeasured checkpoint
                                    pattern premise then
                                 [(safe', unsafe')]
                               else [(safe', []), ([], unsafe')]
                           in
                             {pairs = pairs', lits = lits',
                              vars = vars', lim = lim'}
                           end

                         fun newBranches arguments prems =
                           let
                             fun make [] = brs
                               | make (premise :: rest) =
                                   (checkpoint ();
                                    newPremise arguments premise ::
                                      make rest)
                           in
                             make prems
                           end

                         fun deeper [] = raise NEWBRANCHES
                           | deeper ((rule : tableau_rule) :: other) =
                               let
                                 val _ = checkpoint ()
                                 val pattern = #pattern rule
                                 val prems = #premises rule
                                 val rule_vars =
                                   add_term_vars_measured checkpoint
                                     (pattern, [])
                                 val _ = checkpoint ()
                                 val _ =
                                   #noteUnsafeRuleAttempt monitor ()
                               in
                                 if not
                                      (unifyMeasuredWith
                                         (#cleanupException monitor)
                                         checkpoint state
                                         (rule_vars, pattern, formula)) then
                                   deeper other
                                 else
                                   let
                                     val _ =
                                       #noteUnificationSuccess monitor ()
                                     val _ = checkpoint ()
                                     val updated = mark < trailSize state
                                     val old_vars =
                                       vars_in_vars_measured checkpoint
                                         vars
                                     val new_vars =
                                       foldPremVarsMeasured checkpoint
                                         prems old_vars
                                     val duplicate = md
                                     val lim' =
                                       if updated then
                                         lim -
                                           instantiationPenalty rule_count
                                       else lim - 1
                                     val undo =
                                       mayUndoMeasured checkpoint
                                         {other_rules = not (null other),
                                          updated = updated,
                                          old_vars = old_vars,
                                          new_vars = new_vars}
                                     val step =
                                       UnsafeRule
                                         {rule = rule,
                                          updated = updated,
                                          duplicate = duplicate}

                                     fun descend () =
                                       if killsAllAlternatives lim' prems
                                       then
                                         (rollback (); raise NEWBRANCHES)
                                       else
                                         (if null prems then
                                            closed := !closed + 1
                                          else
                                            created :=
                                              !created +
                                              lengthMeasured checkpoint
                                                prems - 1;
                                          noteRuleInference lim';
                                          prv
                                            (step :: tacs,
                                             brs0 :: trace,
                                             Choice
                                               (mark, branches, PRV) ::
                                               choices,
                                             newBranches
                                               (new_vars, pattern,
                                                duplicate, lim') prems))
                                   in
                                     descend ()
                                     handle PRV =>
                                       if undo then
                                         (rollback (); deeper other)
                                       else backtrack choices
                                   end
                               end
                       in
                         deeper rules
                         handle NEWBRANCHES =>
                           prv
                             (tacs, brs0 :: trace, choices,
                              {pairs = [([], unsafe)],
                               lits = formula :: lits,
                               vars = vars, lim = lim} :: brs)
                       end)
            end
        | _ :: _ => backtrack choices
      end

    val (completion, result) =
      case prepared of
          NONE => (Interrupted, NONE)
        | SOME formulas =>
            ((let
                val initial =
                  case phaseMonitor of
                      NONE => initBranch (formulas, depth)
                    | SOME monitor =>
                        initBranchMeasured (#checkpoint monitor)
                          (formulas, depth)
              in
                (Completed,
                 SOME
                   (prv
                      ([], [], [Choice (trailSize state, 1, PROVE)],
                       [initial])))
              end
              handle PROVE => (Completed, NONE)
                   | INTERRUPTED =>
                       (case phaseMonitor of
                            SOME monitor =>
                              #cleanupException monitor INTERRUPTED state 0
                          | NONE => ();
                        (Interrupted, NONE)))
             handle STOP_EXCEPTION exn =>
                      (case phaseMonitor of
                           SOME monitor =>
                             (#cleanupException monitor exn state 0;
                              raise exn)
                         | NONE => raise exn)
                  | exn =>
                      (case phaseMonitor of
                           SOME monitor =>
                             (#cleanupException monitor exn state 0;
                              raise exn)
                         | NONE => raise exn))
    val (inferences, maximum_resource_cost, fullTrace, phase) =
      instrumentationResult ()
    val statistics =
      {configured_depth = depth,
       maximum_resource_cost = maximum_resource_cost,
       inferences_performed = inferences,
       branches_created = !created,
       branches_closed = !closed,
       choices_pruned = !pruned,
       rule_cache_hits = blastRule.hitCount rule_cache,
       rule_conversions = blastRule.conversionCount rule_cache,
       emergency_cleanup_assignments =
         #emergency_cleanup_assignments phase,
       remaining_trail_assignments = trailSize state,
       cooperative_checkpoints = #cooperative_checkpoints phase,
       candidate_rules_enumerated = #candidate_rules_enumerated phase,
       candidate_conversions_attempted =
         #candidate_conversions_attempted phase,
       safe_rule_attempts = #safe_rule_attempts phase,
       unsafe_rule_attempts = #unsafe_rule_attempts phase,
       rule_unification_attempts = #rule_unification_attempts phase,
       rule_unification_successes = #rule_unification_successes phase,
       equality_substitution_attempts =
         #equality_substitution_attempts phase,
       equality_substitution_successes =
         #equality_substitution_successes phase,
       literal_close_attempts = #literal_close_attempts phase,
       literal_close_successes = #literal_close_successes phase}
  in
    {completion = completion, fullTrace = fullTrace, result = result,
     statistics = statistics}
  end

fun searchTerms claset depth formulas cont =
  #result
    (runTerms Restore Off claset depth (FormulaTerms formulas) cont)

fun searchTermsMeasured options claset depth formulas cont =
  runTerms Restore (On options) claset depth (FormulaTerms formulas) cont

fun goalTerms goal = map first (blastRule.initialBranch goal)

fun searchGoalMeasured options claset depth goal cont =
  runTerms AbandonOwned (On options) claset depth (GoalTerms goal) cont

fun searchGoalWithStats claset depth goal cont =
  let
    val report =
      runTerms Restore Stats claset depth (GoalTerms goal) cont
  in
    {result = #result report, statistics = #statistics report}
  end

fun searchGoal claset depth goal cont =
  #result (runTerms Restore Off claset depth (GoalTerms goal) cont)

fun tryGoal claset depth goal =
  searchGoal claset depth goal (fn proof => proof)

fun debugGoal claset depth goal =
  let
    val report =
      searchGoalMeasured {debug = true, stop = fn () => false}
        claset depth goal (fn proof => proof)
  in
    {fullTrace = #fullTrace report, result = #result report}
  end

(* This legacy iterative-deepening API has no cooperative timeout: each
   fixed-depth run is uninstrumented and is bounded only by its resource
   limit, while the sequence of runs is capped by depth_limit.  Callers that
   need cooperative interruption use the measured fixed-depth APIs. *)
fun deepenGoal claset goal cont =
  let
    val limit = !depth_limit
    fun deepen depth =
      if depth > limit then NONE
      else
        case searchGoal claset depth goal cont of
            NONE => deepen (depth + 1)
          | result => result
  in
    deepen 0
  end

end
