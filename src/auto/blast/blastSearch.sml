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

fun hasSkolem (Skolem _) = true
  | hasSkolem (Abs (_, body)) = hasSkolem body
  | hasSkolem (left $ right) =
      hasSkolem left orelse hasSkolem right
  | hasSkolem _ = false

fun joinMd _ [] = []
  | joinMd md (formula :: formulas) =
      (formula, hasSkolem formula orelse md) :: joinMd md formulas

fun initBranch (formulas, lim) =
  {pairs = [(map (fn formula => (formula, true)) formulas, [])],
   lits = [],
   vars = add_terms_vars (formulas, []),
   lim = lim}

fun sameVars ([], []) = true
  | sameVars (left :: lefts, right :: rights) =
      left = right andalso sameVars (lefts, rights)
  | sameVars _ = false

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

fun requeueGamma (formula, md) remaining duplicate =
  if duplicate then remaining @ [(negOfGoal formula, md)]
  else remaining

fun killsAllAlternatives limit prems =
  limit < 0 andalso not (null prems)

fun mayUndo {other_rules, updated, old_vars, new_vars} =
  other_rules orelse updated orelse sameVars (old_vars, new_vars)

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

fun foldPremVars prems vars =
  List.foldr
    (fn (premise, accumulated) =>
       add_terms_vars (premise, accumulated))
    vars prems

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

fun runTerms debug claset depth formulas cont =
  let
    val state = newState ()
    val closed = ref 0
    val created = ref 1
    val pruned = ref 0
    val fullTrace = ref ([] : branch list list)

    fun proofOf (tacs, trace) =
      {script = rev tacs,
       trace = rev trace,
       depth = depth,
       branches_created = !created,
       branches_closed = !closed,
       choices_pruned = !pruned}

    fun prv (tacs, trace, choices, brs) =
      let
        val _ = if debug then fullTrace := brs :: !fullTrace else ()
        val _ = traceState depth brs
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
              val branches = length brs0
              val next_vars = remainingVars brs
              val formula = norm formula
              val cache = blastRule.newCache ()
              val rules =
                blastRule.safeRules cache claset vars formula

              fun newBranches (vars', lim') prems =
                map
                  (fn premise =>
                     if List.exists isGoal premise then
                       {pairs =
                          (joinMd md premise, []) ::
                          negOfGoals ((safe, unsafe) :: pairs),
                        lits = map negOfGoal lits,
                        vars = vars', lim = lim'}
                     else
                       {pairs =
                          (joinMd md premise, []) ::
                          (safe, unsafe) :: pairs,
                        lits = lits, vars = vars', lim = lim'})
                  prems @ brs

              fun deeper [] = raise NEWBRANCHES
                | deeper ((rule : tableau_rule) :: other) =
                    let
                      val pattern = #pattern rule
                      val prems = #premises rule
                      val rule_vars = add_term_vars (pattern, [])
                    in
                      if not (unify state
                                (rule_vars, pattern, formula)) then
                        deeper other
                      else
                        let
                          val updated = mark < trailSize state
                          val lim' =
                            if updated then
                              lim - instantiationPenalty (length rules)
                            else lim
                          val vars0 = vars_in_vars vars
                          val vars' = foldPremVars prems vars0
                          val choices' =
                            Choice (mark, branches, PRV) :: choices
                          val tacs' =
                            SafeRule {rule = rule, updated = updated} ::
                            tacs

                          fun descend () =
                            if null prems then
                              (closed := !closed + 1;
                               prv
                                 (tacs', brs0 :: trace,
                                  prune state pruned
                                    (branches, next_vars, choices'),
                                  brs))
                            else if lim' < 0 then
                              (clearTo state mark;
                               raise NEWBRANCHES)
                            else
                              (created :=
                                 !created + length prems - 1;
                               prv
                                 (tacs', brs0 :: trace, choices',
                                  newBranches (vars', lim') prems))
                        in
                          descend ()
                          handle PRV =>
                            if updated then
                              (clearTo state mark; deeper other)
                            else backtrack choices
                        end
                    end

              fun closeF [] = raise CLOSEF
                | closeF (literal :: literals) =
                    (case tryClose state (formula, literal) of
                         NONE => closeF literals
                       | SOME step =>
                           let
                             val choices' =
                               prune state pruned
                                 (branches, next_vars,
                                  Choice (mark, branches, PRV) ::
                                  choices)
                           in
                             closed := !closed + 1;
                             (prv
                                (step :: tacs, brs0 :: trace,
                                 choices', brs)
                              handle PRV =>
                                (clearTo state mark;
                                 closeF literals))
                           end)

              fun closeLevels [] = raise CLOSEF
                | closeLevels ((safe, unsafe) :: rest) =
                    (closeF (map first safe)
                     handle CLOSEF =>
                       (closeF (map first unsafe)
                        handle CLOSEF => closeLevels rest))

              fun cascade () =
                if lim < 0 then backtrack choices
                else
                  (prv
                     (HypSubst :: tacs, brs0 :: trace, choices,
                      equalSubst
                        (formula,
                         {pairs = (safe, unsafe) :: pairs,
                          lits = lits, vars = vars, lim = lim}) ::
                      brs)
                   handle DEST_EQ =>
                     (closeF lits
                      handle CLOSEF =>
                        (closeLevels ((safe, unsafe) :: pairs)
                         handle CLOSEF => deeper rules)))
            in
              cascade ()
              handle NEWBRANCHES =>
                (case blastRule.unsafeRules
                        cache claset vars formula of
                     [] =>
                       prv
                         (tacs, brs0 :: trace, choices,
                          {pairs = (safe, unsafe) :: pairs,
                           lits = addLit (formula, lits),
                           vars = vars, lim = lim} :: brs)
                   | _ =>
                       prv
                         ((if isGoal formula then DeferGoal :: tacs
                           else tacs),
                          brs0 :: trace, choices,
                          {pairs =
                             (safe,
                              unsafe @ [(negOfGoal formula, md)]) ::
                             pairs,
                           lits = lits, vars = vars, lim = lim} :: brs))
            end
        | ({pairs = ([], unsafe) :: (safe, unsafe') :: pairs,
            lits, vars, lim} : branch) :: brs =>
            prv
              (tacs, trace, choices,
               {pairs = (safe, unsafe @ unsafe') :: pairs,
                lits = lits, vars = vars, lim = lim} :: brs)
        | brs0 as
            ({pairs = [([], (formula, md) :: unsafe)],
              lits, vars, lim} : branch) :: brs =>
            let
              exception PRV
              val formula = norm formula
              val mark = trailSize state
              val cache = blastRule.newCache ()
              val rules =
                blastRule.unsafeRules cache claset vars formula

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

              fun deeper [] = raise NEWBRANCHES
                | deeper ((rule : tableau_rule) :: other) =
                    let
                      val pattern = #pattern rule
                      val prems = #premises rule
                      val rule_vars = add_term_vars (pattern, [])
                    in
                      if not (unify state
                                (rule_vars, pattern, formula)) then
                        deeper other
                      else
                        let
                          val updated = mark < trailSize state
                          val old_vars = vars_in_vars vars
                          val new_vars = foldPremVars prems old_vars
                          val duplicate = md
                          val lim' =
                            if updated then
                              lim - instantiationPenalty (length rules)
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
                              (clearTo state mark;
                               raise NEWBRANCHES)
                            else
                              (if null prems then
                                 closed := !closed + 1
                               else
                                 created :=
                                   !created + length prems - 1;
                               prv
                                 (step :: tacs, brs0 :: trace,
                                  Choice
                                    (mark, length brs0, PRV) ::
                                    choices,
                                  newBranches
                                    (new_vars, pattern, duplicate,
                                     lim') prems))
                        in
                          descend ()
                          handle PRV =>
                            if undo then
                              (clearTo state mark; deeper other)
                            else backtrack choices
                        end
                    end
            in
              if lim < 1 then backtrack choices
              else
                (deeper rules
                 handle NEWBRANCHES =>
                   prv
                     (tacs, brs0 :: trace, choices,
                      {pairs = [([], unsafe)],
                       lits = formula :: lits,
                       vars = vars, lim = lim} :: brs))
            end
        | _ :: _ => backtrack choices
      end

    val initial = initBranch (formulas, depth)
    val result =
      SOME
        (prv ([], [], [Choice (trailSize state, 1, PROVE)], [initial]))
      handle PROVE => NONE
  in
    {fullTrace = rev (!fullTrace), result = result}
  end

fun searchTerms claset depth formulas cont =
  #result (runTerms false claset depth formulas cont)

fun searchGoal claset depth goal cont =
  searchTerms claset depth
    (map first (blastRule.initialBranch goal)) cont

fun tryGoal claset depth goal =
  searchGoal claset depth goal (fn proof => proof)

fun debugGoal claset depth goal =
  runTerms true claset depth
    (map first (blastRule.initialBranch goal)) (fn proof => proof)

(* There is deliberately no timeout.  A future extension may poll a counter
   at prv entry, but the faithful engine is bounded only by deepening. *)
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
