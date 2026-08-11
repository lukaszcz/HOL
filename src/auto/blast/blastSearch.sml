structure blastSearch :> blastSearch =
struct

(* Faithful search port from Isabelle src/Provers/blast.ML.
   Branches and initialization map lines 93--99 and 1179--1184.
   Equality maps lines 692--790; closers map lines 797--815.
   Child md flags map lines 817--826.  Backtracking and pruning map
   lines 829--874; addTrackedLit maps lines 876--894; the penalty and
   recursive check map lines 897--915.

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
    HypSubst of {equality : int, changed : bool list}
  | CloseAssume of {assumption : int}
  | CloseContradiction of {negative : int, positive : int}
  | SafeRule of
      {rule : tableau_rule, updated : bool, major : int option}
  | DeferGoal
  | UnsafeRule of
      {rule : tableau_rule, updated : bool, duplicate : bool,
       major : int option}

type script = script_step list

type proof =
  {script : script,
   trace : branch list list,
   depth : int,
   branches_created : int,
   branches_closed : int,
   choices_pruned : int}

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

type statistics =
  {configured_depth : int,
   maximum_resource_cost : int,
   inferences_performed : int,
   branches_created : int,
   branches_closed : int,
   choices_pruned : int,
   rule_cache_hits : int,
   rule_conversions : int,
   remaining_trail_assignments : int,
   phase : phase_statistics}

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

(* Assumption tokens are local to one [runTerms] invocation.  Search queues
   may rotate, partition, normalize and deduplicate formulae, so neither a
   queue position nor term equality identifies a typed assumption occurrence.
   Every queued formula therefore carries its occurrence token, while each
   internal branch separately carries the exact ordered model of the typed
   goal's assumptions.  Goal formulae have no token until DeferGoal performs
   ccontr.  Tokens are never exported: recorded script positions are resolved
   against the model at the committing transition. *)
type assumption_token = int
type assumption_model = (assumption_token * pterm) list

datatype tracked_formula =
  Tracked of {term : pterm, token : assumption_token option}

type tracked_level =
  (tracked_formula * bool) list * (tracked_formula * bool) list

type search_branch =
  {pairs : tracked_level list,
   lits : tracked_formula list,
   vars : var list,
   lim : int,
   assumptions : assumption_model}

fun trackedTerm (Tracked {term, ...}) = term
fun trackedToken (Tracked {token, ...}) = token

fun withTrackedTerm term (Tracked {token, ...}) =
  Tracked {term = term, token = token}

fun provenanceError function message =
  raise Fail ("blastSearch." ^ function ^ ": " ^ message)

fun tokenPosition function token assumptions =
  let
    fun find _ [] =
          provenanceError function
            "an assumption token is absent from the branch model"
      | find position ((current, _) :: rest) =
          if current = token then position else find (position + 1) rest
  in
    find 1 assumptions
  end

fun trackedPosition function formula assumptions =
  case trackedToken formula of
      NONE =>
        provenanceError function
          "an assumption formula has no provenance token"
    | SOME token => tokenPosition function token assumptions

fun deleteToken function token assumptions =
  let
    fun remove [] =
          provenanceError function
            "an eliminated assumption token is absent from the branch model"
      | remove ((entry as (current, _)) :: rest) =
          if current = token then rest else entry :: remove rest
  in
    remove assumptions
  end

fun lookupToken function token assumptions =
  case List.find (fn (current, _) => current = token) assumptions of
      SOME entry => entry
    | NONE =>
        provenanceError function
          "an assumption token is absent from the branch model"

fun projectPair (formula, md) = (trackedTerm formula, md)

fun projectBranch
      ({pairs, lits, vars, lim, ...} : search_branch) : branch =
  {pairs = map (fn (safe, unsafe) =>
                  (map projectPair safe, map projectPair unsafe)) pairs,
   lits = map trackedTerm lits, vars = vars, lim = lim}

fun projectBranches branches = map projectBranch branches

datatype choice = Choice of int * int * exn

val not_name = {Thy = "bool", Name = "~"}
val equality_name = {Thy = "min", Name = "="}

fun first (left, _) = left

fun negate formula = Const (not_name, []) $ formula

fun isNot (Const (name, _) $ _) = name = not_name
  | isNot _ = false

fun negOfGoal formula =
  if isGoal formula then negate (rand formula) else formula

fun negOfTracked formula =
  withTrackedTerm (negOfGoal (trackedTerm formula)) formula

fun negOfTrackedPair (formula, md) = (negOfTracked formula, md)

(* Every search worker below has one checkpoint-parameterized body.  The
   plain entry point instantiates it with a no-op callback, while the
   measured entry point passes the run's checkpoint. *)

fun negOfTrackedGoalsMeasured checkpoint pairs =
  let
    val negate_pairs = mapMeasured checkpoint negOfTrackedPair
    fun negate_level (safe, unsafe) = (negate_pairs safe, unsafe)
  in
    mapMeasured checkpoint negate_level pairs
  end

fun negOfTrackedGoals pairs =
  negOfTrackedGoalsMeasured (fn () => ()) pairs

fun joinTrackedMdMeasured checkpoint md formulas =
  let
    fun has term =
      (checkpoint ();
       case term of
           Skolem _ => true
         | Abs (_, body) => has body
         | left $ right => has left orelse has right
         | _ => false)
    fun join formula = (formula, has (trackedTerm formula) orelse md)
  in
    mapMeasured checkpoint join formulas
  end

fun joinTrackedMd md formulas =
  joinTrackedMdMeasured (fn () => ()) md formulas

fun initBranch (formulas, lim) =
  {pairs = [(map (fn formula => (formula, true)) formulas, [])],
   lits = [],
   vars = add_terms_vars (formulas, []),
   lim = lim}

fun initSearchBranchWith checkpoint addVars fresh (formulas, lim) :
      search_branch =
  let
    fun make [] = ([], [])
      | make (term :: rest) =
          let
            val _ = checkpoint ()
            val (tracked, assumptions) = make rest
          in
            if isGoal term then
              (Tracked {term = term, token = NONE} :: tracked,
               assumptions)
            else
              let val token = fresh ()
              in
                (Tracked {term = term, token = SOME token} :: tracked,
                 (token, term) :: assumptions)
              end
          end
    val (tracked, assumptions) = make formulas
    val vars = addVars (formulas, [])
  in
    {pairs = [(map (fn formula => (formula, true)) tracked, [])],
     lits = [], vars = vars, lim = lim, assumptions = assumptions}
  end

fun initSearchBranch fresh arguments =
  initSearchBranchWith (fn () => ()) add_terms_vars fresh arguments

fun initSearchBranchMeasured checkpoint fresh arguments =
  initSearchBranchWith checkpoint (add_terms_vars_measured checkpoint)
    fresh arguments

fun lengthMeasured checkpoint values =
  let
    fun count [] n = n
      | count (_ :: rest) n =
          (checkpoint (); count rest (n + 1))
  in
    count values 0
  end

fun mapFirstMeasured checkpoint values =
  mapMeasured checkpoint first values

fun trackPremise fresh premise =
  let
    fun track [] = ([], [])
      | track (term :: rest) =
          if isGoal term then
            let val (tracked, entries) = track rest
            in
              (Tracked {term = term, token = NONE} :: tracked, entries)
            end
          else
            let
              val token = fresh ()
              val (tracked, entries) = track rest
            in
              (Tracked {term = term, token = SOME token} :: tracked,
               (token, term) :: entries)
            end
  in
    track premise
  end

fun addHiddenAssumption fresh hidden entries =
  case hidden of
      NONE => entries
    | SOME index =>
        let
          val token = fresh ()
          val term = negate False
          val entry = (token, term)
          fun insert 0 rest = entry :: rest
            | insert _ [] =
                provenanceError "addHiddenAssumption"
                  "hidden elimination antecedent index is out of range"
            | insert n (item :: rest) =
                item :: insert (n - 1) rest
        in
          if index < 0 then
            provenanceError "addHiddenAssumption"
              "hidden elimination antecedent index is negative"
          else insert index entries
        end

fun ruleIsElim ({origin, ...} : tableau_rule) =
  case origin of
      blastRule.Stored {is_elim, ...} => is_elim
    | _ => false

fun ruleMajor function rule formula assumptions =
  if ruleIsElim rule then
    SOME (trackedPosition function formula assumptions)
  else
    (case trackedToken formula of
         NONE => NONE
       | SOME _ =>
           provenanceError function
             "an introduction rule selected an assumption formula")

fun childAssumptions function rule duplicate formula assumptions
      new_entries =
  let
    val introduced = rev new_entries
  in
    if not (ruleIsElim rule) then introduced @ assumptions
    else
      case trackedToken formula of
          NONE =>
            provenanceError function
              "an elimination rule selected a goal formula"
        | SOME token =>
            let
              val retained = lookupToken function token assumptions
              val remaining = deleteToken function token assumptions
              val base = introduced @ remaining
            in
              if duplicate then base @ [retained] else base
            end
  end

fun sameVarsWith checkpoint ([], []) = true
  | sameVarsWith checkpoint (left :: lefts, right :: rights) =
      (checkpoint ();
       left = right andalso sameVarsWith checkpoint (lefts, rights))
  | sameVarsWith checkpoint _ = false

fun log4 n = if n < 4 then 0 else 1 + log4 (n div 4)

fun instantiationPenalty n = 1 + log4 n

fun recursivePremiseMeasured checkpoint pattern premise =
  let
    fun matches (Var _) _ = (checkpoint (); true)
      | matches Goal (Const (name, _)) =
          (checkpoint (); name = not_name)
      | matches (Const (name, _)) Goal =
          (checkpoint (); name = not_name)
      | matches (Const (a, ats)) (Const (b, bts)) =
          (checkpoint ();
           a = b andalso match_lists (ats, bts))
      | matches (Fvar a) (Fvar b) = (checkpoint (); a = b)
      | matches Goal Goal = (checkpoint (); true)
      | matches False False = (checkpoint (); true)
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

fun recursivePremise pattern premise =
  recursivePremiseMeasured (fn () => ()) pattern premise

fun requeueGamma (formula, md) remaining duplicate =
  if duplicate then remaining @ [(negOfGoal formula, md)]
  else remaining

fun requeueTrackedGammaMeasured checkpoint
      (formula, md) remaining duplicate =
  if not duplicate then remaining
  else appendMeasured checkpoint remaining [(negOfTracked formula, md)]

fun requeueTrackedGamma pair remaining duplicate =
  requeueTrackedGammaMeasured (fn () => ()) pair remaining duplicate

fun killsAllAlternatives limit prems =
  limit < 0 andalso not (null prems)

fun mayUndoMeasured checkpoint {other_rules, updated, old_vars, new_vars} =
  other_rules orelse updated orelse
  sameVarsWith checkpoint (old_vars, new_vars)

fun mayUndo arguments = mayUndoMeasured (fn () => ()) arguments

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

(* The measured clash test polls once per trail entry and once per next
   variable.  It therefore cannot take clashVar's shortcut on an empty
   next_vars without losing those checkpoints, so the clash test stays a
   parameter of the shared pruning body below. *)
fun clashVarMeasured checkpoint vars (n, trail) =
  let
    fun occurs_in _ [] = false
      | occurs_in variable (next :: rest) =
          (checkpoint ();
           varOccurMeasured checkpoint variable (Var next) orelse
           occurs_in variable rest)
    fun clash (0, _) = false
      | clash (_, []) = false
      | clash (left, variable :: variables) =
          (checkpoint ();
           occurs_in variable vars orelse clash (left - 1, variables))
  in
    clash (n, trail)
  end

fun dropWith checkpoint (0, values) = values
  | dropWith checkpoint (_, []) = []
  | dropWith checkpoint (n, _ :: values) =
      (checkpoint (); dropWith checkpoint (n - 1, values))

fun prunePlanWith checkpoint clashes
      {branches, next_vars, trail_mark, trail, choices} =
  if branches = 1 then choices
  else
    let
      fun scan (last, _, _, []) = last
        | scan (last, mark, current, (oldmark, oldbrs) :: older) =
            (checkpoint ();
             if oldbrs < branches then last
             else if oldbrs > branches then
               scan (last, mark, current, older)
             else if clashes next_vars (mark - oldmark, current) then
               last
             else
               scan (older, oldmark,
                     dropWith checkpoint (mark - oldmark, current),
                     older))
    in
      scan (choices, trail_mark, trail, choices)
    end

(* Pure projection of prune, exported so its clash/no-clash boundary can be
   regression-tested without manufacturing exception values. *)
fun prunePlan arguments =
  prunePlanWith (fn () => ()) clashVar arguments

fun choiceMark (Choice (mark, branches, _)) = (mark, branches)

fun pruneWith checkpoint clashes state pruned
      (branches, next_vars, choices) =
  if branches = 1 then choices
  else
    let
      fun marks [] = []
        | marks (choice :: rest) =
            (checkpoint (); choiceMark choice :: marks rest)
      val all_marks = marks choices
      val remaining =
        prunePlanWith checkpoint clashes
          {branches = branches,
           next_vars = next_vars,
           trail_mark = trailSize state,
           trail = trailVars state,
           choices = all_marks}
      val removed =
        lengthMeasured checkpoint choices -
        lengthMeasured checkpoint remaining
      val _ = pruned := !pruned + removed
    in
      dropWith checkpoint (removed, choices)
    end

fun prune state pruned arguments =
  pruneWith (fn () => ()) clashVar state pruned arguments

fun pruneMeasured checkpoint state pruned arguments =
  pruneWith checkpoint (clashVarMeasured checkpoint) state pruned
    arguments

fun nextVars ({vars, ...} : search_branch) = vars

fun remainingVars [] = []
  | remainingVars (branch :: _) = nextVars branch

fun backtrack [] = raise PROVE
  | backtrack (Choice (_, _, jump) :: _) = raise jump

fun addTrackedLitWith checkpoint equal (original, lits) =
  let
    val original_term = trackedTerm original
    fun ins formula =
      let
        fun member [] = false
          | member (other :: rest) =
              (checkpoint ();
               equal (trackedTerm formula, trackedTerm other) orelse
               member rest)
      in
        if member lits then lits else formula :: lits
      end
  in
    case original_term of
        Goal $ formula =>
          let
            fun bad lit =
              case trackedTerm lit of
                  Goal $ _ => true
                | Const (head, _) $ other =>
                    head = not_name andalso equal (formula, other)
                | _ => false
            fun change lit =
              case trackedTerm lit of
                  Goal $ other =>
                    if equal (formula, other) then NONE
                    else SOME (withTrackedTerm (negate other) lit)
                | Const (head, _) $ other =>
                    if head = not_name andalso equal (formula, other) then
                      NONE
                    else SOME lit
                | _ => SOME lit
            val rest =
              if existsMeasured checkpoint bad lits then
                mapPartialMeasured checkpoint change lits
              else lits
          in
            Tracked
              {term = Goal $ formula, token = trackedToken original} :: rest
          end
      | _ => ins original
  end

fun addTrackedLit arguments =
  addTrackedLitWith (fn () => ()) aconv arguments

fun addTrackedLitMeasured checkpoint arguments =
  addTrackedLitWith checkpoint (aconvMeasured checkpoint) arguments

fun substAtomicWith checkpoint (old, replacement) term =
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

fun substAtomic pair term = substAtomicWith (fn () => ()) pair term

(* Eta-contraction, the occurs check and the Skolem/Fvar orientation of
   blast.ML:692--790, as one body. *)
fun destEqWith checkpoint equal term =
  let
    val member_zero = existsMeasured checkpoint (fn i => i = 0)
    val loose = loose_bnos_measured checkpoint
    val decrement = incr_boundvars_measured checkpoint ~1
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
        fun occursEqual value =
          equal (target, value) orelse visit value
        and visit value =
          (checkpoint ();
           case value of
               Var variable =>
                 (case !variable of
                      SOME assigned => occursEqual assigned
                    | NONE => not (member variable allowed))
             | Abs (_, body) => occursEqual body
             | left $ right => occursEqual right orelse occursEqual left
             | _ => false)
      in
        occursEqual
      end

    fun checked (old, replacement) =
      if occurs old replacement then raise DEST_EQ
      else (old, replacement)

    fun orient (left, right) =
      case (left, right) of
          (Skolem _, _) => checked (left, right)
        | (_, Skolem _) => checked (right, left)
        | (Fvar _, _) => checked (left, right)
        | (_, Fvar _) => checked (right, left)
        | _ => raise DEST_EQ
  in
    checkpoint ();
    case term of
        Const (name, _) $ left0 $ right0 =>
          if name = equality_name then
            let
              val left = contract left0
              val right = contract right0
            in
              orient (left, right)
            end
          else raise DEST_EQ
      | _ => raise DEST_EQ
  end

fun equalTrackedSubstWith checkpoint equal function
      (formula,
       {pairs, lits, vars, lim, assumptions} : search_branch) =
  let
    val (old, replacement) =
      destEqWith checkpoint equal (trackedTerm formula)
    val equality = trackedPosition function formula assumptions
    val token = valOf (trackedToken formula)
    val subst = substAtomicWith checkpoint (old, replacement)
    (* The model mirrors work already polled while traversing the search
       queues.  Keep this bounded positional bookkeeping pure so provenance
       does not perturb the established measured checkpoint counters. *)
    val model_subst = substAtomic (old, replacement)
    fun substitute tracked =
      withTrackedTerm (subst (trackedTerm tracked)) tracked
    fun subForm ((item, md), (changed, unchanged)) =
      let
        val _ = checkpoint ()
        val result = substitute item
      in
        if equal (trackedTerm result, trackedTerm item) then
          (changed, (item, md) :: unchanged)
        else ((result, md) :: changed, unchanged)
      end
    fun subFrame ((safe, unsafe), (changed, frames)) =
      let
        val _ = checkpoint ()
        val (changed', safe') = List.foldr subForm (changed, []) safe
        val (changed'', unsafe') =
          List.foldr subForm (changed', []) unsafe
      in
        (changed'', (safe', unsafe') :: frames)
      end
    fun subLit (lit, (changed, unchanged)) =
      let
        val _ = checkpoint ()
        val result = substitute lit
      in
        if equal (trackedTerm result, trackedTerm lit) then
          (changed, result :: unchanged)
        else ((result, true) :: changed, unchanged)
      end
    fun subEntry
          ((entry as (_, term)), (mask, changed, unchanged)) =
      let val result = model_subst term
      in
        if aconv (result, term) then
          (false :: mask, changed, entry :: unchanged)
        else
          (true :: mask, (#1 entry, result) :: changed, unchanged)
      end
    val remaining = deleteToken function token assumptions
    val (changed_mask, changed_assumptions, unchanged_assumptions) =
      List.foldr subEntry ([], [], []) remaining
    val (changed, lits') = List.foldr subLit ([], []) lits
    val (changed', pairs') = List.foldr subFrame (changed, []) pairs
    val _ = checkpoint ()
  in
    (equality, changed_mask,
     {pairs = (changed', []) :: pairs', lits = lits', vars = vars,
      lim = lim,
      assumptions = changed_assumptions @ unchanged_assumptions})
  end

fun equalTrackedSubst arguments =
  equalTrackedSubstWith (fn () => ()) aconv "equalTrackedSubst" arguments

fun equalTrackedSubstMeasured checkpoint arguments =
  equalTrackedSubstWith checkpoint (aconvMeasured checkpoint)
    "equalTrackedSubstMeasured" arguments

fun closeStep function assumptions (formula, literal) =
  let
    val formula_term = trackedTerm formula
    val literal_term = trackedTerm literal
    fun assumption tracked =
      trackedPosition function tracked assumptions
    fun contradiction negative positive =
      CloseContradiction
        {negative = assumption negative, positive = assumption positive}
  in
    if isGoal formula_term then
      CloseAssume {assumption = assumption literal}
    else if isGoal literal_term then
      CloseAssume {assumption = assumption formula}
    else if isNot formula_term then contradiction formula literal
    else if isNot literal_term then contradiction literal formula
    else
      provenanceError function
        "a successful literal close has no supported polarity"
  end

fun tryTrackedCloseWith unifier function assumptions (formula, literal) =
  let
    val formula_term = trackedTerm formula
    val literal_term = trackedTerm literal
    fun positioned tracked = Option.isSome (trackedToken tracked)
    val reconstructible =
      if isGoal formula_term then positioned literal
      else if isGoal literal_term then positioned formula
      else if isNot formula_term orelse isNot literal_term then
        positioned formula andalso positioned literal
      else false
    fun close (left, right) =
      if reconstructible andalso unifier ([], left, right) then
        SOME (closeStep function assumptions (formula, literal))
      else NONE
  in
    if isGoal formula_term then
      close (rand formula_term, literal_term)
    else if isGoal literal_term then
      close (formula_term, rand literal_term)
    else if isNot formula_term then
      close (rand formula_term, literal_term)
    else if isNot literal_term then
      close (formula_term, rand literal_term)
    else NONE
  end

fun tryTrackedClose state assumptions arguments =
  tryTrackedCloseWith (unify state) "tryTrackedClose" assumptions
    arguments

fun tryTrackedCloseMeasured cleanup checkpoint state assumptions
      arguments =
  tryTrackedCloseWith (unifyMeasuredWith cleanup checkpoint state)
    "tryTrackedCloseMeasured" assumptions arguments

fun foldPremVarsWith checkpoint addVars prems vars =
  let
    fun fold [] accumulated = accumulated
      | fold (premise :: rest) accumulated =
          (checkpoint (); fold rest (addVars (premise, accumulated)))
  in
    fold (rev prems) vars
  end

fun foldPremVars prems vars =
  foldPremVarsWith (fn () => ()) add_terms_vars prems vars

fun foldPremVarsMeasured checkpoint prems vars =
  foldPremVarsWith checkpoint (add_terms_vars_measured checkpoint)
    prems vars

fun termString term =
  case term of
      Const (name, []) => KernelSig.name_toString name
    | Const (name, args) =>
        KernelSig.name_toString name ^ "{" ^
        String.concatWith "," (map termString args) ^ "}"
    | Skolem (name, variables) =>
        name ^ "[" ^ Int.toString (length variables) ^ "]"
    | Fvar name => name
    | Goal => "*Goal*"
    | False => "*False*"
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

datatype interruption_cleanup = Restore | AbandonOwned

fun runGoal cleanup_policy instrumentation claset depth goal cont =
  let
    exception INTERRUPTED
    exception STOP_EXCEPTION of exn
    val state = newState ()
    val rule_cache = blastRule.newCache ()
    val closed = ref 0
    val created = ref 1
    val pruned = ref 0
    val next_token = ref 0
    fun freshToken () =
      (next_token := !next_token + 1; !next_token)
    val safeRuleOrigin = "safe rule"
    val safeChildOrigin = "safe child"
    val unsafeRuleOrigin = "unsafe rule"
    val unsafeChildOrigin = "unsafe child"
    (* The search workers come as two aligned records, one plain and one
       measured, selected once per run: [Off] and [Stats] take the plain
       one, [On] the measured one.  [prv] has a single body that closes
       over the selected components as ordinary free variables, so the
       production and the measured search cannot drift apart.  The phase
       counters and the cooperative checkpoint exist only in the [On] arm;
       every plain counterpart is inert.

       Workers whose measured variant polls the checkpoint -- and so may
       have to roll the trail back before propagating an interruption --
       take the current search step's trail mark as their leading
       argument.  Binding the components once here, rather than passing a
       worker record through [prv]'s mutual recursion, is deliberate: the
       recursion must stay free of record construction and field
       selection. *)
    val plainWorkers =
      let
        val noop = fn () => ()
        val unifyPlain = unify state
        val tryClose = tryTrackedClose state
        val prunePlain = prune state pruned
        val negLits = map negOfTracked
        val existsGoal = List.exists isGoal
        val appendPlain = fn left => fn right => left @ right
        val pairUnflagged = map (fn item => (item, false))
        val initialFormulas =
          fn goal => map first (blastRule.initialBranch goal)
      in
        {checkpointAt=fn _ => (),
         rollbackAt=fn mark => clearTo state mark,
         noteSafeRuleAttempt=noop,
         noteUnificationSuccess=noop,
         noteEqualityAttempt=noop,
         noteEqualitySuccess=noop,
         noteLiteralAttempt=noop,
         noteLiteralSuccess=noop,
         addVarsAt=fn _ => add_term_vars,
         varsInVarsAt=fn _ => vars_in_vars,
         foldPremVarsAt=fn _ => foldPremVars,
         unifyAt=fn _ => unifyPlain,
         tryCloseAt=fn _ => tryClose,
         pruneAt=fn _ => prunePlain,
         equalSubstAt=fn _ => equalTrackedSubst,
         joinMdAt=fn _ => joinTrackedMd,
         negGoalsAt=fn _ => negOfTrackedGoals,
         mapNegLitsAt=fn _ => negLits,
         existsGoalAt=fn _ => existsGoal,
         lengthPremsAt=fn _ => List.length,
         addTrackedLitAt=fn _ => addTrackedLit,
         appendUnsafeAt=fn _ => appendPlain,
         safeRulesFor=blastRule.safeRules rule_cache claset,
         unsafeRulesFor=blastRule.unsafeRules rule_cache claset,
         noteUnsafeRuleAttempt=noop,
         mapPairAt=fn _ => pairUnflagged,
         requeueGammaAt=fn _ => requeueTrackedGamma,
         recursivePremiseAt=fn _ => recursivePremise,
         mayUndoAt=fn _ => mayUndo,
         normAt=fn _ => norm,
         lengthBranchesAt=fn _ => List.length,
         lengthRulesAt=fn _ => List.length,
         mergeUnsafe=appendPlain,
         initialFormulasOf=initialFormulas,
         initialBranchOf=initSearchBranch freshToken,
         cleanupRun=fn _ => ()}
      end

    val (instrumentEntry, noteInference, noteRuleInference,
         instrumentationResult, searchWorkers) =
      case instrumentation of
          Off =>
            (fn brs => traceState depth (projectBranches brs),
             fn () => (), fn _ => (),
             fn () => (0, 0, [], zero_phase_statistics),
             plainWorkers)
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
              (fn brs => traceState depth (projectBranches brs),
               inference, ruleInference, result, plainWorkers)
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
                    let val projected = projectBranches brs
                    in
                      fullTrace := projected :: !fullTrace;
                      traceState depth projected
                    end
                 else traceState depth (projectBranches brs))
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

              (* [at mark] is the checkpoint a worker polls when it may have
                 to roll the trail back to that step's mark first. *)
              fun at mark () = checkpointRollback mark

              val measuredWorkers =
                {checkpointAt=checkpointRollback,
                 rollbackAt=fn mark =>
                   clearToMeasuredWith cleanupException checkpoint state
                     mark,
                 noteSafeRuleAttempt=ruleAttempt safe_attempts,
                 noteUnificationSuccess=unificationSuccess,
                 noteEqualityAttempt=equalityAttempt,
                 noteEqualitySuccess=equalitySuccess,
                 noteLiteralAttempt=literalAttempt,
                 noteLiteralSuccess=literalSuccess,
                 addVarsAt=fn mark =>
                   add_term_vars_measured (at mark),
                 varsInVarsAt=fn mark =>
                   vars_in_vars_measured (at mark),
                 foldPremVarsAt=fn mark =>
                   foldPremVarsMeasured (at mark),
                 unifyAt=fn mark =>
                   unifyMeasuredWith cleanupException (at mark) state,
                 tryCloseAt=fn mark =>
                   tryTrackedCloseMeasured cleanupException (at mark) state,
                 pruneAt=fn mark =>
                   pruneMeasured (at mark) state pruned,
                 equalSubstAt=fn mark =>
                   equalTrackedSubstMeasured (at mark),
                 joinMdAt=fn mark =>
                   joinTrackedMdMeasured (at mark),
                 negGoalsAt=fn mark =>
                   negOfTrackedGoalsMeasured (at mark),
                 mapNegLitsAt=fn mark =>
                   mapMeasured (at mark) negOfTracked,
                 existsGoalAt=fn mark =>
                   existsMeasured (at mark) isGoal,
                 lengthPremsAt=fn mark =>
                   lengthMeasured (at mark),
                 addTrackedLitAt=fn mark =>
                   addTrackedLitMeasured (at mark),
                 appendUnsafeAt=fn mark =>
                   appendMeasured (at mark),
                 safeRulesFor=blastRule.safeRulesMeasured
                   rule_monitor rule_cache claset,
                 unsafeRulesFor=blastRule.unsafeRulesMeasured
                   rule_monitor rule_cache claset,
                 noteUnsafeRuleAttempt=ruleAttempt unsafe_attempts,
                 mapPairAt=fn mark =>
                   mapMeasured (at mark) (fn item => (item, false)),
                 requeueGammaAt=fn mark =>
                   requeueTrackedGammaMeasured (at mark),
                 recursivePremiseAt=fn mark =>
                   recursivePremiseMeasured (at mark),
                 mayUndoAt=fn mark =>
                   mayUndoMeasured (at mark),
                 normAt=fn mark => normMeasured (at mark),
                 lengthBranchesAt=fn mark =>
                   lengthMeasured (at mark),
                 lengthRulesAt=fn mark =>
                   lengthMeasured (at mark),
                 mergeUnsafe=appendMeasured checkpoint,
                 initialFormulasOf=fn goal =>
                   mapFirstMeasured checkpoint
                     (blastRule.initialBranchMeasured checkpoint goal),
                 initialBranchOf=initSearchBranchMeasured
                   checkpoint freshToken,
                 cleanupRun=fn exn => cleanupException exn state 0}
            in
              (entry, inference, ruleInference, result, measuredWorkers)
            end

    val {checkpointAt,rollbackAt,noteSafeRuleAttempt,
         noteUnificationSuccess,noteEqualityAttempt,noteEqualitySuccess,
         noteLiteralAttempt,noteLiteralSuccess,addVarsAt,varsInVarsAt,
         foldPremVarsAt,unifyAt,tryCloseAt,pruneAt,equalSubstAt,joinMdAt,
         negGoalsAt,mapNegLitsAt,existsGoalAt,lengthPremsAt,addTrackedLitAt,
         appendUnsafeAt,safeRulesFor,unsafeRulesFor,noteUnsafeRuleAttempt,
         mapPairAt,requeueGammaAt,recursivePremiseAt,mayUndoAt,normAt,
         lengthBranchesAt,lengthRulesAt,mergeUnsafe,initialFormulasOf,
         initialBranchOf,cleanupRun} = searchWorkers

    val prepared =
      SOME (initialFormulasOf goal)
      handle INTERRUPTED => NONE
           | STOP_EXCEPTION exn => raise exn

    fun proofOf (tacs, trace) =
      {script = rev tacs,
       trace = map projectBranches (rev trace),
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
              lits, vars, lim, assumptions} : search_branch) :: brs =>
            let
              exception PRV
              val mark = trailSize state
              val branches = lengthBranchesAt mark brs0
              val next_vars = remainingVars brs
              val formula =
                withTrackedTerm (normAt mark (trackedTerm formula)) formula
              val rules = safeRulesFor vars (trackedTerm formula)
              val rule_count = lengthRulesAt mark rules

              fun newBranches rule (vars', lim') prems =
                let
                  fun make [] = brs
                    | make ((premise, hidden) :: rest) =
                        let
                          val _ = checkpointAt mark
                          val (tracked, visible_introduced) =
                            trackPremise freshToken premise
                          val introduced =
                            addHiddenAssumption freshToken hidden
                              visible_introduced
                          val joined = joinMdAt mark md tracked
                          val child_assumptions =
                            childAssumptions safeChildOrigin rule false
                              formula assumptions introduced
                          val branch =
                            if existsGoalAt mark premise then
                              {pairs =
                                 (joined, []) ::
                                 negGoalsAt mark ((safe, unsafe) :: pairs),
                               lits = mapNegLitsAt mark lits,
                               vars = vars', lim = lim',
                               assumptions = child_assumptions}
                            else
                              {pairs =
                                 (joined, []) :: (safe, unsafe) :: pairs,
                               lits = lits, vars = vars', lim = lim',
                               assumptions = child_assumptions}
                        in
                          branch :: make rest
                        end
                in
                  make (ListPair.zip (prems, #hidden_assumptions rule))
                end

              fun deeper [] = raise NEWBRANCHES
                | deeper ((rule : tableau_rule) :: other) =
                    let
                      val _ = checkpointAt mark
                      val pattern = #pattern rule
                      val prems = #premises rule
                      val rule_vars = addVarsAt mark (pattern, [])
                      val _ = checkpointAt mark
                      val _ = noteSafeRuleAttempt ()
                    in
                      if not
                           (unifyAt mark
                             (rule_vars, pattern, trackedTerm formula)) then
                        deeper other
                      else
                        let
                          val _ = noteUnificationSuccess ()
                          val _ = checkpointAt mark
                          val updated = mark < trailSize state
                          val lim' =
                            if updated then
                              lim - instantiationPenalty rule_count
                            else lim
                          val vars0 = varsInVarsAt mark vars
                          val vars' = foldPremVarsAt mark prems vars0
                          val choices' =
                            Choice (mark, branches, PRV) :: choices
                          val major =
                            ruleMajor safeRuleOrigin rule formula
                              assumptions
                          val tacs' =
                            SafeRule
                              {rule = rule, updated = updated,
                               major = major} :: tacs

                          fun descend () =
                            if null prems then
                              (closed := !closed + 1;
                               noteRuleInference lim';
                               prv
                                 (tacs', brs0 :: trace,
                                  pruneAt mark
                                    (branches, next_vars, choices'),
                                  brs))
                            else if lim' < 0 then
                              (rollbackAt mark; raise NEWBRANCHES)
                            else
                              (created :=
                                 !created + lengthPremsAt mark prems - 1;
                               noteRuleInference lim';
                               prv
                                 (tacs', brs0 :: trace, choices',
                                  newBranches rule (vars', lim') prems))
                        in
                          descend ()
                          handle PRV =>
                            if updated then
                              (rollbackAt mark; deeper other)
                            else backtrack choices
                        end
                    end

              fun closeF [] = raise CLOSEF
                | closeF (literal :: literals) =
                    let
                      val _ = checkpointAt mark
                      val _ = noteLiteralAttempt ()
                    in
                      case tryCloseAt mark assumptions
                             (formula, literal) of
                          NONE => closeF literals
                        | SOME step =>
                            let
                              val _ = noteLiteralSuccess ()
                              val _ = checkpointAt mark
                              val choices' =
                                pruneAt mark
                                  (branches, next_vars,
                                   Choice (mark, branches, PRV) :: choices)
                            in
                              closed := !closed + 1;
                              noteInference ();
                              (prv
                                 (step :: tacs, brs0 :: trace,
                                  choices', brs)
                               handle PRV =>
                                 (rollbackAt mark; closeF literals))
                            end
                    end

              fun closeLevels [] = raise CLOSEF
                | closeLevels ((level_safe, level_unsafe) :: rest) =
                    (checkpointAt mark;
                     closeF (map first level_safe)
                     handle CLOSEF =>
                       (closeF (map first level_unsafe)
                        handle CLOSEF => closeLevels rest))

              fun cascade () =
                if lim < 0 then backtrack choices
                else
                  (let
                     val _ = checkpointAt mark
                     val _ = noteEqualityAttempt ()
                     val (equality, changed, substituted) =
                       equalSubstAt mark
                         (formula,
                          {pairs = (safe, unsafe) :: pairs,
                           lits = lits, vars = vars, lim = lim,
                           assumptions = assumptions})
                     val _ = noteEqualitySuccess ()
                     val _ = noteInference ()
                   in
                     prv
                       (HypSubst
                          {equality = equality, changed = changed} :: tacs,
                        brs0 :: trace, choices,
                        substituted :: brs)
                   end
                   handle DEST_EQ =>
                     (closeF lits
                      handle CLOSEF =>
                        (closeLevels ((safe, unsafe) :: pairs)
                         handle CLOSEF => deeper rules)))

              fun fallback () =
                case unsafeRulesFor vars (trackedTerm formula) of
                    [] =>
                      prv
                        (tacs, brs0 :: trace, choices,
                         {pairs = (safe, unsafe) :: pairs,
                          lits = addTrackedLitAt mark (formula, lits),
                          vars = vars, lim = lim,
                          assumptions = assumptions} :: brs)
                  | _ =>
                      let
                        val goal_formula = isGoal (trackedTerm formula)
                        val (deferred, assumptions') =
                          if goal_formula then
                            let
                              val token = freshToken ()
                              val term = negOfGoal (trackedTerm formula)
                            in
                              (Tracked {term = term, token = SOME token},
                               (token, term) :: assumptions)
                            end
                          else (negOfTracked formula, assumptions)
                      in
                        prv
                          ((if goal_formula then DeferGoal :: tacs
                            else tacs),
                           brs0 :: trace, choices,
                           {pairs =
                              (safe,
                               appendUnsafeAt mark unsafe
                                 [(deferred, md)]) :: pairs,
                            lits = lits, vars = vars, lim = lim,
                            assumptions = assumptions'} :: brs)
                      end

            in
              cascade () handle NEWBRANCHES => fallback ()
            end
        | ({pairs = ([], unsafe) :: (safe, unsafe') :: pairs,
            lits, vars, lim, assumptions} : search_branch) :: brs =>
            let
              val merged = mergeUnsafe unsafe unsafe'
            in
              prv
                (tacs, trace, choices,
                 {pairs = (safe, merged) :: pairs,
                  lits = lits, vars = vars, lim = lim,
                  assumptions = assumptions} :: brs)
            end
        | brs0 as
            ({pairs = [([], (formula, md) :: unsafe)],
              lits, vars, lim, assumptions} : search_branch) :: brs =>
            let
              exception PRV
              val mark = trailSize state
              val formula =
                withTrackedTerm (normAt mark (trackedTerm formula)) formula
              val rules = unsafeRulesFor vars (trackedTerm formula)
              val rule_count = lengthRulesAt mark rules
              val branches = lengthBranchesAt mark brs0

              fun newPremise
                    (rule, vars', pattern, duplicate, lim')
                    (premise, hidden) =
                let
                  val _ = checkpointAt mark
                  val (tracked, visible_introduced) =
                    trackPremise freshToken premise
                  val introduced =
                    addHiddenAssumption freshToken hidden
                      visible_introduced
                  val safe' = mapPairAt mark tracked
                  val unsafe' =
                    requeueGammaAt mark (formula, md) unsafe duplicate
                  val lits' =
                    if existsGoalAt mark premise then
                      mapNegLitsAt mark lits
                    else lits
                  val pairs' =
                    if recursivePremiseAt mark pattern premise then
                      [(safe', unsafe')]
                    else [(safe', []), ([], unsafe')]
                  val child_assumptions =
                    childAssumptions unsafeChildOrigin rule duplicate
                      formula assumptions introduced
                in
                  {pairs = pairs', lits = lits',
                   vars = vars', lim = lim',
                   assumptions = child_assumptions}
                end

              fun newBranches (arguments as (rule, _, _, _, _)) prems =
                let
                  fun make [] = brs
                    | make (premise :: rest) =
                        (checkpointAt mark;
                         newPremise arguments premise :: make rest)
                in
                  make (ListPair.zip (prems, #hidden_assumptions rule))
                end

              fun deeper [] = raise NEWBRANCHES
                | deeper ((rule : tableau_rule) :: other) =
                    let
                      val _ = checkpointAt mark
                      val pattern = #pattern rule
                      val prems = #premises rule
                      val rule_vars = addVarsAt mark (pattern, [])
                      val _ = checkpointAt mark
                      val _ = noteUnsafeRuleAttempt ()
                    in
                      if not
                           (unifyAt mark
                             (rule_vars, pattern, trackedTerm formula)) then
                        deeper other
                      else
                        let
                          val _ = noteUnificationSuccess ()
                          val _ = checkpointAt mark
                          val updated = mark < trailSize state
                          val old_vars = varsInVarsAt mark vars
                          val new_vars = foldPremVarsAt mark prems old_vars
                          val duplicate = md
                          val lim' =
                            if updated then
                              lim - instantiationPenalty rule_count
                            else lim - 1
                          val undo =
                            mayUndoAt mark
                              {other_rules = not (null other),
                               updated = updated,
                               old_vars = old_vars,
                               new_vars = new_vars}
                          val major =
                            ruleMajor unsafeRuleOrigin rule formula
                              assumptions
                          val step =
                            UnsafeRule
                              {rule = rule, updated = updated,
                               duplicate = duplicate, major = major}

                          fun descend () =
                            if killsAllAlternatives lim' prems then
                              (rollbackAt mark; raise NEWBRANCHES)
                            else
                              (if null prems then
                                 closed := !closed + 1
                               else
                                 created :=
                                   !created + lengthPremsAt mark prems - 1;
                               noteRuleInference lim';
                               prv
                                 (step :: tacs, brs0 :: trace,
                                  Choice (mark, branches, PRV) :: choices,
                                  newBranches
                                    (rule, new_vars, pattern, duplicate,
                                     lim')
                                    prems))
                        in
                          descend ()
                          handle PRV =>
                            if undo then
                              (rollbackAt mark; deeper other)
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
                       vars = vars, lim = lim,
                       assumptions = assumptions} :: brs))
            end
        | _ :: _ => backtrack choices
      end

    val (completion, result) =
      case prepared of
          NONE => (Interrupted, NONE)
        | SOME formulas =>
            ((let
                val initial = initialBranchOf (formulas, depth)
              in
                (Completed,
                 SOME
                   (prv
                      ([], [], [Choice (trailSize state, 1, PROVE)],
                       [initial])))
              end
              handle PROVE => (Completed, NONE)
                   | INTERRUPTED =>
                       (cleanupRun INTERRUPTED; (Interrupted, NONE)))
             handle STOP_EXCEPTION exn => (cleanupRun exn; raise exn)
                  | exn => (cleanupRun exn; raise exn))
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
       remaining_trail_assignments = trailSize state,
       phase = phase}
  in
    {completion = completion, fullTrace = fullTrace, result = result,
     statistics = statistics}
  end

fun searchGoalMeasured options claset depth goal cont =
  runGoal AbandonOwned (On options) claset depth goal cont

fun searchGoalWithStats claset depth goal cont =
  let
    val report =
      runGoal Restore Stats claset depth goal cont
  in
    {result = #result report, statistics = #statistics report}
  end

fun searchGoal claset depth goal cont =
  #result (runGoal Restore Off claset depth goal cont)

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
