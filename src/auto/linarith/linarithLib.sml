structure linarithLib :> linarithLib =
struct

open Abbrev HolKernel Drule

val ERR = mk_HOL_ERR "linarithLib"

val same_type = linarithData.same_type

fun relation_carrier tm =
  let
    val (_, body0) = boolSyntax.strip_forall tm
    val (_, body1) = boolSyntax.strip_imp_only body0
    val body =
      case Lib.total boolSyntax.dest_neg body1 of
          SOME inner => inner
        | NONE => body1
  in
    case Lib.total boolSyntax.dest_eq body of
        SOME (left, right) =>
          if same_type (Term.type_of left) (Term.type_of right) andalso
             not (same_type (Term.type_of left) Type.bool)
          then SOME (Term.type_of left)
          else NONE
      | NONE =>
          (case Lib.total strip_comb body of
               SOME (_, [left, right]) =>
                 if same_type (Term.type_of left) (Term.type_of right) andalso
                    not (same_type (Term.type_of left) Type.bool) andalso
                    same_type (Term.type_of body) Type.bool
                 then SOME (Term.type_of left)
                 else NONE
             | _ => NONE)
  end

fun no_instance_for ty =
  case linarithData.instance_for ty of
      SOME _ => NONE
    | NONE => SOME ty

fun registered_carriers () =
  String.concatWith ", "
    (map (Parse.type_to_string o #ty) (linarithData.all_instances ()))

(* The carrier is a guess about where the arithmetic is, never a
   precondition on the goal -- a contradictory context refutes a
   conclusion of any type -- so it explains a failure rather than
   preventing an attempt.  The roster comes from the registry, so a
   carrier registered later cannot leave it stale. *)
fun unregistered_hint conclusion =
  case Option.mapPartial no_instance_for (relation_carrier conclusion) of
      NONE => ""
    | SOME ty =>
        " (no linarith instance for " ^ Parse.type_to_string ty ^
        "; registered: " ^ registered_carriers () ^ ")"

(* The hint travels with the search rather than being recomputed at the
   failure site: CCONTR_TAC has replaced the conclusion by F long before
   the search gives up. *)
fun no_proof function hint =
  raise ERR function ("linear arithmetic found no proof" ^ hint)

val classical_markers =
  [(clasetLib.destSIntro, "SIntro"),
   (clasetLib.destIntro, "Intro"),
   (clasetLib.destSElim, "SElim"),
   (clasetLib.destElim, "Elim"),
   (clasetLib.destSDest, "SDest"),
   (clasetLib.destDest, "Dest"),
   (clasetLib.destNorm, "Norm"),
   (clasetLib.destForward, "Forward"),
   (clasetLib.destSForward, "SForward")]

fun first_marker theorem markers =
  Lib.get_first
    (fn (dest, name) => Option.map (fn _ => name) (dest theorem))
    markers

fun reject function name =
  raise ERR function (name ^ " marker is not accepted by " ^ function)

fun plain_argument function theorem =
  let
    val {simp_rules, iff_rules, simp_controls, rest} =
      clasetLib.classify_simp_args [theorem]
  in
    if not (null simp_rules) then reject function "Simp"
    else if not (null iff_rules) then reject function "Iff"
    else if not (null simp_controls) then
      reject function "simplifier-control"
    else
      case rest of
          [plain] =>
            (case first_marker plain classical_markers of
                 SOME name => reject function name
               | NONE =>
                   (case clasetLib.destDel plain of
                        SOME _ => reject function "Del"
                      | NONE => plain))
        | _ =>
            raise ERR function "internal argument-classification error"
  end

(* A Split argument is held to the same P-form wherever it is offered:
   the entries below differ only in what they do with an accepted one,
   so an entry that rejects splits still rejects a malformed split as
   malformed rather than as a split. *)
fun classify_split_argument function theorem =
  if markerLib.is_Split theorem then
    let
      val split = markerLib.destSplit theorem
      val _ =
        linarithData.check_asm_split function
          "Split theorem (expected P-form)" split
    in
      SOME split
    end
  else NONE

fun simple_argument function theorem =
  case classify_split_argument function theorem of
      SOME _ => reject function "Split"
    | NONE => plain_argument function theorem

(* Both lists come out in argument order.  The fold is still the
   left-to-right one, and reverses at the end rather than being a
   foldr, because classification is where a malformed argument is
   rejected: this way the first bad argument is the one reported, as it
   is under the map SIMPLE_LINARITH_TAC classifies with. *)
fun full_arguments function arguments =
  let
    fun add (theorem, (facts, splits)) =
      case classify_split_argument function theorem of
          SOME split => (facts, split :: splits)
        | NONE => (plain_argument function theorem :: facts, splits)
    val (facts, splits) = List.foldl add ([], []) arguments
  in
    (List.rev facts, List.rev splits)
  end

(* A goal the arithmetic cannot refute is not yet a failure: the search
   splits it and asks again.  So refute answers NONE rather than
   failing, and only a caller that has run out of splits pays for the
   diagnostics below. *)
fun refutation config (assumptions, conclusion) =
  linarithReplay.refute config assumptions conclusion

(* The diagnostics report the goal as preprocessing left it, so they stay
   on this side of the interface; the failure is reported under the
   caller's name because the public entries report their own.  This is
   split from core because the search below reaches the same dead end
   already knowing the answer is NONE, and re-entering core there would
   spend a second full refutation to be told so again. *)
fun exhausted function hint (assumptions, conclusion) =
  (linarithData.trace_terms 2 "preprocessed assumptions" assumptions;
   linarithData.trace_terms 2 "preprocessed conclusion" [conclusion];
   no_proof function hint)

fun core function hint config goal =
  case refutation config goal of
      SOME tactic => tactic goal
    | NONE => exhausted function hint goal

(* Everything the session owns -- the [arith] table here, and the
   registry and the [arith_split] table at the entry below -- is read
   where the tactic is applied, not where its value is built.  A script
   that binds a tactic at its head and proves an [arith] lemma further
   down would otherwise get a tactic that cannot see the lemma, while
   the same expression written out at the call site could.  What the
   caller owns, its own arguments, is still classified where the value
   is built: a malformed argument is the caller's mistake and is better
   reported at the tactic than at some later goal.  The per-application
   reads are what the memos above make cheap -- a generation compare,
   not a rebuild. *)
fun SIMPLE_LINARITH_TAC arguments =
  let
    val function = "SIMPLE_LINARITH_TAC"
    val argument_facts = map (simple_argument function) arguments
  in
    fn goal =>
      Tactical.THEN
        (clasetLib.INSERT_FACTS_TAC
           (linarithData.arith_facts () @ argument_facts),
         fn inner as (_, conclusion) =>
           core function (unregistered_hint conclusion)
             linarithData.default_config inner) goal
  end

fun has_registered_subterm tm =
  Lib.can
    (find_term
       (fn sub =>
          Option.isSome (linarithData.instance_for (Term.type_of sub))))
    tm

(* The propositional skeleton of a term, classified once for the three
   traversals below. NEG/IMP flip polarity; FORALL/EXISTS bind. *)
datatype shape =
    NEG of term
  | EQUIV of term * term
  | CONJ of term * term
  | DISJ of term * term
  | IMP of term * term
  | FORALL of term * term
  | EXISTS of term * term
  | ATOM

fun shape_of tm =
  case Lib.total boolSyntax.dest_neg tm of
      SOME body => NEG body
    | NONE =>
  case Lib.total boolSyntax.dest_conj tm of
      SOME sides => CONJ sides
    | NONE =>
  case Lib.total boolSyntax.dest_disj tm of
      SOME sides => DISJ sides
    | NONE =>
  case Lib.total boolSyntax.dest_imp_only tm of
      SOME sides => IMP sides
    | NONE =>
  case Lib.total boolSyntax.dest_forall tm of
      SOME parts => FORALL parts
    | NONE =>
  case Lib.total boolSyntax.dest_exists tm of
      SOME parts => EXISTS parts
    | NONE =>
  case Lib.total boolSyntax.dest_eq tm of
      SOME sides => EQUIV sides
    | NONE => ATOM

fun shell_relevant tm =
  linarithDecomp.is_relevant tm orelse
  (case shape_of tm of
       NEG body => shell_relevant body
     | EQUIV (left, right) =>
         same_type (Term.type_of left) Type.bool orelse
         shell_relevant left orelse shell_relevant right
     | CONJ (left, right) =>
         shell_relevant left orelse shell_relevant right
     | DISJ (left, right) =>
         shell_relevant left orelse shell_relevant right
     | IMP (left, right) =>
         shell_relevant left orelse shell_relevant right
     | FORALL (_, body) => shell_relevant body
     | EXISTS (_, body) => shell_relevant body
     | ATOM => has_registered_subterm tm)

(* The assumptions the arithmetic could build a row from.  What this
   drops it drops for good, so an immediate propositional contradiction
   -- F itself, or a literal alongside its negation -- has to be taken
   before this runs rather than after: none of those has arithmetic
   content, so this filter removes exactly the assumptions that would
   have closed the goal.  That is what the opposite_tac step at the
   entry point below is for; the one inside nnf_flatten sees only what
   survived here. *)
fun filter_relevant (assumptions, conclusion) =
  let
    val filtered = List.filter shell_relevant assumptions
    fun validate [theorem] = theorem
      | validate _ =
          raise ERR "filter_relevant" "invalid validation theorem list"
  in
    ([(filtered, conclusion)], validate)
  end

(* The propositional half of the normalization is normalForms.NNF_CONV.
   What remains here is carrier-specific (truncated subtraction, say) and
   arrives from the registry rather than being named.

   Both the rewrite list and the rule REWRITE_RULE builds from it are a
   pure function of the instance registry, so they are built once per
   registry state rather than once per tactic call: REWRITE_RULE builds
   a rewrite net, and the net does not depend on the goal. *)
fun carrier_nnf_rewrites () =
  List.concat (map #nnf_rules (linarithData.all_instances ()))

val carrier_nnf_rule =
  linarithData.memo
    (fn () => Rewrite.REWRITE_RULE (carrier_nnf_rewrites ()))

fun opposite_tac (assumptions, conclusion) =
  let
    fun contradiction [] = NONE
      | contradiction (assumption :: rest) =
          (case Lib.total boolSyntax.dest_neg assumption of
               SOME positive =>
                 if List.exists (Term.aconv positive) assumptions then
                   SOME
                     (MP (ASSUME assumption) (ASSUME positive))
                 else contradiction rest
             | NONE => contradiction rest)
  in
    if List.exists (Term.aconv boolSyntax.F) assumptions then
      Tactic.ACCEPT_TAC (ASSUME boolSyntax.F) (assumptions, conclusion)
    else
      case contradiction assumptions of
          SOME theorem =>
            Tactic.CONTR_TAC theorem (assumptions, conclusion)
        | NONE => raise ERR "opposite_tac" "no immediate contradiction"
  end

(* Tactic.STRIP_ASSUME_TAC without the disjunction case.  Conjunctions
   and existentials decompose an assumption without branching, so they
   are eliminated as soon as they appear.  Disjunctions branch, and are
   left standing for split_on_demand to eliminate one at a time: a goal
   the arithmetic closes never pays for the case splits it did not
   need. *)
val strip_literals =
  Thm_cont.REPEAT_TCL
    (Thm_cont.FIRST_TCL [Thm_cont.CONJUNCTS_THEN, Thm_cont.CHOOSE_THEN])
    Tactic.CHECK_ASSUME_TAC

(* NNF_CONV does not see the carrier rules and it does not see their
   output, so the order is fixed: NNF first, then the carrier pass,
   because SUB_EQ_0 and its kin produce relations already in NNF.  The
   carrier rule is a parameter because building it reads the registry
   and builds a rewrite net; the search runs this at every node of a
   tree over one fixed registry. *)
fun nnf_flatten carrier_rule goal =
  let
    val nnf_rule = carrier_rule o Conv.CONV_RULE normalForms.NNF_CONV
  in
    Tactical.THEN
      (Tactical.POP_ASSUM_LIST
         (fn theorems =>
           Tactical.MAP_EVERY (strip_literals o nnf_rule) theorems),
       Tactical.TRY opposite_tac) goal
  end

fun limit_exceeded function limit =
  let
    val message =
      "linarith_split_limit exceeded (current value is " ^
      Int.toString limit ^ ")"
    val _ = linarithData.trace 1 message
  in
    raise ERR function message
  end

(* One theorem per conclusion, in order of first occurrence -- an order
   compute_split_rules below depends on.  Term.compare, the order the
   conclusions are keyed by, parts company with aconv only over terms
   the tables these results reach -- the solver's atom index, the
   result cache's store and its context graph -- would merge in any
   case, all three being keyed on Term.compare themselves. *)
fun distinct_thms theorems =
  linarithData.distinct_by Term.compare Thm.concl theorems

fun compute_split_rules extra =
  let
    val seeds =
      List.concat (map #pre_split (linarithData.all_instances ()))
    val source =
      distinct_thms
        (linarithData.arith_split_thms () @ extra @ seeds)
    fun forms theorem =
      if splitLib.is_asm_split theorem then [theorem]
      else [theorem, splitLib.mk_asm_split theorem]
  in
    List.concat (map forms source)
  end

(* Without caller-supplied rules the rules are a pure function of the
   instance registry and the [arith_split] table, and so is the tactic
   splitLib derives from them -- which analyses every rule and inserts
   it into a net by a quadratic key walk, so it is the more expensive
   half.  This is the case every entry point takes unless the caller
   passed split arguments, so the tactic is built once per state of the
   two rather than once per call.

   The caller's rules cannot be appended to a cached list: source
   deduplicates in arith_split-then-extra-then-seeds order, so an extra
   that repeats a seed takes the seed's place rather than following it,
   and appending would both reorder the net splitLib builds and keep
   the wrong one of the two theorems.  Those calls recompute. *)
val cached_split_tac =
  linarithData.memo_with_splits
    (fn () => splitLib.SPLIT_TAC (compute_split_rules []))

fun split_tactic [] = cached_split_tac ()
  | split_tactic extra = splitLib.SPLIT_TAC (compute_split_rules extra)

fun decomp_atoms tm =
  case linarithDecomp.decomp tm of
      NONE => []
    | SOME (linarithSolve.Decomp {lhs, rhs, ...}) =>
        map #1 (lhs @ rhs)

(* Every instance sees every atom: an instance's atom_facts declines the
   atoms outside its own carrier, and the ones it accepts need not live
   in that carrier either (int accepts Num i : num). *)
fun facts_for tm =
  List.concat
    (map (fn i => #atom_facts i tm) (linarithData.all_instances ()))

(* One round of augmentation: the atom facts of those atoms of terms
   that processed has not already been asked about, less the ones known
   already records.  Both tests are needed -- the atom set stops an
   atom being asked twice, and the conclusion set stops two different
   atoms contributing the same fact. *)
fun augmentation_round processed known terms =
  let
    val candidates = List.concat (map decomp_atoms terms)
    fun inspect (candidate, entry as (seen, facts)) =
      if Termtab.defined seen candidate then entry
      else
        (Termtab.insert_set candidate seen,
         facts_for candidate @ facts)
    val (seen, facts) = foldl inspect (processed, []) candidates
    val unique = distinct_thms facts
    fun stale theorem = Termtab.defined known (Thm.concl theorem)
  in
    (seen, List.filter (not o stale) unique)
  end

(* Augmentation runs to a fixpoint, because a contributed fact's own
   atoms are candidates in their turn, and it is bounded by limit
   rounds.  It answers the facts to assume together with the atom set
   to carry on with, rather than assuming them itself, because that set
   travels down the branch of the search: see split_on_demand.  What is
   already on the branch travels across the rounds as a set too, each
   round only adding to it. *)
fun augmentation function limit processed assumptions =
  let
    fun remember terms known =
      List.foldl (Lib.uncurry Termtab.insert_set) known terms
    fun loop known processed added rounds terms =
      let
        val (processed', facts) =
          augmentation_round processed known terms
      in
        if null facts then (processed', List.rev added)
        else if rounds >= limit then limit_exceeded function limit
        else
          let
            val conclusions = List.map Thm.concl facts
          in
            loop (remember conclusions known) processed'
              (List.revAppend (facts, added)) (rounds + 1) conclusions
          end
      end
  in
    loop (remember assumptions Termtab.empty) processed [] 0 assumptions
  end

(* Whether a disjunct can be added to the literals already assumed
   without the arithmetic refuting the result.  A disjunct that cannot
   is a case the split would close immediately, so counting them
   measures how much of a disjunction is still live.  The literals are
   taken already decomposed, since every disjunct of every disjunction
   is scored against the same ones. *)
fun consistent config decomposed disjunct =
  case linarithSolve.prove_decomposed config linarithDecomp.decomp
         linarithDecomp.is_nonnegative
         ((disjunct, linarithDecomp.decomp disjunct) :: decomposed)
         boolSyntax.F of
      (_, SOME _) => false
    | (_, NONE) => true

(* Eliminate one disjunctive assumption, choosing the one with the
   fewest disjuncts still consistent with the literals already assumed.
   Choosing blindly makes the search exponential in the number of
   disjunctions, because it expands a disjunction of conjunctions into
   its disjunctive normal form before the arithmetic ever runs.
   Choosing this way is unit propagation modulo the arithmetic: a
   disjunction all but one of whose cases the current literals already
   refute costs one branch, not two. *)
fun disj_elim_tac config (assumptions, conclusion) =
  let
    val (disjunctions, literals) =
      List.partition boolSyntax.is_disj assumptions
    val _ =
      if List.null disjunctions then
        raise ERR "disj_elim_tac" "no disjunctive assumption"
      else ()
    val decomposed =
      List.map (fn tm => (tm, linarithDecomp.decomp tm)) literals
    fun score disjunction =
      (List.length
         (List.filter (consistent config decomposed)
            (boolSyntax.strip_disj disjunction)),
       disjunction)
    fun cheaper (candidate as (count, _), best as (fewest, _)) =
      if count < fewest then candidate else best
    val scored = List.map score disjunctions
    val (_, chosen) = List.foldl cheaper (hd scored) (tl scored)
    val (left, right) = boolSyntax.dest_disj chosen
    val common = List.filter (not o Term.aconv chosen) assumptions
    val goals =
      [(common @ [left], conclusion), (common @ [right], conclusion)]
    fun justify [left_case, right_case] =
          Thm.DISJ_CASES (Thm.ASSUME chosen) left_case right_case
      | justify _ = raise ERR "disj_elim_tac" "invalid justification"
  in
    (goals, justify)
  end

(* Refute the goal in hand; only if that fails, take one step and try
   again.  The steps are ordered by how much they cost and how much
   they can be avoided:

   Disjunction elimination comes first.  An operator split does not
   branch by itself — it replaces a MIN, MAX or truncated subtraction
   by a conditional statement of its cases, which normalization turns
   into a disjunction — so disjunction elimination is what consumes
   what operator splitting produces.  Leaving those disjunctions
   standing lets the operators reappear in every one of them, and the
   splitting never finishes.

   Fact augmentation comes last, because it is the one step that adds
   assumptions without discharging anything: doing it before the case
   splits would offer the splitter its own output to split, and the
   splitting would not finish.  It is tried after the case splits have
   run out and before the goal is declared unrefutable, and it runs to
   a fixpoint there, so a second try at the same goal has nothing left
   to add.  Coming last is also what keeps it from missing atoms:
   nothing reaches it with a disjunction still standing, so the atoms
   it collects from an assumption are the atoms of a literal.

   Disjunction elimination is what has no budget of its own, and what
   keeps the search finite is that nothing refills its supply
   indefinitely.  Both of the other two steps do put disjunctions back:
   an operator split states its cases as one, and an atom fact in
   equivalence form becomes two once normalization has expanded it.  So
   both are bounded along the branch, by split_limit apiece, and
   augmentation additionally carries the atoms it has already
   contributed for down the branch.  That last is the substantive one:
   a fact contributed above a case split is still on the branch below
   it, in whatever form the split left it, so deriving it again there
   derives an assumption -- and, for a fact whose normal form is a
   disjunction, one the split has just consumed, which is an
   alternation that on its own never finishes.  The bounds are the
   backstop for an instance whose atom facts have no finite closure.

   split_limit keeps its meaning of an operator-splitting and
   augmentation bound, now counted along a branch of the search rather
   than along a preprocessing chain.

   The failure hint is an argument of the search rather than of this
   function, so a caller can read it off the goal without rebuilding
   the rewriting the search sets up once. *)
type search_branch =
  {splits : int, augmentations : int, processed : Termtab.set}

fun split_on_demand function config split_tac =
  let
    val limit = #split_limit config
    val carrier_rule = carrier_nnf_rule ()
    val flatten = nnf_flatten carrier_rule
    val start : search_branch =
      {splits = 0, augmentations = 0, processed = Termtab.empty}
    fun node hint spent goal =
      Tactical.THEN (flatten, decide hint spent) goal
    and decide hint spent goal =
      case refutation config goal of
          SOME tactic => tactic goal
        | NONE => branch hint spent goal
    and branch hint (spent as {splits, augmentations, processed}) goal =
      case Lib.total (disj_elim_tac config) goal of
          SOME split => expand hint spent split
        | NONE =>
            (case Lib.total split_tac goal of
                 SOME split =>
                   if splits >= limit then limit_exceeded function limit
                   else
                     expand hint
                       {splits = splits + 1,
                        augmentations = augmentations,
                        processed = processed} split
               | NONE => augment hint spent goal)
    and augment hint {splits, augmentations, processed}
                (goal as (assumptions, _)) =
      let
        val (processed', facts) =
          augmentation function limit processed assumptions
      in
        (* decide has already run the refutation on this goal and been
           told NONE, and augmentation has nothing to add, so the leaf
           is exhausted: report it rather than searching it again. *)
        if null facts then exhausted function hint goal
        else if augmentations >= limit then limit_exceeded function limit
        else
          Tactical.THEN
            (Tactical.MAP_EVERY Tactic.ASSUME_TAC facts,
             Tactical.THEN
               (flatten,
                decide hint
                  {splits = splits,
                   augmentations = augmentations + 1,
                   processed = processed'})) goal
      end
    and expand hint spent (goals, validation) =
      let
        val (result, revalidation) =
          Tactical.ALLGOALS (node hint spent) goals
      in
        (result, validation o revalidation)
      end
  in
    fn hint => node hint start
  end

type linarith_config = linarithData.linarith_config
val default_config = linarithData.default_config

fun CFG_LINARITH_TAC config arguments =
  let
    val function = "CFG_LINARITH_TAC"
    val (argument_facts, argument_splits) =
      full_arguments function arguments
  in
    fn goal =>
      Tactical.THEN
        (clasetLib.INSERT_FACTS_TAC
           (linarithData.arith_facts () @ argument_facts),
         let
           val search =
             split_on_demand function config (split_tactic argument_splits)
         in
           fn inner as (_, conclusion) =>
             Tactical.THEN
               (Tactic.CCONTR_TAC,
                Tactical.THEN
                  (Tactical.TRY opposite_tac,
                   Tactical.THEN
                     (filter_relevant,
                      search (unregistered_hint conclusion)))) inner
         end) goal
  end

val LINARITH_TAC = CFG_LINARITH_TAC default_config

fun atomized_assumptions premises =
  List.concat (map (CONJUNCTS o Thm.ASSUME) premises)

fun forward_prove premises conclusion =
  let
    val premise_theorems = atomized_assumptions premises
    val premise_terms = map Thm.concl premise_theorems
    val (generalized, restore) =
      linarithReplay.generalize (premise_terms @ [conclusion])
    val (generalized_premises, generalized_conclusion) =
      Lib.front_last generalized
    val theorem =
      restore
        (linarithReplay.fwd_prove linarithData.default_config
           (map Thm.ASSUME generalized_premises)
           generalized_conclusion)
  in
    Lib.rev_itlist PROVE_HYP premise_theorems theorem
  end

fun LINARITH_PROVE tm =
  let
    val (variables, body) = boolSyntax.strip_forall tm
    val (premises, conclusion) = boolSyntax.strip_imp_only body
    (* Reported here rather than left to fwd_prove, so that a public
       entry names itself and carries the carrier hint. *)
    val theorem =
      forward_prove premises conclusion
      handle HOL_ERR _ =>
        no_proof "LINARITH_PROVE" (unregistered_hint conclusion)
    val implication = Lib.itlist Thm.DISCH premises theorem
    val result = GENL variables implication
  in
    if Term.aconv (Thm.concl result) tm then result
    else
      raise ERR "LINARITH_PROVE"
        "internal error: reconstructed theorem has the wrong conclusion"
  end

fun attempt prove tm = SOME (prove tm) handle HOL_ERR _ => NONE

(* The ladder a conversion has to climb: a decision procedure must
   answer T or F, so a term it cannot prove is offered negated before
   the failure is reported. *)
fun decide function prove tm =
  case attempt prove tm of
      SOME theorem => EQT_INTRO theorem
    | NONE =>
        (case attempt prove (boolSyntax.mk_neg tm) of
             SOME theorem => EQF_INTRO theorem
           | NONE => no_proof function (unregistered_hint tm))

fun LINARITH_CONV tm = decide "LINARITH_CONV" LINARITH_PROVE tm

(* forward_prove atomises its premise terms itself, so the context
   theorems only have to be discharged against the result. *)
fun context_forward theorems conclusion =
  let
    val theorem = forward_prove (map Thm.concl theorems) conclusion
  in
    Lib.rev_itlist PROVE_HYP theorems theorem
  end

(* What the result cache is keyed on, and the test CTXT_LINARITH opens
   with.  A doubly negated relation is admitted because it is the
   second rung of the ladder below asked about a negated one: ~~(x <= y)
   decomposes nowhere itself, while the question it asks -- is x <= y
   provable? -- is one the procedure answers. *)
fun cache_check tm =
  same_type (Term.type_of tm) Type.bool andalso
  (linarithDecomp.is_relevant tm orelse
   Term.aconv tm boolSyntax.F orelse
   (case Lib.total boolSyntax.dest_neg tm of
        SOME body => linarithDecomp.is_relevant body
      | NONE => false))

(* The cached procedure answers one question, "is tm provable from the
   context?", rather than climbing the T/F ladder itself.  The ladder is
   climbed a rung at a time by CACHED_LINARITH below, each rung its own
   cache question, and that is what lets the solver ask the first rung
   alone: a side-condition solver has no use for a disproof, and asking
   for one here spent a whole second refutation whose only possible
   products were a failure and a |- tm = F that EQT_ELIM could only turn
   into an error.

   Splitting the rungs is also what keeps the cache sound under that
   asymmetry.  RCACHE records failures as well as successes, so a rung
   the solver ran and lost is recorded against that rung's own term; the
   ladder's second rung is a different term and so a different key, and
   is never answered out of the first rung's recorded failure. *)
fun CTXT_LINARITH theorems tm =
  if not (cache_check tm) then
    raise ERR "CTXT_LINARITH" "not applicable"
  else
    case attempt (context_forward theorems) tm of
        SOME theorem => EQT_INTRO theorem
      | NONE => no_proof "CTXT_LINARITH" (unregistered_hint tm)

(* The atoms in order of first occurrence, the bound variables aside.
   Both the set already collected and the binders in scope are keyed
   sets, for the reason distinct_thms is one: this walks a whole term
   once per cache lookup. *)
fun add_atom bound atom (collected as (seen, atoms)) =
  if Termtab.defined bound atom orelse Termtab.defined seen atom then
    collected
  else (Termtab.insert_set atom seen, atom :: atoms)

fun linarith_vars tm =
  let
    fun add_side bound (items, collected) =
      List.foldl
        (fn ((atom, _), result) => add_atom bound atom result)
        collected items
    fun recurse bound collected tm =
      case linarithDecomp.decomp tm of
          SOME (linarithSolve.Decomp {lhs, rhs, ...}) =>
            add_side bound (rhs, add_side bound (lhs, collected))
        | NONE =>
            (case shape_of tm of
                 NEG body => recurse bound collected body
               | CONJ (left, right) =>
                   recurse bound (recurse bound collected left) right
               | DISJ (left, right) =>
                   recurse bound (recurse bound collected left) right
               | IMP (left, right) =>
                   recurse bound (recurse bound collected left) right
               | FORALL (variable, body) =>
                   recurse (Termtab.insert_set variable bound) collected
                     body
               | EXISTS (variable, body) =>
                   recurse (Termtab.insert_set variable bound) collected
                     body
               | EQUIV _ => collected
               | ATOM => collected)
  in
    List.rev (#2 (recurse Termtab.empty (Termtab.empty, []) tm))
  end

val (unguarded_cached_linarith, linarith_cache) =
  Cache.RCACHE {capacity = 2000, per_key_cap = 50}
    (linarith_vars, cache_check, CTXT_LINARITH)

fun clear_linarith_caches () = Cache.clear_cache linarith_cache

(* The result cache is derived from the instance and injection
   registries exactly as the carrier rewrites and the split tactic
   above are, and it is the one derivation that records failures: a
   goal no proof was found for under one registry can be provable under
   the next, and RCACHE answers a repeat of it from the recorded
   failure without consulting the procedure again.  So it is dropped
   when the registries move, by the same generation compare the other
   two pay.

   The [arith] table needs no entry here.  The entry point that reads
   it assumes its facts into the context it hands the cache, so a
   change to the table is a change of context, which is what RCACHE
   already decides staleness by.  Nor does [arith_split]: the cached
   procedure is the forward one, which does no operator splitting. *)
val discard_stale_results =
  linarithData.memo (fn () => clear_linarith_caches ())

fun cached_prove context tm =
  (discard_stale_results (); unguarded_cached_linarith context tm)

fun contains_forall sense tm =
  case shape_of tm of
      NEG body => contains_forall (not sense) body
    | CONJ (left, right) =>
        contains_forall sense left orelse contains_forall sense right
    | DISJ (left, right) =>
        contains_forall sense left orelse contains_forall sense right
    | IMP (left, right) =>
        contains_forall (not sense) left orelse
        contains_forall sense right
    | FORALL (_, body) => sense orelse contains_forall sense body
    | EXISTS (_, body) => not sense orelse contains_forall sense body
    | EQUIV _ => false
    | ATOM => false

fun admissible theorem =
  let
    val conclusion = Thm.concl theorem
  in
    (not (null (Thm.hyp theorem)) orelse
     null (Term.free_vars conclusion)) andalso
    not (contains_forall true conclusion) andalso
    linarithDecomp.is_relevant conclusion
  end

(* The [arith] table split into literals, and each literal assumed.
   Both are a pure function of the table, so they are derived once per
   state of it rather than once per term -- the trade the carrier
   rewrites and the split tactic above make against the registry, and
   the one that matters most here, because the reducer below is offered
   every boolean subterm of a simplification and would otherwise pay a
   kernel inference per fact for each.

   The table's own theorems are the key, compared by pointer: the table
   is a value behind an Sref, so an entry stays the same object until
   something replaces it, and a table rebuilt into equal but fresh
   theorems recomputes rather than answering out of the old one.  That
   is a key the caller brings and no equality type, so this is
   keyed_memo rather than one of the generation memos above.

   Assuming the table is also what tells the result cache that the
   table has moved -- a fact of it is a hypothesis of the context, and
   context is what RCACHE decides staleness by -- so the memo has to
   track the table exactly, which is what a key that is the facts
   themselves does. *)
val arith_envelope =
  linarithData.keyed_memo (Lib.list_eq (Lib.curry Portable.pointer_eq))
    (fn facts =>
      let
        val literals = List.concat (map CONJUNCTS facts)
      in
        (literals, map (Thm.ASSUME o Thm.concl) literals)
      end)

(* Give dynamic [arith] facts assumption-shaped cache identities.  Their
   original proofs remove those identities from the conversion result,
   which is the half of the envelope that is per result rather than per
   table state, and so is the half that stays here.

   cache_check is the same test CTXT_LINARITH opens with, so a term it
   rejects is declined before the table is read at all.  Asking it
   first is what keeps the reducer from carrying the [arith] context
   around every boolean subterm the arithmetic has no row for. *)
fun cached_with_arith context tm =
  if not (cache_check tm) then cached_prove context tm
  else
    let
      val (facts, assumed) =
        arith_envelope (linarithData.arith_facts ())
      val theorem = cached_prove (context @ assumed) tm
    in
      Lib.rev_itlist PROVE_HYP facts theorem
    end

(* The ladder of decide, climbed with a cache question per rung: a
   conversion must answer T or F, so a term the first rung leaves
   unproved is offered negated before the failure is reported.  F is the
   contradictory-context case and needs no second rung, and gets none:
   ~F is a term cache_check declines, so the rung is refused before any
   search is spent on it.  The failure reported is the first rung's, so
   that the hint names the term the caller asked about. *)
fun CACHED_LINARITH context tm =
  case attempt (cached_with_arith context) tm of
      SOME equation => equation
    | NONE =>
        (case attempt (cached_with_arith context)
                (boolSyntax.mk_neg tm) of
             SOME equation => EQF_INTRO (EQT_ELIM equation)
           | NONE => no_proof "CTXT_LINARITH" (unregistered_hint tm))

val LINARITH_REDUCER =
  let
    exception CTXT of thm list
    fun get_context e = (raise e) handle CTXT value => value
    fun addcontext (context, newtheorems) =
      let
        val admitted =
          List.filter admissible
            (List.concat (map CONJUNCTS newtheorems))
      in
        CTXT (admitted @ get_context context)
      end
  in
    Traverse.REDUCER
      {name = SOME "LINARITH_DP",
       addcontext = addcontext,
       apply = fn args =>
         CACHED_LINARITH (get_context (#context args)),
       initial = CTXT []}
  end

val LINARITH_ss =
  simpLib.named_merge_ss "LINARITH"
    [simpLib.SSFRAG
       {name = SOME "LINARITH_DP",
        convs = [], rewrs = [], congs = [], filter = NONE,
        ac = [], dprocs = [LINARITH_REDUCER]}]

(* Whether a context could refute F at all.  Every row the procedure
   builds comes from a premise it can decompose, and the nonnegativity
   rows come from the atoms of those premises, so a context with no
   arithmetic in it yields no rows, and no rows refute nothing.  The
   test is shell_relevant, the one the search itself filters assumptions
   by, applied through the connectives a premise is atomized along: it
   answers yes to strictly more than the procedure can use -- any
   boolean equation, any term with a subterm at a registered type -- so
   what it declines is declined for cause.  The [arith] table is part of
   the context cached_with_arith asks about, so it is asked about here
   too. *)
fun refutable_context theorems =
  List.exists (shell_relevant o Thm.concl) theorems

(* Mirrors Isabelle's solver setup at lin_arith.ML:949.  Arithmetic side
   conditions share the reducer's cache; cached_with_arith is a
   conversion, so EQT_ELIM turns its |- tm = T into the |- tm a solver
   must return, and its HOL_ERR reports an undischarged condition.  Only
   the provability of the condition is asked: a solver has no use for
   the |- tm = F the reducer's second rung would go looking for.

   A condition the guard rejects is one the arithmetic has no row for
   -- MEM x l, P y, an equation at an unregistered type -- and the
   procedure adds the negated conclusion as one more row, so refuting
   it alongside the context is refuting the context alone.  The only
   way such a condition is discharged is therefore from a contradictory
   context, which is what asking for F and applying CONTR says, and
   asking for F asks through the cache, since F is the other term the
   guard admits.  Traverse offers the solver every side condition of
   every conditional rewrite, so that question is worth asking only of a
   context that could answer it. *)
val linarith_solver : Traverse.ssolver =
  {name = "lin_arith",
   solve = fn {context_thms, ...} => fn tm =>
     if cache_check tm then EQT_ELIM (cached_with_arith context_thms tm)
     else if refutable_context context_thms orelse
             refutable_context (linarithData.arith_facts ())
     then
       CONTR tm
         (EQT_ELIM (cached_with_arith context_thms boolSyntax.F))
     else raise ERR "lin_arith" "no arithmetic in the context"}

(* num is registered here, not at the foot of linarithNum the way the
   int, real and rat instances register themselves.  Those live in
   instances/, which a client loads by naming the structure it wants, so
   the load is that client's request for the carrier; num is the carrier
   this library ships with and has to be there for everyone who opens
   it.  This is also the library's only mention of linarithNum, so it is
   what links the structure in at all: registering from linarithNum
   instead leaves num unregistered for a client that names only
   linarithLib. *)
val _ = linarithData.register_instance linarithNum.instance

end
