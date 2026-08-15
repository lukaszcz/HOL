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

val search_failed = "linear arithmetic found no proof"
exception Declined of string

(* The hint travels with the search rather than being recomputed at the
   failure site: CCONTR_TAC has replaced the conclusion by F long before
   the search gives up. *)
fun no_proof function hint = raise ERR function (search_failed ^ hint)

fun decline hint = raise Declined hint

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
            (case clasetLib.marker_of plain of
                 SOME {name,...} => reject function name
               | NONE => plain)
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

   The rule is built over Rewrite.bool_rewrites rather than over
   Rewrite.implicit_rewrites, which is what Rewrite.REWRITE_RULE would
   read.  What the pass wants beyond the registry's rules is the
   propositional tidy-up their output asks for, and that is a fixed
   set; the implicit set is neither fixed nor anything this layer
   chose.  A theory loaded halfway through a session adds to it
   (pairLib, listScript) or replaces it wholesale (integerScript), so
   reading it would decide the same goal one way or the other according
   to which theories a session had loaded and in what order -- and
   REWRITE_RULE reads it where the partial application is built, so the
   memo below would additionally freeze whichever state that was, and
   the order that decided a goal would be the order of the loads
   against the first call rather than against the goal.

   With that, both the rewrite list and the rule are a pure function of
   the instance registry, so they are built once per registry state
   rather than once per tactic call: the rule builds a rewrite net, and
   the net does not depend on the goal. *)
fun carrier_nnf_rewrites () =
  List.concat (map #nnf_rules (linarithData.all_instances ()))

val carrier_nnf_rule =
  linarithData.memo
    (fn () =>
      Rewrite.GEN_REWRITE_RULE Conv.TOP_DEPTH_CONV Rewrite.bool_rewrites
        (carrier_nnf_rewrites ()))

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
  in
    (* splitLib.split_forms answers the rules already analysed, so a
       source theorem is walked once here rather than once to ask
       whether it splits an assumption, once again to derive the form
       that does, and once more when the tactic below is built. *)
    List.concat (map splitLib.split_forms source)
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
   the wrong one of the two theorems.  So a caller that passed splits
   gets a memo of its own instead of the shared one: the rules are a
   pure function of the same two sources once that caller's own
   arguments are fixed, which they are as soon as the tactic value is
   built, and it is the tactic value the memo cell belongs to.  Without
   it a tactic applied to twenty subgoals derives and analyses the
   whole rule set twenty times, since the derivation has to happen
   where the tactic is applied rather than where it is built. *)
val cached_split_tac =
  linarithData.memo_with_splits
    (fn () => splitLib.SPLIT_RULE_TAC (compute_split_rules []))

fun split_tactic [] = cached_split_tac
  | split_tactic extra =
      linarithData.memo_with_splits
        (fn () => splitLib.SPLIT_RULE_TAC (compute_split_rules extra))

fun decomp_atoms tm =
  case linarithDecomp.decomp tm of
      NONE => []
    | SOME (linarithSolve.Decomp {lhs, rhs, ...}) =>
        map #1 (lhs @ rhs)

(* splitLib deliberately chooses the first applicable assumption.  Put
   assumptions connected to the current arithmetic context first: an
   operator whose ordinary atoms already occur elsewhere is more likely
   to expose a contradiction before independent operators are split.  Ties
   retain the incoming order, and only the assumption order changes. *)
fun connected_split_goal (assumptions, conclusion) =
  let
    fun atoms assumption =
      linarithData.distinct_by Term.compare I (decomp_atoms assumption)
    val entries = map (fn assumption => (assumption, atoms assumption))
      assumptions
    fun occurrence_count atom =
      List.foldl
        (fn ((_, entry_atoms), count) =>
           if List.exists (Term.aconv atom) entry_atoms then count + 1
           else count)
        0 entries
    fun score (_, entry_atoms) =
      List.foldl
        (fn (atom, total) =>
           Int.max (0, occurrence_count atom - 1) + total)
        0 entry_atoms
    val scored = map (fn entry => (score entry, entry)) entries
    fun insert item [] = [item]
      | insert (item as (item_score, _))
          ((first as (first_score, _)) :: rest) =
          if item_score >= first_score then item :: first :: rest
          else first :: insert item rest
    val ordered = List.foldr (fn (item, result) => insert item result)
      [] scored
  in
    (map (fn (_, (assumption, _)) => assumption) ordered, conclusion)
  end

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

(* Eliminate the first disjunctive assumption.  The caller orders the
   assumptions by arithmetic connectedness before reaching this function.
   Each child is refuted immediately, so running the solver here as well
   would duplicate the dominant work at every branch. *)
fun disj_elim_tac (assumptions, conclusion) =
  let
    val (disjunctions, _) =
      List.partition boolSyntax.is_disj assumptions
    val _ =
      if List.null disjunctions then
        raise ERR "disj_elim_tac" "no disjunctive assumption"
      else ()
    val chosen = hd disjunctions
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

(* A P-form operator split commonly leaves a complementary pair of
   implications.  Flattening them independently turns one binary sign
   choice into as many as four propositional cases.  When arithmetic can
   prove that the negation of one guard implies the other, branch on the
   first guard directly and carry the corresponding consequence into each
   child.  The validation below reconstructs both consequences from the
   original implications, so this is only a search compression.

   A recurrence reaches the same guard pair under many partial sign
   contexts.  The conjunction of the two guards is its canonical term key;
   both proofs and failures are memoized for the lifetime of one search. *)
fun complementary_implications_tac config cache
                                      (assumptions, conclusion) =
  let
    fun implication assumption =
      case Lib.total boolSyntax.dest_imp_only assumption of
          SOME (guard, consequence) =>
            SOME (assumption, guard, consequence)
        | NONE => NONE
    val implications = List.mapPartial implication assumptions

    fun complement left_guard right_guard =
      let
        val key = boolSyntax.mk_conj (left_guard, right_guard)
        val negated = boolSyntax.mk_neg left_guard
        fun prove () =
          SOME
            (linarithReplay.fwd_prove config
               [Thm.ASSUME negated] right_guard)
          handle Feedback.HOL_ERR _ => NONE
        val answer =
          case Termtab.lookup (!cache) key of
              SOME cached => cached
            | NONE =>
                let
                  val computed = prove ()
                  val _ = cache := Termtab.update (key, computed) (!cache)
                in
                  computed
                end
      in
        Option.map (fn theorem => (negated, theorem)) answer
      end

    fun pair_with _ [] = NONE
      | pair_with (left as (_, left_guard, _)) (right :: rest) =
          let
            val (_, right_guard, _) = right
          in
            case complement left_guard right_guard of
                SOME proof => SOME (left, right, proof)
              | NONE => pair_with left rest
          end
    fun find_pair [] = NONE
      | find_pair (left :: rest) =
          (case pair_with left rest of
               SOME pair => SOME pair
             | NONE => find_pair rest)

    val ((left_assumption, left_guard, left_consequence),
         (right_assumption, _, right_consequence),
         (negated_guard, right_guard_theorem)) =
      case find_pair implications of
          SOME pair => pair
        | NONE =>
            raise ERR "complementary_implications_tac"
              "no complementary implication pair"
    fun chosen assumption =
      Term.aconv assumption left_assumption orelse
      Term.aconv assumption right_assumption
    val common = List.filter (not o chosen) assumptions
    val goals =
      [(common @ [left_guard, left_consequence], conclusion),
       (common @ [negated_guard, right_consequence], conclusion)]
    val excluded_middle =
      SPEC left_guard boolTheory.EXCLUDED_MIDDLE
    val left_consequence_theorem =
      MP (Thm.ASSUME left_assumption) (Thm.ASSUME left_guard)
    val right_consequence_theorem =
      MP (Thm.ASSUME right_assumption) right_guard_theorem
    fun justify [left_case, right_case] =
          Thm.DISJ_CASES excluded_middle
            (PROVE_HYP left_consequence_theorem left_case)
            (PROVE_HYP right_consequence_theorem right_case)
      | justify _ =
          raise ERR "complementary_implications_tac"
            "invalid justification"
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

type search_stats =
  {nodes : int,
   refutations : int,
   disjunction_splits : int,
   operator_splits : int,
   augmentations : int}

val empty_search_stats : search_stats =
  {nodes = 0, refutations = 0,
   disjunction_splits = 0, operator_splits = 0,
   augmentations = 0}

val last_search_stats_ref = ref empty_search_stats

fun last_search_stats () = !last_search_stats_ref

datatype search_event =
    Node
  | Refutation
  | DisjunctionSplit
  | OperatorSplit
  | Augmentation

fun note_search event =
  let
    val {nodes, refutations, disjunction_splits,
         operator_splits, augmentations} = !last_search_stats_ref
    fun increment selected value =
      if event = selected then value + 1 else value
  in
    last_search_stats_ref :=
      {nodes = increment Node nodes,
       refutations = increment Refutation refutations,
       disjunction_splits =
         increment DisjunctionSplit disjunction_splits,
       operator_splits = increment OperatorSplit operator_splits,
       augmentations = increment Augmentation augmentations}
  end

fun split_on_demand function config split_tac =
  let
    val limit = #split_limit config
    val carrier_rule = carrier_nnf_rule ()
    val flatten = nnf_flatten carrier_rule
    val complement_cache =
      ref (Termtab.empty : thm option Termtab.table)
    val start : search_branch =
      {splits = 0, augmentations = 0, processed = Termtab.empty}

    (* One remaining operator cannot multiply later sign choices, so it
       keeps the established splitter.  If the result of the current split
       still contains a splittable operator, there were at least two pending
       and the generic implication expansion would introduce a third live
       case before the next operator.  That branch-count boundary is the
       threshold for the direct binary path. *)
    fun has_successor_split (goals, _) =
      List.exists (Lib.can split_tac) goals

    fun node hint spent goal =
      (note_search Node;
       Tactical.THEN (flatten, decide hint spent) goal)
    and open_node hint spent goal =
      (note_search Node;
       case Lib.total
              (complementary_implications_tac config complement_cache) goal of
           SOME split =>
             (note_search DisjunctionSplit;
              expand node hint spent split)
         | NONE => Tactical.THEN (flatten, branch hint spent) goal)
    and decide hint spent goal =
      (note_search Refutation;
       case refutation config goal of
          SOME tactic => tactic goal
        | NONE => branch hint spent goal)
    and branch hint (spent as {splits, augmentations, processed}) goal =
      case Lib.total disj_elim_tac (connected_split_goal goal) of
          SOME split =>
            (note_search DisjunctionSplit;
             expand node hint spent split)
        | NONE =>
            (case Lib.total split_tac (connected_split_goal goal) of
                 SOME split =>
                   if splits >= limit then limit_exceeded function limit
                   else
                     let
                       val continue =
                         if has_successor_split split then open_node else node
                     in
                       note_search OperatorSplit;
                       expand continue hint
                         {splits = splits + 1,
                          augmentations = augmentations,
                          processed = processed} split
                     end
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
          (note_search Augmentation;
           Tactical.THEN
             (Tactical.MAP_EVERY Tactic.ASSUME_TAC facts,
              Tactical.THEN
                (flatten,
                 decide hint
                   {splits = splits,
                    augmentations = augmentations + 1,
                    processed = processed'})) goal)
      end
    and expand continue hint spent (goals, validation) =
      let
        val (result, revalidation) =
          Tactical.ALLGOALS (continue hint spent) goals
      in
        (result, validation o revalidation)
      end
  in
    fn hint => fn goal =>
      (last_search_stats_ref := empty_search_stats;
       node hint start goal)
  end

type linarith_config = linarithData.linarith_config
val default_config = linarithData.default_config

fun CFG_LINARITH_TAC config arguments =
  let
    val function = "CFG_LINARITH_TAC"
    val (argument_facts, argument_splits) =
      full_arguments function arguments
    val split_tac = split_tactic argument_splits
  in
    fn goal =>
      Tactical.THEN
        (clasetLib.INSERT_FACTS_TAC
           (linarithData.arith_facts () @ argument_facts),
         let
           val search =
             split_on_demand function config (split_tac ())
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
    val generalized_theorems = map Thm.ASSUME generalized_premises
    val generalized_theorem =
      case
        linarithReplay.refute linarithData.default_config
          generalized_premises generalized_conclusion
      of
          NONE => decline ""
        | SOME tactic =>
            let
              val (goals,validation) =
                tactic (generalized_premises,generalized_conclusion)
              val _ =
                if null goals then ()
                else raise ERR "forward_prove" "replay left a subgoal open"
            in
              Lib.rev_itlist PROVE_HYP generalized_theorems
                (validation [])
            end
    val theorem = restore generalized_theorem
  in
    Lib.rev_itlist PROVE_HYP premise_theorems theorem
  end

fun linarith_prove tm =
  let
    val (variables, body) = boolSyntax.strip_forall tm
    val (premises, conclusion) = boolSyntax.strip_imp_only body
    (* A search that found nothing is reported here rather than left to
       fwd_prove, so that a public entry names itself and carries the
       carrier hint.  Nothing else is: a malformed instance fails
       somewhere in the replay machinery, and reporting that as a
       refusal makes a provable goal look unprovable to the one person
       who could fix it. *)
    val theorem = forward_prove premises conclusion
    val implication = Lib.itlist Thm.DISCH premises theorem
    val result = GENL variables implication
  in
    if Term.aconv (Thm.concl result) tm then result
    else
      raise ERR "LINARITH_PROVE"
        "internal error: reconstructed theorem has the wrong conclusion"
  end

fun LINARITH_PROVE tm =
  linarith_prove tm
  handle Declined _ =>
    let
      val (_,body) = boolSyntax.strip_forall tm
      val (_,conclusion) = boolSyntax.strip_imp_only body
    in
      no_proof "LINARITH_PROVE" (unregistered_hint conclusion)
    end

(* NONE is "asked and refused", which is the only failure a rung of the
   ladders below is entitled to treat as an answer: a rung that fails
   because an instance is malformed has not answered the question, and
   letting that stand for "no" would send the caller up the next rung
   and report the whole term undecided under this structure's name. *)
fun attempt prove tm =
  SOME (prove tm)
  handle Declined _ => NONE

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

fun LINARITH_CONV tm = decide "LINARITH_CONV" linarith_prove tm

(* forward_prove atomises its premise terms itself, so the context
   theorems only have to be discharged against the result. *)
fun context_forward theorems conclusion =
  let
    val theorem = forward_prove (map Thm.concl theorems) conclusion
  in
    Lib.rev_itlist PROVE_HYP theorems theorem
  end

(* What the result cache is keyed on, and the test the cached procedure
   opens with.  A doubly negated relation is admitted because it is the
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
   is never answered out of the first rung's recorded failure.

   It reports under the name of the entry point it is the machinery of,
   not under one of its own: this is a private function, and a failure
   naming it names nothing the caller who reads the failure can look
   up.  Every path that reaches it comes through CACHED_LINARITH or
   through the solver, and the solver reaches it only for terms the
   guard admits, so "not applicable" is a message CACHED_LINARITH's
   ladder consumes rather than one a caller is shown. *)
fun cached_procedure theorems tm =
  if not (cache_check tm) then decline ""
  else
    case attempt (context_forward theorems) tm of
        SOME theorem => EQT_INTRO theorem
      | NONE => decline (unregistered_hint tm)

(* RCACHE calls its procedure through Lib.total, because its ordinary
   clients use every exception as a negative cache answer.  Linarith's
   distinction is narrower: only declined errors are negative answers;
   every other exception diagnoses a malformed registered extension.
   A dynamically scoped slot carries such an exception through
   RCACHE's total call.  Dynamic scoping keeps a custom instance that
   recursively invokes the cached entry point from overwriting its
   caller's diagnostic. *)
val cached_error_slots = ref ([] : exn option ref list)

fun remember_cached_error error =
  case !cached_error_slots of
      [] => ()
    | slot :: _ =>
        (case !slot of
             NONE => slot := SOME error
           | SOME _ => ())

fun cache_visible_procedure theorems tm =
  cached_procedure theorems tm
  handle error as Declined _ => raise error
       | error => (remember_cached_error error; raise error)

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
    (linarith_vars, cache_check, cache_visible_procedure)

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
  let
    val slot = ref (NONE : exn option)
    val outer_slots = !cached_error_slots
    fun leave () = cached_error_slots := outer_slots
    fun raise_recorded _ =
      (case !slot of
           SOME error =>
             (clear_linarith_caches (); raise error)
         | NONE => decline "")
    val _ = discard_stale_results ()
    val _ = cached_error_slots := slot :: outer_slots
    val result =
      unguarded_cached_linarith context tm
      handle error => (leave (); raise_recorded error)
    val _ = leave ()
  in
    case !slot of
        SOME error => (clear_linarith_caches (); raise error)
      | NONE => result
  end

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

   cache_check is the same test the cached procedure opens with, so a
   term it rejects is declined before the table is read at all.  Asking
   it first is what keeps the reducer from carrying the [arith] context
   around every boolean subterm the arithmetic has no row for. *)
fun cached_with_arith context tm =
  if not (cache_check tm) then decline ""
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
fun cached_linarith context tm =
  case attempt (cached_with_arith context) tm of
      SOME equation => equation
    | NONE =>
        (case attempt (cached_with_arith context)
                (boolSyntax.mk_neg tm) of
             SOME equation => EQF_INTRO (EQT_ELIM equation)
           | NONE => no_proof "CACHED_LINARITH" (unregistered_hint tm))

fun CACHED_LINARITH context tm =
  cached_linarith context tm
  handle Declined _ =>
    no_proof "CACHED_LINARITH" (unregistered_hint tm)

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
   what it declines is declined for cause.

   The answer is remembered, because the answer this guard exists to
   give is the expensive one.  List.exists stops at a yes; a no is
   reached only after every context theorem has been walked, and
   shell_relevant's ATOM leaf answers no only after find_term has
   visited every subterm and asked the registry about the type of each.
   Traverse offers the solver every side condition of every conditional
   rewrite, and the context is the traversal region's rather than the
   condition's, so the same walk would otherwise be repeated per
   condition.

   The key is the context itself, compared element-wise by pointer: it
   is what the answer is about, it arrives with the call, and it is no
   equality type, so this is keyed_memo rather than one of the
   generation memos.  A single entry suffices -- the context does not
   move between the side conditions of one region -- and the list
   final_solver_tac freshly conses out of reducer_context @
   solver_context is still hit by the pointer compare.

   The generation is in the key beside it because shell_relevant reads
   the registry, through is_relevant and through the instance_for behind
   has_registered_subterm, so the same context answers differently
   across a registration. *)
fun same_context_key (left_generation : int, left_thms)
                     (right_generation, right_thms) =
  left_generation = right_generation andalso
  Lib.list_eq (Lib.curry Portable.pointer_eq) left_thms right_thms

val refutable_for_key =
  linarithData.keyed_memo same_context_key
    (fn (_, theorems) => List.exists (shell_relevant o Thm.concl) theorems)

fun refutable_context theorems =
  refutable_for_key (linarithData.generation (), theorems)

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
   context that could answer it.

   The context asked about is the simplifier's alone, the [arith] table
   the refutation would also see notwithstanding.  The table is a set
   of theorems, so its facts hold together and refute nothing by
   themselves; every further row comes from a premise the procedure can
   decompose, and if not one context theorem carries arithmetic --
   which is what shell_relevant over-approximates, so it misses none --
   the table's rows are all there is and the question is answered
   before it is asked.  Adding the table to the guard would therefore
   never turn a refusal into a proof; what it would do is make the
   guard true at every call in a session where a single [arith] fact
   has been declared anywhere in the ancestry, which is what the
   attribute is for, and send every non-arithmetic side condition of
   every conditional rewrite under the simpsets that carry this solver
   through a contradiction search that cannot succeed.

   A table that did refute F by itself -- possible only of facts
   carrying hypotheses, which the envelope discharges again -- would be
   a self-contradictory table, and would say so at the same volume on
   every call, since neither the question nor its answer would depend
   on the condition being asked about.  That is a state to report, not
   one to spend a search per side condition rediscovering. *)
val linarith_solver : Traverse.ssolver =
  {name = "lin_arith",
   solve = fn {context_thms, ...} => fn tm =>
     (if cache_check tm then EQT_ELIM (cached_with_arith context_thms tm)
      else if refutable_context context_thms then
        CONTR tm
          (EQT_ELIM (cached_with_arith context_thms boolSyntax.F))
      else raise ERR "lin_arith" "no arithmetic in the context")
     handle Declined _ => raise ERR "lin_arith" search_failed}

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
