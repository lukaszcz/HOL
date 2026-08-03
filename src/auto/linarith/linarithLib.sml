structure linarithLib :> linarithLib =
struct

open Abbrev HolKernel Drule

val ERR = mk_HOL_ERR "linarithLib"

val load_hint =
  " (load intLinarith / realLinarith / ratLinarith?)"

fun same_type left right = Type.compare (left, right) = EQUAL

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

fun check_registered function tm =
  case relation_carrier tm of
      NONE => ()
    | SOME ty =>
        (case linarithData.instance_for ty of
             SOME _ => ()
           | NONE =>
               raise ERR function
                 ("no linarith instance for " ^
                  Parse.type_to_string ty ^ load_hint))

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

fun first_marker _ [] = NONE
  | first_marker theorem ((dest, name) :: rest) =
      case dest theorem of
          SOME _ => SOME name
        | NONE => first_marker theorem rest

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

fun simple_argument function theorem =
  if markerLib.is_Split theorem then
    let
      val split = markerLib.destSplit theorem
      val _ =
        linarithData.check_asm_split function
          "Split theorem (expected P-form)" split
    in
      reject function "Split"
    end
  else plain_argument function theorem

fun full_arguments function arguments =
  let
    fun add (theorem, (facts, splits)) =
      if markerLib.is_Split theorem then
        let
          val split = markerLib.destSplit theorem
          val _ =
            linarithData.check_asm_split function
              "Split theorem (expected P-form)" split
        in
          (facts, split :: splits)
        end
      else (plain_argument function theorem :: facts, splits)
  in
    foldl add ([], []) arguments
  end

(* A goal the arithmetic cannot refute is not yet a failure: the search
   splits it and asks again.  So finding the certificate is separate from
   reporting that there is none, and only a caller that has run out of
   splits pays for the diagnostics. *)
fun refutation config (assumptions, conclusion) =
  SOME (linarithReplay.refute config assumptions conclusion)
  handle Feedback.HOL_ERR error =>
    if Feedback.top_function_of error = "refute" then NONE
    else raise Feedback.HOL_ERR error

(* The diagnostics report the goal as preprocessing left it, so they stay
   on this side of the interface; the failure is reported under the
   caller's name because the public entries report their own. *)
fun core function config (goal as (assumptions, conclusion)) =
  case refutation config goal of
      SOME tactic => tactic goal
    | NONE =>
        (linarithData.trace_terms 2 "preprocessed assumptions" assumptions;
         linarithData.trace_terms 2 "preprocessed conclusion" [conclusion];
         raise ERR function "linear arithmetic found no proof")

fun SIMPLE_LINARITH_TAC arguments =
  let
    val function = "SIMPLE_LINARITH_TAC"
    val facts =
      linarithData.arith_facts () @
      map (simple_argument function) arguments
  in
    Tactical.THEN
      (clasetLib.INSERT_FACTS_TAC facts,
       fn goal as (_, conclusion) =>
         (check_registered function conclusion;
          core function linarithData.default_config goal))
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
   arrives from the registry rather than being named. *)
fun carrier_nnf_rewrites () =
  List.concat (map #nnf_rules (linarithData.all_instances ()))

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
   because SUB_EQ_0 and its kin produce relations already in NNF. *)
fun nnf_flatten goal =
  let
    val carrier_rule = Rewrite.REWRITE_RULE (carrier_nnf_rewrites ())
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

fun distinct_thms theorems =
  let
    fun add (theorem, result) =
      if List.exists
           (fn old => Term.aconv (Thm.concl theorem) (Thm.concl old))
           result
      then result
      else theorem :: result
  in
    List.rev (foldl add [] theorems)
  end

fun split_rules extra =
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

fun augmentation_round processed assumptions =
  let
    val candidates = List.concat (map decomp_atoms assumptions)
    fun inspect (candidate, (seen, facts)) =
      if List.exists (Term.aconv candidate) seen then (seen, facts)
      else (candidate :: seen, facts_for candidate @ facts)
    val (seen, facts) = foldl inspect (processed, []) candidates
    val unique = distinct_thms facts
    fun known theorem =
      List.exists (Term.aconv (Thm.concl theorem)) assumptions
    val novel = List.filter (not o known) unique
  in
    (seen, novel)
  end

fun augment_atom_facts function limit =
  let
    fun loop processed rounds (goal as (assumptions, _)) =
      let
        val (processed', facts) =
          augmentation_round processed assumptions
      in
        if null facts then Tactical.TRY opposite_tac goal
        else if rounds >= limit then limit_exceeded function limit
        else
          Tactical.THEN
            (Tactical.MAP_EVERY Tactic.ASSUME_TAC facts,
             loop processed' (rounds + 1)) goal
      end
  in
    loop [] 0
  end

(* Whether a disjunct can be added to the literals already assumed
   without the arithmetic refuting the result.  A disjunct that cannot
   is a case the split would close immediately, so counting them
   measures how much of a disjunction is still live. *)
fun consistent config literals disjunct =
  case linarithSolve.prove config linarithDecomp.decomp
         linarithDecomp.is_nonnegative (disjunct :: literals)
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
    fun score disjunction =
      (List.length
         (List.filter (consistent config literals)
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
   splitting would not finish.  It is tried once per goal, after the
   case splits have run out and before the goal is declared
   unrefutable.  Coming last is also what keeps it from missing atoms:
   nothing reaches it with a disjunction still standing, so the atoms
   it collects from an assumption are the atoms of a literal.

   split_limit keeps its meaning of an operator-splitting and
   augmentation bound, now counted along a branch of the search rather
   than along a preprocessing chain.  Disjunction elimination needs no
   bound: every step of it consumes a disjunction, and only an operator
   split puts one back. *)
fun split_on_demand function config split_tac =
  let
    val limit = #split_limit config
    fun node splits goal =
      Tactical.THEN (nnf_flatten, decide false splits) goal
    and decide augmented splits goal =
      case refutation config goal of
          SOME tactic => tactic goal
        | NONE => branch augmented splits goal
    and branch augmented splits goal =
      case Lib.total (disj_elim_tac config) goal of
          SOME split => expand splits split
        | NONE =>
            (case Lib.total split_tac goal of
                 SOME split =>
                   if splits >= limit then limit_exceeded function limit
                   else expand (splits + 1) split
               | NONE => augment augmented splits goal)
    and augment augmented splits goal =
      if augmented then core function config goal
      else
        Tactical.THEN
          (augment_atom_facts function limit,
           Tactical.THEN (nnf_flatten, decide true splits)) goal
    and expand splits (goals, validation) =
      let
        val (result, revalidation) =
          Tactical.ALLGOALS (node splits) goals
      in
        (result, validation o revalidation)
      end
  in
    node 0
  end

type linarith_config = linarithData.linarith_config
val default_config = linarithData.default_config

fun CFG_LINARITH_TAC config arguments =
  let
    val function = "CFG_LINARITH_TAC"
    val (argument_facts, argument_splits) =
      full_arguments function arguments
    val facts =
      linarithData.arith_facts () @ List.rev argument_facts
    val rules = split_rules (List.rev argument_splits)
    val split_tac = splitLib.SPLIT_TAC rules
    val search = split_on_demand function config split_tac
  in
    Tactical.THEN
      (clasetLib.INSERT_FACTS_TAC facts,
       fn goal as (_, conclusion) =>
         (check_registered function conclusion;
          Tactical.THEN
            (Tactic.CCONTR_TAC,
             Tactical.THEN (filter_relevant, search)) goal))
  end

val LINARITH_TAC = CFG_LINARITH_TAC default_config

fun atomized_assumptions premises =
  List.concat (map (CONJUNCTS o Thm.ASSUME) premises)

fun forward_prove premises conclusion =
  let
    val premise_theorems = atomized_assumptions premises
    val premise_terms = map Thm.concl premise_theorems
    val terms = premise_terms @ [conclusion]
    fun prove generalized =
      let
        val generalized_premises =
          List.take (generalized, List.length premise_terms)
        val generalized_conclusion = List.last generalized
      in
        linarithReplay.fwd_prove linarithData.default_config
          (map Thm.ASSUME generalized_premises)
          generalized_conclusion
      end
    val theorem = linarithReplay.generalize terms prove
  in
    List.foldl
      (fn (premise, result) => PROVE_HYP premise result)
      theorem premise_theorems
  end

fun LINARITH_PROVE tm =
  let
    val (variables, body) = boolSyntax.strip_forall tm
    val (premises, conclusion) = boolSyntax.strip_imp_only body
    val _ = check_registered "LINARITH_PROVE" conclusion
    val theorem = forward_prove premises conclusion
    val implication =
      List.foldr (fn (premise, result) => Thm.DISCH premise result)
        theorem premises
    val result = GENL variables implication
  in
    if Term.aconv (Thm.concl result) tm then result
    else
      raise ERR "LINARITH_PROVE"
        "internal error: reconstructed theorem has the wrong conclusion"
  end

fun attempt prove tm = SOME (prove tm) handle HOL_ERR _ => NONE

fun LINARITH_CONV tm =
  let
    val _ = check_registered "LINARITH_CONV" tm
  in
    case attempt LINARITH_PROVE tm of
        SOME theorem => EQT_INTRO theorem
      | NONE =>
          let
            val negated = boolSyntax.mk_neg tm
          in
            case attempt LINARITH_PROVE negated of
                SOME theorem => EQF_INTRO theorem
              | NONE =>
                  raise ERR "LINARITH_CONV"
                    "linear arithmetic could neither prove nor disprove term"
          end
  end

(* forward_prove atomises its premise terms itself, so the context
   theorems only have to be discharged against the result. *)
fun context_forward theorems conclusion =
  let
    val theorem = forward_prove (map Thm.concl theorems) conclusion
  in
    List.foldl
      (fn (premise, result) => PROVE_HYP premise result)
      theorem theorems
  end

fun CTXT_LINARITH theorems tm =
  if Type.compare (Term.type_of tm, Type.bool) <> EQUAL orelse
     (not (linarithDecomp.is_relevant tm) andalso
      not (Term.aconv tm boolSyntax.F))
  then raise ERR "CTXT_LINARITH" "not applicable"
  else
    let
      fun prove goal = context_forward theorems goal
    in
      case attempt prove tm of
          SOME theorem => EQT_INTRO theorem
        | NONE =>
            if Term.aconv tm boolSyntax.F then
              raise ERR "CTXT_LINARITH" "linear arithmetic found no proof"
            else
              (case attempt prove (boolSyntax.mk_neg tm) of
                   SOME theorem => EQF_INTRO theorem
                 | NONE =>
                     raise ERR "CTXT_LINARITH"
                       "linear arithmetic could neither prove nor disprove \
                       \term")
    end

fun add_atom bound atom atoms =
  if List.exists (Term.aconv atom) bound orelse
     List.exists (Term.aconv atom) atoms
  then atoms
  else atom :: atoms

fun linarith_vars tm =
  let
    fun add_side bound (items, atoms) =
      List.foldl
        (fn ((atom, _), result) => add_atom bound atom result)
        atoms items
    fun recurse bound atoms tm =
      case linarithDecomp.decomp tm of
          SOME (linarithSolve.Decomp {lhs, rhs, ...}) =>
            add_side bound (rhs, add_side bound (lhs, atoms))
        | NONE =>
            (case shape_of tm of
                 NEG body => recurse bound atoms body
               | CONJ (left, right) =>
                   recurse bound (recurse bound atoms left) right
               | DISJ (left, right) =>
                   recurse bound (recurse bound atoms left) right
               | IMP (left, right) =>
                   recurse bound (recurse bound atoms left) right
               | FORALL (variable, body) =>
                   recurse (variable :: bound) atoms body
               | EXISTS (variable, body) =>
                   recurse (variable :: bound) atoms body
               | EQUIV _ => atoms
               | ATOM => atoms)
  in
    List.rev (recurse [] [] tm)
  end

fun cache_check tm =
  Type.compare (Term.type_of tm, Type.bool) = EQUAL andalso
  (linarithDecomp.is_relevant tm orelse Term.aconv tm boolSyntax.F)

val (CACHED_LINARITH, linarith_cache) =
  Cache.RCACHE {capacity = 2000, per_key_cap = 50}
    (linarith_vars, cache_check, CTXT_LINARITH)

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

(* Give dynamic [arith] facts assumption-shaped cache identities.  Their
   original proofs remove those identities from the conversion result. *)
fun cached_with_arith context tm =
  let
    val facts =
      List.concat (map CONJUNCTS (linarithData.arith_facts ()))
    val assumed = map (Thm.ASSUME o Thm.concl) facts
    val theorem = CACHED_LINARITH (context @ assumed) tm
  in
    List.foldl
      (fn (fact, result) => PROVE_HYP fact result)
      theorem facts
  end

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
         cached_with_arith (get_context (#context args)),
       initial = CTXT []}
  end

val LINARITH_ss =
  simpLib.named_merge_ss "LINARITH"
    [simpLib.SSFRAG
       {name = SOME "LINARITH_DP",
        convs = [], rewrs = [], congs = [], filter = NONE,
        ac = [], dprocs = [LINARITH_REDUCER]}]

(* Mirrors Isabelle's solver setup at lin_arith.ML:949.  Arithmetic side
   conditions share the reducer's cache; cached_with_arith is a
   conversion, so EQT_ELIM turns its |- tm = T into the |- tm a solver
   must return, and its HOL_ERR on a |- tm = F correctly reports the
   refuted condition as undischarged.  Terms the guard rejects keep the
   direct forward call: they are the "contradictory context proves
   anything" case, which the cache cannot serve. *)
val linarith_solver : Traverse.ssolver =
  {name = "lin_arith",
   solve = fn {context_thms, ...} => fn tm =>
     if cache_check tm then EQT_ELIM (cached_with_arith context_thms tm)
     else
       context_forward
         (context_thms @ linarithData.arith_facts ()) tm}

fun clear_linarith_caches () = Cache.clear_cache linarith_cache

val _ = linarithData.register_instance linarithNum.instance

end
