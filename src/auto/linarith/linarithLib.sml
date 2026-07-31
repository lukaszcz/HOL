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

fun validate_split function theorem =
  (ignore (splitLib.is_asm_split theorem)
   handle HOL_ERR _ =>
     raise ERR function "Malformed Split theorem (expected P-form)")

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
      val _ = validate_split function split
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
          val _ = validate_split function split
        in
          (facts, split :: splits)
        end
      else (plain_argument function theorem :: facts, splits)
  in
    foldl add ([], []) arguments
  end

fun core function config (assumptions, conclusion) =
  let
    val (split_neq, result) =
      linarithSolve.prove config linarithDecomp.decomp
        assumptions conclusion
  in
    case result of
        SOME justifications =>
          linarithReplay.refute_tac split_neq justifications
            (assumptions, conclusion)
      | NONE =>
          (linarithData.trace_terms 2 "preprocessed assumptions" assumptions;
           linarithData.trace 2
             ("preprocessed conclusion\n" ^
              Parse.term_to_string conclusion);
           raise ERR function "linear arithmetic found no proof")
  end

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

fun shell_relevant tm =
  linarithDecomp.is_relevant tm orelse
  (case Lib.total boolSyntax.dest_neg tm of
       SOME body => shell_relevant body
     | NONE =>
         (case Lib.total boolSyntax.dest_eq tm of
              SOME (left, right) =>
                same_type (Term.type_of left) Type.bool andalso
                (shell_relevant left orelse shell_relevant right)
            | NONE =>
                (case Lib.total boolSyntax.dest_conj tm of
                     SOME (left, right) =>
                       shell_relevant left orelse shell_relevant right
                   | NONE =>
                       (case Lib.total boolSyntax.dest_disj tm of
                     SOME (left, right) =>
                       shell_relevant left orelse shell_relevant right
                   | NONE =>
                       (case Lib.total boolSyntax.dest_imp tm of
                            SOME (left, right) =>
                              shell_relevant left orelse
                              shell_relevant right
                          | NONE =>
                              (case Lib.total boolSyntax.dest_forall tm of
                                   SOME (_, body) => shell_relevant body
                                 | NONE =>
                                     (case Lib.total
                                             boolSyntax.dest_exists tm of
                                          SOME (_, body) =>
                                            shell_relevant body
                                        | NONE => false)))))))

fun filter_relevant (assumptions, conclusion) =
  let
    val filtered = List.filter shell_relevant assumptions
    fun validate [theorem] = theorem
      | validate _ =
          raise ERR "filter_relevant" "invalid validation theorem list"
  in
    ([(filtered, conclusion)], validate)
  end

val nnf_rewrites =
  [boolTheory.IMP_DISJ_THM,
   boolTheory.EQ_IMP_THM,
   boolTheory.DE_MORGAN_THM,
   boolTheory.NOT_FORALL_THM,
   boolTheory.NOT_EXISTS_THM,
   CONJUNCT1 boolTheory.NOT_CLAUSES]

fun nnf_rule theorem = Rewrite.REWRITE_RULE nnf_rewrites theorem

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

fun nnf_flatten goal =
  Tactical.THEN
    (Tactical.POP_ASSUM_LIST
       (fn theorems =>
         Tactical.MAP_EVERY (Tactic.STRIP_ASSUME_TAC o nnf_rule)
           theorems),
     Tactical.TRY opposite_tac) goal

fun limit_exceeded function limit =
  let
    val message =
      "linarith_split_limit exceeded (current value is " ^
      Int.toString limit ^ ")"
    val _ = linarithData.trace 1 message
  in
    raise ERR function message
  end

fun split_fixpoint function limit split_tac =
  let
    fun attempt goal = SOME (split_tac goal) handle HOL_ERR _ => NONE
    fun loop rounds goal =
      case attempt goal of
          NONE => Tactical.ALL_TAC goal
        | SOME (split_goals, split_validation) =>
            if rounds >= limit then limit_exceeded function limit
            else
              let
                val next =
                  Tactical.THEN (nnf_flatten, loop (rounds + 1))
                val (goals, validation) =
                  Tactical.ALLGOALS next split_goals
              in
                (goals, split_validation o validation)
              end
  in
    loop 0
  end

fun insert_aconv tm terms =
  if List.exists (Term.aconv tm) terms then terms else tm :: terms

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

fun facts_for tm =
  case linarithData.instance_for (Term.type_of tm) of
      NONE => []
    | SOME instance =>
        (case #divmod_facts instance of
             NONE => []
           | SOME facts => facts tm)

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

fun augment_divmod function limit =
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
    val split_limit = #split_limit config
    val preprocess =
      Tactical.THEN
        (Tactic.CCONTR_TAC,
         Tactical.THEN
           (filter_relevant,
            Tactical.THEN
              (nnf_flatten,
               Tactical.THEN
                 (split_fixpoint function split_limit split_tac,
                  augment_divmod function split_limit))))
  in
    Tactical.THEN
      (clasetLib.INSERT_FACTS_TAC facts,
       fn goal as (_, conclusion) =>
         (check_registered function conclusion;
          Tactical.THEN (preprocess, core function config) goal))
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

fun context_forward theorems conclusion =
  let
    val atoms = List.concat (map CONJUNCTS theorems)
    val theorem = forward_prove (map Thm.concl atoms) conclusion
  in
    List.foldl
      (fn (premise, result) => PROVE_HYP premise result)
      theorem atoms
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
            (case Lib.total boolSyntax.dest_neg tm of
                 SOME body => recurse bound atoms body
               | NONE =>
                   (case Lib.total boolSyntax.dest_conj tm of
                        SOME (left, right) =>
                          recurse bound (recurse bound atoms left) right
                      | NONE =>
                          (case Lib.total boolSyntax.dest_disj tm of
                               SOME (left, right) =>
                                 recurse bound
                                   (recurse bound atoms left) right
                             | NONE =>
                                 (case Lib.total boolSyntax.dest_imp tm of
                                      SOME (left, right) =>
                                        recurse bound
                                          (recurse bound atoms left) right
                                    | NONE =>
                                        (case Lib.total
                                                boolSyntax.dest_forall tm of
                                             SOME (variable, body) =>
                                               recurse (variable :: bound)
                                                 atoms body
                                           | NONE =>
                                               (case Lib.total
                                                       boolSyntax.dest_exists
                                                       tm of
                                                    SOME (variable, body) =>
                                                      recurse
                                                        (variable :: bound)
                                                        atoms body
                                                  | NONE => atoms))))))
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
  case Lib.total boolSyntax.dest_conj tm of
      SOME (left, right) =>
        contains_forall sense left orelse contains_forall sense right
    | NONE =>
        (case Lib.total boolSyntax.dest_disj tm of
             SOME (left, right) =>
               contains_forall sense left orelse
               contains_forall sense right
           | NONE =>
               (case Lib.total boolSyntax.dest_neg tm of
                    SOME body => contains_forall (not sense) body
                  | NONE =>
                      (case Lib.total boolSyntax.dest_imp tm of
                           SOME (left, right) =>
                             contains_forall (not sense) left orelse
                             contains_forall sense right
                         | NONE =>
                             (case Lib.total boolSyntax.dest_forall tm of
                                  SOME (_, body) =>
                                    sense orelse contains_forall sense body
                                | NONE =>
                                    (case Lib.total
                                            boolSyntax.dest_exists tm of
                                         SOME (_, body) =>
                                           not sense orelse
                                           contains_forall sense body
                                       | NONE => false)))))

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

(* Mirrors Isabelle's solver setup at lin_arith.ML:949. *)
val linarith_solver : Traverse.ssolver =
  {name = "lin_arith",
   solve = fn {context_thms, ...} => fn tm =>
     context_forward
       (context_thms @ linarithData.arith_facts ()) tm}

fun clear_linarith_caches () = Cache.clear_cache linarith_cache

val _ = linarithData.register_instance linarithNum.instance

end
