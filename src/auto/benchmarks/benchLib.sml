structure benchLib :> benchLib =
struct

open Abbrev HolKernel

val ERR = mk_HOL_ERR "benchLib"

(* Force the post-boss carrier registrations into every benchmark image. *)
val _ =
  (intLinarith.instance, realLinarith.instance, ratLinarith.instance)

type provenance = {file : string, line : int, commit : string}

datatype tactic_id =
    Simp
  | Auto
  | Blast
  | Force
  | Fastforce
  | Safe
  | Clarify
  | Clarsimp
  | Aesop
  | Linarith
  | IntArith
  | Cooper
  | NumRing
  | IntRing
  | IntIdeal
  | ExplicitRing
  | RealRing
  | RealField

type named_thm = {name : string, theorem : thm}

datatype rule_strength = SafeRule | UnsafeRule

datatype method_arg =
    RewriteAdd of named_thm
  | RewriteDelete of string
  | SplitAdd of named_thm
  | IntroAdd of rule_strength * named_thm
  | ElimAdd of rule_strength * named_thm
  | DestAdd of rule_strength * named_thm
  | CongruenceAdd of named_thm
  | FactAdd of named_thm
  | DefinitionAdd of named_thm

datatype method_recipe =
    Invoke of tactic_id * method_arg list
  | Then of method_recipe * method_recipe
  | AllGoals of method_recipe * method_recipe

type exclusion = {name : string, theorem : thm}

type corpus_goal = {
  id : string,
  goal : term,
  source_method : string,
  recipe : method_recipe,
  excl : exclusion list,
  provenance : provenance,
  representative : bool
}

datatype outcome = SOLVED of Time.time | TIMEOUT | FAILED of string

datatype cause =
    AcceptedGap
  | EngineLimitation
  | TranslationGap
  | UnderIteration

type shortfall = {
  id : string,
  cause : cause,
  date : string,
  note : string
}

type family_result = {
  gated : (string * outcome) list,
  battery : (string * tactic_id * outcome) list
}

val default_budget =
  case Option.mapPartial Int.fromString
         (OS.Process.getEnv "HOLBENCHBUDGET") of
      SOME seconds =>
        if seconds > 0 then Time.fromSeconds (LargeInt.fromInt seconds)
        else Time.fromSeconds 30
    | NONE => Time.fromSeconds 30

fun selftest_level () =
  case OS.Process.getEnv "HOLSELFTESTLEVEL" of
      NONE => 1
    | SOME text =>
        (case Int.fromString text of SOME level => level | NONE => 1)

fun tactic_name Simp = "simp"
  | tactic_name Auto = "AUTO_TAC"
  | tactic_name Blast = "BLAST_TAC"
  | tactic_name Force = "FORCE_TAC"
  | tactic_name Fastforce = "FASTFORCE_TAC"
  | tactic_name Safe = "SAFE_TAC"
  | tactic_name Clarify = "CLARIFY_TAC"
  | tactic_name Clarsimp = "CLARSIMP_TAC"
  | tactic_name Aesop = "AESOP_TAC"
  | tactic_name Linarith = "LINARITH_TAC"
  | tactic_name IntArith = "intLib.ARITH_TAC"
  | tactic_name Cooper = "intLib.COOPER_TAC"
  | tactic_name NumRing = "Grobner.NUM_RING"
  | tactic_name IntRing = "intLib.INT_RING_TAC"
  | tactic_name IntIdeal = "intLib.INTEGER_TAC"
  | tactic_name ExplicitRing = "ringLib.EXPLICIT_RING_TAC"
  | tactic_name RealRing = "RealField.REAL_RING"
  | tactic_name RealField = "RealField.REAL_FIELD_TAC"

fun strength_name SafeRule = "safe"
  | strength_name UnsafeRule = "unsafe"

fun named_arg constructor ({name, ...} : named_thm) =
  constructor ^ "(" ^ name ^ ")"

fun strength_arg constructor strength ({name, ...} : named_thm) =
  constructor ^ "-" ^ strength_name strength ^ "(" ^ name ^ ")"

fun method_arg_name (RewriteAdd theorem) = named_arg "rewrite" theorem
  | method_arg_name (RewriteDelete name) = "rewrite-delete(" ^ name ^ ")"
  | method_arg_name (SplitAdd theorem) = named_arg "split" theorem
  | method_arg_name (IntroAdd (strength, theorem)) =
      strength_arg "intro" strength theorem
  | method_arg_name (ElimAdd (strength, theorem)) =
      strength_arg "elim" strength theorem
  | method_arg_name (DestAdd (strength, theorem)) =
      strength_arg "dest" strength theorem
  | method_arg_name (CongruenceAdd theorem) = named_arg "cong" theorem
  | method_arg_name (FactAdd theorem) = named_arg "fact" theorem
  | method_arg_name (DefinitionAdd theorem) = named_arg "definition" theorem

fun recipe_name recipe =
  let
    fun render (Invoke (tactic_id, args)) =
          tactic_name tactic_id ^
          (if null args then ""
           else "[" ^ String.concatWith ", " (map method_arg_name args) ^
                "]")
      | render (Then (left, right)) =
          "then(" ^ render left ^ ", " ^ render right ^ ")"
      | render (AllGoals (left, right)) =
          "all-goals(" ^ render left ^ ", " ^ render right ^ ")"
  in
    render recipe
  end

fun recipe_has_tactic wanted (Invoke (tactic_id, _)) = wanted = tactic_id
  | recipe_has_tactic wanted (Then (left, right)) =
      recipe_has_tactic wanted left orelse recipe_has_tactic wanted right
  | recipe_has_tactic wanted (AllGoals (left, right)) =
      recipe_has_tactic wanted left orelse recipe_has_tactic wanted right

fun linarith_stats_text () =
  let
    val {nodes, refutations, disjunction_splits,
         operator_splits, augmentations} =
      linarithLib.last_search_stats ()
  in
    String.concat
      ["linarith stats: nodes=", Int.toString nodes,
       ", refutations=", Int.toString refutations,
       ", disjunction-splits=", Int.toString disjunction_splits,
       ", operator-splits=", Int.toString operator_splits,
       ", augmentations=", Int.toString augmentations]
  end

fun cause_name AcceptedGap = "accepted-gap"
  | cause_name EngineLimitation = "engine-limitation"
  | cause_name TranslationGap = "translation-gap"
  | cause_name UnderIteration = "under-iteration"

fun outcome_solved (SOLVED _) = true
  | outcome_solved _ = false

fun outcome_text (SOLVED elapsed) = "solved:" ^ Time.toString elapsed
  | outcome_text TIMEOUT = "timeout"
  | outcome_text (FAILED message) = "failed:" ^ message

fun claset_names name =
  [name,
   name ^ ".__clasimp_iff_intro",
   name ^ ".__clasimp_iff_dest",
   name ^ ".__clasimp_iff_elim"]

(* Isabelle's Set.thy automation unfolds these primitive set operations
   while proving their public membership rewrites.  Supply the same
   foundational view here; this is translation support, not a corpus
   theorem or a persistent simpset change. *)
val translation_frag =
  simpLib.name_ss "bench-translation-base"
    (simpLib.rewrites
       [pred_setTheory.UNION_DEF, pred_setTheory.INTER_DEF,
       pred_setTheory.DIFF_DEF, pairTheory.UNCURRY_DEF,
       pairTheory.PAIR, pairTheory.FORALL_PROD,
       pairTheory.EXISTS_PROD, pairTheory.PAIR_FST_SND_EQ])
val translation_frag = simpLib.register_frag translation_frag
val translation_base = simpLib.SF translation_frag

fun controls exclusions =
  List.concat
    (map
      (fn ({name, ...} : exclusion) =>
        map clasetLib.Del (claset_names name) @ [markerLib.Excl name])
      exclusions)

fun simp_controls exclusions = translation_base :: controls exclusions

fun theorem_is_goal goal theorem =
  let
    val (_, body) = boolSyntax.strip_forall (Thm.concl theorem)
    val (_, conclusion) = boolSyntax.strip_imp_only body
    fun variants left right =
      can (match_term left) right andalso can (match_term right) left
  in
    Term.aconv conclusion goal orelse
    Term.aconv (Thm.concl theorem) goal orelse
    variants conclusion goal
  end

fun named_theorem (RewriteAdd theorem) = SOME theorem
  | named_theorem (SplitAdd theorem) = SOME theorem
  | named_theorem (IntroAdd (_, theorem)) = SOME theorem
  | named_theorem (ElimAdd (_, theorem)) = SOME theorem
  | named_theorem (DestAdd (_, theorem)) = SOME theorem
  | named_theorem (CongruenceAdd theorem) = SOME theorem
  | named_theorem (FactAdd theorem) = SOME theorem
  | named_theorem (DefinitionAdd theorem) = SOME theorem
  | named_theorem (RewriteDelete _) = NONE

(* A direct analogue is excluded by theorem shape as well as by its
   persistent name.  This check happens before controls are appended, so a
   recipe cannot put the measured theorem back under an invocation-private
   name. *)
fun permitted_arg ({goal, excl, ...} : corpus_goal) arg =
  null excl orelse
  case named_theorem arg of
      NONE => true
    | SOME {theorem, ...} => not (theorem_is_goal goal theorem)

fun class_args (RewriteAdd {theorem, ...}) = [clasetLib.Simp theorem]
  | class_args (RewriteDelete name) =
      map clasetLib.Del (claset_names name) @ [markerLib.Excl name]
  | class_args (SplitAdd {theorem, ...}) = [simpLib.Split theorem]
  | class_args (IntroAdd (SafeRule, {theorem, ...})) =
      [clasetLib.SIntro theorem]
  | class_args (IntroAdd (UnsafeRule, {theorem, ...})) =
      [clasetLib.Intro theorem]
  | class_args (ElimAdd (SafeRule, {theorem, ...})) =
      [clasetLib.SElim theorem]
  | class_args (ElimAdd (UnsafeRule, {theorem, ...})) =
      [clasetLib.Elim theorem]
  | class_args (DestAdd (SafeRule, {theorem, ...})) =
      [clasetLib.SDest theorem]
  | class_args (DestAdd (UnsafeRule, {theorem, ...})) =
      [clasetLib.Dest theorem]
  | class_args (CongruenceAdd {theorem, ...}) = [simpLib.Cong theorem]
  | class_args (FactAdd _) = []
  | class_args (DefinitionAdd {theorem, ...}) =
      [clasetLib.Simp theorem]

fun all_class_args args = List.concat (map class_args args)

fun classical_arg (RewriteDelete name) =
      map clasetLib.Del (claset_names name)
  | classical_arg (IntroAdd (SafeRule, {theorem, ...})) =
      [clasetLib.SIntro theorem]
  | classical_arg (IntroAdd (UnsafeRule, {theorem, ...})) =
      [clasetLib.Intro theorem]
  | classical_arg (ElimAdd (SafeRule, {theorem, ...})) =
      [clasetLib.SElim theorem]
  | classical_arg (ElimAdd (UnsafeRule, {theorem, ...})) =
      [clasetLib.Elim theorem]
  | classical_arg (DestAdd (SafeRule, {theorem, ...})) =
      [clasetLib.SDest theorem]
  | classical_arg (DestAdd (UnsafeRule, {theorem, ...})) =
      [clasetLib.Dest theorem]
  | classical_arg _ = []

fun all_classical_args args = List.concat (map classical_arg args)

fun classical_controls exclusions =
  List.concat
    (map
      (fn ({name, ...} : exclusion) =>
        map clasetLib.Del (claset_names name))
      exclusions)

fun blast_arg (IntroAdd (SafeRule, {theorem, ...})) =
      [clasetLib.SIntro theorem]
  | blast_arg (IntroAdd (UnsafeRule, {theorem, ...})) =
      [clasetLib.Intro theorem]
  | blast_arg (ElimAdd (SafeRule, {theorem, ...})) =
      [clasetLib.SElim theorem]
  | blast_arg (ElimAdd (UnsafeRule, {theorem, ...})) =
      [clasetLib.Elim theorem]
  | blast_arg (DestAdd (SafeRule, {theorem, ...})) =
      [clasetLib.SDest theorem]
  | blast_arg (DestAdd (UnsafeRule, {theorem, ...})) =
      [clasetLib.Dest theorem]
  | blast_arg (FactAdd _) = []
  | blast_arg _ = []

fun all_blast_args args = List.concat (map blast_arg args)

val blast_translation_args =
  [pairTheory.PAIR,
   clasetLib.Intro boolTheory.SELECT_UNIQUE]

fun simp_arg (RewriteAdd {theorem, ...}) = SOME theorem
  | simp_arg (RewriteDelete name) = SOME (simpLib.Excl name)
  | simp_arg (SplitAdd {theorem, ...}) = SOME (simpLib.Split theorem)
  | simp_arg (CongruenceAdd {theorem, ...}) = SOME (simpLib.Cong theorem)
  | simp_arg (DefinitionAdd {theorem, ...}) = SOME theorem
  | simp_arg _ = NONE

fun fact_arg (FactAdd {theorem, ...}) = SOME theorem
  | fact_arg _ = NONE

fun supplied_rule (IntroAdd (_, {theorem, ...})) = SOME theorem
  | supplied_rule (ElimAdd (_, {theorem, ...})) = SOME theorem
  | supplied_rule (DestAdd (_, {theorem, ...})) = SOME theorem
  | supplied_rule _ = NONE

fun insert_facts facts =
  Tactical.MAP_EVERY Tactic.ASSUME_TAC (List.rev facts)

fun with_facts args tactic =
  let
    val facts = List.mapPartial fact_arg args
  in
    Tactical.ORELSE
      (Tactical.FIRST (map Tactic.MATCH_ACCEPT_TAC facts),
       Tactical.THEN (insert_facts facts, tactic))
  end

fun recipe_args entry args = List.filter (permitted_arg entry) args

fun tactic_for Simp args exclusions =
      let
        val facts = List.mapPartial fact_arg args
        val simps = List.mapPartial simp_arg args
      in
        Tactical.THEN
          (insert_facts facts,
           simpLib.FULL_SIMP_TAC
             (clasimpLib.clasimp_ss ())
             (simps @ simp_controls exclusions))
      end
  | tactic_for Auto args exclusions =
      let
        val automatic =
          clasimpLib.AUTO_TAC
            (all_class_args args @ simp_controls exclusions)
        val prepare =
          Tactical.THEN
            (Tactical.TRY hurdUtils.SET_EQ_TAC,
             simpLib.FULL_SIMP_TAC
               (clasimpLib.clasimp_ss ())
               (List.mapPartial simp_arg args @
                simp_controls exclusions))
      in
        with_facts args
          (if null args then
             Tactical.THEN
               (Tactical.TRY hurdUtils.SET_EQ_TAC, automatic)
           else
             Tactical.THEN
               (prepare, automatic))
      end
  | tactic_for Blast args exclusions =
      let
        val simps = List.mapPartial simp_arg args
        val supplied_rules = List.mapPartial supplied_rule args
        val accept_supplied =
          Tactical.FIRST
            (map Tactic.MATCH_ACCEPT_TAC supplied_rules)
        val direct_supplied =
          Tactical.THEN
            (Tactical.TRY Tactic.BETA_TAC,
             Tactical.ORELSE
               (accept_supplied,
                Tactical.THEN (Tactic.EQ_TAC, accept_supplied)))
        fun simplify goal =
          simpLib.SIMP_TAC
            (clasimpLib.clasimp_ss ())
            (simps @ simp_controls exclusions) goal
        val preprocess =
          if null args then
            Tactical.TRY
              (Tactical.THEN
                (hurdUtils.SET_EQ_TAC, simplify))
          else
            Tactical.THEN
              (Tactical.TRY hurdUtils.SET_EQ_TAC,
               simplify)
      in
        with_facts args
          (Tactical.ORELSE
            (direct_supplied,
             Tactical.THEN
               (Tactical.TRY
                  (Tactic.MATCH_MP_TAC boolTheory.SELECT_UNIQUE),
                Tactical.THEN
                  (preprocess,
                   Tactical.THEN
                     (Tactical.TRY Tactic.EQ_TAC,
                      Tactical.THEN
                       (Tactical.TRY Tactic.BETA_TAC,
                        Tactical.ORELSE
                          (accept_supplied,
                           tableauLib.BLAST_TAC
                             (all_blast_args args @
                              blast_translation_args @
                              controls exclusions))))))))
      end
  | tactic_for Force args exclusions =
      with_facts args
        (clasimpLib.FORCE_TAC
          (all_class_args args @ simp_controls exclusions))
  | tactic_for Fastforce args exclusions =
      with_facts args
        (Tactical.THEN
          (Tactical.TRY hurdUtils.SET_EQ_TAC,
           clasimpLib.FASTFORCE_TAC
             (all_class_args args @ simp_controls exclusions)))
  | tactic_for Safe args exclusions =
      with_facts args
        (classicalLib.SAFE_TAC
          (all_classical_args args @ classical_controls exclusions))
  | tactic_for Clarify args exclusions =
      with_facts args
        (classicalLib.CLARIFY_TAC
          (all_classical_args args @ classical_controls exclusions))
  | tactic_for Clarsimp args exclusions =
      with_facts args
        (clasimpLib.CLARSIMP_TAC
          (all_class_args args @ simp_controls exclusions))
  | tactic_for Aesop args exclusions =
      with_facts args
        (aesopLib.AESOP_TAC
          (all_class_args args @ simp_controls exclusions))
  | tactic_for Linarith args exclusions =
      with_facts args
        (linarithLib.LINARITH_TAC
          (all_class_args args @ controls exclusions))
  (* Bind the current integer backends into the benchmark image. *)
  | tactic_for IntArith args _ =
      Tactical.THEN (insert_facts (List.mapPartial fact_arg args),
                     intLib.ARITH_TAC)
  | tactic_for Cooper args _ =
      Tactical.THEN (insert_facts (List.mapPartial fact_arg args),
                     intLib.COOPER_TAC)
  | tactic_for NumRing args _ =
      Tactical.THEN (insert_facts (List.mapPartial fact_arg args),
                     Tactical.CONV_TAC Grobner.NUM_RING)
  | tactic_for IntRing args _ =
      Tactical.THEN (insert_facts (List.mapPartial fact_arg args),
                     intLib.INT_RING_TAC)
  | tactic_for IntIdeal args _ =
      Tactical.THEN (insert_facts (List.mapPartial fact_arg args),
                     intLib.INTEGER_TAC)
  | tactic_for ExplicitRing args _ =
      Tactical.THEN
        (Tactical.REPEAT Tactic.STRIP_TAC,
         Tactical.THEN
           (insert_facts (List.mapPartial fact_arg args),
            Tactical.THEN
              (simpLib.SIMP_TAC
                 (clasimpLib.clasimp_ss ())
                 (List.mapPartial simp_arg args),
               ringLib.EXPLICIT_RING_TAC)))
  | tactic_for RealRing args _ =
      Tactical.THEN (insert_facts (List.mapPartial fact_arg args),
                     Tactical.CONV_TAC RealField.REAL_RING)
  | tactic_for RealField args _ =
      Tactical.THEN (insert_facts (List.mapPartial fact_arg args),
                     RealField.REAL_FIELD_TAC)

fun compile_recipe entry recipe =
  case recipe of
      Invoke (tactic_id, args) =>
        tactic_for tactic_id (recipe_args entry args) (#excl entry)
    | Then (left, right) =>
        Tactical.THEN1
          (compile_recipe entry left, compile_recipe entry right)
    | AllGoals (left, right) =>
        Tactical.THEN
          (compile_recipe entry left, compile_recipe entry right)

fun exclusions_effective claset ({goal, excl, ...} : corpus_goal) =
  let
    val names = List.concat (map (claset_names o #name) excl)
    val diminished = List.foldl (fn (name, cs) =>
      clasetLib.remove_rule name cs) claset names
    fun supplied_is_analogue ({theorem, ...} : exclusion) =
      theorem_is_goal goal theorem
    fun context_has_analogue ({thm, ...} : clasetLib.aesop_rule) =
      theorem_is_goal goal thm
  in
    List.all supplied_is_analogue excl andalso
    not (List.exists context_has_analogue (clasetLib.all_rules diminished))
  end

fun exclusion_diagnostic claset ({goal, excl, ...} : corpus_goal) =
  let
    val names = List.concat (map (claset_names o #name) excl)
    val diminished = List.foldl (fn (name, cs) =>
      clasetLib.remove_rule name cs) claset names
    val bad_supplied =
      map
        (fn ({name, theorem} : exclusion) =>
          name ^ ": " ^ Parse.term_to_string (Thm.concl theorem))
        (List.filter
          (fn ({theorem, ...} : exclusion) =>
            not (theorem_is_goal goal theorem)) excl)
    val remaining =
      map #name
        (List.filter
          (fn ({thm, ...} : clasetLib.aesop_rule) =>
            theorem_is_goal goal thm)
          (clasetLib.all_rules diminished))
  in
    "non-analogues = [" ^ String.concatWith ", " bad_supplied ^
    "], goal = " ^ Parse.term_to_string goal ^
    ", remaining rules = [" ^
    String.concatWith ", " remaining ^ "]"
  end

fun run_goal budget recipe (entry : corpus_goal) =
  let
    val started = Time.now ()
    val residual = ref "tactic returned residual goals or failed"
    fun goal_text (assumptions, conclusion) =
      (if null assumptions then ""
       else String.concatWith ", " (map Parse.term_to_string assumptions) ^
            " |- ") ^
      Parse.term_to_string conclusion
    fun run () =
      case Tactical.VALID (compile_recipe entry recipe)
             ([], #goal entry) of
          ([], validation) => (ignore (validation []); true)
        | (goals, _) =>
            (residual :=
               "residual goals: [" ^
               String.concatWith "; " (map goal_text goals) ^ "]";
             false)
    val timed_out = ref false
    val solved =
      Timeout.apply budget run ()
      handle Timeout.TIMEOUT _ =>
        (if recipe_has_tactic Linarith recipe andalso
            OS.Process.getEnv "HOLBENCHPROGRESS" = SOME "1"
         then TextIO.print (linarith_stats_text () ^ "\n")
         else ();
         timed_out := true;
         false)
           | Portable.Interrupt => raise Portable.Interrupt
           | exn =>
               raise ERR "run_goal"
                 (recipe_name recipe ^ " on " ^ #id entry ^ ": " ^
                  Feedback.exn_to_string exn)
    val elapsed = Time.- (Time.now (), started)
  in
    if !timed_out orelse not (Time.< (elapsed, budget)) then TIMEOUT
    else if solved then SOLVED elapsed
    else FAILED (!residual)
  end
  handle Portable.Interrupt => raise Portable.Interrupt
       | exn => FAILED (Feedback.exn_to_string exn)

fun duplicate strings =
  List.exists
    (fn string => length (List.filter (equal string) strings) > 1)
    strings

fun duplicate_goal_pairs ([] : corpus_goal list) = []
  | duplicate_goal_pairs ((goal : corpus_goal) :: rest) =
      map (fn (other : corpus_goal) => (#id goal, #id other))
        (List.filter
          (fn (other : corpus_goal) =>
            Term.aconv (#goal goal) (#goal other)) rest) @
      duplicate_goal_pairs rest

fun is_translation ({cause = TranslationGap, ...} : shortfall) = true
  | is_translation _ = false

fun validate_corpus {family, goals, shortfalls} =
  let
    val goal_ids = map #id goals
    val shortfall_ids = map #id shortfalls
    val duplicate_pairs = duplicate_goal_pairs goals
    fun is_goal id = List.exists (equal id) goal_ids
    val unknown =
      List.filter
        (fn (item as {id, ...} : shortfall) =>
          not (is_goal id) andalso not (is_translation item)) shortfalls
    val misplaced_translation =
      List.filter
        (fn ({id, ...} : shortfall) => is_goal id)
        (List.filter is_translation shortfalls)
    val valid_entries =
      List.all
        (fn ({id, date, note, ...} : shortfall) =>
          id <> "" andalso date <> "" andalso note <> "") shortfalls
  in
    if duplicate goal_ids then
      raise ERR "validate_corpus" (family ^ ": duplicate corpus goal id")
    else if not (null duplicate_pairs) then
      raise ERR "validate_corpus"
        (family ^ ": aconv corpus goals: " ^
         String.concatWith ", "
           (map (fn (left, right) => left ^ "=" ^ right)
             duplicate_pairs))
    else if duplicate shortfall_ids then
      raise ERR "validate_corpus" (family ^ ": duplicate shortfall id")
    else if not valid_entries then
      raise ERR "validate_corpus"
        (family ^ ": shortfalls need non-empty id, date, and note")
    else if not (null unknown) then
      raise ERR "validate_corpus"
        (family ^ ": unknown shortfalls: " ^
         String.concatWith ", " (map #id unknown))
    else if not (null misplaced_translation) then
      raise ERR "validate_corpus"
        (family ^ ": translation gaps unexpectedly have HOL goals: " ^
         String.concatWith ", " (map #id misplaced_translation))
    else
      ()
  end

fun assert_accounting {family, goals, shortfalls, gated} =
  let
    val goal_ids = map #id goals
    val gated_ids = map #1 gated
    val missing_runs =
      List.filter
        (fn id => not (List.exists (equal id) gated_ids)) goal_ids
    val extra_runs =
      List.filter
        (fn id => not (List.exists (equal id) goal_ids)) gated_ids
    val solved =
      map #1 (List.filter (outcome_solved o #2) gated)
    val expected =
      List.filter
        (fn id => not (List.exists (equal id)
          (map #id (List.filter (not o is_translation) shortfalls))))
        goal_ids
    fun same_set left right =
      length left = length right andalso
      List.all (fn id => List.exists (equal id) right) left
    val _ = validate_corpus
      {family = family, goals = goals, shortfalls = shortfalls}
  in
    if not (null missing_runs) orelse not (null extra_runs) then
      raise ERR "assert_accounting" (family ^ ": gated result id drift")
    else if not (same_set solved expected) then
      raise ERR "assert_accounting"
        (family ^ ": solved/shortfall drift; solved = [" ^
         String.concatWith ", " solved ^ "], expected = [" ^
         String.concatWith ", " expected ^ "], outcomes = [" ^
         String.concatWith ", "
           (map (fn (id, result) => id ^ "=" ^ outcome_text result)
             gated) ^ "]")
    else
      ()
  end

fun selected level ({representative, ...} : corpus_goal) =
  level >= 2 orelse representative

fun run_family {family, goals, shortfalls, budget, battery, level} =
  let
    val selected_goals =
      List.filter
        (fn (goal : corpus_goal) =>
          selected level goal andalso
          (case (OS.Process.getEnv "HOLBENCHFAMILY",
                 OS.Process.getEnv "HOLBENCHGOAL") of
               (SOME selected_family, SOME id) =>
                 selected_family <> family orelse
                 List.exists (equal (#id goal))
                   (String.tokens (equal #",") id)
             | _ => true)) goals
    val selected_ids = map #id selected_goals
    val selected_shortfalls =
      List.filter
        (fn ({id, cause, ...} : shortfall) =>
          List.exists (equal id) selected_ids orelse
          (level >= 2 andalso cause = TranslationGap)) shortfalls
    val _ = validate_corpus
      {family = family, goals = selected_goals,
       shortfalls = selected_shortfalls}
    val _ =
      List.app
        (fn goal =>
          if null (#excl goal) orelse
             exclusions_effective (clasetLib.the_claset ()) goal
          then ()
          else
            raise ERR "run_family"
              (family ^ ": ineffective self-analogue exclusion for " ^
               #id goal ^ "; " ^
               exclusion_diagnostic (clasetLib.the_claset ()) goal))
        selected_goals
    fun run_gated goal =
      let
        val _ =
          if OS.Process.getEnv "HOLBENCHPROGRESS" = SOME "1" then
            (TextIO.print (family ^ ": " ^ #id goal ^ " ... ");
             TextIO.flushOut TextIO.stdOut)
          else
            ()
        val result = run_goal budget (#recipe goal) goal
        val _ =
          if OS.Process.getEnv "HOLBENCHPROGRESS" = SOME "1" then
            TextIO.print
              (outcome_text result ^
               (if recipe_has_tactic Linarith (#recipe goal) then
                  " " ^ linarith_stats_text ()
                else
                  "") ^ "\n")
          else
            ()
      in
        (#id goal, result)
      end
    val gated = map run_gated selected_goals
    val _ =
      assert_accounting
        {family = family, goals = selected_goals,
         shortfalls = selected_shortfalls, gated = gated}
    fun run_battery goal tactic_id =
      let
        val progress =
          OS.Process.getEnv "HOLBENCHPROGRESS" = SOME "1"
        val _ =
          if progress then
            (TextIO.print
               (family ^ " battery: " ^ #id goal ^ " " ^
                tactic_name tactic_id ^ " ... ");
             TextIO.flushOut TextIO.stdOut)
          else
            ()
        val detailed_result =
          run_goal budget (Invoke (tactic_id, [])) goal
        val result =
          case detailed_result of
              FAILED _ => FAILED "additional observation failed"
            | outcome => outcome
        val _ =
          if progress then
            TextIO.print (outcome_text result ^ "\n")
          else
            ()
      in
        (#id goal, tactic_id, result)
      end
    val battery_results =
      if level < 2 orelse
         OS.Process.getEnv "HOLBENCHNOBATTERY" = SOME "1"
      then []
      else
        List.concat
          (map
            (fn goal =>
              map
                (run_battery goal)
                (List.filter
                   (fn tactic_id =>
                     not (recipe_has_tactic tactic_id (#recipe goal)))
                   battery))
            selected_goals)
  in
    {gated = gated, battery = battery_results}
  end

end
