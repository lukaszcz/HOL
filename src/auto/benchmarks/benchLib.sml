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
  | RealRing
  | RealField

type exclusion = {name : string, theorem : thm}

type corpus_goal = {
  id : string,
  goal : term,
  source_method : string,
  mapped : tactic_id,
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
  | tactic_name RealRing = "RealField.REAL_RING"
  | tactic_name RealField = "RealField.REAL_FIELD_TAC"

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
       pred_setTheory.DIFF_DEF, pairTheory.UNCURRY_DEF])
val translation_frag = simpLib.register_frag translation_frag
val translation_base = simpLib.SF translation_frag

fun controls exclusions =
  List.concat
    (map
      (fn ({name, ...} : exclusion) =>
        map clasetLib.Del (claset_names name) @ [markerLib.Excl name])
      exclusions)

fun simp_controls exclusions = translation_base :: controls exclusions

fun tactic_for Simp exclusions =
      simpLib.SIMP_TAC
        (clasimpLib.clasimp_ss ()) (simp_controls exclusions)
  | tactic_for Auto exclusions =
      clasimpLib.AUTO_TAC (simp_controls exclusions)
  | tactic_for Blast exclusions = tableauLib.BLAST_TAC (controls exclusions)
  | tactic_for Force exclusions =
      clasimpLib.FORCE_TAC (simp_controls exclusions)
  | tactic_for Fastforce exclusions =
      clasimpLib.FASTFORCE_TAC (simp_controls exclusions)
  | tactic_for Safe exclusions =
      classicalLib.SAFE_TAC (controls exclusions)
  | tactic_for Clarify exclusions =
      classicalLib.CLARIFY_TAC (controls exclusions)
  | tactic_for Clarsimp exclusions =
      clasimpLib.CLARSIMP_TAC (simp_controls exclusions)
  | tactic_for Aesop exclusions =
      aesopLib.AESOP_TAC (simp_controls exclusions)
  | tactic_for Linarith exclusions =
      linarithLib.LINARITH_TAC (controls exclusions)
  (* Bind the current integer backends into the benchmark image. *)
  | tactic_for IntArith _ = intLib.ARITH_TAC
  | tactic_for Cooper _ = intLib.COOPER_TAC
  | tactic_for NumRing _ = Tactical.CONV_TAC Grobner.NUM_RING
  | tactic_for IntRing _ = intLib.INT_RING_TAC
  | tactic_for RealRing _ = Tactical.CONV_TAC RealField.REAL_RING
  | tactic_for RealField _ = RealField.REAL_FIELD_TAC

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

fun run_goal budget tactic_id (entry : corpus_goal) =
  let
    val started = Time.now ()
    fun run () =
      case Tactical.VALID (tactic_for tactic_id (#excl entry))
             ([], #goal entry) of
          ([], validation) => (ignore (validation []); true)
        | _ => false
    val timed_out = ref false
    val solved =
      Timeout.apply budget run ()
      handle Timeout.TIMEOUT _ => (timed_out := true; false)
           | Portable.Interrupt => raise Portable.Interrupt
           | exn =>
               raise ERR "run_goal"
                 (tactic_name tactic_id ^ " on " ^ #id entry ^ ": " ^
                  Feedback.exn_to_string exn)
    val elapsed = Time.- (Time.now (), started)
  in
    if !timed_out orelse not (Time.< (elapsed, budget)) then TIMEOUT
    else if solved then SOLVED elapsed
    else FAILED "tactic returned residual goals or failed"
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
        val result = run_goal budget (#mapped goal) goal
        val _ =
          if OS.Process.getEnv "HOLBENCHPROGRESS" = SOME "1" then
            TextIO.print (outcome_text result ^ "\n")
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
    val battery_results =
      if level < 2 orelse
         OS.Process.getEnv "HOLBENCHNOBATTERY" = SOME "1"
      then []
      else
        List.concat
          (map
            (fn goal =>
              map
                (fn tactic_id =>
                  (#id goal, tactic_id, run_goal budget tactic_id goal))
                (List.filter (fn id => id <> #mapped goal) battery))
            selected_goals)
  in
    {gated = gated, battery = battery_results}
  end

end
