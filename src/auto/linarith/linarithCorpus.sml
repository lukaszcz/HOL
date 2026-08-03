structure linarithCorpus :> linarithCorpus =
struct

open Abbrev testutils

datatype strength_outcome =
    StrengthSuccess
  | StrengthExpectedFailure of {error : string, remedy : string}

type strength_goal = int * strength_outcome * term

(* Isabelle's Arith_Examples.thy at f7e02b7e1f31 has 54 lemma goals,
   numbered here in source order.  The 34 num/bool ones are a strict
   subset: the other 20 need int, real or rat syntax and so can only
   run in instances/.  Both lists are spelled out, so that the count and
   the duplicate-freeness numbering_relation_holds asserts of each are
   things a mis-edited numbering can actually break. *)
val full_numbering =
  [1, 2, 3, 4, 5, 6, 7, 8, 9,
   10, 11, 12, 13, 14, 15, 16, 17, 18, 19,
   20, 21, 22, 23, 24, 25, 26, 27, 28, 29,
   30, 31, 32, 33, 34, 35, 36, 37, 38, 39,
   40, 41, 42, 43, 44, 45, 46, 47, 48, 49,
   50, 51, 52, 53, 54]

val core_numbering =
  [1, 3, 5, 7, 9,
   14, 15, 16, 17, 18,
   22, 23, 24,
   30, 31, 32, 33, 34, 35, 36, 37, 38, 39,
   40, 41, 42, 43, 44, 45, 46, 47, 48, 49,
   51]

fun check (name, predicate) =
  (tprint name;
   if predicate () then OK () else die "failed")

fun valid_closes tactic goal = null (#1 (Tactical.VALID tactic goal))

fun tactic_fails tactic goal =
  ((ignore (Tactical.VALID tactic goal); false)
   handle Feedback.HOL_ERR _ => true)

fun normalized_rhs (instance : linarithData.linarith_instance) tm =
  #2 (boolSyntax.dest_eq (Thm.concl (#norm_conv instance tm)))

fun canonical_form (instance : linarithData.linarith_instance) tm =
  #2 (boolSyntax.dest_eq
        (Thm.concl (Conv.QCONV (#norm_conv instance) tm)))

(* X_LE_X_SQUARED is not linear, so it can only reach a goal as a fact
   the table supplies.  That is what makes it a usable probe: a caller
   brackets one goal with it and asserts the goal is closed inside the
   bracket and refused outside, which no solver that snapshots the
   table can satisfy. *)
fun with_arith_fact operation =
  case ThmSetData.data_exportfns {settype = "arith"} of
      NONE => false
    | SOME export =>
        let
          val name =
            {Thy = "arithmetic", Name = "X_LE_X_SQUARED"}
          fun remove () =
            #remove export
              {thy = "arithmetic",
               remove = "arithmetic$X_LE_X_SQUARED"}
          val _ =
            #add export
              {thy = "arithmetic",
               named_thm =
                 (name, arithmeticTheory.X_LE_X_SQUARED)}
          val result =
            operation () handle e => (remove (); raise e)
          val _ = remove ()
        in
          result
        end

fun selftest_level () =
  case Option.mapPartial Int.fromString
         (OS.Process.getEnv "HOLSELFTESTLEVEL") of
      SOME level => level
    | NONE => 1

fun duplicates [] = []
  | duplicates (number :: rest) =
      if Lib.mem number rest then
        number :: duplicates (List.filter (fn n => n <> number) rest)
      else duplicates rest

fun outside numbering = List.filter (fn n => not (Lib.mem n numbering))

fun show numbers =
  String.concat (Lib.commafy (map Int.toString numbers))

(* The relation the two suites are partitioned by; asserted from both
   so that either one alone still catches a corpus drifting. *)
fun numbering_relation_holds () =
  null (duplicates full_numbering) andalso
  null (duplicates core_numbering) andalso
  List.length full_numbering = 54 andalso
  List.length core_numbering = 34 andalso
  null (outside full_numbering core_numbering) andalso
  List.length (outside core_numbering full_numbering) = 20

fun check_numbering {suite, numbering} goals =
  let
    val actual = map #1 goals
    val repeated = duplicates actual
    val missing = outside actual numbering
    val extra = outside numbering actual
    val _ = tprint (suite ^ " corpus numbering")
  in
    if not (null repeated) then
      die ("goal numbers occur more than once: " ^ show repeated)
    else if not (null missing) then
      die ("goal numbers missing from the corpus: " ^ show missing)
    else if not (null extra) then
      die ("goal numbers outside the canonical numbering: " ^ show extra)
    else if not (numbering_relation_holds ()) then
      die "core_numbering is no longer 34 of the 54 full_numbering goals"
    else OK ()
  end

(* Each budget carries the text the failure message names it by, so the
   number a reader is told to look for cannot drift from the number
   actually enforced. *)
val goal_budget = (Time.fromSeconds 30, "30 seconds")
val boundary_budget = (Time.fromSeconds 5, "5 seconds")

(* What running one goal to completion can amount to.  Refused carries
   origin and message together: a goal is refused for the documented
   reason or it is not refused as documented. *)
datatype attempt =
    Closed
  | Refused of string
  | Residual
  | Exceeded

fun attempt tactic (budget, _) proposition =
  (if Timeout.apply budget
        (fn () => valid_closes (tactic ()) ([], proposition)) ()
   then Closed
   else Residual)
  handle Timeout.TIMEOUT _ => Exceeded
       | Feedback.HOL_ERR error =>
           Refused
             (Feedback.top_function_of error ^ ": " ^
              Feedback.message_of error)

fun run_goal (suite, tactic, succeeded, boundaries)
             (number, outcome, proposition) =
  let
    val prefix = suite ^ " goal " ^ Int.toString number
    val (label, budget) =
      case outcome of
          StrengthSuccess => (prefix, goal_budget)
        | StrengthExpectedFailure {remedy, ...} =>
            (prefix ^ " (expected failure: " ^ remedy ^ ")",
             boundary_budget)
    val _ = tprint label
    val allowance = " budget of " ^ #2 budget
  in
    case (outcome, attempt tactic budget proposition) of
        (StrengthSuccess, Closed) =>
          (succeeded := !succeeded + 1; OK ())
      | (StrengthSuccess, Exceeded) =>
          die (prefix ^ " exceeded its" ^ allowance)
      | (StrengthSuccess, Residual) =>
          die (prefix ^ " was not closed by LINARITH_TAC")
      | (StrengthSuccess, Refused message) =>
          die (prefix ^ " was not proved by LINARITH_TAC: " ^ message)
      | (StrengthExpectedFailure {error, ...}, Refused message) =>
          if message = error then
            (boundaries := !boundaries + 1; OK ())
          else
            die (prefix ^ " failed with \"" ^ message ^
                 "\" rather than the expected \"" ^ error ^ "\"")
      | (StrengthExpectedFailure {remedy, ...}, Closed) =>
          die (prefix ^ " closed a goal recorded as beyond the method; " ^
               remedy)
      | (StrengthExpectedFailure _, Exceeded) =>
          die (prefix ^ " ran into its boundary instead of reporting " ^
               "it, exceeding the" ^ allowance)
      | (StrengthExpectedFailure _, Residual) =>
          die (prefix ^ " left goals behind instead of reporting that " ^
               "the method does not decide it")
  end

fun run_suite {suite, tactic, suite_budget,
               expected_successes, expected_boundaries} goals =
  let
    val succeeded = ref 0
    val boundaries = ref 0
    val started = Time.now ()
    val _ =
      List.app (run_goal (suite, tactic, succeeded, boundaries)) goals
    val elapsed = Time.- (Time.now (), started)
    val _ = tprint (suite ^ " suite count and time budget")
  in
    if !succeeded = expected_successes andalso
       !boundaries = expected_boundaries andalso
       Time.< (elapsed, suite_budget)
    then OK ()
    else die "failed"
  end

end
