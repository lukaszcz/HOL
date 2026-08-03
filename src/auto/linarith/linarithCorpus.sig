(* Test support shared by the two Arith_Examples strength corpora, and
   not part of linarithLib's surface.  selftest.sml here runs the 34
   num/bool goals; instances/selftest.sml runs all 54 translations.  The
   goal terms cannot be shared, because this directory is pre-boss and
   cannot parse int, real or rat syntax, so each suite supplies its own
   list while this module owns the driver and the canonical numbering
   both lists are checked against. *)

signature linarithCorpus =
sig
  include Abbrev

  (* A corpus goal is either one the tactics are expected to close, or
     one they are expected to refuse.  Refusal is asserted only where
     refusing is the specified behaviour: a method boundary, a goal
     linear arithmetic is documented not to decide.  A goal that is
     merely hard, or slow, does not belong in the second category --
     failing it is not desired behaviour, and a suite that asserts the
     failure obstructs the work of removing it, and cannot tell a
     reported "no proof" from a tactic that never came back.

     Both fields of a boundary are checked.  error is the message the
     tactic must fail with, so that a goal recorded as beyond the method
     cannot be silently satisfied by an unrelated crash; the boundary
     budget is much tighter than the goal budget, so that a boundary is
     one the tactics report rather than one they run into.  remedy names
     the decision procedure that would close the goal, and is what the
     suite prints when the boundary moves. *)
  datatype strength_outcome =
      StrengthSuccess
    | StrengthExpectedFailure of {error : string, remedy : string}

  type strength_goal = int * strength_outcome * term

  (* The goal numbers of Isabelle's Arith_Examples.thy: full_numbering
     is all 54, core_numbering the 34 that survive translation to num.
     Stated here once so that the two suites, which run in different
     processes, cannot drift apart. *)
  val full_numbering : int list
  val core_numbering : int list

  val selftest_level : unit -> int

  (* check_numbering {suite, numbering} goals checks that goals uses
     exactly the numbers in numbering, once each, and that the two
     numberings above still stand in their documented relation. *)
  val check_numbering :
    {suite : string, numbering : int list} -> strength_goal list -> unit

  (* run_suite runs every goal under tactic against a per-goal budget,
     labelling each attempt suite ^ " goal " ^ number, then checks the
     outcome counts and the elapsed time against suite_budget.  tactic
     is a thunk built afresh per goal, so a tactic that snapshots the
     [arith] table sees the table each goal actually runs against. *)
  val run_suite :
    {suite : string,
     tactic : unit -> tactic,
     suite_budget : Time.time,
     expected_successes : int,
     expected_boundaries : int} -> strength_goal list -> unit
end
