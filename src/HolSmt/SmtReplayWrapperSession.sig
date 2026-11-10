(* Copyright (c) 2026 The HOL4 contributors. *)
signature SmtReplayWrapperSession =
sig
  type session
  (* The supplied validation must retain this exact original Source object.
     This is a lifetime/ownership boundary, not a preprocessing theorem. *)
  (* Establish the exact Source owner before preprocessing discovery. *)
  val start : SmtReplaySource.sources -> Abbrev.goal -> session
  (* Opaque GP discovery is permitted once, after start. A callback is not
     an aggregate resource or theorem-authority grant. *)
  val discover : session ->
    (SmtReplaySource.sources -> SmtLib_GraphPreprocess.validation) -> unit
  val prepare : SmtReplayGraph.graph -> SmtReplayGraph.scope ->
    SmtReplaySource.sources -> Abbrev.goal ->
    SmtLib_GraphPreprocess.validation -> session
  val graph : session -> SmtReplayGraph.graph
  val scope : session -> SmtReplayGraph.scope
  val sources : session -> SmtReplaySource.sources
  val preprocessing : session -> SmtLib_GraphPreprocess.validation
  val processed_goal : session -> Abbrev.goal
  val roots : session -> SmtReplayGraph.node list
  val begin_replay : session -> unit
  (* Only an exact original-goal theorem with canonical permitted Hyp may
     enter this boundary. Processed-goal theorems are not accepted. *)
  val accept : session -> Thm.thm -> unit
  (* SolverSpec's late validation must receive the SAME retained theorem and
     original occurrence list. After retirement, the immutable theorem was
     already checked while Source scope was active; no graph API is reopened.
     No raw sorting, aconv or Hyp transport occurs. *)
  val audit : session -> Abbrev.goal -> Thm.thm -> unit
  val close : session -> unit
  (* Explicit original Work is compared with cached ownership before any
     held preprocessing/session activation. No Work is inferred from GP. *)
  val validate_with_work : SmtReplayInvocationWork.portfolio -> session -> unit
  val discover_with_work : session ->
    (SmtReplaySource.sources ->
      {work : SmtReplayInvocationWork.portfolio,
       preprocessing : SmtLib_GraphPreprocess.validation}) ->
    SmtReplayInvocationWork.portfolio
  val preprocessing_with_work : SmtReplayInvocationWork.portfolio ->
    session -> SmtLib_GraphPreprocess.validation
  val processed_goal_with_work : SmtReplayInvocationWork.portfolio ->
    session -> Abbrev.goal
  val audit_with_work : SmtReplayInvocationWork.portfolio -> session ->
    Abbrev.goal -> Thm.thm -> unit

  val discover_with_policy : SmtReplayInvocationWork.portfolio -> session ->
    (SmtReplaySource.sources -> SmtLib_GraphPreprocess.validation) -> unit
  val validate_with_policy : SmtReplayInvocationWork.portfolio ->
    session -> unit
  val preprocessing_with_policy : SmtReplayInvocationWork.portfolio ->
    session -> SmtLib_GraphPreprocess.validation
  val processed_goal_with_policy : SmtReplayInvocationWork.portfolio ->
    session -> Abbrev.goal
  val audit_with_policy : SmtReplayInvocationWork.portfolio -> session ->
    Abbrev.goal -> Thm.thm -> unit
end
