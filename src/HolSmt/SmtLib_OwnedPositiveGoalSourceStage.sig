(* Optional carrier/whole-beta substage; no legacy default change. *)
signature SmtLib_OwnedPositiveGoalSourceStage =
sig
  type owner
  (* Original ordered assumptions FIRST, then positive Goal. SOME Goal
     requires both genuine positive and original-denial views up front.
     NONE leaves positive Goal and its denial unopened and unchanged. *)
  val begin : SmtReplayInvocationWork.portfolio ->
    {assumption_views : SmtReplayGraph.source list,
     goal_view : SmtReplayGraph.source option,
     denial_view : SmtReplayGraph.source option,
     check_type : Type.hol_type -> unit,
     scope_opened : SmtReplayGraph.scope -> unit} -> owner
  (* Optional views are ordered by actual original assumption occurrence.
     NONE remains unchanged original DATA; SOME is validated before build. *)
  val begin_provenance : SmtReplayInvocationWork.portfolio ->
    {assumption_views : SmtReplayGraph.source option list,
     goal_view : SmtReplayGraph.source option,
     denial_view : SmtReplayGraph.source option,
     check_type : Type.hol_type -> unit,
     scope_opened : SmtReplayGraph.scope -> unit} -> owner
  val build : owner -> SmtLib_GraphPreprocess.validation
  val close : owner -> unit
end
