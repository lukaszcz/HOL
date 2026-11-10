(* Internal owned traversal; unchanged roots retain their original terms. *)
signature SmtLib_OwnedCarrierTraversal =
sig
  type owner
  val begin : SmtReplayInvocationWork.portfolio ->
    {check_type : Type.hol_type -> unit,
     scope_opened : SmtReplayGraph.scope -> unit} -> owner
  type result
  val run_owned : owner -> {occurrence : int,view : SmtReplayGraph.source} ->
    result option
  (* Positive Goal is not an original assertion slot. NONE remains raw
     unchanged DATA; SOME must be a genuine registered positive view. *)
  (* Genuine assumption slot >=1. NONE is unchanged original DATA,
     with its public occurrence retained and no opened recipe. *)
  val run_assumption_owned : owner ->
    {occurrence : int,view : SmtReplayGraph.source option} -> result option
  val run_goal_owned : owner -> {view : SmtReplayGraph.source option} ->
    result option
  val denial_conversion : owner -> result ->
    {denial_view : SmtReplayGraph.source} -> SmtReplayProof.closed_conversion
  val canonical_endpoints : owner -> result ->
    {source : SmtReplayGraph.node,target : SmtReplayGraph.node}
  val canonical_fact : owner -> result -> SmtReplayProof.closed_fact
  (* Canonical RAW original Source conversion; not a past Work receipt. *)
  val source_conversion : owner -> result ->
    SmtReplayProof.closed_conversion
  val restore_original : owner -> result -> Thm.thm
  val run : owner -> {occurrence : int,view : SmtReplayGraph.source} ->
    Thm.thm option
  val close : owner -> unit
end
