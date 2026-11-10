(* Owned local GEN/DISCH query; Original Source identity stays external. *)
signature SmtLib_OwnedStrippedNaturalQuery =
sig
  type owner
  type plan
  type query
  val begin : SmtReplayInvocationWork.portfolio ->
    {transfer:SmtLib_OwnedNaturalSequentTransfer.receipt,
     check_type:Type.hol_type -> unit,
     scope_opened:SmtReplayGraph.scope -> unit} -> owner
  val prepare : owner -> plan
  (* Semantic SAME-W whole-target equality, not a policy/past-work grant.
     Source must be EXACT this transfer target; no theorem/node pairing. *)
  val prepare_normalized : owner -> SmtReplayOwnedLargeProofCore.result -> plan
  (* Explicit following NO_SPLIT phase. Does not certify the prior
     contextful REV_FULL_SIMP policy from a semantic equality alone. *)
  val prepare_no_split : owner -> plan
  val prepare_normalized_no_split : owner ->
    SmtReplayOwnedLargeProofCore.result -> plan
  val execute : plan -> query
  val description_for : SmtReplayInvocationWork.portfolio -> query ->
    {frame:SmtReplayOwnedScopeReceipt.receipt,
     assumptions:SmtReplayGraph.node list,goal:SmtReplayGraph.node,
     denied:SmtReplayGraph.node,original_sources:SmtReplaySource.sources}
  (* Extra slots derive ONLY from this query, never caller-supplied Sources.
     Roots and checked laws are prospective replay discoveries. *)
  (* Exact CONTR/ACCEPT terminal reached by NO_SPLIT: no external solver
     and no caller proof. The retained fixed receiver closes its own Hyp. *)
  val solved_for : SmtReplayInvocationWork.portfolio -> query -> bool
  val close_solved : SmtReplayInvocationWork.portfolio -> query -> Thm.thm
  val freeze_for : SmtReplayInvocationWork.portfolio -> query ->
    {roots:SmtReplayGraph.node list,
     closed_facts:SmtReplayProof.closed_fact list,
     conversions:SmtReplayProof.closed_conversion list} -> SmtReplayProof.block
  (* The edge is THIS registered sparse block's contradiction. No theorem,
     Source map, normalization callback or old Work receipt is supplied. *)
  val close_for : SmtReplayInvocationWork.portfolio -> query ->
    SmtReplayProof.block -> SmtReplayProof.edge -> Thm.thm
  val close : owner -> unit
end
