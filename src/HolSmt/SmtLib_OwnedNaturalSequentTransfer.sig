(* Bounded whole-sequent natural prefix, not a whole SIMP implementation. *)
signature SmtLib_OwnedNaturalSequentTransfer =
sig
  type owner
  type plan
  type receipt
  val begin : SmtReplayInvocationWork.portfolio ->
    {traversal : SmtLib_CompactCarrierScheduler.owner,
     check_type : Type.hol_type -> unit,
     scope_opened : SmtReplayGraph.scope -> unit} -> owner
  val prepare : owner -> plan
  val execute : plan -> receipt
  val description_for : SmtReplayInvocationWork.portfolio -> receipt ->
    {source : SmtReplayGraph.source,target : SmtReplayGraph.source,
     variables : Term.term list,original_sources : SmtReplaySource.sources}
  (* Semantic equality receipt; no past Work/admission credit is exported. *)
  val transfer_theorem_for : SmtReplayInvocationWork.portfolio ->
    receipt -> Thm.thm
  (* Exact held original import, not opened-view canonical RAW syntax.
     Expected ownership and both immutable whole bridges are revalidated. *)
  val target_import_for : SmtReplayInvocationWork.portfolio -> receipt ->
    SmtReplayGraph.source
  (* Checked closed semantic evidence, never a caller proof callback or
     credit for earlier work. Must prove EXACT transferred whole sequent. *)
  val close_proof : SmtReplayInvocationWork.portfolio -> receipt ->
    SmtReplayProof.closed_fact -> Thm.thm
  (* Whole quantified query only. Original prefix stays exact; this does
     NOT reproduce the later legacy stripped GEN/DISCH solver query. *)
  val portfolio_for : SmtReplayInvocationWork.portfolio -> receipt ->
    SmtLib_GraphPreprocess.validation
  (* One SAME-receipt claim for the separately owned stripped receiver.
     Claim before admitted work; never reset on failure. Old receiver APIs
     cannot consume a claimed closure. No new Source, Work or counter. *)
  type query_claim
  val claim_query : SmtReplayInvocationWork.portfolio -> receipt -> query_claim
  val query_traversal_for : SmtReplayInvocationWork.portfolio -> query_claim ->
    SmtLib_CompactCarrierScheduler.owner
  val close_query_proof : SmtReplayInvocationWork.portfolio -> query_claim ->
    SmtReplayProof.closed_fact -> Thm.thm
  val close : owner -> unit
end
