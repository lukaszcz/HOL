(* Final original-Source contradiction from one genuine checked Value edge. *)
signature SmtReplayValueRealization =
sig
  type plan
  type result
  datatype requirement = ScopedBinderProgramme of
      SmtLib_GraphParserValue.proof_term
    | SourceCorrespondence of
        {value:SmtLib_GraphParserValue.proof_term,node:SmtReplayGraph.node}
  datatype preparation = Prepared of plan | Needs of requirement list
  (* Outside an action. Only the opaque input minted by the actual private
     Value block is accepted. All current assertions are proved through
     the retained actual query preprocessing, never assumed as Originals.
     A novel parser abstraction needs its genuine scoped binder programme. *)
  val prepare : SmtReplayInvocationWork.portfolio ->
    SmtReplayOwnedValueProof.realization_input ->
    {check_type:Type.hol_type -> unit} -> preparation
  (* Same original-Source programme with genuine graph-owned profiles
     forwarded to P's existing native freeze. No opaque size is inferred
     from a specialization theorem or from its compact formal name. *)
  val prepare_with_profiles : SmtReplayInvocationWork.portfolio ->
    SmtReplayOwnedValueProof.realization_input ->
    {profiles:SmtReplayGraph.policy_opaque_profile list,
     check_type:Type.hol_type -> unit} -> preparation
  (* Outside an action. The actual compact law is closed first and then
     instantiated simultaneously. No INST_TYPE, ALPHA or matching visits
     an expanded Value residue. A plan is consumed once. *)
  val execute : SmtReplayInvocationWork.portfolio -> plan -> result
  (* Caller owns SAME Work action. The conclusion is F and every native Hyp
     is an exact permitted original Source; this is not a binder receipt.
     Ordered current Source occurrence dependencies remain separate DATA. *)
  val contradiction_for : SmtReplayInvocationWork.portfolio ->
    result -> Thm.thm
  val source_dependencies_for : SmtReplayInvocationWork.portfolio ->
    result -> SmtReplayOwnedValueProof.source_lineage list
  val current_dependencies_for : SmtReplayInvocationWork.portfolio ->
    result -> int list
end
