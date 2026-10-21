(* Closed binder laws from authentic parsed proof-binding programmes. *)
signature SmtReplayOwnedValueBinder =
sig
  type plan
  type closed_law
  datatype requirement =
      ChildProgramme of Z3_GraphProofParser.proof_id
    | BindingProgramme of SmtLib_GraphFrontend.value_scoped_session
    | TargetProgramme of SmtLib_GraphParserValue.value
    | GeneralProgramme of SmtReplayOwnedScopedValueLift.requirement
  datatype preparation = Prepared of plan | Needs of requirement list
  (* Outside an action. The rule, immediate Bind and child rule are read
     from the actual held packet, not caller-supplied proof descriptors.
     First programme: one genuine annotated Bound variable, source-free
     reflexivity and an identity lambda on both target sides. Other child
     inferences and conditional Source closure remain explicit work. *)
  val prepare : SmtReplayInvocationWork.portfolio ->
    SmtLib_GraphPreprocess.graph_query ->
    Z3_GraphValueProofParser.proof SmtLib_GraphValueProof.packet ->
    {id:Z3_GraphProofParser.proof_id,
     native_contract:SmtReplayNativeContract.contract,
     check_type:Type.hol_type -> unit} -> preparation
  (* Same authenticated source-free child, with an actual Boolean
     forall/exists identity target prefix. Native ABS/AP_TERM and every
     realized input/result/ALPHA/Type portfolio are bounded first. *)
  val prepare_quantified : SmtReplayInvocationWork.portfolio ->
    SmtLib_GraphPreprocess.graph_query ->
    Z3_GraphValueProofParser.proof SmtLib_GraphValueProof.packet ->
    {id:Z3_GraphProofParser.proof_id,
     native_contract:SmtReplayNativeContract.contract,
     check_type:Type.hol_type -> unit} -> preparation
  (* Actual packet-owned finite child engine. All source-free fixed,
     equality, Boolean and recorded Clause children use the SAME workers;
     the actual target/closing portfolios settle before execution. The
     original atomic entries above remain unchanged specializations. *)
  val prepare_general : SmtReplayInvocationWork.portfolio ->
    SmtLib_GraphPreprocess.graph_query ->
    Z3_GraphValueProofParser.proof SmtLib_GraphValueProof.packet ->
    {id:Z3_GraphProofParser.proof_id,
     native_contract:SmtReplayNativeContract.contract,
     check_type:Type.hol_type -> unit} -> preparation
  (* Outside an action; once only. SAME fixed reflexivity and actual
     BinderEquality kernel worker. All native bodies, output/ALPHA ports,
     Types and surviving hypotheses are admitted before either worker. *)
  val execute : SmtReplayInvocationWork.portfolio -> plan -> closed_law
  (* Caller owns SAME action. Receipt retains the actual packet origin,
     child lifetime and original parent Scope. No Source occurrence is
     created and a copied record cannot authorize a named closed slot. *)
  val data_for : SmtReplayInvocationWork.portfolio -> closed_law ->
    {query:SmtLib_GraphPreprocess.graph_query,
     context:SmtLib_GraphParserValue.context,
     frame:SmtReplayOwnedScopeReceipt.receipt,
     binding:SmtLib_GraphValueProof.binding_frame,
     native_contract:SmtReplayNativeContract.contract,
     statement:SmtLib_GraphParserValue.value,
     law_node:SmtReplayGraph.node,fact:SmtReplayProof.closed_fact,
     aliases:(SmtLib_GraphParserValue.proof_term *
       SmtReplayGraph.node) list}
end
