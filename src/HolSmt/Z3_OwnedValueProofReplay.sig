(* Opt-in final original Goal transport for genuine checked Value packets. *)
signature Z3_SparseOwnedValueProofReplay =
sig
  type invocation
  datatype preparation = Prepared of invocation
    | ReplayNeeds of Z3_OwnedValueNamedReplay.requirement list
  datatype completion = Proved of
      {theorem:Thm.thm,
       dependencies:SmtReplayOwnedValueProof.source_lineage list}
    | RealizationNeeds of SmtReplayValueRealization.requirement list
  (* Outside an action. The actual packet/query and original Source owner
     are authenticated before adoption. Prepared transfers ownership of
     the packet to this invocation. ReplayNeeds leaves it with the caller.
     Only real typed Original/Current Source ports are used. *)
  val prepare_with_policy : SmtReplayInvocationWork.portfolio ->
    SmtLib_GraphPreprocess.graph_query ->
    Z3_GraphValueProofParser.proof SmtLib_GraphValueProof.packet ->
    {assertions:SmtLib_GraphParserValue.value list,
     native_contract:SmtReplayNativeContract.contract,
     profiles:SmtReplayGraph.policy_opaque_profile list,
     check_type:Type.hol_type -> unit} -> preparation
  (* Opt-in actual parsed specialization; uses only the sealed producer
     and its separately reserved CLOSED witnesses. Original/Current Source
     indices and the old preparation programme remain unchanged. Profiles
     also reach genuine original Source realization, not only Goal close. *)
  val prepare_with_specialization_with_policy :
    SmtReplayInvocationWork.portfolio ->
    SmtLib_GraphPreprocess.graph_query ->
    Z3_GraphValueProofParser.proof SmtLib_GraphValueProof.packet ->
    {assertions:SmtLib_GraphParserValue.value list,
     native_contract:SmtReplayNativeContract.contract,
     profiles:SmtReplayGraph.policy_opaque_profile list,
     check_type:Type.hol_type -> unit} -> preparation
  (* Explicit general bounded retained-Graph specialization. The SAME
     receipt/realization/Goal programme and canonical Source contract apply. *)
  val prepare_with_retained_specialization_with_policy :
    SmtReplayInvocationWork.portfolio ->
    SmtLib_GraphPreprocess.graph_query ->
    Z3_GraphValueProofParser.proof SmtLib_GraphValueProof.packet ->
    {assertions:SmtLib_GraphParserValue.value list,
     native_contract:SmtReplayNativeContract.contract,
     profiles:SmtReplayGraph.policy_opaque_profile list,
     check_type:Type.hol_type -> unit} -> preparation
  (* Outside an action, once only. The real receiver finishes its compact
     proof before Real401 prepares the original Source realization.
     RealizationNeeds performs no expanded realization/Goal closure and
     retains the live invocation/packet until close. Success closes the
     owned receiver and packet, returning an ordinary exact Goal theorem.
     Canonical allowed Source hypotheses are kept, never raw-Hyp casts. *)
  (* Same sealed finalization, with explicit genuine raw compatibility. *)
  val prepare_with_raw_resolution_with_policy :
    SmtReplayInvocationWork.portfolio ->
    SmtLib_GraphPreprocess.graph_query ->
    Z3_GraphValueProofParser.proof SmtLib_GraphValueProof.packet ->
    {assertions:SmtLib_GraphParserValue.value list,
     native_contract:SmtReplayNativeContract.contract,
     profiles:SmtReplayGraph.policy_opaque_profile list,
     check_type:Type.hol_type -> unit} -> preparation
  (* Additional actual scoped-identity Bind programme. Default modes
     and all genuine unfinished binder/Source programmes stay unchanged. *)
  val prepare_with_binders_with_policy :
    SmtReplayInvocationWork.portfolio ->
    SmtLib_GraphPreprocess.graph_query ->
    Z3_GraphValueProofParser.proof SmtLib_GraphValueProof.packet ->
    {assertions:SmtLib_GraphParserValue.value list,
     native_contract:SmtReplayNativeContract.contract,
     profiles:SmtReplayGraph.policy_opaque_profile list,
     check_type:Type.hol_type -> unit} -> preparation
  (* Source-free identity Bind, including actual forall/exists prefixes;
     the same owned realization and canonical Source Goal-close programme. *)
  val prepare_with_quantified_binders_with_policy :
    SmtReplayInvocationWork.portfolio ->
    SmtLib_GraphPreprocess.graph_query ->
    Z3_GraphValueProofParser.proof SmtLib_GraphValueProof.packet ->
    {assertions:SmtLib_GraphParserValue.value list,
     native_contract:SmtReplayNativeContract.contract,
     profiles:SmtReplayGraph.policy_opaque_profile list,
     check_type:Type.hol_type -> unit} -> preparation

  (* Explicit composition of the SAME retained-specialization, scoped
     binder and native-raw clause programmes. Each unfinished programme
     still leaves the whole invocation as typed Needs before inference. *)
  val prepare_with_owned_programmes_with_policy :
    SmtReplayInvocationWork.portfolio ->
    SmtLib_GraphPreprocess.graph_query ->
    Z3_GraphValueProofParser.proof SmtLib_GraphValueProof.packet ->
    {assertions:SmtLib_GraphParserValue.value list,
     native_contract:SmtReplayNativeContract.contract,
     profiles:SmtReplayGraph.policy_opaque_profile list,
     check_type:Type.hol_type -> unit} -> preparation
  val finish_with_policy : SmtReplayInvocationWork.portfolio ->
    invocation -> completion
  (* Idempotent; also closes a pending invocation. No Work is renewed. *)
  val close : invocation -> unit
end

(* Opt-in final original Goal transport for genuine checked Value packets. *)
signature Z3_OwnedValueProofReplay =
sig
  type invocation
  datatype preparation = Prepared of invocation
    | ReplayNeeds of Z3_OwnedValueNamedReplay.requirement list
  datatype completion = Proved of
      {theorem:Thm.thm,
       dependencies:SmtReplayOwnedValueProof.source_lineage list}
    | RealizationNeeds of SmtReplayValueRealization.requirement list
  (* Outside an action. The actual packet/query and original Source owner
     are authenticated before adoption. Prepared transfers ownership of
     the packet to this invocation. ReplayNeeds leaves it with the caller.
     Only real typed Original/Current Source ports are used. *)
  val prepare_with_policy : SmtReplayInvocationWork.portfolio ->
    SmtLib_GraphPreprocess.graph_query ->
    Z3_GraphValueProofParser.proof SmtLib_GraphValueProof.packet ->
    {assertions:SmtLib_GraphParserValue.value list,
     native_contract:SmtReplayNativeContract.contract,
     profiles:SmtReplayGraph.policy_opaque_profile list,
     check_type:Type.hol_type -> unit} -> preparation
  (* Opt-in actual parsed specialization; uses only the sealed producer
     and its separately reserved CLOSED witnesses. Original/Current Source
     indices and the old preparation programme remain unchanged. Profiles
     also reach genuine original Source realization, not only Goal close. *)
  val prepare_with_specialization_with_policy :
    SmtReplayInvocationWork.portfolio ->
    SmtLib_GraphPreprocess.graph_query ->
    Z3_GraphValueProofParser.proof SmtLib_GraphValueProof.packet ->
    {assertions:SmtLib_GraphParserValue.value list,
     native_contract:SmtReplayNativeContract.contract,
     profiles:SmtReplayGraph.policy_opaque_profile list,
     check_type:Type.hol_type -> unit} -> preparation
  (* Explicit general bounded retained-Graph specialization. The SAME
     receipt/realization/Goal programme and canonical Source contract apply. *)
  val prepare_with_retained_specialization_with_policy :
    SmtReplayInvocationWork.portfolio ->
    SmtLib_GraphPreprocess.graph_query ->
    Z3_GraphValueProofParser.proof SmtLib_GraphValueProof.packet ->
    {assertions:SmtLib_GraphParserValue.value list,
     native_contract:SmtReplayNativeContract.contract,
     profiles:SmtReplayGraph.policy_opaque_profile list,
     check_type:Type.hol_type -> unit} -> preparation
  (* Outside an action, once only. The real receiver finishes its compact
     proof before Real401 prepares the original Source realization.
     RealizationNeeds performs no expanded realization/Goal closure and
     retains the live invocation/packet until close. Success closes the
     owned receiver and packet, returning an ordinary exact Goal theorem.
     Canonical allowed Source hypotheses are kept, never raw-Hyp casts. *)
  (* Same sealed finalization, with explicit genuine raw compatibility. *)
  val prepare_with_raw_resolution_with_policy :
    SmtReplayInvocationWork.portfolio ->
    SmtLib_GraphPreprocess.graph_query ->
    Z3_GraphValueProofParser.proof SmtLib_GraphValueProof.packet ->
    {assertions:SmtLib_GraphParserValue.value list,
     native_contract:SmtReplayNativeContract.contract,
     profiles:SmtReplayGraph.policy_opaque_profile list,
     check_type:Type.hol_type -> unit} -> preparation
  (* Additional actual scoped-identity Bind programme. Default modes
     and all genuine unfinished binder/Source programmes stay unchanged. *)
  val prepare_with_binders_with_policy :
    SmtReplayInvocationWork.portfolio ->
    SmtLib_GraphPreprocess.graph_query ->
    Z3_GraphValueProofParser.proof SmtLib_GraphValueProof.packet ->
    {assertions:SmtLib_GraphParserValue.value list,
     native_contract:SmtReplayNativeContract.contract,
     profiles:SmtReplayGraph.policy_opaque_profile list,
     check_type:Type.hol_type -> unit} -> preparation
  (* Source-free identity Bind, including actual forall/exists prefixes;
     the same owned realization and canonical Source Goal-close programme. *)
  val prepare_with_quantified_binders_with_policy :
    SmtReplayInvocationWork.portfolio ->
    SmtLib_GraphPreprocess.graph_query ->
    Z3_GraphValueProofParser.proof SmtLib_GraphValueProof.packet ->
    {assertions:SmtLib_GraphParserValue.value list,
     native_contract:SmtReplayNativeContract.contract,
     profiles:SmtReplayGraph.policy_opaque_profile list,
     check_type:Type.hol_type -> unit} -> preparation

  (* Explicit composition of the SAME retained-specialization, scoped
     binder and native-raw clause programmes. Each unfinished programme
     still leaves the whole invocation as typed Needs before inference. *)
  val prepare_with_owned_programmes_with_policy :
    SmtReplayInvocationWork.portfolio ->
    SmtLib_GraphPreprocess.graph_query ->
    Z3_GraphValueProofParser.proof SmtLib_GraphValueProof.packet ->
    {assertions:SmtLib_GraphParserValue.value list,
     native_contract:SmtReplayNativeContract.contract,
     profiles:SmtReplayGraph.policy_opaque_profile list,
     check_type:Type.hol_type -> unit} -> preparation
  val finish_with_policy : SmtReplayInvocationWork.portfolio ->
    invocation -> completion
  (* Idempotent; also closes a pending invocation. No Work is renewed. *)
  val close : invocation -> unit
  (* Explicit individual-Hyp Source realization. The ordinary
     methods above retain their original static backend. *)
  structure Sparse : Z3_SparseOwnedValueProofReplay
end
