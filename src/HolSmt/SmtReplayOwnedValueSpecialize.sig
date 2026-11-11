(* A checked local law over an actual retained original Value source. *)
signature SmtReplayOwnedValueSpecialize =
sig
  type plan
  type closed_law
  datatype requirement = RetainedOriginalSource of
      SmtLib_GraphParserValue.value
    | AtomicFalseOperand of SmtLib_GraphParserValue.value
    | SourceInstance of SmtLib_GraphParserValue.value
    | ArgumentProgramme of SmtLib_GraphParserValue.value list
    | SourceProfile of SmtReplayGraph.scope * SmtReplayGraph.node
    | RetainedOperand of SmtLib_GraphParserValue.value
  datatype preparation = Prepared of plan | Needs of requirement list
  (* Outside an action. This first specialization retains a genuine
     original graph-backed universal, one actual F argument and F target.
     Other Value programmes remain explicit DATA before block construction.
     Profiles are genuine graph-owned measurements, never native admission.
     Root/Scope and all actual native limits derive from Work and its NC.
     Preparation retains only paid metadata; native blocks are execute-only. *)
  val prepare : SmtReplayInvocationWork.portfolio ->
    SmtLib_GraphPreprocess.graph_query ->
    'proof SmtLib_GraphValueProof.packet ->
    {source:SmtLib_GraphParserValue.value,
     arguments:SmtLib_GraphParserValue.value list,
     target:SmtLib_GraphParserValue.value,
     profiles:SmtReplayGraph.policy_opaque_profile list,
     native_contract:SmtReplayNativeContract.contract,
     check_type:Type.hol_type -> unit} -> preparation
  (* Explicit general bounded retained-Graph programme. Every original
     universal, argument and target must have genuine retained backing.
     Their full unfolded/Type geometry is admitted before native syntax
     inspection. The SAME pure local predictor checks simultaneous capture-
     avoiding substitutions and target alpha identity before native freeze.
     Novel Value closures remain typed requirements, not reified operands. *)
  val prepare_retained : SmtReplayInvocationWork.portfolio ->
    SmtLib_GraphPreprocess.graph_query ->
    'proof SmtLib_GraphValueProof.packet ->
    {source:SmtLib_GraphParserValue.value,
     arguments:SmtLib_GraphParserValue.value list,
     target:SmtLib_GraphParserValue.value,
     profiles:SmtReplayGraph.policy_opaque_profile list,
     native_contract:SmtReplayNativeContract.contract,
     check_type:Type.hol_type -> unit} -> preparation
  (* Explicit ordinary-App target adapter. It first runs the unchanged
     retained preparation. Only its exact singleton RetainedOperand target
     may compile a bounded constructor image from actual typed Value Apps,
     genuine graph-backed non-Bound variables and constant atoms. The
     private image is not a caller node pairing, Source or equality proof.
     Original parsed target/statement ports are retained. No native import
     or theorem runs while missing/unsupported programmes remain DATA. *)
  val prepare_retained_application : SmtReplayInvocationWork.portfolio ->
    SmtLib_GraphPreprocess.graph_query ->
    'proof SmtLib_GraphValueProof.packet ->
    {source:SmtLib_GraphParserValue.value,
     arguments:SmtLib_GraphParserValue.value list,
     target:SmtLib_GraphParserValue.value,
     profiles:SmtReplayGraph.policy_opaque_profile list,
     native_contract:SmtReplayNativeContract.contract,
     check_type:Type.hol_type -> unit} -> preparation
  (* Outside an action; once only. SAME P owned local specialization
     programme, including full actual input/result/Type quotation before
     ASSUME/SPEC/DISCH. The private authorizing G block is then retired. *)
  val execute : SmtReplayInvocationWork.portfolio -> plan -> closed_law
  (* Caller owns SAME action. After full data_for authentication, retain
     this law and recheck its live backing/profiles and law closure only;
     no repeated proof correctness, owner linkage or native admission. *)
  val validate_lifetime_for : SmtReplayInvocationWork.portfolio ->
    closed_law -> unit
  (* Caller owns SAME action. Work precedes packet/Scope/fact backing.
     This opaque result is a CLOSED witness, not an Original/Current slot.
     A receiver retains the result and authenticates it with this getter;
     every later use needs this getter or validate_lifetime_for above.
     A copied data record grants no cursor interpretation or Source right. *)
  val data_for : SmtReplayInvocationWork.portfolio -> closed_law ->
    {query:SmtLib_GraphPreprocess.graph_query,
     context:SmtLib_GraphParserValue.context,
     frame:SmtReplayOwnedScopeReceipt.receipt,
     native_contract:SmtReplayNativeContract.contract,
     source:SmtLib_GraphParserValue.proof_term,
     arguments:SmtLib_GraphParserValue.proof_term list,
     target:SmtLib_GraphParserValue.proof_term,
     statement:SmtLib_GraphParserValue.value,
     source_node:SmtReplayGraph.node,target_node:SmtReplayGraph.node,
     law_node:SmtReplayGraph.node,fact:SmtReplayProof.closed_fact,
     original_occurrences:int list}
end
