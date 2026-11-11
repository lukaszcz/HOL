(* A parser-owned Value packet certifies no inference or Source fact. *)
signature SmtLib_GraphValueProof =
sig
  type 'proof packet
  type private_binding =
    {lexical_scope:SmtReplayGraph.scope,scope:SmtReplayGraph.scope,
     marker:SmtLib_GraphParserValue.value,kind:string,
     source:SmtLib_GraphParserValue.value option}
  type 'proof contents =
    {proof:'proof,context:SmtLib_GraphParserValue.context,
     metadata:SmtLib_GraphDeclarationMetadata.metadata,
     graph:SmtReplayGraph.graph,scope:SmtReplayGraph.scope,solver:string,
     versions:{requested:string,resolved:string},
     variables:SmtLib_GraphFrontend.value_solver_variable list,
     private_bindings:private_binding list}
  type 'proof parsed =
    {proof:'proof,terms:SmtLib_GraphFrontend.value_term list,
     bindings:SmtLib_GraphFrontend.value_scoped_session list,
     close:unit -> unit}
  (* Call create outside an action. It creates the genuine Value factory,
     then owns one action for the actual shared parser and publication.
     Reads run inside the SAME caller-owned Work action.
     Expected Work and exact query precede held context/mapping activation.
     The inventory provides eager lifetime checks, not a certificate of its
     completeness or of the caller's proof payload. The actual Z3 entry
     supplies its typed proof walker. Successful guard memoization uses the
     genuine graph revision, never past Work credit. Returned proof syntax
     still requires its context guards and checked inference on every use.
     No Value is reified, cast to a graph node or accepted as a proof. *)
  val create : SmtReplayInvocationWork.portfolio ->
    SmtLib_GraphPreprocess.graph_query ->
    {options:SmtLib_GraphFrontend.value_options,
     metadata:SmtLib_GraphDeclarationMetadata.metadata,
     description:{solver:string,version:string,
       policy:SmtLib_GraphFrontend.lexical_policy,reserved_names:string list},
     requested_version:string,tokens:unit -> string} ->
    (SmtLib_GraphValueTranslation.session -> 'proof parsed) -> 'proof packet
  val contents_with_policy_for : SmtReplayInvocationWork.portfolio ->
    SmtLib_GraphPreprocess.graph_query -> 'proof packet -> 'proof contents
  (* Caller owns SAME action, both to prepare and to invoke the result.
     Only genuine opaque packets qualify: their context has the privately
     constructed Mapping metadata guard, never a supplied callback.
     Preparation and graph-revision OR scope-retirement witness misses
     call the original validate. Its shared revision cache alone decides
     when parsed binding namespace callbacks run; no full walk is forced.
     BOTH witnesses must stay stable across validation before caching.
     Every call checks exact owner, packet/context/Work/declaration lifetime
     and pays its fixed work. Warm hits skip only repeated fixed Mapping
     guards and lifetime/assertion scans backed by BOTH witnesses, never
     caller callbacks that the original validate would have invoked.
     This is a syntax lifetime guard, not proof or future Work credit.
     Across caller callbacks invoke this guard again; it grants no lease.
     The generic contents getter retains its existing validation path. *)
  val prepare_scoped_guard_with_policy_for :
    SmtReplayInvocationWork.portfolio ->
    SmtLib_GraphPreprocess.graph_query -> 'proof packet -> unit -> unit
  (* Caller owns SAME action. SOME is the exact ordered syntax vector
     interpreted from emitted Mapping assertions in this packet context.
     NONE preserves old metadata. This is DATA, never proof or Source. *)
  val assertions_with_policy_for : SmtReplayInvocationWork.portfolio ->
    SmtLib_GraphPreprocess.graph_query -> 'proof packet ->
    SmtLib_GraphParserValue.value list option
  (* Outside an action. Authenticate an actual retained typed Bind first,
     then obtain its existing Scope receipt from the genuine factory's
     Value origin. No arbitrary scoped record or callback is adopted. *)
  val binding_scope_with_policy : SmtReplayInvocationWork.portfolio ->
    SmtLib_GraphPreprocess.graph_query -> 'proof packet ->
    SmtReplayOwnedScopeReceipt.receipt ->
    SmtLib_GraphFrontend.value_scoped_session ->
    SmtReplayOwnedScopeReceipt.receipt
  type binding_frame
  (* Outside an action. This additional port seals the actual packet
     origin, authentic Scope receipt and private factory binder inventory.
     A caller's scoped-session variable list is never adopted. Supplied
     parents retain the complete original getter and packet validation,
     including every parent callback through the frame receipt. *)
  (* Outside an action. Owns construction of the private root receipt;
     only this port permits paired-witness caching of frame geometry.
     No supplied parent receipt or arbitrary callback is adopted. *)
  val prepare_root_binding_frame_with_policy :
    SmtReplayInvocationWork.portfolio ->
    SmtLib_GraphPreprocess.graph_query -> 'proof packet ->
    SmtLib_GraphFrontend.value_scoped_session -> binding_frame
  (* Caller owns SAME action. Generic frames execute the original full
     getter, preserving callback order/count and the first exception.
     Only privately root-owned frames use the paired-witness packet guard
     and geometry cache. Every such invocation checks packet, root,
     factory/context and private lexical active flags. Full frame geometry
     and leaf/path checks run initially and on either revision OR retirement
     witness change. BOTH witnesses must stay stable across validation,
     with post-callback active checks, before caching/returning DATA.
     Generic receipt and binding getters are unchanged. *)
  val binding_frame_data_for : SmtReplayInvocationWork.portfolio ->
    SmtLib_GraphPreprocess.graph_query -> binding_frame ->
    {context:SmtLib_GraphParserValue.context,
     graph:SmtReplayGraph.graph,root:SmtReplayGraph.scope,
     scope:SmtReplayGraph.scope,
     parent:SmtReplayOwnedScopeReceipt.receipt,
     frame:SmtReplayOwnedScopeReceipt.receipt,
     variables:SmtLib_GraphParserValue.value list,
     descriptors:(string * string * Type.hol_type) list,binders:bool}
  (* Idempotent, outside an action too. Closes parser-owned scopes only. *)
  val close : 'proof packet -> unit
end
