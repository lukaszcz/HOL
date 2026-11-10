(* Invocation accounting DATA, not Root issuance or whole-stage admission. *)
signature SmtReplayInvocationWork =
sig
  type portfolio
  type entitlement
  type limits =
    {input_limit : int,output_limit : int,template_limit : int}
  datatype role = LawInstance | LocalCarrier | GoalDenial | ClosedRecord
    | FactAssembly | FinalFreeze
  val begin : SmtReplayGraph.graph -> SmtReplayGraph.scope ->
    SmtReplaySource.sources -> {limits : limits,work_limit : int} -> portfolio
  (* Same original claim/counter; authentic scope setup and every future
     root validation are charged before effect. Old begin stays unchanged. *)
  val begin_with_scope_guard : SmtReplayGraph.graph -> SmtReplayGraph.scope ->
    SmtReplaySource.sources -> {limits:limits,work_limit:int} -> portfolio
  (* Coupled typed metadata programs. Ordinary portfolios select NONE;
     no public Work method returns its private counter adapter. *)
  val priced_root_scope_path : portfolio -> SmtReplayGraph.scope_path option
  val prepare_backend_binding_guard : portfolio -> SmtReplayGraph.scope ->
    SmtReplayGraph.node SmtLib_GraphBackend.binding_origin ->
    SmtLib_GraphBackend.binding_guard option
  val validate_backend_binding_guard : portfolio -> SmtReplayGraph.scope ->
    SmtLib_GraphBackend.binding_guard -> unit
  val validate_priced_scope_frame : portfolio ->
    {graph:SmtReplayGraph.graph,root:SmtReplayGraph.scope,
     scope:SmtReplayGraph.scope,sources:SmtReplaySource.sources,
     limits:limits,epoch:int,symbols:int,path:SmtReplayGraph.scope_path}
    -> unit
  val original_sources : portfolio -> SmtReplaySource.sources
  val semantic_limits : portfolio -> limits
  val work_limit : portfolio -> int
  val validate : portfolio -> SmtReplayGraph.graph -> SmtReplayGraph.scope ->
    SmtReplaySource.sources -> limits -> unit
  val validate_template : portfolio -> SmtReplayGraph.graph ->
    SmtReplayGraph.scope -> int -> unit
  (* An action owns the one active frame. Reentry/failure retires it forever.
     spend/reserve/consume may run inside it, not another action. *)
  val with_step : portfolio -> (unit -> 'a) -> 'a
  val spend : portfolio -> int -> unit
  val reserve : portfolio -> {role : role,ordinal : int,amount : int} ->
    entitlement
  val consume : portfolio -> entitlement -> int -> unit
  val close : portfolio -> unit
  (* Caller owns the existing action. Closed SAME-counter planners keep
     the old remaining -> R/G -> spend guard order; a fixed callback-free
     phase header authenticates Busy before planning. Returned plans include
     future finish reservations: use R/G finishers without paying the cost
     again. Any failure retires Work and preserves the primary exception,
     including R.Limit before later guard failures. No meter or new action
     escapes. All modes supported. Original Work keeps W/A's old guards. *)
  val plan_lookup_int : portfolio ->
    'a ReplayRedblackPrivateWork.int_map * int ->
    'a ReplayRedblackPrivateWork.int_lookup
  val plan_lookup_string : portfolio ->
    ReplayRedblackPrivateWork.string_set * string ->
    ReplayRedblackPrivateWork.string_lookup
  val plan_insert_int : portfolio ->
    'a ReplayRedblackPrivateWork.int_map * int ->
    'a ReplayRedblackPrivateWork.int_insertion
  val plan_insert_string : portfolio ->
    ReplayRedblackPrivateWork.string_set * string ->
    ReplayRedblackPrivateWork.string_insertion
  val plan_insert_int_batch : portfolio ->
    'a ReplayRedblackPrivateWork.int_map * int list ->
    'a ReplayRedblackPrivateWork.int_batch
  (* Pays only the listing; the underlying batch must already be paid. *)
  val plan_list_int_batch : portfolio ->
    'a ReplayRedblackPrivateWork.int_batch ->
    'a ReplayRedblackPrivateWork.int_batch_listing
  val plan_placeholders : portfolio -> SmtReplayGraph.graph ->
    SmtReplayGraph.scope -> {nodes:SmtReplayGraph.node list} ->
    SmtReplayGraph.placeholder_plan

  (* Legacy finite Proof pay also queried remaining AFTER R/G and before
     spend: retain that third active guard on guarded finite portfolios.
     Same closed planning/finish contract as above, no extra semantic checks
     or mode refusal. Original Work retains the same W/A dispatch. *)
  val legacy_plan_lookup_int : portfolio ->
    'a ReplayRedblackPrivateWork.int_map * int ->
    'a ReplayRedblackPrivateWork.int_lookup
  val legacy_plan_lookup_string : portfolio ->
    ReplayRedblackPrivateWork.string_set * string ->
    ReplayRedblackPrivateWork.string_lookup
  val legacy_plan_insert_int : portfolio ->
    'a ReplayRedblackPrivateWork.int_map * int ->
    'a ReplayRedblackPrivateWork.int_insertion
  val legacy_plan_insert_int_batch : portfolio ->
    'a ReplayRedblackPrivateWork.int_map * int list ->
    'a ReplayRedblackPrivateWork.int_batch
  val legacy_plan_list_int_batch : portfolio ->
    'a ReplayRedblackPrivateWork.int_batch ->
    'a ReplayRedblackPrivateWork.int_batch_listing
  val legacy_plan_placeholders : portfolio -> SmtReplayGraph.graph ->
    SmtReplayGraph.scope -> {nodes:SmtReplayGraph.node list} ->
    SmtReplayGraph.placeholder_plan

  (* Reject a known exhausted private plan using the ordinary Work error.
     Retirement only: no debit, phase change to Busy or admission grant. *)
  val abort_work_limit : portfolio -> 'a
  (* Cached audit DATA remains readable after retirement; no admission grant. *)
  val audit : portfolio -> {charged : int,retired : bool}
  val begin_with_policy :
    SmtReplayGraph.graph -> SmtReplayGraph.scope ->
    SmtReplaySource.sources ->
    {limits : SmtReplayResourcePolicy.semantic_policy,
     work_limit : SmtReplayResourcePolicy.limit} ->
    portfolio
  val begin_with_scope_guard_policy :
    SmtReplayGraph.graph -> SmtReplayGraph.scope ->
    SmtReplaySource.sources ->
    {limits : SmtReplayResourcePolicy.semantic_policy,
     work_limit : SmtReplayResourcePolicy.limit} ->
    portfolio
  val semantic_policy : portfolio ->
    SmtReplayResourcePolicy.semantic_policy
  val work_policy : portfolio ->
    SmtReplayResourcePolicy.limit
  val remaining_policy : portfolio ->
    SmtReplayResourcePolicy.limit
  val audit_policy : portfolio ->
    {charged : IntInf.int, retired : bool}
  val validate_policy : portfolio ->
    SmtReplayGraph.graph -> SmtReplayGraph.scope ->
    SmtReplaySource.sources -> SmtReplayResourcePolicy.semantic_policy ->
    unit
  val validate_template_policy : portfolio ->
    SmtReplayGraph.graph -> SmtReplayGraph.scope ->
    SmtReplayResourcePolicy.limit -> unit

  (* Same inside/owner/Scope/epoch and retirement sequence as old payers;
     no IntInf.toInt conversion on the new route. Amounts are derived by
     owned programs exactly as today, not accepted as caller proof/fees. *)
  val spend_policy : portfolio -> IntInf.int -> unit
  (* Last check before a callback-free, publication-free native suffix.
     Validate and measure this SAME owner's actual action-return guard,
     then require its remaining allowance without debiting it twice. No
     credit/entitlement is minted; with_step retains its normal exit guard.
     No further payable operations may follow within the native suffix. *)
  val require_callback_free_return : portfolio -> unit
  val reserve_policy : portfolio ->
    {role : role, ordinal : int,
     amount : IntInf.int} -> entitlement
  val consume_policy : portfolio ->
    entitlement -> IntInf.int -> unit
  val validate_priced_scope_frame_policy : portfolio ->
    {graph:SmtReplayGraph.graph,root:SmtReplayGraph.scope,
     scope:SmtReplayGraph.scope,sources:SmtReplaySource.sources,
     limits:SmtReplayResourcePolicy.semantic_policy,epoch:int,symbols:int,
     path:SmtReplayGraph.scope_path} -> unit

  (* Guard bookkeeping only. Mode is passive DATA; debit accepts only
     unpriced PolicyWork, validates its live original owner in Idle/Busy,
     and spends the SAME allowance without changing phase or entitlement.
     Neither operation admits a native action or permits nested with_step. *)
  (* Passive constructor DATA. Only old begin selects true; do not infer
     this from a missing priced path (policy Work is distinct). *)
  val ordinary_legacy_guard_mode : portfolio -> bool
  val ordinary_policy_guard_mode : portfolio -> bool
  val spend_ordinary_guard_policy : portfolio -> IntInf.int -> unit
  (* Same-counter bookkeeping in Idle or Busy, for all Work modes. No
     action, native permission or entitlement is created. Owner guards
     precede this payer; charges must precede the metered traversal. *)
  val spend_guard_policy : portfolio -> IntInf.int -> unit
  (* Authenticated Value-origin guard. Preparation uses the SAME active
     action; validation is read-only bookkeeping in Idle or Busy and pays
     this Work's actual compiled program, never a supplied amount. *)
  type value_factory
  val create_value_factory_with_policy : portfolio ->
    {graph:SmtReplayGraph.graph,scope:SmtReplayGraph.scope,
     validate_metadata:unit -> unit,
     import_limit:SmtReplayResourcePolicy.limit,
     literal_limit:SmtReplayResourcePolicy.limit,
     binder_limit:SmtReplayResourcePolicy.limit} -> value_factory
  val validate_value_factory_for : portfolio -> value_factory -> unit
  val value_factory_data_for : portfolio -> value_factory ->
    SmtLib_GraphBackend.value_backend
  val close_value_factory : value_factory -> unit
  type value_binding_guard
  val prepare_value_backend_binding_guard : portfolio ->
    value_factory -> SmtReplayGraph.scope ->
    SmtLib_GraphParserValue.value SmtLib_GraphBackend.binding_origin ->
    value_binding_guard
  val validate_value_backend_binding_guard : portfolio ->
    value_binding_guard -> unit
  (* Caller owns SAME action. Metadata ONLY; pays fixed work and checks
     backend private lexical flags/epochs. No factory/context callback,
     leaf/path validation or cached binding DATA is supplied. The caller
     must separately validate its context and captured geometry. *)
  val validate_value_backend_binding_header_for : portfolio ->
    value_binding_guard -> unit
  val value_backend_binding_data_for : portfolio -> value_binding_guard ->
    {scope:SmtReplayGraph.scope,
     variables:SmtLib_GraphParserValue.value list,
     descriptors:(string * string * Type.hol_type) list,binders:bool}

  (* Claims the existing stable Pending Source exactly once. No new
     counter/meter/action/Source; SAME original A Work/request/header. *)
  val begin_original : SmtReplaySource.sources -> portfolio
  (* Closed ordered-original PREFIX, not native/denial/Ready authority.
     These A programmes own their action: do not nest inside with_step. *)
  type original_context
  val prepare_ordered_original_context : portfolio -> original_context
  val ordered_original_progress_for : portfolio -> original_context ->
    {originals:IntInf.int,completed:IntInf.int,
     usage:SmtReplayGraph.original_import_usage,
     revision:IntInf.int,denial_complete:bool}

  (* Fixed closed captured-original operations only. The SAME stored A
     Work/context owns all native/policy/graph admission and retirement.
     These calls own A actions: nested I.with_step is actual reentry. *)
  val advance_ordered_boolean_original : portfolio -> original_context ->
    SmtReplayGraph.original_import_step
  val complete_ordered_boolean_denial : portfolio -> original_context -> unit
  val prepare_ordered_original_sources : portfolio -> original_context -> unit
  (* Readonly summary of privately prepared payload, still Acquiring.
     No Source, proof, array, private hash or Ready publication is exposed. *)
  val ordered_source_preparation_for : portfolio -> original_context ->
    {originals:IntInf.int,ordinary_occurrences:IntInf.int,
     allowed_occurrences:IntInf.int,revision:IntInf.int,
     prepared:bool,full_tariff:bool}

  (* Fixed private-context goal finalisation on SAME hidden A Work.
     Requires actual prepared owned context, Acquiring or genuine Ready.
     Returns an ordinary theorem; does not publish or recapture a policy. *)
  val finalise_ordered_boolean_goal : portfolio -> original_context ->
    Thm.thm -> Thm.thm

  (* Closed private typed-child preparation on SAME original Work.
     Does not expose a child Source, complete a Bool original or publish. *)
  val prepare_ordered_function_child : portfolio -> original_context -> unit

  (* Complete only the authentic captured private prepared producer.
     SAME Source/Work/counters survive; A owns its action and all checks.
     No Source/array/G-context/proof/budget/Ready-flag argument exists. *)
  val complete_ordered_original_acquisition :
    portfolio -> original_context -> unit


  (* Genuine one-payer constructor route. The opaque application comes
     from the actual A constructor; no caller origin flag or Work getter. *)
  type owned_application
  val begin_owned_boolean_application : SmtReplayOriginalAcquisition.request ->
    {function:Term.term,argument:Term.term} ->
    {sources:SmtReplaySource.sources,portfolio:portfolio,
     application:owned_application}
  (* I issues exactly one opaque caller-to-CheckedGraph adoption token.
     Its Ready goal and OriginalPortfolio share the birth Work meter. *)
  type checked_owned_handoff
  val begin_ready_checked_owned_boolean_application :
    SmtReplayOriginalAcquisition.request ->
    {function:Term.term,argument:Term.term} -> checked_owned_handoff
  val take_ready_checked_owned_boolean_application :
    checked_owned_handoff ->
    {sources:SmtReplaySource.sources,portfolio:portfolio,goal:Abbrev.goal,
     owned:SmtReplayOriginalAcquisition.request}
  val close_ready_checked_owned_boolean_application :
    checked_owned_handoff -> unit

  val prepare_owned_application_context : portfolio -> owned_application ->
    original_context
  val complete_owned_application_source : portfolio -> owned_application ->
    original_context -> unit
  val complete_owned_application_denial : portfolio -> owned_application ->
    original_context -> unit


  (* Ready-only empty child workspace; no Work/context extractor, native
     grant, caller delta/budget, callback or refreshed Source identity. *)
  type ordered_proof_scope
  val open_ordered_proof_scope : portfolio -> original_context ->
    ordered_proof_scope
  val ordered_proof_scope_for : portfolio -> original_context ->
    ordered_proof_scope -> SmtReplayGraph.scope
  val close_ordered_proof_scope : portfolio -> original_context ->
    ordered_proof_scope -> unit

  (* SAME hidden original payer/context, no Work or native extraction. *)
  type external_original_stage
  val prepare_ordered_external_original : portfolio -> original_context ->
    external_original_stage
  val ordered_external_original_summary_for : portfolio -> original_context ->
    external_original_stage -> SmtReplayOriginalAcquisition.external_original_stage_summary

  (* Retains this exact OriginalPortfolio and Source binding around A's
     immutable paid full-proof receipt. The callback sees data only. *)
  type paid_cpc_certificate
  val capture_cpc_certificate : portfolio -> TextIO.instream ->
    paid_cpc_certificate
  val with_cpc_certificate_input : portfolio -> paid_cpc_certificate ->
    ((unit -> char option) -> 'a) -> 'a
  (* Same finite payer and caller-owned status-positioned descriptor;
     this opaque format cannot be consumed through the CPC input API. *)
  type paid_z3_certificate
  val capture_z3_certificate : portfolio -> TextIO.instream ->
    paid_z3_certificate
  val with_z3_certificate_input : portfolio -> paid_z3_certificate ->
    ((unit -> char option) -> 'a) -> 'a

  (* Caller owns the action. Paid inspection of this Work's actual issued
     role names returns unused ordinal DATA, not a reservation or credit.
     Use immediately before reserve; existing duplicate/amount checks stay
     authoritative. Prefer the next role ordinal at or above minimum; if
     that successor overflows, find a genuine available gap in that range. *)
  val unused_policy_ordinal : portfolio -> {role:role,minimum:int} -> int
  (* Caller owns the action. Same final malformed-minimum rejection when
     exporting a completed slot; no name search/reservation or Work credit. *)
  val validate_policy_ordinal_minimum : portfolio -> int -> unit

end
