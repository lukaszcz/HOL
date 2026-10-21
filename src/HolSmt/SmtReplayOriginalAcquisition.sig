(* Guarded atomic Ready proposal; general/default/full tariff deferred. *)
signature SmtReplayOriginalAcquisition =
sig
  type seed
  type work
  type native_limits =
    {semantic_limits:SmtReplayResourcePolicy.semantic_policy,
     import_limit:SmtReplayResourcePolicy.limit,
     type_work_limit:SmtReplayResourcePolicy.limit}
  type request =
    {construction_limits:SmtReplayResourcePolicy.graph_policy,
     semantic_limits:SmtReplayResourcePolicy.semantic_policy,
     work_limit:SmtReplayResourcePolicy.limit,native_limits:native_limits}
  val new_metadata : request -> Abbrev.goal -> seed
  (* Immutable metadata only: no Source node, bridge or admission receipt. *)
  val header_metadata : seed ->
    {graph:SmtReplayGraph.graph,root:SmtReplayGraph.scope}
  val original_metadata : seed -> Abbrev.goal
  val request_metadata : seed -> request
  val claim_work : seed -> work
  val validate_work : work -> unit
  (* Expected Work/header precedes stale held backing; expected retires. *)
  val validate_for : work -> seed -> SmtReplayGraph.graph ->
    SmtReplayGraph.scope -> unit
  val with_action : work -> (unit -> 'a) -> 'a
  val charge : work -> IntInf.int -> unit
  val remaining : work -> SmtReplayResourcePolicy.limit
  val request_for_work : work -> request
  val retire_work : work -> unit
  val close_seed : seed -> unit
  val audit : work -> {charged:IntInf.int,retired:bool,busy:bool,
    publication:string}
  (* Ready is reachable only through the closed retained-original producer. *)
  val require_ready : work -> unit
  (* NONE is unknown unfolded geometry of an unopened opaque original,
     never a size-one classification or a finite native admission receipt. *)
  type shape = {raw:IntInf.int option,inc:IntInf.int option,
    ann:IntInf.int option,root_type:IntInf.int}
  type acquisition_portfolio =
    {originals:shape list,denied:shape,equalities:shape list,
     native_program:string list,qualified_initial_inspection:bool,
     full_tariff:bool}
  (* No request/profile/term/theorem/callback argument. All finite semantic,
     native, Type and Work requests refuse in this NEW partial API only. *)
  val acquire_originals_uncapped : work -> unit
  val acquisition_portfolio_for : work -> acquisition_portfolio
  (* One-shot Source adoption, inside SAME owned action. Its data is issued
     only from a privately committed payload for this exact seed/work. *)
  val take_ready_sources : work -> seed ->
    {graph:SmtReplayGraph.graph,root:SmtReplayGraph.scope,
     goal:SmtReplayGraph.source,assumptions:SmtReplayGraph.source list,
     denied:SmtReplayGraph.source}

  (* Additive SAME action guard/debit ports. Neither issues native authority. *)
  val validate_owned_action : work -> unit
  val charge_guard : work -> IntInf.int -> unit

  (* Pending-only bounded native observation; not G Source/Ready authority.
     Goal first, then every original assumption; duplicates remain distinct.
     Unknown raw App/Abs/Clos/non-Bool returns NONE before any REFL effect. *)
  type boolean_original_view
  type boolean_original_summary =
    {original_count:IntInf.int,original_annotations:IntInf.int,
     reflexive_raw_nodes:IntInf.int,reflexive_annotations:IntInf.int,
     prospective_native_work:IntInf.int,full_tariff:bool}
  val prepare_boolean_original_view : work -> boolean_original_view option
  (* Expected owner first; SAME live action, Scope/epochs and paid revision.
     No raw native proof getter and no caller native/admission callback. *)
  val boolean_original_summary_for :
    work -> boolean_original_view -> boolean_original_summary


  (* FIRST attempt only; genuine canonical Bool Var/no assumptions.
     Actual Source is kept privately; no Ready or raw proof getter. *)
  val prepare_first_boolean_variable_source : work -> bool

  (* FIRST-only fresh canonical Bool Const, same Pending original Work;
     no assumptions, denial, portfolio, Ready or caller-supplied proof. *)
  val prepare_first_boolean_constant_source : work -> bool

  (* One-shot SAME Work owned ordered-original capture/progress PREFIX.
     No Source/native witness getter, executor, Ready or denial authority. *)
  type ordered_original_context
  val prepare_ordered_original_context : work -> ordered_original_context
  val ordered_original_progress_for : work -> ordered_original_context ->
    {originals:IntInf.int,completed:IntInf.int,
     usage:SmtReplayGraph.original_import_usage,
     revision:IntInf.int,denial_complete:bool}

  (* Stable Pending Source binding. Minted inside SAME owned action.
     Semantic observations require the complete private Ready payload.
     Neither this binding nor its pure header grants native admission. *)
  type source_binding
  val bind_pending_sources : work -> seed -> source_binding
  val source_binding_header : source_binding ->
    {graph:SmtReplayGraph.graph,root:SmtReplayGraph.scope}
  val source_binding_claim_work : source_binding -> work
  val source_binding_validate_work : work -> source_binding -> unit
  val source_binding_consume_attempt : source_binding -> unit
  val source_binding_refuse_legacy : source_binding -> unit
  val source_binding_sources : source_binding ->
    {graph:SmtReplayGraph.graph,root:SmtReplayGraph.scope,
     goal:SmtReplayGraph.source,assumptions:SmtReplayGraph.source list,
     denied:SmtReplayGraph.source}
  val source_binding_assumption_nodes :
    source_binding -> SmtReplayGraph.node list
  val source_binding_reconciliation :
    source_binding -> SmtReplayGraph.source list
  val source_binding_canonical_goal : source_binding -> Term.term
  val source_binding_original : source_binding -> Abbrev.goal
  val source_binding_require_ready : source_binding -> unit
  val source_binding_check_goal : source_binding -> Thm.thm -> unit
  val source_binding_check_contradiction :
    source_binding -> Thm.thm -> unit

  (* Advance one actual captured Bool Var/Const occurrence, using SAME
     request/counters/graph/context. No Source/native evidence is returned;
     InputsComplete is not denial completion or Ready publication. *)
  val advance_ordered_boolean_original : work -> ordered_original_context ->
    SmtReplayGraph.original_import_step

  (* Real closed denial, only from SAME already-completed atomic context.
     Even a successful denial leaves Acquiring; no Source/Ready getter. *)
  val complete_ordered_boolean_denial : work -> ordered_original_context -> unit

  (* Paid private membership/cache preparation. Success stays Acquiring;
     neither Sources, arrays, proofs nor a Ready setter are exposed. *)
  val prepare_ordered_original_sources : work -> ordered_original_context -> unit
  val ordered_source_preparation_for : work -> ordered_original_context ->
    {originals:IntInf.int,ordinary_occurrences:IntInf.int,
     allowed_occurrences:IntInf.int,revision:IntInf.int,
     prepared:bool,full_tariff:bool}

  (* Paid SAME-context prepared-payload/live-issuance validation only.
     Also validates the SAME privately committed payload in Ready. *)
  val validate_prepared_ordered_sources : work -> ordered_original_context -> unit

  (* One actual native finalisation from SAME prepared private context.
     Works in Acquiring or Ready; never changes publication or renews it. *)
  val finalise_ordered_boolean_goal : work -> ordered_original_context ->
    Thm.thm -> Thm.thm

  val prepare_ordered_function_child : work -> ordered_original_context -> unit
  (* Closed authenticated producer completion, not a caller Ready setter.
     Requires the exact privately prepared complete context, verifies all
     captured limits/roots again, preserves SAME Source/Work/counters. *)
  val complete_ordered_original_acquisition :
    work -> ordered_original_context -> unit
  (* Only S's opaque binding can select this closed captured programme.
     Original ordered Ready shares the same native quota/result latch;
     the existing all-Uncapped producer keeps its legacy closure semantics. *)
  val source_binding_close_contradiction :
    source_binding -> Thm.thm -> Thm.thm

  (* One constructor-owned raw application under the SAME original payer,
     before Seed publication; no replacement Work or caller origin flag. *)
  type owned_application_metadata
  val new_owned_boolean_application_metadata : request ->
    {function:Term.term,argument:Term.term} -> seed * owned_application_metadata
  val prepare_owned_application_context :
    work -> owned_application_metadata -> ordered_original_context
  val prepare_owned_application_children : work -> owned_application_metadata ->
    ordered_original_context -> unit


  (* Real private owned-App Source; SAME captured birth/context/payer.
     No Source/theorem getter, original completion or Ready setter. *)
  val complete_owned_application_source : work -> owned_application_metadata ->
    ordered_original_context -> unit


  (* SAME original Work/birth/context; actual App-aware denial programme.
     No caller Source/hash/term, no Ready or raw proof getter. *)
  val complete_owned_application_denial : work -> owned_application_metadata ->
    ordered_original_context -> unit


  (* Ready-only closed empty child birth/retirement on SAME original
     owner/context/meter. Ordinary external mutations still invalidate it.
     Receipt/scoped view is not native or general replay admission. *)
  type ordered_proof_scope
  val open_ordered_proof_scope : work -> ordered_original_context ->
    ordered_proof_scope
  val ordered_proof_scope_for : work -> ordered_original_context ->
    ordered_proof_scope -> SmtReplayGraph.scope
  val close_ordered_proof_scope : work -> ordered_original_context ->
    ordered_proof_scope -> unit

  (* Actual captured external original visitor, not semantic acquisition.
     Opaque DATA only; arbitrary binders stay retained until a real bounded
     opener/congruence consumer is implemented. Ready is not published. *)
  type external_original_stage
  type external_original_stage_summary =
    {observations:IntInf.int,public_views:IntInf.int,
     opaque_binders:IntInf.int,unresolved:IntInf.int,
     raw:IntInf.int option,inclusive:IntInf.int option,
     root_type_known:bool,revision:IntInf.int,
     semantic_nodes_published:IntInf.int,sources_issued:IntInf.int,
     originals_completed:IntInf.int}
  val prepare_ordered_external_original : work -> ordered_original_context ->
    external_original_stage
  val ordered_external_original_summary_for : work ->
    ordered_original_context -> external_original_stage ->
    external_original_stage_summary

  (* Full proof suffix from the caller-owned, status-positioned stream.
     Exact EOF, a fixed 32 MiB cap, and the original finite Work pay before
     an opaque one-use immutable input can be opened. No Source authority. *)
  type paid_cpc_certificate
  val capture_cpc_certificate : work -> TextIO.instream ->
    paid_cpc_certificate
  val with_cpc_certificate_input : work -> paid_cpc_certificate ->
    ((unit -> char option) -> 'a) -> 'a
  (* Same finite payer and caller-owned status-positioned descriptor;
     this opaque format cannot be consumed through the CPC input API. *)
  type paid_z3_certificate
  val capture_z3_certificate : work -> TextIO.instream ->
    paid_z3_certificate
  val with_z3_certificate_input : work -> paid_z3_certificate ->
    ((unit -> char option) -> 'a) -> 'a

end
