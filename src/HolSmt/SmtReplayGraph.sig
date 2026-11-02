(* Copyright (c) 2026 The HOL4 contributors. *)
signature SmtReplayGraph =
sig
  type graph
  eqtype node
  eqtype scope
  datatype variable_kind = RigidSource | SolverFlexible | Generated | Bound
  datatype view =
      Variable of variable_kind * Term.term
    | Constant of KernelSig.kernelid
    | Application of node * node
    | OpaqueRetained
    | AdmittedBinder of {binder : node, body : node, frame : scope}
  datatype metric = RawNodes | BinderInclusiveNodes
  datatype variable_summary = Known of Term.term list | Unknown
  type source = {node : node, original : Term.term, bridge : Thm.thm}
  (* Recorded syntax views are constructed inside this graph, including
     application recipes. Discovery may call existing binder primitives;
     this operation is not whole-packet early resource admission. *)
  val record_opened_view : graph -> scope -> int -> node -> source
  (* Complete bounded rule recognition before genuine partial opening.
     NONE certifies no NUM/BAG/beta in the whole root, not unknown syntax.
     step is a resource/Scope hook, never proof or work authority. *)
  type partial_discovery
  val discover_partial : graph -> scope ->
    {original : node,maximum : int,scan_limit : int,
     step : unit -> unit} -> partial_discovery
  (* Additive completed projection capture, with its extra SAME-W hooks.
     discover_partial retains its original hook/debit sequence exactly. *)
  val discover_compact_partial : graph -> scope ->
    {original : node,maximum : int,scan_limit : int,
     step : unit -> unit} -> partial_discovery
  (* Same authentic discovery with additional charged construction memo. *)
  val discover_compact_shared_partial : graph -> scope ->
    {original : node,maximum : int,scan_limit : int,
     step : unit -> unit} -> partial_discovery
  (* Graph-owned declaration selection DATA, not a rewrite/proof licence.
     NONE from the selected scanner certifies absence of these declarations
     AND the old carrier/beta rules only. It says nothing about other rules. *)
  type discovery_heads
  val record_discovery_heads : graph -> scope ->
    {heads : node list,maximum : int,step : unit -> unit} -> discovery_heads
  val validate_discovery_heads : graph -> scope -> discovery_heads -> unit
  type selected_partial_discovery
  val discover_compact_selected_partial : graph -> scope ->
    {original : node,heads : discovery_heads,maximum : int,scan_limit : int,
     step : unit -> unit} -> selected_partial_discovery
  val selected_partial_data : graph -> scope -> discovery_heads ->
    selected_partial_discovery -> {original : node,view : source option}
  val validate_partial : graph -> scope -> partial_discovery -> unit
  val partial_view : graph -> scope -> partial_discovery -> source option
  (* Exact completed annotation DATA, not opened/raw origin or Work.
     Discovery records no-op syntax; bounded native measurement below
     makes no assertion about rewrite applicability or normalization.
     Counts preserve repeated child incidences; getters perform no scan. *)
  type opaque_profile
  val opaque_profile_for : graph -> scope -> node -> opaque_profile option
  val opaque_profile_data : graph -> scope -> opaque_profile ->
    {node : node,raw : int,inc : int,ann : IntInf.int,ty : IntInf.int,
     type_bytes : IntInf.int,types : Type.hol_type list}
  (* Actual bounded retained native syntax only. A matching sealed bound
     precedes ordinary body projection and observed annotation measurement.
     No graph view or theorem is created. The observer is used only during
     measurement, never by saved getters. No rewrite/Source permission. *)
  val profile_bounded_native_observed : graph -> scope ->
    {node:node,bound:SmtReplayImport.raw_bound,
     maximum:int,observe:unit -> unit} -> opaque_profile
  (* Actual operator/body projection from the SAME completed no-op scan.
     DATA only: depth is a query envelope, never a binder admission grant. *)
  type opaque_type_projection
  val opaque_type_projection_for : graph -> scope -> node ->
    opaque_type_projection option
  val opaque_type_projection_data : graph -> scope ->
    opaque_type_projection -> IntInf.int ->
    {node : node,work : IntInf.int,visits : int,
     binder_types : Type.hol_type list}
  (* Match the original ID and exact retained Source/bridge object before
     inspecting its original opaque Term. No caller equality is admitted. *)
  val validate_opened_view : graph -> scope -> node -> source -> unit
  (* Cached-only actual import/opened pair for this exact term and target.
     No arbitrary public source pair, discovery or first-anchor replacement. *)
  val imported_opened_source : graph -> scope -> Term.term -> node ->
    source * source
  (* Read-only provenance captured during first genuine binder admission.
     The whole view can have a later alpha-equivalent input: first_input and
     body remain the FIRST admission, never a newly discovered raw body.
     Both admission frames must still be active at every getter call.
     This API confers no constructor permission for a retired/rehome frame.
     Rehomed/constructed targets have no new first-admission origin here. *)
  type binder_origin
  val opened_binder_origin : graph -> scope -> node -> source -> binder_origin
  val binder_origin_data : graph -> scope -> binder_origin ->
    {first_input : Term.term,binder_term : Term.term,binder : node,
     frame : scope,body_frame : scope,body : source,node : node,
     original_node : node,whole : source}
  (* One-step CANONICAL descent from the exact retained first body/frame.
     Every scope argument below is the ORIGINAL opened-root caller scope,
     not a nested declaring/body frame. Getters validate both separately.
     No raw application-child incidence, proof or constructor permission is
     claimed. Rehome/constructed nodes without a first index refuse. *)
  type canonical_child
  type nested_binder_origin
  val binder_origin_body : graph -> scope -> binder_origin -> canonical_child
  val canonical_child_node : graph -> scope -> canonical_child -> node
  val canonical_application_children : graph -> scope -> canonical_child ->
    canonical_child * canonical_child
  val canonical_child_binder_origin : graph -> scope -> canonical_child ->
    nested_binder_origin
  val nested_binder_origin_data : graph -> scope -> nested_binder_origin ->
    {declaring_scope : scope,first_input : Term.term,binder_term : Term.term,
     binder : node,frame : scope,body_frame : scope,body : source,node : node,
     first_whole : source}
  val nested_binder_origin_body : graph -> scope -> nested_binder_origin ->
    canonical_child
  (* Canonical closure frames captured only at genuine NEW construction.
     Old abstraction has no actual body-frame argument and gets no record.
     Known rehomes retain original creation frames, never a raw origin. *)
  val recorded_abstraction : graph -> scope -> int ->
    {binder : node,body : node,body_frame : scope} -> node
  type closure_child
  type binder_closure
  val closure_root : graph -> scope -> node -> closure_child
  val closure_child_node : graph -> scope -> closure_child -> node
  val closure_application_children : graph -> scope -> closure_child ->
    closure_child * closure_child
  val closure_child_binder : graph -> scope -> closure_child -> binder_closure
  val binder_closure : graph -> scope -> node -> binder_closure
  (* Optional DATA lookup for bounded schema readers. NONE only means no
     recorded constructor; present records retain every ordinary guard. *)
  val recorded_binder_closure : graph -> scope -> node -> binder_closure option
  val binder_closure_data : graph -> scope -> binder_closure ->
    {node : node,node_frame : scope,creation_node : node,
     declaring_scope : scope,binder : node,binder_term : Term.term,
     binder_frame : scope,body : node,body_frame : scope,rehomed : bool}
  val binder_closure_body : graph -> scope -> binder_closure -> closure_child
  (* Identity syntax only, never first raw provenance. The owned caller
     forecasts/debits REFL before execution. Retained authentic children
     preserve source and generated backing lifetimes in later validation. *)
  (* Retained Alpha-only discovery recipe. No caller source/theorem pair,
     raw child incidence, symbol-work quote or past Work credit. maximum is
     the caller's existing metadata visit allowance, not a semantic cap. *)
  type discovered_alpha
  val cached_opened_view : graph -> scope -> node -> source
  val discovered_alpha : graph -> scope -> int -> node -> discovered_alpha
  val validate_discovered_alpha : graph -> scope -> discovered_alpha -> unit
  val discovered_alpha_data : graph -> scope -> discovered_alpha ->
    {original : node,source : source,annotation : closure_child,visits : int}
  (* Separate private partial/full/registered-identity projection. The old
     discovered_alpha API retains its complete-opening contract. *)
  type carrier_alpha
  val carrier_alpha_for : graph -> scope -> int ->
    {original : node,source : source} -> carrier_alpha
  (* SAME registered-opening metadata programme. Each actual scan visit
     invokes the caller's existing policy step inside its active action;
     this performs no opening, proof, int projection or native admission. *)
  val carrier_alpha_for_with_policy : graph -> scope ->
    {original:node,source:source,step:unit -> unit} -> carrier_alpha
  val validate_carrier_alpha : graph -> scope -> carrier_alpha -> unit
  val carrier_alpha_data : graph -> scope -> carrier_alpha ->
    {original : node,source : source,annotation : closure_child,visits : int}
  (* Existing exact private child Source, registered with all its guards.
     No caller source triple or proof may be supplied. *)
  val carrier_alpha_source_for : graph -> scope -> carrier_alpha -> source
  val carrier_alpha_application_children : graph -> scope -> int ->
    carrier_alpha -> carrier_alpha * carrier_alpha
  (* Genuine registered Alpha-owned raw operator/body/domain traversal.
     Logical path envelope only: no hidden lazy closure forcing grant. *)
  val record_opened_type_projection : graph -> scope -> int ->
    carrier_alpha -> opaque_type_projection
  val opened_type_projection_visits : graph -> scope ->
    opaque_type_projection -> int
  type identity_closure_view_plan
  val plan_identity_closure_view : graph -> scope -> int ->
    {target : closure_child,retain : closure_child list} ->
    identity_closure_view_plan
  val identity_closure_view_node : identity_closure_view_plan -> node
  val execute_identity_closure_view : identity_closure_view_plan -> source
  val record_identity_closure_view : graph -> scope -> int ->
    {target : closure_child,retain : closure_child list} -> source
  datatype origin = ImportedSource | ConstructedSyntax
  val origin : graph -> node -> origin
  (* First admitted exact source occurrence and its checked origin bridge. *)
  val source_anchor : graph -> node -> source option
  datatype role = Atom | Conjunction | Disjunction | Clause | Context
                | Let | ProofBoundary
  datatype occurrence = Occurrence of
    {node : node, scope : scope, role : role, children : occurrence list}

  val new : unit -> graph
  (* Actual successful node allocations/accesses and intern hit/miss events.
     Entry accesses are events, not distinct visited nodes or Work credit. *)
  type node_statistics =
    {node_creations : IntInf.int,node_accesses : IntInf.int,
     intern_hits : IntInf.int,intern_misses : IntInf.int,total_nodes : int}
  val with_node_statistics : graph -> scope -> (unit -> 'a) ->
    'a * node_statistics
  val root_scope : graph -> scope
  val validate_scope : graph -> scope -> unit
  (* Read-only constructor guards, including captured Type/Term epochs on
     paid graphs. Does not intern syntax or change validation snapshots. *)
  val validate_semantic_scope : graph -> scope -> unit
  (* Close lexical/proof lifetimes without deleting admitted binder metadata.
     Constructors and proof owners reject these scopes after closure. *)
  (* Authentic lifecycle DATA. No proof, metric or Work admission grant.
     The passed caller must still be active in THIS graph. *)
  (* Registry publication and retirement witness; DATA only. It gives no
     proof, syntax admission, lifetime grant or prior Work credit. *)
  val validation_revision : graph -> scope -> IntInf.int
  val scope_retirement_epoch : graph -> scope -> IntInf.int
  val close_scope : graph -> scope -> unit
  val scope_visible : graph -> scope -> scope -> bool
  (* Each binding maps a typed variable to its interpretation in this frame.
     The parent and every bound node must belong to this graph. *)
  val new_scope : graph -> scope -> (Term.term * node) list -> scope
  (* Copy actual lexical binding tables into a NEW construction child of
     the authentic construction ancestor. No old frame is revived. *)
  val new_construction_scope : graph ->
    {lexical : scope,construction : scope} -> scope
  val node_id : node -> int
  val scope_id : scope -> int
  val node_scope : graph -> node -> scope
  val type_id : graph -> node -> int
  val type_of : graph -> node -> Type.hol_type
  val representative : graph -> node -> Term.term
  val view : graph -> node -> view
  val variable : graph -> scope -> variable_kind -> Term.term -> node
  (* Parser binder: preserve lexical lookup separately from fresh HOL name. *)
  val fresh_bound_variable : graph -> scope -> Term.term -> node
  (* Parser-private solver declaration: keep the lexical term in the parser
     namespace and use this fresh representative for the owned node. *)
  val fresh_flexible_variable : graph -> scope -> Term.term -> node
  val constant : graph -> scope -> Term.term -> node
  (* Fixed Boolean grammar only. Debit preparation and prospective legacy
     table/type/scope work BEFORE each constructor. Caller separately prepays
     Term.mk_comb operand/type walks. Paid graphs retain their internal meter.
     These bookkeeping fees grant no proof/native admission authority. *)
  val implication_with_graph_debit : graph -> scope ->
    (IntInf.int -> unit) ->
    node list -> node -> node
  (* Typed declaration identity, independent of lexical aliases. Interns
     only Type metadata, without creating a variable or reserving its name. *)
  val declaration_variable_key : graph -> scope -> Term.term -> string * int
  (* Resolve environments without claiming an alpha source bridge. *)
  val resolve_variable : graph -> scope -> Term.term -> node
  (* Lexical aliases retain their owned kind; a declaration is the checked
     default when this name has no binding in the active environment. *)
  val resolve_reference : graph -> scope -> Term.term -> node -> node
  val application : graph -> scope -> node * node -> node

  (* The caller owns application/closure admission. This imports exposed
     application nodes up to its existing DAG contract and retains binders
     opaquely. Incomplete imports raise HOL_ERR and certify no absence fact.
     It never opens an abstraction while hashing or importing. *)
  (* Metadata-only preflight precedes the first new import theorem.
     Batches may plan every source before executing any source bridge. *)
  type import_plan
  val plan_imports : graph -> scope -> int -> Term.term list ->
    import_plan list
  val plan_import : graph -> scope -> int -> Term.term -> import_plan
  val import_types : import_plan -> Type.hol_type list
  val execute_import : import_plan -> source
  val import : graph -> scope -> int -> Term.term -> source
  (* Retain an actual uninterpreted operand without opening its syntax.
     New leaves intern only the public result Type, with UNKNOWN size/FV.
     Existing imports may retain their precise metadata. The exact native
     REFLEXIVITY bridge supplies no rewrite authority. *)
  val retain_source : graph -> scope -> Term.term -> source
  (* Raw-size admission precedes dest_abs and bounded alpha comparison.
     Nested binders are admitted under the same enclosing raw-size limit. *)
  val admit_binder : graph -> scope -> int -> Term.term -> source
  (* Parser-owned binders: the graph body must already be bounded and must
     contain no opaque node before construction of the HOL abstraction. *)
  val abstraction : graph -> scope -> int -> node * node -> node

  (* Closed, checked equality; IDs and pointer identity never establish a
     semantic rewrite. Opaque independent residues cannot be aligned. *)
  val equality : graph -> node * node -> Thm.thm
  (* Preserve owned variable IDs when a completed bounded block returns to
     an ancestor frame. Closed admitted binders remain retained atoms;
     applications use checked local congruence. Unknown dependencies cannot
     authorize a frame change. *)
  val rehome : graph -> scope -> node -> source
  val reachable : graph -> node list -> node list
  (* Enclosing proof blocks treat completed admitted binders as atoms. *)
  val block_reachable : graph -> node list -> node list
  val dag_nodes : graph -> node list -> int
  (* Saturates at limit + 1; NONE means an opaque node has unknown size. *)
  val unfolded_nodes : graph -> metric -> int -> node -> int option
  val unfolded_nodes_observed : (unit -> unit) -> graph -> metric -> int ->
    node -> int option
  (* Computed on demand over reachable IDs. Unknown is never closed. *)
  val free_variables : graph -> node -> variable_summary
  (* Identity/ownership-preserving version; NONE is an unknown opaque view. *)
  val free_variable_nodes : graph -> node -> node list option
  (* Optional query-local cost attribution, not proof/admission evidence.
     Compare counts scalar key comparisons (including list items).
     Excluded reports each materialized exclusion list; Visited reports the
     lists retained as fresh visited keys. Variable reports output-map writes
     by node ID; Type reports canonical type-ID reads for typed output keys.
     These are logical entries/items, not native heap bytes or a constant-time
     claim for maps, strings, type admission or public kernel primitives.
     No observer or full dependency set is retained at graph nodes. *)
  datatype dependency_event = DependencyVisit | DependencyCompare
    | DependencyExcluded of int list | DependencyVisited of int list
    | DependencyVariable of int | DependencyType of int
  val free_variable_nodes_observed : (dependency_event -> unit) ->
    graph -> node -> node list option
  val free_variables_observed : (dependency_event -> unit) ->
    graph -> node -> variable_summary

  (* Reserve admitted frame/schema variables before allocating placeholders.
     Known source variables and solver names are reserved automatically.
     An opaque source object's uninspected free names need not be reserved:
     closed simultaneous realization inserts it without recursive subst. *)
  val reserve_names : graph -> Term.term list -> unit
  (* Exact graph-owned placeholder/node pairs are already reserved.
     Other schema holes retain ordinary name-collision checks. No allocation. *)
  val reserve_schema_holes : graph -> (Term.term * node) list -> unit
  val placeholder : graph -> node -> Term.term
  (* Atom and ProofBoundary stop extraction; Let follows only its final
     (body) child. Context/Clause are ordered occurrence containers, not
     evidence that their node is a conjunction/disjunction. Explicit binary
     connective roles must match their actual graph children. Only Let and
     ProofBoundary may enter descendant scopes; every node must be visible. *)
  val occurrence_leaves : occurrence -> occurrence list
  val validate_occurrence : graph -> occurrence -> unit
(* Graph-owned placeholder planning and one-shot publication. *)
type placeholder_plan
val plan_placeholders : graph -> scope ->
  {nodes : node list,remaining_work : int} -> placeholder_plan
(* Additive SAME-meter planner. Each instruction is paid before its effect;
   Refusal retains its diagnostic and successful prefix. Costs include paid
   future mint/finish reservations: do NOT charge plan_cost again.
   Validation still requires the caller's separate guard payment. *)
val plan_placeholders_with_meter : graph -> scope ->
  ReplayRedblackPrivateWork.scope_meter ->
  {nodes : node list} -> placeholder_plan
(* Immutable DATA from the genuine planner; not a Work/Root grant. *)
val placeholder_plan_cost : placeholder_plan -> IntInf.int
val placeholder_plan_guard_cost : placeholder_plan -> IntInf.int
val placeholder_plan_names : placeholder_plan -> (node * string) list
val placeholder_plan_bindings :
  placeholder_plan -> (node * string * Type.hol_type) list
(* The P owner pays the authentic guard cost from SAME W before each call;
   no caller-supplied charge/guard pair and no renewed allowance. *)
val validate_placeholder_plan : graph -> scope -> placeholder_plan -> unit
(* One complete batch mint. SAME graph/caller/original state is checked
   BEFORE any new Term or table publication. Old interfaces stay present. *)
val mint_placeholders : graph -> scope -> placeholder_plan -> unit

(* Exact input order, held cached terms and newly minted terms. *)
val mint_placeholder_terms : graph -> scope -> placeholder_plan ->
  (node * Term.term) list

  (* Authentic immutable scope path and its actual fixed-map/setup program.
     DATA only. The Work owner must pay before each validation. *)
  type scope_path
  val prepare_scope_path : graph -> scope ->
    {remaining_work:int} -> scope_path
  val scope_path_setup_work : scope_path -> IntInf.int
  val scope_path_validation_work : scope_path -> IntInf.int
  val validate_scope_path : graph -> scope -> scope_path -> unit
  (* Authentic prepared-path validation programme plus revision field/read.
     Caller pays SAME Work before EVERY use; this is lifecycle DATA only. *)
  val scope_path_revision_work : scope_path -> IntInf.int
  val validation_revision_with_scope_path :
    graph -> scope -> scope_path -> IntInf.int
  (* Typed same-counter graph paths for genuine Backend binding origins. *)
  type binding_scope_path
  val prepare_shared_scope_path : graph -> scope ->
    ReplayRedblackPrivateWork.scope_meter -> scope_path * scope list
  val prepare_binding_scope_path : graph -> scope -> scope ->
    ReplayRedblackPrivateWork.scope_meter -> binding_scope_path
  val binding_scope_path_work : binding_scope_path -> IntInf.int
  val validate_binding_scope_path : graph -> scope -> scope ->
    binding_scope_path -> unit
  val binding_node_scope : graph -> node ->
    ReplayRedblackPrivateWork.scope_meter -> scope
  (* Explicit optional import ceiling; same exposed application-DAG
     metric as old import, abstractions opaque. No default or Work grant. *)
  type policy_import_plan
  val plan_imports_with_policy : graph -> scope ->
    SmtReplayResourcePolicy.limit -> Term.term list -> policy_import_plan list
  val plan_import_with_policy : graph -> scope ->
    SmtReplayResourcePolicy.limit -> Term.term -> policy_import_plan
  val import_types_with_policy : policy_import_plan -> Type.hol_type list
  val execute_import_with_policy : policy_import_plan -> source
  val import_with_policy : graph -> scope ->
    SmtReplayResourcePolicy.limit -> Term.term -> source
  (* Paid immutable native raw geometry only, for SAME live ROOT caller.
     Non-root callers return NONE before payload; foreign owners fail first.
     Exact physical root memo and actual public App/atom shape are required;
     each opaque leaf needs a genuine policy native capture in THIS graph.
     No legacy scope/entry walk is performed by hot metadata notes. No opening,
     Source, profile/lifetime or native admission permission is returned.
     NONE is an incomplete/cold probe: callers MUST retain raw admission.
     SOME may exceed maximum and MUST still be checked against that limit.
     The observer pays metadata plus fixed root/epoch guards on the caller's
     existing meter. Checks are fresh after callbacks, including bulk debits.
     Paid semantic indices additionally retain their own coupled guard. *)
  val imported_native_raw_geometry_observed : graph -> scope ->
    {original:Term.term,maximum:SmtReplayResourcePolicy.limit,
     observe:IntInf.int -> unit} -> IntInf.int option

  (* Same genuine path/mutable frame program, exact optional allowance.
     These require the coupled R policy meter, not an old int projection. *)
  val prepare_scope_path_with_policy : graph -> scope ->
    {remaining_work:SmtReplayResourcePolicy.limit} -> scope_path
  val prepare_shared_scope_path_policy : graph -> scope ->
    ReplayRedblackPrivateWork.scope_meter -> scope_path * scope list
  val prepare_binding_scope_path_policy : graph -> scope -> scope ->
    ReplayRedblackPrivateWork.scope_meter -> binding_scope_path

  val abstraction_with_policy : graph -> scope ->
    SmtReplayResourcePolicy.limit -> node * node -> node
  val recorded_abstraction_with_policy : graph -> scope ->
    SmtReplayResourcePolicy.limit ->
    {binder:node,body:node,body_frame:scope} -> node
  val admit_binder_with_policy : graph -> scope ->
    SmtReplayResourcePolicy.limit -> Term.term -> source
  val record_opened_view_with_policy : graph -> scope ->
    SmtReplayResourcePolicy.limit -> node -> source
  type policy_partial_discovery
  type policy_opaque_profile
  (* Optional publication, NEVER part of discovery's scan/step programme.
     The selecting caller must fund observe on its SAME Work, using only
     allowance spare after mandatory continuation/action-return costs.
     Insufficient remaining_work discards the staged batch and returns
     false; paid prefixes remain charged. Observer exceptions propagate
     unchanged. Genuine completed captures only; no native permission. *)
  val publish_policy_native_raw_geometry_observed : graph -> scope ->
    {profiles:policy_opaque_profile list,
     remaining_work:SmtReplayResourcePolicy.limit,
     observe:IntInf.int -> unit} -> bool
  val discover_partial_with_policy : graph -> scope ->
    {original:node,maximum:SmtReplayResourcePolicy.limit,
     scan_limit:SmtReplayResourcePolicy.limit,step:unit->unit} ->
    policy_partial_discovery
  val validate_partial_with_policy : graph -> scope ->
    policy_partial_discovery -> unit
  val partial_view_with_policy : graph -> scope ->
    policy_partial_discovery -> source option
  val partial_discovery_policy_data : graph -> scope ->
    policy_partial_discovery ->
    {maximum:SmtReplayResourcePolicy.limit,
     scan_limit:SmtReplayResourcePolicy.limit,scans:IntInf.int}
  val partial_profiles_with_policy : graph -> scope ->
    policy_partial_discovery -> policy_opaque_profile list
  val opaque_profile_data_with_policy : graph -> scope ->
    policy_opaque_profile ->
    {node:node,raw:IntInf.int,inc:IntInf.int,ann:IntInf.int,ty:IntInf.int,
     type_bytes:IntInf.int,types:Type.hol_type list}

  (* SOME(cap+1) denotes finite excess; NONE denotes unknown geometry.
     Exact route never opens OpaqueRetained or trusts saturated int data. *)
  val unfolded_nodes_with_policy : graph -> metric ->
    SmtReplayResourcePolicy.limit -> node -> IntInf.int option

  val plan_placeholders_with_policy : graph -> scope ->
    {nodes:node list,remaining_work:SmtReplayResourcePolicy.limit} ->
    placeholder_plan
  val plan_identity_closure_view_with_policy : graph -> scope ->
    SmtReplayResourcePolicy.limit ->
    {target:closure_child,retain:closure_child list,
     profiles:policy_opaque_profile list} -> identity_closure_view_plan

  type profiled_metric
  val prepare_profiled_metric : graph -> scope ->
    {node:node,profiles:policy_opaque_profile list} -> profiled_metric
  val profiled_metric_data : graph -> scope -> profiled_metric ->
    {node:node,raw:IntInf.int,inc:IntInf.int,types:Type.hol_type list}

  val closure_child_scope : graph -> scope -> closure_child -> scope
  (* Liveness only: actual use still needs its genuine requester. *)
  val validate_policy_opaque_profile : graph -> policy_opaque_profile -> unit
  val opaque_profile_for_node_with_policy :
    graph -> scope -> node -> policy_opaque_profile ->
    {node:node,raw:IntInf.int,inc:IntInf.int,ann:IntInf.int,
     ty:IntInf.int,type_bytes:IntInf.int,types:Type.hol_type list} option

  (* Actual finite native gates, separate from metadata and profile DATA. *)
  val recorded_abstraction_with_profile_policy : graph -> scope ->
    {maximum:SmtReplayResourcePolicy.limit,native_limit:int,
     type_work_limit:int,binder:node,body:node,body_frame:scope,
     profiles:policy_opaque_profile list,step:unit->unit} -> node

  val prepare_scoped_profiled_metric : graph -> scope ->
    {node:node,profiles:policy_opaque_profile list} -> profiled_metric
  (* Charged visits/comparisons/copies and retained lifetime guards. *)
  val prepare_scoped_profiled_metric_observed : graph -> scope ->
    {node:node,profiles:policy_opaque_profile list,observe:unit->unit} ->
    profiled_metric

  val opaque_profile_heads_with_policy : graph -> scope ->
    policy_opaque_profile -> {node:node,heads:Term.term list}
  (* Caller-visible target; nested profiles use genuine effective frames.
     Metadata planning only. Execution still requires the caller's own
     actual finite native REFL/Type preflight. *)
  val plan_scoped_identity_closure_view_with_policy : graph -> scope ->
    SmtReplayResourcePolicy.limit ->
    {target:closure_child,retain:closure_child list,
     profiles:policy_opaque_profile list} -> identity_closure_view_plan

  type policy_selected_partial_discovery
  (* Exact policy metadata/scan accounting, actual selected head authority.
     Positive native opening still needs the consumer's finite admission. *)
  val discover_selected_partial_with_policy : graph -> scope ->
    {original:node,heads:discovery_heads,
     maximum:SmtReplayResourcePolicy.limit,
     scan_limit:SmtReplayResourcePolicy.limit,step:unit->unit} ->
    policy_selected_partial_discovery
  val selected_partial_data_with_policy : graph -> scope -> discovery_heads ->
    policy_selected_partial_discovery ->
    {original:node,view:source option,profiles:policy_opaque_profile list}

  (* The supplied genuine retained profile proves generic absence; its
     actual cached declaration heads can prove selected absence. A missing
     profile refuses. A relevant positive path still requires independent
     finite native admission before this call. *)
  val discover_selected_profiled_partial_with_policy : graph -> scope ->
    {original:node,heads:discovery_heads,
     profiles:policy_opaque_profile list,
     maximum:SmtReplayResourcePolicy.limit,
     scan_limit:SmtReplayResourcePolicy.limit,step:unit->unit} ->
    policy_selected_partial_discovery

  (* Projections from actual owned policy discovery only. NONE denotes its
     actual absent recipe, never a selected-numeric no-change certificate. *)
  val carrier_alpha_from_partial_with_policy : graph -> scope ->
    policy_partial_discovery -> carrier_alpha option
  val carrier_alpha_from_selected_with_policy : graph -> scope ->
    discovery_heads -> policy_selected_partial_discovery ->
    carrier_alpha option
  val carrier_alpha_application_children_with_policy : graph -> scope ->
    carrier_alpha -> carrier_alpha * carrier_alpha

  (* Authentic completed generic discovery only. A missing view is not a
     selected numeric no-change certificate or a realized-syntax bound. *)
  val partial_source_header_with_policy : graph -> scope ->
    policy_partial_discovery -> {original:node,view:source option}

  (* Same genuine saved recipe and same acquired rich-node capture. *)
  val alpha_metric_data_with_policy : graph -> scope -> carrier_alpha ->
    profiled_metric ->
    {original:node,source:source,annotation:closure_child,
     raw:IntInf.int,inc:IntInf.int,types:Type.hol_type list}

  (* Isolated metered metadata/validation ports. The caller supplies a
     genuine R meter; no Work/Ready grant or aggregate tariff is minted.
     Node ports retain the independently qualified inherited13 programme. *)
  val root_scope_with_meter : graph ->
    ReplayRedblackPrivateWork.scope_meter -> scope
  val validate_scope_with_meter : graph -> scope ->
    ReplayRedblackPrivateWork.scope_meter -> unit
  (* Read the invalidation witness only after authentic paid Scope
     validation, on the supplied original meter. No native/Ready grant. *)
  val validation_revision_with_meter : graph -> scope ->
    ReplayRedblackPrivateWork.scope_meter -> IntInf.int
  val node_scope_with_meter : graph -> node ->
    ReplayRedblackPrivateWork.scope_meter -> scope
  val representative_with_meter : graph -> node ->
    ReplayRedblackPrivateWork.scope_meter -> Term.term

  (* Closed original Graph construction on the supplied opaque policy
     meter. No invocation, Work/Ready or native permission is returned. *)
  val new_with_bootstrap_meter :
    ReplayRedblackPrivateWork.scope_meter -> graph



  (* Fresh-only structural metadata storage with the captured SAME meter.
     The backing graph never escapes. IDs have distinct opaque types;
     they are NOT G.node/type_id or native admission evidence. *)
  type fixed_storage
  eqtype fixed_type_id
  eqtype fixed_node_id
  datatype fixed_type_key = FixedTypeVariable of string
    | FixedTypeOperator of KernelSig.kernelid * fixed_type_id list
  datatype fixed_node_key =
      FixedVariable of variable_kind * string * fixed_type_id
    | FixedConstant of KernelSig.kernelid * fixed_type_id
    | FixedApplication of fixed_node_id * fixed_node_id
  val new_fixed_storage_with_bootstrap_meter :
    ReplayRedblackPrivateWork.scope_meter -> fixed_storage * scope
  val fixed_storage_counts :
    fixed_storage -> scope -> {types:int,keys:int}
  val fixed_storage_revision : fixed_storage -> scope -> IntInf.int
  val fixed_type_key_id :
    fixed_storage -> scope -> fixed_type_key -> fixed_type_id
  val fixed_node_key_id :
    fixed_storage -> scope -> fixed_node_key -> fixed_node_id

  (* Fresh ORIGINAL birth bundle, never an existing-handle graph getter.
     This distinct factory deliberately returns its newly born graph alias;
     handles from the original fixed-only factory cannot be extracted. *)
  val new_original_with_fixed_storage_bootstrap_meter :
    ReplayRedblackPrivateWork.scope_meter ->
    {graph:graph,root:scope,storage:fixed_storage}

  (* FIRST-only genuine variable Source. The typed request is data, never
     authority; owned A supplies its captured original policy/history. *)
  type first_boolean_variable_limits =
    {construction_limits:SmtReplayResourcePolicy.graph_policy,
     semantic_limits:SmtReplayResourcePolicy.semantic_policy,
     native_limits:
       {semantic_limits:SmtReplayResourcePolicy.semantic_policy,
        import_limit:SmtReplayResourcePolicy.limit,
        type_work_limit:SmtReplayResourcePolicy.limit}}
  val import_first_boolean_variable : fixed_storage -> scope ->
    {original:Term.term,limits:first_boolean_variable_limits} -> source option

  (* FIRST-only genuine canonical Bool constant. Reuses the identical
     original request record vocabulary; variable API remains literal. *)
  val import_first_boolean_constant : fixed_storage -> scope ->
    {original:Term.term,limits:first_boolean_variable_limits} -> source option

  (* Exact captured original policy/list PREFIX, not native admission.
     No public quota debit/reset, graph extractor or executor is exported. *)
  type original_import_context
  type original_import_usage =
    {construction_import:IntInf.int,construction_literal:IntInf.int,
     construction_binder:IntInf.int,recipe_template:IntInf.int,
     recipe_index:IntInf.int,recipe_operand:IntInf.int,
     recipe_token:IntInf.int,semantic_input:IntInf.int,
     semantic_output:IntInf.int,semantic_template:IntInf.int,
     native_input:IntInf.int,native_output:IntInf.int,
     native_template:IntInf.int,native_import:IntInf.int,
     type_work:IntInf.int}
  val begin_original_import_context : fixed_storage -> scope ->
    {limits:first_boolean_variable_limits,originals:Term.term list} ->
    original_import_context
  val original_import_progress : fixed_storage -> scope ->
    original_import_context ->
    {completed:IntInf.int,usage:original_import_usage,
     revision:IntInf.int,denial_complete:bool}

  (* Real captured-list atomic leaf programme. Upper reservations are
     cumulative. No caller term/proof/profile/callback and no Source getter.
     InputsComplete is not denial/Ready. Unsupported latches this context. *)
  datatype original_import_step = OriginalImported
    | OriginalUnsupported | OriginalInputsComplete
  val advance_original_boolean_leaf : fixed_storage -> scope ->
    original_import_context -> original_import_step

  (* Actual constructor-owned denial after captured originals complete.
     No Source/proof getter and no Ready/portfolio publication. *)
  val complete_original_boolean_denial : fixed_storage -> scope ->
    original_import_context -> unit

  (* Authenticated completion data for the opaque A-owned context only.
     Fixed storage/root/context are all required; no adoption/native grant.
     A exposes none of these handles or the returned immutable rows. *)
  val original_source_preparation_data : fixed_storage -> scope ->
    original_import_context ->
    {originals:(source * int) list,denied:source * int,revision:IntInf.int}

  (* Closed atomic-class raw-F validation and genuine native finalisation.
     Raw theorem is data only, never a goal/Source/profile permission.
     No graph mutation or Ready publication; prototype budget qualifier. *)
  val finalise_original_boolean_goal : fixed_storage -> scope ->
    original_import_context -> Thm.thm -> Thm.thm

  (* Closed preparation of the current captured function atom only.
     Source/receipt remain private; no Boolean occurrence is completed. *)
  val prepare_original_function_child : fixed_storage -> scope ->
    original_import_context -> unit

  (* Authentic fixed constructor birth; not a view-Application origin flag.
     Native f/x inputs are positive atoms with genuine fun(Bool,Bool)/Bool.
     Receipt, initial quota history and actual raw children stay opaque. *)
  type owned_application_birth
  val new_owned_boolean_application_with_bootstrap_meter :
    ReplayRedblackPrivateWork.scope_meter ->
    {function:Term.term,argument:Term.term,
     limits:first_boolean_variable_limits} ->
    {graph:graph,root:scope,storage:fixed_storage,original:Term.term,
     birth:owned_application_birth}
  val begin_owned_application_import_context :
    fixed_storage -> scope -> owned_application_birth -> original_import_context
  (* Real captured-child dependency preparation only. Does NOT complete
     an original App, produce its Source, or admit a function hypothesis. *)
  val prepare_owned_application_children : fixed_storage -> scope ->
    original_import_context -> owned_application_birth -> unit


  (* Genuine private argument REFL and local MK_COMB/ALPHA/TRANS App Source.
     Origin from actual constructor receipt only; no original occurrence,
     denial or Ready publication is claimed by this component port. *)
  val complete_owned_application_source : fixed_storage -> scope ->
    original_import_context -> owned_application_birth -> unit


  (* One closed occurrence+denial commit for the authentic constructor App.
     Atomic finalisation remains fenced; no App theorem/Ready grant. *)
  val complete_owned_application_denial : fixed_storage -> scope ->
    original_import_context -> owned_application_birth -> unit


  (* Genuine private programme witness; no caller constructor is exported. *)
  type owned_application_completion
  val classified_original_source_preparation_data : fixed_storage -> scope ->
    original_import_context ->
    {originals:(source * int) list,denied:source * int,revision:IntInf.int,
     application:owned_application_completion option}
  val finalise_owned_application_goal : fixed_storage -> scope ->
    original_import_context -> owned_application_completion ->
    Thm.thm -> Thm.thm


  (* Fixed empty-child workspace only, no native or general replay grant.
     Opaque staging is prepaid and single-use; commit accepts no delta,
     callback, counter, current snapshot or caller completion flag. *)
  type original_proof_scope
  type original_proof_scope_plan
  val stage_original_proof_scope : fixed_storage -> scope ->
    original_import_context ->
    {plan:original_proof_scope_plan,workspace:original_proof_scope,
     revision:IntInf.int}
  val original_proof_scope_for : fixed_storage -> scope ->
    original_import_context -> original_proof_scope -> scope
  val stage_original_proof_scope_close : fixed_storage -> scope ->
    original_import_context -> original_proof_scope ->
    {plan:original_proof_scope_plan,revision:IntInf.int}
  val commit_original_proof_scope : fixed_storage -> scope ->
    original_import_context -> original_proof_scope_plan -> unit

  (* Captured public-view DAG visitor/type-provenance stage. No caller
     term/proof/profile/callback, Source grant, node cast or completion. *)
  type external_original_stage
  type external_original_stage_summary =
    {observations:IntInf.int,public_views:IntInf.int,
     opaque_binders:IntInf.int,unresolved:IntInf.int,
     raw:IntInf.int option,inclusive:IntInf.int option,
     root_type_known:bool,revision:IntInf.int,
     semantic_nodes_published:IntInf.int,sources_issued:IntInf.int,
     originals_completed:IntInf.int}
  val prepare_external_original_stage : fixed_storage -> scope ->
    original_import_context -> external_original_stage
  val external_original_stage_summary : fixed_storage -> scope ->
    original_import_context -> external_original_stage ->
    external_original_stage_summary

  (* Exactly one App completion revision successor per authentic staged
     empty-scope plan; all private proof/Source/policy state is retained.
     The predicted token cannot finalise before actual scope commit. *)
  val stage_owned_application_completion_for_scope :
    fixed_storage -> scope -> original_import_context ->
    owned_application_completion -> original_proof_scope_plan ->
    owned_application_completion

end
