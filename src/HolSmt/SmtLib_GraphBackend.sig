(* Copyright (c) 2026 The HOL4 contributors. *)

signature SmtLib_GraphBackend =
sig
  type 'a backend
  type 'a frame
  type 'a binding_origin
  type recipe
  type 'a solver_variable =
    {node : 'a, lexical : Term.term, scope : SmtReplayGraph.scope option}

  (* The ordinary backend retains the caller's LET and binder conventions.
     The graph backend uses graph IDs before substitution or abstraction. *)
  val terms :
    {mk_bound_var : string * Type.hol_type -> Term.term,
     mk_let : (string * Term.term * Term.term) list * Term.term -> Term.term}
    -> Term.term backend
  val graphs :
    {graph : SmtReplayGraph.graph, scope : SmtReplayGraph.scope,
     import_limit : int, literal_limit : int, binder_limit : int}
    -> SmtReplayGraph.node backend
  (* Scoped source-index provenance. These are original small constructor
     callbacks, never callbacks over graph operands. Capture is backend-local
     and restored on success or failure; it retains no lexical frame. *)
  type index_callback =
    string * (string -> Term.term list -> Term.term list -> Term.term) *
    Term.term option
  val capture_index_callbacks : 'a backend -> (unit -> 'b) ->
    'b * {last:index_callback option, callbacks:unit -> index_callback list}
  val note_index_callback : 'a backend -> index_callback -> unit
  exception IndexSyntaxError of exn
  exception IndexBinderError of exn
  val index_callback : 'a backend -> (unit -> 'b) -> 'b
  val index_source_active : 'a backend -> bool
  (* Failure-only veto, never a liveness lease or validation substitute. *)
  val failure_requires_propagation : 'a backend -> bool
  val root : 'a backend -> 'a frame
  val type_of : 'a backend -> 'a -> Type.hol_type
  (* Shallow syntax observations, never native compound operands. Identity
     is syntax identity only; it is not a semantic equality proof. *)
  datatype 'a view = Atom of Term.term | Apply of 'a * 'a | Opaque
  val view : 'a backend -> 'a frame -> 'a -> 'a view
  val same_value : 'a backend -> 'a * 'a -> bool
  (* Explicitly admit the unfolded small index before reconstructing it.
     Binders/opaque syntax are not opened, evaluated or substituted. *)
  val small_index_with_policy : 'a backend -> 'a frame ->
    SmtReplayResourcePolicy.limit -> 'a -> Term.term
  val lookup : 'a backend -> 'a frame -> string -> 'a option
  (* Immutable lexical map snapshot; only admitted type metadata is read.
     No live lexical frame or operand realization is retained. *)
  val binding_type_lookup : 'a backend -> 'a frame ->
    (string -> Type.hol_type option)
  (* Retained original source syntax is imported in the backend's source
     scope. Lexical references use lookup/variable rather than source
     bridges. *)
  val source : 'a backend -> 'a frame -> Term.term -> 'a
  (* The graph backend checks bounded closed literal/type data here. *)
  val literal : 'a backend -> 'a frame -> Term.term -> 'a
  val variable : 'a backend -> 'a frame ->
    SmtReplayGraph.variable_kind -> string * Type.hol_type -> 'a
  (* Original lexical descriptor, independent of the fresh kernel name. *)
  val variable_descriptor : 'a backend -> 'a -> Term.term option
  (* Fresh flexible allocations, including private constructor operands.
     This inventory supplies metadata only, never instantiation evidence. *)
  val solver_variables : 'a backend -> 'a solver_variable list
  (* Internal private symbols bypass lexical aliases while retaining their
     fresh flexible kind and allocation metadata. *)
  val fresh_solver_variable : 'a backend -> 'a frame ->
    string * Type.hol_type -> 'a
  (* Resolve a lexical typed alias, retaining the supplied declaration's
     kind and ID when it is not shadowed. *)
  val reference : 'a backend -> 'a frame -> Term.term * 'a -> 'a
  val application : 'a backend -> 'a frame -> 'a * 'a -> 'a

  (* Each RHS callback receives the original parent frame. Duplicate keys
     are rejected; the body receives the simultaneous extended frame.
     Entries carry dictionary key and printed source name separately. *)
  val let_expression : 'a backend -> 'a frame ->
    (string * string * ('a frame -> 'a)) list -> ('a frame -> 'a) -> 'a
  val abstraction : 'a backend -> 'a frame ->
    string * string * Type.hol_type -> ('a frame -> 'a) -> 'a

  (* Proof binders stay live until the caller closes the resulting proof
     block. Variables/descriptors are outermost first; closing is explicit. *)
  val frame_scope : 'a backend -> 'a frame -> SmtReplayGraph.scope option
  (* Historical lexical label only. Construction ownership continues to
     use frame_scope and the genuine value's own scope. *)
  val frame_lexical_scope : 'a backend -> 'a frame ->
    SmtReplayGraph.scope option
  val open_bindings : 'a backend -> 'a frame ->
    (string * string * 'a) list ->
    {frame : 'a frame, scope : SmtReplayGraph.scope option,
     close : unit -> unit,origin : 'a binding_origin option}
  val open_binders : 'a backend -> 'a frame ->
    (string * string * Type.hol_type) list ->
    {frame : 'a frame, variables : 'a list,
     scope : SmtReplayGraph.scope option, close : unit -> unit,
     origin : 'a binding_origin option}


  (* Only actual backend opening mints this private frame relationship.
     Expected owner peek is pure; activation checks both lexical frames. *)
  val binding_origin_owner : SmtReplayGraph.node binding_origin ->
    {graph : SmtReplayGraph.graph,parent_scope : SmtReplayGraph.scope,
     scope : SmtReplayGraph.scope}
  val binding_origin_data : SmtReplayGraph.graph -> SmtReplayGraph.scope ->
    SmtReplayGraph.node binding_origin ->
    {scope : SmtReplayGraph.scope,variables : SmtReplayGraph.node list,
     descriptors : (string * string * Type.hol_type) list,binders : bool}

  (* Opaque callback-free program over an authentic private origin.
     The Work consumer supplies its own coupled meter and checks identity
     before activation. These cached getters confer no past Work credit. *)
  type binding_guard
  val prepare_binding_guard : SmtReplayGraph.graph -> SmtReplayGraph.scope ->
    SmtReplayGraph.node binding_origin -> ReplayRedblackPrivateWork.scope_meter
    -> binding_guard
  val binding_guard_uses : ReplayRedblackPrivateWork.scope_meter ->
    binding_guard -> bool
  val binding_guard_work : binding_guard -> IntInf.int
  val validate_binding_guard : SmtReplayGraph.graph -> SmtReplayGraph.scope ->
    binding_guard -> unit
  val binding_guard_data : binding_guard ->
    {scope:SmtReplayGraph.scope,variables:SmtReplayGraph.node list,
     descriptors:(string * string * Type.hol_type) list,binders:bool}

  (* Compile an admitted small constructor template. Holes must be distinct
     typed variables, and cannot occur beneath an abstraction. Templates
     may contain constants, applications and local bounded binders; other
     free variables are rejected. No actual graph operands enter compilation.
     Type instantiation must already have been done on this small template. *)
  val compile_recipe :
    {template : Term.term, holes : Term.term list, template_limit : int}
    -> recipe
  val recipe_type : recipe -> Type.hol_type
  val recipe_size : recipe -> int
  (* Returns only branches constructed from the fixed recipe syntax.
     Actual operand nodes are never entered into this manifest. *)
  val construct_with_branches : 'a backend -> 'a frame -> recipe ->
    'a list -> {value : 'a, branches : 'a list}
  val construct : 'a backend -> 'a frame -> recipe -> 'a list -> 'a
  (* Additive policy-meter path; all original origin/frame/epoch tests
     and every actual scope-meter debit remain in their original order. *)
  val prepare_binding_guard_policy : SmtReplayGraph.graph ->
    SmtReplayGraph.scope -> SmtReplayGraph.node binding_origin ->
    ReplayRedblackPrivateWork.scope_meter -> binding_guard

  (* Explicit policy recipe. Exact size DATA does not admit any native
     private Type/Term work or change a graph backend's own binder policy. *)
  type policy_recipe
  val compile_recipe_with_policy :
    {template:Term.term,holes:Term.term list,
     template_limit:SmtReplayResourcePolicy.limit} -> policy_recipe
  val recipe_type_with_policy : policy_recipe -> Type.hol_type
  val recipe_size_with_policy : policy_recipe -> IntInf.int
  val construct_with_branches_with_policy : 'a backend -> 'a frame ->
    policy_recipe -> 'a list -> {value:'a,branches:'a list}
  val construct_with_policy : 'a backend -> 'a frame ->
    policy_recipe -> 'a list -> 'a

  (* Explicit import/literal/binder policies, with the same genuine
     lexical environments and recorded Graph binder constructors. *)
  val graphs_with_policy :
    {graph:SmtReplayGraph.graph,scope:SmtReplayGraph.scope,
     import_limit:SmtReplayResourcePolicy.limit,
     literal_limit:SmtReplayResourcePolicy.limit,
     binder_limit:SmtReplayResourcePolicy.limit} -> SmtReplayGraph.node backend

  (* Typed owned parser syntax, using the SAME existing frame, LET and
     binder machinery. Accounting belongs to the supplied value context;
     no native abstraction is built over a metadata closure body. *)
  type value_factory_token
  type value_backend =
    {backend:SmtLib_GraphParserValue.value backend,
     context:SmtLib_GraphParserValue.context,
     factory_token:value_factory_token,
     binding_origin_data:SmtReplayGraph.scope ->
       SmtLib_GraphParserValue.value binding_origin ->
       {scope:SmtReplayGraph.scope,
        variables:SmtLib_GraphParserValue.value list,
        descriptors:(string * string * Type.hol_type) list,binders:bool},
     close:unit -> unit}
  val values_with_policy :
    {context:SmtLib_GraphParserValue.context,
     graph:SmtReplayGraph.graph,scope:SmtReplayGraph.scope,
     import_limit:SmtReplayResourcePolicy.limit,
     literal_limit:SmtReplayResourcePolicy.limit,
     binder_limit:SmtReplayResourcePolicy.limit} -> value_backend
  type value_binding_guard
  val value_binding_origin_owner :
    SmtLib_GraphParserValue.value binding_origin ->
    {graph:SmtReplayGraph.graph,parent_scope:SmtReplayGraph.scope,
     scope:SmtReplayGraph.scope}
  (* The authentic factory and actual origin are checked in the caller's
     action. Work alone couples the returned fixed validator to its payer. *)
  val prepare_value_binding_guard : value_backend ->
    SmtReplayGraph.graph -> SmtReplayGraph.scope ->
    SmtLib_GraphParserValue.value binding_origin ->
    {root_scope:SmtReplayGraph.scope,
     remaining_work:unit -> SmtReplayResourcePolicy.limit} ->
    value_binding_guard
  val value_binding_guard_work : value_binding_guard -> IntInf.int
  val value_binding_guard_data : value_binding_guard ->
    {scope:SmtReplayGraph.scope,
     variables:SmtLib_GraphParserValue.value list,
     descriptors:(string * string * Type.hol_type) list,binders:bool}
  val validate_value_binding_guard : SmtReplayGraph.graph ->
    SmtReplayGraph.scope -> value_binding_guard -> unit
  (* Metadata ONLY: private lexical active flags, owner and epochs.
     No context callback, graph path or Value leaf is validated here.
     Never substitutes for the full validator without separate guards and
     a stable (validation revision, scope retirement epoch) witness. *)
  val validate_value_binding_header : SmtReplayGraph.graph ->
    SmtReplayGraph.scope -> value_binding_guard -> unit
end
