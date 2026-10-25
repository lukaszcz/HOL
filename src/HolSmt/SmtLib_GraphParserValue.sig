(* Owned parser syntax; metadata closures are not native graph binders. *)
signature SmtLib_GraphParserValue =
sig
  type context
  eqtype value
  datatype view =
      Variable of SmtReplayGraph.variable_kind * Term.term
    | Constant of Term.term
    | RetainedGraph
    | Application of value * value
    | Abstraction of {binder:value,body:value,body_frame:SmtReplayGraph.scope}
  (* Low-level syntax DATA accepts immutable accounting callbacks. The
     production Mapping adapter captures the authentic original Work owner.
     These callbacks admit no Source, equality or native whole-term work. *)
  val create :
    {graph:SmtReplayGraph.graph,scope:SmtReplayGraph.scope,
     validate:unit -> unit,spend:IntInf.int -> unit,retire:unit -> unit}
    -> context
  val validate_for : context -> SmtReplayGraph.graph ->
    SmtReplayGraph.scope -> unit
  val spend : context -> IntInf.int -> unit
  val protect : context -> (unit -> 'a) -> 'a
  (* All value operations execute in the caller's SAME active Work action.
     They never enter with_step. Creation may capture empty DATA while Idle.
     close expires values and closes only this context's owned children.
     No native binder is built and no value can be cast to a G.node. *)
  val validate : context -> unit
  val close : context -> unit
  val key : context -> value -> int
  val view : context -> value -> view
  (* Shallow constructor observation of retained applications. Child values
     retain authentic graph backing and exact known graph FV identities;
     unknown FV/binders stay opaque. No native compound is constructed. *)
  val constructor_view : context -> value -> view
  val type_of : context -> value -> Type.hol_type
  val scope_of : context -> value -> SmtReplayGraph.scope
  val free_variables : context -> value -> value list
  val usable : context -> SmtReplayGraph.scope -> value -> unit
  val graph_leaf : context -> SmtReplayGraph.scope ->
    SmtReplayGraph.node -> value
  val import : context -> SmtReplayGraph.scope ->
    SmtReplayResourcePolicy.limit -> Term.term -> value
  val literal : context -> SmtReplayGraph.scope ->
    SmtReplayResourcePolicy.limit -> Term.term -> value
  val variable : context -> SmtReplayGraph.scope ->
    SmtReplayGraph.variable_kind -> Term.term -> value
  val fresh_bound : context -> SmtReplayGraph.scope -> Term.term -> value
  val fresh_flexible : context -> SmtReplayGraph.scope -> Term.term -> value
  val mapped_variable : context -> SmtReplayGraph.scope ->
    {identity:int,kind:SmtReplayGraph.variable_kind,lexical:Term.term} -> value
  val resolve_variable : context -> SmtReplayGraph.scope -> Term.term -> value
  val reference : context -> SmtReplayGraph.scope -> Term.term * value -> value
  datatype natural_index = NaturalIndex of Arbnum.num
    | ExpandedIndex | OpaqueIndex | NonNaturalIndex
  (* A scalar observation, not native-term or graph-node access. Admit the
     original unfolded index size first, then decode only stock nat/int
     literal syntax. No beta reduction or binder opening occurs. Guards and
     actual visits/lookup work use the SAME caller-owned action. Normal
     syntax outcomes do not retire Work; real exceptions retire unchanged.
     Negative integers retain the stock Arbint.toNat failure. *)
  val natural_index_with_policy : context ->
    SmtReplayResourcePolicy.limit -> value -> natural_index
  val application : context -> SmtReplayGraph.scope -> value * value -> value
  (* Literal-index grammar may recover from a source type error. All other
     errors retain the ordinary application's expected-owner retirement. *)
  exception IndexApplicationTypeError of exn
  val index_application : context -> SmtReplayGraph.scope ->
    value * value -> value
  val abstraction : context -> SmtReplayGraph.scope ->
    {binder:value,body:value,body_frame:SmtReplayGraph.scope} -> value
  val new_scope : context -> SmtReplayGraph.scope ->
    (Term.term * value) list -> SmtReplayGraph.scope
  val new_construction_scope : context ->
    {lexical:SmtReplayGraph.scope,construction:SmtReplayGraph.scope} ->
    SmtReplayGraph.scope
  val close_scope : context -> SmtReplayGraph.scope -> unit
  (* Compile while the caller owns the action. The retained validator is
     read-only and may run Idle, after its actual work is paid by Work.
     It retains authentic value backing, not a graph-node coercion. *)
  type lifetime_guard
  val prepare_lifetime_guard : context ->
    {remaining_work:unit -> SmtReplayResourcePolicy.limit,
     scopes:SmtReplayGraph.scope list,values:value list} -> lifetime_guard
  val lifetime_guard_work : lifetime_guard -> IntInf.int
  val validate_lifetime_guard : lifetime_guard -> unit
  (* Same genuine leaves, with private successful revision metadata.
     Both methods require the owning action and debit the captured actual
     Context spender. No caller payer, amount or liveness lease enters. *)
  type paid_lifetime_guard
  val prepare_paid_lifetime_guard : context ->
    {remaining_work:unit -> SmtReplayResourcePolicy.limit,
     scopes:SmtReplayGraph.scope list,values:value list} ->
    paid_lifetime_guard
  val validate_paid_lifetime_guard : paid_lifetime_guard -> unit
  datatype graph_correspondence = Corresponding | DifferentGraphSyntax
    | NeedsGraphOpening of SmtReplayGraph.scope * SmtReplayGraph.node
  (* Exact graph/free-ID correspondence; local binder IDs are paired only
     under their authentic typed closure frames. Never matches free leaves
     by their printed names. An opaque unrecorded side remains unfinished.
     This syntax observation grants no Source or equality theorem. *)
  val corresponds_to_graph_with_policy : context -> SmtReplayGraph.graph ->
    SmtReplayGraph.scope -> {value:value,node:SmtReplayGraph.node} ->
    graph_correspondence
  type proof_term
  datatype proof_view = ProofVariable of
      SmtReplayGraph.variable_kind * Term.term
    | ProofConstant of Term.term
    | ProofApplication of proof_term * proof_term
    | ProofAbstraction of
        {binder:proof_term,body:proof_term,body_frame:SmtReplayGraph.scope}
    | ProofOpaque
  (* Authenticated syntax observations of genuine retained closures. Keys
     are context-local syntax DATA, never a graph-node coercion or a Scope
     permission. Reads use the same caller-owned action and retire exactly
     like the existing Value operations. No native compound is returned. *)
  val proof_term : context -> value -> proof_term
  val proof_key : context -> proof_term -> int * int
  val proof_type_of : context -> proof_term -> Type.hol_type
  val proof_view : context -> proof_term -> proof_view
  (* Existing authenticated graph backing only. Recipe values return NONE;
     this is not an interpretation, Source or binder admission. *)
  val proof_graph_reference : context -> proof_term ->
    {graph:SmtReplayGraph.graph,scope:SmtReplayGraph.scope,
     child:SmtReplayGraph.closure_child,node:SmtReplayGraph.node} option
end
