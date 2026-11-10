(* Collection analysis of an authenticated graph query, without emission. *)
signature SmtLib_GraphQueryAnalysis =
sig
  type scoped_node =
    {scope:SmtReplayGraph.scope,node:SmtReplayGraph.node}
  type marker_seeds =
    {graph:SmtReplayGraph.graph,scope:SmtReplayGraph.scope,
     sets:scoped_node list,bags:scoped_node list,
     raw_numbers:scoped_node list}
  type options =
    {collections:SmtReplayGraph.node list,
     declared_const_arity:SmtReplayGraph.node -> int,
     open_opaque:SmtReplayGraph.scope -> SmtReplayGraph.node -> unit}
  type result =
    {roots:scoped_node list,inventory:scoped_node list,
     openings:{scope:SmtReplayGraph.scope,original:SmtReplayGraph.node,
               opened:SmtReplayGraph.node} list,
     computed_applications:(scoped_node * int * scoped_node) list,
     mixed_argument:bool,bound_application:bool,visits:int,bound_visits:int}

  (* Owns one Work action. Both callbacks execute INSIDE it and must not
     nest with_step. Arity is requested only for genuine constant leaves.
     open_opaque performs the caller's existing bounded/native admission;
     its return carries no authority. The exact cached opened view is then
     authenticated against G's registry before any syntax classification.
     Roots remain the exact positive Goal followed by ordered assumptions;
     openings retain their original-to-opened graph relation separately.
     Scoped DAG traversal and bound-stack memoization are local to this
     call. No exception is cached as an absence result. No Sources, proof
     assumptions, serialization or solver permissions are produced.
     Collection equality uses typed structural analysis keys across caller
     frames. Admitted abstraction locals use de Bruijn positions; all free
     variables (including external Bound IDs) retain their exact graph IDs.
     These keys grant no theorem or equality permission. *)
  val analyse_collections_with_policy : SmtReplayInvocationWork.portfolio ->
    SmtLib_GraphPreprocess.graph_query -> options -> result

  (* The theory registry supplies all operator roles and type predicates.
     Every node passed to a callback is a genuine constant leaf; atomic
     distinguishes an empty collection constant from its application.
     pair_constant returns only the typed atomic pair constructor. *)
  type native_syntax =
    {set_role:{head:SmtReplayGraph.node,atomic:bool} ->
        SmtLib_CollectionMarkers.role,
     bag_role:{head:SmtReplayGraph.node,atomic:bool} ->
        SmtLib_CollectionMarkers.role,
     is_set_type:Type.hol_type -> bool,is_bag_type:Type.hol_type -> bool,
     is_cond:SmtReplayGraph.node -> bool,is_let:SmtReplayGraph.node -> bool,
     is_uncurry:SmtReplayGraph.node -> bool,
     pair_constant:Type.hol_type * Type.hol_type -> Term.term,
     is_integer_coercion:SmtReplayGraph.node -> bool,
     is_num_head:SmtReplayGraph.node -> bool,
     is_bag_card_head:SmtReplayGraph.node -> bool,number_type:Type.hol_type}
  type native_options =
    {syntax:native_syntax,declared_const_arity:SmtReplayGraph.node -> int,
     open_opaque:SmtReplayGraph.scope -> SmtReplayGraph.node -> unit}
  type native_result =
    {sets:scoped_node list,bags:scoped_node list,
     set_analysis:result,bag_analysis:result,
     set_marker_visits:int,bag_marker_visits:int,
     raw_numbers:scoped_node list,raw_number_visits:int}

  (* Discover Set/Bag markers automatically over positive Goal and ordered
     assumptions, then apply argument analysis to each discovered family.
     Uses the full Set conditional/let propagation and Bag prefix policy.
     Walk/mark memo keys retain exact scoped syntax and immutable incoming
     marker-list identity. Only complete successful outputs are cached.
     Stock let function-pattern fixup may need a private typed application
     joining sibling frames; such analysis DATA has no graph node or scope
     and is used only for LHS membership. The nonempty function-let fixup
     tags its LHS privately and preserves stock lexical variable-leaf
     matching there only; ordinary marker equality and argument analysis
     retain exact scoped variable IDs. Returned markers remain genuine
     graph nodes. Syntax mismatch is private and never catches Work,
     authentication, bounded admission or other callback failures.
     Raw Num analysis follows automatic Bag marking with the same native
     registry. Its successful visit cache distinguishes NONE/SOME expected
     type, authentic scoped syntax and exact incoming accumulator identity;
     the generic helper retains per-root traversal and outer merge order. *)
  val analyse_native_collections_with_policy :
    SmtReplayInvocationWork.portfolio -> SmtLib_GraphPreprocess.graph_query ->
    native_options -> native_result

  type carrier
  datatype carrier_view =
      VariableView of SmtReplayGraph.variable_kind * Term.term
    | ConstantView of Term.term
    | ApplicationView of carrier * carrier
    | AbstractionView of carrier * carrier
  type native_context =
    {analysis:native_result,goal:carrier,assumptions:carrier list,
     denied:carrier,view:carrier -> carrier_view,
     type_of:carrier -> Type.hol_type,same:carrier * carrier -> bool,
     free_variables:carrier -> carrier list,
     strip_comb:carrier -> carrier * carrier list,
     is_set:carrier -> bool,is_bag:carrier -> bool,
     is_raw_number:carrier -> bool,
     contextual_argument:carrier * int -> carrier option,
     describe:carrier -> scoped_node,key:carrier -> int * int,
     constant:Term.term -> carrier,mk_comb:carrier * carrier -> carrier,
     step:unit -> unit}

  (* The callback borrows the SAME completed native carrier analysis and
     action. Every operation checks callback lifetime and authentic query/
     closure guards before a cache key or result is used. All operations
     expire on callback success or failure, even while Work remains live;
     failure retains the original exception and retires expected Work.
     Native Terms in views are variable/constant LEAVES only. constant and
     mk_comb build real typed graph metadata in a genuine visible frame;
     sibling-frame LET pattern DATA is not exported through this API.
     key describes normalized scoped syntax; describe retains the actual
     supplied carrier position. Marker/equality/FV operations share the
     original semantic caches. Goal/assumptions are the analysis roots;
     denied is the authentic separate GP assertion node. Plain summary/
     scoped-node DATA can outlive this borrow but grants no proof, Source
     or native-action authority. No nested with_step is permitted. *)
  val with_native_analysis_with_policy :
    SmtReplayInvocationWork.portfolio -> SmtLib_GraphPreprocess.graph_query ->
    native_options -> (native_context -> 'a) -> 'a

  type outbound_context =
    {analysis:native_result,goal:carrier,assumptions:carrier list,
     denied:carrier,view:carrier -> carrier_view,
     type_of:carrier -> Type.hol_type,same:carrier * carrier -> bool,
     free_variables:carrier -> carrier list,
     strip_comb:carrier -> carrier * carrier list,
     is_set:carrier -> bool,is_bag:carrier -> bool,
     is_raw_number:carrier -> bool,
     contextual_argument:carrier * int -> carrier option,
     graph_node:carrier -> scoped_node option,key:carrier -> int * int,
     semantic_key:carrier -> int,
     collection_terms:unit ->
       {sets:carrier list,bags:carrier list,raw_numbers:carrier list,
        shadow_same:carrier * carrier -> bool},
     constant:Term.term -> carrier,mk_comb:carrier * carrier -> carrier,
     genvar:Type.hol_type -> carrier,
     list_mk_abs:carrier list * carrier -> carrier,step:unit -> unit}

  (* A separate borrow over the SAME completed analysis. Applications and
     abstractions are typed immutable outbound recipes retaining authentic
     graph operands and closure guards. They have no G node: graph_node is
     NONE, and their key namespaces differ from genuine graph positions.
     genvar allocates only atomic fresh Bound IDs in one lazy construction
     child, closed on every callback outcome. Abstraction never constructs
     a HOL body or inserts a large operand through G.abstraction. FV and
     alpha analysis share the existing engine; binding removes exact IDs.
     Recipe guard caches follow graph revision and scope retirement, and
     every operation checks borrow expiry even for empty constructor lists.
     semantic_key borrows the existing typed alpha-analysis cache with an
     empty external binder environment. IDs agree exactly with same within
     this analysis; they are local DATA and have no cross-borrow identity.
     collection_terms returns the existing ordered marker carriers. Its
     shadow_same is the separate stock lexical compatibility relation used
     only by LET patterns and finite-evidence shadow detection; it never
     identifies distinct free IDs for semantic equality or Source checks.
     No Source, proof edge, global declaration or equality permission is
     produced. Original-to-emitted proof transport remains separate. The
     existing native_context retains its real-only construction contract. *)
  val with_outbound_analysis_with_policy :
    SmtReplayInvocationWork.portfolio -> SmtLib_GraphPreprocess.graph_query ->
    native_options -> (outbound_context -> 'a) -> 'a

  (* Retain original collection roles while analysing checked new roots.
     Seed owner/root must match the expected query before nodes are read;
     every scoped seed retains an authentic live descendant closure. The
     SAME collectors propagate these roles through new syntax. Seeds are
     analysis DATA only, never evidence or permission to rewrite a query. *)
  val with_outbound_seeded_analysis_with_policy :
    SmtReplayInvocationWork.portfolio -> SmtLib_GraphPreprocess.graph_query ->
    native_options -> marker_seeds -> (outbound_context -> 'a) -> 'a

end
