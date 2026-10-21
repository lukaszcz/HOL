(* Copyright (c) 2026 The HOL4 contributors. *)
signature SmtReplayCanonGraph =
sig
  type graph_schema
  type schema_statistics =
    {created_schemas : IntInf.int,schema_raw_nodes : IntInf.int,
     applied_schemas : IntInf.int,applied_schema_raw_nodes : IntInf.int,
     schema_inst_calls : IntInf.int}
  val with_schema_statistics : SmtReplayGraph.graph -> SmtReplayGraph.scope ->
    (unit -> 'a) -> 'a * schema_statistics
  type graph_conversion
  (* Expected Work before any opaque realized leaf activation. *)
  val validate_conversion_for : SmtReplayInvocationWork.portfolio ->
    graph_conversion -> unit
  (* Endpoints/cap come ONLY from the SAME actual P realization receipt. *)
  val graph_realized_leaf : SmtReplayInvocationWork.portfolio ->
    {realization : SmtReplayProof.realization,observe : unit -> unit}
    -> graph_conversion

  (* Closed checked operator schema. Type instantiation precedes this call;
     actual operands are graph references, never inserted expanded terms.
     Local binder work belongs to the existing bounded proof adapter. *)
  val checked_graph_schema : SmtReplayGraph.graph -> SmtReplayGraph.scope ->
    {theorem : Thm.thm, holes : Term.term list,
     operands : SmtReplayGraph.node list, template_limit : int} -> graph_schema
  (* Exact matching of a bounded CLOSED Boolean declaration to an actual
     visible graph statement. Every retained constructor is checked against
     actual G.view children/Types; no caller flag supplies proof authority.
     EQT_INTRO follows the complete endpoint/template/Type checks. *)
  val checked_closed_graph_schema_at : SmtReplayGraph.graph ->
    SmtReplayGraph.scope ->
    {theorem:Thm.thm,holes:Term.term list,operands:SmtReplayGraph.node list,
     source:SmtReplayGraph.node,template_limit:int,type_work_limit:int,
     observe:unit -> unit,pay:IntInf.int -> unit} -> graph_schema
  val graph_schema_source : graph_schema -> SmtReplayGraph.node
  val graph_schema_result : graph_schema -> SmtReplayGraph.node
  (* One actual checked schema step. Operand holes retain their exact IDs;
     ancestor applications are not recursively rebuilt in a child Scope. *)
  val graph_schema_leaf : SmtReplayGraph.graph -> SmtReplayGraph.scope ->
    {schema:graph_schema,observe:unit -> unit} -> graph_conversion

  (* Discover postorder rewrites, retain successful checked schemas and
     detect expansion cycles. Cache keys and constructor matching use IDs.
     Abstractions remain completed atoms; no binder is opened here. *)
  val graph_conversion : SmtReplayGraph.graph -> SmtReplayGraph.scope -> bool ->
    (SmtReplayGraph.node -> graph_schema option) -> SmtReplayGraph.node ->
    graph_conversion
  (* Same memoized schema traversal with the caller's nominal Work hook. *)
  val graph_conversion_with_schemas : SmtReplayGraph.graph ->
    SmtReplayGraph.scope ->
    {revisit : bool,propose : SmtReplayGraph.node -> graph_schema option,
     observe : unit -> unit} -> SmtReplayGraph.node -> graph_conversion
  (* Local equalities are genuine bounded closed facts, including typed
     non-Boolean endpoints. Reserve graph_closed_facts before freeze.
     Applications reuse the ordinary compact constructor assembler.
     observe precedes each normalization visit and constructor operation;
     it is a nominal Work hook, never proof or resource authority. *)
  val graph_conversion_with_closed : SmtReplayGraph.graph ->
    SmtReplayGraph.scope ->
    {template_limit : int, revisit : bool,
     propose : SmtReplayGraph.node -> SmtReplayProof.closed_fact option,
     observe : unit -> unit} ->
    SmtReplayGraph.node -> graph_conversion
  val graph_conversion_with_conversions : SmtReplayGraph.graph ->
    SmtReplayGraph.scope ->
    {template_limit : int,revisit : bool,observe : unit -> unit,
     propose : SmtReplayGraph.node -> SmtReplayProof.closed_conversion option}
    -> SmtReplayGraph.node -> graph_conversion
  val graph_conversions : graph_conversion ->
    SmtReplayProof.closed_conversion list
  (* Opaque checked recipe composition: no expanded parent theorem. *)
  val graph_identity : SmtReplayGraph.graph -> SmtReplayGraph.scope ->
    {observe : unit -> unit} -> SmtReplayGraph.node -> graph_conversion
  val graph_leaf : SmtReplayGraph.graph -> SmtReplayGraph.scope ->
    {conversion : SmtReplayProof.closed_conversion,template_limit : int,
     observe : unit -> unit} -> graph_conversion
  val graph_application : SmtReplayGraph.graph -> SmtReplayGraph.scope ->
    {source : SmtReplayGraph.node,left : graph_conversion,
     right : graph_conversion,observe : unit -> unit} -> graph_conversion
  (* Strict private legacy union; conflicts retain the composed grammar. *)
  val graph_application_fused : SmtReplayGraph.graph -> SmtReplayGraph.scope ->
    {source : SmtReplayGraph.node,left : graph_conversion,
     right : graph_conversion,observe : unit -> unit} -> graph_conversion
  val graph_sequence : SmtReplayGraph.graph -> SmtReplayGraph.scope ->
    {first : graph_conversion,second : graph_conversion,
     observe : unit -> unit} -> graph_conversion
  (* Direct SAME-Work realized slots retain both exact phase occurrences.
     Only the containing sequence names an equality node. *)
  val graph_realized_sequence : SmtReplayInvocationWork.portfolio ->
    {first : graph_conversion,second : graph_conversion,observe : unit -> unit}
    -> graph_conversion
  datatype recipe_kind = LegacyStep | ApplicationRecipe | SequenceRecipe
  type recipe_step =
    {id : int,kind : recipe_kind,source : SmtReplayGraph.node,current : SmtReplayGraph.node,
     result : SmtReplayGraph.node,children : (int * int) option,
     prefix : int option,equality : SmtReplayGraph.node option,
     closed : SmtReplayProof.closed_fact option,
     conversion : SmtReplayProof.closed_conversion option,
     continuation : int option}
  (* IDs identify proof occurrences, never just semantic source nodes.
     This preserves different conversions on a node in successive phases. *)
  val graph_recipe_steps : SmtReplayGraph.graph -> SmtReplayGraph.scope ->
    {observe : unit -> unit} -> graph_conversion ->
    {root : int,steps : recipe_step list}

  type application_step =
    {source : SmtReplayGraph.node,current : SmtReplayGraph.node,
     result : SmtReplayGraph.node,
     children : (SmtReplayGraph.node * SmtReplayGraph.node) option,
     closed : SmtReplayProof.closed_fact option,
     conversion : SmtReplayProof.closed_conversion option,
     continuation : SmtReplayGraph.node option}
  (* Expected graph/visible node Scope guards; cached metadata only.
     Ascending source-ID records. Refuses any ordinary schema branch. *)
  val graph_application_steps : SmtReplayGraph.graph ->
    SmtReplayGraph.scope -> graph_conversion -> application_step list
  val graph_closed_facts : graph_conversion -> SmtReplayProof.closed_fact list
  val graph_source : graph_conversion -> SmtReplayGraph.node
  val graph_result : graph_conversion -> SmtReplayGraph.node
  val graph_equality : graph_conversion -> SmtReplayGraph.node
  val graph_roots : graph_conversion -> SmtReplayGraph.node list

  (* Freeze all graph_roots before assembly. The result proves the compact
     named equality node, ready for the block's one closed realization. *)
  val graph_assemble : SmtReplayGraph.graph -> SmtReplayProof.block ->
    graph_conversion -> SmtReplayProof.edge

  (* Existing conversion sees a bounded constructor prefix with typed named
     holes. Equal semantic operands share one hole. UNCHANGED yields NONE;
     exceptions and invalid schemas remain exceptions, never cached facts. *)
  val graph_schema_conversion : SmtReplayGraph.graph ->
    SmtReplayGraph.scope ->
    {conversion : Term.term -> Thm.thm, template_limit : int,
     prefix_depth : int} -> SmtReplayGraph.node -> graph_schema option
  val graph_assemble_for : SmtReplayInvocationWork.portfolio ->
    SmtReplayGraph.graph -> SmtReplayProof.block ->
    graph_conversion -> SmtReplayProof.edge

  (* Authentic checked schema INST is quoted before kernel assembly.
     Uses compact block names; old descriptor refusals remain unchanged. *)
  val graph_assemble_with_schemas_for : SmtReplayInvocationWork.portfolio ->
    SmtReplayGraph.graph -> SmtReplayProof.block ->
    graph_conversion -> SmtReplayProof.edge

  (* Existing genuine conversion grammar; call inside SAME Work action.
     Fixed rules and closed named-schema INST derive native limits from
     the original block. No expanded graph is handed to a proof callback. *)
  val graph_assemble_with_policy : SmtReplayInvocationWork.portfolio ->
    SmtReplayGraph.graph -> SmtReplayProof.block -> graph_conversion ->
    SmtReplayProof.edge

  (* Same private conversion programme, genuine individual-Hyp owner. *)
  val graph_assemble_sparse_with_policy :
    SmtReplayInvocationWork.portfolio -> SmtReplayGraph.graph ->
    SmtReplayProof.policy_sparse_block -> graph_conversion ->
    SmtReplayProof.policy_sparse_edge

  (* Genuine SAME-Work policy leaves. Invoke inside the existing action.
     The realized variant exposes only its own equality as an ordinary root;
     its actual converted endpoints remain authentic realization cuts.
     Ordinary leaves retain source/target as explicitly demanded roots. *)
  val graph_leaf_with_policy : SmtReplayInvocationWork.portfolio ->
    {frame:SmtReplayOwnedScopeReceipt.receipt,
     conversion:SmtReplayProof.closed_conversion,observe:unit -> unit} ->
    graph_conversion
  val graph_realized_leaf_with_policy :
    SmtReplayInvocationWork.portfolio ->
    {realization:SmtReplayProof.policy_source_realization,
     observe:unit -> unit} -> graph_conversion
  (* Only genuine realized leaves/sequences with the SAME actual frame and
     exact middle endpoint; retains their ordered equality-name grammar. *)
  val graph_realized_sequence_with_policy :
    SmtReplayInvocationWork.portfolio ->
    {first:graph_conversion,second:graph_conversion,observe:unit -> unit} ->
    graph_conversion

  (* Persistent canonical closed-fact lineage is authenticated by P. *)
  val graph_closed_fact_cut_with_policy :
    SmtReplayInvocationWork.portfolio ->
    {cut:SmtReplayProof.policy_closed_fact_cut,observe:unit -> unit} ->
    graph_conversion
  val graph_cut_sequence_with_policy :
    SmtReplayInvocationWork.portfolio ->
    {first:graph_conversion,second:graph_conversion,observe:unit -> unit} ->
    graph_conversion

  (* Actual fixed policy-assembler constructor-definition operands are
     ordinary demands even if the same node is a semantic conversion cut.
     Does not expand unrelated endpoint subgraphs or perform native work. *)
  val graph_roots_with_policy : SmtReplayInvocationWork.portfolio ->
    SmtReplayGraph.graph -> SmtReplayGraph.scope -> graph_conversion ->
    SmtReplayGraph.node list

end
