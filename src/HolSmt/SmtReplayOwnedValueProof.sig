(* Checked compact inferences over one genuine parser packet. *)
signature SmtReplayOwnedValueProof =
sig
  type block
  type edge
  type source_port
  type original_source_port
  type closed_law_port
  type binder_law_port
  type closed_witness =
    {receipt:SmtReplayOwnedValueSpecialize.closed_law,
     node:SmtReplayGraph.node,value:SmtLib_GraphParserValue.value}
  type binder_witness =
    {receipt:SmtReplayOwnedValueBinder.closed_law,
     node:SmtReplayGraph.node,value:SmtLib_GraphParserValue.value}
  datatype source_lineage = Current of int | Original of int
  type formal_source = {lineage:source_lineage,node:SmtReplayGraph.node,
    value:SmtLib_GraphParserValue.value}
  datatype preparation = Prepared of block
    | NeedsOpening of (SmtReplayGraph.scope * SmtReplayGraph.node) list
  (* Outside an action. Assertions are the exact ordered current query
     assumptions followed by its denial. Their ownership and structural
     correspondence are checked internally; no caller predicate is used.
     Novel Value abstractions remain typed atoms in binder-free rules.
     This block grants no binder programme or final native realization. *)
  val prepare : SmtReplayInvocationWork.portfolio ->
    SmtLib_GraphPreprocess.graph_query ->
    'proof SmtLib_GraphValueProof.packet ->
    {assertions:SmtLib_GraphParserValue.value list,
     roots:SmtLib_GraphParserValue.value list,
     native_contract:SmtReplayNativeContract.contract,
     check_type:Type.hol_type -> unit} -> preparation
  (* Demand-specific ORIGINAL occurrences. Each index is resolved solely
     from Work.original_sources, ordered assumptions then denial. Values
     undergo authentic exact graph/free-ID correspondence before naming.
     Repeated indices retain separate formal slots and lineage tags. *)
  val prepare_with_originals : SmtReplayInvocationWork.portfolio ->
    SmtLib_GraphPreprocess.graph_query ->
    'proof SmtLib_GraphValueProof.packet ->
    {assertions:SmtLib_GraphParserValue.value list,
     originals:(int * SmtLib_GraphParserValue.value) list,
     roots:SmtLib_GraphParserValue.value list,
     native_contract:SmtReplayNativeContract.contract,
     check_type:Type.hol_type -> unit} -> preparation
  (* CLOSED witnesses are separately reserved formal hypotheses. They are
     never Current/Original Source occurrences and carry no Source index.
     Only the actual sealed producer receipt can authorize their discharge. *)
  val prepare_with_closed_laws : SmtReplayInvocationWork.portfolio ->
    SmtLib_GraphPreprocess.graph_query ->
    'proof SmtLib_GraphValueProof.packet ->
    {assertions:SmtLib_GraphParserValue.value list,
     originals:(int * SmtLib_GraphParserValue.value) list,
     closed_laws:SmtReplayOwnedValueSpecialize.closed_law list,
     roots:SmtLib_GraphParserValue.value list,
     native_contract:SmtReplayNativeContract.contract,
     check_type:Type.hol_type -> unit} -> preparation
  (* Additional genuine scoped CLOSED witnesses. They are reserved
     separately from both Source lineage and retained-SPEC receipts. *)
  val prepare_with_binder_laws : SmtReplayInvocationWork.portfolio ->
    SmtLib_GraphPreprocess.graph_query ->
    'proof SmtLib_GraphValueProof.packet ->
    {assertions:SmtLib_GraphParserValue.value list,
     originals:(int * SmtLib_GraphParserValue.value) list,
     closed_laws:SmtReplayOwnedValueSpecialize.closed_law list,
     binder_laws:SmtReplayOwnedValueBinder.closed_law list,
     roots:SmtLib_GraphParserValue.value list,
     native_contract:SmtReplayNativeContract.contract,
     check_type:Type.hol_type -> unit} -> preparation
  val binder_law_ports_for : SmtReplayInvocationWork.portfolio ->
    block -> binder_law_port list
  val binder_law_source : SmtReplayInvocationWork.portfolio -> block ->
    binder_law_port -> edge
  val closed_law_ports_for : SmtReplayInvocationWork.portfolio ->
    block -> closed_law_port list
  val closed_law_source : SmtReplayInvocationWork.portfolio -> block ->
    closed_law_port -> edge
  val original_source_ports_for : SmtReplayInvocationWork.portfolio ->
    block -> original_source_port list
  val original_source_data_for : SmtReplayInvocationWork.portfolio ->
    original_source_port ->
    {query:SmtLib_GraphPreprocess.graph_query,index:int,
     node:SmtReplayGraph.node,value:SmtLib_GraphParserValue.value}
  val original_source : SmtReplayInvocationWork.portfolio -> block ->
    original_source_port -> edge
  (* Caller owns the SAME Work action. The original Work is compared before
     held packet/context activation, including empty or cached paths. *)
  val source_port_for : SmtReplayInvocationWork.portfolio -> block -> int ->
    source_port
  val source_data_for : SmtReplayInvocationWork.portfolio -> source_port ->
    {query:SmtLib_GraphPreprocess.graph_query,index:int,
     node:SmtReplayGraph.node,value:SmtLib_GraphParserValue.value}
  val source : SmtReplayInvocationWork.portfolio -> block -> source_port ->
    edge
  val name : SmtReplayInvocationWork.portfolio -> block ->
    SmtLib_GraphParserValue.value -> Term.term
  val constructor : SmtReplayInvocationWork.portfolio -> block ->
    SmtLib_GraphParserValue.value -> edge
  val derive : SmtReplayInvocationWork.portfolio -> block ->
    SmtLib_GraphParserValue.value SmtReplayNamedContext.primitive ->
    edge list -> edge
  (* SAME existing fixed Boolean primitive worker and sealed edges. No
     theorem callback, Source admission or native interpretation is added. *)
  val derive_boolean : SmtReplayInvocationWork.portfolio -> block ->
    SmtLib_GraphParserValue.value SmtReplayNamedContext.boolean_rule ->
    edge list -> edge
  val assemble_equality : SmtReplayInvocationWork.portfolio -> block ->
    {rule:string,target:SmtLib_GraphParserValue.value,
     premises:(SmtLib_GraphParserValue.value * edge) list} -> edge
  val assemble_boolean : SmtReplayInvocationWork.portfolio -> block ->
    {target:SmtLib_GraphParserValue.value,
     premises:(SmtLib_GraphParserValue.value * edge) list} -> edge
  (* SAME caller action; only actual owned syntax cursors enter.
     Constructor equations are derived in the private named block. *)
  val assemble_boolean_with_atom_aliases :
    SmtReplayInvocationWork.portfolio -> block ->
    {target:SmtLib_GraphParserValue.value,
     premises:(SmtLib_GraphParserValue.value * edge) list,
     aliases:(SmtLib_GraphParserValue.proof_term *
              SmtLib_GraphParserValue.proof_term) list} -> edge
  val assemble_boolean_with_fixed_xors :
    SmtReplayInvocationWork.portfolio -> block ->
    {target:SmtLib_GraphParserValue.value,
     premises:(SmtLib_GraphParserValue.value * edge) list,
     aliases:(SmtLib_GraphParserValue.proof_term *
              SmtLib_GraphParserValue.proof_term) list,
     xors:SmtLib_GraphParserValue.proof_term list,
     clause:SmtReplayNamedContext.xor_clause} -> edge
  val assemble_equality_with_atom_aliases :
    SmtReplayInvocationWork.portfolio -> block ->
    {rule:string,target:SmtLib_GraphParserValue.value,
     premises:(SmtLib_GraphParserValue.value * edge) list,
     aliases:(SmtLib_GraphParserValue.proof_term *
              SmtLib_GraphParserValue.proof_term) list} -> edge
  (* Compact theorem under actual named assertion/constructor hypotheses.
     It is NOT a theorem of the original Sources or expanded Value syntax. *)
  val compact_theorem_for : SmtReplayInvocationWork.portfolio -> block ->
    edge -> Thm.thm
  val needed_source_ports_for : SmtReplayInvocationWork.portfolio -> block ->
    edge -> source_port list
  (* Exact constructor/rule provenance, distinct from Hyp-derived support
     when equal named Source terms have duplicate ordered occurrences. *)
  val source_dependencies_for : SmtReplayInvocationWork.portfolio -> block ->
    edge -> source_port list
  (* Caller owns SAME Work action. This sealed port retains one actual
     private block/edge. Its data is compact formal syntax, not original
     Source or native realization authority. Every read fences Work first. *)
  type realization_input
  val realization_input_for : SmtReplayInvocationWork.portfolio ->
    block -> edge -> realization_input
  val realization_input_data_for : SmtReplayInvocationWork.portfolio ->
    realization_input ->
    {query:SmtLib_GraphPreprocess.graph_query,
     context:SmtLib_GraphParserValue.context,
     named:SmtLib_GraphParserValue.proof_term SmtReplayNamedContext.block,
     nodes:SmtLib_GraphParserValue.proof_term list,
     assertions:(SmtReplayGraph.node * SmtLib_GraphParserValue.value) vector,
     native_contract:SmtReplayNativeContract.contract,
     theorem:Thm.thm,dependencies:int list,
     formal_sources:formal_source vector,
     closed_witnesses:closed_witness vector option,
     binder_witnesses:binder_witness vector option}
  val close : block -> unit
  (* Same sealed owner/query/context/NC validator, caller owns action. *)
  val validate_with_policy_for : SmtReplayInvocationWork.portfolio ->
    block -> unit
  (* Both phases use the caller's SAME actual Work action. *)
  type unit_resolution_plan
  val prepare_unit_resolution : SmtReplayInvocationWork.portfolio -> block ->
    {factory:SmtReplayValueClause.factory,
     premises:(SmtReplayValueClause.occurrences * edge) list,
     target:SmtReplayValueClause.occurrences} -> unit_resolution_plan
  val execute_unit_resolution : SmtReplayInvocationWork.portfolio ->
    unit_resolution_plan -> edge
  (* Genuine raw discovery is retained as an opaque factory-owned batch.
     No caller fallback table or native theorem is accepted. Same compact
     recorded worker and constructor proofs execute its selected fallbacks. *)
  type raw_unit_resolution_plan
  val prepare_raw_unit_resolution : SmtReplayInvocationWork.portfolio ->
    block -> {factory:SmtReplayValueClause.factory,
      batch:SmtReplayValueClause.raw_occurrences,premises:edge list} ->
    raw_unit_resolution_plan
  val execute_raw_unit_resolution : SmtReplayInvocationWork.portfolio ->
    raw_unit_resolution_plan -> edge
end
