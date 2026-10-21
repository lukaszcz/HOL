signature SmtLib_GraphSemanticPacketPreprocess =
sig
  type coordinator
  type validation
  type options =
    {graph : SmtReplayGraph.graph,scope : SmtReplayGraph.scope,
     import_limit : int,template_limit : int,prefix_depth : int,
     natural_enabled : bool,admission : SmtReplayBinder.admission}
  val create : options -> coordinator
  val discover : coordinator ->
    {goal : Abbrev.goal,facts : SmtLib_GraphPreprocessFacts.fact list,
     rules : SmtLib_GraphPreprocessDerived.rule list} -> validation
  val original_sources : validation -> SmtReplaySource.sources
  val processed_goal : validation -> Abbrev.goal
  val processed_assumptions : validation -> SmtReplayGraph.node list
  val processed_denied_goal : validation -> SmtReplayGraph.node
  val roots : validation -> SmtReplayGraph.node list
  val source_nodes : validation -> SmtReplayGraph.node list
  val witnesses : validation -> (SmtReplayGraph.node * Thm.thm) list
  val binder_gaps : validation -> SmtReplayGraph.node list
  val dependency_gaps : validation -> SmtReplayGraph.node list
  val outbound_gaps : validation -> SmtReplayGraph.node list
  val outbound_inventory : validation ->
    (SmtLib_GraphScopedInventory.entry *
     SmtLib_GraphScopedInventory.classification) list
  val close : validation -> unit
  val install_packet : validation -> SmtLib_GraphScopedInventory.packet ->
    SmtLib_GraphFrontend.session ->
    {variables : (string * SmtReplayGraph.node) list,
     aliases : (string * SmtLib_GraphScopedInventory.entry) list} -> unit
  val remaining_stages : unit -> string list
  val assembler : validation -> SmtReplayProof.block ->
    SmtReplayGraph.node -> SmtReplayProof.edge option
  val realize_contradiction : validation -> SmtReplayProof.block ->
    SmtReplayGraph.node -> SmtReplayProof.edge -> Thm.thm
  (* Exact outbound mappings are caller-authorized declarations, not names
     invented by preprocessing. All aliases retain owned operand free IDs. *)
  val alias_nodes : validation -> SmtReplayGraph.node list
  val install_frontend : validation -> SmtLib_GraphFrontend.session ->
    {aliases : (string * SmtReplayGraph.node) list,
     scope_opened : SmtReplayGraph.scope -> unit,
     record_map : SmtReplayGraph.node * SmtReplayGraph.node * Thm.thm -> unit}
    -> unit
end
