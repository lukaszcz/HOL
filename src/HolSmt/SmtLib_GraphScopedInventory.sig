signature SmtLib_GraphScopedInventory =
sig
  type inventory
  type entry
  type packet
  datatype kind = Natural | NativeFloat | String
  datatype classification =
      RootAlias of {image : SmtReplayGraph.node,bridge : Thm.thm}
    | TargetPacket of packet
    | Unresolved of string
  type completion =
    {source : SmtReplayGraph.node,target : SmtReplayGraph.node,
     temporary : SmtReplayGraph.scope,body_scope : SmtReplayGraph.scope,
     theorem : Thm.thm}
  val create : SmtReplayGraph.graph -> SmtReplayGraph.scope ->
    SmtReplayBinder.admission -> inventory
  val capture : inventory -> SmtReplayGraph.scope -> kind ->
    {image : SmtReplayGraph.node,operands : SmtReplayGraph.node list} -> unit
  (* Called before a successful binder's temporary scopes close. Ownership
     transfers to this inventory; close releases them on every exit path. *)
  val completed : inventory -> completion -> unit
  val classify : inventory -> SmtReplayGraph.node list ->
    (entry * classification) list
  val image : entry -> SmtReplayGraph.node
  val operands : entry -> SmtReplayGraph.node list
  val entry_kind : entry -> kind
  val packet_target : packet -> SmtReplayGraph.node
  val packet_source : packet -> SmtReplayGraph.node
  val packet_bound : packet -> SmtReplayGraph.node
  val packet_source_bound : packet -> SmtReplayGraph.node option
  val packet_scope : packet -> SmtReplayGraph.scope
  val packet_variables : packet -> SmtReplayGraph.node list
  val packet_bridge : packet -> Thm.thm
  val install_packet : inventory -> packet -> SmtLib_GraphFrontend.session ->
    {variables : (string * SmtReplayGraph.node) list,
     aliases : (string * entry) list} -> unit
  val close : inventory -> unit
end
