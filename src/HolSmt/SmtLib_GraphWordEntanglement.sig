signature SmtLib_GraphWordEntanglement =
sig
  type inventory
  type options =
    {graph : SmtReplayGraph.graph,scope : SmtReplayGraph.scope,
     dag_limit : int,type_limit : int}
  (* Decision metadata only. Incomplete inventory cannot certify absence.
     Primitive types must already be admitted before bounded re-admission
     of a retained admitted binder. WordPolicy supplies a complete unfolded
     type-grammar preflight; no opaque abstraction is admitted here. *)
  val inspect : options -> SmtReplayGraph.node list -> inventory
  val complete : inventory -> bool
  val entangled : inventory -> bool
  val inspected_nodes : inventory -> int
  val gaps : inventory -> SmtReplayGraph.node list
end
