signature SmtLib_GraphNativeFloatTransfer =
sig
  type alias =
    {image : SmtReplayGraph.node, operands : SmtReplayGraph.node list,
     free_variables : SmtReplayGraph.node list}
  type producer =
    {propose : SmtReplayGraph.node -> SmtReplayCanonGraph.graph_schema option,
     aliases : unit -> alias list,
     install_aliases : SmtLib_GraphFrontend.session ->
       (string * SmtReplayGraph.node) list -> unit}
  (* Unconditional nonbinder transfer laws over a checked small prefix.
     Actual operand residues remain graph references throughout discovery. *)
  val create : SmtReplayGraph.graph -> SmtReplayGraph.scope ->
    {template_limit : int, prefix_depth : int,
     check_type : Type.hol_type -> unit} -> producer
end
