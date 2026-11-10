signature SmtLib_GraphScalarPreprocessPublic =
sig
  datatype stage = NumAlgebra | Polymorphic | RealDivision | Reflexivity
    | PositiveLiteralPower | NumeralPower
  val stages : stage list
  val name : stage -> string
  (* Each stage retains the ordinary checked conversion. Only a bounded
     constructor prefix is exposed; actual operands remain owned IDs.
     Full binder, assumption and ordinary tactic parity is separate. *)
  val propose : SmtReplayGraph.graph -> SmtReplayGraph.scope -> stage ->
    {template_limit : int,prefix_depth : int,
     check_type : Type.hol_type -> unit} ->
    SmtReplayGraph.node -> SmtReplayCanonGraph.graph_schema option
end
