signature SmtLib_GraphNumTheoremStage =
sig
  type plan
  type law_row = {head : SmtReplayGraph.node option,ordinal : int,
    original : Thm.thm,normalized : SmtReplayGraph.node,filtered : bool}
  type law_gap = {head : SmtReplayGraph.node option,ordinal : int,
    original : Thm.thm,reason : string}
  (* Fixed checked num-comparison/injection recipes, then stock head-law
     dependency closure. No arbitrary conversion/theorem callback is accepted. *)
  val prepare : SmtReplayGraph.graph -> SmtReplayGraph.scope ->
    SmtReplaySource.sources ->
    {input_limit : int,template_limit : int,
     check_type : Type.hol_type -> unit} -> plan
  (* Genuine closed binder-free theorem DATA may seed dependency tests or
     an independently checked producer. NONE head rows are explicitly not
     claimed as stock selector occurrences; no arbitrary callback is accepted. *)
  val prepare_with_closed_laws :
    SmtReplayGraph.graph -> SmtReplayGraph.scope -> SmtReplaySource.sources ->
    {input_limit : int,template_limit : int,check_type : Type.hol_type -> unit,
     laws : Thm.thm list} -> plan
  val validation : plan -> SmtLib_GraphPreprocess.validation
  val laws : plan -> law_row list
  val gaps : plan -> law_gap list
  val charged : plan -> int
  val template_limit : plan -> int
end
