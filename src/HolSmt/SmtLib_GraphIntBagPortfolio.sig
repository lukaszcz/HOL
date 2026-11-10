(* Source proposal: local recorded int-bag conversions, not full NUM_BINDERS. *)
signature SmtLib_GraphIntBagPortfolio =
sig
  type choice =
    {view : SmtReplayGraph.source,law : SmtReplayProof.closed_fact}
  val prepare : SmtReplayGraph.graph -> SmtReplayGraph.scope ->
    SmtReplaySource.sources ->
    {admission : SmtReplayBinder.admission,template_limit : int,
     assumptions : (int * choice) list,goal : choice option,
     scope_opened : SmtReplayGraph.scope -> unit} ->
    SmtLib_GraphPreprocess.validation
end
