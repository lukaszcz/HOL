(* Nominal public-proof quote, not private/kernel/global work admission. *)
signature SmtReplayOwnedLargeProofAssembly =
sig
  type plan
  type result
  type summary =
    {leaves : int,steps : int,public_operations : int,
     assembly_work : IntInf.int,realization_work : IntInf.int,
     dictionary_work : IntInf.int,type_projection_work : IntInf.int,
     compact_context : IntInf.int * IntInf.int * IntInf.int,
     comparison_context : IntInf.int * IntInf.int * IntInf.int}
  val prepare : SmtReplayInvocationWork.portfolio ->
    {conversion : SmtReplayOwnedCompactApplication.plan,ordinal : int,
     check_type : Type.hol_type -> unit} -> plan
  val report : plan -> summary
  (* SAME original Work; one execution, no supplied theorem/Source leaves. *)
  val execute : SmtReplayInvocationWork.portfolio -> plan -> result
  val theorem_for : SmtReplayInvocationWork.portfolio -> result -> Thm.thm
  (* Semantic DATA from THIS opaque result. Expected Work is checked
     before activating its held owner. No past Work or raw Source grant. *)
  val conversion_description_for : SmtReplayInvocationWork.portfolio ->
    result -> {graph : SmtReplayGraph.graph,scope : SmtReplayGraph.scope,
      sources : SmtReplaySource.sources,source : SmtReplayGraph.node,
      target : SmtReplayGraph.node}
end
