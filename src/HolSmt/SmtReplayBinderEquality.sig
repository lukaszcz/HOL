(* Copyright (c) 2026 The HOL4 contributors. *)
signature SmtReplayBinderEquality =
sig
  type arguments =
    {scope : SmtReplayGraph.scope,
     parent_scope : SmtReplayGraph.scope,
     variables : SmtReplayGraph.node list,
     body : SmtReplayGraph.node,
     target : SmtReplayGraph.node,
     block : SmtReplayProof.block,
     edge : SmtReplayProof.edge,
     witnesses : (int * SmtReplayGraph.node -> Thm.thm option) option,
     canonical_sources : SmtReplayGraph.node list,
     admission : SmtReplayBinder.admission,
     close : unit -> unit}
  (* Introduce precisely the annotated forall/exists/lambda prefix from a
     checked pointwise equality. Admit all realized inputs, hypotheses,
     closures and output before consuming the compact block. *)
  val close_equality : SmtReplayGraph.graph -> arguments -> Thm.thm
  (* Preserve owned parent-frame hypothesis nodes. A raw re-import must not
     change ancestor Bound IDs to source variables. *)
  val close_equality_with_sources : SmtReplayGraph.graph -> arguments ->
    {theorem : Thm.thm, hypotheses : SmtReplayGraph.node list}
  (* Separate draft API: certificates apply only to exact recorded Source
     hypotheses. Existing APIs never request or accept this extra evidence. *)
  val close_equality_with_source_admissions : SmtReplayGraph.graph ->
    {arguments : arguments,
     source_admissions : SmtReplayGraph.node ->
       SmtReplaySourceHypAdmission.certificate option} ->
    {theorem : Thm.thm, hypotheses : SmtReplayGraph.node list}
end
