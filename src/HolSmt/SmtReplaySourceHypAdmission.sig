(* Copyright (c) 2026 The HOL4 contributors. *)
signature SmtReplaySourceHypAdmission =
sig
  type certificate
  type view =
    {source : SmtReplayGraph.node,retained : Term.term,
     admitted : SmtReplayGraph.node,bridge : Thm.thm,
     free_variables : SmtReplayGraph.node list}
  (* The bridge is already a closed checked law with exact retained
     source/admitted endpoints. This constructor certifies actual bounded
     endpoint and whole-law size, types and exact free-ID ownership. Every
     actual size guard precedes type/FV traversal and bridge destruction. *)
  val new : SmtReplayGraph.graph -> SmtReplayGraph.scope ->
    {source : SmtReplayGraph.node,admitted : SmtReplayGraph.node,
     bridge : Thm.thm,source_variables : SmtReplayGraph.node list,
     allow_bound : bool,admission : SmtReplayBinder.admission} -> certificate
  (* Caller must first establish exact membership of source in P.sources.
     variables are the consumer's annotated Bound IDs. Independent IDs
     cannot share an annotation's typed HOL representative. Check again
     with the reduced output limit before closing captured hypotheses. *)
  val check : certificate ->
    {source : SmtReplayGraph.node,scope : SmtReplayGraph.scope,
     variables : SmtReplayGraph.node list,
     admission : SmtReplayBinder.admission} -> view
end
