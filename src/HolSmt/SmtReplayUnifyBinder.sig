(* Copyright (c) 2026 The HOL4 contributors. *)
signature SmtReplayUnifyBinder =
sig
  type relation
  type definition =
    {variable : SmtReplayGraph.node, residue : SmtReplayGraph.node,
     equation : SmtReplayGraph.node}
  (* Admit only bounded opaque binder atoms, retaining an exact source bridge
     and every outer application edge. Large outer DAGs remain graphs. *)
  val admit : SmtReplayGraph.graph -> int -> SmtReplayGraph.source ->
    SmtReplayGraph.source
  val discover : SmtReplayGraph.graph -> SmtReplayGraph.scope ->
    {left : SmtReplayGraph.node, right : SmtReplayGraph.node,
     flexible : SmtReplayGraph.node list, limit : int} -> relation option
  (* Normalize only an admitted bounded binder, resolving known free IDs.
     Predict output size first, clone bound IDs into fresh lexical frames,
     and retain a relation for rechecking under flat definition sources. *)
  val normalize : SmtReplayGraph.graph -> SmtReplayGraph.scope ->
    {node : SmtReplayGraph.node,
     resolve : SmtReplayGraph.node -> SmtReplayGraph.node,
     limit : int} -> SmtReplayGraph.node * relation
  val assignments : relation -> SmtReplayUnify.assignment list
  val left : relation -> SmtReplayGraph.node
  val right : relation -> SmtReplayGraph.node
  (* Independently recheck under canonical normalized assignment sources.
     Returns a bounded equality with exact retained endpoint children and
     only the canonical definition hypotheses actually needed. *)
  val prove : SmtReplayGraph.graph -> SmtReplayGraph.scope -> relation ->
    definition list -> Thm.thm
end
