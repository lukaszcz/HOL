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
  (* The legacy Library fallback admitted whole-input result types, not every
     internal annotation. Its replacement owns that same Type policy at the
     call site. These variants retain all raw operand/residue/output bounds,
     ownership and proof checks, without introducing an internal-Type cutoff
     on that formerly successful route. Existing entries above stay strict. *)
  val discover_raw : SmtReplayGraph.graph -> SmtReplayGraph.scope ->
    {left : SmtReplayGraph.node, right : SmtReplayGraph.node,
     flexible : SmtReplayGraph.node list, limit : int} -> relation option
  val normalize_raw : SmtReplayGraph.graph -> SmtReplayGraph.scope ->
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
