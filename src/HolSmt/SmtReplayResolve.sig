(* Copyright (c) 2026 The HOL4 contributors. *)
signature SmtReplayResolve =
sig
  type resolution
  datatype failure = TypeMismatch | CyclicAssignments | EscapingScope
    | NeedsBinderAdmission | ChangedPreservedRoot
  datatype outcome = Resolved of resolution | Refused of failure

  (* Resolve only explicitly permitted solver-flexible nodes. Rebuild
     application constructors bottom-up; rigid source leaves never change.
     Unknown or affected binders require the caller's bounded local adapter.
     Discover all returned roots before freezing an enclosing proof block. *)
  val prepare : SmtReplayGraph.graph -> SmtReplayGraph.scope ->
    {flexible : SmtReplayGraph.node list,
     assignments : SmtReplayUnify.assignment list,
     roots : SmtReplayGraph.node list,
     preserved : SmtReplayGraph.node list} -> outcome
  (* A bounded local adapter may normalize an affected admitted binder.
     resolve is called only for its known free nodes, never bound IDs.
     The caller retains and proves the original/output binder relation. *)
  val prepare_using : SmtReplayGraph.graph -> SmtReplayGraph.scope ->
    ({node : SmtReplayGraph.node,
      resolve : SmtReplayGraph.node -> SmtReplayGraph.node} ->
      SmtReplayGraph.node option) ->
    {flexible : SmtReplayGraph.node list,
     assignments : SmtReplayUnify.assignment list,
     roots : SmtReplayGraph.node list,
     preserved : SmtReplayGraph.node list} -> outcome
  val validate : SmtReplayGraph.graph -> SmtReplayGraph.scope ->
    resolution -> unit
  val roots : resolution -> SmtReplayGraph.node list
  val node : resolution -> SmtReplayGraph.node -> SmtReplayGraph.node
  (* Only these exact owned equality nodes can discharge solver assignment
     source leaves. Every other frozen source must retain its original node. *)
  (* Record actual stored definition orientations before proof freeze.
     Each source must have an assigned solver variable as an endpoint and
     resolve to reflexivity. Merely equivalent or unrecorded sources remain
     ordinary hypotheses. All source nodes must already belong to roots. *)
  val record_assignment_sources : resolution -> SmtReplayGraph.node list ->
    resolution
  val assignment_sources : resolution -> SmtReplayGraph.node list
  val is_assignment_source : resolution -> SmtReplayGraph.node -> bool
end
