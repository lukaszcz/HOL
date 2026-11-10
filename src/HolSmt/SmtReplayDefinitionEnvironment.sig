(* Copyright (c) 2026 The HOL4 contributors. *)
signature SmtReplayDefinitionEnvironment =
sig
  type environment
  type definition =
    {occurrence : int, stored : SmtReplayGraph.node,
     variable : SmtReplayGraph.node, residue : SmtReplayGraph.node,
     name_on_left : bool}
  datatype selection = Empty | Reflexive of definition list
    | Leaf of {variable : SmtReplayGraph.node, anchor : definition,
               definitions : definition list}
    | DuplicateSCC of
        {variable : SmtReplayGraph.node, anchor : definition,
         definitions : definition list, component : SmtReplayGraph.node list}
    | Unresolved of {definitions : int, variables : int, direct_self : int}
  datatype outcome = Resolved of SmtReplayResolve.resolution
    | RequiresWitness of selection
    | UnificationRefused of SmtReplayUnify.failure
    | ResolutionRefused of SmtReplayResolve.failure

  (* Metadata preparation. Sources are the complete ordered actual portfolio;
     needed is a caller-owned subset, not a theorem-dependency certificate.
     Only explicit SolverFlexible IDs grant assignment permission. *)
  val prepare : SmtReplayGraph.graph ->
    {scope : SmtReplayGraph.scope, allocated : SmtReplayGraph.node list,
     sources : SmtReplayGraph.node list, needed : SmtReplayGraph.node list,
     roots : SmtReplayGraph.node list} -> environment
  val definitions : environment -> definition list
  val sources : environment -> SmtReplayGraph.node list
  val selection : environment -> selection

  (* Acyclic path only. Unification makes checked compact proof objects;
     actual R registers each original stored orientation. Every other Source
     and every preserved root must stay exactly unchanged. SCC/reflexive
     selections need separate checked witnesses and are never assumed here.
     Discover returned R roots before P.freeze; realize exactly once via P.
     No ordinary theorem INST, expanded SUBST_CONV or term proof search. *)
  val resolve : environment ->
    {preserved : SmtReplayGraph.node list} -> outcome
  (* Exact closed original law witnesses authorize only their own Source
     preservation exception. They confer no assignment/cycle permission. *)
  val resolve_with_closed_sources : environment ->
    {preserved : SmtReplayGraph.node list,
     laws : (SmtReplayGraph.node * Thm.thm) list} -> outcome
  (* New sparse consumer only: preserve actual needed open Sources rather
     than unused history. The caller's needed DATA must come from checked
     actual compact Hyp; P still verifies every used ordinary Source image.
     Closed witnesses authorize only the same checked original exceptions. *)
  val resolve_needed_with_closed_sources : environment ->
    {preserved : SmtReplayGraph.node list,
     laws : (SmtReplayGraph.node * Thm.thm) list} -> outcome
  (* Explicit checked variable-only cycle/reflexivity route. The returned
     original closed REFL witnesses do NOT become assignment sources. All
     non-leaf non-variable/packed/ground cycles still require a witness. *)
  val resolve_checked_variables : environment ->
    {preserved : SmtReplayGraph.node list,
     laws : (SmtReplayGraph.node * Thm.thm) list,
     admission : {metric : SmtReplayGraph.metric,limit : int,
                  check_type : Type.hol_type -> unit}} ->
    {outcome : outcome,
     reflexive_sources : (SmtReplayGraph.node * Thm.thm) list}
  (* Sparse opt-in only: caller needed DATA comes from P actual compact Hyp.
     Every used ordinary Source and the preserved target stay guarded. *)
  val resolve_needed_checked_variables : environment ->
    {preserved : SmtReplayGraph.node list,
     laws : (SmtReplayGraph.node * Thm.thm) list,
     admission : {metric : SmtReplayGraph.metric,limit : int,
                  check_type : Type.hol_type -> unit}} ->
    {outcome : outcome,
     reflexive_sources : (SmtReplayGraph.node * Thm.thm) list}
end
