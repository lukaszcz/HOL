(* Copyright (c) 2026 The HOL4 contributors. *)
signature SmtReplayPackedSCC =
sig
  datatype outcome = Resolved of
    {resolution : SmtReplayResolve.resolution,
     images : (int * Thm.thm) list,
     assignments : SmtReplayDefinitionEnvironment.definition list}
    | RequiresWitness of SmtReplayDefinitionEnvironment.selection
    | UnificationRefused of SmtReplayUnify.failure
    | ResolutionRefused of SmtReplayResolve.failure
  (* A check only, never a theorem or source-authority grant. Before inserting
     an actual word, a closed bounded template must have no residual binder,
     GENLIST or w2v occurrence. Public for the exact boundary regression. *)
  val check_instantiation_template : int -> Thm.thm -> unit
  (* Only the caller's actual compact needed Hyp may select this route.
     Original ordered Sources, including duplicates, remain unchanged DATA.
     An eligible packed family needs a real independent anchor outside its
     SCC and every original per-bit equation. No metadata is a theorem. *)
  val resolve : SmtReplayGraph.graph ->
    {scope : SmtReplayGraph.scope,allocated : SmtReplayGraph.node list,
     sources : SmtReplayGraph.node list,needed : SmtReplayGraph.node list,
     roots : SmtReplayGraph.node list,preserved : SmtReplayGraph.node list,
     laws : (SmtReplayGraph.node * Thm.thm) list,
     admission : {metric : SmtReplayGraph.metric,limit : int,
                  check_type : Type.hol_type -> unit}} -> outcome
  (* Explicit checked fresh-bit portfolio. Local abstract equations are
     DISCHarged before INST and proved by exact current REFL/MP afterward;
     no original Source occurrence or authority is added. *)
  val resolve_with_fresh_bits : SmtReplayGraph.graph ->
    {scope : SmtReplayGraph.scope,allocated : SmtReplayGraph.node list,
     sources : SmtReplayGraph.node list,needed : SmtReplayGraph.node list,
     roots : SmtReplayGraph.node list,preserved : SmtReplayGraph.node list,
     laws : (SmtReplayGraph.node * Thm.thm) list,
     admission : {metric : SmtReplayGraph.metric,limit : int,
                  check_type : Type.hol_type -> unit}} -> outcome
end
