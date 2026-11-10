(* Copyright (c) 2026 The HOL4 contributors. *)

signature SmtReplaySource =
sig
  type sources
  (* Public source admission uses the caller's existing import contract. *)
  val new : SmtReplayGraph.graph -> SmtReplayGraph.scope -> int ->
    {goal : Term.term, assumptions : Term.term list} -> sources
  (* Exact admitted owner and original ordered occurrence portfolio.
     Active Source metadata only; not a preprocessing proof or caller grant. *)
  val owning_graph : sources -> SmtReplayGraph.graph
  val owning_scope : sources -> SmtReplayGraph.scope
  (* One new accounting claim per EXACT Source object, not Root authority.
     No reset on failed owned invocation; old paths never invoke this claim. *)
  val claim_invocation_work : sources -> unit
  val original_goal : sources -> Abbrev.goal
  (* ALREADY retained positive Source; no import or opened-view issuance. *)
  val goal_source : sources -> SmtReplayGraph.source
  val canonical_goal : sources -> Term.term
  val assumption_nodes : sources -> SmtReplayGraph.node list
  val denied_goal_node : sources -> SmtReplayGraph.node
  val goal_bridge : sources -> Thm.thm
  (* Exact denied goal then ordered original assumption occurrences. *)
  val reconciliation_sources : sources -> SmtReplayGraph.source list

  (* Hypotheses must already use the retained source representatives. These
     checks never sort or compare mixed original/canonical term sets. *)
  val check_contradiction : sources -> Thm.thm -> unit
  val close_contradiction : sources -> Thm.thm -> Thm.thm
  val check_goal : sources -> Thm.thm -> unit
  (* Cached immutable DATA; no activation/Source renewal or proof grant. *)
  val owner_for_scope_guard : sources ->
    {graph:SmtReplayGraph.graph,scope:SmtReplayGraph.scope}
  val claim_invocation_work_with_path : sources ->
    SmtReplayGraph.scope_path -> unit
  (* Monotone failure latch only; never issues Work or proof authority. *)
  val consume_scope_guard_attempt : sources -> unit
  (* Same Source portfolio and exact bridge checks; explicit ceiling
     only. Uncapped does not open binders or create invocation Work. *)
  val new_with_policy : SmtReplayGraph.graph -> SmtReplayGraph.scope ->
    SmtReplayResourcePolicy.limit ->
    {goal : Term.term,assumptions : Term.term list} -> sources


  (* Metadata-only birth; the SAME Source wrapper survives acquisition.
     Only the coupled Work factory may consume its one invocation claim.
     Legacy Work factories refuse this variant, preventing new counters. *)
  val new_pending : SmtReplayOriginalAcquisition.seed -> sources
  val claim_original_work : sources -> SmtReplayOriginalAcquisition.work
  val validate_original_work :
    SmtReplayOriginalAcquisition.work -> sources -> unit
end
