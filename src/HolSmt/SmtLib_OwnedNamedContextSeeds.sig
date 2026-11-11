(* Compact Source-context projections, not a REV_FULL_SIMP certificate. *)
signature SmtLib_OwnedNamedContextSeeds =
sig
  type owner
  type plan
  type catalogue
  type seed
  (* This additive route proves complete graph FV absence of free NUM/BAG.
     Unknown opaque FV metadata is an explicit error, never a no-op answer.
     No original source, Work, or cap is reconstructed. *)
  val begin_original_nonnum : SmtReplayInvocationWork.portfolio ->
    {check_type:Type.hol_type -> unit} -> owner
  val begin_query : SmtReplayInvocationWork.portfolio ->
    {query:SmtLib_OwnedStrippedNaturalQuery.query,
     check_type:Type.hol_type -> unit} -> owner
  val prepare : owner -> plan
  val execute : plan -> catalogue
  val seeds_for : SmtReplayInvocationWork.portfolio -> catalogue -> seed list
  val description_for : SmtReplayInvocationWork.portfolio -> seed ->
    {node:SmtReplayGraph.node,assumption_slot:int,
     source_occurrence:int,rigid_variables:SmtReplayGraph.node list option}
  (* Genuine named proof only; semantic evidence carries no past Work credit.
     The exported theorem proves the NAME of node, not a raw Source clause. *)
  (* A selected seed must be this exact Goal. No theorem/callback is supplied.
     Query variant closes its own registered block through GEN/CHOOSE. *)
  val close_goal : SmtReplayInvocationWork.portfolio -> catalogue ->
    seed -> Thm.thm
  (* Fixed ground Boolean Source equations only. No schematic/context
     SIMP classification or orientation certificate is exported. *)
  val close_ground_goal : SmtReplayInvocationWork.portfolio ->
    catalogue -> Thm.thm
  (* Distinct expendable producer; final query block remains unclaimed.
     These constructors assert no whole-sequent/natural absence policy. *)
  val begin_rules_original : SmtReplayInvocationWork.portfolio ->
    {check_type:Type.hol_type -> unit} -> owner
  val begin_rules_query : SmtReplayInvocationWork.portfolio ->
    {query:SmtLib_OwnedStrippedNaturalQuery.query,
     check_type:Type.hol_type -> unit} -> owner
  type projected_rule
  val project_rule : SmtReplayInvocationWork.portfolio ->
    catalogue -> seed -> projected_rule
  val projected_rule_for : SmtReplayInvocationWork.portfolio ->
    projected_rule ->
    {frame:SmtReplayOwnedScopeReceipt.receipt,
     query:SmtLib_OwnedStrippedNaturalQuery.query option,
     assumption:SmtReplayGraph.node,assumption_slot:int,
     source_occurrence:int,clause:SmtReplayGraph.node,
     proof:SmtReplayProof.source_realization,theorem:Thm.thm,
     fixed_variables:Term.term list,rigid_types:Type.hol_type list}
  val close : owner -> unit
  (* COMPLETE private conjunction-leaf portfolio of this catalogue, not a
     caller list of selected rules pretending to summarize all Gamma. *)
  type rule_context
  val project_context : SmtReplayInvocationWork.portfolio ->
    catalogue -> rule_context
  val context_for : SmtReplayInvocationWork.portfolio -> rule_context ->
    {frame:SmtReplayOwnedScopeReceipt.receipt,
     query:SmtLib_OwnedStrippedNaturalQuery.query option,
     rules:projected_rule list,variables:Term.term list,
     rigid_types:Type.hol_type list}

  (* Metadata-only complete origins, without admitting every Source leaf
     for matching. NONE is a genuinely unknown opaque summary, not empty. *)
  type context_metadata
  type context_candidate
  val prepare_context_metadata : SmtReplayInvocationWork.portfolio ->
    catalogue -> context_metadata
  val context_metadata_for : SmtReplayInvocationWork.portfolio ->
    context_metadata ->
    {frame:SmtReplayOwnedScopeReceipt.receipt,
     variables:Term.term list option,rigid_types:Type.hol_type list option,
     candidates:context_candidate list}
  val project_context_candidate : SmtReplayInvocationWork.portfolio ->
    context_metadata -> context_candidate -> projected_rule
  (* A selected bounded operation can supply the genuine previously
     unknown clause summary without requiring all other clauses admitted. *)
  val refine_context_candidate : SmtReplayInvocationWork.portfolio ->
    context_metadata -> context_candidate ->
    {rule:projected_rule,metadata:context_metadata}

  (* Exact authentic context-assumption origin, using only held genuine
     selected-clause overrides. Never a complete whole-Gamma certificate. *)
  type context_origin_metadata
  val prepare_context_origin_metadata :
    SmtReplayInvocationWork.portfolio -> context_metadata ->
    SmtReplayGraph.node -> context_origin_metadata
  val context_origin_metadata_for : SmtReplayInvocationWork.portfolio ->
    context_origin_metadata ->
    {frame:SmtReplayOwnedScopeReceipt.receipt,origin:SmtReplayGraph.node,
     variables:Term.term list option,rigid_types:Type.hol_type list option}

end
