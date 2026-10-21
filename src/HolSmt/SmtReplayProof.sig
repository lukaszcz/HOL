(* Copyright (c) 2026 The HOL4 contributors. *)

signature SmtReplayProof =
sig
  type block
  type proof_statistics =
    {edges : IntInf.int,fixed_rule_calls : IntInf.int,
     generic_rule_calls : IntInf.int,final_inst_calls : IntInf.int,
     name_hits : IntInf.int,name_misses : IntInf.int}
  val with_proof_statistics : SmtReplayInvocationWork.portfolio ->
    (unit -> 'a) -> 'a * proof_statistics
  type edge
  (* This opaque closed auxiliary is NOT an original Source occurrence.
     Its original theorem must match genuine recorded graph syntax. *)
  type closed_fact
  type closed_conversion
  (* SAME-engine Source-bearing result; separate from closed equality cuts.
     Only genuine sparse edge metadata derives ordered actual block slots. *)
  type source_realization
  val realize_source_owned_receipt : SmtReplayInvocationWork.portfolio ->
    block -> SmtReplayGraph.node -> edge -> source_realization
  val source_realization_data_for : SmtReplayInvocationWork.portfolio ->
    source_realization ->
    {graph : SmtReplayGraph.graph,root : SmtReplayGraph.scope,
     scope : SmtReplayGraph.scope,frame : SmtReplayOwnedScopeReceipt.receipt,
     original_sources : SmtReplaySource.sources,target : SmtReplayGraph.node,
     source_occurrences : (int * SmtReplayGraph.node) list,
     template_limit : int}
  val source_realization_theorem_for : SmtReplayInvocationWork.portfolio ->
    source_realization -> Thm.thm
  val discharge_source_receipt_with_work :
    SmtReplayInvocationWork.portfolio -> source_realization ->
    SmtReplayGraph.node -> source_realization
  (* Only SAME-engine Source-free realization creates this proof receipt. *)
  type realization
  val realize_owned_receipt : SmtReplayInvocationWork.portfolio ->
    block -> SmtReplayGraph.node -> edge -> realization
  val validate_realization_for : SmtReplayInvocationWork.portfolio ->
    realization -> unit
  val realization_data_for : SmtReplayInvocationWork.portfolio ->
    realization ->
    {graph : SmtReplayGraph.graph,root : SmtReplayGraph.scope,
     scope : SmtReplayGraph.scope,sources : SmtReplaySource.sources,
     equality : SmtReplayGraph.node,source : SmtReplayGraph.node,
     target : SmtReplayGraph.node,template_limit : int}
  val realization_theorem_for : SmtReplayInvocationWork.portfolio ->
    realization -> Thm.thm
  val conversion_from_realization : SmtReplayInvocationWork.portfolio ->
    realization -> closed_conversion
  (* Expected Work guard applies to new receipt leaves; old leaves retain
     their exact existing graph/scope/template validation separately. *)
  val validate_conversion_for : SmtReplayInvocationWork.portfolio ->
    closed_conversion -> unit
  val conversion_realization_for : SmtReplayInvocationWork.portfolio ->
    closed_conversion -> realization option
  (* Private realized endpoint cuts; ordinary demanded roots still expand.
     The original variant derives ALL ordinary Sources from SAME W/S. *)
  type realization_frontier
  val prepare_realization_frontier : SmtReplayInvocationWork.portfolio ->
    {frame : SmtReplayOwnedScopeReceipt.receipt,
     roots : SmtReplayGraph.node list,closed_facts : closed_fact list,
     conversions : closed_conversion list} -> realization_frontier
  val prepare_original_realization_frontier :
    SmtReplayInvocationWork.portfolio ->
    {roots : SmtReplayGraph.node list,closed_facts : closed_fact list,
     conversions : closed_conversion list} -> realization_frontier
  (* Genuine final replay keeps the original ordered S prefix. Extra
     local/law/obligation slots are checked ordinary block Sources and are
     never promoted to original occurrences or a fresh owner. Root only. *)
  val prepare_original_realization_frontier_with_extras :
    SmtReplayInvocationWork.portfolio ->
    {roots : SmtReplayGraph.node list,
     additional_sources : SmtReplayGraph.node list,
     closed_facts : closed_fact list,conversions : closed_conversion list} ->
    realization_frontier
  (* Owns one action; derives original S prefix internally at this genuine
     descendant body/binding frame. Extra slots remain ordinary Sources. *)
  val prepare_scoped_original_realization_frontier :
    SmtReplayInvocationWork.portfolio ->
    {frame : SmtReplayOwnedScopeReceipt.receipt,
     roots : SmtReplayGraph.node list,
     additional_sources : SmtReplayGraph.node list,
     closed_facts : closed_fact list,conversions : closed_conversion list} ->
    realization_frontier
  val realization_frontier_data_for : SmtReplayInvocationWork.portfolio ->
    realization_frontier ->
    {graph : SmtReplayGraph.graph,scope : SmtReplayGraph.scope,
     roots : SmtReplayGraph.node list,sources : SmtReplayGraph.node list,
     reachable : SmtReplayGraph.node list,atoms : SmtReplayGraph.node list,
     template_limit : int}
  (* Exact compact DATA, prospectively counted before naming/proof effects. *)
  val realization_frontier_footprint_for : SmtReplayInvocationWork.portfolio ->
    realization_frontier ->
    {raw:IntInf.int,inclusive:IntInf.int,leaves:IntInf.int}
  type realization_tables_plan
  val prepare_owned_realization_tables : SmtReplayInvocationWork.portfolio ->
    realization_frontier -> realization_tables_plan
  val validate_realization_tables : SmtReplayInvocationWork.portfolio ->
    realization_tables_plan -> unit
  val realization_tables_guard_work : SmtReplayInvocationWork.portfolio ->
    realization_tables_plan -> IntInf.int
  val freeze_owned_realization_tables_plan :
    SmtReplayInvocationWork.portfolio -> realization_tables_plan -> block
  val record_conversion : SmtReplayGraph.graph -> SmtReplayGraph.scope ->
    {source : SmtReplayGraph.node,source_view : SmtReplayGraph.source,
     target : SmtReplayGraph.node,target_view : SmtReplayGraph.source,
     theorem : Thm.thm,template_limit : int,
     check_type : Type.hol_type -> unit} -> closed_conversion
  (* Additive local typed equality leaf. Existing record_conversion
     remains Boolean-only; this path requires identical cached type IDs. *)
  val record_typed_conversion : SmtReplayGraph.graph ->
    SmtReplayGraph.scope ->
    {source : SmtReplayGraph.node,source_view : SmtReplayGraph.source,
     target : SmtReplayGraph.node,target_view : SmtReplayGraph.source,
     theorem : Thm.thm,template_limit : int,
     check_type : Type.hol_type -> unit} -> closed_conversion
  val conversion_source : closed_conversion -> SmtReplayGraph.node
  val conversion_target : closed_conversion -> SmtReplayGraph.node
  val validate_conversion : SmtReplayGraph.graph -> SmtReplayGraph.scope ->
    int -> closed_conversion -> unit
  val freeze_with_conversions : SmtReplayGraph.graph ->
    {scope : SmtReplayGraph.scope,roots : SmtReplayGraph.node list,
     sources : SmtReplayGraph.node list,closed_facts : closed_fact list,
     conversions : closed_conversion list,template_limit : int} -> block
  val prepare_needed_sources_with_conversions : SmtReplayGraph.graph ->
    {scope : SmtReplayGraph.scope,roots : SmtReplayGraph.node list,
     sources : SmtReplayGraph.node list,closed_facts : closed_fact list,
     conversions : closed_conversion list,template_limit : int} -> block
  val conversion : block -> closed_conversion -> edge
  val record_closed : SmtReplayGraph.graph -> SmtReplayGraph.scope ->
    {node : SmtReplayGraph.node, theorem : Thm.thm, template_limit : int,
     check_type : Type.hol_type -> unit} -> closed_fact
  (* Same closed-fact admission and policies; requires the theorem's native
     conclusion to be the EXACT representative. No alignment proof effect. *)
  val record_closed_exact : SmtReplayGraph.graph -> SmtReplayGraph.scope ->
    {node:SmtReplayGraph.node,theorem:Thm.thm,template_limit:int,
     check_type:Type.hol_type -> unit} -> closed_fact
  (* Same admission and exact original theorem, using ONLY already held
     genuine whole import/opened bridges instead of a first node anchor. *)
  val record_closed_from_import :
    SmtReplayGraph.graph -> SmtReplayGraph.scope ->
    {node : SmtReplayGraph.node,theorem : Thm.thm,template_limit : int,
     check_type : Type.hol_type -> unit} -> closed_fact
  val closed_node : closed_fact -> SmtReplayGraph.node
  val closed_original : closed_fact -> Thm.thm
  (* Specialize the recorded forall prefix at SMALL graph placeholders.
     The fully consumed body must be binder-free; no expanded operand is
     inserted under a binder. The original plan's ceiling is retained. *)
  val specialize_closed : closed_fact ->
    {operands : SmtReplayGraph.node list,
     check_type : Type.hol_type -> unit} ->
    {theorem : Thm.thm, holes : Term.term list}
  val validate_closed_fact : SmtReplayGraph.graph -> SmtReplayGraph.scope ->
    int -> closed_fact -> unit
  val prepare_needed_sources_with_closed : SmtReplayGraph.graph ->
    {scope : SmtReplayGraph.scope, roots : SmtReplayGraph.node list,
     sources : SmtReplayGraph.node list, closed_facts : closed_fact list,
     template_limit : int} -> block
  val freeze_with_closed : SmtReplayGraph.graph ->
    {scope : SmtReplayGraph.scope, roots : SmtReplayGraph.node list,
     sources : SmtReplayGraph.node list, closed_facts : closed_fact list,
     template_limit : int} -> block
  val closed : block -> closed_fact -> edge

  (* Reserve binder-frame and schema variables in the graph before freeze.
     Roots include all nodes used by retained successful schemas. Sources
     are recorded Boolean occurrences, with order and duplicates intact. *)
  val freeze : SmtReplayGraph.graph ->
    {scope : SmtReplayGraph.scope, roots : SmtReplayGraph.node list,
     sources : SmtReplayGraph.node list, template_limit : int} -> block
  (* Sparse preparation retains actual compact leaf Hyp instead of lifting
     each edge to the whole context. Only this opt-in stage supports exact
     needed-source inspection; dependency unions are not a Hyp certificate. *)
  val prepare_needed_sources : SmtReplayGraph.graph ->
    {scope : SmtReplayGraph.scope, roots : SmtReplayGraph.node list,
     sources : SmtReplayGraph.node list, template_limit : int} -> block
  (* Original ordered occurrence indices whose node names occur in actual
     compact Hyp. All duplicates of such a Source ID are retained. *)
  val needed_source_occurrences : block -> edge -> int list
  (* Classify actual used Source occurrences. NONE is an open premise;
     only clean CLOSED exact original witnesses become laws. An open
     cross-block witness declines until exact Hyp expansion is implemented. *)
  val needed_sources_using : block -> edge ->
    (int * SmtReplayGraph.node -> Thm.thm option) ->
    {needed : SmtReplayGraph.node list,
     laws : (SmtReplayGraph.node * Thm.thm) list}
  (* Discover actual R/current roots before this FINAL freeze. Graph-owned
     memoized names must be identical. Transfer the compact theorem without
     INST, retire the preparation block, and keep its original template cap.
     The entire original Source occurrence portfolio remains available. *)
  val refreeze_needed_sources : block ->
    {roots : SmtReplayGraph.node list,target : SmtReplayGraph.node,
     edge : edge} -> {block : block,edge : edge}
  (* Additive SAME-original-W sparse stage. Owns its actions; derives the
     original ordered prefix internally. No caller needed-array authority. *)
  val prepare_needed_sources_with_work :
    SmtReplayInvocationWork.portfolio ->
    {frame : SmtReplayOwnedScopeReceipt.receipt,
     roots : SmtReplayGraph.node list,
     additional_sources : SmtReplayGraph.node list,
     closed_facts : closed_fact list,conversions : closed_conversion list} ->
    block
  val needed_source_occurrences_with_work :
    SmtReplayInvocationWork.portfolio -> block -> edge -> int list
  val refreeze_needed_sources_with_work :
    SmtReplayInvocationWork.portfolio -> block ->
    {roots : SmtReplayGraph.node list,target : SmtReplayGraph.node,
     edge : edge} -> {block : block,edge : edge}
  (* Expected W before block activation; old unowned blocks cannot qualify. *)
  val validate_block_for : SmtReplayInvocationWork.portfolio -> block -> unit
  val name : block -> SmtReplayGraph.node -> Term.term
  val context : block -> Term.term
  (* Original retained block ceiling; active accessor, no budget renewal. *)
  val template_limit : block -> int
  val scope : block -> SmtReplayGraph.scope
  val sources : block -> SmtReplayGraph.node list
  val source : block -> int -> edge
  val definition : block -> SmtReplayGraph.node -> edge
  (* Expose an application/operator spine through checked constructor
     equations. Operands stay named; a binder head remains opaque. *)
  val constructor : block -> SmtReplayGraph.node -> edge

  (* Validate the actual small hypotheses before lifting into the common
     context. Only source facts and constructor definitions are admitted. *)
  val checked : block -> Thm.thm -> edge
  val theorem : block -> edge -> Thm.thm
  val dependencies : block -> edge -> int list
  val compose : block -> (Thm.thm list -> Thm.thm) -> edge list -> edge

  (* Close local source facts while the proof is still compact. A fresh
     block keeps the other recorded sources and constructor equations.
     All occurrences of the selected source nodes are removed; implication
     antecedents follow the requested index order. Retires the old block. *)
  val discharge_sources : block ->
    {indices : int list, body : SmtReplayGraph.node, edge : edge} ->
    {block : block, target : SmtReplayGraph.node, edge : edge}

  (* Owns one action. Removes selected occurrence indices only, retaining
     every unselected duplicate Source slot in its exact original order. *)
  val discharge_sources_with_work : SmtReplayInvocationWork.portfolio ->
    block -> {indices : int list,body : SmtReplayGraph.node,edge : edge} ->
    {block : block,target : SmtReplayGraph.node,edge : edge}

  (* A block is realized once, after its common context is discharged.
     The target is a Boolean graph node, not an expanded term template. *)
  val realize : block -> SmtReplayGraph.node -> edge -> Thm.thm
  (* Earlier completed blocks can prove recorded source occurrences.
     Witness endpoints must be exact retained pointers and their hypotheses
     must be canonical frozen source facts. No expanded INST is performed
     on these witnesses. NONE retains the ordinary source assumption. *)
  val realize_with_sources : block -> SmtReplayGraph.node -> edge ->
    (int * SmtReplayGraph.node -> Thm.thm option) -> Thm.thm
  (* Realize a checked solver-only assignment resolution. Ordinary sources
     and the target retain exact original representatives; only recorded
     assignment sources may close by reflexivity after resolution. *)
  val realize_resolved : block -> SmtReplayResolve.resolution ->
    SmtReplayGraph.node -> edge -> Thm.thm
  val realize_resolved_with_sources : block -> SmtReplayResolve.resolution ->
    SmtReplayGraph.node -> edge ->
    (int * SmtReplayGraph.node -> Thm.thm option) -> Thm.thm
  (* Only exact indexed CLOSED checked current images may discharge changed
     nonassignment Sources. Every other Source and target stays unchanged.
     Ordinary supplied witnesses retain the original endpoint/Hyp contract.
     The original ordered Source occurrence inventory is never replaced. *)
  val realize_resolved_with_closed_sources : block ->
    SmtReplayResolve.resolution -> SmtReplayGraph.node -> edge ->
    (int * Thm.thm) list ->
    (int * SmtReplayGraph.node -> Thm.thm option) -> Thm.thm
  (* Fixed public-kernel recipes for a separately owned finite planner.
     These are ordinary block edges, NOT a Work debit/admission receipt. *)
  datatype compact_primitive = ReflexiveName of SmtReplayGraph.node
    | Symmetry | Transitivity | Congruence | EqualityMP
    | ApplyNamedArgument of SmtReplayGraph.node | ImplicationMP
  val derive_primitive : block -> compact_primitive -> edge list -> edge
  type primitive_plan
  val validate_primitive_owner : SmtReplayInvocationWork.portfolio ->
    block -> unit
  val primitive_owner_for : SmtReplayInvocationWork.portfolio ->
    block -> {graph:SmtReplayGraph.graph,scope:SmtReplayGraph.scope}
  val prepare_primitive : SmtReplayInvocationWork.portfolio ->
    block -> compact_primitive -> edge list -> primitive_plan
  val execute_primitive : SmtReplayInvocationWork.portfolio ->
    primitive_plan -> edge

  (* Genuine finite SAME-block conjunction projection. All actual inputs
     are checked before a live metadata-only NONE. A successful opaque
     plan quotes its entire fixed/Boolean kernel programme before any new
     proof rule. Both calls run inside the caller's existing Work action.
     Source occurrences remain intact; only genuine used edges and their
     constructor equations contribute to the returned edge dependencies. *)
  type boolean_projection_plan
  val prepare_boolean_projection : SmtReplayInvocationWork.portfolio ->
    block ->
    {target:SmtReplayGraph.node,premises:(SmtReplayGraph.node * edge) list} ->
    boolean_projection_plan option
  val execute_boolean_projection : SmtReplayInvocationWork.portfolio ->
    boolean_projection_plan -> edge

  (* One-shot closed binder-free schema INST. The actual substitution
     must replace typed variables by authentic SAME-block named variables.
     Both methods run inside the existing SAME-original Work action. *)
  type closed_named_inst_plan
  val prepare_closed_named_inst : SmtReplayInvocationWork.portfolio ->
    block -> {substitution:(Term.term,Term.term) Lib.subst,theorem:Thm.thm} ->
    closed_named_inst_plan
  val execute_closed_named_inst : SmtReplayInvocationWork.portfolio ->
    closed_named_inst_plan -> edge

  (* Additive Source-free owned table route, inside the existing action.
     It quotes actual private Int-map paths and future ordered listing.
     Other P/G/kernel work remains explicit; NOT full private admission. *)
  val freeze_owned_tables : SmtReplayInvocationWork.portfolio ->
    {frame : SmtReplayOwnedScopeReceipt.receipt,
     roots : SmtReplayGraph.node list,closed_facts : closed_fact list,
     conversions : closed_conversion list} -> block
  (* SAME opaque batch/listing state prepared BEFORE policies/placeholders;
     execute refuses foreign/used/stale plans without re-planning. *)
  type owned_tables_plan
  val prepare_owned_tables : SmtReplayInvocationWork.portfolio ->
    {frame : SmtReplayOwnedScopeReceipt.receipt,
     roots : SmtReplayGraph.node list,closed_facts : closed_fact list,
     conversions : closed_conversion list} -> owned_tables_plan
  val owned_tables_guard_work : SmtReplayInvocationWork.portfolio ->
    owned_tables_plan -> IntInf.int
  val validate_owned_tables : SmtReplayInvocationWork.portfolio ->
    owned_tables_plan -> unit
  val freeze_owned_tables_plan : SmtReplayInvocationWork.portfolio ->
    owned_tables_plan -> block
  (* Receipt-owned open-Hyp cuts with actual support occurrence promotion. *)
  type source_cut_block
  val prepare_source_cut_block : SmtReplayInvocationWork.portfolio ->
    {frame : SmtReplayOwnedScopeReceipt.receipt,
     roots : SmtReplayGraph.node list,
     additional_sources : SmtReplayGraph.node list,
     closed_facts : closed_fact list,conversions : closed_conversion list,
     receipts : source_realization list} -> source_cut_block
  val source_cut_block_for : SmtReplayInvocationWork.portfolio ->
    source_cut_block -> block
  val source_cut_edge_for : SmtReplayInvocationWork.portfolio ->
    source_cut_block -> source_realization -> edge
  val realize_source_cut_receipt : SmtReplayInvocationWork.portfolio ->
    source_cut_block -> SmtReplayGraph.node -> edge -> source_realization

  (* SAME receipt supplies actual constructor spine and argument holes. *)
  val prepare_source_cut_constructor_block :
    SmtReplayInvocationWork.portfolio ->
    {frame : SmtReplayOwnedScopeReceipt.receipt,
     roots : SmtReplayGraph.node list,
     additional_sources : SmtReplayGraph.node list,
     closed_facts : closed_fact list,conversions : closed_conversion list,
     receipts : source_realization list} -> source_cut_block

  (* The captured CLOSED fact authenticates the complete ordered law;
     only its genuine outer implication shell can be exposed as syntax. *)
  type closed_law_spine
  val prepare_closed_law_spine : SmtReplayInvocationWork.portfolio ->
    {frame:SmtReplayOwnedScopeReceipt.receipt,fact:closed_fact,
     premises:SmtReplayGraph.node list,target:SmtReplayGraph.node} ->
    closed_law_spine
  (* Outside an action; count selects authentic stored shells only. *)
  val closed_law_spine_prefix_for : SmtReplayInvocationWork.portfolio ->
    closed_law_spine -> int -> closed_law_spine
  val closed_law_spine_data_for : SmtReplayInvocationWork.portfolio ->
    closed_law_spine -> {law:SmtReplayGraph.node,
      premises:SmtReplayGraph.node list,target:SmtReplayGraph.node}
  (* Same authentic rule frontier, prepared without minting native
     placeholders or proof effects. The footprint is exact compact DATA;
     freeze revalidates the SAME plan and enforces its original ceiling. *)
  type source_cut_rule_plan
  val prepare_source_cut_rule_plan : SmtReplayInvocationWork.portfolio ->
    {frame : SmtReplayOwnedScopeReceipt.receipt,
     roots : SmtReplayGraph.node list,
     additional_sources : SmtReplayGraph.node list,
     closed_facts : closed_fact list,conversions : closed_conversion list,
     receipts : source_realization list,targets : SmtReplayGraph.node list,
     boolean : bool,congruence : bool} -> source_cut_rule_plan
  val prepare_source_cut_rule_law_plan : SmtReplayInvocationWork.portfolio ->
    {frame:SmtReplayOwnedScopeReceipt.receipt,
     roots:SmtReplayGraph.node list,
     additional_sources:SmtReplayGraph.node list,
     closed_facts:closed_fact list,conversions:closed_conversion list,
     receipts:source_realization list,targets:SmtReplayGraph.node list,
     boolean:bool,congruence:bool,laws:closed_law_spine list} ->
    source_cut_rule_plan
  val source_cut_rule_footprint_for : SmtReplayInvocationWork.portfolio ->
    source_cut_rule_plan ->
    {raw:IntInf.int,inclusive:IntInf.int,leaves:IntInf.int}
  val freeze_source_cut_rule_plan : SmtReplayInvocationWork.portfolio ->
    source_cut_rule_plan -> source_cut_block
  val prepare_source_cut_rule_block : SmtReplayInvocationWork.portfolio ->
    {frame : SmtReplayOwnedScopeReceipt.receipt,
     roots : SmtReplayGraph.node list,
     additional_sources : SmtReplayGraph.node list,
     closed_facts : closed_fact list,conversions : closed_conversion list,
     receipts : source_realization list,targets : SmtReplayGraph.node list,
     boolean : bool,congruence : bool} -> source_cut_block
  (* A plan can only start from a genuine retained Source proof. No theorem,
     vocabulary map, Source array or ready counter is supplied by a caller. *)
  datatype source_rule_terminal = SourceEquality | SourceTruth | SourceFalse
  datatype source_rule_step = SourceSpec of SmtReplayGraph.closure_child
    | SourceConjunct of bool | SourceCondition
  type source_rule_plan
  type source_rule_recipe
  val prepare_source_rule : SmtReplayInvocationWork.portfolio ->
    {source:source_realization,
     frame:SmtReplayOwnedScopeReceipt.receipt,
     caller:SmtReplayGraph.scope,steps:source_rule_step list,
     terminal:source_rule_terminal,check_type:Type.hol_type -> unit}
    -> source_rule_plan
  val execute_source_rule : SmtReplayInvocationWork.portfolio ->
    source_rule_plan -> source_rule_recipe
  val validate_source_rule_for : SmtReplayInvocationWork.portfolio ->
    source_rule_recipe -> unit
  (* The semantic result is internally realized from the retained named
     program. It grants no past Work or arbitrary proof recording credit. *)
  val realize_source_rule : SmtReplayInvocationWork.portfolio ->
    source_rule_recipe -> Thm.thm
  (* Actual bounded Source body is realized before GEN. This is a distinct
     proof result, not an ordinary SourceCompact/SourceRealization grant. *)
  type source_generalization_plan
  type source_generalization
  val prepare_source_generalization : SmtReplayInvocationWork.portfolio ->
    {source:source_realization,target:SmtReplayGraph.node,
     check_type:Type.hol_type -> unit} -> source_generalization_plan
  val execute_source_generalization : SmtReplayInvocationWork.portfolio ->
    source_generalization_plan -> source_generalization
  val source_generalization_data_for : SmtReplayInvocationWork.portfolio ->
    source_generalization ->
    {source:source_realization,target:SmtReplayGraph.node,
     variables:Term.term list,theorem:Thm.thm}

  (* Genuine transformed evidence; never an ordinary SourceCompact or an
     external semantic theorem/node pairing. Parents retain their origins. *)
  type source_condition_evidence
  type source_condition_plan
  val condition_evidence_for_rule : SmtReplayInvocationWork.portfolio ->
    source_rule_recipe -> source_condition_evidence
  val prepare_source_conditions : SmtReplayInvocationWork.portfolio ->
    {rule:source_condition_evidence,
     premises:source_condition_evidence list,
     check_type:Type.hol_type -> unit} -> source_condition_plan
  val execute_source_conditions : SmtReplayInvocationWork.portfolio ->
    source_condition_plan -> source_condition_evidence
  val realize_source_condition_evidence :
    SmtReplayInvocationWork.portfolio -> source_condition_evidence -> Thm.thm

  (* A genuine transformed-evidence route. The actual owned target frame
     and retained argument closures are distinct from the Source frame. *)
  datatype source_condition_rule_step=EvidenceStep of source_rule_step
    | EvidenceAssertion | EvidenceAntecedentConj
    | EvidenceAntecedentDisj of bool | EvidenceImpFalse
    | EvidenceAntecedentExists of SmtReplayGraph.closure_child
    | EvidenceConditionForall of SmtReplayGraph.closure_child
    | EvidenceSymmetry
  type source_condition_rule_plan
  val prepare_source_condition_rule : SmtReplayInvocationWork.portfolio ->
    {evidence:source_condition_evidence,
     frame:SmtReplayOwnedScopeReceipt.receipt,
     caller:SmtReplayGraph.scope,steps:source_condition_rule_step list,
     terminal:source_rule_terminal,check_type:Type.hol_type -> unit}
    -> source_condition_rule_plan
  val execute_source_condition_rule : SmtReplayInvocationWork.portfolio ->
    source_condition_rule_plan -> source_condition_evidence
  val prepare_retained_source_cut_rule_block :
    SmtReplayInvocationWork.portfolio ->
    {frame : SmtReplayOwnedScopeReceipt.receipt,
     roots : SmtReplayGraph.node list,
     additional_sources : SmtReplayGraph.node list,
     closed_facts : closed_fact list,conversions : closed_conversion list,
     receipts : source_realization list,targets : SmtReplayGraph.node list,
     boolean : bool,congruence : bool} -> source_cut_block
  val source_cut_support_edges_for : SmtReplayInvocationWork.portfolio ->
    source_cut_block -> source_realization ->
    (SmtReplayGraph.node * edge) list
  (* Effective compact GEN evidence; no caller theorem/node authority. *)
  type source_selective_generalization_plan
  type source_selective_generalization
  val prepare_source_selective_generalization :
    SmtReplayInvocationWork.portfolio ->
    {source:source_realization,target:SmtReplayGraph.node,
     check_type:Type.hol_type -> unit} -> source_selective_generalization_plan
  val execute_source_selective_generalization :
    SmtReplayInvocationWork.portfolio ->
    source_selective_generalization_plan ->
    source_selective_generalization
  val source_selective_generalization_theorem_for :
    SmtReplayInvocationWork.portfolio -> source_selective_generalization ->
    Thm.thm
  val discharge_source_selective_generalization :
    SmtReplayInvocationWork.portfolio -> source_selective_generalization ->
    SmtReplayGraph.node -> source_selective_generalization
  val source_selective_generalization_data_for :
    SmtReplayInvocationWork.portfolio -> source_selective_generalization ->
    {source:source_realization,frame:SmtReplayOwnedScopeReceipt.receipt,
     target:SmtReplayGraph.node}

  type source_condition_schema
  val compile_source_condition_schemas :
    SmtReplayInvocationWork.portfolio -> source_condition_evidence ->
    source_condition_schema list
  val source_condition_schema_for : SmtReplayInvocationWork.portfolio ->
    source_condition_schema ->
    {binders:(int*Term.term) list,left:Term.term,right:Term.term option,
     conditions:Term.term list,terminal:source_rule_terminal}
  val prepare_source_condition_schema :
    SmtReplayInvocationWork.portfolio -> source_condition_schema ->
    {frame:SmtReplayOwnedScopeReceipt.receipt,
     caller:SmtReplayGraph.scope,
     arguments:SmtReplayGraph.closure_child list,
     check_type:Type.hol_type -> unit} -> source_condition_rule_plan
  type source_condition_occurrence
  datatype source_rewrite_refusal=ConditionCycle | ConditionStackLimit
    | EquationCycle | PermutativeOrder
  datatype source_rewrite_gate=RewriteAllowed
    | RewriteRefused of source_rewrite_refusal
  val source_condition_occurrences : SmtReplayInvocationWork.portfolio ->
    source_condition_evidence -> source_condition_occurrence list
  val source_condition_rewrite_gate : SmtReplayInvocationWork.portfolio ->
    {rule:source_condition_evidence,stack:source_condition_occurrence list}
    -> source_rewrite_gate
  (* Explicit effective proof witnesses; no external theorem/node admission. *)
  type source_effective_evidence
  type source_effective_cut_block
  val effective_source_for_receipt : SmtReplayInvocationWork.portfolio ->
    source_realization -> source_effective_evidence
  val effective_source_for_generalization :
    SmtReplayInvocationWork.portfolio -> source_selective_generalization ->
    source_effective_evidence
  val effective_source_data_for : SmtReplayInvocationWork.portfolio ->
    source_effective_evidence ->
    {graph:SmtReplayGraph.graph,root:SmtReplayGraph.scope,
     scope:SmtReplayGraph.scope,frame:SmtReplayOwnedScopeReceipt.receipt,
     original_sources:SmtReplaySource.sources,target:SmtReplayGraph.node,
     source_occurrences:(int * SmtReplayGraph.node) list,template_limit:int}
  val effective_source_theorem_for : SmtReplayInvocationWork.portfolio ->
    source_effective_evidence -> Thm.thm
  val prepare_effective_source_cut_rule_block :
    SmtReplayInvocationWork.portfolio ->
    {frame:SmtReplayOwnedScopeReceipt.receipt,roots:SmtReplayGraph.node list,
     additional_sources:SmtReplayGraph.node list,closed_facts:closed_fact list,
     conversions:closed_conversion list,
     receipts:source_effective_evidence list,
     targets:SmtReplayGraph.node list,boolean:bool,congruence:bool} ->
    source_effective_cut_block
  val effective_source_cut_block_for : SmtReplayInvocationWork.portfolio ->
    source_effective_cut_block -> block
  val effective_source_cut_edge_for : SmtReplayInvocationWork.portfolio ->
    source_effective_cut_block -> source_effective_evidence -> edge
  val realize_effective_source_cut_receipt :
    SmtReplayInvocationWork.portfolio -> source_effective_cut_block ->
    SmtReplayGraph.node -> edge -> source_effective_evidence
  type source_antecedent_schema
  val compile_source_antecedent_schemas :
    SmtReplayInvocationWork.portfolio -> source_condition_evidence ->
    source_antecedent_schema list
  val prepare_source_antecedent_schema :
    SmtReplayInvocationWork.portfolio -> source_antecedent_schema ->
    {frame:SmtReplayOwnedScopeReceipt.receipt,
     caller:SmtReplayGraph.scope,check_type:Type.hol_type -> unit} ->
    source_condition_rule_plan
  (* Native proof/row data retains ONE exact opaque effective parent. *)
  type source_effective_compact_view
  type source_effective_row_witness
  type source_effective_completed_witnesses
  val effective_source_compact_for : SmtReplayInvocationWork.portfolio ->
    source_effective_evidence -> source_effective_compact_view
  val effective_source_compact_data_for :
    SmtReplayInvocationWork.portfolio -> source_effective_compact_view ->
    {frame:SmtReplayOwnedScopeReceipt.receipt,graph:SmtReplayGraph.graph,
     scope:SmtReplayGraph.scope,original_sources:SmtReplaySource.sources,
     proof:Thm.thm,target:SmtReplayGraph.node,native_target:Term.term,
     names:(SmtReplayGraph.node * Term.term) list,needed:int list,
     cuts:(int * source_effective_evidence) list,
     rows:(int * Term.term * source_effective_row_witness) list}
  type source_effective_completion_plan
  (* Pure future row/Hyp/substitution preflight before consumer policies.
     The quote is local row incidence DATA, not full private/kernel credit. *)
  val prepare_effective_source_compact_completion :
    SmtReplayInvocationWork.portfolio ->
    {view:source_effective_compact_view,check_type:Type.hol_type -> unit} ->
    source_effective_completion_plan
  val effective_source_completion_work_for :
    SmtReplayInvocationWork.portfolio -> source_effective_completion_plan ->
    IntInf.int
  (* Outside the consumer action. One-shot paid policies precede authentic
     lazy parent actions, then completion owns its separate row action. *)
  val execute_effective_source_compact_completion :
    SmtReplayInvocationWork.portfolio -> source_effective_completion_plan ->
    source_effective_completed_witnesses
  (* Compatibility entry point prepares and executes with no type policy. *)
  val complete_effective_source_compact_witnesses :
    SmtReplayInvocationWork.portfolio -> source_effective_compact_view ->
    source_effective_completed_witnesses
  (* Guarded getter inside the consumer's action; no callback or raw table. *)
  val effective_source_completed_witness_for :
    SmtReplayInvocationWork.portfolio ->
    source_effective_completed_witnesses ->
    source_effective_row_witness -> Thm.thm
  (* Complete free variables of the actual named statement/Hyp after
     interpreting retained graph names; NONE is unknown, never empty. *)
  val source_condition_freshness_for :
    SmtReplayInvocationWork.portfolio -> source_condition_evidence ->
    {frame:SmtReplayOwnedScopeReceipt.receipt,statement:Term.term,
     variables:Term.term list option}
  type source_effective_scope_plan
  val prepare_effective_source_scope :
    SmtReplayInvocationWork.portfolio ->
    {source:source_effective_evidence,hypothesis:SmtReplayGraph.node,
     check_type:Type.hol_type -> unit} -> source_effective_scope_plan
  val execute_effective_source_scope :
    SmtReplayInvocationWork.portfolio -> source_effective_scope_plan ->
    source_effective_evidence
  type source_effective_generalization_plan
  val prepare_effective_source_generalization :
    SmtReplayInvocationWork.portfolio ->
    {source:source_effective_evidence,target:SmtReplayGraph.node,
     check_type:Type.hol_type -> unit} -> source_effective_generalization_plan
  val execute_effective_source_generalization :
    SmtReplayInvocationWork.portfolio ->
    source_effective_generalization_plan ->
    source_effective_evidence
  type source_condition_binder_origins
  val prepare_source_condition_binder_origins :
    SmtReplayInvocationWork.portfolio -> source_condition_evidence ->
    source_condition_binder_origins
  val source_condition_binder_origins_for :
    SmtReplayInvocationWork.portfolio -> source_condition_binder_origins ->
    {frame:SmtReplayOwnedScopeReceipt.receipt,statement:Term.term,
     binders:(int list*Term.term*Term.term) list}
  type source_freshness_origins
  val prepare_source_condition_freshness_origins :
    SmtReplayInvocationWork.portfolio -> source_condition_evidence ->
    source_freshness_origins
  val source_condition_freshness_origins_for :
    SmtReplayInvocationWork.portfolio -> source_freshness_origins ->
    {frame:SmtReplayOwnedScopeReceipt.receipt,statement:Term.term,
     variables:Term.term list,unknown:SmtReplayGraph.node list}
  type source_effective_normalization_plan
  type source_effective_normalization
  (* A genuine bounded clause programme retains its parent and exact row
     witnesses. No caller raw proof, node or lexical map is admitted. *)
  val prepare_effective_source_normalization :
    SmtReplayInvocationWork.portfolio ->
    {source:source_effective_evidence,check_type:Type.hol_type -> unit} ->
    source_effective_normalization_plan
  val execute_effective_source_normalization :
    SmtReplayInvocationWork.portfolio -> source_effective_normalization_plan ->
    source_effective_normalization
  val effective_source_normalization_evidence_for :
    SmtReplayInvocationWork.portfolio -> source_effective_normalization ->
    source_effective_evidence
  val effective_source_normalization_view_for :
    SmtReplayInvocationWork.portfolio -> source_effective_normalization ->
    source_effective_compact_view
  (* original is the bounded syntax of this target's FIRST genuine graph
     Source anchor. It retains that anchor's lexical constructor paths.
     Earlier solver names are not recovered if upstream already emitted
     alpha syntax before this anchor. NONE means no retained graph anchor. *)
  val effective_source_normalization_origin_for :
    SmtReplayInvocationWork.portfolio -> source_effective_normalization ->
    {frame:SmtReplayOwnedScopeReceipt.receipt,target:SmtReplayGraph.node,
     statement:Term.term,original:Term.term option}

  type source_effective_row_hypotheses
  type source_effective_hyp_origin
  (* Outside a consumer's owned action. Canonical actual witness Hyp roots
     with genuine occurrence origins; no proof or FV absence certificate. *)
  val prepare_effective_source_row_hypotheses :
    SmtReplayInvocationWork.portfolio -> source_effective_row_witness ->
    source_effective_row_hypotheses
  val effective_source_row_hypotheses_for :
    SmtReplayInvocationWork.portfolio -> source_effective_row_hypotheses ->
    {graph:SmtReplayGraph.graph,scope:SmtReplayGraph.scope,
     frame:SmtReplayOwnedScopeReceipt.receipt,
     hypotheses:SmtReplayGraph.node list,
     origins:source_effective_hyp_origin list}
  val effective_source_hyp_origin_for :
    SmtReplayInvocationWork.portfolio -> source_effective_hyp_origin ->
    {ordinal:int,node:SmtReplayGraph.node,original:bool}

  type source_condition_argument_plan
  type source_condition_argument_ready
  (* Prospective name/type DATA has no freshness or mint authority. *)
  val prepare_source_condition_exists_argument :
    SmtReplayInvocationWork.portfolio ->
    {evidence:source_condition_evidence,
     frame:SmtReplayOwnedScopeReceipt.receipt,caller:SmtReplayGraph.scope,
     name:string,ty:Type.hol_type,check_type:Type.hol_type -> unit} ->
    source_condition_argument_plan
  val admit_source_condition_exists_argument :
    SmtReplayInvocationWork.portfolio -> source_condition_argument_plan ->
    source_condition_argument_ready
  val source_condition_argument_ready_for :
    SmtReplayInvocationWork.portfolio -> source_condition_argument_ready ->
    {frame:SmtReplayOwnedScopeReceipt.receipt,name:string,ty:Type.hol_type}
  val execute_source_condition_exists_argument :
    SmtReplayInvocationWork.portfolio ->
    {ready:source_condition_argument_ready,
     argument:SmtReplayGraph.closure_child} -> source_condition_evidence

  datatype source_canonical_frontier=CanonicalConjunction
    | CanonicalAntecedentConjunction | CanonicalAntecedentDisjunction
    | CanonicalAntecedentExistential | CanonicalCondition
    | CanonicalImpFalse | CanonicalForall | CanonicalRestrictedForall
    | CanonicalTerminal
  datatype source_canonical_step=CanonicalConjunct of bool
    | CanonicalAntecedentConj | CanonicalAntecedentDisj of bool
    | CanonicalUndisch | CanonicalNotIntro | CanonicalFinish
  datatype source_canonical_future=CanonicalExists | CanonicalUniversals
  type source_canonical_state
  type source_canonical_plan
  type source_canonical_ready
  val prepare_source_canonical_start : SmtReplayInvocationWork.portfolio ->
    {evidence:source_condition_evidence,
     check_type:Type.hol_type -> unit} -> source_canonical_plan
  val source_canonical_frontier_for : SmtReplayInvocationWork.portfolio ->
    source_canonical_state -> source_canonical_frontier
  val source_canonical_current_for : SmtReplayInvocationWork.portfolio ->
    source_canonical_state -> source_condition_evidence
  val prepare_source_canonical_step : SmtReplayInvocationWork.portfolio ->
    {state:source_canonical_state,step:source_canonical_step,
     check_type:Type.hol_type -> unit} -> source_canonical_plan
  (* Future names/types are only quotation DATA, never freshness authority. *)
  val prepare_source_canonical_future : SmtReplayInvocationWork.portfolio ->
    {state:source_canonical_state,operation:source_canonical_future,
     quotations:(string*Type.hol_type) list,
     check_type:Type.hol_type -> unit} -> source_canonical_plan
  val admit_source_canonical_plan : SmtReplayInvocationWork.portfolio ->
    source_canonical_plan -> source_canonical_ready
  val source_canonical_arguments_for : SmtReplayInvocationWork.portfolio ->
    source_canonical_ready ->
    {frame:SmtReplayOwnedScopeReceipt.receipt,
     arguments:(string*Type.hol_type) list}
  val execute_source_canonical_plan : SmtReplayInvocationWork.portfolio ->
    {ready:source_canonical_ready,
     arguments:SmtReplayGraph.closure_child list} -> source_canonical_state
  val source_canonical_finished_for : SmtReplayInvocationWork.portfolio ->
    source_canonical_state -> source_condition_evidence

  (* Bounded authenticated syntax shadow DATA, not proof/Hyp authority. *)
  val source_canonical_syntax_for : SmtReplayInvocationWork.portfolio ->
    source_canonical_state ->
    {frame:SmtReplayOwnedScopeReceipt.receipt,statement:Term.term}

  (* Stock restricted-forall conversion: privately fixed opened closed law,
     genuine current state, full portfolio before policies and G effects. *)
  type source_restricted_plan
  type source_restricted_ready
  val prepare_source_canonical_restricted_forall :
    SmtReplayInvocationWork.portfolio ->
    {state:source_canonical_state,check_type:Type.hol_type -> unit} ->
    source_restricted_plan
  val admit_source_canonical_restricted_forall :
    SmtReplayInvocationWork.portfolio -> source_restricted_plan ->
    source_restricted_ready
  val execute_source_canonical_restricted_forall :
    SmtReplayInvocationWork.portfolio -> source_restricted_ready ->
    source_canonical_state
  (* Authentic current statement DATA; never theorem/Hyp or quote credit. *)
  val source_condition_statement_for : SmtReplayInvocationWork.portfolio ->
    source_condition_evidence ->
    {frame:SmtReplayOwnedScopeReceipt.receipt,statement:Term.term}

  (* Distinct Hyp-only metadata; variables are partial if unknown is nonempty.
     Statement identifies authentic backing only, never raw syntax authority. *)
  type source_hyp_fv_origins
  val prepare_source_condition_hyp_fv_origins :
    SmtReplayInvocationWork.portfolio -> source_condition_evidence ->
    source_hyp_fv_origins
  val source_condition_hyp_fv_origins_for :
    SmtReplayInvocationWork.portfolio -> source_hyp_fv_origins ->
    {frame:SmtReplayOwnedScopeReceipt.receipt,statement:Term.term,
     variables:Term.term list,unknown:SmtReplayGraph.node list}

  (* Metadata decision only. Absence is unavailable with unresolved origins;
     callers receive no proof, GEN, graph-mint or raw-syntax permission. *)
  datatype source_hyp_fv_membership=HypVariablePresent | HypVariableAbsent
    | HypVariableUnresolved of SmtReplayGraph.node list
  val source_condition_hyp_fv_membership_for :
    SmtReplayInvocationWork.portfolio -> source_hyp_fv_origins -> Term.term ->
    source_hyp_fv_membership

  (* Prospective operand DATA only; execution requires authentic closed
     imported law with that exact statement and SAME actual graph/frame. *)
  type source_false_law_plan
  type source_false_law_ready
  val prepare_source_false_law : SmtReplayInvocationWork.portfolio ->
    {evidence:source_condition_evidence,law_statement:Term.term,
     check_type:Type.hol_type -> unit} -> source_false_law_plan
  val admit_source_false_law : SmtReplayInvocationWork.portfolio ->
    source_false_law_plan -> source_false_law_ready
  val execute_source_false_law : SmtReplayInvocationWork.portfolio ->
    {ready:source_false_law_ready,law:closed_fact} ->
    source_condition_evidence

  (* Authentic exact EQT/SYM-EQT loop siblings share one policy barrier.
     Original plans and ready are consumed once; no copies escape. *)
  type source_condition_loop_plan
  type source_condition_loop_ready
  val prepare_source_condition_loop : SmtReplayInvocationWork.portfolio ->
    {first:source_condition_rule_plan,second:source_condition_rule_plan} ->
    source_condition_loop_plan
  val admit_source_condition_loop : SmtReplayInvocationWork.portfolio ->
    source_condition_loop_plan -> source_condition_loop_ready
  val execute_source_condition_loop : SmtReplayInvocationWork.portfolio ->
    source_condition_loop_ready -> source_condition_evidence list

  (* Genuine two-result EQT/LAND programme. Complete portfolio admission
     precedes its fixed-law import and both native proof outputs. *)
  type source_eqt_flip_plan
  type source_eqt_flip_ready
  val prepare_source_eqt_flip : SmtReplayInvocationWork.portfolio ->
    {evidence:source_condition_evidence,check_type:Type.hol_type -> unit} ->
    source_eqt_flip_plan
  val admit_source_eqt_flip : SmtReplayInvocationWork.portfolio ->
    source_eqt_flip_plan -> source_eqt_flip_ready
  val execute_source_eqt_flip : SmtReplayInvocationWork.portfolio ->
    source_eqt_flip_ready -> source_condition_evidence list

  (* One complete predicate conditional programme; no public ants/proof. *)
  type source_predicate_conditional_plan
  type source_predicate_conditional_ready
  val prepare_source_predicate_conditional :
    SmtReplayInvocationWork.portfolio ->
    {evidence:source_condition_evidence,statement:Term.term,
     first:Term.term,second:Term.term,third:Term.term,
     check_type:Type.hol_type -> unit} -> source_predicate_conditional_plan
  val admit_source_predicate_conditional :
    SmtReplayInvocationWork.portfolio -> source_predicate_conditional_plan ->
    source_predicate_conditional_ready
  val source_predicate_conditional_import_for :
    SmtReplayInvocationWork.portfolio -> source_predicate_conditional_ready ->
    {frame:SmtReplayOwnedScopeReceipt.receipt,statement:Term.term,
     import:SmtReplayGraph.import_plan option}
  val execute_source_predicate_conditional :
    SmtReplayInvocationWork.portfolio ->
    {ready:source_predicate_conditional_ready,law:closed_fact option} ->
    source_condition_evidence

  (* A quoted assertion receiver for genuine transformed SCE. No graph
     syntax shadow or caller theorem is accepted by this producer. *)
  type source_assertion_plan
  type source_assertion_ready
  val prepare_source_assertion : SmtReplayInvocationWork.portfolio ->
    {evidence:source_condition_evidence,check_type:Type.hol_type -> unit} ->
    source_assertion_plan
  val admit_source_assertion : SmtReplayInvocationWork.portfolio ->
    source_assertion_plan -> source_assertion_ready
  val execute_source_assertion : SmtReplayInvocationWork.portfolio ->
    source_assertion_ready -> source_condition_evidence

  (* Minted only by the actual conditional executor. The paired evidence
     is the same result as the legacy public executor returns. *)
  type source_predicate_conditional_completed
  val execute_source_predicate_conditional_completed :
    SmtReplayInvocationWork.portfolio ->
    {ready:source_predicate_conditional_ready,law:closed_fact option} ->
    source_predicate_conditional_completed * source_condition_evidence
  val source_predicate_conditional_completed_for :
    SmtReplayInvocationWork.portfolio ->
    source_predicate_conditional_completed ->
    {evidence:source_condition_evidence,
     frame:SmtReplayOwnedScopeReceipt.receipt}

  (* Metadata only. No FV/variable input and no GEN or theorem grant. *)
  type source_conditional_post_metadata
  val prepare_source_conditional_post_metadata :
    SmtReplayInvocationWork.portfolio ->
    source_predicate_conditional_completed -> source_conditional_post_metadata
  val source_conditional_post_metadata_for :
    SmtReplayInvocationWork.portfolio -> source_conditional_post_metadata ->
    {condition_variables:Term.term list,equation_variables:Term.term list,
     hypothesis_variables:Term.term list,unknown:SmtReplayGraph.node list,
     native_hypothesis_variables:Term.term list,types:Type.hol_type list,
     reason:string option}

  (* Optional ORIGINAL-clause refinement from SAME completed ancestry only.
     Metadata DATA grants no GEN/HO or caller FV/variable authority. *)
  val prepare_source_conditional_post_metadata_refined :
    SmtReplayInvocationWork.portfolio ->
    source_predicate_conditional_completed -> source_conditional_post_metadata

  (* Pure completed-derived DATA, never a future executable proof quote. *)
  datatype source_conditional_scalar_decision = ConditionalIdentity
    | ConditionalSingleton of Term.term | ConditionalNotCovered of string
  type source_conditional_native_portfolio
  val prepare_source_conditional_native_portfolio :
    SmtReplayInvocationWork.portfolio ->
    source_predicate_conditional_completed ->
    source_conditional_native_portfolio
  val source_conditional_native_portfolio_for :
    SmtReplayInvocationWork.portfolio -> source_conditional_native_portfolio ->
    {statement:Term.term,decision:source_conditional_scalar_decision,
     complete:bool,hypotheses:int,raw:IntInf.int,inclusive:IntInf.int,
     annotations:IntInf.int}

  (* Syntax DATA, with no executable quote, policy or proof entitlement. *)
  datatype source_scalar_tag_role = ScalarInputTag | ScalarLibraryTag
    | ScalarEmptyTag | ScalarLibraryInputMerge | ScalarNoTheoremTag
  type source_scalar_metrics =
    {raw:IntInf.int,inclusive:IntInf.int,annotations:IntInf.int}
  type source_scalar_operation =
    {event:string,primitive:string,optional:bool,counts_new_theorem:bool,
     tag:source_scalar_tag_role,result:source_scalar_metrics option,
     operands:source_scalar_metrics,native_hypotheses:int,
     result_hyp:source_scalar_metrics,operand_hyp:source_scalar_metrics}
  type source_scalar_syntax_footprint
  val prepare_source_scalar_syntax_footprint :
    SmtReplayInvocationWork.portfolio ->
    source_predicate_conditional_completed -> source_scalar_syntax_footprint
  val source_scalar_syntax_footprint_for :
    SmtReplayInvocationWork.portfolio -> source_scalar_syntax_footprint ->
    {complete:bool,reason:string option,hypotheses:int,
     operations:source_scalar_operation list}

  (* Actual Type DATA; no policy/proof execution or operation credit. *)
  type source_scalar_type_data
  val prepare_source_scalar_type_data :
    SmtReplayInvocationWork.portfolio ->
    source_predicate_conditional_completed -> source_scalar_type_data
  val source_scalar_type_data_for :
    SmtReplayInvocationWork.portfolio -> source_scalar_type_data ->
    {complete:bool,reason:string option,operations:int,ports:int,
     arrows:int,annotations:IntInf.int}
  type source_conditional_closure_data=
    {covered:bool,reason:string option,native_hypotheses:int,
    used_rows:int,support_rows:int,definitions:int,original_roots:int,
    source_occurrences:int,
    body_raw:IntInf.int,body_inclusive:IntInf.int,body_annotations:IntInf.int,
    hypotheses_raw_upper:IntInf.int,hypotheses_inclusive_upper:IntInf.int,
    hypotheses_annotations_upper:IntInf.int,strict_input_bounds:bool,
    input_limit:int,output_limit:int,template_limit:int}
  type source_conditional_closure_plan
  (* Bounded existing ALL-row closure metadata; not proof admission. *)
  val prepare_source_conditional_closure_plan :
    SmtReplayInvocationWork.portfolio ->
    source_predicate_conditional_completed -> source_conditional_closure_plan
  val source_conditional_closure_plan_for :
    SmtReplayInvocationWork.portfolio -> source_conditional_closure_plan ->
    source_conditional_closure_data

  (* Constructor-origin DATA only; not a GEN invoice or Ready authority. *)
  type source_conditional_constructor_origins
  val prepare_source_conditional_constructor_origins :
    SmtReplayInvocationWork.portfolio -> source_predicate_conditional_completed
    -> source_conditional_constructor_origins
  val source_conditional_constructor_origins_for :
    SmtReplayInvocationWork.portfolio -> source_conditional_constructor_origins
    -> {complete:bool,conclusion_known:bool,incoming_conclusion_known:bool,
        hypotheses:int,known_hypotheses:int,unresolved_hypotheses:int,
        captured_events:int}

  (* Fresh paid fixed-library DATA; no theorem/Scope/Ready grant. *)
  type source_eqt_cache_read
  type source_eqt_cache_data =
    {valid:bool,body_nodes:int,type_nodes:int,name_bytes:int,
     closed:bool,bare:bool}
  val prepare_source_eqt_cache_read :
    SmtReplayInvocationWork.portfolio -> source_eqt_cache_read
  val source_eqt_cache_read_for : SmtReplayInvocationWork.portfolio ->
    source_eqt_cache_read -> source_eqt_cache_data

  (* Actual native-effect origin DATA, separately from historical emits. *)
  type source_conditional_effect_origins
  val prepare_source_conditional_effect_origins :
    SmtReplayInvocationWork.portfolio ->
    source_predicate_conditional_completed -> source_conditional_effect_origins
  val source_conditional_effect_origins_for :
    SmtReplayInvocationWork.portfolio -> source_conditional_effect_origins ->
    {recorded:bool,complete:bool,conclusion_known:bool,hypotheses:int,
     known_hypotheses:int,unresolved_hypotheses:int}

  (* Optional bounded local closure. No GEN/HO/Ready or theorem getter. *)
  type source_conditional_local_plan
  type source_conditional_local_proof
  type source_conditional_local_plan_data =
    {covered:bool,reason:string option,operations:int,support_rows:int,
     definitions:int,original_roots:int,source_occurrences:int,
     quote:IntInf.int,
     body_raw:IntInf.int,body_inclusive:IntInf.int,
     body_annotations:IntInf.int,strict_input_bounds:bool}
  val prepare_source_conditional_local_plan :
    SmtReplayInvocationWork.portfolio -> source_predicate_conditional_completed
    -> source_conditional_local_plan
  val source_conditional_local_plan_for :
    SmtReplayInvocationWork.portfolio -> source_conditional_local_plan
    -> source_conditional_local_plan_data
  val execute_source_conditional_local_plan :
    SmtReplayInvocationWork.portfolio -> source_conditional_local_plan
    -> source_conditional_local_proof
  val source_conditional_local_proof_for :
    SmtReplayInvocationWork.portfolio -> source_conditional_local_proof ->
    {closed_definitions:int,hypotheses:int,body_raw:IntInf.int,
     body_inclusive:IntInf.int,body_annotations:IntInf.int,
     strict_input_bounds:bool}

  (* Distinct bounded proof opcode; no SourceRealization/SCE is issued. *)
  type source_bounded_scalar_gen_plan
  type source_bounded_scalar_gen_result
  val prepare_source_bounded_scalar_gen : SmtReplayInvocationWork.portfolio ->
    source_predicate_conditional_completed -> source_bounded_scalar_gen_plan
  val source_bounded_scalar_gen_plan_for :
    SmtReplayInvocationWork.portfolio -> source_bounded_scalar_gen_plan ->
    {variable:Term.term,input:Term.term,original_hypothesis:Term.term,
     normalized_hypothesis:Term.term,statement:Term.term,
     types:Type.hol_type list,input_tag:Tag.tag,
     native_calls:int,subtotal:IntInf.int}
  val admit_source_bounded_scalar_gen : SmtReplayInvocationWork.portfolio ->
    {plan:source_bounded_scalar_gen_plan,check_type:Type.hol_type -> unit} ->
    unit
  val execute_source_bounded_scalar_gen : SmtReplayInvocationWork.portfolio ->
    source_bounded_scalar_gen_plan -> source_bounded_scalar_gen_result
  val source_bounded_scalar_gen_result_for :
    SmtReplayInvocationWork.portfolio -> source_bounded_scalar_gen_result ->
    {statement:Term.term,hypotheses:Term.term list,
     tag:Tag.tag,native_calls:int}

  (* Additive closed leaves with explicit semantic policy. No Work/Scope
     grant, block realization or default selection follows from a leaf. *)
  val record_closed_with_policy : SmtReplayGraph.graph ->
    SmtReplayGraph.scope ->
    {node:SmtReplayGraph.node,theorem:Thm.thm,
     template_limit:SmtReplayResourcePolicy.limit,
     check_type:Type.hol_type -> unit} -> closed_fact
  val record_closed_from_import_with_policy : SmtReplayGraph.graph ->
    SmtReplayGraph.scope ->
    {node:SmtReplayGraph.node,theorem:Thm.thm,
     template_limit:SmtReplayResourcePolicy.limit,
     check_type:Type.hol_type -> unit} -> closed_fact
  val record_conversion_with_policy : SmtReplayGraph.graph ->
    SmtReplayGraph.scope ->
    {source:SmtReplayGraph.node,source_view:SmtReplayGraph.source,
     target:SmtReplayGraph.node,target_view:SmtReplayGraph.source,
     theorem:Thm.thm,template_limit:SmtReplayResourcePolicy.limit,
     check_type:Type.hol_type -> unit} -> closed_conversion
  val record_typed_conversion_with_policy : SmtReplayGraph.graph ->
    SmtReplayGraph.scope ->
    {source:SmtReplayGraph.node,source_view:SmtReplayGraph.source,
     target:SmtReplayGraph.node,target_view:SmtReplayGraph.source,
     theorem:Thm.thm,template_limit:SmtReplayResourcePolicy.limit,
     check_type:Type.hol_type -> unit} -> closed_conversion
  val validate_closed_fact_with_policy : SmtReplayGraph.graph ->
    SmtReplayGraph.scope -> SmtReplayResourcePolicy.limit ->
    closed_fact -> unit
  val validate_conversion_with_policy : SmtReplayGraph.graph ->
    SmtReplayGraph.scope -> SmtReplayResourcePolicy.limit ->
    closed_conversion -> unit

  (* Additive closed leaves with explicit semantic policy. No Work/Scope
     grant, block realization or default selection follows from a leaf. *)
  val record_closed_with_policy_profiles : SmtReplayGraph.graph ->
    SmtReplayGraph.scope ->
    {node:SmtReplayGraph.node,theorem:Thm.thm,
     template_limit:SmtReplayResourcePolicy.limit,
     check_type:Type.hol_type -> unit,
     profiles:SmtReplayGraph.policy_opaque_profile list} -> closed_fact
  val record_closed_from_import_with_policy_profiles : SmtReplayGraph.graph ->
    SmtReplayGraph.scope ->
    {node:SmtReplayGraph.node,theorem:Thm.thm,
     template_limit:SmtReplayResourcePolicy.limit,
     check_type:Type.hol_type -> unit,
     profiles:SmtReplayGraph.policy_opaque_profile list} -> closed_fact
  val record_conversion_with_policy_profiles : SmtReplayGraph.graph ->
    SmtReplayGraph.scope ->
    {source:SmtReplayGraph.node,source_view:SmtReplayGraph.source,
     target:SmtReplayGraph.node,target_view:SmtReplayGraph.source,
     theorem:Thm.thm,template_limit:SmtReplayResourcePolicy.limit,
     check_type:Type.hol_type -> unit,
     profiles:SmtReplayGraph.policy_opaque_profile list} -> closed_conversion
  val record_typed_conversion_with_policy_profiles : SmtReplayGraph.graph ->
    SmtReplayGraph.scope ->
    {source:SmtReplayGraph.node,source_view:SmtReplayGraph.source,
     target:SmtReplayGraph.node,target_view:SmtReplayGraph.source,
     theorem:Thm.thm,template_limit:SmtReplayResourcePolicy.limit,
     check_type:Type.hol_type -> unit,
     profiles:SmtReplayGraph.policy_opaque_profile list} -> closed_conversion

  (* Distinct policy plans cannot be passed to int-template native blocks.
     Each plan is owned by the actual original Work and lexical frame. *)
  type policy_realization_frontier
  val prepare_realization_frontier_with_policy :
    SmtReplayInvocationWork.portfolio ->
    {frame:SmtReplayOwnedScopeReceipt.receipt,
     roots:SmtReplayGraph.node list,closed_facts:closed_fact list,
     conversions:closed_conversion list} -> policy_realization_frontier
  val prepare_original_realization_frontier_with_policy :
    SmtReplayInvocationWork.portfolio ->
    {roots:SmtReplayGraph.node list,closed_facts:closed_fact list,
     conversions:closed_conversion list} -> policy_realization_frontier
  val prepare_original_realization_frontier_with_extras_with_policy :
    SmtReplayInvocationWork.portfolio ->
    {roots:SmtReplayGraph.node list,additional_sources:SmtReplayGraph.node list,
     closed_facts:closed_fact list,conversions:closed_conversion list} ->
    policy_realization_frontier
  val prepare_scoped_original_realization_frontier_with_policy :
    SmtReplayInvocationWork.portfolio ->
    {frame:SmtReplayOwnedScopeReceipt.receipt,
     roots:SmtReplayGraph.node list,additional_sources:SmtReplayGraph.node list,
     closed_facts:closed_fact list,conversions:closed_conversion list} ->
    policy_realization_frontier
  val realization_frontier_data_with_policy_for :
    SmtReplayInvocationWork.portfolio -> policy_realization_frontier ->
    {graph:SmtReplayGraph.graph,scope:SmtReplayGraph.scope,
     roots:SmtReplayGraph.node list,sources:SmtReplayGraph.node list,
     reachable:SmtReplayGraph.node list,atoms:SmtReplayGraph.node list,
     template_limit:SmtReplayResourcePolicy.limit}
  type policy_realization_tables_plan
  val prepare_owned_realization_tables_with_policy :
    SmtReplayInvocationWork.portfolio -> policy_realization_frontier ->
    policy_realization_tables_plan
  val validate_realization_tables_with_policy :
    SmtReplayInvocationWork.portfolio -> policy_realization_tables_plan -> unit
  val realization_tables_guard_work_with_policy :
    SmtReplayInvocationWork.portfolio -> policy_realization_tables_plan ->
    IntInf.int
  val realization_tables_data_with_policy_for :
    SmtReplayInvocationWork.portfolio -> policy_realization_tables_plan ->
    {source_count:IntInf.int,closed_count:IntInf.int,total_count:IntInf.int,
     definition_rows:(int * IntInf.int) list}

  (* The semantic policy is not native permission. This separate plan
     retains an actual finite NativeContract and measures the compact
     Context/H and named/generated Type portfolio before construction.
     Expanded Context/results are optional forecasts, not admission. *)
  type policy_native_freeze_plan
  val prepare_native_realization_freeze_with_policy :
    SmtReplayInvocationWork.portfolio ->
    {tables:policy_realization_tables_plan,
     contract:SmtReplayNativeContract.contract,
     profiles:SmtReplayGraph.policy_opaque_profile list,ordinal:int,
     check_type:Type.hol_type -> unit} -> policy_native_freeze_plan
  val freeze_owned_realization_tables_with_policy :
    SmtReplayInvocationWork.portfolio -> policy_native_freeze_plan -> block
  val native_realization_freeze_data_for :
    SmtReplayInvocationWork.portfolio -> policy_native_freeze_plan ->
    {compact_context:IntInf.int * IntInf.int * IntInf.int,
     actual_context:(IntInf.int * IntInf.int * IntInf.int) option,
     actual_results:(SmtReplayGraph.node *
       (IntInf.int * IntInf.int * IntInf.int) option) list,
     native_template:int,leaf_count:int}
  val policy_native_block_owner_for : SmtReplayInvocationWork.portfolio ->
    block -> {graph:SmtReplayGraph.graph,scope:SmtReplayGraph.scope,
      contract:SmtReplayNativeContract.contract}

  (* Fixed binder-free compact rules, inside SAME original Work action.
     Actual native ceilings derive only from the block's retained NC. *)
  type policy_primitive_plan
  val prepare_primitive_with_policy : SmtReplayInvocationWork.portfolio ->
    block -> compact_primitive -> edge list -> policy_primitive_plan
  val execute_primitive_with_policy : SmtReplayInvocationWork.portfolio ->
    policy_primitive_plan -> edge
  val constructor_with_policy : SmtReplayInvocationWork.portfolio ->
    block -> SmtReplayGraph.node -> edge
  type policy_closed_named_inst_plan
  val prepare_closed_named_inst_with_policy :
    SmtReplayInvocationWork.portfolio -> block ->
    {substitution:(Term.term,Term.term) Lib.subst,theorem:Thm.thm} ->
    policy_closed_named_inst_plan
  val execute_closed_named_inst_with_policy :
    SmtReplayInvocationWork.portfolio -> policy_closed_named_inst_plan -> edge
  (* Close compact law, then one simultaneous binder-free schema INST.
     Residues are actual retained representatives, never caller syntax. *)
  type policy_realization_plan
  type policy_source_realization
  val prepare_realization_with_policy : SmtReplayInvocationWork.portfolio ->
    block -> SmtReplayGraph.node -> edge -> policy_realization_plan
  val execute_realization_with_policy : SmtReplayInvocationWork.portfolio ->
    policy_realization_plan -> policy_source_realization
  (* SAME current Work action. Every entry retains the original individual
     preparation/native quote. Execution consumes this private block once
     after all witnesses succeed; a failed batch publishes no results. *)
  type policy_realization_batch
  val prepare_realization_batch_with_policy :
    SmtReplayInvocationWork.portfolio -> block ->
    (SmtReplayGraph.node * edge) list -> policy_realization_batch
  val execute_realization_batch_with_policy :
    SmtReplayInvocationWork.portfolio -> policy_realization_batch ->
    policy_source_realization list
  val policy_source_realization_theorem_for :
    SmtReplayInvocationWork.portfolio -> policy_source_realization -> Thm.thm

  datatype policy_boolean_rule = PolicyImplicationMP | PolicyConjunction
    | PolicyConjunctLeft | PolicyConjunctRight | PolicyNotIntro
    | PolicyNotElim | PolicyEqTrueElim | PolicyEqFalseElim
    | PolicyContradiction of SmtReplayGraph.node
  type policy_boolean_plan
  val prepare_boolean_primitive_with_policy :
    SmtReplayInvocationWork.portfolio -> block -> policy_boolean_rule ->
    edge list -> policy_boolean_plan
  val execute_boolean_primitive_with_policy :
    SmtReplayInvocationWork.portfolio -> policy_boolean_plan -> edge
  val compact_profile_with_policy : SmtReplayInvocationWork.portfolio ->
    block -> Term.term ->
    {raw:IntInf.int,inc:IntInf.int,ann:IntInf.int,ty:IntInf.int}
  val native_type_weight_with_policy : SmtReplayInvocationWork.portfolio ->
    block -> Type.hol_type -> IntInf.int

  val record_closed_with_policy_scoped_profiles :
    SmtReplayGraph.graph -> SmtReplayGraph.scope ->
    {node:SmtReplayGraph.node,theorem:Thm.thm,
     template_limit:SmtReplayResourcePolicy.limit,
     check_type:Type.hol_type -> unit,
     profiles:SmtReplayGraph.policy_opaque_profile list} -> closed_fact
  type scoped_generated_equality
  val record_generated_equality_with_policy_scoped_profiles :
    SmtReplayGraph.graph -> SmtReplayGraph.scope ->
    {node:SmtReplayGraph.node,theorem:Thm.thm,
     template_limit:SmtReplayResourcePolicy.limit,
     check_type:Type.hol_type -> unit,
     profiles:SmtReplayGraph.policy_opaque_profile list} ->
    scoped_generated_equality
  val scoped_generated_equality_for : SmtReplayGraph.graph ->
    SmtReplayGraph.scope -> SmtReplayResourcePolicy.limit ->
    scoped_generated_equality ->
    {fact:closed_fact,source:SmtReplayGraph.node,target:SmtReplayGraph.node,
     metric:SmtReplayGraph.profiled_metric,
     profiles:SmtReplayGraph.policy_opaque_profile list,
     raw:IntInf.int,inclusive:IntInf.int}

  (* Only a genuine closed policy realization can mint this conversion.
     The original Block, NC, Scope, epochs and captures remain backing. *)
  val policy_source_realization_data_for :
    SmtReplayInvocationWork.portfolio -> policy_source_realization ->
    {graph:SmtReplayGraph.graph,root:SmtReplayGraph.scope,
     scope:SmtReplayGraph.scope,sources:SmtReplaySource.sources,
     frame:SmtReplayOwnedScopeReceipt.receipt,equality:SmtReplayGraph.node,
     source:SmtReplayGraph.node,target:SmtReplayGraph.node,
     template_policy:SmtReplayResourcePolicy.limit,
     native_contract:SmtReplayNativeContract.contract}
  val conversion_from_policy_source_realization_for :
    SmtReplayInvocationWork.portfolio -> policy_source_realization ->
    closed_conversion

  (* Pure guarded metadata from a genuine closed policy equality receipt.
     Native producers retain their existing owned-action requirements. *)
  val policy_source_realization_closed_fact_for :
    SmtReplayInvocationWork.portfolio -> policy_source_realization ->
    closed_fact

  (* Only an actual completed SOURCE-FREE realization. The immutable clean
     canonical proof is authenticated before the output closure inventory
     is captured. The ordinary policy result retains genuine output/frame/
     NC/epoch backing, without repeatedly validating consumed derivation
     tables. The established export and priced route remain unchanged.
     Outside an action; no raw theorem, Source fact or new admission. *)
  val completed_policy_source_realization_closed_fact_for :
    SmtReplayInvocationWork.portfolio -> policy_source_realization ->
    closed_fact

  (* Authentic receipt/frame/source/RHS plus acquired scoped target DATA.
     The Q consumer still applies its real Generated metadata/native gates. *)
  val policy_source_realization_generated_equality_for :
    SmtReplayInvocationWork.portfolio -> policy_source_realization ->
    {profiles:SmtReplayGraph.policy_opaque_profile list} ->
    scoped_generated_equality

  val record_typed_conversion_with_policy_scoped_profiles :
    SmtReplayGraph.graph -> SmtReplayGraph.scope ->
    {source:SmtReplayGraph.node,source_view:SmtReplayGraph.source,
     target:SmtReplayGraph.node,target_view:SmtReplayGraph.source,
     theorem:Thm.thm,template_limit:SmtReplayResourcePolicy.limit,
     check_type:Type.hol_type -> unit,
     profiles:SmtReplayGraph.policy_opaque_profile list} -> closed_conversion

  (* Owns one Work action. Local slots come only from the genuine old
     Block after its immutable original S prefix; no replacement NC. *)
  val discharge_sources_with_policy : SmtReplayInvocationWork.portfolio ->
    block -> {indices:int list,body:SmtReplayGraph.node,edge:edge,
      ordinal:int,check_type:Type.hol_type -> unit} ->
    {block:block,target:SmtReplayGraph.node,edge:edge}

  (* Owns one Work action. Both inputs retain SAME actual frame and NC;
     no raw theorem, replacement contract or Source prefix is accepted. *)
  val join_blocks_with_policy : SmtReplayInvocationWork.portfolio ->
    {left:{block:block,body:SmtReplayGraph.node,edge:edge},
     right:{block:block,body:SmtReplayGraph.node,edge:edge},
     ordinal:int,check_type:Type.hol_type -> unit} ->
    {block:block,left:edge,right:edge}

  (* Fixed local ASSUME/SPEC/DISCH programme. Inputs are genuine owned graph
     ports and an authentic edge in this Block; no native theorem is supplied.
     Both entry points require the caller's existing Work action. *)
  type policy_local_specialize_plan
  val prepare_local_specialize_with_policy :
    SmtReplayInvocationWork.portfolio -> block ->
    {premise:{node:SmtReplayGraph.node,edge:edge},
     arguments:SmtReplayGraph.node list,target:SmtReplayGraph.node,
     profiles:SmtReplayGraph.policy_opaque_profile list,
     check_type:Type.hol_type -> unit} -> policy_local_specialize_plan
  val execute_local_specialize_with_policy :
    SmtReplayInvocationWork.portfolio -> policy_local_specialize_plan ->
    closed_fact

  (* Pure revocation of an actual same-Work policy Block. All old edges and
     naming handles fail their ordinary active guard afterwards. No native
     proof, realization receipt, allowance or credit is produced. *)
  val retire_policy_block_for : SmtReplayInvocationWork.portfolio ->
    block -> unit

  (* Only a genuine same-Work realized contradiction can prepare the fixed
     original Source CCONTR/SYM/EQ_MP closure. Both operations require the
     caller's existing Work action. Legacy Source.close stays unchanged. *)
  type policy_source_close_plan
  val prepare_source_close_with_policy :
    SmtReplayInvocationWork.portfolio -> policy_source_realization ->
    {profiles:SmtReplayGraph.policy_opaque_profile list,
     check_type:Type.hol_type -> unit} -> policy_source_close_plan
  val execute_source_close_with_policy :
    SmtReplayInvocationWork.portfolio -> policy_source_close_plan -> Thm.thm

  (* A genuine canonical closed equality supplies an owned typed cut.
     No raw theorem/endpoints or new native admission are accepted. *)
  val conversion_from_closed_fact_with_policy_for :
    SmtReplayInvocationWork.portfolio ->
    {frame:SmtReplayOwnedScopeReceipt.receipt,fact:closed_fact} ->
    closed_conversion

  (* Authentic closed-fact cut lineage. No arbitrary conversion is adopted. *)
  type policy_closed_fact_cut
  val closed_fact_cut_with_policy_for :
    SmtReplayInvocationWork.portfolio ->
    {frame:SmtReplayOwnedScopeReceipt.receipt,fact:closed_fact} ->
    policy_closed_fact_cut
  val closed_fact_cut_data_with_policy_for :
    SmtReplayInvocationWork.portfolio -> policy_closed_fact_cut ->
    {frame:SmtReplayOwnedScopeReceipt.receipt,graph:SmtReplayGraph.graph,
     root:SmtReplayGraph.scope,scope:SmtReplayGraph.scope,
     sources:SmtReplaySource.sources,conversion:closed_conversion,
     equality:SmtReplayGraph.node,source:SmtReplayGraph.node,
     target:SmtReplayGraph.node}

  (* A closed universal-elimination schema over actual named Block nodes.
     No premise theorem or source proof is accepted or manufactured here.
     The existing executor performs the same admitted ASSUME/SPEC/DISCH
     programme and returns its genuine closed fact. Caller owns the action. *)
  val prepare_local_specialize_schema_with_policy :
    SmtReplayInvocationWork.portfolio -> block ->
    {source:SmtReplayGraph.node,arguments:SmtReplayGraph.node list,
     target:SmtReplayGraph.node,
     profiles:SmtReplayGraph.policy_opaque_profile list,
     check_type:Type.hol_type -> unit} -> policy_local_specialize_plan

  (* Additive Source fragments; UNSEALED. The layout is
     minted/continued only by actual same-Work Block producers. *)
  type policy_scope_slot
  type policy_scope_layout
  type policy_scope_snapshot
  type policy_scope_replay_plan
  val initial_scope_layout_with_policy_for :
    SmtReplayInvocationWork.portfolio -> block -> policy_scope_layout
  val scope_layout_sources_with_policy_for :
    SmtReplayInvocationWork.portfolio -> policy_scope_layout ->
    (SmtReplayGraph.node * policy_scope_slot) list
  val same_scope_slot_with_policy_for :
    SmtReplayInvocationWork.portfolio ->
    policy_scope_slot -> policy_scope_slot -> bool
  val rebuild_scope_layout_with_policy :
    SmtReplayInvocationWork.portfolio -> policy_scope_layout ->
    {append:SmtReplayGraph.node list,roots:SmtReplayGraph.node list,
     closed_facts:closed_fact list,conversions:closed_conversion list,
     ordinal:int,check_type:Type.hol_type -> unit} ->
    {block:block,layout:policy_scope_layout,appended:policy_scope_slot list}
  val capture_scope_snapshot_with_policy :
    SmtReplayInvocationWork.portfolio -> policy_scope_layout ->
    {indices:int list,outputs:{body:SmtReplayGraph.node,edge:edge} list,
     check_type:Type.hol_type -> unit} -> policy_scope_snapshot
  val prepare_scope_replay_batch_with_policy :
    SmtReplayInvocationWork.portfolio -> policy_scope_layout ->
    {snapshots:policy_scope_snapshot list,ordinal:int,
     check_type:Type.hol_type -> unit} -> policy_scope_replay_plan
  val execute_scope_replay_batch_with_policy :
    SmtReplayInvocationWork.portfolio -> policy_scope_replay_plan ->
    {block:block,layout:policy_scope_layout,
     outputs:{snapshot:policy_scope_snapshot,
       targets:(SmtReplayGraph.node * edge) list} list}

  (* Fully recorded, genuinely opened binder leaf only. Existing source
     acquisition is retained evidence, not permission granted by this port.
     Preparation admits the actual local equality/ALPHA/EQ_MP programme. *)
  type policy_alpha_leaf_plan
  val prepare_alpha_leaf_with_policy :
    SmtReplayInvocationWork.portfolio ->
    {frame:SmtReplayOwnedScopeReceipt.receipt,
     alpha:SmtReplayGraph.carrier_alpha,
     capture:SmtReplayGraph.profiled_metric,
     native_contract:SmtReplayNativeContract.contract,
     check_type:Type.hol_type -> unit} -> policy_alpha_leaf_plan
  val execute_alpha_leaf_with_policy :
    SmtReplayInvocationWork.portfolio -> policy_alpha_leaf_plan ->
    closed_fact

  (* Root-only actual binder-free result production. No caller target map.
     Caller owns the same Work action as the existing fixed SPEC preparer. *)
  val prepare_inferred_local_specialize_with_policy :
    SmtReplayInvocationWork.portfolio -> block ->
    {premise:{node:SmtReplayGraph.node,edge:edge},
     arguments:SmtReplayGraph.node list,
     profiles:SmtReplayGraph.policy_opaque_profile list,
     check_type:Type.hol_type -> unit} -> policy_local_specialize_plan

  datatype policy_clause_tree = PolicyClauseFalse of SmtReplayGraph.node
    | PolicyClauseLiteral of
        {node:SmtReplayGraph.node,atom:SmtReplayGraph.node,negative:bool}
    | PolicyClauseOr of
        {node:SmtReplayGraph.node,left:policy_clause_tree,
         right:policy_clause_tree}

  type policy_unit_resolution_plan
  (* Caller owns the actual Work action. Source trees retain recorded
     occurrence boundaries; the separate target expansion is authenticated
     against that same actual root before any rule/callback is executed. *)
  val prepare_unit_resolution_with_policy :
    SmtReplayInvocationWork.portfolio -> block ->
    {premises:{tree:policy_clause_tree,edge:edge} list,
     target:policy_clause_tree,target_expanded:policy_clause_tree option,
     check_type:Type.hol_type->unit} -> policy_unit_resolution_plan
  val execute_unit_resolution_with_policy :
    SmtReplayInvocationWork.portfolio -> policy_unit_resolution_plan -> edge

  (* DATA trees are checked against the actual same-Block constructors.
     The ordinary prepare entry retains its literal empty-fallback route. *)
  val prepare_raw_unit_resolution_with_policy :
    SmtReplayInvocationWork.portfolio -> block ->
    {premises:{tree:policy_clause_tree,edge:edge} list,
     target:policy_clause_tree,target_expanded:policy_clause_tree option,
     fallbacks:policy_clause_tree list,check_type:Type.hol_type->unit} ->
    policy_unit_resolution_plan

  (* Read-only exact-frame closed-fact guard. A realized fact's Work
     header and the genuine Scope receipt precede held backing. Ancestor
     visibility is deliberately insufficient for scoped closed-law rows;
     no equality shape, theorem export or new native admission is issued. *)
  val validate_closed_fact_in_scope_with_policy_for :
    SmtReplayInvocationWork.portfolio ->
    {frame:SmtReplayOwnedScopeReceipt.receipt,fact:closed_fact} -> unit
  (* The same scoped Generated equality DATA, with expected Work and an
     authentic exact frame checked BEFORE its private fact/metric backing.
     Uses the genuine stored cap; accepts no caller graph, scope or policy.
     No new proof, Source permission, native admission or receipt is made. *)
  val scoped_generated_equality_with_policy_for :
    SmtReplayInvocationWork.portfolio ->
    {frame:SmtReplayOwnedScopeReceipt.receipt,
     equality:scoped_generated_equality} ->
    {fact:closed_fact,source:SmtReplayGraph.node,target:SmtReplayGraph.node,
     metric:SmtReplayGraph.profiled_metric,
     profiles:SmtReplayGraph.policy_opaque_profile list,
     raw:IntInf.int,inclusive:IntInf.int}

  (* A separate named owner with individual authentic hypotheses. No old
     block or edge is cast or changed by this opt-in programme. *)
  type policy_sparse_block
  type policy_sparse_edge
  type policy_sparse_freeze_plan
  type policy_sparse_named_inst_plan
  type policy_sparse_realization_plan
  type policy_sparse_realization_batch
  type policy_sparse_result
  val prepare_policy_sparse_freeze :
    SmtReplayInvocationWork.portfolio ->
    {tables:policy_realization_tables_plan,
     contract:SmtReplayNativeContract.contract,
     check_type:Type.hol_type -> unit} -> policy_sparse_freeze_plan
  val execute_policy_sparse_freeze :
    SmtReplayInvocationWork.portfolio -> policy_sparse_freeze_plan ->
    policy_sparse_block
  val policy_sparse_owner_for :
    SmtReplayInvocationWork.portfolio -> policy_sparse_block ->
    {graph:SmtReplayGraph.graph,scope:SmtReplayGraph.scope,
     contract:SmtReplayNativeContract.contract}
  val policy_sparse_sources_for :
    SmtReplayInvocationWork.portfolio -> policy_sparse_block ->
    SmtReplayGraph.node list
  val policy_sparse_name_for :
    SmtReplayInvocationWork.portfolio -> policy_sparse_block ->
    SmtReplayGraph.node -> Term.term
  val policy_sparse_theorem_for :
    SmtReplayInvocationWork.portfolio -> policy_sparse_block ->
    policy_sparse_edge -> Thm.thm
  val policy_sparse_source_for :
    SmtReplayInvocationWork.portfolio -> policy_sparse_block -> int ->
    policy_sparse_edge
  val policy_sparse_closed_for :
    SmtReplayInvocationWork.portfolio -> policy_sparse_block ->
    closed_fact -> policy_sparse_edge
  val policy_sparse_conversion_for :
    SmtReplayInvocationWork.portfolio -> policy_sparse_block ->
    closed_conversion -> policy_sparse_edge
  val policy_sparse_definition_for :
    SmtReplayInvocationWork.portfolio -> policy_sparse_block ->
    SmtReplayGraph.node -> policy_sparse_edge
  val policy_sparse_constructor_for :
    SmtReplayInvocationWork.portfolio -> policy_sparse_block ->
    SmtReplayGraph.node -> policy_sparse_edge
  val policy_sparse_primitive_for :
    SmtReplayInvocationWork.portfolio -> policy_sparse_block ->
    compact_primitive -> policy_sparse_edge list -> policy_sparse_edge
  val policy_sparse_boolean_for :
    SmtReplayInvocationWork.portfolio -> policy_sparse_block ->
    policy_boolean_rule -> policy_sparse_edge list -> policy_sparse_edge
  val prepare_policy_sparse_named_inst :
    SmtReplayInvocationWork.portfolio -> policy_sparse_block ->
    {substitution:(Term.term,Term.term)Lib.subst,theorem:Thm.thm} ->
    policy_sparse_named_inst_plan
  val execute_policy_sparse_named_inst :
    SmtReplayInvocationWork.portfolio -> policy_sparse_named_inst_plan ->
    policy_sparse_edge
  val prepare_policy_sparse_realization :
    SmtReplayInvocationWork.portfolio -> policy_sparse_block ->
    {target:SmtReplayGraph.node,edge:policy_sparse_edge} ->
    policy_sparse_realization_plan
  val execute_policy_sparse_realization :
    SmtReplayInvocationWork.portfolio -> policy_sparse_realization_plan ->
    policy_sparse_result
  val prepare_policy_sparse_realization_batch :
    SmtReplayInvocationWork.portfolio -> policy_sparse_block ->
    {target:SmtReplayGraph.node,edge:policy_sparse_edge} list ->
    policy_sparse_realization_batch
  val execute_policy_sparse_realization_batch :
    SmtReplayInvocationWork.portfolio -> policy_sparse_realization_batch ->
    policy_sparse_result list
  val policy_sparse_result_for :
    SmtReplayInvocationWork.portfolio -> policy_sparse_result ->
    {theorem:Thm.thm,target:SmtReplayGraph.node,
     original_occurrences:int list}


  (* Explicit validated profiles; retained metrics never supply admission.
     Called inside the existing SAME original Work action. *)
  val prepare_policy_sparse_freeze_with_profiles :
    SmtReplayInvocationWork.portfolio ->
    {tables:policy_realization_tables_plan,
     contract:SmtReplayNativeContract.contract,
     profiles:SmtReplayGraph.policy_opaque_profile list,
     check_type:Type.hol_type -> unit} -> policy_sparse_freeze_plan

  (* A genuine sparse result is the only public witness constructor. *)
  type policy_sparse_parent_source
  val record_policy_sparse_parent_source :
    SmtReplayInvocationWork.portfolio -> policy_sparse_result ->
    policy_sparse_parent_source
  val policy_sparse_parent_source_for :
    SmtReplayInvocationWork.portfolio -> policy_sparse_parent_source ->
    {graph:SmtReplayGraph.graph,scope:SmtReplayGraph.scope,
     frame:SmtReplayOwnedScopeReceipt.receipt,
     sources:SmtReplaySource.sources,
     contract:SmtReplayNativeContract.contract,
     target:SmtReplayGraph.node,theorem:Thm.thm,
     original_occurrences:int list}

end
