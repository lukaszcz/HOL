(* Backend selection DATA over the authenticated outbound query borrow. *)
signature SmtLib_GraphBackendSelection =
sig
  type carrier = SmtLib_GraphQueryAnalysis.carrier
  type selection =
    {goal:carrier,assumptions:carrier list,
     sets:carrier list,bags:carrier list,raw_numbers:carrier list,
     finite_sets:carrier list,finite_bags:carrier list,
     sequence_emission:bool,set_backend:SmtLib.outbound_set_backend,
     bag_backend:SmtLib.outbound_bag_backend,
     target:{solver:string,version:string option} option}

  (* All Set/Bag decisions use SmtLib's SAME policy and native registry.
     Seq eligibility uses the existing shared graph analysis. Operations
     must be the complete actual carrier factory, not shape placeholders.
     Finite evidence remains authentic carrier DATA; this selection grants
     no permission to drop or rewrite original assumptions. The producer
     still needs its checked definition/original-source transport. *)
  val select : SmtLib_GraphQueryAnalysis.outbound_context ->
    {operations:carrier SmtLib.outbound_term_translation_operations,
     target:{solver:string,version:string option} option,
     emit_sequences:bool} -> selection

  (* The SAME decision programme and graph adapter report successful finite
     branches in actual child-before-parent order. Each call owns a fresh
     bool memo; hits reuse the caller's retained report descriptor. Evidence
     identifies the first matching operand and its IntInf position in the
     filtered FINITE/FINITE_BAG list, not an original Source index. Reports
     contain borrowed carriers and must be consumed/frozen during this
     borrow. They grant no theorem or hypothesis-erasure permission.
     A report callback Primary escapes without a bool-cache publication. *)
  val select_with_finite_trace :
    SmtLib_GraphQueryAnalysis.outbound_context ->
    (carrier SmtLib.outbound_finite_report -> unit) ->
    {operations:carrier SmtLib.outbound_term_translation_operations,
     target:{solver:string,version:string option} option,
     emit_sequences:bool} -> selection

  (* Later checked FINITE rewriting may demand operands not visited during
     marker eligibility. These predicates use the SAME policy, fresh memo
     and ordered evidence as selection, including any existing reports.
     Entry/exit and every predicate hit retain the original Q borrow guards;
     closures cannot be used after that borrow expires. No traversal or
     theorem construction is performed by this continuation interface. *)
  val with_finite_trace :
    SmtLib_GraphQueryAnalysis.outbound_context ->
    (carrier SmtLib.outbound_finite_report -> unit) ->
    {operations:carrier SmtLib.outbound_term_translation_operations,
     target:{solver:string,version:string option} option,
     emit_sequences:bool} ->
    ({selection:selection,finite_set_term:carrier -> bool,
      finite_bag_term:carrier -> bool,
      finite_set_hypothesis:carrier -> carrier option,
      finite_bag_hypothesis:carrier -> carrier option} -> 'a) -> 'a

  (* Construct and consume the store, dispatch, features and declaration
     metadata inside this installation. It binds the exact ordered query,
     restores every ambient translation cell on success or exception, and
     expires all context operations. No marker HOL Terms are fabricated. *)
  val with_context : SmtLib_GraphQueryAnalysis.outbound_context ->
    selection -> (SmtLib.outbound_backend_context -> 'a) -> 'a

  type transport
  (* Capture the actual original selection returned by the shared policy
     during its original borrow. Plain selection records remain DATA, not
     authority. Seeds come from the actual collection_terms analysis and
     the supplied selection must retain their exact ordered positions.
     Only modes/scoped nodes survive; no borrowed callback is saved. The
     original query association is checked again before seed use. *)
  val capture_transport : SmtReplayInvocationWork.portfolio ->
    SmtLib_GraphPreprocess.graph_query ->
    SmtLib_GraphQueryAnalysis.outbound_context -> selection -> transport

  (* The actual original selection target is scalar DATA. Expected Work
     precedes original backing validation, including on retired snapshots.
     An emitter compares its requested target before any output/preflight;
     changing the target would require a new original selection. *)
  val target_for_transport : SmtReplayInvocationWork.portfolio ->
    transport -> {solver:string,version:string option} option

  (* Reborrow the authentic ORIGINAL query for availability and RegLan
     preflight. Validate exact retained roots, graph/root/Sources before
     invoking opening or consumer callbacks. Original marker DATA and the
     actual sequence/target decisions are reused without backend selection.
     Call outside an action; the borrowed context expires on every outcome. *)
  val with_original_context_with_policy :
    SmtReplayInvocationWork.portfolio -> transport ->
    (SmtReplayGraph.scope -> SmtReplayGraph.node -> unit) ->
    ({context:SmtLib_GraphQueryAnalysis.outbound_context,
      sequence_emission:bool,
      target:{solver:string,version:string option} option} -> 'a) -> 'a

  (* Owns the new query borrow; call outside a Work action. Both authentic
     queries must retain the exact original graph, root and Sources. Seeded
     marker propagation uses new roots but original backend modes, without
     rerunning finite-evidence selection after checked assumption erasure. *)
  val with_transported_context_with_policy :
    SmtReplayInvocationWork.portfolio -> transport ->
    SmtLib_GraphPreprocess.graph_query ->
    (SmtReplayGraph.scope -> SmtReplayGraph.node -> unit) ->
    (SmtLib_GraphQueryAnalysis.outbound_context *
     SmtLib.outbound_backend_context -> 'a) -> 'a
end
