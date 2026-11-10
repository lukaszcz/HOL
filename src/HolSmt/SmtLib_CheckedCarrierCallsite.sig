(* Proposed additive carrier-only entry; not a replacement for SIMP_TAC. *)
signature SmtLib_CheckedCarrierCallsite =
sig
  (* Bounded supported-discovery route; retains the caller's SAME Work.
     Opaque predicates still need the existing genuine opening prerequisite.
     The returned stage stays live until its owning consumer completes. *)
  val prepare_stage : SmtReplayInvocationWork.portfolio ->
    {import_limit : int,check_type : Type.hol_type -> unit,
     scope_opened : SmtReplayGraph.scope -> unit} ->
    SmtLib_OwnedPositiveGoalSourceStage.owner
  (* Automatic compact recipe route; old prepare_stage remains available. *)
  val prepare_compact_stage : SmtReplayInvocationWork.portfolio ->
    {import_limit : int,check_type : Type.hol_type -> unit,
     scope_opened : SmtReplayGraph.scope -> unit} ->
    SmtLib_CompactPositiveGoalSourceStage.owner
  val z3 :
    {limits : SmtCheckedGraph.limits,
     semantic_limits : SmtReplayInvocationWork.limits,work_limit : int,
     check_type : Type.hol_type -> unit,
     scope_opened : SmtReplayGraph.scope -> unit,
     local_law : Z3_GraphProofReplay.local_request -> Thm.thm option,
     nnf : Z3_GraphProofReplay.nnf_request -> Thm.thm option} ->
    Abbrev.goal -> SolverSpec.result
  val cvc :
    {limits : SmtCheckedGraph.limits,
     semantic_limits : SmtReplayInvocationWork.limits,work_limit : int,
     check_type : Type.hol_type -> unit,
     scope_opened : SmtReplayGraph.scope -> unit,ordinary_limit : int,
     worker : CPC_GraphProofReplay.worker,
     force_worker : CPC_GraphProofReplay.worker option} ->
    Abbrev.goal -> SolverSpec.result
  (* Optional cvc route carries the private genuine W.begin result through
     the wrapper/session/replay final receiver. Legacy cvc/z3 stay unchanged. *)
  val cvc_with_work :
    {limits : SmtCheckedGraph.limits,
     semantic_limits : SmtReplayInvocationWork.limits,work_limit : int,
     check_type : Type.hol_type -> unit,
     scope_opened : SmtReplayGraph.scope -> unit,ordinary_limit : int,
     worker : CPC_GraphProofReplay.worker,
     force_worker : CPC_GraphProofReplay.worker option} ->
    Abbrev.goal -> SolverSpec.result

  val z3_with_work :
    {limits : SmtCheckedGraph.limits,
     semantic_limits : SmtReplayInvocationWork.limits,work_limit : int,
     check_type : Type.hol_type -> unit,
     scope_opened : SmtReplayGraph.scope -> unit,
     local_law : Z3_GraphProofReplay.local_request -> Thm.thm option,
     nnf : Z3_GraphProofReplay.nnf_request -> Thm.thm option} ->
    Abbrev.goal -> SolverSpec.result

  val cvc_with_emissions :
    {limits : SmtCheckedGraph.limits,
     semantic_limits : SmtReplayInvocationWork.limits,work_limit : int,
     check_type : Type.hol_type -> unit,
     scope_opened : SmtReplayGraph.scope -> unit,ordinary_limit : int} ->
    Abbrev.goal -> SolverSpec.result

  val z3_with_emissions :
    {limits : SmtCheckedGraph.limits,
     semantic_limits : SmtReplayInvocationWork.limits,work_limit : int,
     check_type : Type.hol_type -> unit,
     scope_opened : SmtReplayGraph.scope -> unit} ->
    Abbrev.goal -> SolverSpec.result

  (* Fixed whole NUM route; SAME W, old carrier selectors unchanged. *)
  val prepare_fixed_num_stage : SmtReplayInvocationWork.portfolio ->
    {import_limit:int,check_type:Type.hol_type -> unit,
     scope_opened:SmtReplayGraph.scope -> unit} ->
    SmtLib_OwnedFixedNumSourceStage.owner
  val cvc_fixed_num_with_work :
    {limits:SmtCheckedGraph.limits,
     semantic_limits:SmtReplayInvocationWork.limits,work_limit:int,
     check_type:Type.hol_type -> unit,
     scope_opened:SmtReplayGraph.scope -> unit,ordinary_limit:int,
     worker:CPC_GraphProofReplay.worker,
     force_worker:CPC_GraphProofReplay.worker option} ->
    Abbrev.goal -> SolverSpec.result
  val z3_fixed_num_with_work :
    {limits:SmtCheckedGraph.limits,
     semantic_limits:SmtReplayInvocationWork.limits,work_limit:int,
     check_type:Type.hol_type -> unit,
     scope_opened:SmtReplayGraph.scope -> unit,
     local_law:Z3_GraphProofReplay.local_request -> Thm.thm option,
     nnf:Z3_GraphProofReplay.nnf_request -> Thm.thm option} ->
    Abbrev.goal -> SolverSpec.result
end
