(* UNCOMPILED carrier-only callsite. Assertions precede positive Goal;
   fixed denial transport is last. Whole NUM/SIMP compatibility stays open.
   Initial genuine opening/private kernel work is not jointly quoted. *)
structure SmtLib_CheckedCarrierCallsite :> SmtLib_CheckedCarrierCallsite =
struct
  structure G = SmtReplayGraph
  structure S = SmtReplaySource
  structure W = SmtReplayInvocationWork
  structure K = SmtLib_CompactPositiveGoalSourceStage
  structure Legacy = SmtLib_OwnedPositiveGoalSourceStage
  structure GP = SmtLib_GraphPreprocess
  val _ = SmtLib_CompactPositiveGoalSourceStage.begin_provenance
  val _ = SmtLib_CompactCarrierScheduler.run_assumption_owned
  val _ = SmtReplayGraph.discover_compact_shared_partial
  val _ = SmtCheckedGraph.prepare_original
  val _ = CVC.CVC_SMT_Owned_Original_Source_Prover
  val _ = CVC.CVC_SMT_Owned_Original_Source_Prover_With_Emissions
  val _ = Z3.Z3_SMT_Original_Source_Prover_With_Work_And_Emissions
  val ERR = Feedback.mk_HOL_ERR "SmtLib_CheckedCarrierCallsite"
  type request =
    {limits : SmtCheckedGraph.limits,semantic_limits : W.limits,
     work_limit : int,check_type : Type.hol_type -> unit,
     scope_opened : G.scope -> unit}
  val prepare_stage = SmtLib_CheckedCarrierProducer.prepare_stage
  val prepare_compact_stage =
    SmtLib_CheckedCarrierProducer.prepare_compact_stage
  val run = SmtLib_CheckedCarrierProducer.run

  fun z3 {limits,semantic_limits,work_limit,check_type,scope_opened,
          local_law,nnf} original =
    run {limits = limits,semantic_limits = semantic_limits,
         work_limit = work_limit,check_type = check_type,
         scope_opened = scope_opened}
      (fn discover => Z3.Z3_SMT_Original_Source_Prover
        {limits = limits,discover = discover,local_law = local_law,nnf = nnf})
      original
  fun cvc {limits,semantic_limits,work_limit,check_type,scope_opened,
           ordinary_limit,worker,force_worker} original =
    run {limits = limits,semantic_limits = semantic_limits,
         work_limit = work_limit,check_type = check_type,
         scope_opened = scope_opened}
      (fn discover => CVC.CVC_SMT_Original_Source_Prover
        {limits = limits,discover = discover,ordinary_limit = ordinary_limit,
         worker = worker,force_worker = force_worker}) original

  val run_cvc_with_work = SmtLib_CheckedCarrierProducer.run_cvc_with_work

  fun cvc_with_work {limits,semantic_limits,work_limit,check_type,scope_opened,
                     ordinary_limit,worker,force_worker} original =
    run_cvc_with_work {limits = limits,semantic_limits = semantic_limits,
      work_limit = work_limit,check_type = check_type,
      scope_opened = scope_opened}
      (fn discover => CVC.CVC_SMT_Owned_Original_Source_Prover
        {limits = limits,discover = discover,ordinary_limit = ordinary_limit,
         worker = worker,force_worker = force_worker}) original

  (* Reuse the exact private actual-W discovery owner from the cvc route.
     No extra Source, normalization counter or Work portfolio is issued. *)
  fun z3_with_work {limits,semantic_limits,work_limit,check_type,scope_opened,
                    local_law,nnf} original =
    run_cvc_with_work {limits = limits,semantic_limits = semantic_limits,
      work_limit = work_limit,check_type = check_type,
      scope_opened = scope_opened}
      (fn discover => Z3.Z3_SMT_Original_Source_Prover_With_Work
        {limits = limits,discover = discover,local_law = local_law,nnf = nnf})
      original

  (* Actual same-W producer, genuine closed emitter registry, fixed workers.
     The original cvc/z3 and explicit-worker paths above remain unchanged. *)
  fun cvc_with_emissions
      {limits,semantic_limits,work_limit,check_type,scope_opened,
       ordinary_limit} original =
    run_cvc_with_work {limits = limits,semantic_limits = semantic_limits,
      work_limit = work_limit,check_type = check_type,
      scope_opened = scope_opened}
      (fn discover => CVC.CVC_SMT_Owned_Original_Source_Prover_With_Emissions
        {limits = limits,discover = discover,ordinary_limit = ordinary_limit})
      original

  fun z3_with_emissions
      {limits,semantic_limits,work_limit,check_type,scope_opened} original =
    run_cvc_with_work {limits = limits,semantic_limits = semantic_limits,
      work_limit = work_limit,check_type = check_type,
      scope_opened = scope_opened}
      (fn discover => Z3.Z3_SMT_Original_Source_Prover_With_Work_And_Emissions
        {limits = limits,discover = discover}) original

  val prepare_fixed_num_stage =
    SmtLib_CheckedCarrierProducer.prepare_fixed_num_stage
  val run_fixed_num_with_work =
    SmtLib_CheckedCarrierProducer.run_fixed_num_with_work
  fun cvc_fixed_num_with_work
      {limits,semantic_limits,work_limit,check_type,scope_opened,
       ordinary_limit,worker,force_worker} original =
    run_fixed_num_with_work
      {limits=limits,semantic_limits=semantic_limits,work_limit=work_limit,
       check_type=check_type,scope_opened=scope_opened}
      (fn discover => CVC.CVC_SMT_Owned_Original_Source_Prover
        {limits=limits,discover=discover,ordinary_limit=ordinary_limit,
         worker=worker,force_worker=force_worker}) original
  fun z3_fixed_num_with_work
      {limits,semantic_limits,work_limit,check_type,scope_opened,
       local_law,nnf} original =
    run_fixed_num_with_work
      {limits=limits,semantic_limits=semantic_limits,work_limit=work_limit,
       check_type=check_type,scope_opened=scope_opened}
      (fn discover => Z3.Z3_SMT_Original_Source_Prover_With_Work
        {limits=limits,discover=discover,local_law=local_law,nnf=nnf}) original
end
