structure SmtLib_GraphOwnedEmissions :> SmtLib_GraphOwnedEmissions =
struct
  structure W = SmtReplayInvocationWork
  structure GP = SmtLib_GraphPreprocess
  structure E = SmtLib_TranslationEmissions
  val _ = CPC_ProofReplay.graph_bounded_worker
  val _ = CPC_ProofReplay.graph_bounded_force_worker
  val _ = SmtLib_TranslationEmissions.emit
  val ERR = Feedback.mk_HOL_ERR "SmtLib_GraphOwnedEmissions"
  datatype receipt = Receipt of
    {work:W.portfolio,preprocessing:GP.validation,goal:Abbrev.goal,
     translation:SmtLib.translation,emission:E.receipt}
  fun validate_for expected (Receipt
      {work,preprocessing,goal,translation,emission}) =
    ((if Portable.pointer_eq (expected,work) then () else
        raise ERR "validate_for" "different original Work";
      GP.validate_with_work expected preprocessing;
      ignore (E.describe_for translation goal emission))
     handle primary => (W.close expected;raise primary))
  fun validate_input_for expected input
      (receipt as Receipt {work,preprocessing,...}) =
    ((if Portable.pointer_eq (expected,work) andalso
          Portable.pointer_eq (input,preprocessing) then () else
        raise ERR "validate_input_for" "different exact preprocessing input";
      validate_for expected receipt)
     handle primary => (W.close expected;raise primary))
  fun emit work preprocessing options =
    ((GP.validate_with_work work preprocessing;
      let val goal = GP.processed_goal preprocessing
          val {receipt = emission,translation,strings} = E.emit options goal
          val _ = GP.validate_with_work work preprocessing
          val receipt = Receipt {work = work,preprocessing = preprocessing,
            goal = goal,translation = translation,emission = emission}
          val _ = validate_for work receipt
      in {receipt = receipt,translation = translation,strings = strings} end)
     handle primary => (W.close work;raise primary))
  fun translation_for expected (receipt as Receipt {translation,...}) =
    (validate_for expected receipt;translation)
  fun selected expected (receipt as Receipt
      {goal,translation,emission,...}) =
    (validate_for expected receipt;
     #definitions (E.describe_for translation goal emission))
  fun worker_for expected receipt =
    let val fixed = CPC_ProofReplay.graph_bounded_worker
          (selected expected receipt)
    in fn request =>
      ((validate_for expected receipt;
        let val result = fixed request
        in validate_for expected receipt;result end)
       handle primary => (W.close expected;raise primary)) end
  fun force_worker_for expected receipt =
    let val fixed = CPC_ProofReplay.graph_bounded_force_worker
          (selected expected receipt)
    in fn request =>
      ((validate_for expected receipt;
        let val result = fixed request
        in validate_for expected receipt;result end)
       handle primary => (W.close expected;raise primary)) end
  val _ = CPC_ProofReplay.graph_bounded_worker_with_clause
  fun clause_worker_for expected receipt =
    let val fixed = CPC_ProofReplay.graph_bounded_worker_with_clause expected
          (selected expected receipt)
    in fn request =>
      ((validate_for expected receipt;
        let val result = fixed request
        in validate_for expected receipt;result end)
       handle primary => (W.close expected;raise primary)) end
  val _ = Z3_ProofReplay.graph_bounded_local_law
  val _ = Z3_ProofReplay.graph_bounded_nnf
  fun z3_workers_for expected receipt proof =
    let val _ = validate_for expected receipt
        val sources = W.original_sources expected
        val graph = SmtReplaySource.owning_graph sources
        val definitions = selected expected receipt
        val local_fixed = Z3_ProofReplay.graph_bounded_local_law_using
          (W.spend_guard_policy expected) graph definitions proof
        val nnf_fixed = Z3_ProofReplay.graph_bounded_nnf graph
        fun protect producer request =
          ((validate_for expected receipt;
            let val result = producer request
            in validate_for expected receipt;result end)
           handle primary => (W.close expected;raise primary))
        (* The caller's actual owned law becomes an ordinary extra Source
           slot, so its whole template must fit BEFORE the fixed worker.
           Arguments keep the existing fixed producer bound, not a new
           template-derived argument cap. The short quote action ends before
           any producer/policy callback. *)
        fun quote_local (request : Z3_GraphProofReplay.local_request) =
          W.with_step expected (fn () =>
            let val _ = validate_for expected receipt
                val cap = #template_limit (W.semantic_limits expected)
                val argument_cap = SmtResource.max_bitblast_term_nodes
                val nodes = #law request :: List.map #node (#arguments request)
                val inventory = (cap,#law request) :: List.map
                  (fn argument => (argument_cap,#node argument))
                  (#arguments request)
                fun counts (limit,node) =
                  let val _ = W.spend expected 1
                      val raw = SmtReplayGraph.unfolded_nodes graph
                        SmtReplayGraph.RawNodes limit node
                      val _ = W.spend expected 1
                      val inclusive = SmtReplayGraph.unfolded_nodes graph
                        SmtReplayGraph.BinderInclusiveNodes limit node
                  in case (raw,inclusive) of (SOME a,SOME b) =>
                       if a <= limit andalso b <= limit then SOME (a,b)
                       else NONE
                   | _ => NONE end
                (* Inspect every authentic incoming node before declining. *)
                val sizes = List.map counts inventory
                fun paid [] = ()
                  | paid (SOME (raw,inclusive)::rest) =
                      (W.spend expected raw;W.spend expected inclusive;
                       paid rest)
                  | paid (NONE::_) = raise ERR "z3_local_quote"
                      "missing eligible fixed inventory"
                fun types [] = ()
                  | types (ty::rest) = (W.spend expected 1;
                      types ((if Type.is_vartype ty then [] else
                        #2 (Type.dest_type ty)) @ rest))
            in if List.all Option.isSome sizes then
                 (paid sizes;
                  types (List.map (SmtReplayGraph.type_of graph)
                    (SmtReplayGraph.block_reachable graph nodes));
                  validate_for expected receipt;true)
               else (validate_for expected receipt;false) end)
        fun quoted_local request =
          if quote_local request then local_fixed request else NONE
    in {local_law = protect quoted_local,nnf = protect nnf_fixed} end

end
