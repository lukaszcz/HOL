(* Copyright (c) 2026 The HOL4 contributors. *)
structure SmtReplayNativeContract :> SmtReplayNativeContract =
struct
  structure G = SmtReplayGraph
  structure S = SmtReplaySource
  structure W = SmtReplayInvocationWork
  val ERR = Feedback.mk_HOL_ERR "SmtReplayNativeContract"
  type limits =
    {semantic_limits:W.limits,import_limit:int,type_work_limit:int}
  datatype contract = Contract of
    {work:W.portfolio,graph:G.graph,root:G.scope,sources:S.sources,
     limits:limits,epoch:int,symbols:int}

  (* This retains the caller's existing finite native/opening/Type limits.
     It creates no allowance, receipt credit, or native admission. Every
     consumer must still measure its actual operands before constructors. *)
  fun capture work (limits as {semantic_limits,import_limit,type_work_limit}
      :limits) =
    ((W.with_step work (fn () =>
      let
        val sources = W.original_sources work
        val graph = S.owning_graph sources
        val root = S.owning_scope sources
        val policy = W.semantic_policy work
        val _ = W.validate_policy work graph root sources policy
        val _ = if #input_limit semantic_limits>0 andalso
            #output_limit semantic_limits>0 andalso
            #template_limit semantic_limits>0 andalso import_limit>0 andalso
            type_work_limit>0 then () else
          raise ERR "capture" "nonpositive native caller contract"
        val result = Contract
          {work=work,graph=graph,root=root,sources=sources,limits=limits,
           epoch=Type.type_epoch (),symbols=Term.term_epoch ()}
        val _ = W.validate_policy work graph root sources policy
      in result end))
     handle primary => (W.close work;raise primary))

  fun for_work expected (saved as Contract {work,...}) =
    ((if Portable.pointer_eq (expected,work) then () else
        raise ERR "for_work" "different original native-contract Work";
      let
        val Contract {graph,root,sources,limits,epoch,symbols,...} = saved
        val policy = W.semantic_policy expected
        val _ = W.validate_policy expected graph root sources policy
        val _ = if Type.type_epoch ()=epoch andalso
            Term.term_epoch ()=symbols then () else
          raise ERR "for_work" "native caller contract retired"
      in limits end)
     handle primary => (W.close expected;raise primary))

  fun validate_for expected saved = ignore (for_work expected saved)
end
