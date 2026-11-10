structure SmtLib_OwnedIncomingHypFV :> SmtLib_OwnedIncomingHypFV =
struct
  structure W=SmtReplayInvocationWork
  structure P=SmtReplayProof
  structure C=SmtLib_OwnedNamedContextSeeds
  structure O=SmtLib_OwnedContextImpCanon
  structure G=SmtReplayGraph
  structure Scope=SmtReplayOwnedScopeReceipt
  val _=SmtReplayProof.prepare_source_condition_hyp_fv_origins
  val _=SmtLib_OwnedContextImpCanon.receipt_context_for
  val ERR=Feedback.mk_HOL_ERR "SmtLib_OwnedIncomingHypFV"
  datatype row=Row of
    {evidence:P.source_condition_evidence,
     origins:P.source_hyp_fv_origins,
     slices:C.context_origin_metadata list,
     variables:Term.term list,unknown:G.node list}
  datatype receipt=Receipt of
    {work:W.portfolio,validation:O.receipt_validation,rows:row list}
  fun protect expected operation=operation()handle primary=>
    (W.close expected;raise primary)
  fun check expected work validation=
    (if Portable.pointer_eq(expected,work)then ()else
       raise ERR "incoming_hyp_fv" "foreign expected Work";
     ignore(O.receipt_validation_for expected validation);
     ignore(O.receipt_context_for expected validation))
  fun entries_for expected(Receipt {work,validation,rows})=
    protect expected(fn()=>
      (check expected work validation;
       let val d=O.receipt_validation_for expected validation
           fun view(Row {evidence,origins,slices,variables,unknown})=
             let val hd=P.source_condition_hyp_fv_origins_for
                   expected origins
                 val _=List.app(fn held=>ignore
                   (C.context_origin_metadata_for expected held))slices
             in {evidence=evidence,frame= #frame hd,
               statement= #statement hd,variables=variables,
               unknown=unknown}end
           val result=List.map view rows
           val _=check expected work validation
       in {ordinal= #ordinal d,assumption_slot= #assumption_slot d,
         source_occurrence= #source_occurrence d,entries=result}end))
  fun prepare expected validation=
    protect expected(fn()=>
      let val d=O.receipt_validation_for expected validation
          val context=O.receipt_context_for expected validation
          fun guard()=
            (ignore(O.receipt_validation_for expected validation);
             ignore(O.receipt_context_for expected validation))
          fun row evidence=
            let val _=guard()
                (* Exactly this privately retained incoming evidence. No
                   UND or caller-supplied condition list is introduced. *)
                val origins=P.prepare_source_condition_hyp_fv_origins
                  expected evidence
                val hd=P.source_condition_hyp_fv_origins_for
                  expected origins
                val cd=C.context_metadata_for expected context
                val hg= #graph(Scope.description_for expected(#frame hd))
                val cg= #graph(Scope.description_for expected(#frame cd))
                val _=if Portable.pointer_eq(hg,cg)then ()else raise ERR
                  "incoming_hyp_fv" "foreign genuine context graph"
                (* Each resolver owns its own Work action. Do not nest
                   C preparation inside the later inventory union action. *)
                val slices=List.map(fn node=>
                  (guard();C.prepare_context_origin_metadata
                    expected context node))(#unknown hd)
                fun live()=
                  (guard();ignore(P.source_condition_hyp_fv_origins_for
                     expected origins);
                   List.app(fn held=>ignore
                     (C.context_origin_metadata_for expected held))slices)
                val (variables,unknown)=W.with_step expected(fn()=>
                  let fun tick n=(live();W.spend expected n)
                      fun insert(value,known)=
                        (tick 1;
                         if Term.is_var value andalso
                             Term.uptodate_term value then ()else raise ERR
                           "incoming_hyp_fv" "non-variable origin metadata";
                         if List.exists(fn old=>
                             (tick 1;Term.term_eq old value))known
                         then known else value::known)
                      fun resolve(held,(known,unknown))=
                        let val od=C.context_origin_metadata_for
                              expected held
                        in case #variables od of
                          SOME values=>(List.foldl insert known values,
                            unknown)
                        | NONE=>(known,#origin od::unknown)end
                      val result=List.foldl resolve
                        (#variables hd,[])slices
                      val _=live()
                  in (#1 result,List.rev(#2 result))end)
                val _=live()
            in Row {evidence=evidence,origins=origins,slices=slices,
              variables=variables,unknown=unknown}end
          val rows=List.map row(#entries d)
          val result=Receipt {work=expected,validation=validation,rows=rows}
          val _=ignore(entries_for expected result)
      in result end)
end
