structure SmtLib_OwnedConditionalPredicate
  :> SmtLib_OwnedConditionalPredicate =
struct
  structure W=SmtReplayInvocationWork
  structure G=SmtReplayGraph
  structure P=SmtReplayProof
  structure O=SmtLib_OwnedContextImpCanon
  structure Scope=SmtReplayOwnedScopeReceipt
  val _=SmtReplayProof.prepare_source_predicate_conditional
  val _=SmtReplayConj.conj_discharge_template_data
  val ERR=Feedback.mk_HOL_ERR "SmtLib_OwnedConditionalPredicate"
  datatype plan=Plan of
    {work:W.portfolio,incoming:O.receipt_validation,index:int,
     evidence:P.source_condition_evidence,
     template:SmtReplayConj.conj_discharge_template,
     proof:Thm.thm,first:Term.term,second:Term.term,third:Term.term,
     lower:P.source_predicate_conditional_plan,used:bool ref}
  fun protect expected action=action()handle primary=>
    (W.close expected;raise primary)
  fun backing expected incoming index evidence template
      proof first second third=
    let val original=O.receipt_validation_for expected incoming
        val actual=List.nth(#entries original,index)
        val d=SmtReplayConj.conj_discharge_template_data template
        val _=if Portable.pointer_eq(actual,evidence)then ()else raise ERR
          "guard" "different authentic incoming row"
        val _=ignore(P.source_condition_statement_for expected evidence)
    in if Portable.pointer_eq(#proof d,proof)andalso
        Portable.pointer_eq(#first d,first)andalso
        Portable.pointer_eq(#second d,second)andalso
        Portable.pointer_eq(#third d,third)then ()else raise ERR
      "guard" "different actual captured conjunction law or parameters"end
  fun guard expected(Plan{work,incoming,index,evidence,template,proof,
      first,second,third,...})=
    protect expected(fn()=>
      (if Portable.pointer_eq(expected,work)then ()else raise ERR
         "guard" "foreign expected Work";
       backing expected incoming index evidence template
         proof first second third))
  fun prepare expected{incoming,index,check_type}=
    protect expected(fn()=>
      let val original=O.receipt_validation_for expected incoming
          val evidence=List.nth(#entries original,index)
          val template=SmtReplayConj.conj_discharge_template()
          val d=SmtReplayConj.conj_discharge_template_data template
          fun live()=backing expected incoming index evidence template
            (#proof d)(#first d)(#second d)(#third d)
          fun policy ty=(live();check_type ty;live())
          val lower=P.prepare_source_predicate_conditional expected
            {evidence=evidence,statement=Thm.concl(#proof d),
             first= #first d,second= #second d,third= #third d,
             check_type=policy}
          val result=Plan{work=expected,incoming=incoming,index=index,
            evidence=evidence,template=template,proof= #proof d,
            first= #first d,second= #second d,third= #third d,
            lower=lower,used=ref false}
          val _=guard expected result
      in result end)
  datatype completed=Completed of
    {work:W.portfolio,parent:plan,
     lower:P.source_predicate_conditional_completed,
     evidence:P.source_condition_evidence}
  fun execute_retained expected(value as Plan{lower,proof,used,...})=
    protect expected(fn()=>
      (guard expected value;
       if !used then raise ERR "execute" "consumed"else ();
       used:=true;
       let val ready=P.admit_source_predicate_conditional expected lower
           val _=guard expected value
           val d=P.source_predicate_conditional_import_for expected ready
           val law=case #import d of NONE=>NONE | SOME import=>
             W.with_step expected(fn()=>
               let fun guarded action=
                     (guard expected value;
                      let val answer=action()
                      in guard expected value;answer end)
                   val frame=Scope.description_for expected(#frame d)
                   val graph= #graph frame val scope= #scope frame
                   val cap= #template_limit(W.semantic_limits expected)
                   val source=guarded(fn()=>G.execute_import import)
                   val opened=guarded(fn()=>G.record_opened_view
                     graph scope cap(#node source))
                   val fact=guarded(fn()=>P.record_closed_from_import
                     graph scope{node= #node opened,theorem=proof,
                       template_limit=cap,check_type=fn _=>()})
                   val actual=guarded(fn()=>P.closed_original fact)
                   val _=if Portable.pointer_eq(actual,proof)then ()else
                     raise ERR "execute" "different exact captured proof"
               in SOME fact end)
           val _=guard expected value
           val(lower_completed,result)=
             P.execute_source_predicate_conditional_completed expected
               {ready=ready,law=law}
           val _=guard expected value
       in Completed{work=expected,parent=value,lower=lower_completed,
         evidence=result}end))
  fun execute expected value=
    let val Completed{evidence,...}=execute_retained expected value
    in evidence end
  fun completed_for expected
      (Completed{work,parent=parent as Plan{incoming,index,used,...},
        lower,evidence})=
    protect expected(fn()=>
      (if Portable.pointer_eq(expected,work)then ()else raise ERR
         "completed" "foreign expected Work";
       guard expected parent;
       if !used then ()else raise ERR "completed" "parent not consumed";
       ignore(O.receipt_context_for expected incoming);
       let val d=P.source_predicate_conditional_completed_for expected lower
           val _=if Portable.pointer_eq(#evidence d,evidence)then ()else
             raise ERR "completed" "different genuine completed result"
           val _=guard expected parent
       in {evidence=evidence,lower=lower,incoming=incoming,index=index,
         frame= #frame d}end))
end
