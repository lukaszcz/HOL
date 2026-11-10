structure SmtLib_OwnedPairedEqTFlip :> SmtLib_OwnedPairedEqTFlip =
struct
  structure W=SmtReplayInvocationWork
  structure P=SmtReplayProof
  structure O=SmtLib_OwnedContextImpCanon
  val _=SmtReplayProof.prepare_source_eqt_flip
  val _=Cond_rewr.eq_sym_template_data
  val ERR=Feedback.mk_HOL_ERR "SmtLib_OwnedPairedEqTFlip"
  datatype plan=Plan of
    {work:W.portfolio,incoming:O.receipt_validation,index:int,
     evidence:P.source_condition_evidence,template:Cond_rewr.eq_sym_template,
     lower:P.source_eqt_flip_plan,used:bool ref}
  fun protect expected operation=operation()handle primary=>
    (W.close expected;raise primary)
  fun fixed template=
    let val d=Cond_rewr.eq_sym_template_data template
    in if Portable.pointer_eq(#proof d,boolTheory.EQ_SYM_EQ)andalso
        Portable.pointer_eq(#statement d,Thm.concl(#proof d))then ()else
      raise ERR "fixed" "namespace is not the exact fixed law"end
  fun backing expected incoming index evidence template=
    (let val d=O.receipt_validation_for expected incoming
           val actual=List.nth(#entries d,index)
       in if Portable.pointer_eq(actual,evidence)then ()else raise ERR
         "guard" "different authentic incoming row"end;
       ignore(P.source_condition_statement_for expected evidence);
       fixed template)
  fun guard expected(Plan{work,incoming,index,evidence,template,...})=
    protect expected(fn()=>
      (if Portable.pointer_eq(expected,work)then ()else raise ERR
         "guard" "foreign expected Work";
       backing expected incoming index evidence template))
  fun prepare expected{incoming,index,check_type}=
    protect expected(fn()=>
      let val d=O.receipt_validation_for expected incoming
          val evidence=List.nth(#entries d,index)
          val template=Cond_rewr.eq_sym_template()
          val _=fixed template
          fun live()=backing expected incoming index evidence template
          fun policy ty=(live();check_type ty;live())
          val lower=P.prepare_source_eqt_flip expected
            {evidence=evidence,check_type=policy}
          val result=Plan{work=expected,incoming=incoming,index=index,
            evidence=evidence,template=template,lower=lower,used=ref false}
          val _=guard expected result
      in result end)
  fun execute expected(value as Plan{lower,used,...})=
    protect expected(fn()=>
      (guard expected value;
       if !used then raise ERR "execute" "consumed"else ();
       used:=true;
       let val ready=P.admit_source_eqt_flip expected lower
           val _=guard expected value
           val result=P.execute_source_eqt_flip expected ready
           val _=guard expected value
       in result end))
end
