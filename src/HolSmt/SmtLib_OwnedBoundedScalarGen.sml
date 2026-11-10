structure SmtLib_OwnedBoundedScalarGen :> SmtLib_OwnedBoundedScalarGen =
struct
  structure W=SmtReplayInvocationWork
  structure P=SmtReplayProof
  structure Conditional=SmtLib_OwnedConditionalPredicate
  structure Q=SmtLib_OwnedConditionQuantifierSelection
  val _=SmtReplayProof.prepare_source_bounded_scalar_gen
  val _=SmtLib_OwnedConditionQuantifierSelection.prepare
  val ERR=Feedback.mk_HOL_ERR "SmtLib_OwnedBoundedScalarGen"
  datatype plan=Plan of {work:W.portfolio,completed:Conditional.completed,
    selection:Q.selection,lower:P.source_bounded_scalar_gen_plan}
  datatype result=Result of
    {plan:plan,lower:P.source_bounded_scalar_gen_result}
  fun protect expected action=action()handle primary=>
    (W.close expected;raise primary)
  fun backing expected(Plan{work,completed,selection,...})=
    (if Portable.pointer_eq(expected,work)then ()else raise ERR
       "guard" "foreign expected Work";
     let val cd=Conditional.completed_for expected completed
         val qd=Q.selection_for expected selection
     in if Portable.pointer_eq(#evidence cd,#evidence qd)then ()else
       raise ERR "guard" "different authentic selected evidence"end)
  fun plan_for expected(value as Plan{lower,selection,...})=
    protect expected(fn()=>
      (backing expected value;
       let val d=P.source_bounded_scalar_gen_plan_for expected lower
           val q=Q.selection_for expected selection
           val selected=case #decision q of Q.Singleton term=>term
             | _=>raise ERR "guard" "genuine Q singleton is required"
           val _=if Term.term_eq selected(#variable d)then ()else raise ERR
             "guard" "Q singleton differs from privately derived variable"
           val _=backing expected value
       in d end))
  fun prepare expected completed=
    protect expected(fn()=>
      let val cd=Conditional.completed_for expected completed
          (* Q retains its genuine O/C resolvers. No external policy runs
             until the low prepare finishes its entire Type portfolio. *)
          val selection=Q.prepare expected
            {completed=completed,check_type=fn _=>()}
          val q=Q.selection_for expected selection
          val _=case #decision q of Q.Singleton _=>() | _=>raise ERR
            "prepare" "genuine Q singleton is required"
          val lower=P.prepare_source_bounded_scalar_gen expected(#lower cd)
          val value=Plan{work=expected,completed=completed,
            selection=selection,lower=lower}
          val _=ignore(plan_for expected value)
      in value end)
  fun admit expected{plan=plan as Plan{lower,...},check_type}=
    protect expected(fn()=>
      let val _=ignore(plan_for expected plan)
          fun policy ty=
            (ignore(plan_for expected plan);check_type ty;
             ignore(plan_for expected plan))
          val _=P.admit_source_bounded_scalar_gen expected
            {plan=lower,check_type=policy}
          val _=ignore(plan_for expected plan)
      in ()end)
  fun execute expected(plan as Plan{lower,...})=
    protect expected(fn()=>
      let val _=ignore(plan_for expected plan)
          val result=P.execute_source_bounded_scalar_gen expected lower
          val _=backing expected plan
      in Result{plan=plan,lower=result}end)
  fun result_for expected(Result{plan,lower})=
    protect expected(fn()=>
      (backing expected plan;
       let val d=P.source_bounded_scalar_gen_result_for expected lower
           val _=backing expected plan
       in d end))
end
