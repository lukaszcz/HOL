structure SmtLib_OwnedConditionQuantifierSelection
  :> SmtLib_OwnedConditionQuantifierSelection =
struct
  structure W=SmtReplayInvocationWork
  structure P=SmtReplayProof
  structure C=SmtLib_OwnedNamedContextSeeds
  structure O=SmtLib_OwnedContextImpCanon
  structure Conditional=SmtLib_OwnedConditionalPredicate
  structure Scope=SmtReplayOwnedScopeReceipt
  structure G=SmtReplayGraph
  val _=SmtReplayProof.prepare_source_conditional_post_metadata
  val _=SmtLib_OwnedConditionalPredicate.completed_for
  val ERR=Feedback.mk_HOL_ERR "SmtLib_OwnedConditionQuantifierSelection"
  datatype decision=Identity | Singleton of Term.term | NotCovered of string
  datatype selection=Selection of
    {work:W.portfolio,completed:Conditional.completed,
     metadata:P.source_conditional_post_metadata,
     slices:C.context_origin_metadata list,
     evidence:P.source_condition_evidence,
     selected:Term.term list,decision:decision,
     condition_variables:Term.term list,equation_variables:Term.term list,
     hypothesis_variables:Term.term list,unknown:G.node list}
  fun protect expected action=action()handle primary=>
    (W.close expected;raise primary)
  fun live expected completed metadata slices=
    (ignore(Conditional.completed_for expected completed);
     ignore(P.source_conditional_post_metadata_for expected metadata);
     List.app(fn slice=>ignore(C.context_origin_metadata_for
       expected slice))slices)
  fun selection_for expected
      (Selection{work,completed,metadata,slices,evidence,selected,decision,
        condition_variables,equation_variables,hypothesis_variables,unknown})=
    protect expected(fn()=>
      (if Portable.pointer_eq(expected,work)then ()else raise ERR
         "selection" "foreign expected Work";
       live expected completed metadata slices;
       {evidence=evidence,selected=selected,decision=decision,
        condition_variables=condition_variables,
        equation_variables=equation_variables,
        hypothesis_variables=hypothesis_variables,unknown=unknown}))
  fun prepare expected{completed,check_type}=
    protect expected(fn()=>
      let val cd=Conditional.completed_for expected completed
          val metadata=P.prepare_source_conditional_post_metadata
            expected(#lower cd)
          val d=P.source_conditional_post_metadata_for expected metadata
          val context=O.receipt_context_for expected(#incoming cd)
          val original=C.context_metadata_for expected context
          val current=Scope.description_for expected(#frame cd)
          val old=Scope.description_for expected(#frame original)
          val _=if Portable.pointer_eq(#graph current,#graph old)then ()else
            raise ERR "selection" "foreign authentic context graph"
          (* Each genuine C resolver owns its action. No nested action in
             the later paid set union or any action-free result getter. *)
          val slices=case #reason d of SOME _=>[] | NONE=>
            List.map(fn node=>
              (ignore(Conditional.completed_for expected completed);
               C.prepare_context_origin_metadata expected context node))
              (#unknown d)
          fun guard()=live expected completed metadata slices
          val (hypothesis_variables,unknown,selected,decision)=
            W.with_step expected(fn()=>
            let fun tick n=(guard();W.spend expected n)
                val _=tick 2
                val resolved_types=ref([]:Type.hol_type list)
                fun profile retain ty=
                  let fun pending []=()
                        | pending([]::rest)=pending rest
                        | pending((ty::args)::rest)=
                            (tick 12;
                             if retain then(tick 4;
                               resolved_types:=ty:: !resolved_types)else ();
                             if Type.is_vartype ty then
                               (tick(String.size(Type.dest_vartype ty)+1);
                                pending(args::rest))
                             else let val{Thy,Tyop,Args}=Type.dest_thy_type ty
                                      val _=tick(String.size Thy+
                                        String.size Tyop+2)
                                  in pending(Args::args::rest)end)
                  in pending[[ty]]end
                fun actual retain term=
                  (tick 4;if Term.is_var term andalso
                      Term.uptodate_term term then ()else raise ERR
                     "selection" "metadata is not an actual typed VARIABLE";
                   profile retain(Term.type_of term);
                   tick(String.size(#1(Term.dest_var term))+1))
                fun equal a b=
                  (actual false a;actual false b;tick 4;Term.term_eq a b)
                fun insert(term,values)=
                  if List.exists(fn held=>equal term held)values then values
                  else(tick 2;term::values)
                fun resolve(slice,(variables,unknown))=
                  let val od=C.context_origin_metadata_for expected slice
                  in case #variables od of
                    SOME values=>(List.foldl(fn(value,all)=>
                      (actual true value;insert(value,all)))variables values,
                      unknown)
                  | NONE=>(variables,#origin od::unknown)end
                val (variables,unknown)=List.foldl resolve
                  (#hypothesis_variables d,[])slices
                fun member term values=List.exists(fn held=>
                  equal term held)values
                val candidates=List.filter(fn term=>
                  not(member term(#equation_variables d)))
                  (#condition_variables d)
                val eligible=List.filter(fn term=>not(member term variables))
                  candidates
                fun compare(a,b)=
                  (actual false a;actual false b;tick 4;Term.compare(a,b))
                fun sorted term []=(tick 2;[term])
                  | sorted term(head::tail)=case compare(term,head)of
                      LESS=>(tick 3;term::head::tail)
                    | EQUAL=>head::tail
                    | GREATER=>(tick 2;head::sorted term tail)
                val selected=List.foldl
                  (fn(term,all)=>sorted term all)[]eligible
                val decision=case #reason d of SOME why=>NotCovered why
                  | NONE=>if not(null unknown)then NotCovered
                      "post-DISCH Original Hyp FV is unresolved"
                    else case selected of []=>Identity
                      | [variable]=>
                          if member variable(#native_hypothesis_variables d)
                            then NotCovered "affected native Hyp needs closure"
                          else if Lib.can Type.dom_rng(Term.type_of variable)
                            then NotCovered
                                "function-valued singleton is not covered"
                          else Singleton variable
                      | _=>NotCovered
                          "multiple selected variables need right fold"
                (* Policies see only a completed metadata portfolio. Every
                   callback has SAME completed O/Scope backing fences. *)
                fun reverse values result=
                  (tick 1;case values of []=>result
                   | ty::rest=>(tick 3;reverse rest(ty::result)))
                fun policy ty=(guard();check_type ty;guard())
                val _=case decision of NotCovered _=>() | _=>
                  let val types=reverse(!resolved_types)[]
                  in List.app policy(#types d);List.app policy types end
                val _=guard()
            in(variables,List.rev unknown,selected,decision)end)
          val result=Selection{work=expected,completed=completed,
            metadata=metadata,slices=slices,evidence= #evidence cd,
            selected=selected,decision=decision,
            condition_variables= #condition_variables d,
            equation_variables= #equation_variables d,
            hypothesis_variables=hypothesis_variables,unknown=unknown}
          val _=ignore(selection_for expected result)
      in result end)
end
