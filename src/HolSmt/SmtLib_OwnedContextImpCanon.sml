structure SmtLib_OwnedContextImpCanon :> SmtLib_OwnedContextImpCanon =
struct
  structure W=SmtReplayInvocationWork
  structure P=SmtReplayProof
  structure C=SmtLib_OwnedNamedContextSeeds
  structure F=SmtLib_OwnedContextFreshChoice
  structure Scope=SmtReplayOwnedScopeReceipt
  val _=SmtReplayProof.prepare_source_canonical_start
  val _=SmtLib_OwnedContextFreshChoice.prepare_canonical_universals
  val ERR=Feedback.mk_HOL_ERR "SmtLib_OwnedContextImpCanon"
  datatype owner=Owner of
    {work:W.portfolio,context:C.context_metadata,
     check_type:Type.hol_type -> unit}
  datatype selection=Selection of
    {owner:owner,candidate:C.context_candidate,ordinal:int}
  datatype receipt=Receipt of
    {selection:selection,projected:C.projected_rule,
     context:C.context_metadata,entries:P.source_condition_evidence list}
  fun protect expected operation=operation()handle primary=>
    (W.close expected;raise primary)
  fun owner_guard expected(Owner {work,context,...})=
    protect expected(fn()=>
      (if Portable.pointer_eq(expected,work)then ()else
         raise ERR "owner_guard" "foreign expected Work";
       ignore(C.context_metadata_for expected context)))
  fun selection_guard expected(Selection {owner,...})=
    owner_guard expected owner
  fun begin expected {catalogue,check_type}=
    protect expected(fn()=>
      let val context=C.prepare_context_metadata expected catalogue
          val owner=Owner {work=expected,context=context,
            check_type=check_type}
          val _=owner_guard expected owner
      in owner end)
  fun selections_for expected(owner as Owner {context,...})=
    protect expected(fn()=>
      (owner_guard expected owner;
       W.with_step expected(fn()=>
         let val d=C.context_metadata_for expected context
             fun rows [] _=[]
               | rows(candidate::rest)ordinal=
                   (owner_guard expected owner;W.spend expected 2;
                    Selection {owner=owner,candidate=candidate,
                      ordinal=ordinal}::rows rest(ordinal+1))
             val result=rows(#candidates d)0
             val _=owner_guard expected owner
         in result end)))
  fun execute expected(selection as Selection
      {owner=Owner {context,check_type,...},...})=
    protect expected(fn()=>
      (selection_guard expected selection;
       let
         val refined=C.refine_context_candidate expected context
           (case selection of Selection {candidate,...}=>candidate)
         val context= #metadata refined val projected= #rule refined
         fun live()=(selection_guard expected selection;
           ignore(C.context_metadata_for expected context);
           ignore(C.projected_rule_for expected projected))
         val data=C.projected_rule_for expected projected
         val frame= #frame data
         val scope= #scope(Scope.description_for expected frame)
         val recipe=P.execute_source_rule expected
           (P.prepare_source_rule expected
             {source= #proof data,frame=frame,caller=scope,steps=[],
              terminal=P.SourceTruth,check_type=check_type})
         val asserted=P.condition_evidence_for_rule expected recipe
         fun run plan=
           (live();let val ready=P.admit_source_canonical_plan expected plan
                       val result=P.execute_source_canonical_plan expected
                         {ready=ready,arguments=[]}
                   in live();result end)
         val first=run(P.prepare_source_canonical_start expected
           {evidence=asserted,check_type=check_type})
         fun step state operation=run(P.prepare_source_canonical_step expected
           {state=state,step=operation,check_type=check_type})
         fun future state prepare=
           (live();let val plan=prepare expected
                         {state=state,context=context,check_type=check_type}
                       val result=F.execute_canonical expected plan
                   in live();result end)
         (* Same DFS queue and reverse accumulator as IMP_CANON. No set,
            sorting or duplicate Source/case elimination enters this seam. *)
         fun queue [] finished=List.rev finished
           | queue(state::rest)finished=
             (live();case P.source_canonical_frontier_for expected state of
               P.CanonicalConjunction=>
                 let val left=step state(P.CanonicalConjunct true)
                     val right=step state(P.CanonicalConjunct false)
                 in queue(left::right::rest)finished end
             | P.CanonicalAntecedentConjunction=>
                 queue(step state P.CanonicalAntecedentConj::rest)finished
             | P.CanonicalAntecedentDisjunction=>
                 let val left=step state(P.CanonicalAntecedentDisj true)
                     val right=step state(P.CanonicalAntecedentDisj false)
                 in queue(left::right::rest)finished end
             | P.CanonicalAntecedentExistential=>
                 queue(future state F.prepare_canonical_exists::rest)finished
             | P.CanonicalCondition=>
                 queue(step state P.CanonicalUndisch::rest)finished
             | P.CanonicalImpFalse=>
                 queue(step state P.CanonicalNotIntro::rest)finished
             | P.CanonicalForall=>
                 queue(future state F.prepare_canonical_universals::rest)
                   finished
             | P.CanonicalRestrictedForall=>
                 let val plan=P.prepare_source_canonical_restricted_forall
                       expected{state=state,check_type=check_type}
                     val ready=P.admit_source_canonical_restricted_forall
                       expected plan
                     val converted=P.execute_source_canonical_restricted_forall
                       expected ready
                 in live();queue(converted::rest)finished end
             | P.CanonicalTerminal=>
                 let val closed=step state P.CanonicalFinish
                     val result=P.source_canonical_finished_for expected
                       closed
                 in queue rest(result::finished)end)
         val entries=queue[first][]
         val _=live()
       in Receipt {selection=selection,projected=projected,
         context=context,entries=entries}end))
  fun entries_for expected(Receipt
      {selection=selection as Selection {ordinal,...},projected,
       context,entries})=
    protect expected(fn()=>
      (selection_guard expected selection;
       ignore(C.context_metadata_for expected context);
       let val data=C.projected_rule_for expected projected
           val _=List.app(fn evidence=>ignore
             (P.prepare_source_condition_binder_origins expected evidence))
             entries
       in {ordinal=ordinal,assumption_slot= #assumption_slot data,
         source_occurrence= #source_occurrence data,entries=entries}end))
  (* Completed authentic origin geometry is DATA. Every access still
     checks expected owner and all actual raw/context/evidence lifetimes. *)
  datatype receipt_validation=ReceiptValidation of
    {work:W.portfolio,raw:receipt,
     origins:P.source_condition_binder_origins list}
  fun receipt_validation_for expected(ReceiptValidation
      {work,raw=Receipt{selection=selection as Selection{ordinal,...},
        projected,context,entries},origins})=
    protect expected(fn()=>
      (if Portable.pointer_eq(expected,work)then ()else
         raise ERR "receipt_validation" "foreign expected Work";
       selection_guard expected selection;
       ignore(C.context_metadata_for expected context);
       let val data=C.projected_rule_for expected projected
           val _=List.app(fn held=>ignore
             (P.source_condition_binder_origins_for expected held))origins
       in {ordinal=ordinal,assumption_slot= #assumption_slot data,
         source_occurrence= #source_occurrence data,entries=entries}end))
  fun prepare_receipt_validation expected(raw as Receipt
      {selection,projected,context,entries})=
    protect expected(fn()=>
      (selection_guard expected selection;
       ignore(C.context_metadata_for expected context);
       ignore(C.projected_rule_for expected projected);
       let val origins=List.map
             (P.prepare_source_condition_binder_origins expected)entries
           val value=ReceiptValidation
             {work=expected,raw=raw,origins=origins}
           val _=receipt_validation_for expected value
       in value end))

  fun receipt_context_for expected
      (held as ReceiptValidation {raw=Receipt {context,...},...})=
    protect expected(fn()=>
      (ignore(receipt_validation_for expected held);context))

end
