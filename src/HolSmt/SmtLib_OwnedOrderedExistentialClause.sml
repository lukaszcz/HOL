(* An ordered selected-clause antecedent operation, not full context SIMPLE. *)
structure SmtLib_OwnedOrderedExistentialClause :>
    SmtLib_OwnedOrderedExistentialClause =
struct
  structure W=SmtReplayInvocationWork
  structure P=SmtReplayProof
  structure C=SmtLib_OwnedNamedContextSeeds
  structure F=SmtLib_OwnedContextFreshChoice
  structure Scope=SmtReplayOwnedScopeReceipt
  val _=SmtLib_OwnedContextFreshChoice.prepare_antecedent
  val ERR=Feedback.mk_HOL_ERR "SmtLib_OwnedOrderedExistentialClause"
  datatype owner=Owner of
    {work:W.portfolio,catalogue:C.catalogue,context:C.context_metadata,
     check_type:Type.hol_type -> unit}
  datatype selection=Selection of
    {owner:owner,candidate:C.context_candidate,ordinal:int}
  datatype plan=Plan of
    {selection:selection,projected:C.projected_rule,
     context:C.context_metadata,choice:F.choice,
     antecedent:F.antecedent_plan,available:bool ref}
  datatype receipt=Receipt of
    {selection:selection,projected:C.projected_rule,
     context:C.context_metadata,choice:F.choice,
     evidence:P.source_condition_evidence}
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
          val owner=Owner {work=expected,catalogue=catalogue,
            context=context,check_type=check_type}
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
  fun backing_guard expected selection projected context choice=
    protect expected(fn()=>
      (selection_guard expected selection;
       ignore(C.projected_rule_for expected projected);
       ignore(C.context_metadata_for expected context);
       ignore(F.describe_for expected choice)))
  (* This inspection only selects a supported actual grammar. It grants
     no freshness, Source, variable, theorem, or primitive allowance. *)
  fun linear_frontier expected selection evidence=
    let val origins=P.prepare_source_condition_binder_origins expected
          evidence
        fun live()=(selection_guard expected selection;
          ignore(P.source_condition_binder_origins_for expected origins))
    in W.with_step expected(fn()=>
      let
        fun tick n=(live();W.spend expected n)
        fun guarded operation=
          (tick 1;let val value=operation()in tick 1;value end)
        fun is_false term=Term.is_const term andalso
          Term.same_const term boolSyntax.F
        fun positive_atom term=
          not(boolSyntax.is_imp_only term orelse boolSyntax.is_conj term
            orelse boolSyntax.is_disj term orelse boolSyntax.is_forall term
            orelse boolSyntax.is_exists term orelse boolSyntax.is_neg term
            orelse boolSyntax.is_res_forall term
            orelse boolSyntax.is_eq term orelse is_false term orelse
            (Term.is_const term andalso Term.same_const term boolSyntax.T))
        fun frontier term=
          (tick 1;
           if not(boolSyntax.is_imp_only term)then raise ERR "frontier"
             "actual implication spine has no existential antecedent"
           else let val(ant,body)=guarded(fn()=>
                      boolSyntax.dest_imp_only term)
             in if boolSyntax.is_conj ant orelse boolSyntax.is_disj ant then
                  raise ERR "frontier"
                    "stock ordered branching continuation is required"
                else if boolSyntax.is_exists ant then
                  if positive_atom body then ()else raise ERR "frontier"
                    "stock consequent continuation is required"
                else if is_false body then raise ERR "frontier"
                  "stock NOT_INTRO continuation is required"
                else frontier body end)
        val data=P.source_condition_binder_origins_for expected origins
        val(lhs,rhs)=guarded(fn()=>boolSyntax.dest_eq(#statement data))
        val _=if Term.is_const rhs andalso
            Term.same_const rhs boolSyntax.T then ()else
          raise ERR "frontier" "actual assertion equality is required"
        val _=frontier lhs
        val _=live()
      in ()end)end
  fun prepare expected
      (selection as Selection {owner=owner as Owner
        {context,check_type,...},candidate,...})=
    protect expected(fn()=>
      (selection_guard expected selection;
       let
         val refined=C.refine_context_candidate expected context candidate
         val projected= #rule refined val context= #metadata refined
         val data=C.projected_rule_for expected projected
         val frame= #frame data
         val scope= #scope(Scope.description_for expected frame)
         val recipe=P.execute_source_rule expected
           (P.prepare_source_rule expected
             {source= #proof data,frame=frame,caller=scope,steps=[],
              terminal=P.SourceTruth,check_type=check_type})
         val evidence=P.condition_evidence_for_rule expected recipe
         val _=linear_frontier expected selection evidence
         val choice=F.prepare_existential expected
           {evidence=evidence,context=context}
         val antecedent=F.prepare_antecedent expected choice
           {check_type=check_type}
         val result=Plan {selection=selection,projected=projected,
           context=context,choice=choice,antecedent=antecedent,
           available=ref true}
         val _=backing_guard expected selection projected context choice
       in result end))
  fun execute expected(Plan
      {selection,projected,context,choice,antecedent,available})=
    protect expected(fn()=>
      (selection_guard expected selection;
       if !available then ()else raise ERR "execute" "consumed plan";
       backing_guard expected selection projected context choice;
       available:=false;
       let val evidence=F.execute_antecedent expected antecedent
           val _=backing_guard expected selection projected context choice
           val result=Receipt {selection=selection,projected=projected,
             context=context,choice=choice,evidence=evidence}
       in result end))
  fun evidence_for expected(Receipt
      {selection=selection as Selection {ordinal,...},projected,
       context,choice,evidence})=
    protect expected(fn()=>
      (backing_guard expected selection projected context choice;
       let val data=C.projected_rule_for expected projected
           val origins=P.prepare_source_condition_binder_origins expected
             evidence
           val _=ignore(P.source_condition_binder_origins_for expected
             origins)
           val _=backing_guard expected selection projected context choice
       in {frame= #frame data,ordinal=ordinal,
         assumption_slot= #assumption_slot data,
         source_occurrence= #source_occurrence data,evidence=evidence}end))
end
