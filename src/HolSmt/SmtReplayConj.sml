structure SmtReplayConj :> SmtReplayConj =
struct
  open HolKernel boolTheory boolSyntax Drule

  (* Constructed only when this HolSmt module loads. Ordinary Cond_rewr
     initialization and theory loading neither build nor retain this law.
     SmtReplayProof checks its bounded schema and current declarations;
     these projections convey no Source admission or Work credit. *)
  val (first,second,third) =
    triple_of_list (fst (strip_forall (concl AND_IMP_INTRO)))
  val proof = fst (EQ_IMP_RULE (SPEC_ALL AND_IMP_INTRO))
  (* Never updated or exported. Reread the actual producer through a cell:
     heap sharing can redirect a theorem's immutable conclusion field while
     a separately compiled constant still retains the old occurrence.
     A cached conclusion constant is therefore not a current projection of
     the exact theorem. Keep every caller's original pointer checks. *)
  val producer = ref {proof=proof,first=first,second=second,third=third,
    bare=List.all Term.is_var [first,second,third],closed=null (hyp proof)}

  datatype conj_discharge_template = ConjDischargeTemplate
  fun conj_discharge_template () = ConjDischargeTemplate
  fun conj_discharge_template_data ConjDischargeTemplate =
    let val {proof,first,second,third,...} = !producer
    in {proof=proof,first=first,second=second,third=third} end
  fun conj_discharge_constructor_data ConjDischargeTemplate =
    let val {proof,bare,closed,...} = !producer
    in {statement=concl proof,tag=tag proof,bare=bare,closed=closed} end

  datatype false_template_kind = FalseConclusion | TruthEqualsFalse
    | FalseEqualsTruth
  datatype false_template = FalseTemplate of false_template_kind
  local
    fun stock tm = fst (hd (Cond_rewr.IMP_EQ_CANON
      (ASSUME tm,BoundedRewrites.UNBOUNDED)))
    (* [F] |- x = F, discharged to Cond_rewr's x_eq_false statement *)
    val x_eq_false = DISCH F (stock F)
    val tf_eq_f = stock (mk_eq (T,F))
    val ft_eq_f = stock (mk_eq (F,T))
    fun hyp_law th = {proof=th,condition=hd (hyp th),result=concl th}
  in
    fun false_template kind = FalseTemplate kind
    fun false_template_data (FalseTemplate FalseConclusion) =
        let val (condition,result) = dest_imp_only (concl x_eq_false)
        in {proof=x_eq_false,condition=condition,result=result} end
      | false_template_data (FalseTemplate TruthEqualsFalse) = hyp_law tf_eq_f
      | false_template_data (FalseTemplate FalseEqualsTruth) = hyp_law ft_eq_f
  end

  datatype eq_sym_template = EqSymTemplate
  fun eq_sym_template () = EqSymTemplate
  fun eq_sym_template_data EqSymTemplate =
    {proof=EQ_SYM_EQ,statement=concl EQ_SYM_EQ}
end
