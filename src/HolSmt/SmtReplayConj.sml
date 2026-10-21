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
  val data = {proof=proof,first=first,second=second,third=third}
  val metadata = {statement=concl proof,tag=tag proof,
    bare=List.all Term.is_var [first,second,third],closed=null (hyp proof)}

  datatype conj_discharge_template = ConjDischargeTemplate
  fun conj_discharge_template () = ConjDischargeTemplate
  fun conj_discharge_template_data ConjDischargeTemplate = data
  fun conj_discharge_constructor_data ConjDischargeTemplate = metadata
end
