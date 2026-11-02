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
end
