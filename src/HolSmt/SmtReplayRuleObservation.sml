structure SmtReplayRuleObservation :> SmtReplayRuleObservation =
struct
  type statistics =
    {selected_returns:IntInf.int,
     theorem_operand_edges:IntInf.int,
     zero_premise_returns:IntInf.int,
     one_premise_returns:IntInf.int,
     two_premise_returns:IntInf.int,
     three_premise_returns:IntInf.int}
  type meter =
    {selected_returns:IntInf.int ref,
     theorem_operand_edges:IntInf.int ref,
     spec_returns:IntInf.int ref,
     zero_premise_returns:IntInf.int ref,
     one_premise_returns:IntInf.int ref,
     two_premise_returns:IntInf.int ref,
     three_premise_returns:IntInf.int ref}
  val meter : meter option ref = ref NONE
  fun observe action =
    let val _ = case !meter of NONE => () | SOME _ =>
          raise Feedback.mk_HOL_ERR "SmtReplayRuleObservation"
            "with_statistics" "observation reentry"
        val fields : meter =
          {selected_returns=ref 0,
           theorem_operand_edges=ref 0,
           spec_returns=ref 0,
           zero_premise_returns=ref 0,
           one_premise_returns=ref 0,
           two_premise_returns=ref 0,
           three_premise_returns=ref 0}
        val _ = meter := SOME fields
        val outcome = Exn.capture action ()
        val _ = meter := NONE
        val counts : statistics =
          {selected_returns= !(#selected_returns fields),
           theorem_operand_edges= !(#theorem_operand_edges fields),
           zero_premise_returns= !(#zero_premise_returns fields),
           one_premise_returns= !(#one_premise_returns fields),
           two_premise_returns= !(#two_premise_returns fields),
           three_premise_returns= !(#three_premise_returns fields)}
    in (Exn.release outcome,counts, !(#spec_returns fields)) end
  fun with_statistics action =
    let val (result,counts,_) = observe action in (result,counts) end
  fun with_spec_statistics action =
    let val (result,_,spec) = observe action in (result,spec) end
  (* This helper is private. Public typed wrappers select their OWN actual
     theorem-argument arity, after the unchanged rule returns successfully.
     Repeated theorem arguments are repeated edges, not distinct identities. *)
  fun returned edges proof =
    (case !meter of NONE => () | SOME fields =>
       let val arity = case edges of
             0 => #zero_premise_returns fields
           | 1 => #one_premise_returns fields
           | 2 => #two_premise_returns fields
           | _ => #three_premise_returns fields
       in #selected_returns fields := !(#selected_returns fields)+1;
          #theorem_operand_edges fields :=
            !(#theorem_operand_edges fields)+edges;
          arity := !arity+1
       end;proof)
  fun ASSUME a = returned 0 (Thm.ASSUME a)
  fun REFL a = returned 0 (Thm.REFL a)
  fun ALPHA a b = returned 0 (Thm.ALPHA a b)
  fun SYM a = returned 1 (Thm.SYM a)
  fun TRANS a b = returned 2 (Thm.TRANS a b)
  fun EQ_MP a b = returned 2 (Thm.EQ_MP a b)
  fun MP a b = returned 2 (Thm.MP a b)
  fun DISCH a b = returned 1 (Thm.DISCH a b)
  fun SPEC a b =
    let val proof = Thm.SPEC a b in
      case !meter of NONE => proof
      | SOME fields =>
          (#spec_returns fields := !(#spec_returns fields) + 1;
           returned 1 proof)
    end
  fun AP_TERM a b = returned 1 (Thm.AP_TERM a b)
  fun AP_THM a b = returned 1 (Thm.AP_THM a b)
  fun MK_COMB pair = returned 2 (Thm.MK_COMB pair)
  fun CONJ a b = returned 2 (Thm.CONJ a b)
  fun CONJUNCT1 a = returned 1 (Thm.CONJUNCT1 a)
  fun CONJUNCT2 a = returned 1 (Thm.CONJUNCT2 a)
  fun DISJ1 a b = returned 1 (Thm.DISJ1 a b)
  fun DISJ2 a b = returned 1 (Thm.DISJ2 a b)
  fun DISJ_CASES a b c = returned 3 (Thm.DISJ_CASES a b c)
  fun NOT_ELIM a = returned 1 (Thm.NOT_ELIM a)
  fun CCONTR a b = returned 1 (Thm.CCONTR a b)
  fun D_CONTR a b = returned 1 (Drule.CONTR a b)
  fun D_EQF_ELIM a = returned 1 (Drule.EQF_ELIM a)
  fun D_PROVE_HYP a b = returned 2 (Drule.PROVE_HYP a b)
  fun D_SPECL a b = returned 1 (Drule.SPECL a b)
  fun SUBST_LITERAL variable equality template proof = returned 2
    (Thm.SUBST[{redex=variable,residue=equality}]template proof)
  fun INST a b = returned 1 (SmtReplayInstanceObservation.inst a b)
  fun INST_TYPE a b = returned 1 (SmtReplayInstanceObservation.inst_type a b)
  fun inst_ty_term (terms,types) proof =
    INST terms (INST_TYPE types proof)
end
