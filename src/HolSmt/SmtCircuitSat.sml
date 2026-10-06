(* Checked SAT for already-clausified Boolean circuit definitions. *)

structure SmtCircuitSat =
struct
  open HolKernel

  val ERR = Feedback.mk_HOL_ERR "SmtCircuitSat"

  val atom_cnf = Library.prove
    (``(p : bool) = q <=> (p \/ ~q) /\ (~p \/ q)``,
     tautLib.TAUT_TAC)
  val true_cnf = Library.prove
    (``((p : bool) = T) <=> p``, tautLib.TAUT_TAC)
  val false_cnf = Library.prove
    (``((p : bool) = F) <=> ~p``, tautLib.TAUT_TAC)

  (* Each result is a kernel theorem equating a gate definition with its
     CNF clauses.  Non-connective right sides remain propositional atoms. *)
  fun definition_cnf definition =
    let
      val (_, body) = boolSyntax.dest_eq definition
      val _ = Term.type_of body = Type.bool orelse
        raise ERR "definition_cnf" "gate definition is not Boolean"
      val law =
        if boolSyntax.is_neg body then satTheory.dc_neg
        else if boolSyntax.is_conj body then satTheory.dc_conj
        else if boolSyntax.is_disj body then satTheory.dc_disj
        else if boolSyntax.is_imp body then satTheory.dc_imp
        else if boolSyntax.is_eq body andalso
                Term.type_of (boolSyntax.lhs body) = Type.bool then
          satTheory.dc_eq
        else if boolSyntax.is_cond body then satTheory.dc_cond
        else if Term.aconv body boolSyntax.T then true_cnf
        else if Term.aconv body boolSyntax.F then false_cnf
        else atom_cnf
    in
      Drule.INST_TY_TERM
        (Term.match_term (boolSyntax.lhs (Thm.concl law)) definition) law
    end

  (* Balanced proof trees avoid a linear-depth conjunction spine during
     congruence and subsequent instantiation of large definition graphs. *)
  fun balanced_equivalences [] = Thm.REFL boolSyntax.T
    | balanced_equivalences [theorem] = theorem
    | balanced_equivalences theorems =
        let
          val half = List.length theorems div 2
          val conjunction = Term.rator (Term.rator
            (boolSyntax.mk_conj (boolSyntax.T, boolSyntax.T)))
          val left = balanced_equivalences (List.take (theorems, half))
          val right = balanced_equivalences (List.drop (theorems, half))
        in
          Thm.MK_COMB (Thm.MK_COMB (Thm.REFL conjunction, left), right)
        end

  fun balanced_conjunction [] = boolTheory.TRUTH
    | balanced_conjunction [theorem] = theorem
    | balanced_conjunction theorems =
        let val half = List.length theorems div 2 in
          Thm.CONJ
            (balanced_conjunction (List.take (theorems, half)))
            (balanced_conjunction (List.drop (theorems, half)))
        end

  (* Prove [cnf ==> output] without asking HolSat to re-clausify the graph.
     SAT means this abstraction cannot discharge the obligation; no model
     theorem is required.  Every UNSAT certificate is replayed in HOL. *)
  fun prove_cnf (cnf, output) =
    let
      val denied = boolSyntax.mk_neg output
      fun flatten pending accumulated =
        case pending of
          [] => List.rev accumulated
        | theorem :: rest =>
            (case Lib.total boolSyntax.dest_conj (Thm.concl theorem) of
               SOME _ => flatten
                 (Thm.CONJUNCT1 theorem :: Thm.CONJUNCT2 theorem :: rest)
                 accumulated
             | NONE => flatten rest (theorem :: accumulated))
      val clauses = flatten [Thm.ASSUME cnf] []
      (* DIMACS abstracts T and F as atoms.  Supply their checked values. *)
      val constants =
        [boolTheory.TRUTH, Drule.EQF_ELIM (Thm.REFL boolSyntax.F)]
      val refutation_proof = List.foldr
        (fn (clause, rest) => Thm.CONJ clause rest)
        (Thm.ASSUME denied) (clauses @ constants)
      val refutation = Thm.concl refutation_proof
      val no_refutation = HolSatLib.GEN_SAT_PROVE_ONLY
        (satConfig.set_flag_is_cnf true
          (satConfig.set_term refutation satConfig.base_config))
      val _ = List.null (Thm.hyp no_refutation) andalso
        Term.aconv (Thm.concl no_refutation)
          (boolSyntax.mk_neg refutation) orelse
        raise ERR "prove_cnf" "checked CNF refutation endpoint mismatch"
      val _ = Library.check_oracle_tags
        "SmtCircuitSat" "CNF refutation" no_refutation
      val contradiction = Thm.MP
        (Thm.NOT_ELIM no_refutation) refutation_proof
      val theorem = Thm.DISCH cnf (Thm.CCONTR output contradiction)
      val _ = List.null (Thm.hyp theorem) andalso
        Term.aconv (Thm.concl theorem) (boolSyntax.mk_imp (cnf, output))
        orelse raise ERR "prove_cnf" "checked CNF implication mismatch"
      val _ = Library.check_oracle_tags
        "SmtCircuitSat" "CNF implication" theorem
    in theorem end
end
