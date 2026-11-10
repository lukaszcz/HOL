(* Checked SAT for already-clausified Boolean circuit definitions. *)

structure SmtCircuitSat =
struct
  open HolKernel

  val ERR = Feedback.mk_HOL_ERR "SmtCircuitSat"

  (* The clause shapes are built, not parsed: a constant a client theory
     exports must not capture the proposition variables. *)
  local
    open boolSyntax
    val p = Term.mk_var ("p", Type.bool)
    val q = Term.mk_var ("q", Type.bool)
  in
    (* (p = q) <=> (p \/ ~q) /\ (~p \/ q) *)
    val atom_cnf = Library.prove
      (mk_eq (mk_eq (p, q),
         mk_conj (mk_disj (p, mk_neg q), mk_disj (mk_neg p, q))),
       tautLib.TAUT_TAC)
    (* (p = T) <=> p *)
    val true_cnf = Library.prove (mk_eq (mk_eq (p, T), p), tautLib.TAUT_TAC)
    (* (p = F) <=> ~p *)
    val false_cnf = Library.prove
      (mk_eq (mk_eq (p, F), mk_neg p), tautLib.TAUT_TAC)
  end

  (* Each result is a kernel theorem equating a gate definition with its
     CNF clauses.  Non-connective right sides remain propositional atoms. *)
  fun definition_cnf_observed visit before_match instantiate definition =
    let
      val _ = visit definition
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
      val _ = before_match law definition
    in
      instantiate
        (Term.match_term (boolSyntax.lhs (Thm.concl law)) definition) law
    end

  fun silent_definition _ = ()
  fun silent_match _ _ = ()
  fun definition_cnf_using instantiate definition =
    definition_cnf_observed silent_definition silent_match
      instantiate definition

  fun definition_cnf definition =
    definition_cnf_using SmtReplayRuleObservation.inst_ty_term definition

  (* Balanced proof trees avoid a linear-depth conjunction spine during
     congruence and subsequent instantiation of large definition graphs. *)
  fun balanced_equivalences_using reflexive congruence [] =
        reflexive boolSyntax.T
    | balanced_equivalences_using reflexive congruence [theorem] = theorem
    | balanced_equivalences_using reflexive congruence theorems =
        let
          val half = List.length theorems div 2
          val conjunction = Term.rator (Term.rator
            (boolSyntax.mk_conj (boolSyntax.T, boolSyntax.T)))
          val left = balanced_equivalences_using reflexive congruence
            (List.take (theorems, half))
          val right = balanced_equivalences_using reflexive congruence
            (List.drop (theorems, half))
        in
          congruence (congruence (reflexive conjunction, left), right)
        end

  fun balanced_equivalences proofs =
    balanced_equivalences_using SmtReplayRuleObservation.REFL
      SmtReplayRuleObservation.MK_COMB proofs

  fun balanced_conjunction [] = boolTheory.TRUTH
    | balanced_conjunction [theorem] = theorem
    | balanced_conjunction theorems =
        let val half = List.length theorems div 2 in
          SmtReplayRuleObservation.CONJ
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
                 (SmtReplayRuleObservation.CONJUNCT1 theorem :: SmtReplayRuleObservation.CONJUNCT2 theorem :: rest)
                 accumulated
             | NONE => flatten rest (theorem :: accumulated))
      val clauses = flatten [SmtReplayRuleObservation.ASSUME cnf] []
      (* DIMACS abstracts T and F as atoms.  Supply their checked values. *)
      val constants =
        [boolTheory.TRUTH, SmtReplayRuleObservation.D_EQF_ELIM (SmtReplayRuleObservation.REFL boolSyntax.F)]
      val refutation_proof = List.foldr
        (fn (clause, rest) => SmtReplayRuleObservation.CONJ clause rest)
        (SmtReplayRuleObservation.ASSUME denied) (clauses @ constants)
      val refutation = Thm.concl refutation_proof
      fun original () = HolSatLib.GEN_SAT_PROVE_ONLY
        (satConfig.set_flag_is_cnf true
          (satConfig.set_term refutation satConfig.base_config))
      fun native () =
        let
          val inventory = flatten [Thm.ASSUME refutation] []
          val clauses = Array.fromList (List.map Thm.concl inventory)
        in
          case SmtCnfProve.prove clauses of
            SmtCnfProve.Unknown => original ()
          | SmtCnfProve.Model _ => raise HolSatLib.SAT_satisfiable ()
          | SmtCnfProve.Refuted proof =>
              let
                val used = Thm.hypset proof
                val needed = List.filter
                  (fn law => HOLset.member (used, Thm.concl law)) inventory
                (* Discharge the compact clauses before inserting their
                   existing proofs under the single refutation context. *)
                val closed = List.foldl
                  (fn (law, result) => Thm.DISCH (Thm.concl law) result)
                  proof needed
                val expanded = List.foldl
                  (fn (law, result) => Thm.MP result law)
                  closed (List.rev needed)
              in Thm.NOT_INTRO (Thm.DISCH refutation expanded) end
        end
      val no_refutation = native ()
      val _ = List.null (Thm.hyp no_refutation) andalso
        Term.aconv (Thm.concl no_refutation)
          (boolSyntax.mk_neg refutation) orelse
        raise ERR "prove_cnf" "checked CNF refutation endpoint mismatch"
      val _ = Library.check_oracle_tags
        "SmtCircuitSat" "CNF refutation" no_refutation
      val contradiction = SmtReplayRuleObservation.MP
        (SmtReplayRuleObservation.NOT_ELIM no_refutation) refutation_proof
      val theorem = SmtReplayRuleObservation.DISCH cnf (SmtReplayRuleObservation.CCONTR output contradiction)
      val _ = List.null (Thm.hyp theorem) andalso
        Term.aconv (Thm.concl theorem) (boolSyntax.mk_imp (cnf, output))
        orelse raise ERR "prove_cnf" "checked CNF implication mismatch"
      val _ = Library.check_oracle_tags
        "SmtCircuitSat" "CNF implication" theorem
    in theorem end
end
