(* Checked SAT for already-clausified Boolean circuit definitions. *)

structure SmtCircuitSat =
struct
  open HolKernel

  val ERR = Feedback.mk_HOL_ERR "SmtCircuitSat"

  val atom_cnf = canonContextTheory.pth_peq1  (* (p = q) <=> CNF *)
  val true_cnf = HolSmtTheory.r003  (* (p = T) <=> p *)
  val false_cnf = HolSmtTheory.r005  (* (p = F) <=> ~p *)

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

  local
    fun balanced_using empty combine [] = empty
      | balanced_using _ _ [leaf] = leaf
      | balanced_using _ combine leaves =
          let
            fun build count input =
              if count = 1 then (hd input, tl input)
              else
                let
                  val half = count div 2
                  val (left, remaining) = build half input
                  val (right, remaining) = build (count - half) remaining
                in (combine (left, right), remaining) end
          in #1 (build (List.length leaves) leaves) end
  in
    (* Balanced proof trees avoid a linear-depth conjunction spine during
       congruence and subsequent instantiation of large definition graphs. *)
    fun balanced_equivalences_using reflexive _ [] = reflexive boolSyntax.T
      | balanced_equivalences_using _ _ [theorem] = theorem
      | balanced_equivalences_using reflexive congruence
          (theorems as first :: _) =
          let
            val conjunction = Term.rator (Term.rator
              (boolSyntax.mk_conj (boolSyntax.T, boolSyntax.T)))
            fun combine (left, right) =
              congruence (congruence (reflexive conjunction, left), right)
          in balanced_using first combine theorems end

    fun balanced_equivalences proofs =
      balanced_equivalences_using SmtReplayRuleObservation.REFL
        SmtReplayRuleObservation.MK_COMB proofs

    val balanced_conjunction_term =
      balanced_using boolSyntax.T boolSyntax.mk_conj
    val balanced_conjunction =
      balanced_using boolTheory.TRUTH
        (fn (left, right) => SmtReplayRuleObservation.CONJ left right)
  end

  (* Prove [cnf ==> output] without asking HolSat to re-clausify the graph.
     SAT means this abstraction cannot discharge the obligation; no model
     theorem is required.  Every UNSAT certificate is replayed in HOL. *)
  fun prove_cnf (cnf, output) =
    let
      val denied = boolSyntax.mk_neg output
      (* DIMACS abstracts T and F as atoms.  Supply their checked values. *)
      val not_false = boolSyntax.mk_neg boolSyntax.F
      fun prove_not_false () = SmtReplayRuleObservation.D_EQF_ELIM
        (SmtReplayRuleObservation.REFL boolSyntax.F)
      fun original () =
        let
          val refutation_proof = SmtReplayRuleObservation.CONJ
            (SmtReplayRuleObservation.ASSUME cnf)
            (SmtReplayRuleObservation.CONJ boolTheory.TRUTH
              (SmtReplayRuleObservation.CONJ (prove_not_false ())
                (SmtReplayRuleObservation.ASSUME denied)))
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
        in
          SmtReplayRuleObservation.MP
            (SmtReplayRuleObservation.NOT_ELIM no_refutation) refutation_proof
        end
      val contradiction =
        case SmtCnfProve.prove_conjunction
            (cnf,[boolSyntax.T, not_false, denied]) of
          SmtCnfProve.Unknown => original ()
        | SmtCnfProve.Model _ => raise HolSatLib.SAT_satisfiable ()
        | SmtCnfProve.Refuted proof =>
            let
              val remaining = ref (Thm.hypset proof)
              fun take term =
                if HOLset.member (!remaining,term) then
                  (remaining := HOLset.delete (!remaining,term); true)
                else false
              (* Select the first occurrence of each used hypothesis.
                 Shared prefixes are projected once, in clause order. *)
              fun select term =
                if HOLset.isEmpty (!remaining) then NONE
                else case Lib.total boolSyntax.dest_conj term of
                    NONE => if take term then SOME (curry (op ::))
                            else NONE
                  | SOME (a,b) =>
                    (case (select a,select b) of
                        (NONE,NONE) => NONE
                      | (SOME left,NONE) => SOME
                          (left o SmtReplayRuleObservation.CONJUNCT1)
                      | (NONE,SOME right) => SOME
                          (right o SmtReplayRuleObservation.CONJUNCT2)
                      | (SOME left,SOME right) =>
                          SOME (fn law =>
                            left (SmtReplayRuleObservation.CONJUNCT1 law) o
                            right (SmtReplayRuleObservation.CONJUNCT2 law)))
              val selected = select cnf
              fun include_fact (term,fact) =
                if take term then SOME (fact ()) else NONE
              val facts = List.mapPartial include_fact
                [(boolSyntax.T, fn () => boolTheory.TRUTH),
                 (not_false, prove_not_false),
                 (denied, fn () => SmtReplayRuleObservation.ASSUME denied)]
              val needed = case selected of NONE => facts
                | SOME project => project
                    (SmtReplayRuleObservation.ASSUME cnf) facts
              (* Discharge every clause before introducing cnf or denied:
                 either hypothesis may also be a clause in the inventory. *)
              val closed = List.foldl
                (fn (law, result) => Thm.DISCH (Thm.concl law) result)
                proof needed
              val _ = List.null (Thm.hyp closed) andalso
                Term.aconv (Thm.concl proof) boolSyntax.F orelse
                raise ERR "prove_cnf" "checked CNF refutation endpoint mismatch"
            in
              List.foldl (fn (law, result) => Thm.MP result law)
                closed (List.rev needed)
            end
      val theorem = SmtReplayRuleObservation.DISCH cnf (SmtReplayRuleObservation.CCONTR output contradiction)
      val _ = List.null (Thm.hyp theorem) andalso
        Term.aconv (Thm.concl theorem) (boolSyntax.mk_imp (cnf, output))
        orelse raise ERR "prove_cnf" "checked CNF implication mismatch"
      val _ = Library.check_oracle_tags
        "SmtCircuitSat" "CNF implication" theorem
    in theorem end
end
