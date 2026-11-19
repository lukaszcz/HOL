(* Checked extensional regular-language relations shared by proof formats.
   Source HOL equality on the regex syntax datatype remains intensional. *)

structure SmtRegLanProve =
struct
  val ERR = Feedback.mk_HOL_ERR "SmtRegLanProve"

  val reglan_ty =
    Type.mk_thy_type {Thy = "smtstring", Tyop = "reglan", Args = []}
  val equiv_tm = Term.prim_mk_const
    {Thy = "smtstring", Name = "reglan_equiv"}

  fun mk_equiv (left, right) =
    Term.list_mk_comb (equiv_tm, [left, right])

  fun dest_equiv proposition =
    case boolSyntax.strip_comb proposition of
      (head, [left, right]) =>
        if Term.same_const head equiv_tm then (left, right)
        else raise ERR "dest_equiv" "not regular-language equivalence"
    | _ => raise ERR "dest_equiv" "not regular-language equivalence"

  val is_equiv = Lib.can dest_equiv

  fun proof_equality (left, right) =
    if Type.compare (Term.type_of left, reglan_ty) = EQUAL then
      mk_equiv (left, right)
    else boolSyntax.mk_eq (left, right)

  fun refl regex =
    let val generic = Drule.SPEC_ALL smtstringTheory.reglan_equiv_refl in
      Drule.INST_TY_TERM
        (Term.match_term (Thm.concl generic) (mk_equiv (regex, regex)))
        generic
    end

  fun sym premise =
    Drule.MATCH_MP smtstringTheory.reglan_equiv_sym premise

  fun trans first second =
    let
      val (_, middle) = dest_equiv (Thm.concl first)
      val (middle', _) = dest_equiv (Thm.concl second)
      val _ = Term.aconv middle middle' orelse
        raise ERR "trans" "regular-language middle endpoints differ"
    in
      Drule.MATCH_MP smtstringTheory.reglan_equiv_trans
        (Thm.CONJ first second)
    end

  val congruence_theorems =
    [smtstringTheory.reglan_eq_imp_equiv,
     smtstringTheory.reglan_equiv_refl,
     smtstringTheory.reglan_equiv_sym,
     smtstringTheory.reglan_equiv_trans,
     smtstringTheory.reglan_equiv_equiv_eq,
     smtstringTheory.reglan_concat_equiv,
     smtstringTheory.reglan_union_equiv,
     smtstringTheory.reglan_inter_equiv,
     smtstringTheory.reglan_diff_equiv,
     smtstringTheory.reglan_comp_equiv,
     smtstringTheory.reglan_star_equiv,
     smtstringTheory.reglan_plus_equiv,
     smtstringTheory.reglan_opt_equiv,
     smtstringTheory.reglan_power_equiv,
     smtstringTheory.reglan_loop_equiv,
     smtstringTheory.reglan_cond_equiv,
     smtstringTheory.smt_in_re_equiv_eq]

  fun metis facts target =
    Lib.with_flag (metisTools.limit,
      {time = SOME 1.0, infs = SOME 5000} : mlibMeter.limit)
      (HOLFlags.with_flags [(metisTools.metis_trace, 0)]
        (metisLib.METIS_PROVE facts)) target

  (* The compact boundary supplies the same laws in its injective local
     namespace, including variables absent from a law's consequence. *)
  fun congruence_with_theorems schemas premises target =
    let
      fun exact proposition =
        case List.find (Term.aconv proposition o Thm.concl) premises of
          SOME theorem => theorem
        | NONE =>
            (case Lib.total boolSyntax.dest_conj proposition of
               SOME (left, right) => Thm.CONJ (exact left) (exact right)
             | NONE =>
                 case Lib.total dest_equiv proposition of
                   SOME (left, right) =>
                     if Term.aconv left right then refl left
                     else raise ERR "congruence" "missing operand relation"
                 | NONE =>
                     let val (left, right) = boolSyntax.dest_eq proposition in
                       Thm.ALPHA left right
                     end)
      fun instantiate schema =
        let
          val generic = Drule.SPEC_ALL schema
          val (_, consequence) = boolSyntax.strip_imp (Thm.concl generic)
          val instance = Drule.INST_TY_TERM
            (Term.match_term consequence target) generic
          val (antecedents, _) = boolSyntax.strip_imp (Thm.concl instance)
        in Drule.LIST_MP (List.map exact antecedents) instance end
    in
      Lib.tryfind instantiate schemas
      handle Feedback.HOL_ERR _ =>
        metis (premises @ schemas) target
    end

  fun congruence premises target =
    congruence_with_theorems congruence_theorems premises target

  val rewrite_theorems =
    [smtstringTheory.reglan_equiv_refl,
     smtstringTheory.reglan_equiv_concat_literals,
     smtstringTheory.reglan_equiv_all,
     smtstringTheory.reglan_equiv_diff,
     smtstringTheory.reglan_equiv_opt,
     smtstringTheory.reglan_equiv_plus,
     smtstringTheory.reglan_equiv_power_loop,
     smtstringTheory.reglan_equiv_power_zero,
     smtstringTheory.reglan_equiv_power_one,
     smtstringTheory.reglan_equiv_star_none,
     smtstringTheory.reglan_equiv_star_epsilon,
     smtstringTheory.reglan_equiv_star_star,
     smtstringTheory.reglan_equiv_union_comm,
     smtstringTheory.reglan_equiv_union_assoc,
     smtstringTheory.reglan_equiv_inter_comm,
     smtstringTheory.reglan_equiv_inter_assoc]

  fun rewrite target =
    (dest_equiv target;
     let
       fun instantiate schema =
         let val generic = Drule.SPEC_ALL schema in
           Drule.INST_TY_TERM
             (Term.match_term (Thm.concl generic) target) generic
         end
     in
       Lib.tryfind instantiate rewrite_theorems
       handle Feedback.HOL_ERR _ =>
         (let
            (* Exact syntax equality is a sufficient, checked special case
               of language equivalence.  Reuse the String normalizer for
               string computations embedded in regex constructors. *)
            val endpoints = dest_equiv target
            val equality = SmtStringProve.string_rewrite_prove
              (boolSyntax.mk_eq endpoints)
          in
            Drule.MATCH_MP smtstringTheory.reglan_eq_imp_equiv equality
          end
          handle Feedback.HOL_ERR holerr =>
            if SmtResource.is_resource_gate holerr then
              raise Feedback.HOL_ERR holerr
            else metis (rewrite_theorems @ congruence_theorems) target)
     end)
end
