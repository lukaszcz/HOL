(* Copyright (c) 2026 The HOL4 contributors. *)

(* Solver-neutral checked replay support for SMT-LIB ArraysEx lemmas. *)

structure SmtArrayProve =
struct

  val ERR = Feedback.mk_HOL_ERR "SmtArrayProve"

  fun unsupported t =
    raise ERR "array_prove"
      ("unsupported th-lemma shape: theory=array; checked replay is only " ^
       "implemented for function-update select/store/extensionality lemmas; " ^
       "conclusion=" ^ Library.term_to_string t)

  (* A simplification prover that deals with function (i.e., array) updates
     when the indices are integer or word literals. *)
  val simp_prove_update =
  let
    val word_type = wordsSyntax.mk_word_type Type.alpha
    val x = Term.mk_var ("x", word_type)
    val y = Term.mk_var ("y", word_type)
    val pat = boolSyntax.mk_eq (x, y)
  in
    simpLib.SIMP_PROVE (simpLib.&& (simpLib.++
    (intSimps.int_ss, simpLib.std_conv_ss {name = "word_EQ_CONV",
      pats = [pat], conv = wordsLib.word_EQ_CONV}),
    [combinTheory.UPDATE_def, boolTheory.EQ_SYM_EQ])) []
  end

  val array_rewrites = [
    combinTheory.UPDATE_def,
    combinTheory.APPLY_UPDATE_THM,
    combinTheory.UPDATE_APPLY_IMP_ID,
    combinTheory.UPDATE_EQ,
    boolTheory.FUN_EQ_THM,
    boolTheory.EQ_SYM_EQ
  ]

  fun symbolic_index_prove t =
    Tactical.prove (t,
      Tactical.THEN (bossLib.RW_TAC (bossLib.srw_ss()) [
          combinTheory.UPDATE_def,
          combinTheory.APPLY_UPDATE_THM,
          boolTheory.EQ_SYM_EQ
        ], bossLib.METIS_TAC []))

  fun extensionality_prove t =
    Tactical.prove (t,
      bossLib.RW_TAC (bossLib.srw_ss()) [
        boolTheory.FUN_EQ_THM,
        combinTheory.APPLY_UPDATE_THM,
        combinTheory.UPDATE_APPLY_IMP_ID,
        combinTheory.UPDATE_EQ,
        boolTheory.EQ_SYM_EQ
      ])

  fun choice_extensionality_prove t =
    Tactical.prove (t,
      Tactical.THEN
        (bossLib.RW_TAC (bossLib.srw_ss()) array_rewrites,
         bossLib.METIS_TAC [boolTheory.SELECT_AX]))

  fun metis_array_prove t =
    metisLib.METIS_PROVE array_rewrites t

  fun has_update_comb t =
    Lib.can (HolKernel.find_term combinSyntax.is_update_comb) t

  fun array_prove t =
    Z3_ProformaThms.prove Z3_ProformaThms.array_thms t
    handle Feedback.HOL_ERR _ =>
    simp_prove_update t
    handle Feedback.HOL_ERR _ =>
    symbolic_index_prove t
    handle Feedback.HOL_ERR _ =>
    extensionality_prove t
    handle Feedback.HOL_ERR _ =>
    choice_extensionality_prove t
    handle Feedback.HOL_ERR _ =>
    (if has_update_comb t then metis_array_prove t else unsupported t)
    handle Feedback.HOL_ERR _ =>
    unsupported t

end
