(* Copyright (c) 2026 The HOL4 contributors. *)

(* Solver-neutral checked replay support for SMT-LIB Unicode-string lemmas. *)

structure SmtStringProve =
struct

  val ERR = Feedback.mk_HOL_ERR "SmtStringProve"

  fun profile name f x = Profile.profile_with_exn_name name f x

  (* Keep future first-order string rungs under the shared replay bound. *)
  val metis_limit : mlibMeter.limit = {time = SOME 1.0, infs = SOME 5000}
  fun with_metis_limit f = Lib.with_flag (metisTools.limit, metis_limit) f

  fun unsupported theory t =
    raise ERR (theory ^ "_prove")
      ("unsupported th-lemma shape: theory=" ^ theory ^
       "; checked replay is only implemented for Unicode-string proforma, " ^
       "ground evaluation, and length/arithmetic lemmas; conclusion=" ^
       Library.term_to_string t)

  fun phase6_seq_gate t =
    raise ERR "check_seq_type"
      ("checked Z3_TAC replay for Z3 sequence/set/bag extensions is not " ^
       "implemented; missing feature: " ^
       "theory:Z3_Extensions:seq-set-bag:checked-replay; failing case IDs: " ^
       "theory:Z3_Extensions:seq, theory:Z3_Extensions:set, " ^
       "theory:Z3_Extensions:bag, proof-rule:th-lemma-seq; conclusion=" ^
       Library.term_to_string t)

  fun subterms t = HolKernel.find_terms (fn _ => true) t

  fun list_element_type tm =
    Lib.total listSyntax.dest_list_type (Term.type_of tm)

  (* Z3 uses the seq rule for both String and its polymorphic Seq extension.
     Phase 4 owns num-list strings only; every other element type must retain
     the Phase-6 sequence/set/bag gate. *)
  fun check_seq_type t =
    if List.exists
      (fn tm =>
        case list_element_type tm of
          SOME ty => Type.compare (ty, numSyntax.num) <> EQUAL
        | NONE => false)
      (subterms t)
    then phase6_seq_gate t
    else ()

  fun proforma_prove t =
    Z3_ProformaThms.prove Z3_ProformaThms.string_thms t
    handle Fail message =>
      raise ERR "proforma_prove" ("proforma lookup failed: " ^ message)

  val ground_eval_thms = [
    smtstringTheory.wfstr_compute,
    smtstringTheory.smtstr_concat_compute,
    smtstringTheory.smtstr_len_compute,
    smtstringTheory.smtstr_substr_compute,
    smtstringTheory.smtstr_at_compute,
    smtstringTheory.smtstr_prefixof_compute,
    smtstringTheory.smtstr_suffixof_compute,
    smtstringTheory.smtstr_contains_compute,
    smtstringTheory.smtstr_indexof_aux_compute,
    smtstringTheory.smtstr_indexof_compute,
    smtstringTheory.smtstr_lt_compute,
    smtstringTheory.smtstr_le_compute,
    smtstringTheory.smtstr_char_compute,
    smtstringTheory.smt_in_re_deriv,
    smtstringTheory.smtstr_replace_compute,
    smtstringTheory.smtstr_replace_all_compute,
    smtstringTheory.smtstr_replace_re_compute,
    smtstringTheory.smtstr_replace_re_all_compute,
    smtstringTheory.smtstr_is_digit_compute,
    smtstringTheory.smtstr_to_code_compute,
    smtstringTheory.smtstr_from_code_compute,
    smtstringTheory.smtstr_digits_compute,
    smtstringTheory.smtstr_to_int_compute,
    smtstringTheory.smtstr_from_int_compute,
    smtstringz3Theory.seq_unit_compute,
    smtstringz3Theory.seq_tail_compute,
    smtstringz3Theory.seq_eq_compute,
    smtstringz3Theory.seq_nth_i_compute,
    smtstringz3Theory.char_is_digit_compute,
    smtstringz3Theory.seq_digit2int_compute,
    smtstringz3Theory.seq_digit_compute,
    smtstringz3Theory.seq_stoi_compute,
    smtstringz3Theory.aut_chars_compute,
    smtstringz3Theory.aut_alphabet_compute,
    smtstringz3Theory.aut_extend_compute,
    smtstringz3Theory.aut_derivatives_compute,
    smtstringz3Theory.aut_state_compute,
    smtstringz3Theory.aut_accept_compute
  ]

  val ground_eval_compset =
    computeLib.add_thms ground_eval_thms
      (computeLib.copy (!computeLib.the_compset))

  fun ground_eval_prove t =
    Drule.EQT_ELIM (computeLib.CBV_CONV ground_eval_compset t)
    handle Conv.UNCHANGED =>
      raise ERR "ground_eval_prove"
        "ground evaluation did not change the conclusion"
         | Fail message =>
      raise ERR "ground_eval_prove"
        ("ground evaluation failed: " ^ message)

  val length_arith_rewrites = [
    smtstringTheory.smtstr_len_concat_int,
    smtstringTheory.smtstr_len_substr,
    smtstringTheory.smtstr_len_at,
    smtstringTheory.smtstr_len_nonnegative,
    smtstringTheory.smtstr_len_char,
    smtstringz3Theory.seq_unit_length,
    smtstringz3Theory.seq_tail_length,
    smtstringz3Theory.seq_eq_compute
  ]

  fun length_arith_prove arith_prove t =
    let
      val normalized =
        simpLib.SIMP_CONV
          (simpLib.++ (bossLib.srw_ss(), intSimps.INT_REDUCE_ss))
          length_arith_rewrites t
      val t' = boolSyntax.rhs (Thm.concl normalized)
      val _ = if Term.aconv t t' then
          raise ERR "length_arith_prove"
            "length normalization did not change the conclusion"
        else ()
    in
      Thm.EQ_MP (Thm.SYM normalized) (arith_prove t')
    end
    handle Conv.UNCHANGED =>
      raise ERR "length_arith_prove"
        "length normalization did not change the conclusion"
         | Fail message =>
      raise ERR "length_arith_prove"
        ("length/arithmetic replay failed: " ^ message)

  fun string_prove arith_prove t =
    let val () = check_seq_type t in
      profile "string(rung:1/proforma)" proforma_prove t
      handle Feedback.HOL_ERR _ =>
      profile "string(rung:2/ground-eval)" ground_eval_prove t
      handle Feedback.HOL_ERR _ =>
      profile "string(rung:3/length-arith)"
        (length_arith_prove arith_prove) t
      handle Feedback.HOL_ERR _ =>
      profile "string(rung:7/unsupported)" (unsupported "seq") t
    end

  fun char_prove t =
    profile "string(rung:6/char-placeholder)" (unsupported "char") t

end
