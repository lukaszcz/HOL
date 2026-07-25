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
       "ground evaluation, length/arithmetic, and symbolic " ^
       "concat/prefix/suffix/contains and regex/aut.accept lemmas; " ^
       "conclusion=" ^
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

  val symbolic_normalizations = [
    smtstringTheory.smtstr_concat_assoc,
    smtstringTheory.smtstr_concat_nil_left,
    smtstringTheory.smtstr_concat_nil_right,
    smtstringTheory.smtstr_concat_middle_singleton,
    smtstringTheory.smtstr_singleton_concat_middle,
    smtstringTheory.smtstr_prefixof_refl,
    smtstringTheory.smtstr_suffixof_refl,
    smtstringTheory.smtstr_contains_refl,
    smtstringTheory.smtstr_prefixof_singleton,
    smtstringz3Theory.seq_head_tail_int,
    smtstringz3Theory.seq_head_tail_int_zero_left,
    smtstringz3Theory.seq_prefixof_singleton,
    smtstringz3Theory.seq_prefixof_head,
    smtstringz3Theory.seq_concat_middle_singleton,
    smtstringz3Theory.seq_concat_middle_singleton_result,
    smtstringz3Theory.seq_concat_middle_singleton_right,
    smtstringz3Theory.seq_concat_middle_singleton_left,
    smtstringz3Theory.seq_head_shared_singleton_prefix,
    smtstringz3Theory.seq_head_shared_singleton_prefix_right,
    smtstringz3Theory.seq_length_two,
    smtstringz3Theory.seq_two_two_concat_not_three,
    smtstringz3Theory.seq_tail_zero_step,
    smtstringz3Theory.seq_unit_compute,
    smtstringz3Theory.seq_eq_compute
  ]

  val symbolic_lemmas = [
    smtstringTheory.smtstr_concat_middle_singleton,
    smtstringTheory.smtstr_singleton_concat_middle,
    smtstringTheory.smtstr_len_eq_zero,
    smtstringTheory.smtstr_prefixof_decompose,
    smtstringTheory.smtstr_suffixof_decompose,
    smtstringTheory.smtstr_contains_decompose,
    smtstringTheory.smtstr_prefixof_refl,
    smtstringTheory.smtstr_suffixof_refl,
    smtstringTheory.smtstr_contains_refl,
    smtstringTheory.smtstr_prefixof_singleton,
    smtstringTheory.smtstr_prefixof_imp_contains,
    smtstringTheory.smtstr_suffixof_imp_contains,
    smtstringTheory.smtstr_prefixof_trans,
    smtstringTheory.smtstr_suffixof_trans,
    smtstringTheory.smtstr_contains_trans,
    smtstringz3Theory.seq_head_tail_int,
    smtstringz3Theory.seq_head_tail_int_zero_left,
    smtstringz3Theory.seq_prefixof_singleton,
    smtstringz3Theory.seq_prefixof_head,
    smtstringz3Theory.seq_concat_middle_singleton,
    smtstringz3Theory.seq_concat_middle_singleton_result,
    smtstringz3Theory.seq_concat_middle_singleton_right,
    smtstringz3Theory.seq_concat_middle_singleton_left,
    smtstringz3Theory.seq_head_shared_singleton_prefix,
    smtstringz3Theory.seq_head_shared_singleton_prefix_right,
    smtstringz3Theory.seq_length_two,
    smtstringz3Theory.seq_two_two_concat_not_three,
    smtstringz3Theory.seq_tail_zero_step
  ]

  val symbolic_string_consts =
    List.map
      (fn name => Term.prim_mk_const {Thy = "smtstring", Name = name})
      ["smtstr_concat", "smtstr_prefixof", "smtstr_suffixof",
       "smtstr_contains"]

  val symbolic_thms =
    Z3_ProformaThms.thm_net_from_list symbolic_lemmas

  fun is_symbolic_string_goal t =
    List.exists
      (fn c => Lib.can (HolKernel.find_term (Term.same_const c)) t)
      symbolic_string_consts

  fun symbolic_string_prove t =
    if not (is_symbolic_string_goal t) then
      raise ERR "symbolic_string_prove"
        "no symbolic concat/prefix/suffix/contains term"
    else
      Z3_ProformaThms.prove symbolic_thms t
      handle Feedback.HOL_ERR _ =>
      with_metis_limit (fn () =>
        metisLib.METIS_PROVE
          [smtstringz3Theory.seq_head_shared_singleton_prefix_right] t) ()
      handle Feedback.HOL_ERR _ =>
      with_metis_limit (fn () =>
        Tactical.prove (t,
          Tactical.THEN
            (bossLib.RW_TAC
               (simpLib.++ (bossLib.srw_ss(), intSimps.INT_REDUCE_ss))
               symbolic_normalizations,
             bossLib.METIS_TAC symbolic_lemmas))) ()

  val regex_normalizations = [
    smtstringz3Theory.seq_unit_compute,
    smtstringTheory.re_nullable_def,
    smtstringTheory.re_deriv_def,
    smtstringTheory.reglan_power_deriv_def,
    smtstringTheory.reglan_loop_deriv_def,
    smtstringTheory.smt_in_re_loop_singleton_0_1,
    smtstringTheory.smt_in_re_loop_singleton_0_2,
    smtstringTheory.smt_in_re_loop_singleton_1_3,
    smtstringTheory.smt_in_re_loop_nullable_singleton_0_1,
    smtstringTheory.smt_in_re_loop_nullable_singleton_1_2,
    smtstringTheory.smt_in_re_star_allchar,
    smtstringTheory.smt_in_re_plus_allchar,
    smtstringTheory.smt_in_re_def,
    smtstringTheory.smtstr_len_def,
    smtstringz3Theory.aut_accept_zero,
    smtstringz3Theory.aut_accept_transition_int,
    smtstringz3Theory.aut_accept_range_deriv,
    smtstringz3Theory.aut_accept_loop_deriv_1_3,
    smtstringz3Theory.aut_accept_loop_deriv_0_2,
    smtstringz3Theory.aut_accept_loop_deriv_0_1,
    smtstringz3Theory.aut_accept_loop_nullable_deriv_1_2,
    smtstringz3Theory.aut_accept_loop_nullable_deriv_0_1,
    smtstringz3Theory.aut_accept_range_transition_zero,
    smtstringz3Theory.aut_accept_loop_transition_zero,
    smtstringz3Theory.aut_accept_loop_transition_one,
    smtstringz3Theory.aut_accept_loop_transition_two,
    smtstringz3Theory.aut_accept_range_transition_seq_unit,
    smtstringz3Theory.aut_accept_loop_transition_seq_unit_zero,
    smtstringz3Theory.aut_accept_loop_transition_seq_unit_one,
    smtstringz3Theory.aut_accept_loop_transition_seq_unit_two,
    smtstringz3Theory.aut_accept_comp_transition_seq_unit,
    smtstringz3Theory.aut_accept_inter_transition_seq_unit,
    smtstringz3Theory.aut_accept_loop_nullable_transition_seq_unit_zero,
    smtstringz3Theory.aut_accept_loop_nullable_transition_seq_unit_one,
    smtstringz3Theory.aut_accept_empty,
    smtstringz3Theory.aut_accept_empty_terminal_int
  ]

  val regex_lemmas = [
    smtstringTheory.re_nullable_def,
    smtstringTheory.smt_in_re_loop_singleton_0_1,
    smtstringTheory.smt_in_re_loop_singleton_0_2,
    smtstringTheory.smt_in_re_loop_singleton_1_3,
    smtstringTheory.smt_in_re_loop_nullable_singleton_0_1,
    smtstringTheory.smt_in_re_loop_nullable_singleton_1_2,
    smtstringTheory.smt_in_re_star_allchar,
    smtstringTheory.smt_in_re_plus_allchar,
    smtstringTheory.re_deriv_correct,
    smtstringTheory.re_nullable_correct,
    smtstringz3Theory.aut_accept_nonnullable_length,
    smtstringz3Theory.aut_accept_nonnullable_length_int,
    smtstringz3Theory.aut_accept_range_length_int,
    smtstringz3Theory.aut_accept_range_length_zero,
    smtstringz3Theory.aut_accept_loop_positive_length_zero,
    smtstringz3Theory.aut_accept_loop_positive_length_seq_unit,
    smtstringz3Theory.aut_accept_plus_allchar_length_one,
    smtstringz3Theory.aut_accept_step,
    smtstringz3Theory.aut_accept_transition,
    smtstringz3Theory.aut_accept_transition_int,
    smtstringz3Theory.aut_accept_range_deriv,
    smtstringz3Theory.aut_accept_loop_deriv_1_3,
    smtstringz3Theory.aut_accept_loop_deriv_0_2,
    smtstringz3Theory.aut_accept_loop_deriv_0_1,
    smtstringz3Theory.aut_accept_loop_nullable_deriv_1_2,
    smtstringz3Theory.aut_accept_loop_nullable_deriv_0_1,
    smtstringz3Theory.aut_accept_range_transition_zero,
    smtstringz3Theory.aut_accept_loop_transition_zero,
    smtstringz3Theory.aut_accept_loop_transition_one,
    smtstringz3Theory.aut_accept_loop_transition_two,
    smtstringz3Theory.aut_accept_range_transition_seq_unit,
    smtstringz3Theory.aut_accept_loop_transition_seq_unit_zero,
    smtstringz3Theory.aut_accept_loop_transition_seq_unit_one,
    smtstringz3Theory.aut_accept_loop_transition_seq_unit_two,
    smtstringz3Theory.aut_accept_comp_singleton_transition,
    smtstringz3Theory.aut_accept_comp_range_transition,
    smtstringz3Theory.aut_accept_inter_range_comp_transition,
    smtstringz3Theory.aut_accept_loop_nullable_transition_zero,
    smtstringz3Theory.aut_accept_loop_nullable_transition_one,
    smtstringz3Theory.aut_accept_comp_transition_seq_unit,
    smtstringz3Theory.aut_accept_comp_range_transition_seq_unit,
    smtstringz3Theory.aut_accept_inter_transition_seq_unit,
    smtstringz3Theory.aut_accept_loop_nullable_transition_seq_unit_zero,
    smtstringz3Theory.aut_accept_loop_nullable_transition_seq_unit_one,
    smtstringz3Theory.aut_accept_empty,
    smtstringz3Theory.aut_accept_empty_terminal_int
  ]

  val regex_consts =
    List.map
      (fn {Thy, Name} => Term.prim_mk_const {Thy = Thy, Name = Name})
      [{Thy = "smtstring", Name = "smt_in_re"},
       {Thy = "smtstringz3", Name = "aut_accept"}]

  val regex_thms =
    Z3_ProformaThms.thm_net_from_list regex_lemmas

  fun is_regex_goal t =
    List.exists
      (fn c => Lib.can (HolKernel.find_term (Term.same_const c)) t)
      regex_consts

  fun regex_prove t =
    if not (is_regex_goal t) then
      raise ERR "regex_prove" "no regex membership or aut.accept term"
    else
      Z3_ProformaThms.prove regex_thms t
      handle Feedback.HOL_ERR _ =>
      with_metis_limit
        (fn () => metisLib.METIS_PROVE regex_lemmas t) ()
      handle Feedback.HOL_ERR _ =>
      with_metis_limit (fn () =>
        Tactical.prove (t,
          Tactical.THEN
            (bossLib.RW_TAC
               (simpLib.++ (bossLib.srw_ss(), intSimps.INT_REDUCE_ss))
               regex_normalizations,
             bossLib.METIS_TAC regex_lemmas))) ()

  fun string_prove arith_prove t =
    let val () = check_seq_type t in
      profile "string(rung:1/proforma)" proforma_prove t
      handle Feedback.HOL_ERR _ =>
      profile "string(rung:2/ground-eval)" ground_eval_prove t
      handle Feedback.HOL_ERR _ =>
      profile "string(rung:3/length-arith)"
        (length_arith_prove arith_prove) t
      handle Feedback.HOL_ERR _ =>
      profile "string(rung:4/symbolic)" symbolic_string_prove t
      handle Feedback.HOL_ERR _ =>
      profile "string(rung:5/regex)" regex_prove t
      handle Feedback.HOL_ERR _ =>
      profile "string(rung:7/unsupported)" (unsupported "seq") t
    end

  fun char_prove t =
    profile "string(rung:6/char-placeholder)" (unsupported "char") t

end
