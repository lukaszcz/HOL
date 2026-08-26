(* Copyright (c) 2026 The HOL4 contributors. *)

(* Solver-neutral checked replay support for SMT-LIB Unicode-string lemmas. *)

structure SmtStringProve =
struct

  val ERR = Feedback.mk_HOL_ERR "SmtStringProve"

  fun profile name f x = Profile.profile_with_exn_name name f x

  fun with_string_budget case_id prove t =
    SmtResource.with_resource_step_time "String" case_id
      (fn target =>
        (SmtResource.check_resource_goal "String" case_id target;
         prove target)) t

  fun rethrow_resource holerr =
    if SmtResource.is_resource_gate holerr then raise Feedback.HOL_ERR holerr
    else ()

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

  (* `check_seq_type` is a boundary guard for direct users of the String
     prover.  Z3 th-lemma dispatch classifies genuine lists first and sends
     them to SmtSeqProve; this guard therefore cannot hide a native Seq
     failure behind a String-prover fallback. *)
  fun nonstring_seq_error t =
    raise ERR "check_seq_type"
      ("unsupported th-lemma shape: theory=seq; " ^
       "shape=non-string-sequence; dispatch genuine (Seq A) terms through " ^
       "SmtSeqProve; conclusion=" ^ Library.term_to_string t)

  fun smtstring_consts thy names =
    List.map (fn name => Term.prim_mk_const {Thy = thy, Name = name}) names

  (* Rung guards test a term against a whole family of constants.  Comparing
     (theory, name) pairs against a set keeps that to one traversal, rather
     than one traversal per constant, while agreeing with
     'Term.same_const' in ignoring the type instance. *)
  fun const_name_set consts =
    Redblackset.addList
      (Redblackset.empty (Lib.pair_compare (String.compare, String.compare)),
       List.map
         (fn c =>
           let val {Thy, Name, ...} = Term.dest_thy_const c
           in (Thy, Name) end)
         consts)

  fun is_named_const names tm =
    Term.is_const tm andalso
    let val {Thy, Name, ...} = Term.dest_thy_const tm
    in Redblackset.member (names, (Thy, Name)) end

  fun mentions_any names t =
    Lib.can (HolKernel.find_term (is_named_const names)) t

  fun list_element_type tm =
    Lib.total listSyntax.dest_list_type (Term.type_of tm)

  (* Z3 uses the seq rule for both String and its polymorphic Seq extension.
     Phase 4 String has its own type.  Its constructor payload is an
     implementation detail, while every other HOL list belongs to the
     native SmtSeqProve replayer. *)
  fun check_seq_type t =
    let
      fun is_smtstr_value tm =
        case boolSyntax.strip_comb tm of
          (head, [_]) =>
            Term.is_const head andalso
            let val {Thy, Name, ...} = Term.dest_thy_const head
            in Thy = "smtstring" andalso Name = "SmtStr" end
        | _ => false
      fun contains_sequence tm =
        if is_smtstr_value tm then
          false
        else if Option.isSome (list_element_type tm) then
          true
        else
          (let val (rator, rand) = Term.dest_comb tm
           in contains_sequence rator orelse contains_sequence rand end
           handle Feedback.HOL_ERR _ =>
             (let val (_, body) = Term.dest_abs tm
              in contains_sequence body end
              handle Feedback.HOL_ERR _ => false))
    in
      if contains_sequence t then nonstring_seq_error t else ()
    end

  (* ':smtstr' is a type definition rather than a datatype, so evaluation
     goes through the representation: 'smtstr_rep_compute' unfolds a
     wellformed literal and 'SmtStr_eq_compute' supplies the equality test
     that a datatype constructor would otherwise have given us.  Both are
     load-bearing here -- without them ground string steps do not reduce. *)
  val ground_eval_thms = [
    smtstringTheory.smtstr_rep_compute,
    smtstringTheory.SmtStr_eq_compute,
    smtstringTheory.smtstr_concat_def,
    smtstringTheory.smtstr_len_def,
    smtstringTheory.smtstr_substr_def,
    smtstringTheory.smtstr_update_def,
    smtstringTheory.smtstr_rev_def,
    smtstringTheory.smtstr_at_def,
    smtstringTheory.smtstr_prefixof_def,
    smtstringTheory.smtstr_suffixof_def,
    smtstringTheory.smtstr_contains_def,
    smtstringTheory.smtstr_indexof_aux_def,
    smtstringTheory.smtstr_indexof_def,
    smtstringTheory.smtstr_lt_def,
    smtstringTheory.smtstr_le_def,
    smtstringTheory.smtstr_char_def,
    smtstringTheory.smt_in_re_deriv,
    smtstringTheory.smtstr_replace_def,
    smtstringTheory.smtstr_replace_all_def,
    smtstringTheory.smtstr_replace_re_def,
    smtstringTheory.smtstr_replace_re_all_def,
    smtstringTheory.smtstr_is_digit_compute,
    smtstringTheory.smtstr_to_code_def,
    smtstringTheory.smtstr_from_code_def,
    smtstringTheory.smtstr_digits_def,
    smtstringTheory.smtstr_to_int_def,
    smtstringTheory.smtstr_from_int_def,
    smtstringz3Theory.seq_unit_def,
    smtstringz3Theory.seq_tail_def,
    smtstringz3Theory.seq_eq_def,
    smtstringz3Theory.seq_nth_i_compute,
    smtstringz3Theory.char_is_digit_def,
    smtstringz3Theory.seq_digit2int_def,
    smtstringz3Theory.seq_digit_def,
    smtstringz3Theory.seq_stoi_def,
    smtstringz3Theory.aut_state_def,
    smtstringz3Theory.aut_accept_compute
  ]

  val ground_eval_compset =
    computeLib.add_thms ground_eval_thms
      (computeLib.copy (computeLib.the_compset()))

  fun ground_eval_prove t =
    Drule.EQT_ELIM (computeLib.CBV_CONV ground_eval_compset t)
    handle Conv.UNCHANGED =>
      raise ERR "ground_eval_prove"
        "ground evaluation did not change the conclusion"
         | Fail message =>
      raise ERR "ground_eval_prove"
        ("ground evaluation failed: " ^ message)

  val length_arith_rewrites = [
    smtstringTheory.smtstr_len_concat,
    smtstringTheory.smtstr_len_substr,
    smtstringTheory.smtstr_len_at,
    smtstringTheory.smtstr_len_nonnegative,
    smtstringTheory.smtstr_len_char,
    smtstringz3Theory.seq_unit_length,
    smtstringz3Theory.seq_tail_length,
    smtstringz3Theory.seq_eq_def,
    integerTheory.int_ge,
    integerTheory.INT_LE_ADDR
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
      Thm.EQ_MP (Thm.SYM normalized)
        (arith_prove t'
         handle Feedback.HOL_ERR holerr =>
           raise ERR "length_arith_prove"
             ("arithmetic prover rejected normalized conclusion " ^
              Parse.term_to_string t' ^ ": " ^
              Feedback.message_of holerr))
    end
    handle Conv.UNCHANGED =>
      raise ERR "length_arith_prove"
        "length normalization did not change the conclusion"
         | Fail message =>
      raise ERR "length_arith_prove"
        ("length/arithmetic replay failed: " ^ message)

  val seq_shape_rules = [
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
    smtstringz3Theory.seq_tail_zero_step
  ]

  val symbolic_normalizations = [
    smtstringTheory.smtstr_concat_assoc,
    smtstringTheory.smtstr_concat_nil_left,
    smtstringTheory.smtstr_concat_nil_right,
    smtstringTheory.smtstr_concat_middle_singleton,
    smtstringTheory.smtstr_singleton_concat_middle,
    smtstringTheory.smtstr_prefixof_refl,
    smtstringTheory.smtstr_suffixof_refl,
    smtstringTheory.smtstr_contains_refl,
    smtstringTheory.smtstr_prefixof_singleton
  ] @ seq_shape_rules @ [
    smtstringz3Theory.seq_unit_def,
    smtstringz3Theory.seq_eq_def,
    smtstringTheory.smtstr_update_def,
    smtstringTheory.smtstr_len_def
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
    smtstringTheory.smtstr_contains_trans
  ] @ seq_shape_rules

  val symbolic_string_names =
    const_name_set
      (smtstring_consts "smtstring"
        ["smtstr_concat", "smtstr_update", "smtstr_prefixof",
         "smtstr_suffixof", "smtstr_contains"])

  val middle_singleton_lemmas = [
    smtstringz3Theory.seq_concat_middle_singleton,
    smtstringz3Theory.seq_concat_middle_singleton_result,
    smtstringz3Theory.seq_concat_middle_singleton_right,
    smtstringz3Theory.seq_concat_middle_singleton_left
  ]

  fun is_symbolic_string_goal t = mentions_any symbolic_string_names t

  (* Refute inconsistent concat decompositions by exposing their finite list
     representations.  The simplifier considers exactly the constructor
     splits present in the literal/unit lists in the goal, so the work is
     bounded by those input lengths rather than a recorded 2+2-versus-3
     theorem. *)
  fun bounded_concat_split_refute t =
    let
      val (antecedent, consequence) = boolSyntax.dest_imp t
      val _ = Term.aconv consequence boolSyntax.F orelse
        raise ERR "bounded_concat_split_refute"
          "concat split goal does not conclude false"
      val antecedent_thm = Thm.ASSUME antecedent
      val length_tm = Term.prim_mk_const
        {Thy = "smtstring", Name = "smtstr_len"}
      fun length_equality conjunct =
        let
          val equality = simpLib.SIMP_RULE boolSimps.bool_ss
            [smtstringz3Theory.seq_eq_def]
            (Library.conj_elim (antecedent_thm, conjunct))
          val length_equality = Thm.AP_TERM length_tm equality
        in
          simpLib.SIMP_RULE
            (simpLib.++ (bossLib.srw_ss(), numSimps.REDUCE_ss))
            [smtstringz3Theory.seq_unit_length,
             smtstringTheory.smtstr_len_concat]
            length_equality
        end
      val length_equalities =
        List.map length_equality (boolSyntax.strip_conj antecedent)
      val contradiction = Tactical.TAC_PROOF
        ((List.map Thm.concl length_equalities, boolSyntax.F),
         intLib.ARITH_TAC)
      val contradiction = List.foldl
        (fn (premise, proof) => Drule.PROVE_HYP premise proof)
        contradiction length_equalities
    in
      Thm.DISCH antecedent contradiction
    end

  fun symbolic_string_prove t =
    if not (is_symbolic_string_goal t) then
      raise ERR "symbolic_string_prove"
        "no symbolic concat/prefix/suffix/contains term"
    else
      (* E1(b): bounded constructor splitting is general for the literal
         concat-refutation shape and fails loudly outside that family. *)
      profile "string-symbolic(1)(bounded-concat-split)"
        bounded_concat_split_refute t
      handle Feedback.HOL_ERR _ =>
      (* E1(c): redundant middle-singleton cache.  The general symbolic rung
         below searches the same rules when fast paths are disabled. *)
      (Library.require_fastpath "symbolic string middle-singleton";
       profile "string-symbolic(2)(middle-singleton)"
         (fn target => with_metis_limit (fn () =>
           metisLib.METIS_PROVE middle_singleton_lemmas target) ()) t)
      handle Feedback.HOL_ERR _ =>
      (* E1(b): normalization plus bounded first-order search is the general
         symbolic String-family procedure and has a loud failure boundary. *)
      profile "string-symbolic(3)(general)"
        (fn target =>
          (* Some parametric constructor rules match before normalization;
             others need the normalized representation.  Both searches use
             members of the same general lemma set and shared bound.  Try the
             cheapest single-rule search before the full set. *)
          with_metis_limit
            (fn () => metisLib.METIS_PROVE
              [smtstringz3Theory.seq_head_shared_singleton_prefix_right]
              target) ()
          handle Feedback.HOL_ERR _ =>
          (* The middle-singleton rules are stated over 'seq_unit', which
             normalization unfolds.  Keep their ordered search within this
             general symbolic rung, before the normalized representation. *)
          with_metis_limit
            (fn () => metisLib.METIS_PROVE middle_singleton_lemmas target) ()
          handle Feedback.HOL_ERR _ =>
          with_metis_limit
            (fn () => metisLib.METIS_PROVE symbolic_lemmas target) ()
          handle Feedback.HOL_ERR _ =>
            with_metis_limit (fn () =>
              Tactical.prove (target,
                Tactical.THEN
                  (bossLib.RW_TAC
                     (simpLib.++
                       (bossLib.srw_ss(), intSimps.INT_REDUCE_ss))
                     symbolic_normalizations,
                   bossLib.METIS_TAC symbolic_lemmas))) ()) t

  (* General automaton rules only.  Literal states and loop bounds are
     specialized from these at replay time below. *)
  val aut_transition_rules = [
    smtstringz3Theory.aut_accept_range_deriv,
    smtstringz3Theory.aut_accept_loop_deriv,
    smtstringz3Theory.aut_accept_loop_nullable_deriv,
    smtstringz3Theory.aut_accept_range_transition,
    smtstringz3Theory.aut_accept_loop_transition,
    smtstringz3Theory.aut_accept_loop_nullable_transition,
    smtstringz3Theory.aut_accept_comp_transition,
    smtstringz3Theory.aut_accept_comp_range_transition,
    smtstringz3Theory.aut_accept_inter_range_comp_transition,
    smtstringz3Theory.aut_accept_loop_empty
  ]

  val regex_normalizations = [
    smtstringz3Theory.seq_unit_def,
    smtstringTheory.re_nullable_def,
    smtstringTheory.re_deriv_def,
    smtstringTheory.reglan_power_deriv_def,
    smtstringTheory.reglan_loop_deriv_def,
    smtstringTheory.smt_in_re_loop_singleton,
    smtstringTheory.smt_in_re_loop_nullable_singleton,
    smtstringTheory.smt_in_re_loop_empty,
    smtstringTheory.re_deriv_loop_singleton,
    smtstringTheory.re_deriv_loop_nullable_singleton,
    smtstringTheory.smt_in_re_star_allchar,
    smtstringTheory.smt_in_re_plus_allchar,
    smtstringTheory.smt_in_re_def,
    smtstringTheory.smtstr_len_def,
    smtstringz3Theory.aut_accept_zero,
    smtstringz3Theory.aut_accept_transition_int
  ] @ aut_transition_rules @ [
    smtstringz3Theory.aut_accept_comp_transition_seq_unit,
    smtstringz3Theory.aut_accept_inter_transition_seq_unit,
    smtstringz3Theory.aut_accept_loop_nullable_transition_seq_unit_zero,
    smtstringz3Theory.aut_accept_loop_nullable_transition_seq_unit_one,
    smtstringz3Theory.aut_accept_empty,
    smtstringz3Theory.aut_accept_empty_terminal_int
  ]

  val regex_lemmas = [
    smtstringTheory.re_nullable_def,
    smtstringTheory.smt_in_re_loop_singleton,
    smtstringTheory.smt_in_re_loop_nullable_singleton,
    smtstringTheory.smt_in_re_loop_empty,
    smtstringTheory.re_deriv_loop_singleton,
    smtstringTheory.re_deriv_loop_nullable_singleton,
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
    smtstringz3Theory.aut_accept_transition_int
  ] @ aut_transition_rules @ [
    smtstringz3Theory.aut_accept_empty,
    smtstringz3Theory.aut_accept_empty_terminal_int
  ]

  val regex_names =
    const_name_set
      (smtstring_consts "smtstring" ["smt_in_re"] @
       smtstring_consts "smtstringz3" ["aut_accept"])

  (* Length facts are implications whose automaton premise already occurs in
     the goal.  Match the parametric theorem after introducing that premise,
     then reduce only its concrete numeral/code-point side conditions. *)
  val parametric_regex_length_rules = [
    smtstringz3Theory.aut_accept_range_length_int,
    smtstringz3Theory.aut_accept_loop_positive_length_zero,
    smtstringz3Theory.aut_accept_loop_positive_length_seq_unit,
    smtstringz3Theory.aut_accept_plus_allchar_length_one
  ]

  (* Numeral reduction shared by the regex-length and automaton rungs; the
     simpset is built once rather than per replay step. *)
  val regex_reduce_ss = simpLib.++
    (simpLib.++ (boolSimps.bool_ss, numSimps.REDUCE_ss),
     intSimps.INT_REDUCE_ss)

  fun regex_normalize term = Conv.QCONV
    (simpLib.SIMP_CONV regex_reduce_ss [smtstringz3Theory.seq_unit_def])
    term

  fun replay_parametric_regex_length_prove target =
    let
      val target_normalization = regex_normalize target
      val normalized_target =
        boolSyntax.rhs (Thm.concl target_normalization)
      val target_premise =
        Lib.fst (boolSyntax.dest_imp normalized_target)
      fun instantiate rule =
        let
          val rule_premise =
            Lib.fst (boolSyntax.dest_imp (Thm.concl rule))
          fun match_premise premise =
            let
              val normalized_premise =
                boolSyntax.rhs (Thm.concl (regex_normalize premise))
            in
              Term.match_term normalized_premise target_premise
            end
          val substitution =
            Lib.tryfind match_premise (boolSyntax.strip_conj rule_premise)
          val instance = Drule.INST_TY_TERM substitution rule
          val instance = simpLib.SIMP_RULE regex_reduce_ss
            [smtstringz3Theory.seq_unit_def] instance
          val _ = Term.aconv (Thm.concl instance) normalized_target orelse
            raise ERR "replay_parametric_regex_length_prove"
              "specialized length rule has the wrong conclusion"
        in
          Thm.EQ_MP (Thm.SYM target_normalization) instance
        end
    in
      Lib.tryfind instantiate parametric_regex_length_rules
    end

  fun replay_specialized_automaton_prove target =
    let
      val numerals = HOLset.listItems
        (HOLset.addList (Term.empty_tmset,
          HolKernel.find_terms numSyntax.is_numeral target))
      fun controls_arithmetic variable tm =
        let
          val (head, args) = boolSyntax.strip_comb tm
          val controlling =
            (Library.same_const head numSyntax.suc_tm orelse
             Library.same_const head numSyntax.minus_tm) andalso
            List.exists (fn arg =>
              List.exists (Term.aconv variable) (Term.free_vars arg)) args
        in
          controlling orelse
          List.exists (controls_arithmetic variable) args
        end
        handle Feedback.HOL_ERR _ => false
      fun control_vars theorem =
        List.filter (fn variable =>
          Type.compare (Term.type_of variable, numSyntax.num) = EQUAL andalso
          controls_arithmetic variable (Thm.concl theorem))
          (Term.free_vars (Thm.concl theorem))
      fun substitutions [] = [[]]
        | substitutions (variable :: variables) =
            List.concat (List.map (fn numeral =>
              List.map (fn rest => Lib.|-> (variable, numeral) :: rest)
                (substitutions variables)) numerals)
      val target_normalization = regex_normalize target
      val normalized_target =
        boolSyntax.rhs (Thm.concl target_normalization)
      fun instantiate theorem =
        let
          val schema =
            Lib.snd (boolSyntax.dest_imp (Thm.concl theorem))
            handle Feedback.HOL_ERR _ => Thm.concl theorem
          val instance = Drule.INST_TY_TERM
            (Term.match_term schema normalized_target) theorem
          val instance = simpLib.SIMP_RULE regex_reduce_ss
            [smtstringz3Theory.seq_unit_def,
             smtstringz3Theory.aut_accept_loop_empty] instance
          val _ = Term.aconv (Thm.concl instance) normalized_target orelse
            raise ERR "replay_specialized_automaton_prove"
              "specialized transition has the wrong conclusion"
        in
          instance
        end
      (* Candidates are thunks: the control-variable instances are
         combinatorial in the numerals, and at most one is ever used. *)
      fun control_instances theorem =
        (fn () => theorem) :: List.map (fn substitution => fn () =>
          simpLib.SIMP_RULE regex_reduce_ss
            [smtstringz3Theory.aut_accept_loop_empty]
            (Thm.INST substitution theorem))
          (substitutions (control_vars theorem))
      val candidates =
        List.concat (List.map control_instances aut_transition_rules)
      val theorem =
        Lib.tryfind (fn candidate => instantiate (candidate ())) candidates
    in
      Thm.EQ_MP (Thm.SYM target_normalization) theorem
    end

  fun is_regex_goal t = mentions_any regex_names t

  fun regex_prove t =
    if not (is_regex_goal t) then
      raise ERR "regex_prove" "no regex membership or aut.accept term"
    else
      (* E1(b): general instantiation for the named parametric regex-length
         schemas, with a loud shape boundary. *)
      profile "regex(1)(parametric-length)"
        replay_parametric_regex_length_prove t
      handle Feedback.HOL_ERR _ =>
      (* E1(b): finite specialization of the named automaton schemas over
         numerals present in the target, with a loud boundary. *)
      profile "regex(2)(specialized-automaton)"
        replay_specialized_automaton_prove t
      handle Feedback.HOL_ERR _ =>
      (* E1(b): bounded first-order search over the complete named regex
         lemma set used by this replay family. *)
      profile "regex(3)(bounded-metis)"
        (fn target => with_metis_limit
          (fn () => metisLib.METIS_PROVE regex_lemmas target) ()) t
      handle Feedback.HOL_ERR _ =>
      (* E1(b): the general normalized regex/automaton procedure is terminal
         for the family and fails loudly when it cannot reconstruct a fact. *)
      profile "regex(4)(normalized-metis)"
        (fn target => with_metis_limit (fn () =>
          Tactical.prove (target,
            Tactical.THEN
              (bossLib.RW_TAC
                 (simpLib.++ (bossLib.srw_ss(), intSimps.INT_REDUCE_ss))
                 regex_normalizations,
              bossLib.METIS_TAC regex_lemmas))) ()) t

  (* `rewrite` steps are a separate customer of the string theory.  Keep
     their entry point narrow: a failed string attempt must not turn an
     ordinary arithmetic rewrite into a string diagnostic. *)
  val string_theory_names =
    const_name_set
      (smtstring_consts "smtstring"
         ["smtstr_concat", "smtstr_len", "smtstr_substr", "smtstr_update",
          "smtstr_rev", "smtstr_at", "smtstr_prefixof", "smtstr_suffixof",
          "smtstr_contains",
          "smtstr_indexof", "smtstr_lt", "smtstr_le", "smtstr_replace",
          "smtstr_replace_all", "smtstr_replace_re",
          "smtstr_replace_re_all", "smtstr_is_digit", "smtstr_to_code",
          "smtstr_from_code", "smtstr_to_int", "smtstr_from_int",
          "smt_in_re", "reglan_to_re", "reglan_concat", "reglan_union",
          "reglan_inter", "reglan_diff", "reglan_comp", "reglan_star",
          "reglan_plus", "reglan_opt", "reglan_range", "reglan_power",
          "reglan_loop"] @
       smtstring_consts "smtstringz3"
         ["seq_unit", "seq_tail", "seq_eq", "seq_nth_i", "seq_stoi",
          "seq_digit", "char_is_digit", "char_bit", "aut_state",
          "aut_accept"])

  fun has_string_theory_term t = mentions_any string_theory_names t

  (* These are semantic rewrite facts, rather than a general-purpose simp
     set.  In particular, do not include METIS here: each rewrite rung must
     reconstruct the recorded equality by a targeted conversion. *)
  val rewrite_normalizations = [
    smtstringTheory.smtstr_concat_def,
    smtstringTheory.smtstr_concat_assoc,
    smtstringTheory.smtstr_concat_nil_left,
    smtstringTheory.smtstr_concat_nil_right,
    smtstringTheory.smtstr_update_def,
    smtstringTheory.smtstr_rev_def,
    smtstringTheory.smtstr_len_concat,
    smtstringTheory.smtstr_len_eq_zero,
    smtstringTheory.smtstr_prefixof_refl,
    smtstringTheory.smtstr_suffixof_refl,
    smtstringTheory.smtstr_contains_refl,
    smtstringTheory.smtstr_lt_irrefl,
    smtstringTheory.smtstr_le_refl,
    smtstringTheory.smtstr_lt_imp_le,
    smtstringTheory.smt_in_re_deriv,
    smtstringz3Theory.seq_unit_def,
    smtstringz3Theory.seq_tail_def,
    smtstringz3Theory.seq_eq_def,
    smtstringz3Theory.seq_nth_i_compute,
    smtstringz3Theory.char_is_digit_def,
    smtstringz3Theory.seq_digit_def,
    smtstringz3Theory.seq_stoi_def,
    smtstringz3Theory.aut_state_def,
    smtstringz3Theory.aut_accept_compute
  ]

  val contextual_normalizations =
    ground_eval_thms @ rewrite_normalizations @ regex_normalizations

  (* Contextual rung: the recorded conclusion follows from the assertion
     context by simplification with the shared string-theory rule sets.
     Callers order this after the rewrite and theory rungs. *)
  fun string_contextual_prove context target =
    let
      val _ = List.app
        (SmtResource.check_resource_goal "String" "contextual") context
    in
      with_string_budget "contextual" (fn target =>
        Tactical.TAC_PROOF ((context, target),
          bossLib.ASM_SIMP_TAC
            (simpLib.++ (bossLib.srw_ss(), intSimps.INT_REDUCE_ss))
            contextual_normalizations)) target
    end

  fun rewrite_simp_prove t =
    simpLib.SIMP_PROVE
      (simpLib.++ (bossLib.srw_ss(), intSimps.INT_REDUCE_ss))
      rewrite_normalizations t
    handle Feedback.HOL_ERR _ =>
      raise ERR "rewrite_simp_prove"
        "string rewrite normalization did not close the conclusion"

  val regex_rewrite_names =
    const_name_set
      (smtstring_consts "smtstring"
         ["reglan_to_re", "reglan_none", "reglan_all", "reglan_allchar",
          "reglan_concat", "reglan_union", "reglan_inter", "reglan_diff",
          "reglan_comp", "reglan_star", "reglan_plus", "reglan_opt",
          "reglan_range", "reglan_power", "reglan_loop"])

  fun has_regex_rewrite_term t = mentions_any regex_rewrite_names t

  fun rewrite_evaluation_prove t =
    if has_regex_rewrite_term t andalso not (is_regex_goal t) then
      (* Regex constructor equalities are normalized structurally.  Sending
         them through CBV unfolds the derivative engine unnecessarily. *)
      rewrite_simp_prove t
    else if List.null (Term.free_vars t) then
      ground_eval_prove t
    else
      raise ERR "rewrite_ground_eval_prove"
        "ground evaluation requires a closed conclusion"

  (* The ordering is intentional and mirrors `string_prove`: executable
     evaluation precedes the small, named normalization set above. *)
  fun string_rewrite_prove t =
    with_string_budget "rewrite" (fn t =>
      if not (has_string_theory_term t) then
        raise ERR "string_rewrite_prove" "no Unicode-string term"
      else
        (* E1(a): executable evaluation is complete for closed String/regex
           constructor equalities (and structural regex constructors). *)
        profile "string-rewrite(1)(ground-eval)"
          rewrite_evaluation_prove t
        handle Feedback.HOL_ERR holerr =>
        (rethrow_resource holerr;
         (* E1(b): the named semantic String normalization family is general
            for its rewrite set and fails loudly outside it. *)
         profile "string-rewrite(2)(normalization)"
           rewrite_simp_prove t)) t

  fun string_prove arith_prove t =
    with_string_budget "replay" (fn t =>
      let val () = check_seq_type t in
        (* E1(a): CBV decides the closed executable String fragment. *)
        profile "string(1)(ground-eval)" ground_eval_prove t
        handle Feedback.HOL_ERR holerr =>
        (rethrow_resource holerr;
         (* E1(b): length normalization followed by the supplied arithmetic
            procedure is general for the selected length family. *)
         profile "string(2)(length-arith)"
           (length_arith_prove arith_prove) t)
        handle Feedback.HOL_ERR holerr =>
        (rethrow_resource holerr;
         (* E1(b): the symbolic sub-ladder is general for selected concat,
            prefix, suffix and contains clauses, with loud refusal. *)
         profile "string(3)(symbolic)" symbolic_string_prove t)
        handle Feedback.HOL_ERR holerr =>
        (rethrow_resource holerr;
         (* E1(b): the regex sub-ladder is general for selected membership
            and aut.accept clauses, with loud refusal. *)
         profile "string(4)(regex)" regex_prove t)
        handle Feedback.HOL_ERR holerr =>
        (rethrow_resource holerr;
         (* E1(b): terminal loud String/regex family boundary. *)
         profile "string(5)(unsupported)" (unsupported "seq") t)
      end) t

  (* Z3 shares each tail of its bitwise comparison through proof lets.
     Parsing expands those lets, so compact the Boolean recurrence
     top-down before bit-blasting to keep the checked term linear. *)
  val compact_char_compare =
    tautLib.TAUT_PROVE
      ``((~d /\ c) \/ (~d /\ r) \/ (c /\ r)) =
        ((c /\ ~d) \/ ((c = d) /\ r))``

  val char_decomposition_names =
    const_name_set
      (smtstring_consts "smtstringz3" ["char_bit", "char_is_digit"] @
       smtstring_consts "words" ["word_or"])

  fun char_bitblast_prove t =
    let
      val _ =
        if mentions_any char_decomposition_names t then ()
        else raise ERR "char_prove" "no char decomposition atom"
      val compacted =
        Conv.TRY_CONV
          (Conv.TOP_DEPTH_CONV
            (Conv.REWR_CONV compact_char_compare)) t
        handle Conv.UNCHANGED => Thm.REFL t
             | Feedback.HOL_ERR _ => Thm.REFL t
      val compacted_t = boolSyntax.rhs (Thm.concl compacted)
      val simplified =
        simpLib.SIMP_CONV
          (simpLib.++ (bossLib.srw_ss(), wordsLib.WORD_BIT_EQ_ss))
          [smtstringz3Theory.char_bit_word18,
           smtstringz3Theory.char_is_digit_word18,
           smtstringz3Theory.char_le_word18] compacted_t
      val normalized = Thm.TRANS compacted simplified
      val t' = boolSyntax.rhs (Thm.concl normalized)
      val thm = Tactical.prove (t', blastLib.BBLAST_TAC)
    in
      Thm.EQ_MP (Thm.SYM normalized) thm
    end

  fun char_prove t =
    with_string_budget "char-bitblast" (fn t =>
      (* E1(a): normalization plus BBLAST decides the selected 18-bit
         character-decomposition formula fragment. *)
      profile "char(1)(bitblast)" char_bitblast_prove t
      handle Feedback.HOL_ERR holerr =>
        (rethrow_resource holerr;
         (* E1(b): terminal loud character-family boundary. *)
         profile "char(2)(unsupported)" (unsupported "char") t)) t

end
