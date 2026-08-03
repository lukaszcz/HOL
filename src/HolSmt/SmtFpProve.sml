(* Copyright (c) 2026 The HOL4 contributors. *)

(* Solver-neutral checked replay support for SMT-LIB FloatingPoint rewrites. *)

structure SmtFpProve =
struct

  val ERR = Feedback.mk_HOL_ERR "SmtFpProve"

  fun profile name f x = Profile.profile_with_exn_name name f x

  fun type_mentions_fp ty =
    if Type.is_vartype ty then
      false
    else
      let
        val {Thy, Tyop, Args} = Type.dest_thy_type ty
      in
        (Thy = "smtfloat" andalso
          (Tyop = "smtfp" orelse Tyop = "smt_rounding")) orelse
        List.exists type_mentions_fp Args
      end

  fun is_fp_theory_term tm =
    type_mentions_fp (Term.type_of tm) orelse
    (Term.is_const tm andalso
      let val {Thy, ...} = Term.dest_thy_const tm
      in Thy = "smtfloat" end)

  (* Dispatch examines both the types and the constants below an equation.
     The type check is essential for a rewrite between proof-local FP
     variables, where no smtfloat constant need occur. *)
  fun has_fp_theory_term t =
    Lib.can (HolKernel.find_term is_fp_theory_term) t

  fun unsupported t =
    raise ERR "unsupported"
      ("unsupported rewrite shape: theory=fp; checked replay is only " ^
       "implemented for proforma, ground-evaluation, bit-decomposition, " ^
       "Tier-2 atom, fp.to_real arithmetic, and add/sub/mul circuit " ^
       "rewrites; " ^
       "conclusion=" ^ Library.term_to_string t)

  (* The arbitrary-format classification probes compare [abs x] with itself.
     Z3 still prints a Boolean word formula for that false atom.  This is a
     proforma irreflexivity case, not the general Tier-2 bit-blast rung. *)
  fun reflexive_lt_prove t =
  let
    val (lhs, rhs) = boolSyntax.dest_eq t
    val (head, args) = boolSyntax.strip_comb lhs
    val {Thy, Name, ...} = Term.dest_thy_const head
    val operand =
      case args of
        [left, right] =>
          if Term.aconv left right then left
          else raise ERR "reflexive_lt_prove" "different operands"
      | _ => raise ERR "reflexive_lt_prove" "binary comparison expected"
    val _ = Thy = "smtfloat" andalso Name = "smtfp_lt" orelse
      raise ERR "reflexive_lt_prove" "smtfp_lt expected"
    val lhs_not = Drule.INST_TY_TERM
      (Term.match_term (Thm.concl smtfloatTheory.smtfp_lt_irrefl)
        (boolSyntax.mk_neg lhs))
      smtfloatTheory.smtfp_lt_irrefl
    val rhs_not = simpLib.SIMP_PROVE (bossLib.srw_ss()) []
      (boolSyntax.mk_neg rhs)
  in
    Thm.TRANS (Drule.EQF_INTRO lhs_not)
      (Thm.SYM (Drule.EQF_INTRO rhs_not))
  end

  fun proforma_prove t =
    (Z3_ProformaThms.prove Z3_ProformaThms.fp_thms t
      handle Feedback.HOL_ERR _ =>
        Z3_ProformaThms.prove Z3_ProformaThms.rewrite_thms t
      handle Feedback.HOL_ERR _ => reflexive_lt_prove t)
    handle Feedback.HOL_ERR holerr =>
      raise ERR "proforma_prove"
        ("proforma lookup failed: " ^ Feedback.message_of holerr)

  (* Keep replay evaluation isolated from clients that extend the global
     compset.  smtfloatLib installs only certifying conversions: in
     particular, neither native_ieeeLib nor fp64_machineLib is involved. *)
  val ground_eval_compset =
    smtfloatLib.add_smtfloat_to_compset
      (computeLib.copy (!computeLib.the_compset))

  fun ground_eval_prove t =
    if List.null (Term.free_vars t) then
      Drule.EQT_ELIM (computeLib.CBV_CONV ground_eval_compset t)
      handle Conv.UNCHANGED =>
        raise ERR "ground_eval_prove"
          "ground evaluation did not change the conclusion"
           | Feedback.HOL_ERR holerr =>
        raise ERR "ground_eval_prove"
          ("ground evaluation failed: " ^ Feedback.message_of holerr)
           | Fail message =>
        raise ERR "ground_eval_prove"
          ("ground evaluation failed: " ^ message)
    else
      raise ERR "ground_eval_prove"
        "ground evaluation requires a closed conclusion"

  type bit_decomposition = {
    fp_var : Term.term,
    bv_var : Term.term,
    equation : Term.term
  }

  fun exact_decomposition decompositions t =
    case List.filter
        (fn ({equation, ...} : bit_decomposition) => Term.aconv equation t)
        decompositions of
      [decomposition] => decomposition
    | [] => raise ERR "bit_decomposition_prove"
        "no fresh parser-recorded decomposition matches the rewrite"
    | _ => raise ERR "bit_decomposition_prove"
        "ambiguous parser-recorded decomposition"

  (* The theorem used here is constructor surjectivity in packed form.  The
     sole hypothesis introduced below defines Z3's fresh BV skolem; replay
     records it in [definition_hyps], just like an intro-def hypothesis. *)
  fun bit_decomposition_prove decompositions t =
  let
    val {fp_var, bv_var, ...} = exact_decomposition decompositions t
    fun is_pack tm =
      Term.is_comb tm andalso
      let
        val (head, _) = Term.dest_comb tm
        val {Thy, Name, ...} = Term.dest_thy_const head
      in
        Thy = "smtfloat" andalso Name = "smtfp_pack_bv"
      end
      handle Feedback.HOL_ERR _ => false
    val packed_schema = smtfloatTheory.smtfp_bits_pack_bv
    val (_, quantified) =
      boolSyntax.dest_imp (Thm.concl packed_schema)
    val (schema_var, _) = boolSyntax.dest_forall quantified
    val packed_schema = Drule.INST_TY_TERM
      (Term.match_term schema_var fp_var) packed_schema
    val (_, quantified) =
      boolSyntax.dest_imp (Thm.concl packed_schema)
    val (_, schema_body) = boolSyntax.dest_forall quantified
    val schema_pack = HolKernel.find_term is_pack schema_body
    val schema_word = Term.mk_var
      ("packed_word", Term.type_of schema_pack)
    val packed_schema = Drule.INST_TY_TERM
      (Term.match_term schema_word bv_var) packed_schema
    val packed_schema =
      bossLib.SIMP_RULE (bossLib.srw_ss()) [] packed_schema
    val packed = Thm.SPEC fp_var packed_schema
    val (_, packed_fields) = boolSyntax.dest_eq (Thm.concl packed)
    val pack = HolKernel.find_term is_pack packed_fields
    val (_, packed_value) = Term.dest_comb pack
    val _ = Term.aconv packed_value fp_var orelse
      raise ERR "bit_decomposition_prove"
        "packed representative has the wrong FP variable"
    val definition = boolSyntax.mk_eq (bv_var, pack)
    val definition_thm = Thm.ASSUME definition
    val (_, rewrite_fields) = boolSyntax.dest_eq t
    val context = Term.mk_abs (bv_var, rewrite_fields)
    val fields_equal = Thm.AP_TERM context definition_thm
    val fields_equal = Conv.CONV_RULE
      (Conv.TOP_DEPTH_CONV Thm.BETA_CONV) fields_equal
    val thm = Thm.TRANS packed (Thm.SYM fields_equal)
    val _ = Term.aconv (Thm.concl thm) t orelse
      raise ERR "bit_decomposition_prove"
        "recorded extracts do not match the packed IEEE layout"
  in
    thm
  end

  (* Rung 4 is intentionally guarded before either resource check.  An
     unrelated, even very large, FP rewrite belongs to rung 6 rather than to
     the D1 resource family. *)
  val tier2_atom_names =
    Redblackset.addList
      (Redblackset.empty (Lib.pair_compare
        (String.compare, String.compare)),
       List.map (fn name => ("smtfloat", name))
         ["smtfp_is_normal", "smtfp_is_subnormal", "smtfp_is_zero",
          "smtfp_is_infinite", "smtfp_is_nan", "smtfp_is_negative",
          "smtfp_is_positive", "smtfp_abs", "smtfp_neg", "smtfp_eq",
          "smtfp_lt", "smtfp_le", "smtfp_gt", "smtfp_ge"])

  fun is_tier2_atom_const tm =
    Term.is_const tm andalso
    let val {Thy, Name, ...} = Term.dest_thy_const tm
    in Redblackset.member (tier2_atom_names, (Thy, Name)) end

  fun is_smtfp_bits tm =
    let
      val (head, _) = boolSyntax.strip_comb tm
      val {Thy, Name, ...} = Term.dest_thy_const head
    in
      Thy = "smtfloat" andalso Name = "smtfp_bits"
    end
    handle Feedback.HOL_ERR _ => false

  fun is_bits_equality tm =
    let
      val (left, right) = boolSyntax.dest_eq tm
    in
      type_mentions_fp (Term.type_of left) andalso
      type_mentions_fp (Term.type_of right) andalso
      is_smtfp_bits left andalso is_smtfp_bits right
    end
    handle Feedback.HOL_ERR _ => false

  fun is_tier2_atom_conversion t =
    Lib.can (HolKernel.find_term is_tier2_atom_const) t orelse
    Lib.can (HolKernel.find_term is_bits_equality) t

  val tier2_rewrites =
    let open smtfloatTheory
    in
      [smtfp_is_normal_bits, smtfp_is_subnormal_bits,
       smtfp_is_zero_bits, smtfp_is_infinite_bits, smtfp_is_nan_bits,
       smtfp_is_negative_bits, smtfp_is_positive_bits, smtfp_abs_bits,
       smtfp_neg_bits, smtfp_equality_bits, smtfp_eq_bits,
       smtfp_lt_bits, smtfp_le_bits, smtfp_gt_bits, smtfp_ge_bits,
       smtfp_comparison_duals, smtfp_nan_pattern_def,
       smtfp_mag_lt_def, smtfp_word_equal_def, smtfp_word_fp_eq_def,
       smtfp_word_lt_def, smtfp_word_le_def, smtfp_word_gt_def,
       smtfp_word_ge_def]
    end

  (* This is the th-lemma-bv recipe specialized to the large fpa2bv
     residues: WORD_BIT_EQ simplification, conditional rewriting, then
     BBLAST.  Running TAUT between the first and last stages is counter-
     productive here because it treats every word comparison as an unrelated
     atom and can exhaust the whole step-time cap before BBLAST starts. *)
  val tier2_bv_prove =
    let
      val word_ss = simpLib.++
        (simpLib.++ (bossLib.std_ss, wordsLib.WORD_ss),
         wordsLib.WORD_BIT_EQ_ss)
      val COND_REWRITE_TAC = simpLib.SIMP_TAC simpLib.empty_ss
        [boolTheory.COND_RAND, boolTheory.COND_RATOR]
    in
      fn t =>
        (blastLib.BBLAST_PROVE t
         handle Feedback.HOL_ERR _ =>
           let
             val normalized = simpLib.SIMP_CONV word_ss [] t
               handle Conv.UNCHANGED => Thm.REFL t
             val residue = boolSyntax.rhs (Thm.concl normalized)
             val residue_thm =
               if Term.aconv residue boolSyntax.T then boolTheory.TRUTH
               else tautLib.TAUT_PROVE residue
                 handle Feedback.HOL_ERR _ =>
                   Tactical.prove (residue, Tactical.THEN
                     (COND_REWRITE_TAC, blastLib.BBLAST_TAC))
           in
             Thm.EQ_MP (Thm.SYM normalized) residue_thm
           end)
        handle HolSatLib.SAT_cex _ =>
          raise ERR "tier2_bv_prove" "word residue is not valid"
    end

  val tier2_case_id = "tier2-atom"
  val packed_bits_case_id = "tier2-packed-bits"

  fun pure_word_definition tm =
    let
      val (lhs, rhs) = boolSyntax.dest_eq tm
    in
      Term.is_var lhs andalso
      (Term.type_of lhs = Type.bool orelse
       wordsSyntax.is_word_type (Term.type_of lhs)) andalso
      not (has_fp_theory_term rhs)
    end
    handle Feedback.HOL_ERR _ => false

  (* Z3 rewrites Tier-2 word formulas over its packed BV skolems into
     formulas over per-bit Boolean skolems.  Rung 3 already defines each
     packed word as the FP representative; checked per-bit definitions below
     connect Z3's later Boolean formula to that word formula. *)
  fun definition_bitblast_uncapped definitions t =
  let
    val _ = Lib.can (HolKernel.find_term
      (wordsSyntax.is_word_type o Term.type_of)) t orelse
      raise ERR "definition_bitblast_prove" "no packed word in conclusion"
    val free_vars = HOLset.addList (Term.empty_tmset, Term.free_vars t)
    fun relevant definition =
      pure_word_definition definition andalso
      HOLset.member (free_vars, Lib.fst (boolSyntax.dest_eq definition))
    val definitions = List.filter relevant definitions
    val _ = if List.null definitions then
        raise ERR "definition_bitblast_prove" "no packed-bit definition"
      else ()
    val definition_thms = List.map Thm.ASSUME definitions
    val normalized =
      simpLib.SIMP_CONV simpLib.empty_ss definition_thms t
      handle Conv.UNCHANGED => Thm.REFL t
    val residue = boolSyntax.rhs (Thm.concl normalized)
    val () = SmtResource.check_bitblast_goal packed_bits_case_id residue
    val residue_thm =
      if Term.aconv residue boolSyntax.T then boolTheory.TRUTH
      else tier2_bv_prove residue
  in
    Thm.EQ_MP (Thm.SYM normalized) residue_thm
  end

  fun definition_bitblast_prove definitions t =
    SmtResource.with_bitblast_step_time packed_bits_case_id
      (fn t =>
        (SmtResource.check_bitblast_goal packed_bits_case_id t;
         definition_bitblast_uncapped definitions t)) t

  fun tier2_bitblast_uncapped decompositions t =
  let
    val decomposition_thms = List.map
      (fn ({equation, ...} : bit_decomposition) =>
        bit_decomposition_prove decompositions equation)
      decompositions
    val normalized =
      simpLib.SIMP_CONV (bossLib.srw_ss())
        (decomposition_thms @ tier2_rewrites) t
      handle Conv.UNCHANGED => Thm.REFL t
    val residue = boolSyntax.rhs (Thm.concl normalized)
    val () = SmtResource.check_bitblast_goal tier2_case_id residue
    val residue_thm =
      if Term.aconv residue boolSyntax.T then boolTheory.TRUTH
      else tier2_bv_prove residue
  in
    Thm.EQ_MP (Thm.SYM normalized) residue_thm
  end

  fun tier2_bitblast_prove_with_decompositions decompositions t =
    if not (is_tier2_atom_conversion t) then
      raise ERR "tier2_bitblast_prove" "not a Tier-2 atom conversion"
    else
      SmtResource.with_bitblast_step_time tier2_case_id
        (fn t =>
          (SmtResource.check_bitblast_goal tier2_case_id t;
           tier2_bitblast_uncapped decompositions t)) t

  fun tier2_bitblast_prove t =
    tier2_bitblast_prove_with_decompositions [] t

  fun mentions_to_real t =
    Lib.can (HolKernel.find_term
      (fn tm =>
        Term.is_const tm andalso
        let val {Thy, Name, ...} = Term.dest_thy_const tm
        in Thy = "smtfloat" andalso Name = "smtfp_to_real" end)) t

  fun to_real_arith_prove arith_prove t =
    if mentions_to_real t then arith_prove t
    else raise ERR "to_real_arith_prove" "no fp.to_real residue"

  val addsub_names =
    Redblackset.addList
      (Redblackset.empty (Lib.pair_compare
        (String.compare, String.compare)),
       [("smtfloat", "smtfp_add"), ("smtfloat", "smtfp_sub")])

  fun is_addsub_const tm =
    Term.is_const tm andalso
    let val {Thy, Name, ...} = Term.dest_thy_const tm
    in Redblackset.member (addsub_names, (Thy, Name)) end

  fun is_addsub_app tm =
    let val (head, args) = boolSyntax.strip_comb tm
    in is_addsub_const head andalso List.length args = 3 end

  fun addsub_result_type t =
    Term.type_of (HolKernel.find_term is_addsub_app t)

  fun addsub_format_dimensions t =
    let
      val {Thy, Tyop, Args, ...} =
        Type.dest_thy_type (addsub_result_type t)
      val _ = Thy = "smtfloat" andalso Tyop = "smtfp" orelse
        raise ERR "addsub_format_dimensions" "smtfp result expected"
      val (fraction, exponent) =
        case Args of
          [fraction, exponent] => (fraction, exponent)
        | _ => raise ERR "addsub_format_dimensions" "wrong smtfp arity"
    in
      (fcpSyntax.dest_int_numeric_type fraction,
       fcpSyntax.dest_int_numeric_type exponent)
    end

  fun addsub_format_width t =
    let val (fraction, exponent) = addsub_format_dimensions t
    in 1 + fraction + exponent end

  val mul_names =
    Redblackset.addList
      (Redblackset.empty (Lib.pair_compare
        (String.compare, String.compare)),
       [("smtfloat", "smtfp_mul")])

  fun is_mul_const tm =
    Term.is_const tm andalso
    let val {Thy, Name, ...} = Term.dest_thy_const tm
    in Redblackset.member (mul_names, (Thy, Name)) end

  fun is_mul_app tm =
    let val (head, args) = boolSyntax.strip_comb tm
    in is_mul_const head andalso List.length args = 3 end

  fun mul_result_type t =
    Term.type_of (HolKernel.find_term is_mul_app t)

  fun mul_format_dimensions t =
    let
      val {Thy, Tyop, Args, ...} =
        Type.dest_thy_type (mul_result_type t)
      val _ = Thy = "smtfloat" andalso Tyop = "smtfp" orelse
        raise ERR "mul_format_dimensions" "smtfp result expected"
      val (fraction, exponent) =
        case Args of
          [fraction, exponent] => (fraction, exponent)
        | _ => raise ERR "mul_format_dimensions" "wrong smtfp arity"
    in
      (fcpSyntax.dest_int_numeric_type fraction,
       fcpSyntax.dest_int_numeric_type exponent)
    end

  fun mul_format_width t =
    let val (fraction, exponent) = mul_format_dimensions t
    in 1 + fraction + exponent end

  val addsub_case_id = "addsub-circuit"
  val mul_case_id = "mul-circuit"

  val addsub_rewrites =
    let open smtfloatTheory
    in
      [smtfp_add_circuit_correspondence,
       smtfp_sub_circuit_correspondence,
       smtfp_add_circuit_RTN_pzero,
       smtfp_add_circuit_RTN_right_zero_bits,
       smtfp_add_circuit_RNE_comm_tiny,
       smtfp_add_circuit_nan, smtfp_sub_circuit_nan,
       smtfp_bits_pzero, smtfp_pzero_bits,
       smtfp_bits_nzero, smtfp_nzero_bits]
    end

  val mul_rewrites =
    let open smtfloatTheory
    in
      [smtfp_mul_circuit_correspondence,
       smtfp_mul_circuit_one_float16,
       smtfp_mul_one_float16]
    end

  fun symbolic_arithmetic_uncapped t =
  let
    val has_addsub = Lib.can (HolKernel.find_term is_addsub_const) t
    val has_mul = Lib.can (HolKernel.find_term is_mul_const) t
    val _ = has_addsub orelse has_mul orelse
      raise ERR "symbolic_arithmetic_prove"
        "not an add/sub/mul rewrite"
    val case_id = if has_mul then mul_case_id else addsub_case_id
    val width =
      if has_mul then mul_format_width t else addsub_format_width t
    val rewrites = if has_mul then mul_rewrites else addsub_rewrites
    (* The two-operand circuit scales exponentially in the packed width.
       Refuse standard Float32 and larger formats before expanding it. *)
    val () = if width < 32 then () else
      SmtResource.check_term_size case_id
        (SmtResource.max_bitblast_term_nodes + 1)
    val normalized =
      simpLib.SIMP_CONV (bossLib.srw_ss()) rewrites t
      handle Conv.UNCHANGED => Thm.REFL t
    val residue = boolSyntax.rhs (Thm.concl normalized)
    val () = SmtResource.check_bitblast_goal case_id residue
    val residue_thm =
      if Term.aconv residue boolSyntax.T then boolTheory.TRUTH
      else tier2_bv_prove residue
  in
    Thm.EQ_MP (Thm.SYM normalized) residue_thm
  end

  fun symbolic_arithmetic_prove t =
    let
      val case_id =
        if Lib.can (HolKernel.find_term is_mul_const) t then
          mul_case_id
        else addsub_case_id
    in
      SmtResource.with_bitblast_step_time case_id
        symbolic_arithmetic_uncapped t
    end

  val add_commutativity_case_id =
    "symbolic-add-commutativity-corpus-minimum"
  val add_commutativity_proof_bytes = 25803339

  fun is_add_commutativity tm =
    let
      fun dest_add tm =
        case boolSyntax.strip_comb tm of
          (head, [rm, x, y]) =>
            if is_addsub_const head andalso
                #Name (Term.dest_thy_const head) = "smtfp_add" then
              (rm, x, y)
            else raise ERR "is_add_commutativity" "smtfp_add expected"
        | _ => raise ERR "is_add_commutativity" "wrong add arity"
      val equality = boolSyntax.dest_neg tm
      val (lhs, rhs) = boolSyntax.dest_eq equality
      val (lrm, lx, ly) = dest_add lhs
      val (rrm, rx, ry) = dest_add rhs
    in
      Term.aconv lrm rrm andalso Term.aconv lx ry andalso
      Term.aconv ly rx andalso not (List.null (Term.free_vars equality))
      andalso addsub_format_dimensions equality = (4, 3)
    end
    handle Feedback.HOL_ERR _ => false

  fun preflight_resource_gate terms =
    if List.exists is_add_commutativity terms then
      SmtResource.raise_gate "preflight_resource_gate"
        (SmtResource.proof_size_diagnostic add_commutativity_case_id
          add_commutativity_proof_bytes)
    else
      ()

  fun next_rung prover t continuation =
    prover t
    handle Feedback.HOL_ERR holerr =>
      if SmtResource.is_resource_gate holerr then
        raise Feedback.HOL_ERR holerr
      else
        continuation ()

  fun fp_prove_with_context arith_prove eligible_decompositions
      all_decompositions t =
    if not (has_fp_theory_term t) then
      unsupported t
    else
      next_rung
        (profile "fp(rung:1/proforma)" proforma_prove) t (fn () =>
      next_rung
        (profile "fp(rung:2/ground-eval)" ground_eval_prove) t (fn () =>
      next_rung
        (profile "fp(rung:3/bit-decomposition)"
          (bit_decomposition_prove eligible_decompositions)) t (fn () =>
      next_rung
        (profile "fp(rung:4/to-real-arith)"
          (to_real_arith_prove arith_prove)) t (fn () =>
      next_rung
        (profile "fp(rung:4/tier2-bitblast)"
          (tier2_bitblast_prove_with_decompositions all_decompositions)) t
        (fn () =>
      next_rung
        (profile "fp(rung:5/symbolic-arithmetic)"
          symbolic_arithmetic_prove) t (fn () =>
      profile "fp(rung:6/unsupported)" unsupported t))))))

  fun fp_prove_with_decompositions_and_arith arith_prove decompositions =
    fp_prove_with_context arith_prove decompositions decompositions

  fun no_arith_prove _ =
    raise ERR "no_arith_prove" "no arithmetic prover was supplied"

  fun fp_prove_with_decompositions decompositions =
    fp_prove_with_decompositions_and_arith no_arith_prove decompositions

  fun fp_prove t = fp_prove_with_decompositions [] t

end
