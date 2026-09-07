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
      ("unsupported rewrite shape: theory=fp; supported fragment: proved " ^
       "proforma rewrites, closed executable FP terms, parser-recorded " ^
       "packed decompositions, selected symbolic FP predicates, " ^
       "comparisons, and abs/neg conversions, fp.to_real arithmetic, " ^
       "and symbolic add/sub/mul circuits below packed width 32; " ^
       "capability refusal: symbolic FP operations outside those named " ^
       "families or identities outside the proved schemas have no " ^
       "checked reconstruction procedure; resource refusal: selected " ^
       "symbolic predicates, comparisons, and abs/neg conversions and " ^
       "add/sub/mul circuits can exceed the term-size or time caps, and " ^
       "symbolic add/sub/mul at packed width 32 or greater is refused; " ^
       "conclusion=" ^ Library.term_to_string t)

  (* The arbitrary-format classification probes compare [abs x] with itself.
     Z3 still prints a Boolean word formula for that false atom.  The general
     Tier-2 bit-blast rung closes this family; this direct irreflexivity proof
     is only its D1-gated performance cache. *)
  fun reflexive_lt_prove_unbounded t =
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

  fun reflexive_lt_prove t =
    Library.require_fastpath "FP reflexive less-than" t
      (profile "fp(1)(reflexive-lt)" reflexive_lt_prove_unbounded) t

  fun proforma_prove t =
    ((Z3_ProformaThms.prove Z3_ProformaThms.fp_thms t
      handle Feedback.HOL_ERR _ =>
        Z3_ProformaThms.prove Z3_ProformaThms.rewrite_thms t
      handle Feedback.HOL_ERR _ =>
        reflexive_lt_prove t))
    handle Feedback.HOL_ERR holerr =>
      raise ERR "proforma_prove"
        ("proforma lookup failed: " ^ Feedback.message_of holerr)

  (* Keep replay evaluation isolated from clients that extend the global
     compset.  smtfloatLib installs only certifying conversions: in
     particular, neither native_ieeeLib nor fp64_machineLib is involved. *)
  val ground_eval_compset =
    smtfloatLib.add_smtfloat_to_compset
      (computeLib.copy (computeLib.the_compset()))

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

  (* fp(5)(tier2-bitblast) is intentionally guarded before either resource
     check.  An unrelated, even very large, FP rewrite belongs to the
     fp(7)(unsupported) boundary rather than to the D12 resource family. *)
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
      [smtfloatTheory.smtfp_is_normal_bits,
       smtfloatTheory.smtfp_is_subnormal_bits,
       smtfloatTheory.smtfp_is_zero_bits,
       smtfloatTheory.smtfp_is_infinite_bits,
       smtfloatTheory.smtfp_is_nan_bits,
       smtfloatTheory.smtfp_is_negative_bits,
       smtfloatTheory.smtfp_is_positive_bits,
       smtfloatTheory.smtfp_abs_bits,
       smtfloatTheory.smtfp_neg_bits,
       smtfloatTheory.smtfp_equality_bits,
       smtfloatTheory.smtfp_eq_bits,
       smtfloatTheory.smtfp_lt_bits,
       smtfloatTheory.smtfp_le_bits,
       smtfloatTheory.smtfp_gt_bits,
       smtfloatTheory.smtfp_ge_bits,
       smtfloatTheory.smtfp_comparison_duals,
       smtfloatTheory.smtfp_nan_pattern_def,
       smtfloatTheory.smtfp_mag_lt_def,
       smtfloatTheory.smtfp_word_equal_def,
       smtfloatTheory.smtfp_word_fp_eq_def,
       smtfloatTheory.smtfp_word_lt_def,
       smtfloatTheory.smtfp_word_le_def,
       smtfloatTheory.smtfp_word_gt_def,
       smtfloatTheory.smtfp_word_ge_def]
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
        (* E1(a): direct BBLAST decides the finite fixed-width BV residue. *)
        (blastLib.BBLAST_PROVE t
         handle Feedback.HOL_ERR _ =>
           let
             (* E1(a): semantics-preserving word normalization followed by
                TAUT or BBLAST remains a decision procedure for that same
                finite fixed-width Boolean/word fragment. *)
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
     formulas over per-bit Boolean skolems.  fp(3)(bit-decomposition) already
     defines each packed word as the FP representative; checked per-bit
     definitions below connect Z3's later Boolean formula to that word
     formula. *)
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
      [smtfloatTheory.smtfp_add_circuit_correspondence,
       smtfloatTheory.smtfp_sub_circuit_correspondence,
       smtfloatTheory.smtfp_add_circuit_RNE_comm,
       smtfloatTheory.smtfp_add_circuit_RTN_pzero,
       smtfloatTheory.smtfp_add_circuit_RTN_right_zero_bits,
       smtfloatTheory.smtfp_add_circuit_nan,
       smtfloatTheory.smtfp_sub_circuit_nan,
       smtfloatTheory.smtfp_bits_pzero,
       smtfloatTheory.smtfp_pzero_bits,
       smtfloatTheory.smtfp_bits_nzero,
       smtfloatTheory.smtfp_nzero_bits]
    end

  val mul_rewrites =
    let open smtfloatTheory
    in
      [smtfloatTheory.smtfp_mul_one]
    end

  fun mul_one_prove t =
  let
    val theorem = smtfloatTheory.smtfp_mul_one
    val (_, consequent) = boolSyntax.dest_imp (Thm.concl theorem)
    val theorem = Drule.INST_TY_TERM (Term.match_term consequent t) theorem
    val (premise, _) = boolSyntax.dest_imp (Thm.concl theorem)
    val premise_thm = simpLib.SIMP_PROVE (bossLib.srw_ss())
      [binary_ieeeTheory.float_value_def,
       binary_ieeeTheory.float_to_real_def,
       smtfloatTheory.canon_def, smtfloatTheory.smtfp_nan_pattern_def,
       wordsTheory.UINT_MAX_def, wordsTheory.INT_MAX_def]
      premise
  in
    Thm.MP theorem premise_thm
  end

  fun is_mul_one_shape t =
    let
      val (_, consequent) =
        boolSyntax.dest_imp (Thm.concl smtfloatTheory.smtfp_mul_one)
    in
      Lib.can (Term.match_term consequent) t
    end

  fun symbolic_arithmetic_uncapped allow_direct_mul t =
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
    val direct_mul =
      if allow_direct_mul andalso has_mul andalso is_mul_one_shape t then
        SOME (mul_one_prove t)
      else NONE
    val normalized =
      case direct_mul of
        SOME theorem => Drule.EQT_INTRO theorem
      | NONE =>
          (simpLib.SIMP_CONV (bossLib.srw_ss()) rewrites t
           handle Conv.UNCHANGED => Thm.REFL t)
    val residue = boolSyntax.rhs (Thm.concl normalized)
    val () = SmtResource.check_bitblast_goal case_id residue
    val residue_thm =
      if Term.aconv residue boolSyntax.T then boolTheory.TRUTH
      else tier2_bv_prove residue
  in
    Thm.EQ_MP (Thm.SYM normalized) residue_thm
  end

  fun symbolic_arithmetic_prove_mode allow_direct_mul t =
    let
      val case_id =
        if Lib.can (HolKernel.find_term is_mul_const) t then
          mul_case_id
        else addsub_case_id
    in
      SmtResource.with_bitblast_step_time case_id
        (symbolic_arithmetic_uncapped allow_direct_mul) t
    end

  val symbolic_arithmetic_prove = symbolic_arithmetic_prove_mode true

  val symbolic_arithmetic_replay_prove =
    symbolic_arithmetic_prove_mode false

  val symbolic_arithmetic_preflight_case_id =
    "symbolic-arithmetic-cost"

  (* A format-independent preflight: charge every symbolic add/sub/mul term
     by its syntax size times packed width.  This is deliberately oblivious
     to operand names and dimensions; equal-width formats receive identical
     treatment.  The standing width>=32 refusal remains in the replay rung. *)
  fun preflight_resource_gate terms =
    let
      val limit = SmtResource.max_bitblast_term_nodes
      fun check term =
        let
          val has_addsub = Lib.can (HolKernel.find_term is_addsub_const) term
          val has_mul = Lib.can (HolKernel.find_term is_mul_const) term
        in
          if not (has_addsub orelse has_mul) orelse
             List.null (Term.free_vars term) then ()
          else
            let
              val width = if has_mul then mul_format_width term
                else addsub_format_width term
              val nodes = SmtResource.term_nodes_up_to limit term
              val cost = if width <= 0 orelse nodes > limit div width then
                  limit + 1
                else nodes * width
            in
              SmtResource.check_term_size
                symbolic_arithmetic_preflight_case_id cost
            end
        end
    in
      List.app check terms
    end

  fun next_rung prover t continuation =
    prover t
    handle Feedback.HOL_ERR holerr =>
      if SmtResource.is_resource_gate holerr then
        raise Feedback.HOL_ERR holerr
      else
        continuation ()

  fun fp_prove_with_context_mode symbolic_prover arith_prove
      eligible_decompositions all_decompositions t =
    if not (has_fp_theory_term t) then
      unsupported t
    else
      next_rung
        (* E1(a): theorem-net instantiation is the checked procedure for the
           proved FP rewrite schemas.  Its final reflexive-lt fallback is a
           separately D1-gated E1(c) cache. *)
        (profile "fp(1)(proforma)" proforma_prove) t (fn () =>
      next_rung
        (* E1(a): CBV decides closed executable SMT floating-point terms. *)
        (profile "fp(2)(ground-eval)" ground_eval_prove) t (fn () =>
      next_rung
        (* E1(a): exact lookup in the finite parser-recorded decomposition
           set plus the checked packed-fields theorem is complete. *)
        (profile "fp(3)(bit-decomposition)"
          (bit_decomposition_prove eligible_decompositions)) t (fn () =>
      next_rung
        (* E1(b): the supplied arithmetic procedure is general for selected
           fp.to_real residues and fails loudly outside that family. *)
        (profile "fp(4)(to-real-arith)"
          (to_real_arith_prove arith_prove)) t (fn () =>
      next_rung
        (* E1(a): checked lowering plus BBLAST decides the selected finite
           Tier-2 atom/decomposition fragment, subject to the D4 cap. *)
        (profile "fp(5)(tier2-bitblast)"
          (tier2_bitblast_prove_with_decompositions all_decompositions)) t
        (fn () =>
      next_rung
        (* E1(b): checked circuit lowering and terminal BV decision is the
           general selected add/sub/mul family, with a loud D4 boundary. *)
        (profile "fp(6)(symbolic-arithmetic)"
          symbolic_prover) t (fn () =>
      (* E1(b): terminal loud floating-point family boundary. *)
      profile "fp(7)(unsupported)" unsupported t))))))

  fun fp_prove_with_context arith_prove eligible_decompositions
      all_decompositions =
    fp_prove_with_context_mode symbolic_arithmetic_replay_prove arith_prove
      eligible_decompositions all_decompositions

  fun fp_prove_with_decompositions_and_arith arith_prove decompositions =
    fp_prove_with_context_mode symbolic_arithmetic_prove arith_prove
      decompositions decompositions

  fun no_arith_prove _ =
    raise ERR "no_arith_prove" "no arithmetic prover was supplied"

  fun fp_prove_with_decompositions decompositions =
    fp_prove_with_decompositions_and_arith no_arith_prove decompositions

  fun fp_prove t = fp_prove_with_decompositions [] t

end
