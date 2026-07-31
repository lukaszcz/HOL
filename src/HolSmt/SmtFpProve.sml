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
       "implemented for proforma, ground-evaluation, and fresh " ^
       "bit-decomposition rewrites; " ^
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

  (* TASK_23 and TASK_25 replace these deliberate fall-through stubs with
     Tier-2 bit-blast and arithmetic circuits. *)
  fun tier2_bitblast_prove _ =
    raise ERR "tier2_bitblast_prove" "rung 4 is not installed"

  fun symbolic_arithmetic_prove _ =
    raise ERR "symbolic_arithmetic_prove" "rung 5 is not installed"

  fun next_rung prover t continuation =
    prover t
    handle Feedback.HOL_ERR holerr =>
      if SmtResource.is_resource_gate holerr then
        raise Feedback.HOL_ERR holerr
      else
        continuation ()

  fun fp_prove_with_decompositions decompositions t =
    if not (has_fp_theory_term t) then
      unsupported t
    else
      next_rung
        (profile "fp(rung:1/proforma)" proforma_prove) t (fn () =>
      next_rung
        (profile "fp(rung:2/ground-eval)" ground_eval_prove) t (fn () =>
      next_rung
        (profile "fp(rung:3/bit-decomposition)"
          (bit_decomposition_prove decompositions)) t (fn () =>
      next_rung
        (profile "fp(rung:4/tier2-bitblast)" tier2_bitblast_prove) t
        (fn () =>
      next_rung
        (profile "fp(rung:5/symbolic-arithmetic)"
          symbolic_arithmetic_prove) t (fn () =>
      profile "fp(rung:6/unsupported)" unsupported t)))))

  fun fp_prove t = fp_prove_with_decompositions [] t

end
