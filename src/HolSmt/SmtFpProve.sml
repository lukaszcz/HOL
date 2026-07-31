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
       "implemented for proforma and ground-evaluation rewrites; " ^
       "conclusion=" ^ Library.term_to_string t)

  fun proforma_prove t =
    Z3_ProformaThms.prove Z3_ProformaThms.fp_thms t
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

  (* TASK_22, TASK_23 and TASK_25 replace these deliberate fall-through
     stubs with bit decomposition, Tier-2 bit-blast and arithmetic circuits. *)
  fun bit_decomposition_prove _ =
    raise ERR "bit_decomposition_prove" "rung 3 is not installed"

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

  fun fp_prove t =
    if not (has_fp_theory_term t) then
      unsupported t
    else
      next_rung
        (profile "fp(rung:1/proforma)" proforma_prove) t (fn () =>
      next_rung
        (profile "fp(rung:2/ground-eval)" ground_eval_prove) t (fn () =>
      next_rung
        (profile "fp(rung:3/bit-decomposition)"
          bit_decomposition_prove) t (fn () =>
      next_rung
        (profile "fp(rung:4/tier2-bitblast)" tier2_bitblast_prove) t
        (fn () =>
      next_rung
        (profile "fp(rung:5/symbolic-arithmetic)"
          symbolic_arithmetic_prove) t (fn () =>
      profile "fp(rung:6/unsupported)" unsupported t)))))

end
