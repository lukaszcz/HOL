(* Proof reconstruction for cvc5 CPC: proof representation and rule registry. *)

structure CPC_Proof =
struct

  datatype rule_namespace = ProofRule | RareRewrite

  datatype proof_version_support = AllCVCVersions
                                 | CVCVersionPrefixes of string list
                                 | CVCVersions of string list

  type proof_rule = {
    name : string,
    namespace : rule_namespace,
    version_support : proof_version_support,
    replay_handler : string
  }

  (* The frozen CPC vocabulary was captured and replayed with cvc5 1.3.4.
     These are the versions whose dialect was actually measured; a patch
     release does not change it, so the whole 1.3 series counts as tested.
     Another version is admitted here once its matrix has been recaptured and
     replayed.  Until then it is not rejected: `resolve_version` warns and
     replays it under the nearest measured dialect. *)
  val supported_cvc_versions = ["1.3.4"]

  fun mk_rule namespace (name, replay_handler) : proof_rule = {
    name = name,
    namespace = namespace,
    version_support = CVCVersions supported_cvc_versions,
    replay_handler = replay_handler
  }

  (* This is deliberately a registry, rather than a catch-all replay case.
     Entries are promoted from the recorded CPC corpus.  The initial list is
     the cvc5 1.3.4 dsl-rewrite seed inventory; an unlisted rule is a checked
     replay failure, never an implicit trust step. *)
  val proof_rule_registry : proof_rule list = [
    mk_rule ProofRule ("refl", "refl"),
    mk_rule ProofRule ("eq-refl", "eq_refl"),
    mk_rule ProofRule ("symm", "symm"),
    mk_rule ProofRule ("trans", "trans"),
    mk_rule ProofRule ("cong", "cong"),
    mk_rule ProofRule ("nary_cong", "cong"),
    mk_rule ProofRule ("ho_cong", "ho_cong"),
    mk_rule ProofRule ("beta-reduce", "beta_reduce"),
    mk_rule ProofRule ("lambda-elim", "lambda_elim"),
    mk_rule ProofRule ("eq_resolve", "eq_resolve"),
    mk_rule ProofRule ("evaluate", "evaluate"),
    mk_rule ProofRule ("and_elim", "and_elim"),
    mk_rule ProofRule ("instantiate", "instantiate"),
    mk_rule ProofRule ("contra", "contra"),
    mk_rule ProofRule ("false_intro", "false_intro"),
    mk_rule ProofRule ("false_elim", "false_elim"),
    mk_rule ProofRule ("distinct_values", "datatype"),
    mk_rule ProofRule ("dt_split", "datatype"),
    mk_rule ProofRule ("dt-cycle", "datatype_eq"),
    mk_rule ProofRule ("dt", "datatype"),
    mk_rule ProofRule ("resolution", "resolution"),
    mk_rule ProofRule ("chain_m_resolution", "resolution"),
    mk_rule ProofRule ("reordering", "reordering"),
    mk_rule ProofRule ("arith", "arith"),
    mk_rule ProofRule ("array", "array"),
    mk_rule ProofRule ("arrays-select-const", "arrays_select_const"),
    (* cvc5 has used both this macro and the narrow [sets-*] rewrites. *)
    mk_rule ProofRule ("sets", "sets"),
    mk_rule ProofRule ("bool", "bool"),
    mk_rule ProofRule ("trust", "trust"),
    mk_rule ProofRule ("str", "string"),
    mk_rule ProofRule ("string_eager_reduction", "string"),
    mk_rule ProofRule ("string_length_pos", "string"),
    mk_rule ProofRule ("string_reduction", "string"),
    mk_rule ProofRule ("aci_norm", "aci_norm"),
    mk_rule ProofRule ("bv_poly_norm", "bv_poly_norm"),
    mk_rule ProofRule ("bv_poly_norm_eq", "bv_poly_norm_eq"),
    mk_rule ProofRule ("bv_bitblast_step", "bv_poly_norm"),
    mk_rule RareRewrite ("bv-xor-duplicate", "bv_xor_duplicate"),
    mk_rule RareRewrite ("bv-not-idemp", "bv_not_idemp"),
    mk_rule RareRewrite ("bv-shl-by-const-0", "bv_shl_by_const_0"),
    mk_rule RareRewrite ("bv-shl-by-const-2", "bv_shl_by_const_2"),
    mk_rule RareRewrite ("bv-lshr-by-const-0", "bv_lshr_by_const_0"),
    mk_rule RareRewrite ("bv-ashr-by-const-0", "bv_ashr_by_const_0"),
    mk_rule RareRewrite ("eq-symm", "rewrite"),
    (* Native (Seq A) rules observed in the frozen cvc5 CPC corpus. *)
    mk_rule RareRewrite ("seq-eval-op", "seq_rewrite"),
    mk_rule RareRewrite ("seq-rev-rev", "seq_rev_rev"),
    mk_rule RareRewrite ("str-contains-refl", "str_contains_refl"),
    mk_rule RareRewrite ("str-substr-full-eq", "str_substr_full_eq"),
    mk_rule RareRewrite ("str-at-elim", "seq_at_elim"),
    mk_rule RareRewrite ("str-substr-concat1", "seq_rewrite"),
    (* Complete frozen cvc5 1.3.4 Set RARE inventory.  Keep this explicit:
       an unrecorded sets-* spelling must fail registry lookup loudly. *)
    mk_rule RareRewrite ("sets-card-emp", "sets_rewrite"),
    mk_rule RareRewrite ("sets-card-singleton", "sets_rewrite"),
    mk_rule RareRewrite ("sets-card-union", "sets_rewrite"),
    mk_rule RareRewrite ("sets-card-minus", "sets_rewrite"),
    mk_rule RareRewrite ("sets-choose-singleton", "sets_rewrite"),
    mk_rule RareRewrite ("sets-eval-op", "sets_rewrite"),
    mk_rule RareRewrite ("sets-insert-elim", "sets_rewrite"),
    mk_rule RareRewrite ("sets-inter-comm", "sets_rewrite"),
    mk_rule RareRewrite ("sets-inter-member", "sets_rewrite"),
    mk_rule RareRewrite ("sets-is-empty-elim", "sets_rewrite"),
    mk_rule RareRewrite ("sets-is-singleton-elim", "sets_rewrite"),
    mk_rule RareRewrite ("sets-member-emp", "sets_rewrite"),
    mk_rule RareRewrite ("sets-member-singleton", "sets_rewrite"),
    mk_rule RareRewrite ("sets-minus-member", "sets_rewrite"),
    mk_rule RareRewrite ("sets-minus-self", "sets_rewrite"),
    mk_rule RareRewrite ("sets-subset-elim", "sets_rewrite"),
    mk_rule RareRewrite ("sets-union-comm", "sets_rewrite"),
    mk_rule RareRewrite ("sets-union-member", "sets_rewrite"),
    mk_rule RareRewrite ("exists-elim", "exists_elim"),
    mk_rule RareRewrite ("absorb", "rewrite"),
    mk_rule RareRewrite ("arith-divisible-elim", "rewrite"),
    mk_rule RareRewrite ("arith-abs-eq", "arith_abs_eq"),
    mk_rule RareRewrite ("arith-abs-int-gt", "arith_abs_int_gt"),
    mk_rule RareRewrite ("arith-div-total-zero-real", "rewrite"),
    mk_rule RareRewrite ("arith-div-total-zero-int", "rewrite"),
    mk_rule RareRewrite ("arith-int-div-total", "rewrite"),
    mk_rule RareRewrite ("arith-int-div-total-one", "rewrite"),
    mk_rule RareRewrite ("arith-int-div-total-zero", "rewrite"),
    mk_rule RareRewrite ("arith-int-div-total-neg", "rewrite"),
    mk_rule RareRewrite ("arith-int-mod-total", "rewrite"),
    mk_rule RareRewrite ("arith-int-mod-total-one", "rewrite"),
    mk_rule RareRewrite ("arith-int-mod-total-zero", "rewrite"),
    mk_rule RareRewrite ("arith-int-mod-total-neg", "rewrite"),
    mk_rule RareRewrite ("arith-mod-over-mod-1", "rewrite"),
    mk_rule RareRewrite ("arith-mod-over-mod", "rewrite"),
    mk_rule RareRewrite ("arith-mod-over-mod-mult", "rewrite"),
    mk_rule RareRewrite ("array-read-over-write", "rewrite"),
    mk_rule RareRewrite ("array-read-over-write-split", "rewrite"),
    mk_rule RareRewrite ("array-store-overwrite", "rewrite"),
    mk_rule RareRewrite ("bool-double-not-elim", "rewrite"),
    mk_rule RareRewrite ("bool-eq-false", "rewrite"),
    mk_rule RareRewrite ("bool-eq-true", "rewrite"),
    mk_rule RareRewrite ("bool-xor-comm", "rewrite"),
    mk_rule RareRewrite ("bool-xor-false", "rewrite"),
    mk_rule RareRewrite ("bool-xor-true", "rewrite"),
    mk_rule RareRewrite ("bool-impl-elim", "rewrite"),
    mk_rule RareRewrite ("bool-impl-false1", "rewrite"),
    mk_rule RareRewrite ("bool-impl-true1", "rewrite"),
    mk_rule RareRewrite ("bool-impl-true2", "rewrite"),
    mk_rule RareRewrite ("bool-eq-nrefl", "rewrite"),
    mk_rule RareRewrite ("bool-not-eq-elim2", "rewrite"),
    mk_rule RareRewrite ("bool-not-eq-elim1", "rewrite"),
    mk_rule RareRewrite ("distinct-elim", "rewrite"),
    mk_rule RareRewrite ("eq-ite-lift", "rewrite"),
    mk_rule RareRewrite ("ite-neg-branch", "ite_neg_branch"),
    mk_rule RareRewrite ("re-all-elim", "string"),
    mk_rule RareRewrite ("re-concat-merge", "string"),
    mk_rule RareRewrite ("re-diff-elim", "string"),
    mk_rule RareRewrite ("re-in-comp", "string"),
    mk_rule RareRewrite ("re-in-cstring", "string"),
    mk_rule RareRewrite ("re-inter-cstring", "string"),
    mk_rule RareRewrite ("re-loop-elim", "string"),
    mk_rule RareRewrite ("re-opt-elim", "string"),
    mk_rule RareRewrite ("re-plus-elim", "string"),
    mk_rule RareRewrite ("re-repeat-elim", "string"),
    mk_rule RareRewrite ("str-concat-clash-rev", "string"),
    mk_rule RareRewrite ("str-concat-unify-rev", "string"),
    mk_rule RareRewrite ("str-contains-concat-find", "string"),
    mk_rule RareRewrite ("str-in-re-eval", "string"),
    mk_rule RareRewrite ("str-in-re-range-elim", "string"),
    mk_rule RareRewrite ("str-in-re-union-elim", "string"),
    mk_rule RareRewrite ("str-is-digit-elim", "rewrite"),
    mk_rule RareRewrite ("str-len-concat-rec", "string"),
    mk_rule RareRewrite ("str-lt-elim", "rewrite"),
    mk_rule RareRewrite ("str-replace-re-all-eval", "string"),
    mk_rule RareRewrite ("str-replace-re-eval", "string"),
    mk_rule RareRewrite ("str-substr-empty-range", "string"),
    mk_rule RareRewrite ("str-substr-empty-str", "string"),
    mk_rule RareRewrite ("str-substr-eq-empty", "string"),
    mk_rule RareRewrite ("bool-or-de-morgan", "rewrite"),
    mk_rule RareRewrite ("bool-implies-de-morgan", "rewrite"),
    mk_rule ProofRule ("not_implies_elim2", "not_implies_elim2"),
    mk_rule ProofRule ("not_implies_elim1", "not_implies_elim1"),
    mk_rule ProofRule ("implies_elim", "implies_elim"),
    mk_rule ProofRule ("factoring", "factoring"),
    mk_rule ProofRule ("cnf_implies_neg1", "cnf"),
    mk_rule ProofRule ("cnf_implies_neg2", "cnf"),
    mk_rule ProofRule ("cnf_implies_pos", "cnf"),
    mk_rule ProofRule ("cnf_and_pos", "cnf"),
    mk_rule ProofRule ("cnf_and_neg", "cnf"),
    mk_rule ProofRule ("cnf_or_neg", "cnf"),
    mk_rule ProofRule ("cnf_or_pos", "cnf"),
    mk_rule ProofRule ("cnf_equiv_neg1", "cnf"),
    mk_rule ProofRule ("cnf_equiv_neg2", "cnf"),
    mk_rule ProofRule ("cnf_equiv_pos1", "cnf"),
    mk_rule ProofRule ("cnf_equiv_pos2", "cnf"),
    mk_rule ProofRule ("cnf_xor_pos1", "cnf"),
    mk_rule ProofRule ("cnf_xor_pos2", "cnf"),
    mk_rule ProofRule ("cnf_xor_neg1", "cnf"),
    mk_rule ProofRule ("cnf_xor_neg2", "cnf"),
    mk_rule ProofRule ("cnf_ite_pos1", "cnf"),
    mk_rule ProofRule ("cnf_ite_pos2", "cnf"),
    mk_rule ProofRule ("cnf_ite_pos3", "cnf"),
    mk_rule ProofRule ("cnf_ite_neg1", "cnf"),
    mk_rule ProofRule ("cnf_ite_neg2", "cnf"),
    mk_rule ProofRule ("cnf_ite_neg3", "cnf"),
    mk_rule ProofRule ("not_equiv_elim1", "not_equiv_elim1"),
    mk_rule ProofRule ("not_equiv_elim2", "not_equiv_elim2"),
    mk_rule ProofRule ("equiv_elim2", "equiv_elim2"),
    mk_rule ProofRule ("equiv_elim1", "equiv_elim1"),
    mk_rule ProofRule ("arith_poly_norm", "arith_rule"),
    mk_rule ProofRule ("arith_poly_norm_rel", "arith_rel"),
    mk_rule ProofRule ("arith-elim-lt", "arith_rule"),
    mk_rule ProofRule ("arith-elim-leq", "arith_rule"),
    mk_rule ProofRule ("arith-elim-gt", "arith_rule"),
    mk_rule ProofRule ("arith-leq-norm", "arith_rule"),
    mk_rule ProofRule ("arith-eq-elim-int", "arith_rule"),
    mk_rule ProofRule ("skolem_intro", "refl"),
    mk_rule ProofRule ("skolemize", "skolemize"),
    mk_rule ProofRule ("true_elim", "true_elim"),
    mk_rule ProofRule ("true_intro", "true_intro"),
    mk_rule ProofRule ("ite_eq", "ite_eq"),
    mk_rule ProofRule ("ite_elim1", "ite_elim1"),
    mk_rule ProofRule ("ite_elim2", "ite_elim2"),
    mk_rule ProofRule ("quant-unused-vars", "quant_unused_vars"),
    mk_rule ProofRule ("quant-miniscope-and", "quant_rewrite"),
    mk_rule ProofRule ("quant-var-elim-eq", "quant_rewrite"),
    mk_rule ProofRule ("alpha_equiv", "alpha_equiv"),
    mk_rule ProofRule ("scope", "scope"),
    mk_rule ProofRule ("process_scope", "process_scope"),
    mk_rule ProofRule ("not_and", "not_and"),
    mk_rule ProofRule ("not_or_elim", "not_or_elim"),
    mk_rule ProofRule ("not_not_elim", "not_not_elim"),
    mk_rule ProofRule ("and_intro", "and_intro"),
    mk_rule ProofRule ("arith_mult_neg", "arith_mult_neg"),
    mk_rule ProofRule ("arith_mult_pos", "arith_mult_pos"),
    mk_rule ProofRule ("arith_mult_sign", "arith_mult_sign"),
    mk_rule ProofRule ("arith_trichotomy", "arith_trichotomy"),
    mk_rule ProofRule ("arith_reduction", "arith_reduction"),
    mk_rule ProofRule ("int_tight_lb", "int_tight_lb"),
    mk_rule ProofRule ("int_tight_ub", "int_tight_ub"),
    mk_rule ProofRule ("modus_ponens", "modus_ponens"),
    mk_rule ProofRule ("arith_sum_ub", "arith_sum_ub"),
    mk_rule ProofRule
      ("arith_mult_abs_comparison", "arith_mult_abs_comparison"),
    mk_rule ProofRule ("aci_norm", "aci_norm"),
    mk_rule RareRewrite ("arith-geq-norm1-int", "arith_rule"),
    mk_rule RareRewrite ("arith-geq-norm1-real", "arith_rule"),
    mk_rule RareRewrite ("arith-geq-tighten", "arith_rule"),
    mk_rule RareRewrite ("arith-int-geq-tighten", "arith_rule"),
    mk_rule RareRewrite ("arith-max-geq1", "arith_max_geq1"),
    mk_rule RareRewrite ("arith-min-lt2", "arith_min_lt2"),
    mk_rule RareRewrite ("ite-not-cond", "ite_not_cond"),
    mk_rule RareRewrite ("ite-true-cond", "ite_true_cond"),
    mk_rule RareRewrite ("ite-then-true", "ite_then_true"),
    mk_rule RareRewrite ("ite-false-cond", "ite_false_cond"),
    mk_rule RareRewrite ("bv-nego-eliminate", "rewrite"),
    mk_rule RareRewrite ("bv-sdivo-eliminate", "rewrite"),
    mk_rule RareRewrite ("bv-sge-eliminate", "rewrite"),
    mk_rule RareRewrite ("bv-sgt-eliminate", "rewrite"),
    mk_rule RareRewrite ("bv-sle-eliminate", "rewrite"),
    mk_rule RareRewrite ("bv-uge-eliminate", "rewrite"),
    mk_rule RareRewrite ("bv-ugt-eliminate", "rewrite"),
    mk_rule RareRewrite ("bv-ule-eliminate", "rewrite"),
    mk_rule RareRewrite ("distinct-false", "rewrite"),
    mk_rule RareRewrite ("distinct-binary-elim", "rewrite"),
    mk_rule RareRewrite ("dt-collapse-selector", "datatype_eq")
  ]

  val unknown_cvc_version = "<unknown>"

  (* Resolves a discovered cvc5 version to the tested version whose CPC
     dialect the registry replays under; see `Library`.  Callers resolve once,
     at the proof-parsing boundary, so `version_supported` below always sees a
     tested version and an unknown or untested cvc5 never fails a proof by
     itself -- it warns and replays under the nearest measured dialect. *)
  fun resolve_version version =
    Library.resolve_solver_version
      {solver = "cvc5", supported = supported_cvc_versions, version = version}

  fun version_supported version (rule : proof_rule) =
    case #version_support rule of
      AllCVCVersions => true
    | CVCVersions versions => List.exists (Lib.equal version) versions
    | CVCVersionPrefixes prefixes =>
        List.exists (fn prefix => String.isPrefix prefix version) prefixes

  fun lookup_rule version name =
    case List.find (fn (rule : proof_rule) => #name rule = name)
      proof_rule_registry of
      SOME rule => if version_supported version rule then SOME rule else NONE
    | NONE => NONE

  fun namespace_name ProofRule = "ProofRule"
    | namespace_name RareRewrite = "RARE rewrite"

  fun registry_lookup_failure version name =
    case List.find (fn (rule : proof_rule) => #name rule = name)
      proof_rule_registry of
      SOME rule => "CPC proof rule registry lookup failed: " ^
        namespace_name (#namespace rule) ^ " rule " ^ name ^
        " is not supported by cvc5 version " ^ version
    | NONE => "CPC proof rule registry lookup failed: unknown rule " ^ name ^
      " for cvc5 version " ^ version

  type step = {
    id : string,
    conclusion : Term.term option,
    rule : proof_rule,
    premises : string list,
    args : Term.term list
  }

  datatype command = ASSUME of string * Term.term
                   | ASSUME_PUSH of string * Term.term
                   | STEP of step

  type proof = {
    commands : command list,
    cvc_version : string
  }

  fun proof_commands (proof : proof) = #commands proof
  fun proof_version (proof : proof) = #cvc_version proof

end
