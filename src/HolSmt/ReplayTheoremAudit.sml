(* Structural completeness audit for the three theories that supply checked
   replay.  The positive set is derived from the loaded theories and the
   consumers are derived from SML source identifiers; only genuinely
   non-replay exports appear in the explicit exception table below. *)

structure ReplayTheoremAudit =
struct

type exemption = {theory : string, name : string, reason : string}

fun exempt theory reason names =
  List.map (fn name => {theory = theory, name = name, reason = reason}) names

val hol_semantic_reason =
  "semantic definition or specification for a replay-visible constant; " ^
  "replay consumes the constant or a derived rule"
val hol_proof_reason =
  "theory-proof auxiliary used to derive a consumed general arithmetic rule"
val generated_definition_reason =
  "generated specification or recursion artifact; replay consumes its " ^
  "public definition theorem"
val string_semantic_reason =
  "semantic definition or specification for Z3 proof vocabulary; replay " ^
  "consumes its derived compute or transition rules"
val string_proof_reason =
  "general theory-proof scaffold used to derive consumed string or regex rules"
val fp_definition_reason =
  "public floating-point semantic definition, representation, or " ^
  "specification theorem; it is not a replay-table entry"
val fp_proof_reason =
  "standalone floating-point semantic or proof-development theorem; it is " ^
  "not a replay-table entry"
val fp_example_reason =
  "floating-point theory example or ground certificate; it documents the " ^
  "semantic theory and does not serve replay"

val non_replay_exports : exemption list =
  exempt "HolSmt" hol_semantic_reason [
      "array_ext_def",
      "smt_rdiv",
      "smt_seq_nth_spec"
    ] @
  exempt "HolSmt" hol_proof_reason [
      "smt_ediv_bounds_neg_aux",
      "smt_ediv_bounds_neg_bridge",
      "smt_ediv_bounds_pos_aux",
      "smt_ediv_bounds_pos_bridge",
      "smt_emod_ediv_neg",
      "smt_emod_ediv_pos"
    ] @
  exempt "HolSmt" generated_definition_reason [
      "smt_seq_replace_all_aux_compute",
      "smt_seq_replace_all_aux_ind"
    ] @
  exempt "smtstringz3" string_semantic_reason [
      "aut_accept_def",
      "char_bit_def",
      "seq_nth_i_spec"
    ] @
  exempt "smtstringz3" string_proof_reason [
      "aut_accept_lang",
      "aut_accept_plus_allchar",
      "seq_head_tail",
      "seq_nth_i_def"
    ] @
  exempt "smtfloat" fp_definition_reason [
      "float_canon_qnan_def",
      "float_from_ieee_bv_def",
      "float_max_zero_choice_spec",
      "float_min_zero_choice_spec",
      "float_pack_ieee_bv_def",
      "float_to_real_unspecified_spec",
      "float_to_sbv_unspecified_spec",
      "float_to_ubv_unspecified_spec",
      "integral_round_candidate_def",
      "integral_round_tiesToAway_def",
      "round_tiesToAway_def",
      "smt_float_restore_zero_sign_def",
      "smt_rounding_BIJ",
      "smt_rounding_CASE",
      "smt_rounding_TY_DEF",
      "smt_rounding_size_def",
      "smtfp_BIJ",
      "smtfp_TY_DEF",
      "smtfp_abs_def",
      "smtfp_add_def",
      "smtfp_addsub_circuit_def",
      "smtfp_addsub_magnitude_def",
      "smtfp_addsub_result_sign_def",
      "smtfp_addsub_scale_def",
      "smtfp_addsub_trace_def",
      "smtfp_addsub_zero_sign_def",
      "smtfp_bits_def",
      "smtfp_canonical_def",
      "smtfp_circuit_divisor_def",
      "smtfp_circuit_effective_exponent_def",
      "smtfp_circuit_encode_def",
      "smtfp_circuit_encoded_exponent_def",
      "smtfp_circuit_endpoint_def",
      "smtfp_circuit_exp_def",
      "smtfp_circuit_infinity_def",
      "smtfp_circuit_overflow_def",
      "smtfp_circuit_pack_def",
      "smtfp_circuit_quotient_def",
      "smtfp_circuit_remainder_def",
      "smtfp_circuit_round_def",
      "smtfp_circuit_round_up_def",
      "smtfp_circuit_rounded_def",
      "smtfp_circuit_shift_def",
      "smtfp_circuit_sig_def",
      "smtfp_circuit_top_def",
      "smtfp_circuit_units_def",
      "smtfp_circuit_wanted_exponent_def",
      "smtfp_div_def",
      "smtfp_eq_def",
      "smtfp_fma_def",
      "smtfp_from_ieee_bv_def",
      "smtfp_from_real_def",
      "smtfp_from_sbv_def",
      "smtfp_from_ubv_def",
      "smtfp_ge_def",
      "smtfp_gt_def",
      "smtfp_intro_def",
      "smtfp_is_finite_def",
      "smtfp_is_infinite_def",
      "smtfp_is_integral_def",
      "smtfp_is_nan_def",
      "smtfp_is_negative_def",
      "smtfp_is_normal_def",
      "smtfp_is_positive_def",
      "smtfp_is_signalling_def",
      "smtfp_is_subnormal_def",
      "smtfp_is_zero_def",
      "smtfp_le_def",
      "smtfp_lt_def",
      "smtfp_max_def",
      "smtfp_min_def",
      "smtfp_mul_circuit_def",
      "smtfp_mul_def",
      "smtfp_mul_divisor_def",
      "smtfp_mul_encode_def",
      "smtfp_mul_encoded_exponent_def",
      "smtfp_mul_exponent_sum_def",
      "smtfp_mul_product_def",
      "smtfp_mul_quotient_def",
      "smtfp_mul_remainder_def",
      "smtfp_mul_shift_right_def",
      "smtfp_mul_sign_def",
      "smtfp_mul_trace_def",
      "smtfp_mul_wanted_exponent_def",
      "smtfp_nan_def",
      "smtfp_neg_def",
      "smtfp_ninf_def",
      "smtfp_nzero_def",
      "smtfp_pack_bv_def",
      "smtfp_pack_ieee_bv_def",
      "smtfp_pack_rounding_def",
      "smtfp_pinf_def",
      "smtfp_pzero_def",
      "smtfp_rem_def",
      "smtfp_round_to_integral_def",
      "smtfp_sqrt_def",
      "smtfp_sub_def",
      "smtfp_to_fp_def",
      "smtfp_to_real_def",
      "smtfp_to_sbv_def",
      "smtfp_to_ubv_def",
      "smtfp_unordered_def",
      "smtfp_unpack_rounding_def",
      "to_binary_rounding_def"
    ] @
  exempt "smtfloat" fp_proof_reason [
      "SmtFp_11",
      "SmtFp_smtfp_rep",
      "abs_real_of_int",
      "canon_canonical",
      "canon_idem",
      "canon_smtfp_rep",
      "circuit_bound_arithmetic",
      "circuit_carry_units_arithmetic",
      "circuit_divisor_units_arithmetic",
      "circuit_double_mult_scale",
      "circuit_nearest_multiple",
      "circuit_normalized_lower",
      "circuit_normalized_upper",
      "circuit_quotient_units_arithmetic",
      "circuit_remainder_units_arithmetic",
      "circuit_scaled_double_eq",
      "circuit_scaled_double_le",
      "circuit_scaled_double_lt",
      "circuit_units_log2",
      "circuit_wanted_exponent_units",
      "closest_finite_negative_inward_unique",
      "closest_finite_positive_inward_unique",
      "closest_such_finite_properties",
      "closest_such_integral_properties",
      "closest_such_properties",
      "datatype_smt_rounding",
      "div_common_right_factor",
      "equal_distance_same_away",
      "finite_floats_nonempty",
      "float_bits_is_nan",
      "float_canon_qnan_is_nan",
      "float_canon_qnan_significand_nonzero",
      "float_canon_qnan_value",
      "float_comparison_duals",
      "float_equal_components",
      "float_ieee_bv_pack_unpack",
      "float_ieee_bv_roundtrip_float32",
      "float_ieee_bv_unpack_pack",
      "float_is_integral_to_real",
      "float_is_nan_abs",
      "float_is_nan_negate",
      "float_less_than_bits_raw",
      "float_max_opposite_zero",
      "float_min_max_gt",
      "float_min_max_lt",
      "float_min_max_nan_left",
      "float_min_max_nan_right",
      "float_min_opposite_zero",
      "float_rem_infinity_zero_is_nan",
      "float_rem_self",
      "float_rem_zero_infinity",
      "float_sqrt_nan",
      "float_to_real_bits_lt",
      "float_to_real_bits_sign",
      "float_to_real_bits_zero",
      "float_to_real_flip_sign",
      "float_to_real_negative_bits",
      "float_to_sbv_out_of_range",
      "float_to_sbv_special",
      "float_to_sbv_valid",
      "float_to_ubv_out_of_range",
      "float_to_ubv_special",
      "float_to_ubv_valid",
      "integral_candidate_from_finite_closest",
      "integral_candidate_nearest",
      "integral_candidate_strict_unique",
      "integral_round_candidate_gap",
      "integral_round_candidate_infinities",
      "integral_round_candidates_nonempty",
      "integral_round_tiesToAway_at_threshold",
      "integral_round_tiesToAway_away",
      "integral_round_tiesToAway_eq_RNE_when_closest_unique",
      "integral_round_tiesToAway_is_closest",
      "integral_round_tiesToAway_midpoint",
      "integral_round_tiesToAway_tie_away",
      "is_integral_real_of_int",
      "is_integral_separated",
      "mod_common_right_factor",
      "negative_lt_nonnegative",
      "nonnegative_lt_negative",
      "nonzero_float_at_least_ulp",
      "num2smt_rounding_11",
      "num2smt_rounding_ONTO",
      "num2smt_rounding_smt_rounding2num",
      "num2smt_rounding_thm",
      "round_RTN_greatest_finite",
      "round_RTP_least_finite",
      "round_tiesToAway_at_threshold",
      "round_tiesToAway_away",
      "round_tiesToAway_eq_RNE_when_closest_unique",
      "round_tiesToAway_is_closest",
      "round_tiesToAway_midpoint",
      "round_tiesToAway_representable_nonzero",
      "round_tiesToAway_tie_away",
      "round_tiesToAway_zero_is_zero",
      "smt_float_add_finite_round",
      "smt_float_mul_finite_round",
      "smt_float_round_RTP_circuit_normalized_in_range",
      "smt_float_round_representable_nonzero",
      "smt_float_round_to_neg_nonzero_result",
      "smt_float_round_zero",
      "smt_float_sub_finite_round",
      "smt_float_to_fp_infinities",
      "smt_float_to_fp_nan",
      "smt_float_to_fp_shared_roundtrip",
      "smt_float_to_fp_shared_zero",
      "smt_float_to_real_special",
      "smt_float_to_real_valid",
      "smt_integer_ties_to_away_basic",
      "smt_integral_round_shared",
      "smt_nearest_integer_basic",
      "smt_nearest_integer_ties_even",
      "smt_real_to_fp_shared_representable",
      "smt_real_to_fp_shared_zero",
      "smt_round_shared",
      "smt_rounding2num_11",
      "smt_rounding2num_ONTO",
      "smt_rounding2num_num2smt_rounding",
      "smt_rounding2num_thm",
      "smt_rounding_Axiom",
      "smt_rounding_EQ_smt_rounding",
      "smt_rounding_case_cong",
      "smt_rounding_case_def",
      "smt_rounding_case_eq",
      "smt_rounding_distinct",
      "smt_rounding_induction",
      "smt_rounding_nchotomy",
      "smtfp_SmtFp_round_zero",
      "smtfp_add_RNE_comm",
      "smtfp_add_nan",
      "smtfp_add_nan_circuit_correspondence",
      "smtfp_addsub_circuit_correspondence",
      "smtfp_addsub_circuit_exact_zero_correspondence",
      "smtfp_addsub_circuit_finite_correspondence",
      "smtfp_addsub_circuit_finite_nonzero_correspondence",
      "smtfp_addsub_circuit_finite_right_zero_nonzero",
      "smtfp_addsub_circuit_finite_right_zero_nonzero_correspondence",
      "smtfp_addsub_circuit_finite_zero",
      "smtfp_addsub_exact_value",
      "smtfp_addsub_exact_zero",
      "smtfp_addsub_scale_positive",
      "smtfp_addsub_trace_exact",
      "smtfp_addsub_zero_sign_negative",
      "smtfp_addsub_zero_sign_value",
      "smtfp_addsub_zero_toneg",
      "smtfp_aligned_add_exact",
      "smtfp_bits_11_non_nan",
      "smtfp_bits_eq_nan",
      "smtfp_bits_neq_nan_left",
      "smtfp_bits_neq_nan_right",
      "smtfp_bits_pack_ieee_bv",
      "smtfp_bits_rep",
      "smtfp_bits_surjective",
      "smtfp_bool_sign_cond",
      "smtfp_canon_zero_bits",
      "smtfp_circuit_RNA_negative_endpoint",
      "smtfp_circuit_RNA_negative_overflow_band",
      "smtfp_circuit_RNA_positive_endpoint",
      "smtfp_circuit_RNA_positive_overflow_band",
      "smtfp_circuit_RNE_error_bound",
      "smtfp_circuit_RNE_negative_endpoint",
      "smtfp_circuit_RNE_negative_overflow_band",
      "smtfp_circuit_RNE_positive_endpoint",
      "smtfp_circuit_RNE_positive_overflow_band",
      "smtfp_circuit_ULP_scale",
      "smtfp_circuit_adjacent_negative_closest_hi",
      "smtfp_circuit_adjacent_negative_closest_lo",
      "smtfp_circuit_adjacent_positive_closest_hi",
      "smtfp_circuit_adjacent_positive_closest_lo",
      "smtfp_circuit_align_value",
      "smtfp_circuit_directed_negative_endpoint",
      "smtfp_circuit_directed_positive_endpoint",
      "smtfp_circuit_division",
      "smtfp_circuit_divisor_units",
      "smtfp_circuit_effective_encoded",
      "smtfp_circuit_effective_exponent_positive",
      "smtfp_circuit_encode_correct",
      "smtfp_circuit_encode_endpoint",
      "smtfp_circuit_encode_finite_correct",
      "smtfp_circuit_encode_overflow_correct",
      "smtfp_circuit_encode_representable",
      "smtfp_circuit_encode_zero",
      "smtfp_circuit_endpoint_ULP",
      "smtfp_circuit_endpoint_ULP_divisor",
      "smtfp_circuit_endpoint_boundary",
      "smtfp_circuit_endpoint_even",
      "smtfp_circuit_endpoint_even_finite",
      "smtfp_circuit_endpoint_finite",
      "smtfp_circuit_endpoint_next_hi",
      "smtfp_circuit_endpoint_nonzero",
      "smtfp_circuit_endpoint_units",
      "smtfp_circuit_endpoint_value",
      "smtfp_circuit_exp_positive",
      "smtfp_circuit_infinity_rep",
      "smtfp_circuit_largest_threshold_units",
      "smtfp_circuit_overflow_midpoint_units",
      "smtfp_circuit_overflow_rep",
      "smtfp_circuit_pack_endpoint",
      "smtfp_circuit_pack_overflow",
      "smtfp_circuit_pack_top",
      "smtfp_circuit_positive_value",
      "smtfp_circuit_quotient_normalized_lower",
      "smtfp_circuit_quotient_normalized_upper",
      "smtfp_circuit_quotient_units",
      "smtfp_circuit_remainder_units",
      "smtfp_circuit_round_abs_diff",
      "smtfp_circuit_round_bounds",
      "smtfp_circuit_round_exact",
      "smtfp_circuit_round_nearest_multiple",
      "smtfp_circuit_round_units",
      "smtfp_circuit_round_up_scale",
      "smtfp_circuit_rounded_units",
      "smtfp_circuit_scaled_abs_diff",
      "smtfp_circuit_scaled_abs_diff_neg",
      "smtfp_circuit_scaled_abs_diff_neg_left",
      "smtfp_circuit_scaled_midpoint_hi",
      "smtfp_circuit_scaled_midpoint_lo",
      "smtfp_circuit_sig_bound",
      "smtfp_circuit_sig_mantissa",
      "smtfp_circuit_signed_align_value",
      "smtfp_circuit_strict_overflow_round",
      "smtfp_circuit_strict_overflow_units",
      "smtfp_circuit_threshold_largest",
      "smtfp_circuit_tie_divisor",
      "smtfp_circuit_top_rep",
      "smtfp_circuit_units_value",
      "smtfp_circuit_value",
      "smtfp_circuit_value_float",
      "smtfp_conversion_reps",
      "smtfp_float_value_finite",
      "smtfp_from_ieee_bv_fields",
      "smtfp_ieee_bv_roundtrip_float32",
      "smtfp_ieee_bv_unpack_pack",
      "smtfp_intro_rep",
      "smtfp_mag_lt_asym",
      "smtfp_max_op_nan",
      "smtfp_min_max_nan_left",
      "smtfp_min_max_nan_right",
      "smtfp_min_op_nan",
      "smtfp_mul_exact_value",
      "smtfp_mul_product_zero",
      "smtfp_mul_trace_components",
      "smtfp_negative_positive_lt",
      "smtfp_negative_real_lt",
      "smtfp_nzero_neq_pzero",
      "smtfp_op_nan",
      "smtfp_positive_exponent_monotone",
      "smtfp_positive_mag_lt",
      "smtfp_positive_mag_lt_backward",
      "smtfp_positive_mag_lt_forward",
      "smtfp_positive_negative_not_lt",
      "smtfp_positive_real_eq_not_mag_lt",
      "smtfp_positive_real_nonnegative",
      "smtfp_positive_real_zero",
      "smtfp_positive_same_exponent_lt",
      "smtfp_rem_op_nan",
      "smtfp_rem_zero_infinity",
      "smtfp_rep_SmtFp",
      "smtfp_rep_bits",
      "smtfp_rep_compute",
      "smtfp_rep_def",
      "smtfp_rep_finite_n2w_bits",
      "smtfp_rep_intro",
      "smtfp_rep_11",
      "smtfp_rep_canonical",
      "smtfp_rep_surjective",
      "smtfp_signed_magnitude_add",
      "smtfp_sub_nan",
      "smtfp_sub_nan_circuit_correspondence",
      "smtfp_to_real_valid",
      "smtfp_to_sbv_valid",
      "smtfp_to_ubv_valid",
      "smtfp_unpack_pack_rounding",
      "to_binary_rounding_of_binary"
    ] @
  exempt "smtfloat" fp_example_reason [
      "float32_ieee_one_ground",
      "float32_one_conversion_ground",
      "float32_one_to_fp_ground",
      "smtfp_tier2_classification_example",
      "smtfp_tier2_equality_example",
      "smtfp_tier2_ordering_example",
      "smtfp_tier2_sign_example"
    ]

val replay_theories =
  [("HolSmt", "HolSmtScript.sml"),
   ("smtstringz3", "smtstringz3Script.sml"),
   ("smtfloat", "smtfloatScript.sml")]

fun ERR function message =
  Feedback.mk_HOL_ERR "ReplayTheoremAudit" function message

fun readable path =
  OS.FileSys.access (path, [OS.FileSys.A_READ]) handle OS.SysErr _ => false

fun source_directory () =
let
  fun under root = OS.Path.concat (root, "src/HolSmt")
  val candidates =
    List.mapPartial (fn candidate => candidate)
      [Option.map under (OS.Process.getEnv "HOLSMT_ROOT"),
       SOME (OS.FileSys.getDir ()),
       Option.map under (OS.Process.getEnv "HOLDIR")]
  fun is_source_directory directory =
    readable (OS.Path.concat (directory, "Unittest.sml"))
in
  case List.find is_source_directory candidates of
    SOME directory => directory
  | NONE => raise ERR "source_directory"
      "cannot locate src/HolSmt source files"
end

fun directory_entries directory =
let
  val stream = OS.FileSys.openDir directory
  fun loop entries =
    case OS.FileSys.readDir stream of
      NONE => List.rev entries
    | SOME entry => loop (entry :: entries)
  val entries = loop [] handle error =>
    (OS.FileSys.closeDir stream; raise error)
  val _ = OS.FileSys.closeDir stream
in
  entries
end

fun read_file path =
let
  val stream = TextIO.openIn path
  val contents = TextIO.inputAll stream
  val _ = TextIO.closeIn stream
in
  contents
end

datatype lexical_state =
    Code
  | Comment of int
  | Quoted
  | HolQuoted of int
datatype sml_token = Identifier of string | Dot

fun sml_tokens text =
let
  val size = String.size text
  fun at index = String.sub (text, index)
  fun starts index (first, second) =
    index + 1 < size andalso at index = first andalso
    at (index + 1) = second
  fun identifier_start character =
    Char.isAlpha character orelse character = #"_"
  fun identifier_character character =
    Char.isAlphaNum character orelse character = #"_" orelse
    character = #"'"
  fun identifier_end index =
    if index < size andalso identifier_character (at index) then
      identifier_end (index + 1)
    else
      index
  fun scan index state tokens =
    if index >= size then
      (case state of
         Code => List.rev tokens
       | Comment _ => raise ERR "sml_tokens" "unterminated SML comment"
       | Quoted => raise ERR "sml_tokens" "unterminated SML string"
       | HolQuoted _ =>
           raise ERR "sml_tokens" "unterminated HOL quotation")
    else
      case state of
        Code =>
          if starts index (#"(", #"*") then
            scan (index + 2) (Comment 1) tokens
          else if at index = #"\"" then
            scan (index + 1) Quoted tokens
          else if starts index (#"`", #"`") then
            scan (index + 2) (HolQuoted 2) tokens
          else if at index = #"`" then
            scan (index + 1) (HolQuoted 1) tokens
          else if identifier_start (at index) then
            let
              val finish = identifier_end (index + 1)
              val identifier = String.substring (text, index, finish - index)
            in
              scan finish Code (Identifier identifier :: tokens)
            end
          else if at index = #"." then
            scan (index + 1) Code (Dot :: tokens)
          else
            scan (index + 1) Code tokens
      | Comment depth =>
          if starts index (#"(", #"*") then
            scan (index + 2) (Comment (depth + 1)) tokens
          else if starts index (#"*", #")") then
            if depth = 1 then scan (index + 2) Code tokens
            else scan (index + 2) (Comment (depth - 1)) tokens
          else
            scan (index + 1) (Comment depth) tokens
      | Quoted =>
          if at index = #"\\" then
            scan (Int.min (index + 2, size)) Quoted tokens
          else if at index = #"\"" then
            scan (index + 1) Code tokens
          else
            scan (index + 1) Quoted tokens
      | HolQuoted width =>
          if at index = #"\\" then
            scan (Int.min (index + 2, size)) (HolQuoted width) tokens
          else if width = 2 andalso starts index (#"`", #"`") then
            scan (index + 2) Code tokens
          else if width = 1 andalso at index = #"`" then
            scan (index + 1) Code tokens
          else
            scan (index + 1) (HolQuoted width) tokens
in
  scan 0 Code []
end

fun source_token_streams directory =
let
  val audit_sources =
    ["ReplayTheoremAudit.sml", "Unittest.sml", "selftest.sml"]
  fun is_consumer name =
    String.isSuffix ".sml" name andalso
    not (List.exists (fn audit_source => name = audit_source) audit_sources)
  fun tokens name =
    (name, sml_tokens (read_file (OS.Path.concat (directory, name))))
in
  List.map tokens
    (Listsort.sort String.compare
      (List.filter is_consumer (directory_entries directory)))
end

fun has_qualified_reference theory name tokens =
let
  val structure_name = theory ^ "Theory"
  fun search preceded_by_dot tokens =
    case tokens of
      Identifier found_structure :: Dot :: Identifier found_name :: rest =>
        (not preceded_by_dot andalso found_structure = structure_name andalso
         found_name = name) orelse
        search false (Dot :: Identifier found_name :: rest)
    | Dot :: rest => search true rest
    | _ :: rest => search false rest
    | [] => false
in
  search false tokens
end

fun expect_lexer_error text =
  ((sml_tokens text; false) handle Feedback.HOL_ERR _ => true)

fun scanner_regressions () =
let
  fun found text =
    has_qualified_reference "HolSmt" "r001" (sml_tokens text)
in
  found "val theorem = HolSmtTheory.r001" andalso
  not (found "val r001 = seed") andalso
  not (found "fun bind r001 = r001") andalso
  not (found "case value of r001 => r001") andalso
  not (found "val theorem = Other.HolSmtTheory.r001") andalso
  not (found "\"HolSmtTheory.r001\"") andalso
  not (found "(* HolSmtTheory.r001 *)") andalso
  not (found "``let x = HolSmtTheory.r001 in x``") andalso
  not (found "`^HolSmtTheory.r001`") andalso
  expect_lexer_error "(* outer (* nested *)" andalso
  expect_lexer_error "\"unterminated" andalso
  expect_lexer_error "`unterminated" andalso
  expect_lexer_error "``unterminated"
end

fun exported_theorems () =
  List.concat (List.map (fn (theory, _) =>
    List.map (fn (name, _) => (theory, name)) (DB.thms theory))
      replay_theories)

fun key (theory, name) = theory ^ "Theory." ^ name

fun audit () =
let
  val sources = source_token_streams (source_directory ())
  val exports = exported_theorems ()
  fun own_script theory =
    case List.find (fn (found, _) => theory = found) replay_theories of
      SOME (_, script) => script
    | NONE => raise ERR "audit" ("unknown replay theory " ^ theory)
  fun references (theory, name) =
    List.map #1 (List.filter (fn (file, tokens) =>
      file <> own_script theory andalso
      has_qualified_reference theory name tokens) sources)
  fun exemption_for (theory, name) =
    List.find (fn {theory = allowed_theory, name = allowed_name, ...} =>
      theory = allowed_theory andalso name = allowed_name)
      non_replay_exports
  val referenced = List.filter (not o List.null o references) exports
  val exempted = List.filter (Option.isSome o exemption_for) exports
  val orphans = List.filter (fn export =>
    List.null (references export) andalso
    not (Option.isSome (exemption_for export))) exports
  val stale_exemptions = List.filter
    (fn {theory, name, ...} =>
      not (List.exists (fn export => export = (theory, name)) exports))
    non_replay_exports
  val consumed_exemptions = List.filter
    (fn {theory, name, ...} => not (List.null (references (theory, name))))
    non_replay_exports
  val unjustified_exemptions = List.filter
    (fn {reason, ...} => String.size reason = 0) non_replay_exports
  fun duplicate [] = NONE
    | duplicate ({theory, name, ...} :: rest) =
        if List.exists (fn {theory = other_theory, name = other_name, ...} =>
             theory = other_theory andalso name = other_name) rest then
          SOME (theory, name)
        else
          duplicate rest
in
  {exports = exports, referenced = referenced, exempted = exempted,
   orphans = orphans, stale_exemptions = stale_exemptions,
   consumed_exemptions = consumed_exemptions,
   unjustified_exemptions = unjustified_exemptions,
   duplicate_exemption = duplicate non_replay_exports,
   references = references}
end

fun check () =
let
  val {orphans, stale_exemptions, consumed_exemptions,
       unjustified_exemptions, duplicate_exemption, ...} = audit ()
  fun exemption_key {theory, name, ...} = key (theory, name)
  fun comma strings = String.concatWith ", " strings
  val _ = if scanner_regressions () then () else
    raise ERR "check" "SML qualified-reference scanner regression"
  val _ =
    case duplicate_exemption of
      NONE => ()
    | SOME duplicate => raise ERR "check"
        ("duplicate non-replay exemption: " ^ key duplicate)
  val _ = if List.null stale_exemptions then () else raise ERR "check"
    ("stale non-replay exemptions: " ^
     comma (List.map exemption_key stale_exemptions))
  val _ = if List.null consumed_exemptions then () else raise ERR "check"
    ("referenced theorems remain exempted: " ^
     comma (List.map exemption_key consumed_exemptions))
  val _ = if List.null unjustified_exemptions then () else raise ERR "check"
    ("non-replay exemptions lack reasons: " ^
     comma (List.map exemption_key unjustified_exemptions))
  val _ = if List.null orphans then () else raise ERR "check"
    ("replay-serving theorem exports lack SML consumers: " ^
     comma (List.map key orphans))
in
  ()
end

end
