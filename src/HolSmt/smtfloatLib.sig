signature smtfloatLib =
sig
  val round_CONV : Conv.conv
  val float_round_CONV : Conv.conv
  val round_tiesToAway_CONV : Conv.conv
  val integral_round_tiesToAway_CONV : Conv.conv
  val smt_round_CONV : Conv.conv
  val smt_integral_round_CONV : Conv.conv
  val smt_float_round_CONV : Conv.conv
  val smt_float_add_CONV : Conv.conv
  val smt_float_sub_CONV : Conv.conv
  val smt_float_mul_CONV : Conv.conv
  val smt_float_div_CONV : Conv.conv
  val smt_float_sqrt_CONV : Conv.conv
  val smt_float_fma_CONV : Conv.conv
  val smt_float_round_to_integral_CONV : Conv.conv
  val float_min_CONV : Conv.conv
  val float_max_CONV : Conv.conv
  val smt_nearest_integer_CONV : Conv.conv
  val float_rem_CONV : Conv.conv
  val smt_integer_ties_to_away_CONV : Conv.conv
  val smt_real_to_int_CONV : Conv.conv
  val float_to_ubv_CONV : Conv.conv
  val float_to_sbv_CONV : Conv.conv
  val smt_float_to_real_CONV : Conv.conv
  val smt_float_to_fp_CONV : Conv.conv
  val smt_real_to_fp_CONV : Conv.conv
  val smt_ubv_to_fp_CONV : Conv.conv
  val smt_sbv_to_fp_CONV : Conv.conv

  val add_smtfloat_to_compset :
    computeLib.compset -> computeLib.compset
end
