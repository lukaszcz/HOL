signature smtfloatLib =
sig
  val round_CONV : Conv.conv
  val float_round_CONV : Conv.conv
  val round_tiesToAway_CONV : Conv.conv
  val integral_round_tiesToAway_CONV : Conv.conv
  val smt_round_CONV : Conv.conv
  val smt_integral_round_CONV : Conv.conv

  val add_smtfloat_to_compset :
    computeLib.compset -> computeLib.compset
end
