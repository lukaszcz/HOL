structure benchSetShortfalls =
struct

val entries : benchLib.shortfall list =
  [{id = "set_L869_doubleton_eq_iff",
    cause = benchLib.EngineLimitation, date = "2026-08-15",
    note = "assigned tactic does not close without a direct analogue"},
   {id = "set_L928_subset_image_iff",
    cause = benchLib.EngineLimitation, date = "2026-08-15",
    note = "assigned tactic does not close without a direct analogue"},
   {id = "set_L1604_Pow_singleton_iff",
    cause = benchLib.EngineLimitation, date = "2026-08-15",
    note = "assigned tactic does not close without a direct analogue"}]

end
