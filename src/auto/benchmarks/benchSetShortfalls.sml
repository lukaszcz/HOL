structure benchSetShortfalls =
struct

val entries : benchLib.shortfall list =
  map
    (fn id =>
      {id = id, cause = benchLib.EngineLimitation,
       date = "2026-08-16",
       note = "assigned tactic does not close without a measured-goal theorem"})
    ["set_theory_L79",
     "set_theory_L180",
     "set_theory_L199",
     "set_L869_doubleton_eq_iff",
     "set_L928_subset_image_iff",
     "set_L1125_image_Pow_surj",
     "set_L1593_ex_bool_eq",
     "set_L1604_Pow_singleton_iff",
     "set_L1610_Pow_Compl",
     "set_L1844_the_elem_eq",
     "set_L1967_pairwise_image"]

end
