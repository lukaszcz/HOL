structure pureSimps :> pureSimps =
struct

open simpLib;

val PURE_ss = name_ss "PURE" (leveled_filter_ss Cond_rewr.mk_cond_rewrs_at)

val pure_ss = mk_simpset [PURE_ss]

end
