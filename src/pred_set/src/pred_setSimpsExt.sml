(* Immutable ingredients and public conversions only: no ordinary fragment,
   simpset or BasicProvers update-log inspection. Install these explicitly,
   SET_SPEC then GSPEC_SIMP, at the corresponding default recipe steps. *)
structure pred_setSimpsExt :> pred_setSimpsExt =
struct

open HolKernel boolLib

local
  val GSPEC_t = prim_mk_const {Name = "GSPEC", Thy = "pred_set"}
  val IN_t = mk_thy_const {Name = "IN", Thy = "bool",
                          Ty = alpha --> (alpha --> bool) --> bool}
  val f_t = mk_var ("f", beta --> pairSyntax.mk_prod (alpha, bool))
  val x_t = mk_var ("x", alpha)
in
  val SET_SPEC_ss = simpExtLib.register_frag
    (simpExtLib.SSFRAG
      {name = SOME "SET_SPEC", ac = [], congs = [],
       convs = [{conv = K (K (PGspec.SET_SPEC_CONV
                               pred_setTheory.GSPECIFICATION)),
                 key = SOME ([],list_mk_comb
                                  (IN_t,[x_t,mk_comb (GSPEC_t,f_t)])),
                 name = "SET_SPEC_CONV", trace = 2}],
       dprocs = [], filter = NONE, rewrs = []})
end

val GSPEC_SIMP_ss = let
  val f = mk_var ("f", beta --> pairSyntax.mk_prod (alpha, bool))
in
  simpExtLib.register_frag
    (simpExtLib.SSFRAG
      {ac = [], name = SOME "GSPEC_SIMP", congs = [],
       convs = [{key = SOME ([],mk_comb (pred_setSyntax.gspec_tm,f)),
                 conv = K (K pred_setSimps.GSPEC_SIMP_CONV), trace = 2,
                 name = "GSPEC_SIMP_CONV"}],
       rewrs = [], dprocs = [], filter = NONE})
end

end
