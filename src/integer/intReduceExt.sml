(* Immutable original keys and literal guard; share the public evaluator.
   No ordinary fragment, simpset, update log or replay is imported. *)
structure intReduceExt :> intReduceExt =
struct

open HolKernel boolSyntax intSyntax

local
  val x = mk_var ("x", int_ty)
  val y = mk_var ("y", int_ty)
  val n = mk_var ("n", numSyntax.num)
  val basic_op_patterns = map (fn t => list_mk_comb (t, [x,y]))
    [plus_tm, minus_tm, mult_tm, div_tm, mod_tm, int_eq_tm,
     less_tm, leq_tm, greater_tm, geq_tm, divides_tm, rem_tm, quot_tm,
     min_tm, max_tm]
  val exp_pattern = list_mk_comb (exp_tm, [x,n])
  val abs_patterns =
    [lhs (#2 (strip_forall (concl integerTheory.INT_ABS_NEG))),
     lhs (#2 (strip_forall (concl integerTheory.INT_ABS_NUM)))]
  fun reducible t = is_int_literal t orelse numSyntax.is_numeral t
  fun reducer t = let
    val (_,args) = strip_comb t
  in
    if List.all reducible args then intReduce.REDUCE_CONV t
    else Conv.NO_CONV t
  end
  fun mk_conv pat =
    {name = "Integer calculation", key = SOME ([],pat), trace = 2,
     conv = K (K reducer)}
in
  val INT_REDUCE_ss = simpExtLib.register_frag (simpExtLib.SSFRAG
    {name = SOME "INT_REDUCE",
     convs = map mk_conv (exp_pattern :: (abs_patterns @ basic_op_patterns)),
     rewrs = [], congs = [], filter = NONE, ac = [], dprocs = []})
end

end
