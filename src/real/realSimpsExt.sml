(* Only the logged real defaults.  Reconstruct the immutable literal
   theorem recipes; share the public arithmetic conversions, not ordinary
   fragments, compiled sets, registries, or update logs. *)
structure realSimpsExt :> realSimpsExt =
struct

open HolKernel Parse boolLib realTheory realSyntax simpExtLib
structure Parse = struct
  open Parse
  val (Type,Term) = parse_from_grammars $ valOf $ grammarDB {thyname = "real"}
end
open Parse
val SSFRAG = register_frag o SSFRAG

local
  (* Specialisation only needs boolean/numeral rewriting, not the pair
     fragment or the arithmetic decision procedure in realSimps.arith_ss. *)
  val arith_ss = boolSimpsExt.bool_ss ++ numSimpsExt.ARITH_RWTS_ss ++
                 numSimpsExt.REDUCE_ss
  val num_eq_0 = realTheory.num_eq_0
  datatype splitting = posneg | posneg0 | nb12
  fun splitfn split rv nv th = let
    open numSyntax
    val injected = mk_injected (mk_comb(numeral_tm, nv))
  in
    case split of
      posneg => [INST [rv |-> injected] th,
                 INST [rv |-> mk_negated injected] th]
    | posneg0 => INST [rv |-> realSyntax.zero_tm] th ::
                splitfn posneg rv nv th
    | nb12 => map (fn bit => INST [rv |-> mk_injected
                 (mk_comb(numeral_tm, mk_comb(bit, nv)))] th)
                  [bit1_tm, bit2_tm]
  end
  fun transform vs th = let
    val T_imp = hd (CONJUNCTS (SPEC_ALL IMP_CLAUSES))
    val rwt = REWRITE_CONV
      ([REAL_INJ, REAL_NEGNEG, REAL_NEG_EQ0, num_eq_0, REAL_LT, REAL_LE,
        REAL_DIV_LZERO, REAL_MUL_RZERO, REAL_MUL_LZERO,
        REAL_ADD_LID, REAL_ADD_RID, arithmeticTheory.ZERO_LESS_EQ] @
       map (fn n => List.nth(CONJUNCTS le_int, n)) [1,3])
    fun simp t =
      ((if is_imp t then LAND_CONV rwt THENC REWR_CONV T_imp
        else ALL_CONV) THENC RAND_CONV rwt) t
    fun recurse [] th = [th]
      | recurse ((v,split)::rest) th = let
          val nv = mk_var(#1 (dest_var v), numSyntax.num)
        in
          List.concat (map (recurse rest)
            (map (CONV_RULE simp) (splitfn split v nv th)))
        end
  in recurse vs th end
  val x = mk_var("x", real_ty)
  val y = mk_var("y", real_ty)
  val z = mk_var("z", real_ty)
  val u = mk_var("u", real_ty)
  val v = mk_var("v", real_ty)
  val ratvars = [(x,posneg), (y,nb12), (u,posneg), (v,nb12)]
  val leftvars = [(x,posneg), (y,nb12), (z,posneg0)]
  val rightvars = [(x,posneg0), (y,posneg), (z,nb12)]
  val add_rats = transform ratvars add_rat
  val add_ratls = transform leftvars add_ratl
  val add_ratrs = transform rightvars add_ratr
  val mult_rats = transform ratvars mult_rat
  val mult_ratls = transform leftvars mult_ratl
  val mult_ratrs = transform rightvars mult_ratr
  val neg_ths = REAL_NEG_0 :: transform [(y,nb12)] neg_rat
  val sub1 = transform ratvars (SPECL [mk_div(x,y),mk_div(u,v)] real_sub)
  val sub2 = transform [(x,posneg0), (u,posneg), (v,nb12)]
                       (SPECL [x,mk_div(u,v)] real_sub)
  val sub3 = transform leftvars (SPECL [mk_div(x,y),z] real_sub)
  val sub4 = transform [(x,posneg0),(y,posneg0)] (SPEC_ALL real_sub)
  val div_rats = transform ratvars div_rat
  val div_ratls = transform [(x,posneg),(y,nb12),(z,nb12)] div_ratl
  val div_ratrs = transform [(x,posneg),(z,nb12),(y,posneg)] div_ratr
  val div_eq_1 = transform [(x,nb12)] (SPEC_ALL REAL_DIV_REFL)
  fun extrema th =
    (transform [(x,posneg0),(y,posneg0)] (SPEC_ALL th),
     transform ratvars (SPECL [mk_div(x,y),mk_div(u,v)] th),
     transform [(x,posneg),(y,nb12),(u,posneg0)]
               (SPECL [mk_div(x,y),u] th),
     transform [(x,posneg),(y,nb12),(u,posneg0)]
               (SPECL [u,mk_div(x,y)] th))
  val (max_ints,max_rats,max_ratls,max_ratrs) = extrema max_def
  val (min_ints,min_rats,min_ratls,min_ratrs) = extrema min_def
  val (a,b,c,d) = Lib.quadruple_of_list (CONJUNCTS NUM_FLOOR_EQNS)
  val rule = REWRITE_RULE [GSYM arithmeticTheory.NOT_ZERO_LT_ZERO, num_eq_0]
  val r1 = rule o Q.INST [`m` |-> `NUMERAL (BIT1 m)`]
  val r2 = rule o Q.INST [`m` |-> `NUMERAL (BIT2 m)`]
  val flr = LIST_CONJ [a,b,r1 c,r2 c,r1 d,r2 d]
  val abs1 = transform [(x,posneg),(y,nb12)]
                       (SPEC (mk_div(x,y)) realTheory.abs)
  val abs2 = transform [(x,posneg)] (SPEC x realTheory.abs)
  val n = mk_var("n", numSyntax.num)
  val m = mk_var("m", numSyntax.num)
  fun to_numeraln th = INST
    [n |-> mk_comb(numSyntax.numeral_tm,n),
     m |-> mk_comb(numSyntax.numeral_tm,m)] th
  val clg0 = SIMP_RULE boolSimpsExt.bool_ss [flr,LET_THM]
                       (SPEC ``0r`` NUM_CEILING_NUM_FLOOR)
  val op_rwts =
    [to_numeraln mult_ints, to_numeraln add_ints, flr, clg0,
     REAL_DIV_LZERO, REAL_NEGNEG] @
    transform [(x,posneg)] (SPEC x NUM_CEILING_NUM_FLOOR) @
    (transform [(x,posneg),(y,nb12)]
       (SPEC (mk_div(x,y)) NUM_CEILING_NUM_FLOOR)
     |> map (SIMP_RULE arith_ss
          [REAL_LE_LDIV_EQ, REAL_LT, REAL_LE, REAL_MUL_LZERO,
           REAL_NEG_LE0, ltnb12, flr, let_id])) @
    transform [(x,posneg0)] (SPEC_ALL REAL_ADD_LID) @
    transform [(x,posneg)] (SPEC_ALL REAL_ADD_RID) @
    transform [(x,posneg0)] (SPEC_ALL REAL_MUL_LZERO) @
    transform [(x,posneg)] (SPEC_ALL REAL_MUL_RZERO) @
    neg_ths @ add_rats @ add_ratls @ add_ratrs @
    mult_rats @ mult_ratls @ mult_ratrs @ sub1 @ sub2 @ sub3 @ sub4 @
    div_rats @ div_ratls @ div_ratrs @ div_eq_1 @
    max_ratls @ max_ratrs @ max_rats @ max_ints @
    min_ratls @ min_ratrs @ min_rats @ min_ints @
    (REAL_ABS_0 :: abs1) @ abs2
  fun nat2nat th = let
    val simp = REWRITE_RULE [REAL_INJ, REAL_NEGNEG, REAL_NEG_EQ0, num_eq_0]
    val th0 = if free_in ``n:num`` (concl th) then
      map simp [INST [``n:num`` |-> ``NUMERAL (BIT1 n)``] th,
                INST [``n:num`` |-> ``NUMERAL (BIT2 n)``] th]
      else [th]
  in
    if free_in ``m:num`` (concl th) then
      List.concat (map (fn th => map simp
        [INST [``m:num`` |-> ``NUMERAL (BIT1 m)``] th,
         INST [``m:num`` |-> ``NUMERAL (BIT2 m)``] th]) th0)
    else th0
  end
  fun relations vars th = List.concat (map (transform vars) (nat2nat th))
  val lt_rats = relations [(x,posneg),(u,posneg)] lt_rat
  val lt_ratls = relations [(x,posneg),(u,posneg0)] lt_ratl
  val lt_ratrs = relations [(x,posneg0),(u,posneg)] lt_ratr
  val le_rats = relations [(x,posneg),(u,posneg)] le_rat
  val le_ratls = relations [(x,posneg),(u,posneg0)] le_ratl
  val le_ratrs = relations [(x,posneg0),(u,posneg)] le_ratr
  val eq_rats = transform ratvars eq_rat
  val eq_ratls = transform leftvars eq_ratl
  val eq_ratrs = transform leftvars eq_ratr
  fun realrels th =
    transform [(x,posneg0),(y,posneg0)] (SPEC_ALL th) @
    transform ratvars (SPECL [mk_div(x,y),mk_div(u,v)] th) @
    transform [(x,posneg),(y,nb12),(u,posneg0)]
              (SPECL [mk_div(x,y),u] th) @
    transform [(x,posneg),(y,nb12),(u,posneg0)]
              (SPECL [u,mk_div(x,y)] th)
  val rel_rwts = [eq_ints,le_int,lt_int] @
    eq_rats @ eq_ratls @ eq_ratrs @ lt_rats @ lt_ratls @ lt_ratrs @
    le_rats @ le_ratrs @ le_ratls @ realrels real_gt @ realrels real_ge
  val rwts = pow_rat :: (op_rwts @ rel_rwts)
  val ecf_patterns =
    [Term`&(NUMERAL n) / &(NUMERAL (BIT1 m))`,
     Term`&(NUMERAL n) / &(NUMERAL (BIT2 m))`,
     Term`~&(NUMERAL n) / &(NUMERAL (BIT1 m))`,
     Term`~&(NUMERAL n) / &(NUMERAL (BIT2 m))`]
in
val REAL_REDUCE_ss = SSFRAG
  {name = SOME "REAL_REDUCE", ac = [], congs = [], dprocs = [],
   filter = NONE, rewrs = map (fn th => (NONE,th)) rwts,
   convs = map (fn p =>
     {conv = K (K realSimps.elim_common_factor), key = SOME ([],p),
      name = "realSimps.elim_common_factor", trace = 2}) ecf_patterns}
end

val x = mk_var("x",real_ty)
val y = mk_var("y",real_ty)
val z = mk_var("z",real_ty)
val n = mk_var("n",numSyntax.num)
val RMULCANON_ss = SSFRAG
  {name = SOME "RMULCANON", ac = [], congs = [], dprocs = [],
   filter = NONE, rewrs = [], convs =
    [{conv = K (K realSimps.REALMULCANON), trace = 2,
      key = SOME ([],mk_mult(x,y)), name = "REALMULCANON"}]}
val RMULRELNORM_ss = SSFRAG
  {name = SOME "RMULRELNORM", ac = [], congs = [], dprocs = [],
   filter = NONE, rewrs = [], convs =
    [{key = SOME ([],mk_leq(x,y)), name = "RMUL_LEQNORM", trace = 2,
      conv = realSimps.mulrelnorm leq_tm
               [(REAL_LE_LMUL,rhs),(REAL_LE_LMUL_NEG,rhs)]},
     {key = SOME ([],mk_eq(x,mk_mult(y,z))),
      name = "RMUL_EQNORM1", trace = 2,
      conv = realSimps.mulrelnorm equality [(REAL_EQ_LMUL,rand o rhs)]},
     {key = SOME ([],mk_eq(mk_mult(x,y),z)),
      name = "RMUL_EQNORM2", trace = 2,
      conv = realSimps.mulrelnorm equality [(REAL_EQ_LMUL,rand o rhs)]},
     {key = SOME ([],mk_eq(mk_div(x,y),z)),
      name = "RMUL_EQNORM3", trace = 2,
      conv = realSimps.mulrelnorm equality [(REAL_EQ_LMUL,rand o rhs)]},
     {key = SOME ([],mk_eq(z,mk_div(x,y))),
      name = "RMUL_EQNORM4", trace = 2,
      conv = realSimps.mulrelnorm equality [(REAL_EQ_LMUL,rand o rhs)]},
     {key = SOME ([],mk_eq(mk_pow(x,n),z)),
      name = "RMUL_EQNORM5", trace = 2,
      conv = realSimps.mulrelnorm equality [(REAL_EQ_LMUL,rand o rhs)]},
     {key = SOME ([],mk_eq(z,mk_pow(x,n))),
      name = "RMUL_EQNORM6", trace = 2,
      conv = realSimps.mulrelnorm equality [(REAL_EQ_LMUL,rand o rhs)]},
     {key = SOME ([],mk_less(x,y)), name = "RMUL_LTNORM", trace = 2,
      conv = realSimps.mulrelnorm less_tm
               [(REAL_LT_LMUL,rhs),(REAL_LT_LMUL_NEG,rhs)]}]}
end
