(* numSimps's logged numeral recipes, built from immutable ingredients.
   No ordinary fragment, simpset, update log or replay is used here.
   The small private reduction guard and derived rewrite recipes match
   numSimps; the actual numeral and arithmetic conversions stay shared. *)
structure numSimpsExt :> numSimpsExt =
struct

open HolKernel Parse boolLib liteLib

structure Parse =
struct
  open Parse
  val SOME arithmetic_grammars = grammarDB {thyname="arithmetic"}
  val (Type,Term) = parse_from_grammars arithmetic_grammars
end
open Parse

val SSFRAG = simpExtLib.register_frag o simpExtLib.SSFRAG

local
  fun reducer t = let
    open numSyntax
    val (_, args) = strip_comb t
    fun reducible t =
      is_numeral t orelse (is_suc t andalso reducible (snd (dest_comb t)))
  in
    if List.all reducible args then
      CHANGED_CONV reduceLib.REDUCE_CONV t
    else NO_CONV t
  end
  fun mk_redconv0 pat =
    {name = "REDUCE_CONV (arithmetic reduction)", trace = 2,
     key = SOME ([], pat), conv = K (K reducer)}
  val x = mk_var ("x", numSyntax.num)
  val y = mk_var ("y", numSyntax.num)
  fun mk_unary_rconv op_t = mk_redconv0 (mk_comb (op_t, x))
  fun mk_redconv op_t = mk_redconv0 (list_mk_comb (op_t, [x,y]))
in
val REDUCE_ss = let
  open numSyntax
in
  SSFRAG
    {name = SOME "REDUCE",
     convs = mk_unary_rconv even_tm ::
             mk_unary_rconv odd_tm ::
             mk_unary_rconv pre_tm ::
             mk_unary_rconv suc_tm ::
             mk_unary_rconv div2_tm ::
             map mk_redconv [mult_tm, plus_tm, minus_tm,
                             div_tm, mod_tm, exp_tm,
                             less_tm, leq_tm, greater_tm, geq_tm,
                             min_tm, max_tm, Term`$= : num -> num -> bool`],
     rewrs = [], congs = [], filter = NONE, ac = [], dprocs = []}
end
end

(* Preserve both the input order and the original (including local) names.
   numSimps does not expose arithmetic_rewrites, so only these immutable
   theorem recipes are repeated, not its arithmetic decision procedure. *)
local
  open arithmeticTheory
  val ARITH = EQT_ELIM o Arith.ARITH_CONV
  val one_suc = Rewrite.PURE_REWRITE_RULE [ONE]
  val add_sym = Rewrite.ONCE_REWRITE_RULE [ADD_SYM]
in
val ARITH_RWTS_ss = SSFRAG
  {name = SOME "ARITH_RWTS", convs = [], congs = [], filter = NONE,
   ac = [], dprocs = [],
   rewrs =
    map (fn s => (SOME {Thy="arithmetic", Name=s},
                  DB.fetch "arithmetic" s)) [
      "ADD_0", "ADD_EQ_0", "ADD_INV_0_EQ", "MULT_EQ_0", "MULT_EQ_1", "MULT_0",
      "MULT_RIGHT_1", "MULT_LEFT_1", "SUB_EQUAL_0", "SUC_SUB1", "SUB_0",
      "ADD_SUB", "SUB_EQ_0", "SUB_LESS_EQ", "SUB_MONO_EQ", "SUB_RIGHT_GREATER",
      "SUB_RIGHT_LESS", "SUB_RIGHT_GREATER_EQ", "SUB_RIGHT_LESS_EQ",
      "EXP_EXP_INJECTIVE", "EXP_BASE_INJECTIVE", "EXP_BASE_LT_MONO",
      "EXP_BASE_LE_MONO", "EXP_EXP_LT_MONO", "EXP_EXP_LE_MONO",
      "LESS_EQ_0", "LESS_EQ_ADD", "LESS_EQ_REFL", "LESS_MONO_ADD_EQ",
      "ADD_MONO_LESS_EQ", "EQ_MONO_ADD_EQ", "LESS_MONO_EQ",
      "LESS_EQ_MONO", "LESS_MULT_MONO", "MULT_SUC_EQ", "MULT_MONO_EQ",
      "NOT_SUC_LESS_EQ", "MULT_EXP_MONO", "LE_MULT_LCANCEL",
      "LE_MULT_RCANCEL", "LT_MULT_LCANCEL", "LT_MULT_RCANCEL",
      "LT_MULT_CANCEL_LBARE", "LT_MULT_CANCEL_RBARE",
      "LE_MULT_CANCEL_LBARE", "LE_MULT_CANCEL_RBARE", "ZERO_LESS_EQ",
      "MIN_0", "MAX_0", "MIN_IDEM", "MAX_IDEM", "MIN_LE", "MAX_LE",
      "MIN_LT", "MAX_LT", "MIN_MAX_EQ", "MIN_MAX_LT",
      "X_MOD_Y_EQ_X", "DIV_1", "MOD_1", "LESS_MOD",
      "ZERO_MOD", "MOD_MOD", "NUMERAL_MULT_EQ_DIV", "MOD_LESS", "DIV_LESS",
      "NOT_EXP_0", "NOT_ODD_EQ_EVEN", "NOT_SUC_ADD_LESS_EQ",
      "NOT_SUC_LESS_EQ_0"
    ] @
    map (fn (nm,th) => (SOME {Thy="", Name=nm}, th)) [
      ("SUC_EQ_1",
       ARITH(Term`!x. ((SUC x = 1) = (x=0)) /\ ((1 = SUC x) = (x = 0))`)),
      ("SUC_EQ_2",
       ARITH(Term`!x. ((SUC x = 2) = (x=1)) /\ ((2 = SUC x) = (x = 1))`)),
      ("ADD_0'", add_sym ADD_0),
      ("ADD_INV_0_EQ'", add_sym ADD_INV_0_EQ),
      ("MULT_0'", ONCE_REWRITE_RULE [MULT_COMM] MULT_0),
      ("MULT_EQ_SUC0", one_suc MULT_EQ_1),
      ("PRE", prim_recTheory.PRE), ("ADD_SUB'", add_sym ADD_SUB),
      ("LESS_0", prim_recTheory.LESS_0),
      ("SUC_GT0", ARITH ``SUC x > 0``),
      ("GEQ0", ARITH ``x >= 0``),
      ("X_LT_SUC", ARITH ``x < SUC x``),
      ("X_LE_SUC", ARITH ``x <= SUC x``),
      ("X_LT_X_PLUS", ARITH ``x < x + c <=> 0 < c``),
      ("X_LT_PLUS_X", ARITH ``x < c + x <=> 0 < c``),
      ("X_LE_X_PLUS", ARITH ``x <= x + c <=> 0 <= c``),
      ("X_LE_PLUS_X", ARITH ``x <= c + x <=> 0 <= c``),
      ("GEQ_REFL", ARITH ``x >= x``),
      ("LESS_MONO_ADD_EQ'", add_sym LESS_MONO_ADD_EQ),
      ("ADD_MONO_LESS_EQ", add_sym ADD_MONO_LESS_EQ),
      ("EQ_MONO_ADD_EQ", add_sym EQ_MONO_ADD_EQ),
      ("X_PLUS_LT_PLUS_X", ARITH ``x + y < w + x <=> y < w``),
      ("PLUS_X_LT_X_PLUS", ARITH ``y + x < x + w <=> y < w``),
      ("INV_SUC_EQ", prim_recTheory.INV_SUC_EQ),
      ("GT_REFL", ARITH ``~(x > x)``),
      ("LESS_REFL", prim_recTheory.LESS_REFL),
      ("NOT_LESS_0", prim_recTheory.NOT_LESS_0)
    ]}
end

(* MOD needs a relational reducer and congruences, not ARITH_DP or a
   separate numeral fragment. relsimp_ss constructs the reducer from these
   theorem inputs; simpExtLib explicitly lifts its opaque ordinary reducer.
   Relational rewrites are not native equality rewrite-source handles. *)
val MOD_ss = let
  open arithmeticTheory simpExtLib
  val rsd = {refl = MODEQ_REFL, trans = MODEQ_TRANS,
             weakenings = [MODEQ_INTRO_CONG], subsets = [],
             rewrs = [MODEQ_NUMERAL, MODEQ_MOD, MODEQ_0]}
  val RSD_ss = relsimp_ss rsd
  val congs = SSFRAG
    {dprocs = [], ac = [], rewrs = [],
     congs = [MODEQ_PLUS_CONG, MODEQ_MULT_CONG, MODEQ_SUC_CONG,
              MODEQ_EXP_CONG],
     filter = NONE, convs = [], name = NONE}
in
  merge_ss [RSD_ss, congs] |> name_ss "MOD"
end

end
