structure linarithNum :> linarithNum =
struct

open HolKernel Conv Drule Rewrite

fun dest_lit tm =
  Arbrat.fromNat (numSyntax.dest_numeral tm)
  handle HOL_ERR _ =>
    Arbrat.+ (Arbrat.one, dest_lit (numSyntax.dest_suc tm))

fun mk_lit value = numSyntax.mk_numeral (Arbrat.toNat value)

val ac_ops : linarithCancel.ac_ops =
  {dest_less = numSyntax.dest_less,
   dest_leq = numSyntax.dest_leq,
   strip_plus = numSyntax.strip_plus,
   mk_plus = numSyntax.mk_plus,
   zero = numSyntax.zero_tm,
   assoc = arithmeticTheory.ADD_ASSOC,
   comm = arithmeticTheory.ADD_COMM,
   rid = arithmeticTheory.ADD_0,
   ac_fallback = SOME numSimps.ADDR_CANON_CONV}

val cancel_common = linarithCancel.cancel_common ac_ops

(* The cancellation theorem for a relation of this carrier, and NONE for
   anything else.  Deciding this once is what lets norm_conv dispatch:
   ORELSEC catches HOL_ERR only, so an alternative that signals "not
   mine" by raising UNCHANGED is never reached past. *)
fun cancel_rule tm =
  if numSyntax.is_leq tm then SOME arithmeticTheory.LE_ADD_LCANCEL
  else if numSyntax.is_less tm then SOME arithmeticTheory.LT_ADD_LCANCEL
  else if boolSyntax.is_eq tm andalso
          Term.type_of (#1 (boolSyntax.dest_eq tm)) = numSyntax.num
  then SOME arithmeticTheory.EQ_ADD_LCANCEL
  else NONE

(* Products need canonicalizing as well as sums.  Replay scales a row by
   a literal, and a row scaled twice arrives as t * 2 * 3; cancellation
   matches summands syntactically, so without MUL_CANON_CONV that term
   never meets the t * 6 on the other side and a correct certificate
   replays to a true relation rather than to falsity.  The int and real
   instances get this from their polynomial normalizers; num has no
   polynomial conversion and composes the two canonicalizers itself. *)
fun expression_conv tm =
  if Term.type_of tm = numSyntax.num then
    (Conv.DEPTH_CONV numSimps.MUL_CANON_CONV THENC
     numSimps.ADDR_CANON_CONV THENC
     TRY_CONV reduceLib.REDUCE_CONV) tm
  else raise Conv.UNCHANGED

fun relation_conv tm =
  case cancel_rule tm of
      NONE => raise UNCHANGED
    | SOME cancel =>
        (BINOP_CONV expression_conv THENC
         REPEATC (cancel_common cancel) THENC
         TRY_CONV reduceLib.REDUCE_CONV THENC
         TRY_CONV
           (simpLib.SIMP_CONV boolSimps.bool_ss
              [prim_recTheory.LESS_REFL,
               arithmeticTheory.LESS_EQ_REFL])) tm

fun dispatch tm =
  case cancel_rule tm of
      SOME _ => relation_conv tm
    | NONE => expression_conv tm

fun norm_conv tm =
  (Conv.DEPTH_CONV
     (Conv.REWR_CONV arithmeticTheory.ADD1 ORELSEC
      Conv.REWR_CONV arithmeticTheory.LEFT_ADD_DISTRIB ORELSEC
      Conv.REWR_CONV arithmeticTheory.RIGHT_ADD_DISTRIB ORELSEC
      Conv.CHANGED_CONV reduceLib.REDUCE_CONV) THENC dispatch) tm

fun positive_literal divisor =
  let
    val test = numSyntax.mk_less (numSyntax.zero_tm, divisor)
  in
    SOME (EQT_ELIM (reduceLib.REDUCE_CONV test))
    handle HOL_ERR _ => NONE
  end

fun dest_divmod tm =
  case Lib.total numSyntax.dest_div tm of
      SOME args => SOME args
    | NONE => Lib.total numSyntax.dest_mod tm

(* atom_facts sees every atom of every carrier; dest_divmod declines the
   ones outside the naturals. *)
fun atom_facts tm =
  case dest_divmod tm of
      NONE => []
    | SOME (dividend, divisor) =>
        if Term.aconv divisor numSyntax.zero_tm then
          if numSyntax.is_mod tm then
            [SPEC dividend
               (GEN_ALL (CONJUNCT1 arithmeticTheory.MOD_0))]
          else
            [SPEC dividend
               (GEN_ALL (CONJUNCT1 arithmeticTheory.DIV_0))]
        else
          case positive_literal divisor of
              NONE => []
            | SOME positive =>
                CONJUNCTS
                  (SPEC dividend
                    (MP (SPEC divisor arithmeticTheory.DIVISION) positive))

fun nonneg tm =
  if Term.type_of tm = numSyntax.num then
    SOME (SPEC tm arithmeticTheory.ZERO_LESS_EQ)
  else NONE

val lessD =
  REWRITE_RULE [arithmeticTheory.ADD1] arithmeticTheory.LESS_EQ

val instance : linarithData.linarith_instance =
  {ty = numSyntax.num,
   discrete = SOME {lessD = [lessD]},
   dest =
     {dest_plus = numSyntax.dest_plus,
      dest_minus = NONE,
      dest_neg = NONE,
      dest_mult = numSyntax.dest_mult,
      dest_div = NONE,
      dest_suc = SOME numSyntax.dest_suc,
      dest_lit = dest_lit,
      mk_lit = mk_lit,
      dest_less = numSyntax.dest_less,
      dest_leq = numSyntax.dest_leq},
   kit =
     {add_mono =
        [arithmeticTheory.LESS_EQ_LESS_EQ_MONO,
         linarithSeedTheory.NUM_LT_ADD2,
         linarithSeedTheory.NUM_LET_ADD2,
         linarithSeedTheory.NUM_LTE_ADD2],
      mult_mono =
        [arithmeticTheory.LESS_MONO_MULT,
         arithmeticTheory.LT_MULT_LCANCEL],
      not_less = arithmeticTheory.NOT_LESS,
      not_le = arithmeticTheory.NOT_LESS_EQUAL,
      neqE = linarithSeedTheory.NUM_NEQ_E,
      nonneg = nonneg},
   norm_conv = norm_conv,
   nnf_rules = [arithmeticTheory.SUB_EQ_0],
   pre_split =
     [linarithSeedTheory.NUM_MIN_SPLIT,
      linarithSeedTheory.NUM_MAX_SPLIT,
      linarithSeedTheory.NUM_SUB_SPLIT],
   atom_facts = atom_facts}

end
