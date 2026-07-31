structure linarithNum :> linarithNum =
struct

open Abbrev HolKernel Conv Drule Rewrite

fun dest_lit tm =
  Arbrat.fromNat (numSyntax.dest_numeral tm)
  handle HOL_ERR _ =>
    Arbrat.+ (Arbrat.one, dest_lit (numSyntax.dest_suc tm))

fun mk_lit value = numSyntax.mk_numeral (Arbrat.toNat value)

fun remove_aconv _ [] = NONE
  | remove_aconv tm (item :: rest) =
      if Term.aconv tm item then SOME rest
      else Option.map (fn rest' => item :: rest') (remove_aconv tm rest)

fun common_summand [] _ = NONE
  | common_summand (item :: rest) right =
      case remove_aconv item right of
          SOME right' => SOME (item, rest, right')
        | NONE =>
            Option.map
              (fn (common, left, right') =>
                  (common, item :: left, right'))
              (common_summand rest right)

fun mk_sum [] = numSyntax.zero_tm
  | mk_sum [tm] = tm
  | mk_sum terms = numSyntax.list_mk_plus terms

fun ac_equality left right =
  if Term.aconv left right then Thm.REFL left
  else
    EQT_ELIM
      (AC_CONV
        (arithmeticTheory.ADD_ASSOC, arithmeticTheory.ADD_COMM)
        (boolSyntax.mk_eq (left, right)))

fun cancel_common cancel tm =
  let
    val operator = Term.rator (Term.rator tm)
    val (left, right) =
      if numSyntax.is_leq tm then numSyntax.dest_leq tm
      else if numSyntax.is_less tm then numSyntax.dest_less tm
      else boolSyntax.dest_eq tm
    val lefts = numSyntax.strip_plus left
    val rights = numSyntax.strip_plus right
  in
    case common_summand lefts rights of
        NONE => raise UNCHANGED
      | SOME (common, left', right') =>
          let
            val left_target = numSyntax.mk_plus (common, mk_sum left')
            val right_target = numSyntax.mk_plus (common, mk_sum right')
            val left_thm = ac_equality left left_target
            val right_thm = ac_equality right right_target
            val relation_thm =
              Thm.MK_COMB (Thm.AP_TERM operator left_thm, right_thm)
            val cancel_thm =
              REWR_CONV cancel
                (#2 (boolSyntax.dest_eq (Thm.concl relation_thm)))
          in
            Thm.TRANS relation_thm cancel_thm
          end
  end

fun relation_conv tm =
  let
    val cancel =
      if numSyntax.is_leq tm then arithmeticTheory.LE_ADD_LCANCEL
      else if numSyntax.is_less tm then arithmeticTheory.LT_ADD_LCANCEL
      else if boolSyntax.is_eq tm andalso
              Term.type_of (#1 (boolSyntax.dest_eq tm)) = numSyntax.num
      then arithmeticTheory.EQ_ADD_LCANCEL
      else raise UNCHANGED
  in
    (BINOP_CONV numSimps.ADDR_CANON_CONV THENC
     REPEATC (cancel_common cancel) THENC
     TRY_CONV reduceLib.REDUCE_CONV THENC
     TRY_CONV (simpLib.SIMP_CONV boolSimps.bool_ss [])) tm
  end

fun expression_conv tm =
  if Term.type_of tm = numSyntax.num then
    (numSimps.ADDR_CANON_CONV THENC
     TRY_CONV reduceLib.REDUCE_CONV) tm
  else raise Conv.UNCHANGED

fun norm_conv tm =
  (Conv.DEPTH_CONV
     (Conv.REWR_CONV arithmeticTheory.ADD1 ORELSEC
      Conv.CHANGED_CONV reduceLib.REDUCE_CONV) THENC
   (relation_conv ORELSEC expression_conv ORELSEC Conv.ALL_CONV)) tm

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

fun divmod_facts tm =
  case dest_divmod tm of
      NONE => []
    | SOME (dividend, divisor) =>
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
   discrete = true,
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
      lessD = [lessD],
      not_less = arithmeticTheory.NOT_LESS,
      not_le = arithmeticTheory.NOT_LESS_EQUAL,
      neqE = linarithSeedTheory.NUM_NEQ_E,
      nonneg = nonneg},
   norm_conv = norm_conv,
   pre_split =
     [linarithSeedTheory.NUM_MIN_SPLIT,
      linarithSeedTheory.NUM_MAX_SPLIT,
      linarithSeedTheory.NUM_SUB_SPLIT],
   divmod_facts = SOME divmod_facts}

end
