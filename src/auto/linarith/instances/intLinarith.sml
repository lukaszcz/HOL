structure intLinarith :> intLinarith =
struct

open Abbrev HolKernel Conv Drule Rewrite

fun dest_lit tm =
  Arbrat.fromAInt (intSyntax.int_of_term tm)

fun mk_lit value = intSyntax.term_of_int (Arbrat.toAInt value)

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

fun mk_sum [] = intSyntax.zero_tm
  | mk_sum [tm] = tm
  | mk_sum terms = intSyntax.list_mk_plus terms

fun ac_equality left right =
  if Term.aconv left right then Thm.REFL left
  else
    EQT_ELIM
      (AC_CONV
        (integerTheory.INT_ADD_ASSOC, integerTheory.INT_ADD_COMM)
        (boolSyntax.mk_eq (left, right)))

fun cancel_common cancel tm =
  let
    val operator = Term.rator (Term.rator tm)
    val (left, right) =
      if intSyntax.is_leq tm then intSyntax.dest_leq tm
      else if intSyntax.is_less tm then intSyntax.dest_less tm
      else boolSyntax.dest_eq tm
    fun summands expression =
      case intSyntax.strip_plus expression of
          [] => [expression]
        | terms => terms
    val lefts = summands left
    val rights = summands right
  in
    case common_summand lefts rights of
        NONE => raise UNCHANGED
      | SOME (_, [], []) => raise UNCHANGED
      | SOME (common, left', right') =>
          let
            fun cancellation_side original [] =
                  let
                    val target = intSyntax.mk_plus
                      (common, intSyntax.zero_tm)
                    val expanded =
                      Thm.SYM
                        (Thm.SPEC common integerTheory.INT_ADD_RID)
                  in
                    (target,
                     Thm.TRANS (ac_equality original common) expanded)
                  end
              | cancellation_side original rest =
                  let
                    val target = intSyntax.mk_plus (common, mk_sum rest)
                  in
                    (target, ac_equality original target)
                  end
            val (left_target, left_thm) =
              cancellation_side left left'
            val (right_target, right_thm) =
              cancellation_side right right'
            val relation_thm =
              Thm.MK_COMB (Thm.AP_TERM operator left_thm, right_thm)
            val cancel_thm =
              REWR_CONV cancel
                (#2 (boolSyntax.dest_eq (Thm.concl relation_thm)))
          in
            Thm.TRANS relation_thm cancel_thm
          end
  end

fun expression_conv tm =
  if Term.type_of tm = intSyntax.int_ty then
    (TRY_CONV intLib.INT_POLY_CONV THENC
     TRY_CONV intSimps.ADDR_CANON_CONV THENC
     TRY_CONV intReduce.RED_CONV) tm
  else raise UNCHANGED

fun relation_conv tm =
  let
    val cancel =
      if intSyntax.is_leq tm then integerTheory.INT_LE_LADD
      else if intSyntax.is_less tm then integerTheory.INT_LT_LADD
      else if boolSyntax.is_eq tm andalso
              Term.type_of (#1 (boolSyntax.dest_eq tm)) =
                intSyntax.int_ty
      then integerTheory.INT_EQ_LADD
      else raise UNCHANGED
  in
    (BINOP_CONV expression_conv THENC
     REPEATC (cancel_common cancel) THENC
     TRY_CONV intReduce.RED_CONV THENC
     TRY_CONV
       (simpLib.SIMP_CONV boolSimps.bool_ss
          [integerTheory.INT_LT_REFL,
           integerTheory.INT_LE_REFL])) tm
  end

fun norm_conv tm =
  (relation_conv ORELSEC expression_conv ORELSEC ALL_CONV) tm

fun nonzero_literal divisor =
  if not (intSyntax.is_int_literal divisor) then NONE
  else
    SOME
      (EQT_ELIM
        (intReduce.REDUCE_CONV
          (boolSyntax.mk_neg
            (boolSyntax.mk_eq (divisor, intSyntax.zero_tm)))))
    handle HOL_ERR _ => NONE

fun dest_divmod tm =
  case Lib.total intSyntax.dest_div tm of
      SOME args => SOME args
    | NONE => Lib.total intSyntax.dest_mod tm

(* INT_DIVISION exposes directly the quotient/remainder facts represented
   existentially by INT_DIV_P and INT_MOD_P, without adding split cases. *)
fun division_facts dividend divisor nonzero =
  let
    val division =
      Thm.SPEC dividend
        (Thm.MP
          (Thm.SPEC divisor integerTheory.INT_DIVISION)
          nonzero)
    val sign =
      intReduce.REDUCE_CONV
        (intSyntax.mk_less (divisor, intSyntax.zero_tm))
  in
    CONJUNCTS
      (simpLib.SIMP_RULE boolSimps.bool_ss [sign] division)
  end

fun divmod_facts tm =
  case dest_divmod tm of
      NONE => []
    | SOME (dividend, divisor) =>
        case nonzero_literal divisor of
            NONE => []
          | SOME nonzero =>
              division_facts dividend divisor nonzero

fun nonneg tm =
  case Lib.total intSyntax.dest_injected tm of
      SOME n => SOME (Thm.SPEC n integerTheory.INT_POS)
    | NONE => NONE

fun atom_facts tm =
  case Lib.total intSyntax.dest_Num tm of
      SOME i => [Thm.SPEC i integerTheory.INT_OF_NUM]
    | NONE => []

val instance : linarithData.linarith_instance =
  {ty = intSyntax.int_ty,
   discrete = true,
   dest =
     {dest_plus = intSyntax.dest_plus,
      dest_minus = SOME intSyntax.dest_minus,
      dest_neg = SOME intSyntax.dest_negated,
      dest_mult = intSyntax.dest_mult,
      dest_div = NONE,
      dest_suc = NONE,
      dest_lit = dest_lit,
      mk_lit = mk_lit,
      dest_less = intSyntax.dest_less,
      dest_leq = intSyntax.dest_leq},
   kit =
     {add_mono =
        [integerTheory.INT_LE_ADD2,
         integerTheory.INT_LT_ADD2,
         linarithInstTheory.INT_LET_ADD2,
         linarithInstTheory.INT_LTE_ADD2],
      mult_mono =
        [linarithInstTheory.INT_LE_LMUL_POS,
         linarithInstTheory.INT_LT_LMUL_POS],
      lessD = [integerTheory.INT_LT_LE1],
      not_less = integerTheory.INT_NOT_LT,
      not_le = integerTheory.INT_NOT_LE,
      neqE = linarithInstTheory.INT_NEQ_E,
      nonneg = nonneg},
   norm_conv = norm_conv,
   pre_split =
     [linarithInstTheory.INT_MIN_SPLIT,
      linarithInstTheory.INT_MAX_SPLIT,
      linarithInstTheory.INT_ABS_SPLIT],
   atom_facts = atom_facts,
   divmod_facts = SOME divmod_facts}

val _ = linarithData.register_instance instance

val _ =
  linarithData.register_injection
    {from_ty = numSyntax.num,
     to_ty = intSyntax.int_ty,
     inj = intSyntax.int_injection,
     hom =
       {le = integerTheory.INT_LE,
        lt = integerTheory.INT_LT,
        eq = integerTheory.INT_INJ,
        add = integerTheory.INT_ADD,
        mul = integerTheory.INT_MUL}}

end
