structure realLinarith :> realLinarith =
struct

open Abbrev HolKernel Conv Drule Rewrite

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

fun mk_sum [] = realSyntax.zero_tm
  | mk_sum [tm] = tm
  | mk_sum terms = realSyntax.list_mk_plus terms

fun ac_equality left right =
  if Term.aconv left right then Thm.REFL left
  else
    EQT_ELIM
      (AC_CONV
        (realTheory.REAL_ADD_ASSOC, realTheory.REAL_ADD_COMM)
        (boolSyntax.mk_eq (left, right)))

fun cancel_common cancel tm =
  let
    val operator = Term.rator (Term.rator tm)
    val (left, right) =
      if realSyntax.is_leq tm then realSyntax.dest_leq tm
      else if realSyntax.is_less tm then realSyntax.dest_less tm
      else boolSyntax.dest_eq tm
    fun summands expression =
      case realSyntax.strip_plus expression of
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
                    val target = realSyntax.mk_plus
                      (common, realSyntax.zero_tm)
                    val expanded =
                      Thm.SYM
                        (Thm.SPEC common realTheory.REAL_ADD_RID)
                  in
                    (target,
                     Thm.TRANS (ac_equality original common) expanded)
                  end
              | cancellation_side original rest =
                  let
                    val target = realSyntax.mk_plus (common, mk_sum rest)
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

fun safe_conv conversion tm =
  conversion tm
  handle HOL_ERR _ => Thm.REFL tm
       | UNCHANGED => Thm.REFL tm

fun expression_conv tm =
  if Term.type_of tm = realSyntax.real_ty then
    (safe_conv
       (TOP_DEPTH_CONV
         (FIRST_CONV
           [REWR_CONV intrealTheory.real_of_int_neg,
            REWR_CONV intrealTheory.real_of_int_num])) THENC
     TRY_CONV RealField.REAL_POLY_CONV THENC
     TRY_CONV realSimps.REALADDCANON THENC
     TRY_CONV RealField.REAL_RAT_REDUCE_CONV) tm
  else raise UNCHANGED

fun relation_conv tm =
  let
    val cancel =
      if realSyntax.is_leq tm then realTheory.REAL_LE_LADD
      else if realSyntax.is_less tm then realTheory.REAL_LT_LADD
      else if boolSyntax.is_eq tm andalso
              Term.type_of (#1 (boolSyntax.dest_eq tm)) =
                realSyntax.real_ty
      then realTheory.REAL_EQ_LADD
      else raise UNCHANGED
  in
    (BINOP_CONV expression_conv THENC
     REPEATC (cancel_common cancel) THENC
     TRY_CONV RealField.REAL_RAT_REDUCE_CONV THENC
     TRY_CONV
       (simpLib.SIMP_CONV boolSimps.bool_ss
          [realTheory.REAL_LT_REFL,
           realTheory.REAL_LE_REFL])) tm
  end

fun norm_conv tm =
  (relation_conv ORELSEC expression_conv ORELSEC ALL_CONV) tm

fun nonneg tm =
  case Lib.total realSyntax.dest_injected tm of
      SOME n => SOME (Thm.SPEC n realTheory.REAL_POS)
    | NONE => NONE

val instance : linarithData.linarith_instance =
  {ty = realSyntax.real_ty,
   discrete = false,
   dest =
     {dest_plus = realSyntax.dest_plus,
      dest_minus = SOME realSyntax.dest_minus,
      dest_neg = SOME realSyntax.dest_negated,
      dest_mult = realSyntax.dest_mult,
      dest_div = SOME realSyntax.dest_div,
      dest_suc = NONE,
      dest_lit = RealArith.rat_of_term,
      mk_lit = RealArith.term_of_rat,
      dest_less = realSyntax.dest_less,
      dest_leq = realSyntax.dest_leq},
   kit =
     {add_mono =
        [realTheory.REAL_LE_ADD2,
         realTheory.REAL_LT_ADD2,
         realTheory.REAL_LET_ADD2,
         realTheory.REAL_LTE_ADD2],
      mult_mono =
        [realTheory.REAL_LE_LMUL_IMP,
         realTheory.REAL_LT_LMUL_IMP],
      lessD = [],
      not_less = realTheory.REAL_NOT_LT,
      not_le = realTheory.REAL_NOT_LE,
      neqE = linarithInstTheory.REAL_NEQ_E,
      nonneg = nonneg},
   norm_conv = norm_conv,
   pre_split =
     [linarithInstTheory.REAL_MIN_SPLIT,
      linarithInstTheory.REAL_MAX_SPLIT,
      linarithInstTheory.REAL_ABS_SPLIT],
   atom_facts = (fn _ => []),
   divmod_facts = NONE}

val _ = linarithData.register_instance instance

val _ =
  linarithData.register_injection
    {from_ty = numSyntax.num,
     to_ty = realSyntax.real_ty,
     inj = realSyntax.real_injection,
     hom =
       {le = realTheory.REAL_OF_NUM_LE,
        lt = realTheory.REAL_OF_NUM_LT,
        eq = realTheory.REAL_OF_NUM_EQ,
        add = realTheory.REAL_OF_NUM_ADD,
        mul = realTheory.REAL_OF_NUM_MUL}}

val _ =
  linarithData.register_injection
    {from_ty = intSyntax.int_ty,
     to_ty = realSyntax.real_ty,
     inj = intrealSyntax.real_of_int_tm,
     hom =
       {le = intrealTheory.real_of_int_le,
        lt = intrealTheory.real_of_int_lt,
        eq = intrealTheory.real_of_int_11,
        add = intrealTheory.real_of_int_add,
        mul = intrealTheory.real_of_int_mul}}

end
