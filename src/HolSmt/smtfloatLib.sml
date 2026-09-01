(* Copyright (c) 2026 The HOL4 contributors. *)

(* Certifying ground conversions for SMT-LIB floating-point rounding.
   All numerical work is discharged by kernel-checked word and real
   conversions.  In particular, this library does not use the native IEEE
   hardware evaluators. *)
structure smtfloatLib :> smtfloatLib =
struct

open HolKernel Parse boolLib bossLib
open realSyntax binary_ieeeSyntax
open smtfloatIntegralRoundTheory
structure IntegralRound = smtfloatIntegralRoundTheory

val ERR = Feedback.mk_HOL_ERR "smtfloatLib"
val lhsc = boolSyntax.lhs o Thm.concl
val rhsc = boolSyntax.rhs o Thm.concl

fun mk_tw (t, w) =
  boolSyntax.mk_itself (pairSyntax.mk_prod (t, w))

fun mk_large tw = binary_ieeeSyntax.mk_largest (mk_tw tw)
fun mk_neg tm = realSyntax.mk_negated tm
fun mk_not tm = boolSyntax.mk_neg tm
fun mk_eq (l, r) = boolSyntax.mk_eq (l, r)
fun mk_leq (l, r) = realSyntax.mk_leq (l, r)
fun mk_lt (l, r) = realSyntax.mk_less (l, r)

fun mk_next_hi tm =
  Term.mk_comb
    (Term.mk_thy_const
       {Thy = "binary_ieee", Name = "next_hi",
        Ty = Type.mk_type
          ("fun", [Term.type_of tm, Term.type_of tm])}, tm)

fun prove tm =
  Drule.EQT_ELIM (EVAL tm)
  handle HOL_ERR _ =>
    let
      val thm = simpLib.SIMP_CONV (bossLib.srw_ss ())
        [binary_ieeeTheory.float_is_integral_def,
         binary_ieeeTheory.is_integral_def,
         binary_ieeeTheory.float_value_def,
         binary_ieeeTheory.float_to_real_def,
         realTheory.abs] tm
    in
      Drule.EQT_ELIM thm
      handle HOL_ERR _ =>
        raise ERR "prove"
          ("stuck at: " ^ Parse.term_to_string (rhsc thm))
    end

fun can_prove tm =
  Lib.can prove tm

fun certify thm ants =
  let
    fun prove_antecedent tm =
      prove tm
      handle HOL_ERR e =>
        raise ERR "certify"
          ("could not reduce premise: " ^ Parse.term_to_string tm ^
           "; " ^ Feedback.message_of e)
  in
    Drule.MATCH_MP thm (Drule.LIST_CONJ (map prove_antecedent ants))
  end

fun normalize_rhs thm =
  Conv.CONV_RULE (Conv.RAND_CONV EVAL) thm

fun finite tm = binary_ieeeSyntax.mk_float_is_finite tm
fun zero tm = binary_ieeeSyntax.mk_float_is_zero tm
fun f2r tm = binary_ieeeSyntax.mk_float_to_real tm

fun limit_CONV (mode, x, tw) =
  let
    val large = mk_large tw
    val nlarge = mk_neg large
  in
    if mode ~~ binary_ieeeSyntax.roundTowardPositive_tm then
      if can_prove (mk_lt (large, x)) then
        SOME (Drule.MATCH_MP
          binary_ieeeTheory.round_roundTowardPositive_plus_infinity
          (prove (mk_lt (large, x))))
      else if can_prove (mk_lt (x, nlarge)) then
        SOME (Drule.MATCH_MP
          binary_ieeeTheory.round_roundTowardPositive_bottom
          (prove (mk_lt (x, nlarge))))
      else NONE
    else if mode ~~ binary_ieeeSyntax.roundTowardNegative_tm then
      if can_prove (mk_lt (x, nlarge)) then
        SOME (Drule.MATCH_MP
          binary_ieeeTheory.round_roundTowardNegative_minus_infinity
          (prove (mk_lt (x, nlarge))))
      else if can_prove (mk_lt (large, x)) then
        SOME (Drule.MATCH_MP
          binary_ieeeTheory.round_roundTowardNegative_top
          (prove (mk_lt (large, x))))
      else NONE
    else NONE
  end

fun directed_finite_CONV (mode, x, t, w) =
  let
    val tw = (t, w)
    val large = mk_large tw
    val ulp = binary_ieeeSyntax.mk_ulp (mk_tw tw)
    val small_rtp =
      mode ~~ binary_ieeeSyntax.roundTowardPositive_tm andalso
      can_prove (mk_lt (``0r``, x)) andalso
      can_prove (mk_leq (x, ulp))
    val small_rtn =
      mode ~~ binary_ieeeSyntax.roundTowardNegative_tm andalso
      can_prove (mk_leq (mk_neg ulp, x)) andalso
      can_prove (mk_lt (x, ``0r``))
    val rtzero =
      binary_ieeeSyntax.mk_round
        (binary_ieeeSyntax.roundTowardZero_tm, x, t, w)
  in
    if small_rtp then
      Drule.MATCH_MP smtfloatTheory.round_RTP_small_positive
        (prove (boolSyntax.mk_conj
          (mk_lt (``0r``, x), mk_leq (x, ulp))))
      |> normalize_rhs
    else if small_rtn then
      Drule.MATCH_MP smtfloatTheory.round_RTN_small_negative
        (prove (boolSyntax.mk_conj
          (mk_leq (mk_neg ulp, x), mk_lt (x, ``0r``))))
      |> normalize_rhs
    else
      let
        val zero_thm = binary_ieeeLib.round_CONV rtzero
        val lo = rhsc zero_thm
        val rlo = f2r lo
        val next = mk_next_hi lo
        val rnext = f2r next
        val bounds = [mk_leq (mk_neg large, x), mk_leq (x, large)]
        fun common y = bounds @ [finite y, mk_not (zero y)]
        val exact = can_prove (mk_eq (rlo, x))
        val thm =
          if exact andalso
             mode ~~ binary_ieeeSyntax.roundTowardPositive_tm then
            certify smtfloatTheory.round_RTP_exact
              (common lo @ [mk_eq (rlo, x)])
          else if exact then
            certify smtfloatTheory.round_RTN_exact
              (common lo @ [mk_eq (rlo, x)])
          else if mode ~~ binary_ieeeSyntax.roundTowardPositive_tm andalso
                  can_prove (mk_lt (``0r``, x)) then
            certify smtfloatTheory.round_RTP_positive_next_hi
              (bounds @ [finite lo, finite next, mk_not (zero next),
                         mk_leq (``0r``, rlo), mk_lt (rlo, x),
                         mk_leq (x, rnext)])
          else if mode ~~ binary_ieeeSyntax.roundTowardPositive_tm then
            certify smtfloatTheory.round_RTP_negative_inward
              (common lo @ [mk_lt (rnext, x), mk_leq (x, rlo),
                            mk_lt (rlo, ``0r``),
                            mk_lt (rnext, ``0r``)])
          else if can_prove (mk_lt (``0r``, x)) then
            certify smtfloatTheory.round_RTN_positive_inward
              (common lo @ [mk_lt (``0r``, rlo), mk_leq (rlo, x),
                            mk_lt (x, rnext),
                            mk_lt (``0r``, rnext)])
          else
            certify smtfloatTheory.round_RTN_negative_next_hi
              (bounds @ [finite lo, finite next,
                         mk_not (zero next), mk_leq (rnext, x),
                         mk_lt (x, rlo), mk_lt (rlo, ``0r``),
                         mk_lt (rnext, ``0r``)])
      in
        normalize_rhs thm
      end
  end

fun round_CONV tm =
  let
    val (mode, x, t, w) = binary_ieeeSyntax.dest_round tm
  in
    if mode ~~ binary_ieeeSyntax.roundTowardPositive_tm orelse
       mode ~~ binary_ieeeSyntax.roundTowardNegative_tm then
      case limit_CONV (mode, x, (t, w)) of
        SOME thm => normalize_rhs thm
      | NONE => directed_finite_CONV (mode, x, t, w)
    else
      binary_ieeeLib.round_CONV tm
  end
  handle HOL_ERR e =>
    raise ERR "round_CONV" (Feedback.message_of e)

fun float_round_CONV tm =
  if binary_ieeeSyntax.is_float_round tm then
    let
      val (mode, toneg, x, t, w) =
        binary_ieeeSyntax.dest_float_round tm
    in
      if mode ~~ binary_ieeeSyntax.roundTowardPositive_tm orelse
         mode ~~ binary_ieeeSyntax.roundTowardNegative_tm then
        let
          val rnd = round_CONV
            (binary_ieeeSyntax.mk_round (mode, x, t, w))
          val y = rhsc rnd
        in
          if binary_ieeeSyntax.is_float_plus_infinity y then
            Drule.MATCH_MP
              binary_ieeeTheory.float_round_plus_infinity rnd
            |> Thm.SPEC toneg
          else if binary_ieeeSyntax.is_float_minus_infinity y then
            Drule.MATCH_MP
              binary_ieeeTheory.float_round_minus_infinity rnd
            |> Thm.SPEC toneg
          else if binary_ieeeSyntax.is_float_top y then
            Drule.MATCH_MP binary_ieeeTheory.float_round_top rnd
            |> Thm.SPEC toneg
          else if binary_ieeeSyntax.is_float_bottom y then
            Drule.MATCH_MP binary_ieeeTheory.float_round_bottom rnd
            |> Thm.SPEC toneg
          else
            let
              val (_, e, f) =
                binary_ieeeSyntax.dest_floating_point y
              val nz = boolSyntax.mk_disj
                (mk_not (mk_eq
                   (e, wordsSyntax.mk_n2w (numSyntax.zero_tm, w))),
                 mk_not (mk_eq
                   (f, wordsSyntax.mk_n2w (numSyntax.zero_tm, t))))
            in
              Drule.MATCH_MP binary_ieeeTheory.float_round_non_zero
                (Thm.CONJ rnd (prove nz))
              |> Thm.SPEC toneg
            end
        end
      else
        binary_ieeeLib.float_round_CONV tm
    end
  else
    raise ERR "float_round_CONV" "not a float_round term"

fun dest_float_type ty =
  case Type.dest_thy_type ty of
    {Thy = "binary_ieee", Tyop = "float", Args = [t, w]} => (t, w)
  | _ => raise ERR "dest_float_type" "not a float type"

fun dest_named_unop thy name tm =
  let
    val (f, x) = Term.dest_comb tm
    val {Thy, Name, ...} = Term.dest_thy_const f
  in
    if Thy = thy andalso Name = name then x
    else raise ERR "dest_named_unop" "wrong constant"
  end

fun abs_diff (y, x) =
  realSyntax.mk_absval (realSyntax.mk_minus (f2r y, x))

fun round_tiesToAway_CONV tm =
  let
    val x = dest_named_unop "smtfloat" "round_tiesToAway" tm
    val (t, w) = dest_float_type (Term.type_of tm)
    val threshold = binary_ieeeSyntax.mk_threshold (mk_tw (t, w))
    val nthreshold = mk_neg threshold
  in
    if can_prove (mk_leq (x, nthreshold)) then
      Drule.MATCH_MP
        (cj 1 smtfloatTheory.round_tiesToAway_overflow)
        (prove (mk_leq (x, nthreshold)))
      |> normalize_rhs
    else if can_prove (mk_leq (threshold, x)) then
      Drule.MATCH_MP
        (cj 2 smtfloatTheory.round_tiesToAway_overflow)
        (prove (mk_leq (threshold, x)))
      |> normalize_rhs
    else
      let
        val ulp = binary_ieeeSyntax.mk_ulp (mk_tw (t, w))
        val half = mk_eq
          (realSyntax.mk_mult
             (``2r``, realSyntax.mk_absval x), ulp)
      in
        if can_prove half then
          if can_prove (mk_lt (``0r``, x)) then
            Drule.MATCH_MP
              smtfloatTheory.round_tiesToAway_half_ulp_positive
              (prove (boolSyntax.mk_conj
                (mk_lt (``0r``, x),
                 mk_eq (realSyntax.mk_mult (``2r``, x), ulp))))
            |> normalize_rhs
          else
            Drule.MATCH_MP
              smtfloatTheory.round_tiesToAway_half_ulp_negative
              (prove (boolSyntax.mk_conj
                (mk_lt (x, ``0r``),
                 mk_eq
                   (realSyntax.mk_mult (``2r``, mk_neg x), ulp))))
            |> normalize_rhs
        else
          let
            val bounds =
              [mk_not (mk_eq (x, ``0r``)), mk_lt (nthreshold, x),
               mk_lt (x, threshold)]
            val rne = round_CONV
              (binary_ieeeSyntax.mk_round
                 (binary_ieeeSyntax.roundTiesToEven_tm, x, t, w))
            val even = rhsc rne
            val reven = f2r even
            val away_even =
              can_prove (mk_leq
                (realSyntax.mk_absval x, realSyntax.mk_absval reven))
            val closest_even =
              Drule.MATCH_MP smtfloatTheory.round_RNE_is_closest
                (prove (boolSyntax.list_mk_conj
                  [mk_lt (nthreshold, x), mk_lt (x, threshold)]))
              |> REWRITE_RULE [rne]
          in
            if away_even then
              Drule.MATCH_MP
                smtfloatTheory.round_tiesToAway_from_closest_away
                (Drule.LIST_CONJ
                  (map prove bounds @
                   [closest_even, prove (mk_not (zero even)),
                    prove (mk_leq
                      (realSyntax.mk_absval x,
                       realSyntax.mk_absval reven))]))
              |> normalize_rhs
            else
              let
                val next = mk_next_hi even
                val same_distance =
                  mk_eq (abs_diff (next, x), abs_diff (even, x))
              in
                if can_prove same_distance then
                  let
                    val closest = Drule.MATCH_MP
                      smtfloatTheory.is_closest_finite_equal_distance
                      (Drule.LIST_CONJ
                        [closest_even, prove (finite next),
                         prove same_distance])
                  in
                    Drule.MATCH_MP
                      smtfloatTheory.round_tiesToAway_from_closest_away
                      (Drule.LIST_CONJ
                        (map prove bounds @
                         [closest, prove (mk_not (zero next)),
                          prove (mk_leq
                            (realSyntax.mk_absval x,
                             realSyntax.mk_absval (f2r next)))]))
                    |> normalize_rhs
                  end
                else if can_prove (mk_lt (``0r``, x)) then
                  Drule.MATCH_MP
                    smtfloatTheory.round_tiesToAway_positive_inward
                    (Drule.LIST_CONJ
                      (map prove
                         [mk_lt (nthreshold, x), mk_lt (x, threshold)] @
                       [closest_even] @
                       map prove
                         [finite even, mk_not (zero even), finite next,
                          mk_lt (``0r``, reven), mk_lt (reven, x),
                          mk_lt (x, f2r next),
                          mk_lt (abs_diff (even, x),
                                 abs_diff (next, x))]))
                  |> normalize_rhs
                else
                  Drule.MATCH_MP
                    smtfloatTheory.round_tiesToAway_negative_inward
                    (Drule.LIST_CONJ
                      (map prove
                         [mk_lt (nthreshold, x), mk_lt (x, threshold)] @
                       [closest_even] @
                       map prove
                         [finite even, mk_not (zero even), finite next,
                          mk_lt (reven, ``0r``), mk_lt (x, reven),
                          mk_lt (f2r next, x),
                          mk_lt (abs_diff (even, x),
                                 abs_diff (next, x))]))
                  |> normalize_rhs
              end
          end
        end
  end

fun real_to_arbrat tm =
  let
    fun positive t =
      case Lib.total realSyntax.dest_injected t of
        SOME n => Arbrat.fromNat (numLib.dest_numeral n)
      | NONE => raise ERR "real_to_arbrat" "not a ground rational"
    fun signed t =
      case Lib.total realSyntax.dest_negated t of
        SOME n => Arbrat.negate (positive n)
      | NONE => positive t
  in
    case Lib.total realSyntax.dest_div tm of
      SOME (n, d) => Arbrat./ (signed n, signed d)
    | NONE => signed tm
  end

fun nearest_away_integer tm =
  let
    val r = real_to_arbrat tm
    val half = Arbrat./ (Arbrat.one, Arbrat.two)
    val magnitude = Arbrat.floor (Arbrat.+ (Arbrat.abs r, half))
  in
    if Arbrat.< (r, Arbrat.zero) then Arbint.~ magnitude else magnitude
  end

fun nearest_even_integer tm =
  let
    val r = real_to_arbrat tm
    val lo = Arbrat.floor r
    val frac = Arbrat.- (r, Arbrat.fromAInt lo)
    val half = Arbrat./ (Arbrat.one, Arbrat.two)
  in
    case Arbrat.compare (frac, half) of
      LESS => lo
    | GREATER => Arbint.+ (lo, Arbint.one)
    | EQUAL =>
        if Arbint.mod (Arbint.abs lo, Arbint.two) = Arbint.zero then lo
        else Arbint.+ (lo, Arbint.one)
  end

fun integral_integer (mode, x) =
  let
    val r = real_to_arbrat x
  in
    if mode ~~ binary_ieeeSyntax.roundTiesToEven_tm then
      nearest_even_integer x
    else if mode ~~ binary_ieeeSyntax.roundTowardPositive_tm then
      Arbrat.ceil r
    else if mode ~~ binary_ieeeSyntax.roundTowardNegative_tm then
      Arbrat.floor r
    else if mode ~~ binary_ieeeSyntax.roundTowardZero_tm then
      if Arbrat.< (r, Arbrat.zero) then Arbrat.ceil r else Arbrat.floor r
    else
      raise ERR "integral_integer" "unsupported binary rounding mode"
  end

fun prove_even_abs (i, ry) =
  let
    val n = Arbint.abs i
    val ntm = numSyntax.mk_numeral (Arbint.toNat n)
    val nvar = Term.mk_var ("n", numSyntax.num)
    val body = boolSyntax.mk_conj
      (numSyntax.mk_even nvar,
       mk_eq (realSyntax.mk_absval ry, realSyntax.mk_injected nvar))
    val ex = boolSyntax.mk_exists (nvar, body)
    val witness = Thm.CONJ
      (prove (numSyntax.mk_even ntm))
      (prove (mk_eq
        (realSyntax.mk_absval ry, realSyntax.mk_injected ntm)))
  in
    Thm.EXISTS (ex, ntm) witness
  end

fun prove_float_even_abs y =
  let
    val ry = f2r y
    val normalized = rhsc (EVAL ry)
    val i = nearest_even_integer normalized
  in
    prove_even_abs (i, ry)
  end

fun mk_named_unop thy name result_ty arg =
  Term.mk_comb
    (Term.mk_thy_const
       {Thy = thy, Name = name,
        Ty = Type.mk_type
          ("fun", [realSyntax.real_ty, result_ty])}, arg)

fun integral_round_tiesToAway_CONV tm =
  let
    val x =
      dest_named_unop "smtfloat" "integral_round_tiesToAway" tm
    val result_ty = Term.type_of tm
    val (t, w) = dest_float_type result_ty
    val threshold = binary_ieeeSyntax.mk_threshold (mk_tw (t, w))
    val nthreshold = mk_neg threshold
  in
    if can_prove (mk_leq (x, nthreshold)) then
      Drule.MATCH_MP
        (cj 1 smtfloatTheory.integral_round_tiesToAway_overflow)
        (prove (mk_leq (x, nthreshold)))
      |> normalize_rhs
    else if can_prove (mk_leq (threshold, x)) then
      Drule.MATCH_MP
        (cj 2 smtfloatTheory.integral_round_tiesToAway_overflow)
        (prove (mk_leq (threshold, x)))
      |> normalize_rhs
    else
      let
        val pinf =
          binary_ieeeSyntax.mk_float_plus_infinity (mk_tw (t, w))
        val ninf =
          binary_ieeeSyntax.mk_float_minus_infinity (mk_tw (t, w))
        val ordinary_thm = round_tiesToAway_CONV
          (mk_named_unop
             "smtfloat" "round_tiesToAway" result_ty x)
        val ordinary = rhsc ordinary_thm
        val ordinary_integral =
          binary_ieeeSyntax.mk_float_is_integral ordinary
        val bounds =
          [mk_not (mk_eq (x, ``0r``)), mk_lt (nthreshold, x),
           mk_lt (x, threshold)]
      in
        if can_prove ordinary_integral andalso
           can_prove (mk_not (zero ordinary)) then
          Drule.MATCH_MP
            smtfloatTheory.integral_round_tiesToAway_from_float_round
            (Drule.LIST_CONJ
              (map prove bounds @ [ordinary_thm] @
               map prove
                 [ordinary_integral, mk_not (zero ordinary),
                  mk_lt (abs_diff (ordinary, x), abs_diff (pinf, x)),
                  mk_lt (abs_diff (ordinary, x), abs_diff (ninf, x))]))
          |> normalize_rhs
        else
          let
            val i = nearest_away_integer x
            val ri = realSyntax.term_of_int i
            val rounded = round_tiesToAway_CONV
              (mk_named_unop
                 "smtfloat" "round_tiesToAway" result_ty ri)
            val y = rhsc rounded
            val ry = f2r y
            val twice_distance =
              realSyntax.mk_mult
                (``2r``,
                 realSyntax.mk_absval (realSyntax.mk_minus (ry, x)))
            val common =
              bounds @
              [binary_ieeeSyntax.mk_float_is_integral y,
               mk_not (zero y)]
            val limits =
              [mk_lt (abs_diff (y, x), abs_diff (pinf, x)),
               mk_lt (abs_diff (y, x), abs_diff (ninf, x))]
          in
            if can_prove (mk_lt (twice_distance, ``1r``)) then
              certify
                smtfloatTheory.integral_round_tiesToAway_strict_nearest
                (common @ [mk_lt (twice_distance, ``1r``)] @ limits)
              |> normalize_rhs
            else
              certify smtfloatTheory.integral_round_tiesToAway_nearest
                (common @
                 [mk_leq (twice_distance, ``1r``),
                  mk_leq
                    (realSyntax.mk_absval x,
                     realSyntax.mk_absval ry)] @ limits)
              |> normalize_rhs
          end
      end
  end
  handle HOL_ERR e =>
    raise ERR "integral_round_tiesToAway_CONV" (Feedback.message_of e)

fun integral_round_CONV tm =
  let
    val (mode, x) = binary_ieeeSyntax.dest_integral_round tm
    val (t, w) = dest_float_type (Term.type_of tm)
    val tw = mk_tw (t, w)
    val large = binary_ieeeSyntax.mk_largest tw
    val nlarge = mk_neg large
    val threshold = binary_ieeeSyntax.mk_threshold tw
    val nthreshold = mk_neg threshold

    fun apply thm ant =
      Drule.MATCH_MP thm (prove ant) |> normalize_rhs

    fun rne_edge result cert (lower, upper, value) =
      let
        val y = rhsc result
        val even_abs = prove_float_even_abs y
        val ants = map prove
          [lower, upper, binary_ieeeSyntax.mk_float_is_integral y,
           value, mk_not (zero y)] @ [even_abs]
      in
        Drule.MATCH_MP cert (Drule.LIST_CONJ ants)
        |> normalize_rhs
      end
  in
    if mode ~~ binary_ieeeSyntax.roundTiesToEven_tm andalso
       can_prove (mk_leq (x, nthreshold)) then
      apply smtfloatIntegralRoundTheory.integral_round_RNE_underflow
        (mk_leq (x, nthreshold))
    else if mode ~~ binary_ieeeSyntax.roundTiesToEven_tm andalso
            can_prove (mk_leq (threshold, x)) then
      apply smtfloatIntegralRoundTheory.integral_round_RNE_overflow
        (mk_leq (threshold, x))
    else if can_prove (mk_lt (x, nlarge)) then
      if mode ~~ binary_ieeeSyntax.roundTowardZero_tm then
        apply smtfloatIntegralRoundTheory.integral_round_RTZ_underflow
          (mk_lt (x, nlarge))
      else if mode ~~ binary_ieeeSyntax.roundTowardPositive_tm then
        apply smtfloatIntegralRoundTheory.integral_round_RTP_underflow
          (mk_lt (x, nlarge))
      else if mode ~~ binary_ieeeSyntax.roundTowardNegative_tm then
        apply smtfloatIntegralRoundTheory.integral_round_RTN_underflow
          (mk_lt (x, nlarge))
      else if mode ~~ binary_ieeeSyntax.roundTiesToEven_tm andalso
              can_prove (mk_lt (nthreshold, x)) then
        let
          val result = apply
            smtfloatIntegralRoundTheory.integral_round_RTP_underflow
            (mk_lt (x, nlarge))
          val y = rhsc result
          val cert =
            IntegralRound.integral_round_RNE_just_above_underflow
        in
          rne_edge result cert
            (mk_lt (nthreshold, x), mk_lt (x, nlarge),
             mk_eq (f2r y, nlarge))
        end
      else
        raise ERR "integral_round_CONV" "unsupported binary rounding mode"
    else if can_prove (mk_lt (large, x)) then
      if mode ~~ binary_ieeeSyntax.roundTowardZero_tm then
        apply smtfloatIntegralRoundTheory.integral_round_RTZ_overflow
          (mk_lt (large, x))
      else if mode ~~ binary_ieeeSyntax.roundTowardPositive_tm then
        apply smtfloatIntegralRoundTheory.integral_round_RTP_overflow
          (mk_lt (large, x))
      else if mode ~~ binary_ieeeSyntax.roundTowardNegative_tm then
        apply smtfloatIntegralRoundTheory.integral_round_RTN_overflow
          (mk_lt (large, x))
      else if mode ~~ binary_ieeeSyntax.roundTiesToEven_tm andalso
              can_prove (mk_lt (x, threshold)) then
        let
          val result = apply
            smtfloatIntegralRoundTheory.integral_round_RTN_overflow
            (mk_lt (large, x))
          val y = rhsc result
          val cert =
            IntegralRound.integral_round_RNE_just_below_overflow
        in
          rne_edge result cert
            (mk_lt (large, x), mk_lt (x, threshold),
             mk_eq (f2r y, large))
        end
      else
        raise ERR "integral_round_CONV" "unsupported binary rounding mode"
    else if mode ~~ binary_ieeeSyntax.roundTowardPositive_tm orelse
            mode ~~ binary_ieeeSyntax.roundTowardNegative_tm then
      let
        val rounded = round_CONV
          (binary_ieeeSyntax.mk_round (mode, x, t, w))
        val y = rhsc rounded
        val ry = f2r y
        val integral = binary_ieeeSyntax.mk_float_is_integral y
        val nonzero = mk_not (zero y)
        val bounds = [mk_leq (nlarge, x), mk_leq (x, large)]
        val (cert, side) =
          if mode ~~ binary_ieeeSyntax.roundTowardPositive_tm then
            (IntegralRound.integral_round_RTP_from_float_round,
             realSyntax.mk_geq (ry, x))
          else
            (IntegralRound.integral_round_RTN_from_float_round,
             mk_leq (ry, x))
      in
        if can_prove integral andalso can_prove nonzero then
          Drule.MATCH_MP cert
            (Drule.LIST_CONJ
              (map prove bounds @ [rounded] @
               map prove [integral, side, nonzero]))
          |> normalize_rhs
        else
          let
            val i = integral_integer (mode, x)
            val ri = realSyntax.term_of_int i
            val fallback = round_CONV
              (binary_ieeeSyntax.mk_round (mode, ri, t, w))
            val fallback_y = rhsc fallback
            val fallback_ry = f2r fallback_y
            val fallback_integral =
              binary_ieeeSyntax.mk_float_is_integral fallback_y
            val fallback_nonzero = mk_not (zero fallback_y)
          in
            if not (can_prove fallback_nonzero) then
              raise ERR "integral_round_CONV"
                "zero result requires float-facing signed-zero restoration"
            else if mode ~~ binary_ieeeSyntax.roundTowardPositive_tm then
              certify IntegralRound.integral_round_RTP_inrange
                (bounds @
                 [mk_lt
                    (realSyntax.mk_minus (fallback_ry, ``1r``), x),
                  mk_leq (x, fallback_ry),
                  fallback_integral, fallback_nonzero])
              |> normalize_rhs
            else
              certify IntegralRound.integral_round_RTN_inrange
                (bounds @
                 [mk_leq (fallback_ry, x),
                  mk_lt (x, realSyntax.mk_plus (fallback_ry, ``1r``)),
                  fallback_integral, fallback_nonzero])
              |> normalize_rhs
          end
      end
    else
      let
        val i = integral_integer (mode, x)
        val ri = realSyntax.term_of_int i
        val rounded = round_CONV
          (binary_ieeeSyntax.mk_round (mode, ri, t, w))
        val y = rhsc rounded
        val ry = f2r y
        val integral = binary_ieeeSyntax.mk_float_is_integral y
        val nonzero = mk_not (zero y)
        val pinf = binary_ieeeSyntax.mk_float_plus_infinity tw
        val ninf = binary_ieeeSyntax.mk_float_minus_infinity tw
        val distance =
          realSyntax.mk_absval (realSyntax.mk_minus (ry, x))
      in
        if not (can_prove nonzero) then
          raise ERR "integral_round_CONV"
            "zero result requires float-facing signed-zero restoration"
        else if mode ~~ binary_ieeeSyntax.roundTiesToEven_tm then
          if can_prove
               (mk_leq
                  (realSyntax.mk_mult (``2r``, distance), ``1r``)) then
            let
              val even_abs = prove_even_abs (i, ry)
              val ants =
                map prove
                  [mk_lt (nthreshold, x), mk_lt (x, threshold),
                   integral, nonzero,
                   mk_leq
                     (realSyntax.mk_mult (``2r``, distance), ``1r``)] @
                [even_abs] @
                map prove
                  [mk_lt (distance,
                     realSyntax.mk_absval
                       (realSyntax.mk_minus (f2r pinf, x))),
                   mk_lt (distance,
                     realSyntax.mk_absval
                       (realSyntax.mk_minus (f2r ninf, x)))]
            in
              Drule.MATCH_MP
                smtfloatIntegralRoundTheory.integral_round_RNE_nearest
                (Drule.LIST_CONJ ants)
              |> normalize_rhs
            end
          else
            let
              fun directed mode =
                Term.mk_comb
                  (Term.mk_comb (Term.rator (Term.rator tm), mode), x)
              val floor_thm = integral_round_CONV
                (directed binary_ieeeSyntax.roundTowardNegative_tm)
              val ceiling_thm = integral_round_CONV
                (directed binary_ieeeSyntax.roundTowardPositive_tm)
              val lo = rhsc floor_thm
              val hi = rhsc ceiling_thm
              val rlo = f2r lo
              val rhi = f2r hi
              val lo_integral =
                binary_ieeeSyntax.mk_float_is_integral lo
              val hi_integral =
                binary_ieeeSyntax.mk_float_is_integral hi
              val lo_side = mk_leq (rlo, x)
              val hi_side = realSyntax.mk_geq (rhi, x)
              val bounds = [mk_leq (nlarge, x), mk_leq (x, large)]
              val floor_cert =
                IntegralRound.directed_floor_result_is_closest
              val floor_closest = Drule.MATCH_MP
                floor_cert
                (Drule.LIST_CONJ
                  (map prove bounds @ [floor_thm] @
                   map prove [lo_integral, lo_side]))
              val ceiling_cert =
                IntegralRound.directed_ceiling_result_is_closest
              val ceiling_closest = Drule.MATCH_MP
                ceiling_cert
                (Drule.LIST_CONJ
                  (map prove bounds @ [ceiling_thm] @
                   map prove [hi_integral, hi_side]))
              val dlo = abs_diff (lo, x)
              val dhi = abs_diff (hi, x)

              fun choose theorem chosen strict =
                let
                  val even_abs = prove_float_even_abs chosen
                  val ants =
                    map prove
                      [mk_lt (nthreshold, x), mk_lt (x, threshold)] @
                    [floor_closest, ceiling_closest] @
                    map prove
                      [lo_integral, lo_side, hi_integral, hi_side,
                       mk_not (zero chosen), strict] @
                    [even_abs]
                in
                  Drule.MATCH_MP theorem (Drule.LIST_CONJ ants)
                  |> normalize_rhs
                end
            in
              if can_prove (mk_lt (dlo, dhi)) then
                choose
                  IntegralRound.integral_round_RNE_from_directed_lower
                  lo (mk_lt (dlo, dhi))
              else if can_prove (mk_lt (dhi, dlo)) then
                choose
                  IntegralRound.integral_round_RNE_from_directed_upper
                  hi (mk_lt (dhi, dlo))
              else
                raise ERR "integral_round_CONV"
                  "ambiguous equidistant directed integral candidates"
            end
        else if mode ~~ binary_ieeeSyntax.roundTowardZero_tm andalso
                can_prove (mk_lt (``0r``, ry)) then
          certify smtfloatIntegralRoundTheory.integral_round_RTZ_positive
            [mk_lt (``0r``, ry), mk_leq (ry, x),
             mk_lt (x, realSyntax.mk_plus (ry, ``1r``)),
             mk_leq (x, large), integral]
          |> normalize_rhs
        else if mode ~~ binary_ieeeSyntax.roundTowardZero_tm then
          certify smtfloatIntegralRoundTheory.integral_round_RTZ_negative
            [mk_lt (ry, ``0r``),
             mk_lt (realSyntax.mk_minus (ry, ``1r``), x),
             mk_leq (x, ry), mk_leq (nlarge, x), integral]
          |> normalize_rhs
        else
          raise ERR "integral_round_CONV" "unsupported binary rounding mode"
      end
  end
  handle HOL_ERR e =>
    raise ERR "integral_round_CONV" (Feedback.message_of e)

fun reduce_rounding_case_CONV tm =
  (Conv.REWR_CONV smtfloatTheory.smt_round_def
   THENC simpLib.SIMP_CONV (bossLib.srw_ss ()) []) tm

fun reduce_integral_rounding_case_CONV tm =
  (Conv.REWR_CONV smtfloatTheory.smt_integral_round_def
   THENC simpLib.SIMP_CONV (bossLib.srw_ss ()) []) tm

fun smt_round_CONV tm =
  (reduce_rounding_case_CONV
   THENC (round_tiesToAway_CONV ORELSEC round_CONV)) tm

fun smt_integral_round_CONV tm =
  (reduce_integral_rounding_case_CONV
   THENC (integral_round_tiesToAway_CONV ORELSEC integral_round_CONV)) tm

(* Ground operation conversions.  The operation definitions are deliberately
   [nocompute]: several contain choice-based rounding definitions which must
   never be unfolded by the evaluator.  Each conversion exposes only the
   outer dispatch and then lets the registered certifying conversions reduce
   the resulting real arithmetic and IEEE operation. *)
fun unfold_and_eval def tm =
  (Conv.REWR_CONV def THENC EVAL) tm

val float_unordered_CONV =
  unfold_and_eval binary_ieeeTheory.float_unordered_def
fun smt_float_round_CONV tm =
  (Conv.REWR_CONV smtfloatTheory.smt_float_round_RNA_zero ORELSEC
   unfold_and_eval smtfloatTheory.smt_float_round_def) tm
val smt_float_add_CONV =
  unfold_and_eval smtfloatTheory.smt_float_add_def
val smt_float_sub_CONV =
  unfold_and_eval smtfloatTheory.smt_float_sub_def
val smt_float_mul_CONV =
  unfold_and_eval smtfloatTheory.smt_float_mul_def
val smt_float_div_CONV =
  unfold_and_eval smtfloatTheory.smt_float_div_def
val smt_float_sqrt_CONV =
  unfold_and_eval smtfloatTheory.smt_float_sqrt_def
val smt_float_fma_CONV =
  unfold_and_eval smtfloatTheory.smt_float_fma_def

fun mk_smt_integral_round (mode, x, result_ty) =
  Term.list_mk_comb
    (Term.mk_thy_const
       {Thy = "smtfloat", Name = "smt_integral_round",
        Ty = Type.mk_type
          ("fun", [Term.type_of mode,
            Type.mk_type ("fun", [realSyntax.real_ty, result_ty])])},
     [mode, x])

fun binary_integral_zero_class tm =
  let
    val (mode, x) = binary_ieeeSyntax.dest_integral_round tm
    val (t, w) = dest_float_type (Term.type_of tm)
    val tw = mk_tw (t, w)
    val large = binary_ieeeSyntax.mk_largest tw
    val threshold = binary_ieeeSyntax.mk_threshold tw
    val half = realSyntax.mk_div (``1r``, ``2r``)
    val absx = realSyntax.mk_absval x
    val bounds_threshold =
      [mk_lt (mk_neg threshold, x), mk_lt (x, threshold)]
    val bounds_largest =
      [mk_leq (mk_neg large, x), mk_leq (x, large)]
    fun all_provable ants = List.all can_prove ants
    fun use thm ants =
      if all_provable ants then certify thm ants
      else raise Conv.UNCHANGED
  in
    if mode ~~ binary_ieeeSyntax.roundTiesToEven_tm then
      use smtfloatIntegralRoundTheory.integral_round_RNE_zero_class
        (bounds_threshold @ [mk_leq (absx, half)])
    else if mode ~~ binary_ieeeSyntax.roundTowardZero_tm then
      use smtfloatIntegralRoundTheory.integral_round_RTZ_zero_class
        (bounds_largest @ [mk_lt (absx, ``1r``)])
    else if mode ~~ binary_ieeeSyntax.roundTowardPositive_tm then
      use smtfloatIntegralRoundTheory.integral_round_RTP_zero_class
        (bounds_largest @ [mk_lt (``~1r``, x), mk_leq (x, ``0r``)])
    else if mode ~~ binary_ieeeSyntax.roundTowardNegative_tm then
      use smtfloatIntegralRoundTheory.integral_round_RTN_zero_class
        (bounds_largest @ [mk_leq (``0r``, x), mk_lt (x, ``1r``)])
    else
      raise Conv.UNCHANGED
  end

fun smt_integral_zero_class tm =
  let
    val reduced = reduce_integral_rounding_case_CONV tm
    val binary_tm = rhsc reduced
    val zbinary =
      case Lib.total
        (dest_named_unop "smtfloat" "integral_round_tiesToAway")
        binary_tm of
        SOME x =>
        let
          val (t, w) = dest_float_type (Term.type_of binary_tm)
          val tw = mk_tw (t, w)
          val threshold = binary_ieeeSyntax.mk_threshold tw
          val pinf = binary_ieeeSyntax.mk_float_plus_infinity tw
          val ninf = binary_ieeeSyntax.mk_float_minus_infinity tw
          val absx = realSyntax.mk_absval x
          val half = realSyntax.mk_div (``1r``, ``2r``)
          val ants =
            [mk_lt (mk_neg threshold, x), mk_lt (x, threshold),
             mk_lt (absx, half),
             mk_lt (absx,
               realSyntax.mk_absval
                 (realSyntax.mk_minus (f2r pinf, x))),
             mk_lt (absx,
               realSyntax.mk_absval
                 (realSyntax.mk_minus (f2r ninf, x)))]
        in
          if List.all can_prove ants then
            certify
              smtfloatIntegralRoundTheory.integral_round_RNA_zero_class
              ants
          else raise Conv.UNCHANGED
        end
      | NONE => binary_integral_zero_class binary_tm
    val zeq =
      Conv.RAND_CONV (Conv.REWR_CONV reduced)
        (binary_ieeeSyntax.mk_float_is_zero tm)
  in
    Thm.EQ_MP (Thm.SYM zeq) zbinary
  end

fun dest_smt_float_round_to_integral tm =
  let
    val (head, args) = strip_comb tm
    val named = Lib.total Term.dest_thy_const head
  in
    case (named, args) of
        (SOME {Thy = "smtfloat", Name = "smt_float_round_to_integral",
               ...}, [mode, x]) => (mode, x)
      | _ => raise Conv.UNCHANGED
  end

fun checked_smt_float_round_to_integral_result tm thm =
  case Lib.total (boolSyntax.dest_eq o Thm.concl) thm of
      SOME (lhs, _) =>
        if Term.aconv lhs tm then thm
        else raise ERR "smt_float_round_to_integral_CONV"
          "proof conversion returned theorem for wrong left-hand side"
    | NONE => raise ERR "smt_float_round_to_integral_CONV"
        "proof conversion returned a non-equational theorem"

val smt_float_round_to_integral_checked_result_for_test =
  checked_smt_float_round_to_integral_result

fun smt_float_round_to_integral_CONV tm =
  let
    val (mode, x) = dest_smt_float_round_to_integral tm
    val value_thm = binary_ieeeLib.float_value_CONV
      (binary_ieeeSyntax.mk_float_value x)
    val result =
      if binary_ieeeSyntax.is_float (rhsc value_thm) then
        let
          val r = binary_ieeeSyntax.dest_float (rhsc value_thm)
          val integral = mk_smt_integral_round (mode, r, Term.type_of x)
          val zero_thm = smt_integral_zero_class integral
          val result = Drule.MATCH_MP
            smtfloatTheory.smt_float_round_to_integral_zero_class
            (Thm.CONJ value_thm zero_thm)
        in
          normalize_rhs result
        end
        handle Conv.UNCHANGED =>
          (Conv.REWR_CONV smtfloatTheory.smt_float_round_to_integral_def
           THENC Conv.ONCE_DEPTH_CONV
             (fn t => if binary_ieeeSyntax.is_float_value t then
                binary_ieeeLib.float_value_CONV t
              else raise Conv.UNCHANGED)
           THENC simpLib.SIMP_CONV pureSimps.pure_ss []
           THENC Conv.ONCE_DEPTH_CONV smt_integral_round_CONV
           THENC EVAL) tm
      else
        (Conv.REWR_CONV smtfloatTheory.smt_float_round_to_integral_def
         THENC EVAL) tm
  in
    checked_smt_float_round_to_integral_result tm result
  end
val float_min_CONV = unfold_and_eval smtfloatTheory.float_min_def
val float_max_CONV = unfold_and_eval smtfloatTheory.float_max_def
val smt_nearest_integer_CONV =
  unfold_and_eval smtfloatTheory.smt_nearest_integer_def
val float_rem_CONV = unfold_and_eval smtfloatTheory.float_rem_def
val smt_integer_ties_to_away_CONV =
  unfold_and_eval smtfloatTheory.smt_integer_ties_to_away_def
val smt_real_to_int_CONV =
  unfold_and_eval smtfloatTheory.smt_real_to_int_def
val float_to_ubv_CONV =
  unfold_and_eval smtfloatTheory.float_to_ubv_def
val float_to_sbv_CONV =
  unfold_and_eval smtfloatTheory.float_to_sbv_def
val smt_float_to_real_CONV =
  unfold_and_eval smtfloatTheory.smt_float_to_real_def
val smt_float_to_fp_CONV =
  unfold_and_eval smtfloatTheory.smt_float_to_fp_def
val smt_real_to_fp_CONV =
  unfold_and_eval smtfloatTheory.smt_real_to_fp_def
val smt_ubv_to_fp_CONV =
  unfold_and_eval smtfloatTheory.smt_ubv_to_fp_def
val smt_sbv_to_fp_CONV =
  unfold_and_eval smtfloatTheory.smt_sbv_to_fp_def

fun ground_predicate_CONV tm =
  simpLib.SIMP_CONV (bossLib.srw_ss ())
    [binary_ieeeTheory.float_is_integral_def,
     binary_ieeeTheory.is_integral_def,
     binary_ieeeTheory.float_value_def,
     binary_ieeeTheory.float_to_real_def,
     realTheory.abs] tm

fun thy_const thy name =
  Term.prim_mk_const {Thy = thy, Name = name}

fun smtfloat_const name = thy_const "smtfloat" name

fun add_smtfloat_to_compset cs =
  let
    open computeLib
    val conversions =
      [(binary_ieeeSyntax.round_tm, 2, round_CONV),
       (binary_ieeeSyntax.float_round_tm, 3, float_round_CONV),
       (thy_const "binary_ieee" "float_is_integral", 1,
        ground_predicate_CONV),
       (thy_const "binary_ieee" "float_unordered", 2,
        float_unordered_CONV),
       (smtfloat_const "round_tiesToAway", 1,
        round_tiesToAway_CONV),
       (smtfloat_const "integral_round_tiesToAway", 1,
        integral_round_tiesToAway_CONV),
       (smtfloat_const "smt_round", 2, smt_round_CONV),
       (smtfloat_const "smt_integral_round", 2,
        smt_integral_round_CONV),
       (smtfloat_const "smt_float_round", 3,
        smt_float_round_CONV),
       (smtfloat_const "smt_float_add", 3, smt_float_add_CONV),
       (smtfloat_const "smt_float_sub", 3, smt_float_sub_CONV),
       (smtfloat_const "smt_float_mul", 3, smt_float_mul_CONV),
       (smtfloat_const "smt_float_div", 3, smt_float_div_CONV),
       (smtfloat_const "smt_float_sqrt", 2, smt_float_sqrt_CONV),
       (smtfloat_const "smt_float_fma", 4, smt_float_fma_CONV),
       (smtfloat_const "smt_float_round_to_integral", 2,
        smt_float_round_to_integral_CONV),
       (smtfloat_const "float_min", 2, float_min_CONV),
       (smtfloat_const "float_max", 2, float_max_CONV),
       (smtfloat_const "smt_nearest_integer", 1,
        smt_nearest_integer_CONV),
       (smtfloat_const "float_rem", 2, float_rem_CONV),
       (smtfloat_const "smt_integer_ties_to_away", 1,
        smt_integer_ties_to_away_CONV),
       (smtfloat_const "smt_real_to_int", 2,
        smt_real_to_int_CONV),
       (smtfloat_const "float_to_ubv", 2, float_to_ubv_CONV),
       (smtfloat_const "float_to_sbv", 2, float_to_sbv_CONV),
       (smtfloat_const "smt_float_to_real", 1,
        smt_float_to_real_CONV),
       (smtfloat_const "smt_float_to_fp", 2,
        smt_float_to_fp_CONV),
       (smtfloat_const "smt_real_to_fp", 2,
        smt_real_to_fp_CONV),
       (smtfloat_const "smt_ubv_to_fp", 2,
        smt_ubv_to_fp_CONV),
       (smtfloat_const "smt_sbv_to_fp", 2,
        smt_sbv_to_fp_CONV)]
  in
    foldl (fn (conversion, cmp) => add_conv conversion cmp)
      cs conversions
  end

val () =
  computeLib.put_compset
    (add_smtfloat_to_compset (computeLib.the_compset()))

end
