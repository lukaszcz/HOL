(* Copyright (c) 2026 The HOL4 contributors. *)

(* The SMT-LIB significand width includes the hidden bit.  Thus the HOL
   instance corresponding to (_ FloatingPoint eb sb) is ('t,'w) float with
   dimindex(:'t) = sb - 1 and dimindex(:'w) = eb.  In particular, Float32
   is (23,8) float.  The definitions in this theory remain schematic in
   both widths.

   Canonicalization audit for the core surface (P5.5): every FP-valued
   definition post-composes [canon].  This applies to smtfp_intro,
   smtfp_bits, nan/pinf/ninf/pzero/nzero, abs/neg, add/sub/mul/div/sqrt/fma,
   round_to_integral, min/max, rem, and every to_fp-family operation.  The
   classification predicates (nan, signalling, infinite, normal, subnormal,
   zero, finite, integral, negative, positive), comparisons
   (lt/le/gt/ge/eq/unordered), and BV/real-valued conversions inspect
   smtfp_rep directly, so canonicalization is not applicable.  The internal
   IEEE packing helper is not part of the SMT-LIB surface. *)
Theory smtfloat
Ancestors[qualified]
  binary_ieee
  binary_ieeeProps
  integer_word

Datatype:
  smt_rounding = RNE | RNA | RTP | RTN | RTZ
End

(* SMT-LIB has one NaN value, whereas binary_ieee records carry a sign and
   payload.  The concrete quiet NaN below is the unique NaN representation
   admitted by smtfp.  Rotating 1 right puts its only set bit at the MSB. *)
Definition float_canon_qnan_def:
  float_canon_qnan : ('t,'w) float =
    <| Sign := 0w;
       Exponent := UINT_MAXw;
       Significand := 1w #>> 1 |>
End

Theorem canon_qnan_msb[local]:
  (1w #>> 1 <> 0w : 'a word) /\ word_msb (1w : 'a word #>> 1)
Proof
  simp_tac (srw_ss() ++ wordsLib.WORD_BIT_EQ_ss) [] \\
  conj_tac
  >| [qexists_tac `dimindex(:'a) - 1`, all_tac] \\
  simp [DECIDE ``0n < n ==> (n - 1 + 1 = n)``,
        wordsTheory.word_index]
QED

Theorem float_canon_qnan_is_nan[simp]:
  float_is_nan (float_canon_qnan : ('t,'w) float)
Proof
  simp [float_canon_qnan_def, binary_ieeeTheory.float_is_nan_def,
        binary_ieeeTheory.float_value_def, canon_qnan_msb]
QED

Definition smtfp_canonical_def:
  smtfp_canonical (x : ('t,'w) float) <=>
    ~float_is_nan x \/ x = float_canon_qnan
End

Theorem SMTFP_EXISTS[local]:
  ?x : ('t,'w) float. smtfp_canonical x
Proof
  qexists_tac `float_plus_zero (:'t # 'w)` >>
  simp [smtfp_canonical_def]
QED

val smtfp_tyax = new_type_definition ("smtfp", SMTFP_EXISTS)

val smtfp_bij = define_new_type_bijections {
  name = "smtfp_BIJ",
  ABS = "SmtFp",
  REP = "smtfp_rep",
  tyax = smtfp_tyax}

Theorem SmtFp_smtfp_rep[simp] = CONJUNCT1 smtfp_bij

Theorem smtfp_rep_SmtFp = BETA_RULE (CONJUNCT2 smtfp_bij)

Theorem smtfp_rep_def[simp]:
  !r. smtfp_canonical r ==> (smtfp_rep (SmtFp r) = r)
Proof
  simp [smtfp_rep_SmtFp]
QED

Theorem smtfp_rep_canonical[simp]:
  smtfp_canonical (smtfp_rep x)
Proof
  simp [smtfp_rep_SmtFp]
QED

Theorem smtfp_rep_11[simp]:
  (smtfp_rep x = smtfp_rep y) <=> (x = y)
Proof
  metis_tac [SmtFp_smtfp_rep]
QED

Theorem smtfp_rep_surjective:
  smtfp_canonical r <=> ?x : ('t,'w) smtfp. smtfp_rep x = r
Proof
  metis_tac [smtfp_rep_SmtFp, smtfp_rep_canonical]
QED

(* Invalid raw representatives have no smtfp image.  Ground evaluation must
   expose that error, rather than let the type-definition choice leak. *)
Theorem smtfp_rep_compute[compute]:
  !r. smtfp_rep (SmtFp r) =
      if smtfp_canonical r then r
      else FAIL smtfp_rep ^(mk_var ("non-canonical NaN", bool))
        (SmtFp r)
Proof
  rw [combinTheory.FAIL_THM, smtfp_rep_SmtFp]
QED

Definition canon_def:
  canon (x : ('t,'w) float) =
    if float_is_nan x then float_canon_qnan else x
End

Theorem canon_canonical[simp]:
  smtfp_canonical (canon x)
Proof
  rw [canon_def, smtfp_canonical_def]
QED

Theorem canon_idem[simp]:
  canon (canon x) = canon x
Proof
  Cases_on `float_is_nan x` >> simp [canon_def]
QED

Definition smtfp_intro_def:
  smtfp_intro (x : ('t,'w) float) = SmtFp (canon x)
End

Theorem smtfp_rep_intro[simp]:
  smtfp_rep (smtfp_intro x) = canon x
Proof
  simp [smtfp_intro_def, smtfp_rep_SmtFp]
QED

Theorem canon_smtfp_rep[simp]:
  canon (smtfp_rep x) = smtfp_rep x
Proof
  rw [canon_def] >>
  metis_tac [smtfp_rep_canonical, smtfp_canonical_def]
QED

Definition to_binary_rounding_def:
  to_binary_rounding mode =
    case mode of
      RNE => SOME roundTiesToEven
    | RNA => NONE
    | RTP => SOME roundTowardPositive
    | RTN => SOME roundTowardNegative
    | RTZ => SOME roundTowardZero
End

(* Among equally close finite values, this predicate selects the value on
   the side away from zero.  The threshold branches are the same as RNE's;
   equality at the overflow threshold is itself a tie and therefore rounds
   to the appropriately signed infinity. *)
Definition round_tiesToAway_def[nocompute]:
  round_tiesToAway (x : real) : ('t,'w) float =
    let t = threshold (:'t # 'w) in
      if x <= -t then
        float_minus_infinity (:'t # 'w)
      else if x >= t then
        float_plus_infinity (:'t # 'w)
      else
        closest_such
          (\a. abs x <= abs (float_to_real a)) float_is_finite x
End

(* An integral result can be an infinity in a small format: the nearest
   integral encodings around the top finite value can be that finite value
   and infinity.  Infinity therefore participates in the closest-choice
   set.  On an infinity record, float_to_real gives exactly the adjacent
   endpoint used by binary_ieee's threshold construction. *)
Definition integral_round_candidate_def[nocompute]:
  integral_round_candidate (a : ('t,'w) float) <=>
    float_is_integral a \/ float_is_infinite a
End

(* RNA for fp.roundToIntegral uses the same choice recipe, with all encoded
   integral results, including the two infinities, as candidates. *)
Definition integral_round_tiesToAway_def[nocompute]:
  integral_round_tiesToAway (x : real) : ('t,'w) float =
    let t = threshold (:'t # 'w) in
      if x <= -t then
        float_minus_infinity (:'t # 'w)
      else if x >= t then
        float_plus_infinity (:'t # 'w)
      else
        closest_such
          (\a. abs x <= abs (float_to_real a))
          integral_round_candidate x
End

Definition smt_round_def[nocompute]:
  smt_round mode (x : real) : ('t,'w) float =
    case mode of
      RNE => round roundTiesToEven x
    | RNA => round_tiesToAway x
    | RTP => round roundTowardPositive x
    | RTN => round roundTowardNegative x
    | RTZ => round roundTowardZero x
End

(* Like binary_ieee.integral_round, this rounds a real value.  Signed-zero
   preservation belongs to the later float-facing fp.roundToIntegral
   operation, because HOL reals do not distinguish the two zero signs. *)
Definition smt_integral_round_def[nocompute]:
  smt_integral_round mode (x : real) : ('t,'w) float =
    case mode of
      RNE => integral_round roundTiesToEven x
    | RNA => integral_round_tiesToAway x
    | RTP => integral_round roundTowardPositive x
    | RTN => integral_round roundTowardNegative x
    | RTZ => integral_round roundTowardZero x
End

(* The datatype package also exports smt_rounding_distinct,
   smt_rounding_nchotomy, smt_rounding_induction and the case combinator
   theorems.  These two convenient forms are intended for clients. *)
Theorem smt_rounding_cases:
  !mode. (mode = RNE) \/ (mode = RNA) \/ (mode = RTP) \/
         (mode = RTN) \/ (mode = RTZ)
Proof
  Cases >> simp []
QED

Theorem smt_rounding_distinctness:
  RNE <> RNA /\ RNE <> RTP /\ RNE <> RTN /\ RNE <> RTZ /\
  RNA <> RTP /\ RNA <> RTN /\ RNA <> RTZ /\
  RTP <> RTN /\ RTP <> RTZ /\ RTN <> RTZ
Proof
  simp []
QED

Theorem smt_round_shared:
  to_binary_rounding mode = SOME binary_mode ==>
  (smt_round mode x : ('t,'w) float) = round binary_mode x
Proof
  Cases_on `mode` >> simp [to_binary_rounding_def, smt_round_def]
QED

Theorem smt_integral_round_shared:
  to_binary_rounding mode = SOME binary_mode ==>
  (smt_integral_round mode x : ('t,'w) float) =
    integral_round binary_mode x
Proof
  Cases_on `mode` >> simp [to_binary_rounding_def, smt_integral_round_def]
QED

Theorem finite_floats_nonempty:
  (float_is_finite : ('t,'w) float -> bool) <> {}
Proof
  simp [pred_setTheory.EXTENSION, IN_DEF] >>
  irule_at Any (cj 1 binary_ieeeTheory.zeroes_are_finite_floats)
QED

Theorem integral_round_candidates_nonempty:
  (integral_round_candidate : ('t,'w) float -> bool) <> {}
Proof
  simp [pred_setTheory.EXTENSION, IN_DEF] >>
  qexists_tac `float_plus_zero (:'t # 'w)` >>
  simp [integral_round_candidate_def]
QED

Theorem integral_round_candidate_infinities[simp]:
  integral_round_candidate (float_plus_infinity (:'t # 'w)) /\
  integral_round_candidate (float_minus_infinity (:'t # 'w))
Proof
  simp [integral_round_candidate_def]
QED

Theorem closest_such_properties:
  s <> {} ==>
  is_closest s x (closest_such p s x) /\
  ((?b. is_closest s x b /\ p b) ==> p (closest_such p s x))
Proof
  rw [binary_ieeeTheory.closest_such_def] >>
  SELECT_ELIM_TAC >>
  metis_tac [binary_ieeeTheory.is_closest_exists]
QED

Theorem closest_such_finite_properties:
  is_closest float_is_finite x
    (closest_such p float_is_finite x : ('t,'w) float) /\
  ((?b : ('t,'w) float. is_closest float_is_finite x b /\ p b) ==>
   p (closest_such p float_is_finite x : ('t,'w) float))
Proof
  metis_tac [closest_such_properties, finite_floats_nonempty]
QED

Theorem closest_such_integral_properties:
  is_closest integral_round_candidate x
    (closest_such p integral_round_candidate x : ('t,'w) float) /\
  ((?b : ('t,'w) float.
      is_closest integral_round_candidate x b /\ p b) ==>
   p (closest_such p integral_round_candidate x : ('t,'w) float))
Proof
  metis_tac
    [closest_such_properties, integral_round_candidates_nonempty]
QED

Theorem round_tiesToAway_is_closest:
  -threshold (:'t # 'w) < x /\ x < threshold (:'t # 'w) ==>
  is_closest float_is_finite x
    (round_tiesToAway x : ('t,'w) float)
Proof
  strip_tac >>
  `~(x <= -threshold (:'t # 'w)) /\
   ~(x >= threshold (:'t # 'w))` by realLib.REAL_ASM_ARITH_TAC >>
  simp [round_tiesToAway_def] >>
  irule (cj 1 closest_such_finite_properties)
QED

Theorem integral_round_tiesToAway_is_closest:
  -threshold (:'t # 'w) < x /\ x < threshold (:'t # 'w) ==>
  is_closest integral_round_candidate x
    (integral_round_tiesToAway x : ('t,'w) float)
Proof
  strip_tac >>
  `~(x <= -threshold (:'t # 'w)) /\
   ~(x >= threshold (:'t # 'w))` by realLib.REAL_ASM_ARITH_TAC >>
  simp [integral_round_tiesToAway_def] >>
  irule (cj 1 closest_such_integral_properties)
QED

(* In an in-range tie, if an away-side closest value exists, RNA selects an
   away-side value. *)
Theorem round_tiesToAway_away:
  -threshold (:'t # 'w) < x /\ x < threshold (:'t # 'w) /\
  is_closest float_is_finite x (away : ('t,'w) float) /\
  abs x <= abs (float_to_real away) ==>
  abs x <= abs (float_to_real (round_tiesToAway x : ('t,'w) float))
Proof
  strip_tac >>
  `~(x <= -threshold (:'t # 'w)) /\
   ~(x >= threshold (:'t # 'w))` by realLib.REAL_ASM_ARITH_TAC >>
  simp [round_tiesToAway_def] >>
  irule (BETA_RULE (cj 2
    (Q.INST [`p` |-> `\a : ('t,'w) float.
                         abs x <= abs (float_to_real a)`]
       closest_such_finite_properties))) >>
  qexists_tac `away` >>
  simp []
QED

Theorem integral_round_tiesToAway_away:
  -threshold (:'t # 'w) < x /\ x < threshold (:'t # 'w) /\
  is_closest integral_round_candidate x (away : ('t,'w) float) /\
  abs x <= abs (float_to_real away) ==>
  abs x <=
    abs (float_to_real (integral_round_tiesToAway x : ('t,'w) float))
Proof
  strip_tac >>
  `~(x <= -threshold (:'t # 'w)) /\
   ~(x >= threshold (:'t # 'w))` by realLib.REAL_ASM_ARITH_TAC >>
  simp [integral_round_tiesToAway_def] >>
  irule (BETA_RULE (cj 2
    (Q.INST [`p` |-> `\a : ('t,'w) float.
                         abs x <= abs (float_to_real a)`]
       closest_such_integral_properties))) >>
  qexists_tac `away` >>
  simp []
QED

(* Away and even agree whenever the closest finite representation is
   unique, i.e. away from ties (with the two signed zero records counted
   separately). *)
Theorem round_tiesToAway_eq_RNE_when_closest_unique:
  -threshold (:'t # 'w) < x /\ x < threshold (:'t # 'w) /\
  (!a b : ('t,'w) float.
     is_closest float_is_finite x a /\
     is_closest float_is_finite x b ==> a = b) ==>
  (round_tiesToAway x : ('t,'w) float) = round roundTiesToEven x
Proof
  strip_tac >>
  `~(x <= -threshold (:'t # 'w)) /\
   ~(x >= threshold (:'t # 'w))` by realLib.REAL_ASM_ARITH_TAC >>
  simp [round_tiesToAway_def, binary_ieeeTheory.round_def] >>
  qpat_x_assum `!a b. _` irule >>
  conj_tac >>
  irule (cj 1 closest_such_finite_properties)
QED

(* If the away-side closest representation is unique, this gives the exact
   representative selected at a tie. *)
Theorem round_tiesToAway_tie_away:
  -threshold (:'t # 'w) < x /\ x < threshold (:'t # 'w) /\
  is_closest float_is_finite x (away : ('t,'w) float) /\
  abs x <= abs (float_to_real away) /\
  (!a : ('t,'w) float.
     is_closest float_is_finite x a /\
     abs x <= abs (float_to_real a) ==> a = away) ==>
  (round_tiesToAway x : ('t,'w) float) = away
Proof
  strip_tac >>
  qpat_x_assum `!a. _` irule >>
  conj_tac
  >- (irule round_tiesToAway_away >> simp [] >>
      qexists_tac `away` >> simp [])
  >- (irule round_tiesToAway_is_closest >> simp [])
QED

(* A representative interior midpoint has one closest value on the away
   side and every other closest value strictly on the inward side.  These
   theorems discharge the choice predicate and identify the result. *)
Theorem round_tiesToAway_midpoint:
  -threshold (:'t # 'w) < x /\ x < threshold (:'t # 'w) /\
  is_closest float_is_finite x (away : ('t,'w) float) /\
  abs x <= abs (float_to_real away) /\
  (!a : ('t,'w) float.
     is_closest float_is_finite x a /\ a <> away ==>
     abs (float_to_real a) < abs x) ==>
  (round_tiesToAway x : ('t,'w) float) = away
Proof
  strip_tac >>
  irule round_tiesToAway_tie_away >>
  simp [] >>
  rpt strip_tac >>
  Cases_on `a = away` >> simp [] >>
  qpat_x_assum `!a. _` (qspec_then `a` mp_tac) >>
  realLib.REAL_ASM_ARITH_TAC
QED

Theorem integral_round_tiesToAway_eq_RNE_when_closest_unique:
  -threshold (:'t # 'w) < x /\ x < threshold (:'t # 'w) /\
  is_closest integral_round_candidate x
    (integral_round roundTiesToEven x : ('t,'w) float) /\
  (!a b : ('t,'w) float.
     is_closest integral_round_candidate x a /\
     is_closest integral_round_candidate x b ==> a = b) ==>
  (integral_round_tiesToAway x : ('t,'w) float) =
    integral_round roundTiesToEven x
Proof
  strip_tac >>
  qpat_x_assum `!a b. _` irule >>
  simp [integral_round_tiesToAway_is_closest]
QED

Theorem integral_round_tiesToAway_tie_away:
  -threshold (:'t # 'w) < x /\ x < threshold (:'t # 'w) /\
  is_closest integral_round_candidate x (away : ('t,'w) float) /\
  abs x <= abs (float_to_real away) /\
  (!a : ('t,'w) float.
     is_closest integral_round_candidate x a /\
     abs x <= abs (float_to_real a) ==> a = away) ==>
  (integral_round_tiesToAway x : ('t,'w) float) = away
Proof
  strip_tac >>
  qpat_x_assum `!a. _` irule >>
  conj_tac
  >- (irule integral_round_tiesToAway_away >> simp [] >>
      qexists_tac `away` >> simp [])
  >- (irule integral_round_tiesToAway_is_closest >> simp [])
QED

Theorem integral_round_tiesToAway_midpoint:
  -threshold (:'t # 'w) < x /\ x < threshold (:'t # 'w) /\
  is_closest integral_round_candidate x (away : ('t,'w) float) /\
  abs x <= abs (float_to_real away) /\
  (!a : ('t,'w) float.
     is_closest integral_round_candidate x a /\ a <> away ==>
     abs (float_to_real a) < abs x) ==>
  (integral_round_tiesToAway x : ('t,'w) float) = away
Proof
  strip_tac >>
  irule integral_round_tiesToAway_tie_away >>
  simp [] >>
  rpt strip_tac >>
  Cases_on `a = away` >> simp [] >>
  qpat_x_assum `!a. _` (qspec_then `a` mp_tac) >>
  realLib.REAL_ASM_ARITH_TAC
QED

(* These include the two exponent-boundary halfway cases: equality with
   threshold rounds to infinity, rather than to the largest finite value. *)
Theorem round_tiesToAway_overflow[simp]:
  ((x <= -threshold (:'t # 'w)) ==>
   ((round_tiesToAway x : ('t,'w) float) =
    float_minus_infinity (:'t # 'w))) /\
  ((threshold (:'t # 'w) <= x) ==>
   ((round_tiesToAway x : ('t,'w) float) =
    float_plus_infinity (:'t # 'w)))
Proof
  conj_tac
  >- simp [round_tiesToAway_def]
  >- (strip_tac >>
      `0 < threshold (:'t # 'w)` by
        simp [binary_ieeeTheory.threshold_is_positive] >>
      `~(x <= -threshold (:'t # 'w))` by
        realLib.REAL_ASM_ARITH_TAC >>
      simp [round_tiesToAway_def, realTheory.real_ge])
QED

Theorem integral_round_tiesToAway_overflow[simp]:
  ((x <= -threshold (:'t # 'w)) ==>
   ((integral_round_tiesToAway x : ('t,'w) float) =
    float_minus_infinity (:'t # 'w))) /\
  ((threshold (:'t # 'w) <= x) ==>
   ((integral_round_tiesToAway x : ('t,'w) float) =
    float_plus_infinity (:'t # 'w)))
Proof
  conj_tac
  >- simp [integral_round_tiesToAway_def]
  >- (strip_tac >>
      `0 < threshold (:'t # 'w)` by
        simp [binary_ieeeTheory.threshold_is_positive] >>
      `~(x <= -threshold (:'t # 'w))` by
        realLib.REAL_ASM_ARITH_TAC >>
      simp [integral_round_tiesToAway_def, realTheory.real_ge])
QED

(* The two overflow midpoints are unconditional representative ties. *)
Theorem round_tiesToAway_at_threshold[simp]:
  ((round_tiesToAway (threshold (:'t # 'w)) : ('t,'w) float) =
   float_plus_infinity (:'t # 'w)) /\
  ((round_tiesToAway (-threshold (:'t # 'w)) : ('t,'w) float) =
   float_minus_infinity (:'t # 'w))
Proof
  simp []
QED

Theorem integral_round_tiesToAway_at_threshold[simp]:
  ((integral_round_tiesToAway (threshold (:'t # 'w)) :
      ('t,'w) float) = float_plus_infinity (:'t # 'w)) /\
  ((integral_round_tiesToAway (-threshold (:'t # 'w)) :
      ('t,'w) float) = float_minus_infinity (:'t # 'w))
Proof
  simp []
QED

(* SMT-LIB FloatingPoint (version 2021-05-12) deliberately leaves the
   result of fp.min/fp.max on opposite-signed zero arguments unspecified:
   either zero is permitted.  Each operation therefore gets one fixed
   per-format choice, rather than an input-dependent ARB or a concrete
   ordering of the two zero encodings.  See
   https://smt-lib.org/theories-FloatingPoint.shtml, fp.min/fp.max. *)
Theorem float_min_zero_choice_exists[local]:
  ?f : ('t # 'w) itself -> ('t,'w) float.
    !index.
      f index = float_plus_zero (:'t # 'w) \/
      f index = float_minus_zero (:'t # 'w)
Proof
  qexists_tac `\index. float_plus_zero (:'t # 'w)` >>
  simp []
QED

val float_min_zero_choice_spec =
  new_specification
    ("float_min_zero_choice_spec", ["float_min_zero_choice"],
     float_min_zero_choice_exists);

Theorem float_max_zero_choice_exists[local]:
  ?f : ('t # 'w) itself -> ('t,'w) float.
    !index.
      f index = float_plus_zero (:'t # 'w) \/
      f index = float_minus_zero (:'t # 'w)
Proof
  qexists_tac `\index. float_minus_zero (:'t # 'w)` >>
  simp []
QED

val float_max_zero_choice_spec =
  new_specification
    ("float_max_zero_choice_spec", ["float_max_zero_choice"],
     float_max_zero_choice_exists);

(* -------------------------------------------------------------------------
   Core SMT floating-point operation surface
   ------------------------------------------------------------------------- *)

Definition smt_float_round_def[nocompute]:
  smt_float_round mode to_neg r : ('t,'w) float =
    let x = smt_round mode r in
      if float_is_zero x then
        if to_neg then float_minus_zero (:'t # 'w)
        else float_plus_zero (:'t # 'w)
      else x
End

(* The four binary_ieee modes delegate to its operations.  Only the RNA
   branch below spells out the corresponding IEEE special-case dispatch. *)
Definition smt_float_add_def[nocompute]:
  smt_float_add mode (x : ('t,'w) float) y =
    case to_binary_rounding mode of
      SOME m => SND (float_add m x y)
    | NONE =>
        case float_value x, float_value y of
          NaN, _ => float_canon_qnan
        | _, NaN => float_canon_qnan
        | Infinity, Infinity =>
            if x.Sign = y.Sign then x else float_canon_qnan
        | Infinity, _ => x
        | _, Infinity => y
        | Float r1, Float r2 =>
            smt_float_round RNA
              (if r1 = 0 /\ r2 = 0 /\ x.Sign = y.Sign then
                 x.Sign = 1w
               else F) (r1 + r2)
End

Definition smt_float_sub_def[nocompute]:
  smt_float_sub mode (x : ('t,'w) float) y =
    case to_binary_rounding mode of
      SOME m => SND (float_sub m x y)
    | NONE =>
        case float_value x, float_value y of
          NaN, _ => float_canon_qnan
        | _, NaN => float_canon_qnan
        | Infinity, Infinity =>
            if x.Sign = y.Sign then float_canon_qnan else x
        | Infinity, _ => x
        | _, Infinity => float_negate y
        | Float r1, Float r2 =>
            smt_float_round RNA
              (if r1 = 0 /\ r2 = 0 /\ x.Sign <> y.Sign then
                 x.Sign = 1w
               else F) (r1 - r2)
End

Definition smt_float_mul_def[nocompute]:
  smt_float_mul mode (x : ('t,'w) float) y =
    case to_binary_rounding mode of
      SOME m => SND (float_mul m x y)
    | NONE =>
        case float_value x, float_value y of
          NaN, _ => float_canon_qnan
        | _, NaN => float_canon_qnan
        | Infinity, Float r =>
            if r = 0 then float_canon_qnan
            else if x.Sign = y.Sign then float_plus_infinity (:'t # 'w)
            else float_minus_infinity (:'t # 'w)
        | Float r, Infinity =>
            if r = 0 then float_canon_qnan
            else if x.Sign = y.Sign then float_plus_infinity (:'t # 'w)
            else float_minus_infinity (:'t # 'w)
        | Infinity, Infinity =>
            if x.Sign = y.Sign then float_plus_infinity (:'t # 'w)
            else float_minus_infinity (:'t # 'w)
        | Float r1, Float r2 =>
            smt_float_round RNA (x.Sign <> y.Sign) (r1 * r2)
End

Definition smt_float_div_def[nocompute]:
  smt_float_div mode (x : ('t,'w) float) y =
    case to_binary_rounding mode of
      SOME m => SND (float_div m x y)
    | NONE =>
        case float_value x, float_value y of
          NaN, _ => float_canon_qnan
        | _, NaN => float_canon_qnan
        | Infinity, Infinity => float_canon_qnan
        | Infinity, _ =>
            if x.Sign = y.Sign then float_plus_infinity (:'t # 'w)
            else float_minus_infinity (:'t # 'w)
        | _, Infinity =>
            if x.Sign = y.Sign then float_plus_zero (:'t # 'w)
            else float_minus_zero (:'t # 'w)
        | Float r1, Float r2 =>
            if r2 = 0 then
              if r1 = 0 then float_canon_qnan
              else if x.Sign = y.Sign then float_plus_infinity (:'t # 'w)
              else float_minus_infinity (:'t # 'w)
            else smt_float_round RNA (x.Sign <> y.Sign) (r1 / r2)
End

Definition smt_float_sqrt_def[nocompute]:
  smt_float_sqrt mode (x : ('t,'w) float) =
    case to_binary_rounding mode of
      SOME m => SND (float_sqrt m x)
    | NONE =>
        if x.Sign = 0w then
          case float_value x of
            NaN => float_canon_qnan
          | Infinity => float_plus_infinity (:'t # 'w)
          | Float r => smt_float_round RNA F (sqrt r)
        else if x = float_minus_zero (:'t # 'w) then x
        else float_canon_qnan
End

Definition smt_float_fma_def[nocompute]:
  smt_float_fma mode (x : ('t,'w) float) y z =
    case to_binary_rounding mode of
      SOME m => SND (float_mul_add m x y z)
    | NONE =>
        let sign_p = word_xor x.Sign y.Sign in
        let inf_p = (float_is_infinite x \/ float_is_infinite y) in
          if float_is_nan x \/ float_is_nan y \/ float_is_nan z then
            float_canon_qnan
          else if
            float_is_infinite x /\ float_is_zero y \/
            float_is_zero x /\ float_is_infinite y \/
            float_is_infinite z /\ inf_p /\ sign_p <> z.Sign
          then float_canon_qnan
          else if
            float_is_infinite z /\ z.Sign = 0w \/ inf_p /\ sign_p = 0w
          then float_plus_infinity (:'t # 'w)
          else if
            float_is_infinite z /\ z.Sign = 1w \/ inf_p /\ sign_p = 1w
          then float_minus_infinity (:'t # 'w)
          else
            let r1 = float_to_real x * float_to_real y in
            let r2 = float_to_real z in
            let r = r1 + r2 in
              smt_float_round RNA
                (r = 0 /\
                 (if r1 = 0 /\ r2 = 0 /\ sign_p = z.Sign then
                    sign_p = 1w
                  else F) \/ r < 0) r
End

Definition smt_float_round_to_integral_def[nocompute]:
  smt_float_round_to_integral mode (x : ('t,'w) float) =
    case to_binary_rounding mode of
      SOME m => float_round_to_integral m x
    | NONE =>
        case float_value x of
          Float r =>
            let y = smt_integral_round RNA r in
              if float_is_zero y then
                if x.Sign = 1w then float_minus_zero (:'t # 'w)
                else float_plus_zero (:'t # 'w)
              else y
        | _ => x
End

(* This is the official SMT-LIB minNum/maxNum dispatch: one NaN is ignored,
   two NaNs produce a NaN (the second argument here), ordinary arguments are
   ordered numerically, and only the opposite-signed-zero case consults the
   fixed underspecified choices above. *)
Definition float_min_def[nocompute]:
  float_min (x : ('t,'w) float) (y : ('t,'w) float) =
    if float_is_nan x then y
    else if float_is_nan y then x
    else if float_is_zero x /\ float_is_zero y /\ x.Sign <> y.Sign then
      float_min_zero_choice (:'t # 'w)
    else if float_less_than x y then x
    else y
End

Definition float_max_def[nocompute]:
  float_max (x : ('t,'w) float) (y : ('t,'w) float) =
    if float_is_nan x then y
    else if float_is_nan y then x
    else if float_is_zero x /\ float_is_zero y /\ x.Sign <> y.Sign then
      float_max_zero_choice (:'t # 'w)
    else if float_greater_than x y then x
    else y
End

(* The unbounded counterpart of TASK_07's RNE integral rounding.  fp.rem's
   quotient integer is mathematical, not restricted to the operand format:
   rounding it through [('t,'w) float] would overflow for, e.g., max-finite
   divided by min-subnormal.  This is binary_ieee.float_to_int's exact RNE
   floor/ceiling dispatch, including the ties-to-even predicate. *)
Definition smt_nearest_integer_def[nocompute]:
  smt_nearest_integer (r : real) : int =
    let f = INT_FLOOR r in
    let df = abs (r - real_of_int f) in
      if df < 1 / 2 \/
         df = 1 / 2 /\ EVEN (Num (ABS f))
      then f
      else INT_CEILING r
End

(* SMT-LIB FloatingPoint, fp.rem: NaN is returned for a NaN operand, an
   infinite dividend, or a zero divisor; a finite dividend is returned for
   an infinite divisor.  Otherwise r = x - y*n, where n is the nearest
   mathematical integer to x/y with ties to even.  IEEE remainder is exact;
   applying RNE to r returns that representable result.  [smt_float_round]'s
   zero branch preserves the sign of the dividend, as required by the same
   spec passage. *)
Definition float_rem_def[nocompute]:
  float_rem (x : ('t,'w) float) (y : ('t,'w) float) =
    case float_value x, float_value y of
      NaN, _ => float_canon_qnan
    | _, NaN => float_canon_qnan
    | Infinity, _ => float_canon_qnan
    | _, Infinity => x
    | Float r1, Float r2 =>
        if r2 = 0 then float_canon_qnan
        else
          let n = real_of_int (smt_nearest_integer (r1 / r2)) in
            smt_float_round RNE (x.Sign = 1w) (r1 - r2 * n)
End

(* -------------------------------------------------------------------------
   SMT-LIB conversions
   ------------------------------------------------------------------------- *)

(* The integer result before a BV range check.  RNE uses the same exact
   mathematical rule as binary_ieee.float_to_int.  RNA chooses the nearest
   integer and resolves a tie away from zero; the directed modes are the
   corresponding floor/ceiling operations. *)
Definition smt_integer_ties_to_away_def[nocompute]:
  smt_integer_ties_to_away (r : real) : int =
    if r < 0 then
      let c = INT_CEILING r in
        if abs (r - real_of_int c) < 1 / 2 then c else INT_FLOOR r
    else
      let f = INT_FLOOR r in
        if abs (r - real_of_int f) < 1 / 2 then f else INT_CEILING r
End

Definition smt_real_to_int_def[nocompute]:
  smt_real_to_int mode (r : real) : int =
    case mode of
      RNE => smt_nearest_integer r
    | RNA => smt_integer_ties_to_away r
    | RTP => INT_CEILING r
    | RTN => INT_FLOOR r
    | RTZ => if r < 0 then INT_CEILING r else INT_FLOOR r
End

(* SMT-LIB leaves each invalid conversion result unspecified, but it still
   denotes a function.  These constants therefore receive no constraint
   beyond function consistency.  In particular, no concrete default word or
   real is exposed by the specifications. *)
Theorem float_to_ubv_unspecified_exists[local]:
  ?f : smt_rounding -> ('t,'w) float -> 'm word.
    !mode x. f mode x = f mode x
Proof
  qexists_tac `\mode x. 0w` >> simp []
QED

val float_to_ubv_unspecified_spec =
  new_specification
    ("float_to_ubv_unspecified_spec", ["float_to_ubv_unspecified"],
     float_to_ubv_unspecified_exists);

Theorem float_to_sbv_unspecified_exists[local]:
  ?f : smt_rounding -> ('t,'w) float -> 'm word.
    !mode x. f mode x = f mode x
Proof
  qexists_tac `\mode x. 0w` >> simp []
QED

val float_to_sbv_unspecified_spec =
  new_specification
    ("float_to_sbv_unspecified_spec", ["float_to_sbv_unspecified"],
     float_to_sbv_unspecified_exists);

Theorem float_to_real_unspecified_exists[local]:
  ?f : ('t,'w) float -> real. !x. f x = f x
Proof
  qexists_tac `\x. 0` >> simp []
QED

val float_to_real_unspecified_spec =
  new_specification
    ("float_to_real_unspecified_spec", ["float_to_real_unspecified"],
     float_to_real_unspecified_exists);

Definition float_to_ubv_def[nocompute]:
  float_to_ubv mode (x : ('t,'w) float) : 'm word =
    case float_value x of
      Float r =>
        let i = smt_real_to_int mode r in
          if 0 <= i /\ i < &(dimword(:'m)) then n2w (Num i)
          else float_to_ubv_unspecified mode (canon x)
    | _ => float_to_ubv_unspecified mode (canon x)
End

Definition float_to_sbv_def[nocompute]:
  float_to_sbv mode (x : ('t,'w) float) : 'm word =
    case float_value x of
      Float r =>
        let i = smt_real_to_int mode r in
          if integer_word$INT_MIN(:'m) <= i /\
             i <= integer_word$INT_MAX(:'m)
          then i2w i
          else float_to_sbv_unspecified mode (canon x)
    | _ => float_to_sbv_unspecified mode (canon x)
End

Definition smt_float_to_real_def[nocompute]:
  smt_float_to_real (x : ('t,'w) float) =
    case float_value x of
      Float r => r
    | _ => float_to_real_unspecified (canon x)
End

(* Re-encoding a finite value rounds its mathematical value once in the
   destination format.  [smt_float_round] preserves the sign if that result
   is zero.  Infinities preserve their sign and all NaN encodings map to the
   canonical NaN. *)
Definition smt_float_to_fp_def[nocompute]:
  smt_float_to_fp mode (x : ('a,'b) float) : ('t,'w) float =
    case float_value x of
      NaN => float_canon_qnan
    | Infinity =>
        if x.Sign = 1w then float_minus_infinity (:'t # 'w)
        else float_plus_infinity (:'t # 'w)
    | Float r => smt_float_round mode (x.Sign = 1w) r
End

Definition smt_real_to_fp_def[nocompute]:
  smt_real_to_fp mode (r : real) : ('t,'w) float =
    smt_float_round mode (r < 0) r
End

Definition smt_ubv_to_fp_def[nocompute]:
  smt_ubv_to_fp mode (v : 'a word) : ('t,'w) float =
    smt_real_to_fp mode (&(w2n v))
End

Definition smt_sbv_to_fp_def[nocompute]:
  smt_sbv_to_fp mode (v : 'a word) : ('t,'w) float =
    smt_real_to_fp mode (real_of_int (w2i v))
End

(* The one-argument indexed to_fp is a bit-exact IEEE interchange unpack.
   Its argument type enforces the SMT-LIB width eb + sb, namely
   1 + eb + (sb - 1). *)
Definition float_from_ieee_bv_def:
  float_from_ieee_bv
    (v : (1 + ('w + 't)) word) : ('t,'w) float =
    let em : ('w + 't) word =
      (dimindex(:'w) + dimindex(:'t) - 1 >< 0) v in
      <| Sign :=
           (dimindex(:'w) + dimindex(:'t) ><
              dimindex(:'w) + dimindex(:'t)) v;
         Exponent :=
           (dimindex(:'w) + dimindex(:'t) - 1 >< dimindex(:'t)) em;
         Significand := (dimindex(:'t) - 1 >< 0) em |>
End

(* SMT-LIB deliberately has no FP-to-IEEE-BV operation because its unique
   NaN has many IEEE encodings.  This exact packing function is only an
   internal inverse used by the sanity theorems below. *)
Definition float_pack_ieee_bv_def:
  float_pack_ieee_bv (x : ('t,'w) float) : (1 + ('w + 't)) word =
    x.Sign @@ ((x.Exponent @@ x.Significand) : ('w + 't) word)
End

Definition smtfp_bits_def:
  smtfp_bits (s : word1) (e : 'w word) (m : 't word) =
    SmtFp (canon <| Sign := s; Exponent := e; Significand := m |>)
End

Definition smtfp_nan_def:
  smtfp_nan : ('t,'w) smtfp =
    SmtFp (canon (float_canon_qnan : ('t,'w) float))
End

Definition smtfp_pinf_def:
  smtfp_pinf : ('t,'w) smtfp =
    SmtFp (canon (float_plus_infinity (:'t # 'w)))
End

Definition smtfp_ninf_def:
  smtfp_ninf : ('t,'w) smtfp =
    SmtFp (canon (float_minus_infinity (:'t # 'w)))
End

Definition smtfp_pzero_def:
  smtfp_pzero : ('t,'w) smtfp =
    SmtFp (canon (float_plus_zero (:'t # 'w)))
End

Definition smtfp_nzero_def:
  smtfp_nzero : ('t,'w) smtfp =
    SmtFp (canon (float_minus_zero (:'t # 'w)))
End

Definition smtfp_is_nan_def:
  smtfp_is_nan (x : ('t,'w) smtfp) = float_is_nan (smtfp_rep x)
End

Definition smtfp_is_signalling_def:
  smtfp_is_signalling (x : ('t,'w) smtfp) =
    float_is_signalling (smtfp_rep x)
End

Definition smtfp_is_infinite_def:
  smtfp_is_infinite (x : ('t,'w) smtfp) =
    float_is_infinite (smtfp_rep x)
End

Definition smtfp_is_normal_def:
  smtfp_is_normal (x : ('t,'w) smtfp) =
    float_is_normal (smtfp_rep x)
End

Definition smtfp_is_subnormal_def:
  smtfp_is_subnormal (x : ('t,'w) smtfp) =
    float_is_subnormal (smtfp_rep x)
End

Definition smtfp_is_zero_def:
  smtfp_is_zero (x : ('t,'w) smtfp) = float_is_zero (smtfp_rep x)
End

Definition smtfp_is_finite_def:
  smtfp_is_finite (x : ('t,'w) smtfp) =
    float_is_finite (smtfp_rep x)
End

Definition smtfp_is_integral_def:
  smtfp_is_integral (x : ('t,'w) smtfp) =
    float_is_integral (smtfp_rep x)
End

Definition smtfp_is_negative_def:
  smtfp_is_negative (x : ('t,'w) smtfp) <=>
    ~float_is_nan (smtfp_rep x) /\ (smtfp_rep x).Sign = 1w
End

Definition smtfp_is_positive_def:
  smtfp_is_positive (x : ('t,'w) smtfp) <=>
    ~float_is_nan (smtfp_rep x) /\ (smtfp_rep x).Sign = 0w
End

Definition smtfp_abs_def:
  smtfp_abs (x : ('t,'w) smtfp) =
    SmtFp (canon (float_abs (smtfp_rep x)))
End

Definition smtfp_neg_def:
  smtfp_neg (x : ('t,'w) smtfp) =
    SmtFp (canon (float_negate (smtfp_rep x)))
End

Definition smtfp_lt_def:
  smtfp_lt (x : ('t,'w) smtfp) y =
    float_less_than (smtfp_rep x) (smtfp_rep y)
End

Definition smtfp_le_def:
  smtfp_le (x : ('t,'w) smtfp) y =
    float_less_equal (smtfp_rep x) (smtfp_rep y)
End

Definition smtfp_gt_def:
  smtfp_gt (x : ('t,'w) smtfp) y =
    float_greater_than (smtfp_rep x) (smtfp_rep y)
End

Definition smtfp_ge_def:
  smtfp_ge (x : ('t,'w) smtfp) y =
    float_greater_equal (smtfp_rep x) (smtfp_rep y)
End

Definition smtfp_eq_def:
  smtfp_eq (x : ('t,'w) smtfp) y =
    float_equal (smtfp_rep x) (smtfp_rep y)
End

Definition smtfp_unordered_def:
  smtfp_unordered (x : ('t,'w) smtfp) y =
    float_unordered (smtfp_rep x) (smtfp_rep y)
End

Definition smtfp_add_def:
  smtfp_add mode (x : ('t,'w) smtfp) y =
    SmtFp (canon (smt_float_add mode (smtfp_rep x) (smtfp_rep y)))
End

Definition smtfp_sub_def:
  smtfp_sub mode (x : ('t,'w) smtfp) y =
    SmtFp (canon (smt_float_sub mode (smtfp_rep x) (smtfp_rep y)))
End

Definition smtfp_mul_def:
  smtfp_mul mode (x : ('t,'w) smtfp) y =
    SmtFp (canon (smt_float_mul mode (smtfp_rep x) (smtfp_rep y)))
End

Definition smtfp_div_def:
  smtfp_div mode (x : ('t,'w) smtfp) y =
    SmtFp (canon (smt_float_div mode (smtfp_rep x) (smtfp_rep y)))
End

Definition smtfp_sqrt_def:
  smtfp_sqrt mode (x : ('t,'w) smtfp) =
    SmtFp (canon (smt_float_sqrt mode (smtfp_rep x)))
End

Definition smtfp_fma_def:
  smtfp_fma mode (x : ('t,'w) smtfp) y z =
    SmtFp (canon
      (smt_float_fma mode (smtfp_rep x) (smtfp_rep y) (smtfp_rep z)))
End

Definition smtfp_round_to_integral_def:
  smtfp_round_to_integral mode (x : ('t,'w) smtfp) =
    SmtFp (canon (smt_float_round_to_integral mode (smtfp_rep x)))
End

Definition smtfp_min_def:
  smtfp_min (x : ('t,'w) smtfp) (y : ('t,'w) smtfp) =
    SmtFp (canon (float_min (smtfp_rep x) (smtfp_rep y)))
End

Definition smtfp_max_def:
  smtfp_max (x : ('t,'w) smtfp) (y : ('t,'w) smtfp) =
    SmtFp (canon (float_max (smtfp_rep x) (smtfp_rep y)))
End

Definition smtfp_rem_def:
  smtfp_rem (x : ('t,'w) smtfp) (y : ('t,'w) smtfp) =
    SmtFp (canon (float_rem (smtfp_rep x) (smtfp_rep y)))
End

Definition smtfp_to_ubv_def:
  smtfp_to_ubv mode (x : ('t,'w) smtfp) : 'm word =
    float_to_ubv mode (smtfp_rep x)
End

Definition smtfp_to_sbv_def:
  smtfp_to_sbv mode (x : ('t,'w) smtfp) : 'm word =
    float_to_sbv mode (smtfp_rep x)
End

Definition smtfp_to_real_def:
  smtfp_to_real (x : ('t,'w) smtfp) =
    smt_float_to_real (smtfp_rep x)
End

Definition smtfp_to_fp_def:
  smtfp_to_fp mode (x : ('a,'b) smtfp) : ('t,'w) smtfp =
    SmtFp (canon (smt_float_to_fp mode (smtfp_rep x)))
End

Definition smtfp_from_real_def:
  smtfp_from_real mode (r : real) : ('t,'w) smtfp =
    SmtFp (canon (smt_real_to_fp mode r))
End

Definition smtfp_from_ubv_def:
  smtfp_from_ubv mode (v : 'a word) : ('t,'w) smtfp =
    SmtFp (canon (smt_ubv_to_fp mode v))
End

Definition smtfp_from_sbv_def:
  smtfp_from_sbv mode (v : 'a word) : ('t,'w) smtfp =
    SmtFp (canon (smt_sbv_to_fp mode v))
End

Definition smtfp_from_ieee_bv_def:
  smtfp_from_ieee_bv
    (v : (1 + ('w + 't)) word) : ('t,'w) smtfp =
    SmtFp (canon (float_from_ieee_bv v))
End

(* Internal inverse for round-trip checks; this is not an SMT-LIB symbol. *)
Definition smtfp_pack_ieee_bv_def:
  smtfp_pack_ieee_bv
    (x : ('t,'w) smtfp) : (1 + ('w + 't)) word =
    float_pack_ieee_bv (smtfp_rep x)
End

(* Invalid branches expose only the corresponding specified choice.  The
   argument is canonicalized so all raw IEEE NaN payloads represent the one
   SMT-LIB NaN argument and therefore receive a function-consistent result. *)
Theorem float_to_ubv_special:
  float_value x = NaN \/ float_value x = Infinity ==>
  (float_to_ubv mode x : 'm word) =
    float_to_ubv_unspecified mode (canon x)
Proof
  strip_tac >> fs [float_to_ubv_def]
QED

Theorem float_to_sbv_special:
  float_value x = NaN \/ float_value x = Infinity ==>
  (float_to_sbv mode x : 'm word) =
    float_to_sbv_unspecified mode (canon x)
Proof
  strip_tac >> fs [float_to_sbv_def]
QED

Theorem smt_float_to_real_special:
  float_value x = NaN \/ float_value x = Infinity ==>
  smt_float_to_real x = float_to_real_unspecified (canon x)
Proof
  strip_tac >> fs [smt_float_to_real_def]
QED

Theorem float_to_ubv_valid:
  float_value x = Float r /\
  (let i = smt_real_to_int mode r in
     0 <= i /\ i < &(dimword(:'m))) ==>
  (float_to_ubv mode x : 'm word) =
    n2w (Num (smt_real_to_int mode r))
Proof
  strip_tac >> fs [float_to_ubv_def]
QED

Theorem float_to_sbv_valid:
  float_value x = Float r /\
  (let i = smt_real_to_int mode r in
     integer_word$INT_MIN(:'m) <= i /\
     i <= integer_word$INT_MAX(:'m)) ==>
  (float_to_sbv mode x : 'm word) =
    i2w (smt_real_to_int mode r)
Proof
  strip_tac >> fs [float_to_sbv_def]
QED

Theorem smt_float_to_real_valid:
  float_value x = Float r ==> smt_float_to_real x = r
Proof
  simp [smt_float_to_real_def]
QED

Theorem float_to_ubv_out_of_range:
  float_value x = Float r /\
  (let i = smt_real_to_int mode r in
     ~(0 <= i /\ i < &(dimword(:'m)))) ==>
  (float_to_ubv mode x : 'm word) =
    float_to_ubv_unspecified mode (canon x)
Proof
  strip_tac >> fs [float_to_ubv_def]
QED

Theorem float_to_sbv_out_of_range:
  float_value x = Float r /\
  (let i = smt_real_to_int mode r in
     ~(integer_word$INT_MIN(:'m) <= i /\
       i <= integer_word$INT_MAX(:'m))) ==>
  (float_to_sbv mode x : 'm word) =
    float_to_sbv_unspecified mode (canon x)
Proof
  strip_tac >> fs [float_to_sbv_def]
QED

Theorem smtfp_to_ubv_valid:
  float_value (smtfp_rep x) = Float r /\
  (let i = smt_real_to_int mode r in
     0 <= i /\ i < &(dimword(:'m))) ==>
  (smtfp_to_ubv mode x : 'm word) =
    n2w (Num (smt_real_to_int mode r))
Proof
  simp [smtfp_to_ubv_def, float_to_ubv_valid]
QED

Theorem smtfp_to_sbv_valid:
  float_value (smtfp_rep x) = Float r /\
  (let i = smt_real_to_int mode r in
     integer_word$INT_MIN(:'m) <= i /\
     i <= integer_word$INT_MAX(:'m)) ==>
  (smtfp_to_sbv mode x : 'm word) =
    i2w (smt_real_to_int mode r)
Proof
  simp [smtfp_to_sbv_def, float_to_sbv_valid]
QED

Theorem smtfp_to_real_valid:
  float_value (smtfp_rep x) = Float r ==> smtfp_to_real x = r
Proof
  simp [smtfp_to_real_def, smt_float_to_real_valid]
QED

(* The subtype lifts have no quotient respectfulness obligations.  These
   representative equations are their boundary interface and, for every
   FP-valued conversion, make the required post-composition with canon
   explicit. *)
Theorem smtfp_conversion_reps[simp]:
  smtfp_rep (smtfp_to_fp mode x : ('t,'w) smtfp) =
    canon (smt_float_to_fp mode (smtfp_rep x)) /\
  smtfp_rep (smtfp_from_real mode r : ('t,'w) smtfp) =
    canon (smt_real_to_fp mode r) /\
  smtfp_rep (smtfp_from_ubv mode u : ('t,'w) smtfp) =
    canon (smt_ubv_to_fp mode u) /\
  smtfp_rep (smtfp_from_sbv mode s : ('t,'w) smtfp) =
    canon (smt_sbv_to_fp mode s) /\
  smtfp_rep (smtfp_from_ieee_bv b : ('t,'w) smtfp) =
    canon (float_from_ieee_bv b)
Proof
  simp [smtfp_to_fp_def, smtfp_from_real_def, smtfp_from_ubv_def,
        smtfp_from_sbv_def, smtfp_from_ieee_bv_def, smtfp_rep_def]
QED

(* For finite index types the packing utility is a two-sided inverse at the
   raw-float level.  The smtfp unpack-pack direction remains valid after NaN
   canonicalization; pack-unpack intentionally need not preserve a
   noncanonical IEEE NaN bit pattern. *)
Theorem float_ieee_bv_unpack_pack:
  FINITE (UNIV : 'w -> bool) /\ FINITE (UNIV : 't -> bool) ==>
  !x : ('t,'w) float.
    float_from_ieee_bv (float_pack_ieee_bv x) = x
Proof
  strip_tac >> gen_tac >> fs [] >>
  rw [float_from_ieee_bv_def, float_pack_ieee_bv_def,
      binary_ieeeTheory.float_component_equality] >>
  asm_simp_tac (srw_ss() ++ wordsLib.WORD_BIT_EQ_ss)
    [wordsTheory.word_index, fcpTheory.finite_sum,
     fcpTheory.index_sum]
QED

Theorem float_ieee_bv_pack_unpack:
  FINITE (UNIV : 't -> bool) /\ FINITE (UNIV : 'w -> bool) ==>
  !v : (1 + ('w + 't)) word.
    float_pack_ieee_bv (float_from_ieee_bv v : ('t,'w) float) = v
Proof
  strip_tac >> gen_tac >> fs [] >>
  rw [float_from_ieee_bv_def, float_pack_ieee_bv_def] >>
  asm_simp_tac (srw_ss() ++ wordsLib.WORD_BIT_EQ_ss)
    [wordsTheory.word_index, fcpTheory.finite_sum,
     fcpTheory.index_sum] >>
  rpt strip_tac >>
  Cases_on `dimindex(:'t) + dimindex(:'w) <= i` >>
  Cases_on `dimindex(:'t) <= i` >>
  asm_simp_tac (srw_ss() ++ wordsLib.WORD_BIT_EQ_ss)
    [wordsTheory.word_index, fcpTheory.finite_sum,
     fcpTheory.index_sum]
QED

Theorem smtfp_ieee_bv_unpack_pack:
  FINITE (UNIV : 'w -> bool) /\ FINITE (UNIV : 't -> bool) ==>
  !x : ('t,'w) smtfp.
    smtfp_from_ieee_bv (smtfp_pack_ieee_bv x) = x
Proof
  strip_tac >> gen_tac >>
  simp [smtfp_from_ieee_bv_def, smtfp_pack_ieee_bv_def,
        float_ieee_bv_unpack_pack]
QED

Theorem float_ieee_bv_roundtrip_float32[simp]:
  !x : (23,8) float.
    float_from_ieee_bv (float_pack_ieee_bv x) = x
Proof
  simp [float_ieee_bv_unpack_pack]
QED

Theorem smtfp_ieee_bv_roundtrip_float32[simp]:
  !x : (23,8) smtfp.
    smtfp_from_ieee_bv (smtfp_pack_ieee_bv x) = x
Proof
  simp [smtfp_ieee_bv_unpack_pack]
QED

Theorem smt_real_to_fp_shared_representable:
  2 <= dimindex(:'w) /\ float_is_finite (x : ('t,'w) float) /\
  ~float_is_zero x /\ to_binary_rounding mode = SOME binary_mode ==>
  smt_real_to_fp mode (float_to_real x) = x
Proof
  strip_tac >>
  `round binary_mode (float_to_real x) = x` by
    (irule binary_ieeePropsTheory.round_representable_nonzero >>
     fs [binary_ieeeTheory.float_is_zero_to_real]) >>
  `smt_round mode (float_to_real x) = x` by
    (imp_res_tac smt_round_shared >> fs []) >>
  simp [smt_real_to_fp_def, smt_float_round_def]
QED

Theorem smt_float_to_fp_shared_roundtrip:
  2 <= dimindex(:'w) /\ float_is_finite (x : ('t,'w) float) /\
  ~float_is_zero x /\ to_binary_rounding mode = SOME binary_mode ==>
  smt_float_to_fp mode x = x
Proof
  strip_tac >>
  `float_value x = Float (float_to_real x)` by
    simp [binary_ieeePropsTheory.float_value_eq_float_to_real] >>
  `round binary_mode (float_to_real x) = x` by
    (irule binary_ieeePropsTheory.round_representable_nonzero >>
     fs [binary_ieeeTheory.float_is_zero_to_real]) >>
  `smt_round mode (float_to_real x) = x` by
    (imp_res_tac smt_round_shared >> fs []) >>
  simp [smt_float_to_fp_def, smt_float_round_def]
QED

Theorem smt_float_to_fp_infinities[simp]:
  smt_float_to_fp mode (float_plus_infinity (:'a # 'b)) =
    (float_plus_infinity (:'t # 'w) : ('t,'w) float) /\
  smt_float_to_fp mode (float_minus_infinity (:'a # 'b)) =
    (float_minus_infinity (:'t # 'w) : ('t,'w) float)
Proof
  simp [smt_float_to_fp_def]
QED

Theorem smt_float_to_fp_nan[simp]:
  smt_float_to_fp mode (float_canon_qnan : ('a,'b) float) =
    (float_canon_qnan : ('t,'w) float)
Proof
  simp [smt_float_to_fp_def, float_canon_qnan_def,
        binary_ieeeTheory.float_value_def, canon_qnan_msb]
QED

Theorem smt_float_to_fp_shared_zero[simp]:
  2 <= dimindex(:'w) /\ to_binary_rounding mode = SOME binary_mode ==>
  smt_float_to_fp mode (float_plus_zero (:'a # 'b)) =
    (float_plus_zero (:'t # 'w) : ('t,'w) float) /\
  smt_float_to_fp mode (float_minus_zero (:'a # 'b)) =
    (float_minus_zero (:'t # 'w) : ('t,'w) float)
Proof
  strip_tac >>
  `smt_round mode 0 = (float_plus_zero (:'t # 'w) : ('t,'w) float) \/
   smt_round mode 0 = float_minus_zero (:'t # 'w)` by
    (imp_res_tac smt_round_shared >>
     metis_tac [binary_ieeePropsTheory.round_representable_zero]) >>
  simp [smt_float_to_fp_def, smt_float_round_def] >>
  fs []
QED

Theorem smt_real_to_fp_shared_zero[simp]:
  2 <= dimindex(:'w) /\ to_binary_rounding mode = SOME binary_mode ==>
  (smt_real_to_fp mode 0 : ('t,'w) float) =
    float_plus_zero (:'t # 'w)
Proof
  strip_tac >>
  `smt_round mode 0 = (float_plus_zero (:'t # 'w) : ('t,'w) float) \/
   smt_round mode 0 = float_minus_zero (:'t # 'w)` by
    (imp_res_tac smt_round_shared >>
     metis_tac [binary_ieeePropsTheory.round_representable_zero]) >>
  simp [smt_real_to_fp_def, smt_float_round_def] >>
  fs []
QED

Theorem float32_ieee_one_ground[simp]:
  float_from_ieee_bv
    (0x3F800000w : (1 + (8 + 23)) word) =
      (<| Sign := 0w; Exponent := 127w; Significand := 0w |> :
       (23,8) float) /\
  float_pack_ieee_bv
    (<| Sign := 0w; Exponent := 127w; Significand := 0w |> :
     (23,8) float) =
      (0x3F800000w : (1 + (8 + 23)) word)
Proof
  rw [float_from_ieee_bv_def, float_pack_ieee_bv_def,
      binary_ieeeTheory.float_component_equality] >>
  simp_tac (srw_ss() ++ wordsLib.WORD_EXTRACT_ss) []
QED

Theorem float32_one_conversion_ground[simp]:
  let one =
    (<| Sign := 0w; Exponent := 127w; Significand := 0w |> :
     (23,8) float)
  in
    (float_to_ubv RTZ one : word8) = 1w /\
    (float_to_sbv RTN one : word8) = 1w /\
    smt_float_to_real one = 1
Proof
  simp [float_to_ubv_def, float_to_sbv_def,
        smt_float_to_real_def, smt_real_to_int_def,
        binary_ieeeTheory.float_value_def,
        binary_ieeeTheory.float_to_real_def,
        wordsTheory.INT_MAX_def, wordsTheory.dimword_def,
        intrealTheory.INT_FLOOR, integer_wordTheory.i2w_pos]
QED

Theorem float32_one_to_fp_ground[simp]:
  let one =
    (<| Sign := 0w; Exponent := 127w; Significand := 0w |> :
     (23,8) float)
  in
    smt_real_to_fp RNE 1 = one /\
    smt_ubv_to_fp RNE (1w : word8) = one /\
    smt_sbv_to_fp RNE (1w : word8) = one /\
    smt_float_to_fp RNE one = one
Proof
  simp [smt_ubv_to_fp_def, smt_sbv_to_fp_def,
        integer_wordTheory.w2i_def] >>
  rpt conj_tac
  >- (`1 = float_to_real
        (<| Sign := 0w; Exponent := 127w; Significand := 0w |> :
         (23,8) float)` by
        simp [binary_ieeeTheory.float_to_real_def] >>
      pop_assum (once_rewrite_tac o single) >>
      irule smt_real_to_fp_shared_representable >>
      simp [to_binary_rounding_def,
            binary_ieeeTheory.float_is_finite_def,
            binary_ieeeTheory.float_is_zero_def,
            binary_ieeeTheory.float_value_def,
            binary_ieeeTheory.float_to_real_def])
  >- (`1 = float_to_real
        (<| Sign := 0w; Exponent := 127w; Significand := 0w |> :
         (23,8) float)` by
        simp [binary_ieeeTheory.float_to_real_def] >>
      pop_assum (once_rewrite_tac o single) >>
      irule smt_real_to_fp_shared_representable >>
      simp [to_binary_rounding_def,
            binary_ieeeTheory.float_is_finite_def,
            binary_ieeeTheory.float_is_zero_def,
            binary_ieeeTheory.float_value_def,
            binary_ieeeTheory.float_to_real_def])
  >- (`1 = float_to_real
        (<| Sign := 0w; Exponent := 127w; Significand := 0w |> :
         (23,8) float)` by
        simp [binary_ieeeTheory.float_to_real_def] >>
      pop_assum (once_rewrite_tac o single) >>
      irule smt_real_to_fp_shared_representable >>
      simp [to_binary_rounding_def,
            binary_ieeeTheory.float_is_finite_def,
            binary_ieeeTheory.float_is_zero_def,
            binary_ieeeTheory.float_value_def,
            binary_ieeeTheory.float_to_real_def])
  >- (irule smt_float_to_fp_shared_roundtrip >>
      simp [to_binary_rounding_def,
            binary_ieeeTheory.float_is_finite_def,
            binary_ieeeTheory.float_is_zero_def,
            binary_ieeeTheory.float_value_def,
            binary_ieeeTheory.float_to_real_def])
QED

Theorem smt_integer_ties_to_away_basic[simp]:
  smt_integer_ties_to_away 0 = 0 /\
  smt_integer_ties_to_away (5 / 2) = 3 /\
  smt_integer_ties_to_away (-5 / 2) = -3
Proof
  rw [smt_integer_ties_to_away_def, intrealTheory.INT_FLOOR,
      intrealTheory.INT_CEILING] >>
  realLib.REAL_ARITH_TAC
QED

(* The concrete RNA tie cases and Float32 interchange round-trips above are
   definitional ground instances.  TASK_12 adds the general evaluator. *)

(* One proof covers the canonicalization obligation of every result-valued
   operation above: a NaN result is always the sole SMT-LIB NaN value. *)
Theorem smtfp_op_nan:
  float_is_nan r ==> SmtFp (canon r) = (smtfp_nan : ('t,'w) smtfp)
Proof
  simp [canon_def, smtfp_nan_def]
QED

Theorem smtfp_min_op_nan:
  float_is_nan (float_min (smtfp_rep x) (smtfp_rep y)) ==>
  smtfp_min x y = (smtfp_nan : ('t,'w) smtfp)
Proof
  simp [smtfp_min_def, smtfp_op_nan]
QED

Theorem smtfp_max_op_nan:
  float_is_nan (float_max (smtfp_rep x) (smtfp_rep y)) ==>
  smtfp_max x y = (smtfp_nan : ('t,'w) smtfp)
Proof
  simp [smtfp_max_def, smtfp_op_nan]
QED

Theorem smtfp_rem_op_nan:
  float_is_nan (float_rem (smtfp_rep x) (smtfp_rep y)) ==>
  smtfp_rem x y = (smtfp_nan : ('t,'w) smtfp)
Proof
  simp [smtfp_rem_def, smtfp_op_nan]
QED

(* Away from NaN and the one underspecified signed-zero case, min/max agree
   directly with the strict floating-point order. *)
Theorem float_min_max_lt:
  ~float_is_nan x /\ ~float_is_nan y /\
  ~(float_is_zero x /\ float_is_zero y) /\
  float_less_than x y ==>
  float_min x y = x /\ float_max x y = y
Proof
  strip_tac >>
  fs [float_min_def, float_max_def,
      binary_ieeeTheory.float_less_than_def,
      binary_ieeeTheory.float_greater_than_def]
QED

Theorem float_min_max_gt:
  ~float_is_nan x /\ ~float_is_nan y /\
  ~(float_is_zero x /\ float_is_zero y) /\
  float_greater_than x y ==>
  float_min x y = y /\ float_max x y = x
Proof
  strip_tac >>
  fs [float_min_def, float_max_def,
      binary_ieeeTheory.float_less_than_def,
      binary_ieeeTheory.float_greater_than_def]
QED

(* minNum/maxNum ignore a sole NaN.  If both arguments are NaN these
   equations still return a NaN, which the smtfp wrappers canonicalize. *)
Theorem float_min_max_nan_left:
  float_is_nan x ==>
  float_min x y = y /\ float_max x y = y
Proof
  simp [float_min_def, float_max_def]
QED

Theorem float_min_max_nan_right:
  ~float_is_nan x /\ float_is_nan y ==>
  float_min x y = x /\ float_max x y = x
Proof
  simp [float_min_def, float_max_def]
QED

Theorem smtfp_min_max_nan_left:
  smtfp_is_nan x ==>
  smtfp_min x y = y /\ smtfp_max x y = y
Proof
  rw [smtfp_is_nan_def, smtfp_min_def, smtfp_max_def,
      float_min_def, float_max_def]
QED

Theorem smtfp_min_max_nan_right:
  ~smtfp_is_nan x /\ smtfp_is_nan y ==>
  smtfp_min x y = x /\ smtfp_max x y = x
Proof
  rw [smtfp_is_nan_def, smtfp_min_def, smtfp_max_def,
      float_min_def, float_max_def]
QED

Theorem float_min_opposite_zero:
  float_min (float_plus_zero (:'t # 'w))
    (float_minus_zero (:'t # 'w)) =
  float_min_zero_choice (:'t # 'w)
Proof
  simp [float_min_def]
QED

Theorem float_max_opposite_zero:
  float_max (float_plus_zero (:'t # 'w))
    (float_minus_zero (:'t # 'w)) =
  float_max_zero_choice (:'t # 'w)
Proof
  simp [float_max_def]
QED

Theorem smt_nearest_integer_basic[simp]:
  smt_nearest_integer 0 = 0 /\ smt_nearest_integer 1 = 1
Proof
  simp [smt_nearest_integer_def]
QED

Theorem smt_nearest_integer_ties_even[simp]:
  smt_nearest_integer (5 / 2) = 2 /\
  smt_nearest_integer (7 / 2) = 4
Proof
  `INT_FLOOR (5 / 2) = 2` by
    (rw [intrealTheory.INT_FLOOR] >> realLib.REAL_ARITH_TAC) >>
  `INT_FLOOR (7 / 2) = 3` by
    (rw [intrealTheory.INT_FLOOR] >> realLib.REAL_ARITH_TAC) >>
  `INT_CEILING (7 / 2) = 4` by
    (rw [intrealTheory.INT_CEILING] >> realLib.REAL_ARITH_TAC) >>
  simp [smt_nearest_integer_def] >>
  realLib.REAL_ARITH_TAC
QED

(* Definitional ground sanity instances.  TASK_12 adds the full literal
   evaluator, including further ordinary finite remainder examples. *)
Theorem float_rem_self:
  float_value x = Float r /\ r <> 0 ==>
  float_rem x x =
    if x.Sign = 1w then float_minus_zero (:'t # 'w)
    else float_plus_zero (:'t # 'w)
Proof
  rw [float_rem_def] >>
  imp_res_tac realTheory.REAL_DIV_REFL >>
  simp [smt_float_round_def, smt_round_def,
        binary_ieeeTheory.float_is_zero_to_real]
QED

Theorem float_rem_zero_infinity[simp]:
  float_rem (float_plus_zero (:'t # 'w))
    (float_plus_infinity (:'t # 'w)) =
      float_plus_zero (:'t # 'w) /\
  float_rem (float_minus_zero (:'t # 'w))
    (float_minus_infinity (:'t # 'w)) =
      float_minus_zero (:'t # 'w)
Proof
  simp [float_rem_def]
QED

Theorem float_rem_infinity_zero_is_nan[simp]:
  float_is_nan
    (float_rem (float_plus_infinity (:'t # 'w))
      (float_plus_zero (:'t # 'w)))
Proof
  simp [float_rem_def]
QED

Theorem smtfp_rem_zero_infinity[simp]:
  smtfp_rem (smtfp_pzero : ('t,'w) smtfp) smtfp_pinf = smtfp_pzero /\
  smtfp_rem (smtfp_nzero : ('t,'w) smtfp) smtfp_ninf = smtfp_nzero
Proof
  simp [smtfp_rem_def, smtfp_pzero_def, smtfp_nzero_def,
        smtfp_pinf_def, smtfp_ninf_def, smtfp_rep_def,
        smtfp_canonical_def, float_rem_def, canon_def]
QED

Definition smtfp_nan_pattern_def:
  smtfp_nan_pattern (e : 'w word) (m : 't word) <=>
    e = UINT_MAXw /\ m <> 0w
End

Theorem float_bits_is_nan[simp]:
  float_is_nan
    (<| Sign := s; Exponent := e; Significand := m |> : ('t,'w) float) <=>
  smtfp_nan_pattern e m
Proof
  simp [smtfp_nan_pattern_def, cj 1 binary_ieeeTheory.float_tests]
QED

Theorem SmtFp_11:
  smtfp_canonical r /\ smtfp_canonical q ==>
  ((SmtFp r : ('t,'w) smtfp) = SmtFp q <=> r = q)
Proof
  strip_tac >>
  metis_tac [smtfp_rep_def]
QED

Theorem smtfp_bits_nan:
  e = UINT_MAXw /\ m <> 0w ==>
  smtfp_bits s e m = (smtfp_nan : ('t,'w) smtfp)
Proof
  strip_tac >>
  simp [smtfp_bits_def, smtfp_nan_def, canon_def,
        smtfp_nan_pattern_def]
QED

Theorem smtfp_bits_surjective:
  !x : ('t,'w) smtfp. ?s e m. x = smtfp_bits s e m
Proof
  gen_tac >>
  qexists_tac `(smtfp_rep x).Sign` >>
  qexists_tac `(smtfp_rep x).Exponent` >>
  qexists_tac `(smtfp_rep x).Significand` >>
  `<| Sign := (smtfp_rep x).Sign;
       Exponent := (smtfp_rep x).Exponent;
       Significand := (smtfp_rep x).Significand |> = smtfp_rep x` by
    simp [binary_ieeeTheory.float_component_equality] >>
  simp [smtfp_bits_def]
QED

Theorem smtfp_bits_11_non_nan:
  ~smtfp_nan_pattern e m /\ ~smtfp_nan_pattern e' m' ==>
  ((smtfp_bits s e m : ('t,'w) smtfp) = smtfp_bits s' e' m' <=>
   s = s' /\ e = e' /\ m = m')
Proof
  strip_tac >>
  `~float_is_nan
     (<| Sign := s; Exponent := e; Significand := m |> :
       ('t,'w) float)` by
    fs [smtfp_nan_pattern_def] >>
  `~float_is_nan
     (<| Sign := s'; Exponent := e'; Significand := m' |> :
       ('t,'w) float)` by
    fs [smtfp_nan_pattern_def] >>
  simp [smtfp_bits_def, canon_def, SmtFp_11,
        smtfp_canonical_def,
        binary_ieeeTheory.float_component_equality]
QED

Theorem smtfp_nzero_neq_pzero:
  (smtfp_nzero : ('t,'w) smtfp) <> smtfp_pzero
Proof
  `((SmtFp (float_minus_zero (:'t # 'w)) : ('t,'w) smtfp) =
     SmtFp (float_plus_zero (:'t # 'w))) <=>
    float_minus_zero (:'t # 'w) = float_plus_zero (:'t # 'w)` by
    (irule SmtFp_11 >> simp [smtfp_canonical_def]) >>
  simp [smtfp_nzero_def, smtfp_pzero_def, canon_def]
QED

(* Certifying interfaces for the rounding conversions. *)
Theorem round_RTP_least_finite:
  -largest (:'t # 'w) <= x /\ x <= largest (:'t # 'w) /\
  float_is_finite (y : ('t,'w) float) /\ ~float_is_zero y /\
  x <= float_to_real y /\
  (!b : ('t,'w) float.
     float_is_finite b /\ x <= float_to_real b ==>
     float_to_real y <= float_to_real b) ==>
  round roundTowardPositive x = y
Proof
  rw [binary_ieeeTheory.round_def, binary_ieeeTheory.closest_def,
      binary_ieeeTheory.closest_such_def,
      binary_ieeeTheory.is_closest_def] >>
  TRY realLib.REAL_ASM_ARITH_TAC >>
  SELECT_ELIM_TAC >>
  conj_tac
  >- (qexists_tac `y` >> simp [] >> rpt strip_tac >>
      TRY realLib.REAL_ASM_ARITH_TAC >>
      qpat_x_assum `!b. _ ==> float_to_real y <= float_to_real b`
        (qspec_then `b` mp_tac) >>
      impl_tac
      >- (conj_tac >- simp [] >> realLib.REAL_ASM_ARITH_TAC) >>
      strip_tac >> realLib.REAL_ASM_ARITH_TAC)
  >- (rpt strip_tac >>
      qpat_x_assum `!b. _ ==> float_to_real y <= float_to_real b`
        (qspec_then `x'` mp_tac) >>
      impl_tac
      >- (conj_tac >- simp [] >> realLib.REAL_ASM_ARITH_TAC) >>
      strip_tac >>
      qpat_x_assum `!b. _ ==> _ <= abs (float_to_real b - x)`
        (qspec_then `y` mp_tac) >>
      impl_tac
      >- (conj_tac >- simp [] >> realLib.REAL_ASM_ARITH_TAC) >>
      strip_tac >>
      `float_to_real x' = float_to_real y` by
        realLib.REAL_ASM_ARITH_TAC >>
      fs [binary_ieeeTheory.float_to_real_eq] >> fs [])
QED

Theorem round_RTN_greatest_finite:
  -largest (:'t # 'w) <= x /\ x <= largest (:'t # 'w) /\
  float_is_finite (y : ('t,'w) float) /\ ~float_is_zero y /\
  float_to_real y <= x /\
  (!b : ('t,'w) float.
     float_is_finite b /\ float_to_real b <= x ==>
     float_to_real b <= float_to_real y) ==>
  round roundTowardNegative x = y
Proof
  rw [binary_ieeeTheory.round_def, binary_ieeeTheory.closest_def,
      binary_ieeeTheory.closest_such_def,
      binary_ieeeTheory.is_closest_def] >>
  TRY realLib.REAL_ASM_ARITH_TAC >>
  SELECT_ELIM_TAC >>
  conj_tac
  >- (qexists_tac `y` >> simp [] >> rpt strip_tac >>
      TRY realLib.REAL_ASM_ARITH_TAC >>
      qpat_x_assum `!b. _ ==> float_to_real b <= float_to_real y`
        (qspec_then `b` mp_tac) >>
      impl_tac
      >- (conj_tac >- simp [] >> realLib.REAL_ASM_ARITH_TAC) >>
      strip_tac >> realLib.REAL_ASM_ARITH_TAC)
  >- (rpt strip_tac >>
      qpat_x_assum `!b. _ ==> float_to_real b <= float_to_real y`
        (qspec_then `x'` mp_tac) >>
      impl_tac
      >- (conj_tac >- simp [] >> realLib.REAL_ASM_ARITH_TAC) >>
      strip_tac >>
      qpat_x_assum `!b. _ ==> _ <= abs (float_to_real b - x)`
        (qspec_then `y` mp_tac) >>
      impl_tac
      >- (conj_tac >- simp [] >> realLib.REAL_ASM_ARITH_TAC) >>
      strip_tac >>
      `float_to_real x' = float_to_real y` by
        realLib.REAL_ASM_ARITH_TAC >>
      fs [binary_ieeeTheory.float_to_real_eq] >> fs [])
QED

Theorem round_RNE_is_closest:
  -threshold (:'t # 'w) < x /\ x < threshold (:'t # 'w) ==>
  is_closest float_is_finite x
    (round roundTiesToEven x : ('t,'w) float)
Proof
  strip_tac >>
  `~(x <= -threshold (:'t # 'w)) /\
   ~(x >= threshold (:'t # 'w))` by
    realLib.REAL_ASM_ARITH_TAC >>
  simp [binary_ieeeTheory.round_def] >>
  irule (cj 1 closest_such_finite_properties)
QED

Theorem round_tiesToAway_from_closest_away:
  x <> 0 /\
  -threshold (:'t # 'w) < x /\ x < threshold (:'t # 'w) /\
  is_closest float_is_finite x (y : ('t,'w) float) /\
  ~float_is_zero y /\ abs x <= abs (float_to_real y) ==>
  round_tiesToAway x = y
Proof
  strip_tac >> irule round_tiesToAway_tie_away >> simp [] >>
  rpt strip_tac >>
  fs [binary_ieeeTheory.is_closest_def] >>
  res_tac >>
  qpat_x_assum
    `!b. b IN float_is_finite ==>
         abs (float_to_real y - x) <= _`
    (qspec_then `float_plus_zero (:'t # 'w)` mp_tac) >>
  simp [IN_DEF] >> strip_tac >>
  `float_to_real a = float_to_real y` by
    realLib.REAL_ASM_ARITH_TAC >>
  fs [binary_ieeeTheory.float_to_real_eq] >> fs []
QED

Theorem is_closest_finite_equal_distance:
  is_closest float_is_finite x (a : ('t,'w) float) /\
  float_is_finite (b : ('t,'w) float) /\
  abs (float_to_real b - x) = abs (float_to_real a - x) ==>
  is_closest float_is_finite x b
Proof
  strip_tac >> fs [binary_ieeeTheory.is_closest_def, IN_DEF] >>
  rpt strip_tac >> res_tac
QED

Theorem is_integral_real_of_int:
  binary_ieee$is_integral x <=> ?i : int. x = real_of_int i
Proof
  rw [binary_ieeeTheory.is_integral_def, realTheory.abs]
  >- (eq_tac >> rpt strip_tac
      >- (qexists_tac `&n` >> simp [])
      >- (Cases_on `i` >> fs []))
  >- (eq_tac >> rpt strip_tac
      >- (qexists_tac `-&n` >> simp [] >>
          realLib.REAL_ASM_ARITH_TAC)
      >- (Cases_on `i` >> fs []))
QED

Theorem abs_real_of_int:
  abs (real_of_int i) = real_of_int (ABS i)
Proof
  Cases_on `i` >> simp [intrealTheory.real_of_int_def,
                         integerTheory.INT_ABS]
QED

Theorem is_integral_separated:
  binary_ieee$is_integral x /\ binary_ieee$is_integral y /\ x <> y ==>
  1 <= abs (x - y)
Proof
  rw [is_integral_real_of_int] >>
  once_rewrite_tac [GSYM intrealTheory.real_of_int_sub] >>
  rewrite_tac [abs_real_of_int] >>
  once_rewrite_tac
    [GSYM (Q.INST [`n` |-> `1`] intrealTheory.real_of_int_num)] >>
  rewrite_tac [intrealTheory.real_of_int_le] >>
  fs [intrealTheory.real_of_int_11] >> intLib.ARITH_TAC
QED

Theorem float_is_integral_to_real:
  float_is_integral (a : ('t,'w) float) ==>
  binary_ieee$is_integral (float_to_real a)
Proof
  fs [binary_ieeeTheory.float_is_integral_def] >>
  Cases_on `float_value a` >>
  fs [binary_ieeeTheory.float_value_def] >>
  Cases_on `a.Exponent = -1w` >> fs [] >>
  Cases_on `a.Significand = 0w` >> fs []
QED

Theorem integral_round_candidate_gap:
  integral_round_candidate (a : ('t,'w) float) ==>
  float_to_real a = 0 \/ 1 <= abs (float_to_real a)
Proof
  rw [integral_round_candidate_def]
  >- (fs [binary_ieeeTheory.float_is_integral_def] >>
      Cases_on `float_value a` >>
      fs [binary_ieeeTheory.is_integral_def,
          binary_ieeeTheory.float_value_def] >>
      Cases_on `a.Exponent = -1w` >> fs [] >>
      Cases_on `a.Significand = 0w` >> fs [] >>
      Cases_on `n` >> fs [])
  >- (`1 <= abs (float_to_real
          (float_plus_infinity (:'t # 'w)))` by
        (simp [binary_ieeeTheory.float_plus_infinity_def,
               binary_ieeeTheory.float_to_real,
               wordsTheory.w2n_minus1] >>
         once_rewrite_tac [realTheory.REAL_MUL_COMM] >>
         rewrite_tac [GSYM realTheory.real_div] >>
         simp [realTheory.ABS_DIV, realTheory.REAL_LE_RDIV_EQ,
               wordsTheory.UINT_MAX_def, wordsTheory.INT_MAX_def] >>
         simp [DECIDE
           ``!n : num. 0 < n ==> 1 + (n - 1) = n``] >>
         irule arithmeticTheory.LESS_IMP_LESS_OR_EQ >>
         irule wordsTheory.INT_MIN_LT_DIMWORD) >>
      fs [binary_ieeeTheory.float_sets,
          binary_ieeeTheory.float_minus_infinity_def,
          binary_ieeeTheory.float_to_real_negate])
QED

Theorem integral_candidate_nearest:
  float_is_integral (y : ('t,'w) float) /\
  2 * abs (float_to_real y - x) <= 1 /\
  abs (float_to_real y - x) <
    abs (float_to_real (float_plus_infinity (:'t # 'w)) - x) /\
  abs (float_to_real y - x) <
    abs (float_to_real (float_minus_infinity (:'t # 'w)) - x) ==>
  is_closest integral_round_candidate x y
Proof
  rw [binary_ieeeTheory.is_closest_def, IN_DEF,
      integral_round_candidate_def]
  >- (imp_res_tac float_is_integral_to_real >>
      Cases_on `float_to_real y = float_to_real b` >> simp [] >>
      `1 <= abs (float_to_real y - float_to_real b)` by
        metis_tac [is_integral_separated] >>
      `abs (float_to_real y - float_to_real b) <=
       abs (float_to_real y - x) +
       abs (float_to_real b - x)` by
        (qspec_then
           `float_to_real y - x`
           (qspec_then `x - float_to_real b` mp_tac)
           realTheory.ABS_TRIANGLE >>
         simp [] >> realLib.REAL_ASM_ARITH_TAC) >>
      realLib.REAL_ASM_ARITH_TAC)
  >- (fs [binary_ieeeTheory.float_sets] >>
      realLib.REAL_ASM_ARITH_TAC)
QED

Theorem integral_round_tiesToAway_nearest:
  x <> 0 /\
  -threshold (:'t # 'w) < x /\ x < threshold (:'t # 'w) /\
  float_is_integral (y : ('t,'w) float) /\ ~float_is_zero y /\
  2 * abs (float_to_real y - x) <= 1 /\
  abs x <= abs (float_to_real y) /\
  abs (float_to_real y - x) <
    abs (float_to_real (float_plus_infinity (:'t # 'w)) - x) /\
  abs (float_to_real y - x) <
    abs (float_to_real (float_minus_infinity (:'t # 'w)) - x) ==>
  integral_round_tiesToAway x = y
Proof
  strip_tac >> irule integral_round_tiesToAway_tie_away >>
  simp [] >>
  conj_tac
  >- (rpt strip_tac >>
      `is_closest integral_round_candidate x y` by
        (irule integral_candidate_nearest >> simp []) >>
      fs [binary_ieeeTheory.is_closest_def, IN_DEF] >>
      qpat_x_assum
        `!b. integral_round_candidate b ==>
             abs (float_to_real a - x) <= _`
        (qspec_then `y` mp_tac) >> simp [] >> strip_tac >>
      qpat_x_assum `integral_round_candidate a`
        (strip_assume_tac o
         REWRITE_RULE [integral_round_candidate_def])
      >- (`float_to_real a <> 0` by
            (strip_tac >> fs [] >> Cases_on `0 <= x` >>
             fs [realTheory.abs] >> realLib.REAL_ASM_ARITH_TAC) >>
          `float_to_real y <> 0` by
            (strip_tac >> fs [] >> Cases_on `0 <= x` >>
             fs [realTheory.abs] >> realLib.REAL_ASM_ARITH_TAC) >>
          `1 <= abs (float_to_real a)` by
            (mp_tac (Q.INST [`a` |-> `a`]
               integral_round_candidate_gap) >>
             simp [integral_round_candidate_def]) >>
          `1 <= abs (float_to_real y)` by
            (mp_tac (Q.INST [`a` |-> `y`]
               integral_round_candidate_gap) >>
             simp [integral_round_candidate_def]) >>
          `abs (float_to_real y - x) <=
           abs (float_to_real a - x)` by
            (qpat_x_assum `!b. integral_round_candidate b ==> _`
               irule >>
             simp [integral_round_candidate_def]) >>
          `float_to_real a = float_to_real y` by
            (Cases_on `0 <= x` >>
             Cases_on `0 <= float_to_real a` >>
             Cases_on `0 <= float_to_real y` >>
             Cases_on `0 <= float_to_real a - x` >>
             Cases_on `0 <= float_to_real y - x` >>
             fs [realTheory.abs] >> realLib.REAL_ASM_ARITH_TAC) >>
          metis_tac [binary_ieeeTheory.float_to_real_eq])
      >- (fs [GSYM IN_DEF, binary_ieeeTheory.float_sets] >>
          qpat_x_assum `a = _` SUBST_ALL_TAC >>
          realLib.REAL_ASM_ARITH_TAC))
  >- (irule integral_candidate_nearest >> simp [])
QED

Theorem round_RTP_exact:
  -largest (:'t # 'w) <= x /\ x <= largest (:'t # 'w) /\
  float_is_finite (y : ('t,'w) float) /\ ~float_is_zero y /\
  float_to_real y = x ==>
  round roundTowardPositive x = y
Proof
  strip_tac >> irule round_RTP_least_finite >> simp []
QED

Theorem round_RTN_exact:
  -largest (:'t # 'w) <= x /\ x <= largest (:'t # 'w) /\
  float_is_finite (y : ('t,'w) float) /\ ~float_is_zero y /\
  float_to_real y = x ==>
  round roundTowardNegative x = y
Proof
  strip_tac >> irule round_RTN_greatest_finite >> simp []
QED

Theorem round_RTP_positive_next_hi:
  -largest (:'t # 'w) <= x /\ x <= largest (:'t # 'w) /\
  float_is_finite (lo : ('t,'w) float) /\
  float_is_finite (next_hi lo) /\ ~float_is_zero (next_hi lo) /\
  0 <= float_to_real lo /\ float_to_real lo < x /\
  x <= float_to_real (next_hi lo) ==>
  round roundTowardPositive x = next_hi lo
Proof
  strip_tac >> irule round_RTP_least_finite >> simp [] >>
  rpt strip_tac >>
  `abs (float_to_real lo) < abs (float_to_real b)` by
    realLib.REAL_ASM_ARITH_TAC >>
  `abs (float_to_real (next_hi lo)) <= abs (float_to_real b)` by
    metis_tac [binary_ieeeTheory.next_hi_discrete] >>
  realLib.REAL_ASM_ARITH_TAC
QED

Theorem round_RTP_negative_inward:
  -largest (:'t # 'w) <= x /\ x <= largest (:'t # 'w) /\
  float_is_finite (y : ('t,'w) float) /\ ~float_is_zero y /\
  float_to_real (next_hi y) < x /\ x <= float_to_real y /\
  float_to_real y < 0 /\ float_to_real (next_hi y) < 0 ==>
  round roundTowardPositive x = y
Proof
  strip_tac >> irule round_RTP_least_finite >> simp [] >>
  rpt strip_tac >>
  Cases_on `0 <= float_to_real b`
  >- realLib.REAL_ASM_ARITH_TAC >>
  Cases_on `float_to_real y <= float_to_real b`
  >- simp [] >>
  `abs (float_to_real y) < abs (float_to_real b)` by
    realLib.REAL_ASM_ARITH_TAC >>
  `abs (float_to_real (next_hi y)) <= abs (float_to_real b)` by
    metis_tac [binary_ieeeTheory.next_hi_discrete] >>
  realLib.REAL_ASM_ARITH_TAC
QED

Theorem round_RTN_positive_inward:
  -largest (:'t # 'w) <= x /\ x <= largest (:'t # 'w) /\
  float_is_finite (y : ('t,'w) float) /\ ~float_is_zero y /\
  0 < float_to_real y /\ float_to_real y <= x /\
  x < float_to_real (next_hi y) /\
  0 < float_to_real (next_hi y) ==>
  round roundTowardNegative x = y
Proof
  strip_tac >> irule round_RTN_greatest_finite >> simp [] >>
  rpt strip_tac >>
  Cases_on `float_to_real b <= 0`
  >- realLib.REAL_ASM_ARITH_TAC >>
  Cases_on `float_to_real b <= float_to_real y`
  >- simp [] >>
  `abs (float_to_real y) < abs (float_to_real b)` by
    realLib.REAL_ASM_ARITH_TAC >>
  `abs (float_to_real (next_hi y)) <= abs (float_to_real b)` by
    metis_tac [binary_ieeeTheory.next_hi_discrete] >>
  realLib.REAL_ASM_ARITH_TAC
QED

Theorem round_RTN_negative_next_hi:
  -largest (:'t # 'w) <= x /\ x <= largest (:'t # 'w) /\
  float_is_finite (lo : ('t,'w) float) /\
  float_is_finite (next_hi lo) /\ ~float_is_zero (next_hi lo) /\
  float_to_real (next_hi lo) <= x /\ x < float_to_real lo /\
  float_to_real lo < 0 /\ float_to_real (next_hi lo) < 0 ==>
  round roundTowardNegative x = next_hi lo
Proof
  strip_tac >> irule round_RTN_greatest_finite >> simp [] >>
  rpt strip_tac >>
  `abs (float_to_real lo) < abs (float_to_real b)` by
    realLib.REAL_ASM_ARITH_TAC >>
  `abs (float_to_real (next_hi lo)) <= abs (float_to_real b)` by
    metis_tac [binary_ieeeTheory.next_hi_discrete] >>
  realLib.REAL_ASM_ARITH_TAC
QED

Theorem nonzero_float_at_least_ulp:
  ~float_is_zero (y : ('t,'w) float) ==>
  ulp (:'t # 'w) <= abs (float_to_real y)
Proof
  strip_tac >>
  mp_tac (Q.SPECL [`float_plus_zero (:'t # 'w)`, `y`]
    binary_ieeeTheory.diff_float_ULP) >>
  simp [binary_ieeeTheory.float_is_zero_to_real,
        binary_ieeeTheory.exponent_boundary_def,
        binary_ieeeTheory.ulp_def] >>
  metis_tac [binary_ieeeTheory.float_is_zero_to_real]
QED

Theorem round_RTP_small_positive:
  0 < x /\ x <= ulp (:'t # 'w) ==>
  round roundTowardPositive x = float_plus_min (:'t # 'w)
Proof
  strip_tac >> irule round_RTP_least_finite >>
  simp [GSYM binary_ieeeTheory.ulp] >>
  conj_tac
  >- (rpt strip_tac >>
      Cases_on `float_is_zero b`
      >- (fs [binary_ieeeTheory.float_is_zero_to_real] >>
          realLib.REAL_ASM_ARITH_TAC) >>
      mp_tac (Q.SPEC `b` (GEN_ALL nonzero_float_at_least_ulp)) >>
      simp [realTheory.abs] >> realLib.REAL_ASM_ARITH_TAC) >>
  mp_tac (INST_TYPE [alpha |-> ``:'t``, beta |-> ``:'w``]
    binary_ieeeTheory.ulp_lt_largest) >>
  simp [] >> realLib.REAL_ASM_ARITH_TAC
QED

Theorem round_RTN_small_negative:
  -ulp (:'t # 'w) <= x /\ x < 0 ==>
  round roundTowardNegative x =
    float_negate (float_plus_min (:'t # 'w))
Proof
  strip_tac >> irule round_RTN_greatest_finite >>
  simp [GSYM binary_ieeeTheory.neg_ulp] >>
  conj_tac
  >- (rpt strip_tac >>
      Cases_on `float_is_zero b`
      >- (fs [binary_ieeeTheory.float_is_zero_to_real] >>
          realLib.REAL_ASM_ARITH_TAC) >>
      mp_tac (Q.SPEC `b` (GEN_ALL nonzero_float_at_least_ulp)) >>
      simp [realTheory.abs] >> realLib.REAL_ASM_ARITH_TAC) >>
  mp_tac (INST_TYPE [alpha |-> ``:'t``, beta |-> ``:'w``]
    binary_ieeeTheory.ulp_lt_largest) >>
  simp [] >> realLib.REAL_ASM_ARITH_TAC
QED

Theorem closest_finite_positive_inward_unique:
  is_closest float_is_finite x (y : ('t,'w) float) /\
  float_is_finite y /\ ~float_is_zero y /\
  float_is_finite (next_hi y) /\
  0 < float_to_real y /\ float_to_real y < x /\
  x < float_to_real (next_hi y) /\
  abs (float_to_real y - x) <
    abs (float_to_real (next_hi y) - x) ==>
  !a : ('t,'w) float. is_closest float_is_finite x a ==> a = y
Proof
  strip_tac >> rpt strip_tac >>
  fs [binary_ieeeTheory.is_closest_def, IN_DEF] >>
  `abs (float_to_real a - x) = abs (float_to_real y - x)` by
    (qpat_x_assum
       `!b. float_is_finite b ==>
          abs (float_to_real y - x) <= abs (float_to_real b - x)`
       (qspec_then `a` mp_tac) >>
     qpat_x_assum
       `!b. float_is_finite b ==>
          abs (float_to_real a - x) <= abs (float_to_real b - x)`
       (qspec_then `y` mp_tac) >>
     simp [] >> realLib.REAL_ASM_ARITH_TAC) >>
  Cases_on `float_to_real a <= float_to_real y`
  >- (`abs (float_to_real a - x) = x - float_to_real a` by
        (rw [realTheory.abs] >> realLib.REAL_ASM_ARITH_TAC) >>
      `abs (float_to_real y - x) = x - float_to_real y` by
        (rw [realTheory.abs] >> realLib.REAL_ASM_ARITH_TAC) >>
      `float_to_real a = float_to_real y` by
        realLib.REAL_ASM_ARITH_TAC >>
      metis_tac [binary_ieeeTheory.float_to_real_eq])
  >- (`abs (float_to_real y) < abs (float_to_real a)` by
        (rw [realTheory.abs] >> realLib.REAL_ASM_ARITH_TAC) >>
      `abs (float_to_real (next_hi y)) <= abs (float_to_real a)` by
        metis_tac [binary_ieeeTheory.next_hi_discrete] >>
      `0 < float_to_real (next_hi y)` by
        realLib.REAL_ASM_ARITH_TAC >>
      `float_to_real (next_hi y) <= float_to_real a` by
        (fs [realTheory.abs] >> realLib.REAL_ASM_ARITH_TAC) >>
      `abs (float_to_real a - x) = float_to_real a - x` by
        (rw [realTheory.abs] >> realLib.REAL_ASM_ARITH_TAC) >>
      `abs (float_to_real y - x) = x - float_to_real y` by
        (rw [realTheory.abs] >> realLib.REAL_ASM_ARITH_TAC) >>
      `abs (float_to_real (next_hi y) - x) =
       float_to_real (next_hi y) - x` by
        (rw [realTheory.abs] >> realLib.REAL_ASM_ARITH_TAC) >>
      realLib.REAL_ASM_ARITH_TAC)
QED

Theorem closest_finite_negative_inward_unique:
  is_closest float_is_finite x (y : ('t,'w) float) /\
  float_is_finite y /\ ~float_is_zero y /\
  float_is_finite (next_hi y) /\
  float_to_real y < 0 /\ x < float_to_real y /\
  float_to_real (next_hi y) < x /\
  abs (float_to_real y - x) <
    abs (float_to_real (next_hi y) - x) ==>
  !a : ('t,'w) float. is_closest float_is_finite x a ==> a = y
Proof
  strip_tac >> rpt strip_tac >>
  fs [binary_ieeeTheory.is_closest_def, IN_DEF] >>
  `abs (float_to_real a - x) = abs (float_to_real y - x)` by
    (qpat_x_assum
       `!b. float_is_finite b ==>
          abs (float_to_real y - x) <= abs (float_to_real b - x)`
       (qspec_then `a` mp_tac) >>
     qpat_x_assum
       `!b. float_is_finite b ==>
          abs (float_to_real a - x) <= abs (float_to_real b - x)`
       (qspec_then `y` mp_tac) >>
     simp [] >> realLib.REAL_ASM_ARITH_TAC) >>
  Cases_on `float_to_real y <= float_to_real a`
  >- (`abs (float_to_real a - x) = float_to_real a - x` by
        (rw [realTheory.abs] >> realLib.REAL_ASM_ARITH_TAC) >>
      `abs (float_to_real y - x) = float_to_real y - x` by
        (rw [realTheory.abs] >> realLib.REAL_ASM_ARITH_TAC) >>
      `float_to_real a = float_to_real y` by
        realLib.REAL_ASM_ARITH_TAC >>
      metis_tac [binary_ieeeTheory.float_to_real_eq])
  >- (`abs (float_to_real y) < abs (float_to_real a)` by
        (rw [realTheory.abs] >> realLib.REAL_ASM_ARITH_TAC) >>
      `abs (float_to_real (next_hi y)) <= abs (float_to_real a)` by
        metis_tac [binary_ieeeTheory.next_hi_discrete] >>
      `float_to_real (next_hi y) < 0` by
        realLib.REAL_ASM_ARITH_TAC >>
      `float_to_real a <= float_to_real (next_hi y)` by
        (fs [realTheory.abs] >> realLib.REAL_ASM_ARITH_TAC) >>
      `abs (float_to_real a - x) = x - float_to_real a` by
        (rw [realTheory.abs] >> realLib.REAL_ASM_ARITH_TAC) >>
      `abs (float_to_real y - x) = float_to_real y - x` by
        (rw [realTheory.abs] >> realLib.REAL_ASM_ARITH_TAC) >>
      `abs (float_to_real (next_hi y) - x) =
       x - float_to_real (next_hi y)` by
        (rw [realTheory.abs] >> realLib.REAL_ASM_ARITH_TAC) >>
      realLib.REAL_ASM_ARITH_TAC)
QED

Theorem round_tiesToAway_positive_inward:
  -threshold (:'t # 'w) < x /\ x < threshold (:'t # 'w) /\
  is_closest float_is_finite x (y : ('t,'w) float) /\
  float_is_finite y /\ ~float_is_zero y /\
  float_is_finite (next_hi y) /\
  0 < float_to_real y /\ float_to_real y < x /\
  x < float_to_real (next_hi y) /\
  abs (float_to_real y - x) <
    abs (float_to_real (next_hi y) - x) ==>
  round_tiesToAway x = y
Proof
  strip_tac >>
  `!a : ('t,'w) float.
     is_closest float_is_finite x a ==> a = y` by
    metis_tac [closest_finite_positive_inward_unique] >>
  `round roundTiesToEven x = y` by
    (qpat_x_assum `!a. is_closest _ _ a ==> a = y` irule >>
     irule round_RNE_is_closest >> simp []) >>
  metis_tac [round_tiesToAway_eq_RNE_when_closest_unique]
QED

Theorem round_tiesToAway_negative_inward:
  -threshold (:'t # 'w) < x /\ x < threshold (:'t # 'w) /\
  is_closest float_is_finite x (y : ('t,'w) float) /\
  float_is_finite y /\ ~float_is_zero y /\
  float_is_finite (next_hi y) /\
  float_to_real y < 0 /\ x < float_to_real y /\
  float_to_real (next_hi y) < x /\
  abs (float_to_real y - x) <
    abs (float_to_real (next_hi y) - x) ==>
  round_tiesToAway x = y
Proof
  strip_tac >>
  `!a : ('t,'w) float.
     is_closest float_is_finite x a ==> a = y` by
    metis_tac [closest_finite_negative_inward_unique] >>
  `round roundTiesToEven x = y` by
    (qpat_x_assum `!a. is_closest _ _ a ==> a = y` irule >>
     irule round_RNE_is_closest >> simp []) >>
  metis_tac [round_tiesToAway_eq_RNE_when_closest_unique]
QED

Theorem integral_candidate_from_finite_closest:
  is_closest float_is_finite x (y : ('t,'w) float) /\
  float_is_integral y /\
  abs (float_to_real y - x) <
    abs (float_to_real (float_plus_infinity (:'t # 'w)) - x) /\
  abs (float_to_real y - x) <
    abs (float_to_real (float_minus_infinity (:'t # 'w)) - x) ==>
  is_closest integral_round_candidate x y
Proof
  rw [binary_ieeeTheory.is_closest_def, IN_DEF,
      integral_round_candidate_def]
  >- (qpat_x_assum `!b. float_is_finite b ==> _` irule >>
      fs [binary_ieeeTheory.float_is_integral_def,
          binary_ieeeTheory.float_is_finite_def] >>
      Cases_on `float_value b` >> fs [])
  >- (fs [GSYM IN_DEF, binary_ieeeTheory.float_sets] >>
      realLib.REAL_ASM_ARITH_TAC)
QED

Theorem integral_candidate_strict_unique:
  float_is_integral (y : ('t,'w) float) /\ ~float_is_zero y /\
  2 * abs (float_to_real y - x) < 1 /\
  abs (float_to_real y - x) <
    abs (float_to_real (float_plus_infinity (:'t # 'w)) - x) /\
  abs (float_to_real y - x) <
    abs (float_to_real (float_minus_infinity (:'t # 'w)) - x) ==>
  !a : ('t,'w) float.
    is_closest integral_round_candidate x a ==> a = y
Proof
  strip_tac >>
  `is_closest integral_round_candidate x y` by
    (irule integral_candidate_nearest >> simp [] >>
     realLib.REAL_ASM_ARITH_TAC) >>
  rpt strip_tac >>
  `abs (float_to_real y - x) <= abs (float_to_real a - x)` by
    (qpat_x_assum `is_closest integral_round_candidate x y`
       (mp_tac o Q.SPEC `a` o cj 2 o
        REWRITE_RULE [binary_ieeeTheory.is_closest_def, IN_DEF]) >>
     disch_then irule >>
     qpat_x_assum `is_closest integral_round_candidate x a` mp_tac >>
     simp [binary_ieeeTheory.is_closest_def, IN_DEF]) >>
  `abs (float_to_real a - x) <= abs (float_to_real y - x)` by
    (qpat_x_assum `is_closest integral_round_candidate x a`
       (mp_tac o Q.SPEC `y` o cj 2 o
        REWRITE_RULE [binary_ieeeTheory.is_closest_def, IN_DEF]) >>
     disch_then irule >>
     qpat_x_assum `is_closest integral_round_candidate x y` mp_tac >>
     simp [binary_ieeeTheory.is_closest_def, IN_DEF]) >>
  `abs (float_to_real a - x) = abs (float_to_real y - x)` by
    realLib.REAL_ASM_ARITH_TAC >>
  `integral_round_candidate a` by
    (qpat_x_assum `is_closest integral_round_candidate x a` mp_tac >>
     simp [binary_ieeeTheory.is_closest_def, IN_DEF]) >>
  `~float_is_infinite a` by
    (strip_tac >>
     fs [GSYM IN_DEF, binary_ieeeTheory.float_sets] >>
     qpat_x_assum `a = _` SUBST_ALL_TAC >>
     realLib.REAL_ASM_ARITH_TAC) >>
  `float_is_integral a` by
    fs [integral_round_candidate_def] >>
  imp_res_tac float_is_integral_to_real >>
  Cases_on `float_to_real a = float_to_real y`
  >- metis_tac [binary_ieeeTheory.float_to_real_eq] >>
  `1 <= abs (float_to_real a - float_to_real y)` by
    metis_tac [is_integral_separated] >>
  `abs (float_to_real a - float_to_real y) <=
   abs (float_to_real a - x) + abs (float_to_real y - x)` by
    (qspec_then `float_to_real a - x`
       (qspec_then `x - float_to_real y` mp_tac)
       realTheory.ABS_TRIANGLE >>
     simp [] >> realLib.REAL_ASM_ARITH_TAC) >>
  realLib.REAL_ASM_ARITH_TAC
QED

Theorem integral_round_tiesToAway_strict_nearest:
  x <> 0 /\
  -threshold (:'t # 'w) < x /\ x < threshold (:'t # 'w) /\
  float_is_integral (y : ('t,'w) float) /\ ~float_is_zero y /\
  2 * abs (float_to_real y - x) < 1 /\
  abs (float_to_real y - x) <
    abs (float_to_real (float_plus_infinity (:'t # 'w)) - x) /\
  abs (float_to_real y - x) <
    abs (float_to_real (float_minus_infinity (:'t # 'w)) - x) ==>
  integral_round_tiesToAway x = y
Proof
  strip_tac >>
  `!a : ('t,'w) float.
     is_closest integral_round_candidate x a ==> a = y` by
    metis_tac [integral_candidate_strict_unique] >>
  `~(x <= -threshold (:'t # 'w)) /\
   ~(x >= threshold (:'t # 'w))` by
    realLib.REAL_ASM_ARITH_TAC >>
  simp [integral_round_tiesToAway_def] >>
  first_x_assum irule >>
  irule (cj 1 closest_such_integral_properties)
QED

Theorem round_tiesToAway_half_ulp_positive:
  0 < x /\ 2 * x = ulp (:'t # 'w) ==>
  (round_tiesToAway x : ('t,'w) float) = float_plus_min (:'t # 'w)
Proof
  strip_tac >>
  `-threshold (:'t # 'w) < x /\ x < threshold (:'t # 'w)` by
    (mp_tac (INST_TYPE [alpha |-> ``:'t``, beta |-> ``:'w``]
       binary_ieeeTheory.ulp_lt_threshold) >>
     simp [] >> realLib.REAL_ASM_ARITH_TAC) >>
  `float_to_real
      (round roundTiesToEven x : ('t,'w) float) = 0` by
    (mp_tac (Q.SPEC `x`
       (INST_TYPE [alpha |-> ``:'t``, beta |-> ``:'w``]
         binary_ieeeTheory.round_roundTiesToEven_is_zero)) >>
     impl_tac >- (simp [] >> realLib.REAL_ASM_ARITH_TAC) >>
     strip_tac >> fs []) >>
  `is_closest float_is_finite x
      (round roundTiesToEven x : ('t,'w) float)` by
    metis_tac [round_RNE_is_closest] >>
  `float_is_finite (float_plus_min (:'t # 'w))` by simp [] >>
  `abs (float_to_real (float_plus_min (:'t # 'w)) - x) =
   abs (float_to_real
     (round roundTiesToEven x : ('t,'w) float) - x)` by
    (simp [GSYM binary_ieeeTheory.ulp] >>
     realLib.REAL_ASM_ARITH_TAC) >>
  `is_closest float_is_finite x
      (float_plus_min (:'t # 'w))` by
    metis_tac [is_closest_finite_equal_distance] >>
  irule round_tiesToAway_from_closest_away >>
  simp [GSYM binary_ieeeTheory.ulp] >>
  realLib.REAL_ASM_ARITH_TAC
QED

Theorem round_tiesToAway_half_ulp_negative:
  x < 0 /\ 2 * -x = ulp (:'t # 'w) ==>
  (round_tiesToAway x : ('t,'w) float) =
  float_negate (float_plus_min (:'t # 'w))
Proof
  strip_tac >>
  `-threshold (:'t # 'w) < x /\ x < threshold (:'t # 'w)` by
    (mp_tac (INST_TYPE [alpha |-> ``:'t``, beta |-> ``:'w``]
       binary_ieeeTheory.ulp_lt_threshold) >>
     simp [] >> realLib.REAL_ASM_ARITH_TAC) >>
  `float_to_real
      (round roundTiesToEven x : ('t,'w) float) = 0` by
    (mp_tac (Q.SPEC `x`
       (INST_TYPE [alpha |-> ``:'t``, beta |-> ``:'w``]
         binary_ieeeTheory.round_roundTiesToEven_is_zero)) >>
     impl_tac >- (simp [] >> realLib.REAL_ASM_ARITH_TAC) >>
     strip_tac >> fs []) >>
  `is_closest float_is_finite x
      (round roundTiesToEven x : ('t,'w) float)` by
    metis_tac [round_RNE_is_closest] >>
  `float_is_finite
      (float_negate (float_plus_min (:'t # 'w)))` by
    simp [binary_ieeeTheory.float_negate_def,
          binary_ieeeTheory.float_plus_min_def,
          binary_ieeeTheory.float_is_finite_def,
          binary_ieeeTheory.float_value_def] >>
  `abs (float_to_real
          (float_negate (float_plus_min (:'t # 'w))) - x) =
   abs (float_to_real
     (round roundTiesToEven x : ('t,'w) float) - x)` by
    (simp [GSYM binary_ieeeTheory.neg_ulp] >>
     realLib.REAL_ASM_ARITH_TAC) >>
  `is_closest float_is_finite x
      (float_negate (float_plus_min (:'t # 'w)))` by
    metis_tac [is_closest_finite_equal_distance] >>
  irule round_tiesToAway_from_closest_away >>
  simp [GSYM binary_ieeeTheory.neg_ulp] >>
  realLib.REAL_ASM_ARITH_TAC
QED

Theorem equal_distance_same_away:
  x <> 0 /\ abs (y - x) <= abs x /\ abs (z - x) = abs (y - x) /\
  (abs x <= abs z <=> abs x <= abs y) ==>
  z = y
Proof
  rpt strip_tac >>
  Cases_on `0 <= x` >> Cases_on `0 <= y` >> Cases_on `0 <= z` >>
  Cases_on `0 <= y - x` >> Cases_on `0 <= z - x` >>
  fs [realTheory.abs] >> realLib.REAL_ASM_ARITH_TAC
QED

Theorem integral_round_tiesToAway_from_float_round:
  x <> 0 /\
  -threshold (:'t # 'w) < x /\ x < threshold (:'t # 'w) /\
  (round_tiesToAway x : ('t,'w) float) = y /\
  float_is_integral y /\ ~float_is_zero y /\
  abs (float_to_real y - x) <
    abs (float_to_real (float_plus_infinity (:'t # 'w)) - x) /\
  abs (float_to_real y - x) <
    abs (float_to_real (float_minus_infinity (:'t # 'w)) - x) ==>
  integral_round_tiesToAway x = y
Proof
  strip_tac >>
  `is_closest float_is_finite x y` by
    metis_tac [round_tiesToAway_is_closest] >>
  `is_closest integral_round_candidate x y` by
    (irule integral_candidate_from_finite_closest >> simp []) >>
  `~(x <= -threshold (:'t # 'w)) /\
   ~(x >= threshold (:'t # 'w))` by
    realLib.REAL_ASM_ARITH_TAC >>
  simp [integral_round_tiesToAway_def] >>
  qabbrev_tac `z : ('t,'w) float =
    closest_such (\a. abs x <= abs (float_to_real a))
      integral_round_candidate x` >>
  mp_tac (Q.INST
    [`p` |-> `\a : ('t,'w) float. abs x <= abs (float_to_real a)`,
     `x` |-> `x`] closest_such_integral_properties) >>
  simp [Abbr `z`] >> strip_tac >>
  qabbrev_tac `z : ('t,'w) float =
    closest_such (\a. abs x <= abs (float_to_real a))
      integral_round_candidate x` >>
  `abs (float_to_real y - x) <= abs (float_to_real z - x)` by
    (qpat_x_assum `is_closest integral_round_candidate x y`
       (mp_tac o Q.SPEC `z` o cj 2 o
        REWRITE_RULE [binary_ieeeTheory.is_closest_def, IN_DEF]) >>
     disch_then irule >>
     qpat_x_assum `is_closest integral_round_candidate x z` mp_tac >>
     simp [binary_ieeeTheory.is_closest_def, IN_DEF]) >>
  `abs (float_to_real z - x) <= abs (float_to_real y - x)` by
    (qpat_x_assum `is_closest integral_round_candidate x z`
       (mp_tac o Q.SPEC `y` o cj 2 o
        REWRITE_RULE [binary_ieeeTheory.is_closest_def, IN_DEF]) >>
     disch_then irule >>
     qpat_x_assum `is_closest integral_round_candidate x y` mp_tac >>
     simp [binary_ieeeTheory.is_closest_def, IN_DEF]) >>
  `abs (float_to_real z - x) = abs (float_to_real y - x)` by
    realLib.REAL_ASM_ARITH_TAC >>
  `integral_round_candidate z` by
    (qpat_x_assum `is_closest integral_round_candidate x z` mp_tac >>
     simp [binary_ieeeTheory.is_closest_def, IN_DEF]) >>
  `~float_is_infinite z` by
    (strip_tac >>
     fs [GSYM IN_DEF, binary_ieeeTheory.float_sets] >>
     qpat_x_assum `z = _` SUBST_ALL_TAC >>
     realLib.REAL_ASM_ARITH_TAC) >>
  `float_is_integral z` by
    fs [integral_round_candidate_def] >>
  `is_closest float_is_finite x z` by
    (rw [binary_ieeeTheory.is_closest_def, IN_DEF]
     >- (fs [binary_ieeeTheory.float_is_integral_def,
             binary_ieeeTheory.float_is_finite_def] >>
         Cases_on `float_value z` >> fs [])
     >- (qpat_x_assum `is_closest float_is_finite x y`
           (mp_tac o Q.SPEC `b` o cj 2 o
            REWRITE_RULE [binary_ieeeTheory.is_closest_def, IN_DEF]) >>
         simp [])) >>
  `abs x <= abs (float_to_real z) <=>
   abs x <= abs (float_to_real y)` by
    (eq_tac >> strip_tac
     >- metis_tac [round_tiesToAway_away]
     >- (qpat_x_assum
           `(?b. is_closest integral_round_candidate x b /\
                 abs x <= abs (float_to_real b)) ==>
            abs x <= abs (float_to_real z)` irule >>
         qexists_tac `y` >> simp [])) >>
  `abs (float_to_real y - x) <= abs x` by
    (qpat_x_assum `is_closest float_is_finite x y`
       (mp_tac o Q.SPEC `float_plus_zero (:'t # 'w)` o cj 2 o
        REWRITE_RULE [binary_ieeeTheory.is_closest_def, IN_DEF]) >>
     simp []) >>
  `float_to_real z = float_to_real y` by
    metis_tac [equal_distance_same_away] >>
  `z = y` by
    (fs [binary_ieeeTheory.float_to_real_eq] >> fs []) >>
  simp [Abbr `z`]
QED
