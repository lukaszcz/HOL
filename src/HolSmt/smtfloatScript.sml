(* Copyright (c) 2026 The HOL4 contributors. *)

(* The SMT-LIB significand width includes the hidden bit.  Thus the HOL
   instance corresponding to (_ FloatingPoint eb sb) is ('t,'w) float with
   dimindex(:'t) = sb - 1 and dimindex(:'w) = eb.  In particular, Float32
   is (23,8) float.  The definitions in this theory remain schematic in
   both widths.

   Canonicalization audit for the core surface (P5.5): every FP-valued
   definition post-composes [canon].  This applies to smtfp_intro,
   smtfp_bits, nan/pinf/ninf/pzero/nzero, abs/neg, add/sub/mul/div/sqrt/fma,
   and round_to_integral.  The classification predicates (nan, signalling,
   infinite, normal, subnormal, zero, finite, integral, negative, positive)
   and comparisons (lt/le/gt/ge/eq/unordered) are Bool-valued: they inspect
   smtfp_rep directly, so canonicalization is not applicable. *)
Theory smtfloat
Ancestors[qualified]
  binary_ieee

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

(* One proof covers the canonicalization obligation of every result-valued
   operation above: a NaN result is always the sole SMT-LIB NaN value. *)
Theorem smtfp_op_nan:
  float_is_nan r ==> SmtFp (canon r) = (smtfp_nan : ('t,'w) smtfp)
Proof
  simp [canon_def, smtfp_nan_def]
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
