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

Theorem smtfp_intro_rep[simp]:
  smtfp_intro (smtfp_rep x) = x
Proof
  simp [smtfp_intro_def]
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

(* The native binary_ieee surface has the four IEEE rounding modes that are
   shared with SMT-LIB.  This total map is the mode component of the outbound
   transfer kit; RNA has no native binary_ieee constructor. *)
Definition smtfp_rounding_of_binary_def:
  smtfp_rounding_of_binary mode =
    case mode of
      roundTiesToEven => RNE
    | roundTowardPositive => RTP
    | roundTowardNegative => RTN
    | roundTowardZero => RTZ
End

Theorem to_binary_rounding_of_binary[simp]:
  to_binary_rounding (smtfp_rounding_of_binary mode) = SOME mode
Proof
  Cases_on `mode` >> simp [smtfp_rounding_of_binary_def,
                           to_binary_rounding_def]
QED

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
Theorem round_tiesToAway_zero_is_zero[simp]:
  float_is_zero (round_tiesToAway 0 : ('t,'w) float)
Proof
  rewrite_tac [binary_ieeeTheory.float_is_zero_to_real] >>
  rewrite_tac [GSYM binary_ieeePropsTheory.is_closest_0_float_to_real] >>
  irule round_tiesToAway_is_closest >>
  simp [binary_ieeeTheory.threshold_is_positive]
QED

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

(* The unbounded mathematical integer rounders are shared by fp.rem,
   fp.roundToIntegral, and the BV conversions. *)
Definition smt_nearest_integer_def[nocompute]:
  smt_nearest_integer (r : real) : int =
    let f = INT_FLOOR r in
    let df = abs (r - real_of_int f) in
      if df < 1 / 2 \/
         df = 1 / 2 /\ EVEN (Num (ABS f))
      then f
      else INT_CEILING r
End

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
Theorem smt_float_round_RNA_zero[simp]:
  smt_float_round RNA to_neg 0 =
    if to_neg then float_minus_zero (:'t # 'w)
    else float_plus_zero (:'t # 'w)
Proof
  simp [smt_float_round_def, smt_round_def]
QED

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
    case float_value x of
      Float r =>
        let i = smt_real_to_int mode r in
          smt_float_round mode (x.Sign = 1w) (real_of_int i)
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

(* fp.rem's quotient integer is mathematical, not restricted to the operand
   format: rounding it through [('t,'w) float] would overflow for, e.g.,
   max-finite divided by min-subnormal. *)
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

(* The result index is independent of the field index expression.  A
   proof-local (_ BitVec n) type has the same dimension as 1 + eb + (sb - 1),
   but need not be syntactically the same HOL index type. *)
Definition smtfp_pack_bv_def:
  smtfp_pack_bv (x : ('t,'w) smtfp) : 'p word =
    (smtfp_rep x).Sign @@
      (((smtfp_rep x).Exponent @@ (smtfp_rep x).Significand) :
       ('w + 't) word)
End

(* -------------------------------------------------------------------------
   Proved outbound transfer kit for native binary_ieee terms
   ------------------------------------------------------------------------- *)

Theorem float_canon_qnan_value[simp]:
  float_value (float_canon_qnan : ('t,'w) float) = NaN
Proof
  simp [float_canon_qnan_def, binary_ieeeTheory.float_value_def,
        canon_qnan_msb]
QED

Theorem native_float_bits_transfer:
  smtfp_intro
    (<| Sign := s; Exponent := e; Significand := m |> : ('t,'w) float) =
  smtfp_bits s e m
Proof
  simp [smtfp_intro_def, smtfp_bits_def]
QED

(* A binder transfers only after its body has factored completely through
   smtfp_intro.  Thus quantified raw equality cannot match these theorems,
   while a goal on the invariant operator surface gets an exact smtfp binder.
   Surjectivity is supplied by smtfp_rep, not assumed by the serializer. *)
Theorem native_float_forall_transfer:
  (!x : ('t,'w) float. P (smtfp_intro x)) <=>
  (!y : ('t,'w) smtfp. P y)
Proof
  metis_tac [smtfp_intro_rep]
QED

Theorem native_float_exists_transfer:
  (?x : ('t,'w) float. P (smtfp_intro x)) <=>
  (?y : ('t,'w) smtfp. P y)
Proof
  metis_tac [smtfp_intro_rep]
QED

Theorem native_float_special_transfer:
  smtfp_intro (float_plus_zero (:'t # 'w)) = smtfp_pzero /\
  smtfp_intro (float_minus_zero (:'t # 'w)) = smtfp_nzero /\
  smtfp_intro (float_plus_infinity (:'t # 'w)) = smtfp_pinf /\
  smtfp_intro (float_minus_infinity (:'t # 'w)) = smtfp_ninf /\
  (!op. smtfp_intro (float_some_qnan op) =
        (smtfp_nan : ('t,'w) smtfp))
Proof
  simp [smtfp_intro_def, smtfp_pzero_def, smtfp_nzero_def,
        smtfp_pinf_def, smtfp_ninf_def, smtfp_nan_def,
        binary_ieeeTheory.some_nan_properties, canon_def]
QED

Theorem native_float_classification_transfer:
  (float_is_nan x <=> smtfp_is_nan (smtfp_intro x)) /\
  (float_is_infinite x <=> smtfp_is_infinite (smtfp_intro x)) /\
  (float_is_normal x <=> smtfp_is_normal (smtfp_intro x)) /\
  (float_is_subnormal x <=> smtfp_is_subnormal (smtfp_intro x)) /\
  (float_is_zero x <=> smtfp_is_zero (smtfp_intro x))
Proof
  Cases_on `float_is_nan x` >>
  simp [canon_def, smtfp_is_nan_def, smtfp_is_infinite_def,
        smtfp_is_normal_def, smtfp_is_subnormal_def,
        smtfp_is_zero_def] >>
  metis_tac [binary_ieeeTheory.float_is_distinct,
              float_canon_qnan_is_nan]
QED

Theorem native_float_sign_transfer:
  ((~float_is_nan x /\ x.Sign = 1w) <=>
     smtfp_is_negative (smtfp_intro x)) /\
  ((~float_is_nan x /\ x.Sign = 0w) <=>
     smtfp_is_positive (smtfp_intro x))
Proof
  Cases_on `float_is_nan x` >>
  simp [canon_def, smtfp_is_negative_def, smtfp_is_positive_def]
QED

Theorem float_is_nan_abs[simp]:
  float_is_nan (float_abs x) <=> float_is_nan x
Proof
  Cases_on `x` >>
  simp [binary_ieeeTheory.float_abs_def,
        binary_ieeeTheory.float_is_nan_def,
        binary_ieeeTheory.float_value_def] >>
  rpt COND_CASES_TAC >> simp []
QED

Theorem float_is_nan_negate[simp]:
  float_is_nan (float_negate x) <=> float_is_nan x
Proof
  Cases_on `x` >>
  simp [binary_ieeeTheory.float_negate_def,
        binary_ieeeTheory.float_is_nan_def,
        binary_ieeeTheory.float_value_def] >>
  rpt COND_CASES_TAC >> simp []
QED

Theorem native_float_abs_transfer:
  smtfp_intro (float_abs x) = smtfp_abs (smtfp_intro x)
Proof
  simp [smtfp_intro_def, smtfp_abs_def, smtfp_rep_def] >>
  Cases_on `float_is_nan x` >> simp [canon_def]
QED

Theorem native_float_neg_transfer:
  smtfp_intro (float_negate x) = smtfp_neg (smtfp_intro x)
Proof
  simp [smtfp_intro_def, smtfp_neg_def, smtfp_rep_def] >>
  Cases_on `float_is_nan x` >> simp [canon_def]
QED

Theorem native_float_comparison_transfer:
  (float_less_than x y <=>
     smtfp_lt (smtfp_intro x) (smtfp_intro y)) /\
  (float_less_equal x y <=>
     smtfp_le (smtfp_intro x) (smtfp_intro y)) /\
  (float_greater_than x y <=>
     smtfp_gt (smtfp_intro x) (smtfp_intro y)) /\
  (float_greater_equal x y <=>
     smtfp_ge (smtfp_intro x) (smtfp_intro y)) /\
  (float_equal x y <=>
     smtfp_eq (smtfp_intro x) (smtfp_intro y)) /\
  (float_unordered x y <=>
     smtfp_is_nan (smtfp_intro x) \/
     smtfp_is_nan (smtfp_intro y))
Proof
  Cases_on `float_value x` >> Cases_on `float_value y` >>
  simp [canon_def, binary_ieeeTheory.float_is_nan_def,
        smtfp_lt_def, smtfp_le_def, smtfp_gt_def, smtfp_ge_def,
        smtfp_eq_def, smtfp_unordered_def, smtfp_is_nan_def,
        binary_ieeeTheory.float_less_than_def,
        binary_ieeeTheory.float_less_equal_def,
        binary_ieeeTheory.float_greater_than_def,
        binary_ieeeTheory.float_greater_equal_def,
        binary_ieeeTheory.float_equal_def,
        binary_ieeeTheory.float_unordered_def,
        binary_ieeeTheory.float_compare_def] >>
  rpt COND_CASES_TAC >> simp []
QED

Theorem native_float_add_transfer:
  smtfp_intro (SND (float_add mode x y)) =
    smtfp_add (smtfp_rounding_of_binary mode)
      (smtfp_intro x) (smtfp_intro y)
Proof
  simp [smtfp_intro_def, smtfp_add_def, smtfp_rep_def,
        smt_float_add_def] >>
  Cases_on `float_value x` >> Cases_on `float_value y` >>
  simp [canon_def, binary_ieeeTheory.float_is_nan_def,
        binary_ieeeTheory.float_add_def,
        binary_ieeeTheory.some_nan_properties]
QED

Theorem native_float_sub_transfer:
  smtfp_intro (SND (float_sub mode x y)) =
    smtfp_sub (smtfp_rounding_of_binary mode)
      (smtfp_intro x) (smtfp_intro y)
Proof
  simp [smtfp_intro_def, smtfp_sub_def, smtfp_rep_def,
        smt_float_sub_def] >>
  Cases_on `float_value x` >> Cases_on `float_value y` >>
  simp [canon_def, binary_ieeeTheory.float_is_nan_def,
        binary_ieeeTheory.float_sub_def,
        binary_ieeeTheory.some_nan_properties]
QED

Theorem native_float_mul_transfer:
  smtfp_intro (SND (float_mul mode x y)) =
    smtfp_mul (smtfp_rounding_of_binary mode)
      (smtfp_intro x) (smtfp_intro y)
Proof
  simp [smtfp_intro_def, smtfp_mul_def, smtfp_rep_def,
        smt_float_mul_def] >>
  Cases_on `float_value x` >> Cases_on `float_value y` >>
  simp [canon_def, binary_ieeeTheory.float_is_nan_def,
        binary_ieeeTheory.float_mul_def,
        binary_ieeeTheory.some_nan_properties]
QED

Theorem native_float_div_transfer:
  smtfp_intro (SND (float_div mode x y)) =
    smtfp_div (smtfp_rounding_of_binary mode)
      (smtfp_intro x) (smtfp_intro y)
Proof
  simp [smtfp_intro_def, smtfp_div_def, smtfp_rep_def,
        smt_float_div_def] >>
  Cases_on `float_value x` >> Cases_on `float_value y` >>
  simp [canon_def, binary_ieeeTheory.float_is_nan_def,
        binary_ieeeTheory.float_div_def,
        binary_ieeeTheory.some_nan_properties]
QED

Theorem float_sqrt_nan:
  float_is_nan x ==> float_is_nan (SND (float_sqrt mode x))
Proof
  rw [binary_ieeeTheory.float_sqrt_def] >>
  Cases_on `x.Sign = 0w` >> fs [] >>
  fs [binary_ieeeTheory.float_is_nan_def] >>
  Cases_on `float_value x` >> fs []
QED

Theorem native_float_sqrt_transfer:
  smtfp_intro (SND (float_sqrt mode x)) =
    smtfp_sqrt (smtfp_rounding_of_binary mode) (smtfp_intro x)
Proof
  simp [smtfp_intro_def, smtfp_sqrt_def, smtfp_rep_def,
        smt_float_sqrt_def] >>
  Cases_on `float_is_nan x` >> simp [canon_def, float_sqrt_nan] >>
  fs []
QED

Theorem native_float_fma_transfer:
  smtfp_intro (SND (float_mul_add mode x y z)) =
    smtfp_fma (smtfp_rounding_of_binary mode)
      (smtfp_intro x) (smtfp_intro y) (smtfp_intro z)
Proof
  simp [smtfp_intro_def, smtfp_fma_def, smtfp_rep_def,
        smt_float_fma_def] >>
  Cases_on `float_is_nan x` >> Cases_on `float_is_nan y` >>
  Cases_on `float_is_nan z` >> simp [canon_def] >>
  simp [binary_ieeeTheory.float_mul_add_def,
        binary_ieeeTheory.some_nan_properties]
QED

(* Invalid raw record equality is deliberately absent: smtfp_intro identifies
   all NaN payloads, so no injectivity theorem can soundly join this kit. *)

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

Theorem smtfp_bits_rep[simp]:
  smtfp_bits (smtfp_rep x).Sign (smtfp_rep x).Exponent
    (smtfp_rep x).Significand = x
Proof
  `<| Sign := (smtfp_rep x).Sign;
       Exponent := (smtfp_rep x).Exponent;
       Significand := (smtfp_rep x).Significand |> = smtfp_rep x` by
    simp [binary_ieeeTheory.float_component_equality] >>
  simp [smtfp_bits_def]
QED

(* Expose the exact field layout used by fpa2bv decompositions.  Keeping this
   as a boundary theorem means replay does not need to unfold either the
   carrier or the IEEE interchange unpacker. *)
Theorem smtfp_from_ieee_bv_fields:
  FINITE (UNIV : 'w -> bool) /\ FINITE (UNIV : 't -> bool) ==>
  !v : (1 + ('w + 't)) word.
    smtfp_from_ieee_bv v =
      smtfp_bits
        ((dimindex(:'w) + dimindex(:'t) ><
          dimindex(:'w) + dimindex(:'t)) v)
        ((dimindex(:'w) + dimindex(:'t) - 1 >< dimindex(:'t)) v)
        ((dimindex(:'t) - 1 >< 0) v)
Proof
  strip_tac >> gen_tac >> fs [] >>
  `0 < dimindex(:'w)` by simp [wordsTheory.DIMINDEX_GT_0] >>
  `0 < dimindex(:'t)` by simp [wordsTheory.DIMINDEX_GT_0] >>
  rw [smtfp_from_ieee_bv_def, float_from_ieee_bv_def,
      smtfp_bits_def] >>
  asm_simp_tac (srw_ss() ++ ARITH_ss ++ wordsLib.WORD_EXTRACT_ss)
    [arithmeticTheory.MIN_DEF, wordsTheory.word_index,
     wordsTheory.DIMINDEX_GT_0, fcpTheory.finite_sum,
     fcpTheory.index_sum]
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

Theorem smtfp_bits_pack_ieee_bv:
  FINITE (UNIV : 'w -> bool) /\ FINITE (UNIV : 't -> bool) ==>
  !x : ('t,'w) smtfp.
    x = smtfp_bits
      ((dimindex(:'w) + dimindex(:'t) ><
        dimindex(:'w) + dimindex(:'t)) (smtfp_pack_ieee_bv x))
      ((dimindex(:'w) + dimindex(:'t) - 1 >< dimindex(:'t))
        (smtfp_pack_ieee_bv x))
      ((dimindex(:'t) - 1 >< 0) (smtfp_pack_ieee_bv x))
Proof
  strip_tac >> gen_tac >>
  simp [GSYM smtfp_from_ieee_bv_fields,
        smtfp_ieee_bv_unpack_pack]
QED

Theorem smtfp_bits_pack_bv:
  FINITE (UNIV : 'p -> bool) /\ FINITE (UNIV : 'w -> bool) /\
  FINITE (UNIV : 't -> bool) /\
  dimindex(:'p) = 1 + dimindex(:'w) + dimindex(:'t) ==>
  !x : ('t,'w) smtfp.
    x = smtfp_bits
      ((dimindex(:'w) + dimindex(:'t) ><
        dimindex(:'w) + dimindex(:'t))
        (smtfp_pack_bv x : 'p word))
      ((dimindex(:'w) + dimindex(:'t) - 1 >< dimindex(:'t))
        (smtfp_pack_bv x : 'p word))
      ((dimindex(:'t) - 1 >< 0) (smtfp_pack_bv x : 'p word))
Proof
  strip_tac >> gen_tac >> fs [] >>
  `0 < dimindex(:'w)` by simp [wordsTheory.DIMINDEX_GT_0] >>
  `0 < dimindex(:'t)` by simp [wordsTheory.DIMINDEX_GT_0] >>
  rw [smtfp_pack_bv_def] >>
  asm_simp_tac (srw_ss() ++ ARITH_ss ++ wordsLib.WORD_EXTRACT_ss)
    [arithmeticTheory.MIN_DEF, wordsTheory.word_index,
     wordsTheory.DIMINDEX_GT_0, fcpTheory.finite_sum,
     fcpTheory.index_sum]
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

(* Proforma forms for the literal-normalization rewrites in the Phase-5
   proof corpora.  Variables are retained in the triples so the replay net
   can match numeral spellings first and discharge these ground side
   conditions afterwards. *)
Theorem smtfp_bits_pzero:
  s = 0w /\ e = 0w /\ m = 0w ==>
  smtfp_bits s e m = (smtfp_pzero : ('t,'w) smtfp)
Proof
  simp [smtfp_bits_def, smtfp_pzero_def, canon_def,
        smtfp_nan_pattern_def, binary_ieeeTheory.float_plus_zero_def]
QED

Theorem smtfp_pzero_bits:
  s = 0w /\ e = 0w /\ m = 0w ==>
  (smtfp_pzero : ('t,'w) smtfp) = smtfp_bits s e m
Proof
  metis_tac [smtfp_bits_pzero]
QED

Theorem smtfp_bits_nzero:
  s = 1w /\ e = 0w /\ m = 0w ==>
  smtfp_bits s e m = (smtfp_nzero : ('t,'w) smtfp)
Proof
  simp [smtfp_bits_def, smtfp_nzero_def, canon_def,
        smtfp_nan_pattern_def, binary_ieeeTheory.float_minus_zero_def,
        binary_ieeeTheory.float_plus_zero_def,
        binary_ieeeTheory.float_negate_def] >>
  wordsLib.WORD_DECIDE_TAC
QED

Theorem smtfp_nzero_bits:
  s = 1w /\ e = 0w /\ m = 0w ==>
  (smtfp_nzero : ('t,'w) smtfp) = smtfp_bits s e m
Proof
  metis_tac [smtfp_bits_nzero]
QED

Theorem smtfp_bits_pinf:
  s = 0w /\ e = UINT_MAXw /\ m = 0w ==>
  smtfp_bits s e m = (smtfp_pinf : ('t,'w) smtfp)
Proof
  simp [smtfp_bits_def, smtfp_pinf_def, canon_def,
        smtfp_nan_pattern_def,
        binary_ieeeTheory.float_plus_infinity_def]
QED

Theorem smtfp_pinf_bits:
  s = 0w /\ e = UINT_MAXw /\ m = 0w ==>
  (smtfp_pinf : ('t,'w) smtfp) = smtfp_bits s e m
Proof
  metis_tac [smtfp_bits_pinf]
QED

Theorem smtfp_bits_ninf:
  s = 1w /\ e = UINT_MAXw /\ m = 0w ==>
  smtfp_bits s e m = (smtfp_ninf : ('t,'w) smtfp)
Proof
  simp [smtfp_bits_def, smtfp_ninf_def, canon_def,
        smtfp_nan_pattern_def,
        binary_ieeeTheory.float_minus_infinity_def,
        binary_ieeeTheory.float_plus_infinity_def,
        binary_ieeeTheory.float_negate_def] >>
  wordsLib.WORD_DECIDE_TAC
QED

Theorem smtfp_ninf_bits:
  s = 1w /\ e = UINT_MAXw /\ m = 0w ==>
  (smtfp_ninf : ('t,'w) smtfp) = smtfp_bits s e m
Proof
  metis_tac [smtfp_bits_ninf]
QED

Theorem smtfp_nan_bits:
  e = UINT_MAXw /\ m <> 0w ==>
  (smtfp_nan : ('t,'w) smtfp) = smtfp_bits s e m
Proof
  metis_tac [smtfp_bits_nan]
QED

Theorem smtfp_is_nan_bits:
  smtfp_is_nan (smtfp_bits s e m : ('t,'w) smtfp) <=>
  smtfp_nan_pattern e m
Proof
  rewrite_tac [smtfp_is_nan_def] >>
  `smtfp_rep (smtfp_bits s e m : ('t,'w) smtfp) =
   canon <| Sign := s; Exponent := e; Significand := m |>` by
    simp [smtfp_bits_def] >>
  pop_assum (rewrite_tac o single) >>
  Cases_on `smtfp_nan_pattern e m` >> simp [canon_def] >> fs []
QED

(* Equality rewrites and the fp.eq boundary observed around symbolic
   comparison atoms.  Unlike HOL equality, fp.eq is false on NaN and treats
   the two signed zero encodings as equal. *)
Theorem smtfp_equality_refl:
  (x : ('t,'w) smtfp) = x
Proof
  simp []
QED

Theorem smtfp_equality_symm:
  (x : ('t,'w) smtfp) = y ==> y = x
Proof
  simp []
QED

Theorem smtfp_eq_refl:
  smtfp_eq x x <=> ~smtfp_is_nan x
Proof
  simp [smtfp_eq_def, smtfp_is_nan_def,
        binary_ieeeTheory.float_is_nan_impl]
QED

Theorem smtfp_eq_of_equality:
  (x : ('t,'w) smtfp) = y ==>
  (smtfp_eq x y <=> ~smtfp_is_nan x)
Proof
  simp [smtfp_eq_refl]
QED

Theorem smtfp_eq_signed_zero:
  smtfp_eq (smtfp_pzero : ('t,'w) smtfp) smtfp_nzero
Proof
  simp [smtfp_eq_def, smtfp_pzero_def, smtfp_nzero_def] >>
  simp [canon_def, GSYM binary_ieeeTheory.float_is_zero_impl]
QED

Theorem smt_rounding_refl:
  (mode : smt_rounding) = mode
Proof
  simp []
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

(* -------------------------------------------------------------------------
   Tier-2 word correspondence

   These formulas are deliberately stated on [smtfp_bits].  Consequently
   their right-hand sides contain only words and Booleans and can be handed
   directly to the existing bit-vector simplifier and bit-blaster.
   ------------------------------------------------------------------------- *)

Definition smtfp_mag_lt_def:
  smtfp_mag_lt (e : 'w word) (m : 't word) e' m' <=>
    e <+ e' \/ (e = e' /\ m <+ m')
End

Definition smtfp_word_equal_def:
  smtfp_word_equal (s : word1) (e : 'w word) (m : 't word)
                   s' e' m' <=>
    smtfp_nan_pattern e m /\ smtfp_nan_pattern e' m' \/
    ~smtfp_nan_pattern e m /\ ~smtfp_nan_pattern e' m' /\
    s = s' /\ e = e' /\ m = m'
End

Definition smtfp_word_fp_eq_def:
  smtfp_word_fp_eq (s : word1) (e : 'w word) (m : 't word)
                   s' e' m' <=>
    ~smtfp_nan_pattern e m /\ ~smtfp_nan_pattern e' m' /\
    ((e = 0w /\ m = 0w /\ e' = 0w /\ m' = 0w) \/
     (s = s' /\ e = e' /\ m = m'))
End

Definition smtfp_word_lt_def:
  smtfp_word_lt (s : word1) (e : 'w word) (m : 't word)
                s' e' m' <=>
    ~smtfp_nan_pattern e m /\ ~smtfp_nan_pattern e' m' /\
    if s = s' then
      if s = 0w then smtfp_mag_lt e m e' m'
      else smtfp_mag_lt e' m' e m
    else
      s = 1w /\ ~(e = 0w /\ m = 0w /\ e' = 0w /\ m' = 0w)
End

Theorem smtfp_rep_bits[simp]:
  smtfp_rep (smtfp_bits s e m : ('t,'w) smtfp) =
  canon <| Sign := s; Exponent := e; Significand := m |>
Proof
  simp [smtfp_bits_def]
QED

Theorem smtfp_is_normal_bits:
  smtfp_is_normal (smtfp_bits s e m : ('t,'w) smtfp) <=>
  e <> 0w /\ e <> UINT_MAXw
Proof
  Cases_on `smtfp_nan_pattern e m` >>
  simp [smtfp_is_normal_def, canon_def,
        smtfp_nan_pattern_def,
        binary_ieeeTheory.float_is_normal_def,
        float_canon_qnan_def] >> fs [smtfp_nan_pattern_def]
QED

Theorem smtfp_is_subnormal_bits:
  smtfp_is_subnormal (smtfp_bits s e m : ('t,'w) smtfp) <=>
  e = 0w /\ m <> 0w
Proof
  Cases_on `smtfp_nan_pattern e m` >>
  simp [smtfp_is_subnormal_def, canon_def,
        smtfp_nan_pattern_def,
        binary_ieeeTheory.float_is_subnormal_def,
        float_canon_qnan_def] >> fs [smtfp_nan_pattern_def]
QED

Theorem smtfp_is_zero_bits:
  smtfp_is_zero (smtfp_bits s e m : ('t,'w) smtfp) <=>
  e = 0w /\ m = 0w
Proof
  Cases_on `smtfp_nan_pattern e m` >>
  simp [smtfp_is_zero_def, canon_def,
        smtfp_nan_pattern_def, binary_ieeeTheory.float_is_zero,
        float_canon_qnan_def] >> fs [smtfp_nan_pattern_def]
QED

Theorem float_canon_qnan_significand_nonzero[simp]:
  (1w #>> 1 <> 0w : 't word)
Proof
  mp_tac (INST_TYPE [alpha |-> ``:'t``, beta |-> ``:'w``]
    float_canon_qnan_is_nan) >>
  rewrite_tac [float_canon_qnan_def, float_bits_is_nan] >>
  simp [smtfp_nan_pattern_def]
QED

Theorem smtfp_is_infinite_bits:
  smtfp_is_infinite (smtfp_bits s e m : ('t,'w) smtfp) <=>
  e = UINT_MAXw /\ m = 0w
Proof
  Cases_on `smtfp_nan_pattern e m` >>
  simp [smtfp_is_infinite_def, canon_def,
        smtfp_nan_pattern_def, cj 3 binary_ieeeTheory.float_tests,
        float_canon_qnan_def] >>
  fs [smtfp_nan_pattern_def]
QED

Theorem smtfp_is_negative_bits:
  smtfp_is_negative (smtfp_bits s e m : ('t,'w) smtfp) <=>
  ~smtfp_nan_pattern e m /\ s = 1w
Proof
  Cases_on `smtfp_nan_pattern e m` >>
  simp [smtfp_is_negative_def, canon_def,
        smtfp_nan_pattern_def, float_canon_qnan_def] >>
  fs [smtfp_nan_pattern_def]
QED

Theorem smtfp_is_positive_bits:
  smtfp_is_positive (smtfp_bits s e m : ('t,'w) smtfp) <=>
  ~smtfp_nan_pattern e m /\ s = 0w
Proof
  Cases_on `smtfp_nan_pattern e m` >>
  simp [smtfp_is_positive_def, canon_def,
        smtfp_nan_pattern_def, float_canon_qnan_def] >>
  fs [smtfp_nan_pattern_def]
QED

Theorem smtfp_abs_bits:
  smtfp_abs (smtfp_bits s e m : ('t,'w) smtfp) =
  smtfp_bits 0w e m
Proof
  Cases_on `smtfp_nan_pattern e m` >>
  simp [smtfp_abs_def, smtfp_bits_def, canon_def,
        smtfp_nan_pattern_def, binary_ieeeTheory.float_abs_def,
        float_canon_qnan_def]
QED

Theorem smtfp_neg_bits:
  smtfp_neg (smtfp_bits s e m : ('t,'w) smtfp) =
  smtfp_bits (~s) e m
Proof
  Cases_on `smtfp_nan_pattern e m` >>
  simp [smtfp_neg_def, smtfp_bits_def, canon_def,
        smtfp_nan_pattern_def, binary_ieeeTheory.float_negate_def,
        float_canon_qnan_def]
QED

Theorem smtfp_neg_neg[simp]:
  smtfp_neg (smtfp_neg x) = x
Proof
  qspec_then `x` strip_assume_tac smtfp_bits_surjective >>
  fs [smtfp_neg_bits]
QED

Theorem smtfp_abs_abs[simp]:
  smtfp_abs (smtfp_abs x) = smtfp_abs x
Proof
  qspec_then `x` strip_assume_tac smtfp_bits_surjective >>
  fs [smtfp_abs_bits]
QED

Theorem smtfp_abs_neg[simp]:
  smtfp_abs (smtfp_neg x) = smtfp_abs x
Proof
  qspec_then `x` strip_assume_tac smtfp_bits_surjective >>
  fs [smtfp_abs_bits, smtfp_neg_bits]
QED

Theorem smtfp_bits_eq_nan:
  smtfp_nan_pattern e m /\ smtfp_nan_pattern e' m' ==>
  (smtfp_bits s e m : ('t,'w) smtfp) = smtfp_bits s' e' m'
Proof
  strip_tac >>
  `smtfp_bits s e m = (smtfp_nan : ('t,'w) smtfp)` by
    (irule smtfp_bits_nan >> fs [smtfp_nan_pattern_def]) >>
  `smtfp_bits s' e' m' = (smtfp_nan : ('t,'w) smtfp)` by
    (irule smtfp_bits_nan >> fs [smtfp_nan_pattern_def]) >>
  simp []
QED

Theorem smtfp_bits_neq_nan_left:
  smtfp_nan_pattern e m /\ ~smtfp_nan_pattern e' m' ==>
  (smtfp_bits s e m : ('t,'w) smtfp) <> smtfp_bits s' e' m'
Proof
  strip_tac >> strip_tac >>
  qpat_x_assum `_ = _`
    (mp_tac o AP_TERM
      ``smtfp_is_nan : ('t,'w) smtfp -> bool``) >>
  simp [smtfp_is_nan_bits]
QED

Theorem smtfp_bits_neq_nan_right:
  ~smtfp_nan_pattern e m /\ smtfp_nan_pattern e' m' ==>
  (smtfp_bits s e m : ('t,'w) smtfp) <> smtfp_bits s' e' m'
Proof
  metis_tac [smtfp_bits_neq_nan_left]
QED

Theorem smtfp_equality_bits:
  ((smtfp_bits s e m : ('t,'w) smtfp) = smtfp_bits s' e' m') <=>
  smtfp_word_equal s e m s' e' m'
Proof
  Cases_on `smtfp_nan_pattern e m` >>
  Cases_on `smtfp_nan_pattern e' m'` >>
  simp [smtfp_word_equal_def, smtfp_bits_eq_nan,
        smtfp_bits_neq_nan_left, smtfp_bits_neq_nan_right,
        smtfp_bits_11_non_nan]
QED

Theorem float_equal_components:
  float_equal (x : ('t,'w) float) y <=>
  ~float_is_nan x /\ ~float_is_nan y /\
  (float_is_zero x /\ float_is_zero y \/ x = y)
Proof
  rw [binary_ieeeTheory.float_equal_def,
      binary_ieeeTheory.float_is_nan_def,
      binary_ieeeTheory.float_is_zero_def] >>
  Cases_on `float_value x` >> Cases_on `float_value y` >>
  gvs [binary_ieeeTheory.float_compare_def,
       binary_ieeeTheory.float_value_def,
       binary_ieeeTheory.float_to_real_eq,
       binary_ieeeTheory.float_component_equality, AllCaseEqs()] >>
  simp [GSYM binary_ieeeTheory.float_is_zero_to_real,
        GSYM binary_ieeeTheory.float_component_equality,
        binary_ieeeTheory.float_to_real_eq] >>
  `(float_is_zero x /\ float_is_zero y \/ x = y) ==>
   float_to_real x = float_to_real y` by
    metis_tac [binary_ieeeTheory.float_to_real_eq] >>
  metis_tac [realTheory.REAL_LT_REFL]
QED

Theorem smtfp_eq_bits:
  smtfp_eq (smtfp_bits s e m : ('t,'w) smtfp)
    (smtfp_bits s' e' m') <=>
  smtfp_word_fp_eq s e m s' e' m'
Proof
  rewrite_tac [smtfp_eq_def, float_equal_components] >>
  rewrite_tac [GSYM smtfp_is_nan_def, GSYM smtfp_is_zero_def] >>
  simp [smtfp_is_nan_bits, smtfp_is_zero_bits,
        smtfp_equality_bits, smtfp_word_fp_eq_def,
        smtfp_word_equal_def] >>
  tautLib.TAUT_TAC
QED

Theorem smtfp_positive_real_nonnegative:
  0 <= float_to_real
    (<| Sign := 0w; Exponent := e; Significand := m |> : ('t,'w) float)
Proof
  rw [binary_ieeeTheory.float_to_real_def] >>
  simp [realTheory.REAL_LE_MUL, realTheory.REAL_LE_ADD]
QED

Theorem smtfp_positive_real_zero:
  (float_to_real
     (<| Sign := 0w; Exponent := e; Significand := m |> :
      ('t,'w) float) = 0) <=>
  e = 0w /\ m = 0w
Proof
  rewrite_tac [GSYM binary_ieeeTheory.float_is_zero_to_real] >>
  simp [binary_ieeeTheory.float_is_zero]
QED

Theorem smtfp_positive_same_exponent_lt:
  float_to_real
    (<| Sign := 0w; Exponent := e; Significand := m |> :
     ('t,'w) float) <
  float_to_real
    (<| Sign := 0w; Exponent := e; Significand := m' |> :
     ('t,'w) float) <=>
  m <+ m'
Proof
  Cases_on `e` >> Cases_on `m` >> Cases_on `m'` >>
  Cases_on `n = 0` >>
  simp [binary_ieeeTheory.float_to_real_def,
        wordsTheory.word_lo_n2w, wordsTheory.dimword_def,
        realTheory.REAL_LT_LMUL, realTheory.REAL_LT_RMUL,
        realTheory.REAL_LT_LDIV_EQ]
QED

Theorem smtfp_positive_exponent_monotone:
  float_to_real
    (<| Sign := 0w; Exponent := e; Significand := m |> :
     ('t,'w) float) <
  float_to_real
    (<| Sign := 0w; Exponent := e'; Significand := m' |> :
     ('t,'w) float) ==>
  e <=+ e'
Proof
  strip_tac >>
  `abs (float_to_real
      (<| Sign := 0w; Exponent := e; Significand := m |> :
       ('t,'w) float)) <
   abs (float_to_real
      (<| Sign := 0w; Exponent := e'; Significand := m' |> :
       ('t,'w) float))` by
    simp [realTheory.abs, smtfp_positive_real_nonnegative] >>
  qpat_x_assum `abs _ < abs _`
    (ACCEPT_TAC o SIMP_RULE (srw_ss()) [] o
     MATCH_MP binary_ieeeTheory.Exponent_monotone)
QED

Theorem smtfp_positive_mag_lt_forward:
  float_to_real
    (<| Sign := 0w; Exponent := e; Significand := m |> :
     ('t,'w) float) <
  float_to_real
    (<| Sign := 0w; Exponent := e'; Significand := m' |> :
     ('t,'w) float) ==>
  smtfp_mag_lt e m e' m'
Proof
  strip_tac >>
  `e <=+ e'` by metis_tac [smtfp_positive_exponent_monotone] >>
  fs [smtfp_mag_lt_def, wordsTheory.WORD_LOWER_OR_EQ] >>
  metis_tac [smtfp_positive_same_exponent_lt]
QED

Theorem smtfp_mag_lt_asym:
  smtfp_mag_lt e m e' m' ==> ~smtfp_mag_lt e' m' e m
Proof
  rw [smtfp_mag_lt_def] >>
  wordsLib.WORD_DECIDE_TAC
QED

Theorem smtfp_positive_real_eq_not_mag_lt:
  float_to_real
    (<| Sign := 0w; Exponent := e; Significand := m |> :
     ('t,'w) float) =
  float_to_real
    (<| Sign := 0w; Exponent := e'; Significand := m' |> :
     ('t,'w) float) ==>
  ~smtfp_mag_lt e m e' m'
Proof
  strip_tac >>
  fs [binary_ieeeTheory.float_to_real_eq,
      binary_ieeeTheory.float_component_equality,
      binary_ieeeTheory.float_is_zero, smtfp_mag_lt_def] >>
  wordsLib.WORD_DECIDE_TAC
QED

Theorem smtfp_positive_mag_lt_backward:
  smtfp_mag_lt e m e' m' ==>
  float_to_real
    (<| Sign := 0w; Exponent := e; Significand := m |> :
     ('t,'w) float) <
  float_to_real
    (<| Sign := 0w; Exponent := e'; Significand := m' |> :
     ('t,'w) float)
Proof
  metis_tac [smtfp_positive_mag_lt_forward, smtfp_mag_lt_asym,
             smtfp_positive_real_eq_not_mag_lt,
             realTheory.REAL_LT_TOTAL]
QED

Theorem smtfp_positive_mag_lt:
  float_to_real
    (<| Sign := 0w; Exponent := e; Significand := m |> :
     ('t,'w) float) <
  float_to_real
    (<| Sign := 0w; Exponent := e'; Significand := m' |> :
     ('t,'w) float) <=>
  smtfp_mag_lt e m e' m'
Proof
  metis_tac [smtfp_positive_mag_lt_forward,
             smtfp_positive_mag_lt_backward]
QED

Theorem float_to_real_bits_sign:
  float_to_real
    (<| Sign := s; Exponent := e; Significand := m |> :
     ('t,'w) float) =
  if s = 0w then
    float_to_real
      (<| Sign := 0w; Exponent := e; Significand := m |> :
       ('t,'w) float)
  else
    -float_to_real
      (<| Sign := 0w; Exponent := e; Significand := m |> :
       ('t,'w) float)
Proof
  wordsLib.Cases_on_word_value `s` >>
  simp [binary_ieeeTheory.float_to_real_def] >>
  realLib.REAL_ARITH_TAC
QED

Theorem float_to_real_negative_bits:
  float_to_real
    (<| Sign := 1w; Exponent := e; Significand := m |> :
     ('t,'w) float) =
  -float_to_real
    (<| Sign := 0w; Exponent := e; Significand := m |> :
     ('t,'w) float)
Proof
  simp [binary_ieeeTheory.float_to_real_def] >>
  realLib.REAL_ARITH_TAC
QED

Theorem nonnegative_lt_negative:
  0 <= x /\ 0 <= y ==> ~(x < -y)
Proof
  realLib.REAL_ARITH_TAC
QED

Theorem negative_lt_nonnegative:
  0 <= x /\ 0 <= y ==> (-x < y <=> ~(x = 0 /\ y = 0))
Proof
  realLib.REAL_ARITH_TAC
QED

Theorem smtfp_positive_negative_not_lt:
  ~(
    float_to_real
      (<| Sign := 0w; Exponent := e; Significand := m |> :
       ('t,'w) float) <
    float_to_real
      (<| Sign := 1w; Exponent := e'; Significand := m' |> :
       ('t,'w) float))
Proof
  rewrite_tac [float_to_real_negative_bits] >>
  irule nonnegative_lt_negative >>
  simp [smtfp_positive_real_nonnegative]
QED

Theorem smtfp_negative_positive_lt:
  float_to_real
    (<| Sign := 1w; Exponent := e; Significand := m |> :
     ('t,'w) float) <
  float_to_real
    (<| Sign := 0w; Exponent := e'; Significand := m' |> :
     ('t,'w) float) <=>
  ~(e = 0w /\ m = 0w /\ e' = 0w /\ m' = 0w)
Proof
  rewrite_tac [float_to_real_negative_bits] >>
  `(-float_to_real
       (<| Sign := 0w; Exponent := e; Significand := m |> :
        ('t,'w) float) <
     float_to_real
       (<| Sign := 0w; Exponent := e'; Significand := m' |> :
        ('t,'w) float) <=>
     ~(float_to_real
         (<| Sign := 0w; Exponent := e; Significand := m |> :
          ('t,'w) float) = 0 /\
       float_to_real
         (<| Sign := 0w; Exponent := e'; Significand := m' |> :
          ('t,'w) float) = 0))` by
    (irule negative_lt_nonnegative >>
     simp [smtfp_positive_real_nonnegative]) >>
  pop_assum (rewrite_tac o single) >>
  simp [smtfp_positive_real_zero] >>
  tautLib.TAUT_TAC
QED

Theorem smtfp_negative_real_lt:
  float_to_real
    (<| Sign := 1w; Exponent := e; Significand := m |> :
     ('t,'w) float) <
  float_to_real
    (<| Sign := 1w; Exponent := e'; Significand := m' |> :
     ('t,'w) float) <=>
  smtfp_mag_lt e' m' e m
Proof
  rewrite_tac [float_to_real_negative_bits] >>
  simp [realTheory.REAL_LT_NEG, smtfp_positive_mag_lt]
QED

Theorem float_to_real_bits_lt:
  float_to_real
    (<| Sign := s; Exponent := e; Significand := m |> :
     ('t,'w) float) <
  float_to_real
    (<| Sign := s'; Exponent := e'; Significand := m' |> :
     ('t,'w) float) <=>
  if s = s' then
    if s = 0w then smtfp_mag_lt e m e' m'
    else smtfp_mag_lt e' m' e m
  else
    s = 1w /\ ~(e = 0w /\ m = 0w /\ e' = 0w /\ m' = 0w)
Proof
  wordsLib.Cases_on_word_value `s` >>
  wordsLib.Cases_on_word_value `s'` >>
  simp [smtfp_positive_mag_lt, smtfp_positive_negative_not_lt,
        smtfp_negative_positive_lt, smtfp_negative_real_lt]
QED

Theorem float_less_than_bits_raw:
  float_less_than
    (<| Sign := s; Exponent := e; Significand := m |> :
     ('t,'w) float)
    (<| Sign := s'; Exponent := e'; Significand := m' |>) <=>
  ~smtfp_nan_pattern e m /\ ~smtfp_nan_pattern e' m' /\
  if s = s' then
    if s = 0w then smtfp_mag_lt e m e' m'
    else smtfp_mag_lt e' m' e m
  else
    s = 1w /\ ~(e = 0w /\ m = 0w /\ e' = 0w /\ m' = 0w)
Proof
  wordsLib.Cases_on_word_value `s` >>
  wordsLib.Cases_on_word_value `s'` >>
  Cases_on `e = UINT_MAXw` >> Cases_on `m = 0w` >>
  Cases_on `e' = UINT_MAXw` >> Cases_on `m' = 0w` >>
  simp [binary_ieeeTheory.float_less_than_def,
        binary_ieeeTheory.float_compare_def,
        binary_ieeeTheory.float_value_def, smtfp_nan_pattern_def,
        float_to_real_bits_lt, smtfp_mag_lt_def,
        wordsTheory.WORD_LOWER_OR_EQ, AllCaseEqs()] >>
  fs [GSYM wordsTheory.WORD_NEG_1, wordsTheory.WORD_LO_word_T]
QED

Definition smtfp_word_le_def:
  smtfp_word_le (s : word1) (e : 'w word) (m : 't word)
                s' e' m' <=>
    smtfp_word_lt s e m s' e' m' \/
    smtfp_word_fp_eq s e m s' e' m'
End

Definition smtfp_word_gt_def:
  smtfp_word_gt (s : word1) (e : 'w word) (m : 't word)
                s' e' m' <=>
    smtfp_word_lt s' e' m' s e m
End

Definition smtfp_word_ge_def:
  smtfp_word_ge (s : word1) (e : 'w word) (m : 't word)
                s' e' m' <=>
    smtfp_word_le s' e' m' s e m
End

Theorem smtfp_lt_bits:
  smtfp_lt (smtfp_bits s e m : ('t,'w) smtfp)
    (smtfp_bits s' e' m') <=>
  smtfp_word_lt s e m s' e' m'
Proof
  Cases_on `smtfp_nan_pattern e m` >>
  Cases_on `smtfp_nan_pattern e' m'` >>
  simp [smtfp_lt_def, smtfp_word_lt_def, smtfp_rep_bits,
        canon_def, float_less_than_bits_raw, smtfp_nan_pattern_def,
        float_canon_qnan_def]
QED

Theorem smtfp_lt_irrefl[simp]:
  ~smtfp_lt x x
Proof
  Cases_on `float_value (smtfp_rep x)` >>
  simp [smtfp_lt_def, binary_ieeeTheory.float_less_than_def,
        binary_ieeeTheory.float_compare_def]
QED

Theorem float_comparison_duals:
  (float_less_equal x y <=> float_less_than x y \/ float_equal x y) /\
  (float_greater_than x y <=> float_less_than y x) /\
  (float_greater_equal x y <=> float_less_equal y x)
Proof
  rw [binary_ieeeTheory.float_less_equal_def,
      binary_ieeeTheory.float_less_than_def,
      binary_ieeeTheory.float_greater_than_def,
      binary_ieeeTheory.float_greater_equal_def,
      binary_ieeeTheory.float_equal_def] >>
  Cases_on `float_compare x y` >>
  Cases_on `float_compare y x` >>
  gvs [binary_ieeeTheory.float_compare_def, AllCaseEqs()] >>
  TRY (Cases_on `float_value x`) >>
  TRY (Cases_on `float_value y`) >>
  TRY (wordsLib.Cases_on_word_value `x.Sign`) >>
  TRY (wordsLib.Cases_on_word_value `y.Sign`) >>
  gvs [binary_ieeeTheory.float_compare_def, AllCaseEqs()] >>
  TRY realLib.REAL_ASM_ARITH_TAC >>
  wordsLib.WORD_DECIDE_TAC
QED

Theorem smtfp_comparison_duals:
  (smtfp_le x y <=> smtfp_lt x y \/ smtfp_eq x y) /\
  (smtfp_gt x y <=> smtfp_lt y x) /\
  (smtfp_ge x y <=> smtfp_le y x)
Proof
  simp [smtfp_le_def, smtfp_lt_def, smtfp_eq_def,
        smtfp_gt_def, smtfp_ge_def, float_comparison_duals]
QED

Theorem smtfp_le_bits:
  smtfp_le (smtfp_bits s e m : ('t,'w) smtfp)
    (smtfp_bits s' e' m') <=>
  smtfp_word_le s e m s' e' m'
Proof
  rewrite_tac [cj 1 smtfp_comparison_duals, smtfp_lt_bits,
               smtfp_eq_bits, smtfp_word_le_def]
QED

Theorem smtfp_gt_bits:
  smtfp_gt (smtfp_bits s e m : ('t,'w) smtfp)
    (smtfp_bits s' e' m') <=>
  smtfp_word_gt s e m s' e' m'
Proof
  rewrite_tac [cj 2 smtfp_comparison_duals, smtfp_lt_bits,
               smtfp_word_gt_def]
QED

Theorem smtfp_ge_bits:
  smtfp_ge (smtfp_bits s e m : ('t,'w) smtfp)
    (smtfp_bits s' e' m') <=>
  smtfp_word_ge s e m s' e' m'
Proof
  rewrite_tac [cj 3 smtfp_comparison_duals, smtfp_le_bits,
               smtfp_word_ge_def]
QED

(* -------------------------------------------------------------------------
   Tier-3 add/sub reference circuit

   This is an independently computed integer datapath.  A finite operand is
   represented by its integer significand and its effective biased exponent.
   Alignment is exact (the smaller exponent is the common scale), so no
   information is lost before the operate stage.  The encoder normalizes the
   exact magnitude and performs quotient/remainder rounding; [residue] is
   combined guard/round/sticky residue.  In particular, the circuit result
   does not call either semantic add/sub operation or a real-number rounder.
   ------------------------------------------------------------------------- *)

Definition smtfp_circuit_sig_def:
  smtfp_circuit_sig (e : 'w word) (m : 't word) =
    if e = 0w then w2n m else 2 ** dimindex (:'t) + w2n m
End

Definition smtfp_circuit_exp_def:
  smtfp_circuit_exp (e : 'w word) = if e = 0w then 1 else w2n e
End

Theorem smtfp_circuit_exp_positive[simp]:
  0 < smtfp_circuit_exp e
Proof
  Cases_on `e = 0w` >>
  simp [smtfp_circuit_exp_def] >>
  CCONTR_TAC >>
  fs [wordsTheory.w2n_eq_0]
QED

Theorem smtfp_circuit_sig_bound:
  smtfp_circuit_sig e (m : 't word) <
  2 * 2 ** dimindex (:'t)
Proof
  `w2n m < 2 ** dimindex (:'t)` by
    (mp_tac (INST_TYPE [alpha |-> ``:'t``]
       wordsTheory.w2n_lt) >>
     simp [wordsTheory.dimword_def]) >>
  Cases_on `e = 0w`
  >- (simp [smtfp_circuit_sig_def] >>
      irule arithmeticTheory.LESS_LESS_EQ_TRANS >>
      qexists_tac `2 ** dimindex (:'t)` >> simp [])
  >> simp [smtfp_circuit_sig_def]
QED

Theorem smtfp_circuit_sig_mantissa:
  smtfp_circuit_sig f.Exponent f.Significand =
  binary_ieeeProps$mantissa f
Proof
  simp [smtfp_circuit_sig_def,
        binary_ieeePropsTheory.mantissa_def]
QED

Theorem smtfp_circuit_value:
  float_to_real
    (<| Sign := s; Exponent := e; Significand := m |> :
     ('t,'w) float) =
  (-1) pow w2n s * &smtfp_circuit_sig e m *
    (2 pow smtfp_circuit_exp e /
     2 pow (INT_MAX (:'w) + dimindex (:'t)))
Proof
  rewrite_tac [binary_ieeePropsTheory.float_to_real_ulp] >>
  simp [smtfp_circuit_sig_def, smtfp_circuit_exp_def,
        binary_ieeePropsTheory.mantissa_def,
        binary_ieeeTheory.float_ulp_def, binary_ieeeTheory.ULP_def]
QED

Theorem smtfp_circuit_positive_value:
  float_to_real
    (<| Sign := 0w; Exponent := e; Significand := m |> :
     ('t,'w) float) =
  &smtfp_circuit_sig e m *
    (2 pow smtfp_circuit_exp e /
     2 pow (INT_MAX (:'w) + dimindex (:'t)))
Proof
  simp [smtfp_circuit_value]
QED

Theorem smtfp_circuit_align_value:
  scale <= smtfp_circuit_exp e ==>
  float_to_real
    (<| Sign := 0w; Exponent := e; Significand := m |> :
     ('t,'w) float) =
  &(smtfp_circuit_sig e m *
    2 ** (smtfp_circuit_exp e - scale)) *
    (2 pow scale /
     2 pow (INT_MAX (:'w) + dimindex (:'t)))
Proof
  strip_tac >>
  rewrite_tac [smtfp_circuit_positive_value] >>
  `smtfp_circuit_exp e - scale + scale = smtfp_circuit_exp e` by
    decide_tac >>
  first_assum (once_rewrite_tac o single o GSYM) >>
  simp [realTheory.REAL_POW_ADD,
        realTheory.REAL_OF_NUM_MUL,
        realTheory.REAL_OF_NUM_POW,
        realTheory.real_div,
        realTheory.REAL_MUL_ASSOC] >>
  disj2_tac >>
  qpat_assum
    `smtfp_circuit_exp e - scale + scale = smtfp_circuit_exp e`
    (once_rewrite_tac o single o GSYM) >>
  simp [arithmeticTheory.EXP_ADD,
        arithmeticTheory.MULT_COMM]
QED

Definition smtfp_circuit_round_up_def:
  smtfp_circuit_round_up mode (sign : word1) q (residue : num) divisor <=>
    residue <> 0 /\
    case mode of
      RNE => divisor < 2 * residue \/
             divisor = 2 * residue /\ ODD q
    | RNA => divisor <= 2 * residue
    | RTP => sign = 0w
    | RTN => sign = 1w
    | RTZ => F
End

Definition smtfp_circuit_round_def:
  smtfp_circuit_round mode sign q (residue : num) divisor =
    q + if smtfp_circuit_round_up mode sign q residue divisor then 1 else 0
End

Theorem smtfp_circuit_round_exact[simp]:
  smtfp_circuit_round mode sign q 0 divisor = q
Proof
  Cases_on `mode` >>
  simp [smtfp_circuit_round_def, smtfp_circuit_round_up_def]
QED

Theorem smtfp_circuit_round_bounds:
  q <= smtfp_circuit_round mode sign q residue divisor /\
  smtfp_circuit_round mode sign q residue divisor <= q + 1
Proof
  simp [smtfp_circuit_round_def] >>
  Cases_on `smtfp_circuit_round_up mode sign q residue divisor` >>
  simp []
QED

Theorem smtfp_circuit_division:
  magnitude = magnitude DIV (2 ** shift) * 2 ** shift +
              magnitude MOD (2 ** shift) /\
  magnitude MOD (2 ** shift) < 2 ** shift
Proof
  simp [arithmeticTheory.DIVISION]
QED

Definition smtfp_circuit_infinity_def:
  smtfp_circuit_infinity (format : ('t,'w) smtfp) (sign : word1) =
    (smtfp_bits sign UINT_MAXw 0w : ('t,'w) smtfp)
End

Definition smtfp_circuit_top_def:
  smtfp_circuit_top (format : ('t,'w) smtfp) (sign : word1) =
    (smtfp_bits sign (n2w (dimword (:'w) - 2))
      (n2w (2 ** dimindex (:'t) - 1)) : ('t,'w) smtfp)
End

Definition smtfp_circuit_overflow_def:
  smtfp_circuit_overflow mode (format : ('t,'w) smtfp)
      (sign : word1) =
    case mode of
      RNE => smtfp_circuit_infinity format sign
    | RNA => smtfp_circuit_infinity format sign
    | RTP => if sign = 0w then smtfp_circuit_infinity format sign
             else smtfp_circuit_top format sign
    | RTN => if sign = 1w then smtfp_circuit_infinity format sign
             else smtfp_circuit_top format sign
    | RTZ => smtfp_circuit_top format sign
End

(* Keep the normalization arithmetic behind small, named boundaries.  The
   circuit correspondence reasons about each of these quantities separately;
   unfolding the former monolithic encoder obscured those invariants and made
   even definitional simplification unnecessarily expensive. *)
Definition smtfp_circuit_wanted_exponent_def:
  smtfp_circuit_wanted_exponent (fraction_width : num) (scale : num)
      (magnitude : num) =
    MAX 1 (LOG2 magnitude + scale - fraction_width)
End

Definition smtfp_circuit_encoded_exponent_def:
  smtfp_circuit_encoded_exponent (maximum_exponent : num)
      (fraction_width : num) (scale : num) (magnitude : num) =
    MIN maximum_exponent
      (smtfp_circuit_wanted_exponent fraction_width scale magnitude)
End

Definition smtfp_circuit_effective_exponent_def:
  smtfp_circuit_effective_exponent (maximum_exponent : num)
      (fraction_width : num) (scale : num) (magnitude : num) =
    MAX 1
      (smtfp_circuit_encoded_exponent maximum_exponent fraction_width
        scale magnitude)
End

Definition smtfp_circuit_shift_def:
  smtfp_circuit_shift (maximum_exponent : num) (fraction_width : num)
      (scale : num) (magnitude : num) =
    smtfp_circuit_effective_exponent maximum_exponent fraction_width
      scale magnitude - scale
End

Definition smtfp_circuit_divisor_def:
  smtfp_circuit_divisor (maximum_exponent : num) (fraction_width : num)
      (scale : num) (magnitude : num) =
    (2 : num) **
      smtfp_circuit_shift maximum_exponent fraction_width scale magnitude
End

Definition smtfp_circuit_quotient_def:
  smtfp_circuit_quotient (maximum_exponent : num) (fraction_width : num)
      (scale : num) (magnitude : num) =
    let effective_exponent =
      smtfp_circuit_effective_exponent maximum_exponent fraction_width
        scale magnitude in
    let divisor =
      smtfp_circuit_divisor maximum_exponent fraction_width scale
        magnitude in
      if scale <= effective_exponent then magnitude DIV divisor
      else magnitude * (2 : num) ** (scale - effective_exponent)
End

Definition smtfp_circuit_remainder_def:
  smtfp_circuit_remainder (maximum_exponent : num)
      (fraction_width : num) (scale : num) (magnitude : num) =
    let effective_exponent =
      smtfp_circuit_effective_exponent maximum_exponent fraction_width
        scale magnitude in
    let divisor =
      smtfp_circuit_divisor maximum_exponent fraction_width scale
        magnitude in
      if scale <= effective_exponent then magnitude MOD divisor else 0
End

Definition smtfp_circuit_rounded_def:
  smtfp_circuit_rounded mode sign (maximum_exponent : num)
      (fraction_width : num) (scale : num) (magnitude : num) =
    smtfp_circuit_round mode sign
      (smtfp_circuit_quotient maximum_exponent fraction_width scale
        magnitude)
      (smtfp_circuit_remainder maximum_exponent fraction_width scale
        magnitude)
      (smtfp_circuit_divisor maximum_exponent fraction_width scale
        magnitude)
End

Definition smtfp_circuit_pack_def:
  smtfp_circuit_pack mode (format : ('t,'w) smtfp) sign
      (maximum_exponent : num) (fraction_width : num) (exponent : num)
      (rounded : num) =
    if maximum_exponent = 0 then
      if rounded < 2 ** fraction_width then
        smtfp_bits sign 0w (n2w rounded)
      else smtfp_circuit_overflow mode format sign
    else if 2 ** (fraction_width + 1) < rounded then
      smtfp_circuit_overflow mode format sign
    else if rounded = 2 ** (fraction_width + 1) then
      if exponent < maximum_exponent then
        smtfp_bits sign (n2w (exponent + 1)) 0w
      else smtfp_circuit_overflow mode format sign
    else if rounded < 2 ** fraction_width then
      smtfp_bits sign 0w (n2w rounded)
    else
      smtfp_bits sign (n2w exponent)
        (n2w (rounded - 2 ** fraction_width))
End

Definition smtfp_circuit_encode_def:
  smtfp_circuit_encode mode (format : ('t,'w) smtfp)
      (sign : word1) (scale : num) magnitude =
    if magnitude = 0 then
      (smtfp_bits sign 0w 0w : ('t,'w) smtfp)
    else
      let fraction_width = dimindex (:'t) in
      let maximum_exponent = dimword (:'w) - 2 in
      let exponent =
        smtfp_circuit_encoded_exponent maximum_exponent fraction_width
          scale magnitude in
      let rounded =
        smtfp_circuit_rounded mode sign maximum_exponent fraction_width
          scale magnitude in
        smtfp_circuit_pack mode format sign maximum_exponent fraction_width
          exponent rounded
End

Theorem smtfp_circuit_encode_representable:
  2 <= dimindex (:'w) /\ (e : 'w word) <> UINT_MAXw ==>
  smtfp_circuit_encode mode (format : ('t,'w) smtfp) sign
    (smtfp_circuit_exp e) (smtfp_circuit_sig e (m : 't word)) =
  (smtfp_bits sign e m : ('t,'w) smtfp)
Proof
  strip_tac >> Cases_on `e = 0w`
  >- (Cases_on `m = 0w`
      >- simp [smtfp_circuit_encode_def, smtfp_circuit_exp_def,
               smtfp_circuit_sig_def,
               smtfp_circuit_wanted_exponent_def,
               smtfp_circuit_encoded_exponent_def,
               smtfp_circuit_effective_exponent_def,
               smtfp_circuit_shift_def,
               smtfp_circuit_divisor_def,
               smtfp_circuit_quotient_def,
               smtfp_circuit_remainder_def,
               smtfp_circuit_rounded_def,
               smtfp_circuit_pack_def]
      >> imp_res_tac wordsTheory.LOG2_w2n_lt >>
      `2 < dimword (:'w)` by
        (simp [wordsTheory.dimword_def] >>
         irule arithmeticTheory.LESS_LESS_EQ_TRANS >>
         qexists_tac `2 ** 2` >> simp []) >>
      `MAX 1 (LOG2 (w2n m) + 1 - dimindex (:'t)) = 1` by
        (irule (cj 1 arithmeticTheory.MAX_EQ_GE) >> decide_tac) >>
      `1 <= dimword (:'w) - 2` by decide_tac >>
      `w2n m < 2 ** dimindex (:'t)` by
        (mp_tac (INST_TYPE [alpha |-> ``:'t``]
           wordsTheory.w2n_lt) >>
         simp [wordsTheory.dimword_def]) >>
      `w2n m < 2 ** (dimindex (:'t) + 1)` by
        (irule arithmeticTheory.LESS_LESS_EQ_TRANS >>
         qexists_tac `2 ** dimindex (:'t)` >> simp []) >>
      fs [smtfp_circuit_encode_def, smtfp_circuit_exp_def,
          smtfp_circuit_sig_def, arithmeticTheory.MIN_EQ_LE,
          smtfp_circuit_wanted_exponent_def,
          smtfp_circuit_encoded_exponent_def,
          smtfp_circuit_effective_exponent_def,
          smtfp_circuit_shift_def, smtfp_circuit_divisor_def,
          smtfp_circuit_quotient_def, smtfp_circuit_remainder_def,
          smtfp_circuit_rounded_def, smtfp_circuit_pack_def]) >>
  Cases_on `e` >>
  gvs [wordsTheory.dimword_def, wordsTheory.word_T_def,
       wordsTheory.UINT_MAX_def] >>
  `n <= 2 ** dimindex (:'w) - 2` by decide_tac >>
  `w2n m < 2 ** dimindex (:'t)` by
    (mp_tac (INST_TYPE [alpha |-> ``:'t``]
       wordsTheory.w2n_lt) >>
     simp [wordsTheory.dimword_def]) >>
  `LOG2 (2 ** dimindex (:'t) + w2n m) = dimindex (:'t)` by
    (irule bitTheory.LOG2_UNIQUE >>
     simp [arithmeticTheory.EXP] >> decide_tac) >>
  fs [smtfp_circuit_encode_def, smtfp_circuit_exp_def,
      smtfp_circuit_sig_def, wordsTheory.dimword_def,
      arithmeticTheory.MIN_EQ_LE, arithmeticTheory.MAX_EQ_GE,
      arithmeticTheory.EXP, smtfp_circuit_wanted_exponent_def,
      smtfp_circuit_encoded_exponent_def,
      smtfp_circuit_effective_exponent_def,
      smtfp_circuit_shift_def, smtfp_circuit_divisor_def,
      smtfp_circuit_quotient_def, smtfp_circuit_remainder_def,
      smtfp_circuit_rounded_def, smtfp_circuit_pack_def] >>
  `w2n m + 2 ** dimindex (:'t) <
   2 ** (dimindex (:'t) + 1)` by
    (simp [arithmeticTheory.EXP_ADD] >> decide_tac) >>
  fs []
QED

Theorem round_tiesToAway_representable_nonzero:
  2 <= dimindex (:'w) /\
  float_is_finite (f : ('t,'w) float) /\
  float_to_real f <> 0 ==>
  round_tiesToAway (float_to_real f) = f
Proof
  strip_tac >>
  irule round_tiesToAway_from_closest_away >>
  simp [binary_ieeeTheory.is_closest_def, IN_DEF] >>
  `abs (float_to_real f) <= largest (:'t # 'w)` by
    (mp_tac (INST_TYPE [alpha |-> ``:'t``, beta |-> ``:'w``]
       binary_ieeeTheory.abs_float_bounds) >>
     simp []) >>
  mp_tac (INST_TYPE [alpha |-> ``:'t``, beta |-> ``:'w``]
    binary_ieeeTheory.largest_lt_threshold) >>
  simp [binary_ieeeTheory.float_is_zero_to_real] >>
  realLib.REAL_ASM_ARITH_TAC
QED

Theorem smt_float_round_representable_nonzero:
  2 <= dimindex (:'w) /\
  float_is_finite (f : ('t,'w) float) /\
  float_to_real f <> 0 ==>
  smt_float_round mode to_neg (float_to_real f) = f
Proof
  strip_tac >>
  `(smt_round mode (float_to_real f) : ('t,'w) float) = f` by
    (Cases_on `mode`
     >- (simp [smt_round_def] >>
         irule binary_ieeePropsTheory.round_representable_nonzero >>
         simp [])
     >- simp [smt_round_def, round_tiesToAway_representable_nonzero]
     >- (simp [smt_round_def] >>
         irule binary_ieeePropsTheory.round_representable_nonzero >>
         simp [])
     >- (simp [smt_round_def] >>
         irule binary_ieeePropsTheory.round_representable_nonzero >>
         simp [])
     >- (simp [smt_round_def] >>
         irule binary_ieeePropsTheory.round_representable_nonzero >>
         simp [])) >>
  simp [smt_float_round_def,
        binary_ieeeTheory.float_is_zero_to_real]
QED

Theorem smt_float_round_to_neg_nonzero_result:
  smt_float_round mode F r = (output : ('t,'w) float) /\
  ~float_is_zero output ==>
  smt_float_round mode to_neg r = output
Proof
  rw [smt_float_round_def] >>
  Cases_on `float_is_zero (smt_round mode r : ('t,'w) float)` >>
  rw [] >>
  fs [binary_ieeeTheory.zero_properties]
QED

Theorem smtfp_circuit_encode_zero[simp]:
  smtfp_circuit_encode mode format sign scale 0 =
  smtfp_bits sign 0w 0w
Proof
  simp [smtfp_circuit_encode_def, smtfp_circuit_pack_def]
QED

(* Semantic boundary for a normalized positive RTP circuit result.  The
   arithmetic normalization proof supplies the adjacent lower endpoint;
   directed rounding then selects the encoder output. *)
Theorem smt_float_round_RTP_circuit_normalized_in_range:
  let output =
    smtfp_rep
      (smtfp_circuit_encode RTP (format : ('t,'w) smtfp)
        0w scale magnitude) in
  float_is_normal (lo : ('t,'w) float) /\
  float_is_normal output /\
  float_is_finite lo /\ float_is_finite output /\
  ~float_is_zero output /\
  next_hi lo = output /\
  0 <= float_to_real lo /\ float_to_real lo < r /\
  r <= float_to_real output /\
  -largest (:'t # 'w) <= r /\ r <= largest (:'t # 'w) ==>
  smt_float_round RTP F r = output
Proof
  simp_tac pure_ss [LET_THM] >> rw [] >>
  `round roundTowardPositive r = next_hi lo` by
    (irule round_RTP_positive_next_hi >> simp []) >>
  simp [smt_float_round_def, smt_round_def]
QED

Definition smtfp_addsub_trace_def:
  smtfp_addsub_trace subtract (x : ('t,'w) smtfp)
      (y : ('t,'w) smtfp) =
    let xr = smtfp_rep x in
    let yr = smtfp_rep y in
    let x_exponent = smtfp_circuit_exp xr.Exponent in
    let y_exponent = smtfp_circuit_exp yr.Exponent in
    let scale = MIN x_exponent y_exponent in
    let x_aligned = smtfp_circuit_sig xr.Exponent xr.Significand *
      (2 : num) ** (x_exponent - scale) in
    let y_aligned = smtfp_circuit_sig yr.Exponent yr.Significand *
      (2 : num) ** (y_exponent - scale) in
    let y_sign = if subtract then ~yr.Sign else yr.Sign in
    let result_sign =
      if xr.Sign = y_sign \/ y_aligned <= x_aligned then xr.Sign
      else y_sign in
    let magnitude =
      if xr.Sign = y_sign then x_aligned + y_aligned
      else if y_aligned <= x_aligned then x_aligned - y_aligned
      else y_aligned - x_aligned in
      (scale, x_aligned, y_aligned, result_sign, magnitude)
End

Theorem smtfp_circuit_signed_align_value:
  scale <= smtfp_circuit_exp e ==>
  float_to_real
    (<| Sign := s; Exponent := e; Significand := m |> :
     ('t,'w) float) =
  if s = 0w then
    float_to_real
      (<| Sign := 0w; Exponent := e; Significand := m |> :
       ('t,'w) float)
  else
    -float_to_real
      (<| Sign := 0w; Exponent := e; Significand := m |> :
       ('t,'w) float)
Proof
  strip_tac >>
  irule float_to_real_bits_sign
QED

Theorem smtfp_signed_magnitude_add:
  let sign = if (sx : word1) = sy \/ y <= x then sx else sy in
  let magnitude =
    if sx = sy then x + y
    else if y <= x then x - y else y - x
  in
    (if sx = 0w then &x else -&x) +
    (if sy = 0w then &y else -&y) =
    if sign = 0w then &magnitude else -&magnitude
Proof
  wordsLib.Cases_on_word_value `sx` >>
  wordsLib.Cases_on_word_value `sy` >>
  Cases_on `y <= x` >>
  simp [realTheory.REAL_OF_NUM_SUB] >>
  once_rewrite_tac [GSYM realTheory.REAL_NEG_ADD] >>
  simp [] >>
  realLib.REAL_ARITH_TAC
QED

Definition smtfp_addsub_scale_def:
  smtfp_addsub_scale subtract (x : ('t,'w) smtfp) y =
    let (scale, x_aligned, y_aligned, sign, magnitude) =
      smtfp_addsub_trace subtract x y
    in scale
End

Definition smtfp_addsub_magnitude_def:
  smtfp_addsub_magnitude subtract (x : ('t,'w) smtfp) y =
    let (scale, x_aligned, y_aligned, sign, magnitude) =
      smtfp_addsub_trace subtract x y
    in magnitude
End

Definition smtfp_addsub_result_sign_def:
  smtfp_addsub_result_sign subtract (x : ('t,'w) smtfp) y =
    let (scale, x_aligned, y_aligned, sign, magnitude) =
      smtfp_addsub_trace subtract x y
    in sign
End

Theorem smtfp_addsub_scale_positive[simp]:
  0 < smtfp_addsub_scale subtract x y
Proof
  simp [smtfp_addsub_scale_def, smtfp_addsub_trace_def]
QED

Theorem float_to_real_flip_sign:
  float_to_real
    (<| Sign := ~s; Exponent := e; Significand := m |> :
     ('t,'w) float) =
  -float_to_real
    (<| Sign := s; Exponent := e; Significand := m |> :
     ('t,'w) float)
Proof
  `(-1w : word1) = 1w` by wordsLib.WORD_DECIDE_TAC >>
  wordsLib.Cases_on_word_value `s` >>
  simp [float_to_real_negative_bits]
QED

Theorem smtfp_aligned_add_exact:
  scale <= smtfp_circuit_exp ex /\
  scale <= smtfp_circuit_exp ey ==>
  let xa = smtfp_circuit_sig ex mx *
             2 ** (smtfp_circuit_exp ex - scale) in
  let ya = smtfp_circuit_sig ey my *
             2 ** (smtfp_circuit_exp ey - scale) in
  let sign = if sx = sy \/ ya <= xa then sx else sy in
  let magnitude =
    if sx = sy then xa + ya
    else if ya <= xa then xa - ya else ya - xa
  in
    float_to_real
      (<| Sign := sx; Exponent := ex; Significand := mx |> :
       ('t,'w) float) +
    float_to_real
      (<| Sign := sy; Exponent := ey; Significand := my |> :
       ('t,'w) float) =
    (if sign = 0w then &magnitude else -&magnitude) *
      (2 pow scale /
       2 pow (INT_MAX (:'w) + dimindex (:'t)))
Proof
  strip_tac >> rewrite_tac [LET_THM] >>
  `(1w : word1) <> 0w` by wordsLib.WORD_DECIDE_TAC >>
  `float_to_real
     (<| Sign := 0w; Exponent := ex; Significand := mx |> :
      ('t,'w) float) =
   &(smtfp_circuit_sig ex mx *
     2 ** (smtfp_circuit_exp ex - scale)) *
   (2 pow scale /
    2 pow (INT_MAX (:'w) + dimindex (:'t)))` by
    (irule smtfp_circuit_align_value >> simp []) >>
  `float_to_real
     (<| Sign := 0w; Exponent := ey; Significand := my |> :
      ('t,'w) float) =
   &(smtfp_circuit_sig ey my *
     2 ** (smtfp_circuit_exp ey - scale)) *
   (2 pow scale /
    2 pow (INT_MAX (:'w) + dimindex (:'t)))` by
    (irule smtfp_circuit_align_value >> simp []) >>
  `!m n : num. ~(n <= m) ==> m <= n` by decide_tac >>
  wordsLib.Cases_on_word_value `sx` >>
  wordsLib.Cases_on_word_value `sy` >>
  Cases_on
    `smtfp_circuit_sig ey my *
       2 ** (smtfp_circuit_exp ey - scale) <=
     smtfp_circuit_sig ex mx *
       2 ** (smtfp_circuit_exp ex - scale)` >>
  rewrite_tac [float_to_real_negative_bits] >>
  asm_rewrite_tac [] >>
  asm_simp_tac std_ss
    [realTheory.REAL_OF_NUM_ADD,
     realTheory.REAL_OF_NUM_MUL,
     realTheory.REAL_OF_NUM_SUB,
     GSYM realTheory.REAL_NEG_LMUL,
     GSYM realTheory.REAL_ADD_RDISTRIB,
     realTheory.REAL_NEG_ADD,
     arithmeticTheory.MULT_COMM] >>
  rewrite_tac [GSYM realTheory.REAL_OF_NUM_ADD] >>
  RealField.REAL_FIELD_TAC
QED

Theorem smtfp_addsub_trace_exact:
  case smtfp_addsub_trace subtract (x : ('t,'w) smtfp) y of
    (scale, xa, ya, sign, magnitude) =>
      float_to_real (smtfp_rep x) +
        (if subtract then -float_to_real (smtfp_rep y)
         else float_to_real (smtfp_rep y)) =
      (if sign = 0w then &magnitude else -&magnitude) *
        (2 pow scale /
         2 pow (INT_MAX (:'w) + dimindex (:'t)))
Proof
  Cases_on `smtfp_rep x` >> Cases_on `smtfp_rep y` >>
  `(~0w : word1) = 1w` by wordsLib.WORD_DECIDE_TAC >>
  `(~1w : word1) = 0w` by wordsLib.WORD_DECIDE_TAC >>
  `(1w : word1) <> 0w` by wordsLib.WORD_DECIDE_TAC >>
  wordsLib.Cases_on_word_value `c` >>
  wordsLib.Cases_on_word_value `c'` >>
  Cases_on `subtract` >>
  simp_tac pure_ss [smtfp_addsub_trace_def] >>
  asm_rewrite_tac [] >>
  simp_tac bool_ss
    (LET_THM :: pairTheory.pair_case_thm ::
     TypeBase.accessors_of ``:('t,'w) float``) >>
  `float 0w c0 c1 =
   (<| Sign := 0w; Exponent := c0; Significand := c1 |> :
    ('t,'w) float)` by
    simp [binary_ieeeTheory.float_component_equality] >>
  `float 0w c0' c1' =
   (<| Sign := 0w; Exponent := c0'; Significand := c1' |> :
    ('t,'w) float)` by
    simp [binary_ieeeTheory.float_component_equality] >>
  `float_to_real
     (<| Sign := 0w; Exponent := c0; Significand := c1 |> :
      ('t,'w) float) =
   &(smtfp_circuit_sig c0 c1 *
     2 ** (smtfp_circuit_exp c0 -
       MIN (smtfp_circuit_exp c0) (smtfp_circuit_exp c0'))) *
   (2 pow (MIN (smtfp_circuit_exp c0) (smtfp_circuit_exp c0')) /
    2 pow (INT_MAX (:'w) + dimindex (:'t)))` by
    (irule smtfp_circuit_align_value >> simp []) >>
  `float_to_real
     (<| Sign := 0w; Exponent := c0'; Significand := c1' |> :
      ('t,'w) float) =
   &(smtfp_circuit_sig c0' c1' *
     2 ** (smtfp_circuit_exp c0' -
       MIN (smtfp_circuit_exp c0) (smtfp_circuit_exp c0'))) *
   (2 pow (MIN (smtfp_circuit_exp c0) (smtfp_circuit_exp c0')) /
    2 pow (INT_MAX (:'w) + dimindex (:'t)))` by
    (irule smtfp_circuit_align_value >> simp []) >>
  `float_to_real (float 1w c0 c1) =
   -float_to_real (float 0w c0 c1)` by
    (simp [binary_ieeeTheory.float_to_real_def] >>
     RealField.REAL_FIELD_TAC) >>
  `float_to_real (float 1w c0' c1') =
   -float_to_real (float 0w c0' c1')` by
    (simp [binary_ieeeTheory.float_to_real_def] >>
     RealField.REAL_FIELD_TAC) >>
  `!m n : num. ~(n <= m) ==> m <= n` by decide_tac >>
  Cases_on
    `smtfp_circuit_sig c0' c1' *
       2 ** (smtfp_circuit_exp c0' -
         MIN (smtfp_circuit_exp c0) (smtfp_circuit_exp c0')) <=
     smtfp_circuit_sig c0 c1 *
       2 ** (smtfp_circuit_exp c0 -
         MIN (smtfp_circuit_exp c0) (smtfp_circuit_exp c0'))` >>
  rewrite_tac [float_to_real_bits_sign] >>
  asm_rewrite_tac [] >>
  asm_simp_tac std_ss
    [realTheory.REAL_OF_NUM_ADD,
     realTheory.REAL_OF_NUM_MUL,
     realTheory.REAL_OF_NUM_SUB,
     GSYM realTheory.REAL_NEG_LMUL,
     GSYM realTheory.REAL_ADD_RDISTRIB,
     realTheory.REAL_NEG_ADD,
     arithmeticTheory.MULT_COMM] >>
  rewrite_tac [GSYM realTheory.REAL_OF_NUM_ADD] >>
  rpt (pop_assum kall_tac) >>
  RealField.REAL_FIELD_TAC
QED

Theorem smtfp_addsub_exact_value:
  float_to_real (smtfp_rep (x : ('t,'w) smtfp)) +
    (if subtract then -float_to_real (smtfp_rep y)
     else float_to_real (smtfp_rep y)) =
  (if smtfp_addsub_result_sign subtract x y = 0w then
     &smtfp_addsub_magnitude subtract x y
   else
     -&smtfp_addsub_magnitude subtract x y) *
    (2 pow (smtfp_addsub_scale subtract x y) /
     2 pow (INT_MAX (:'w) + dimindex (:'t)))
Proof
  rewrite_tac [smtfp_addsub_scale_def, smtfp_addsub_magnitude_def,
               smtfp_addsub_result_sign_def, LET_THM] >>
  pairarg_tac >> gvs [] >>
  mp_tac (Q.INST [`subtract` |-> `subtract`, `x` |-> `x`,
                    `y` |-> `y`] smtfp_addsub_trace_exact) >>
  gvs []
QED

(* Every finite encoding is an integer multiple of the least-format ULP.
   This boundary removes exponent adjacency from subsequent rounder proofs:
   candidate distances can be compared as natural numbers after scaling all
   operands to exponent one. *)
Definition smtfp_circuit_units_def:
  smtfp_circuit_units (e : 'w word) (m : 't word) =
    smtfp_circuit_sig e m * 2 ** (smtfp_circuit_exp e - 1)
End

Theorem smtfp_circuit_units_value:
  float_to_real
    (<| Sign := s; Exponent := e; Significand := m |> :
     ('t,'w) float) =
  (if s = 0w then &smtfp_circuit_units e m
   else -&smtfp_circuit_units e m) *
    (2 pow 1 / 2 pow (INT_MAX (:'w) + dimindex (:'t)))
Proof
  `float_to_real
     (<| Sign := 0w; Exponent := e; Significand := m |> :
      ('t,'w) float) =
   &smtfp_circuit_units e m *
     (2 pow 1 / 2 pow (INT_MAX (:'w) + dimindex (:'t)))` by
    (rewrite_tac [smtfp_circuit_units_def] >>
     irule smtfp_circuit_align_value >>
     mp_tac (Q.INST [`e` |-> `e`]
       (INST_TYPE [alpha |-> ``:'w``]
         smtfp_circuit_exp_positive)) >>
     decide_tac) >>
  wordsLib.Cases_on_word_value `s` >>
  simp [float_to_real_negative_bits]
QED

Theorem smtfp_addsub_exact_zero:
  (float_to_real (smtfp_rep (x : ('t,'w) smtfp)) +
     (if subtract then -float_to_real (smtfp_rep y)
      else float_to_real (smtfp_rep y)) = 0) <=>
  smtfp_addsub_magnitude subtract x y = 0
Proof
  rewrite_tac [smtfp_addsub_exact_value] >>
  Cases_on `smtfp_addsub_result_sign subtract x y = 0w` >>
  simp [realTheory.real_div]
QED

Definition smtfp_addsub_zero_sign_def:
  smtfp_addsub_zero_sign subtract mode (x : ('t,'w) smtfp)
      (y : ('t,'w) smtfp) =
    let xr = smtfp_rep x in
    let yr = smtfp_rep y in
    let y_sign = if subtract then ~yr.Sign else yr.Sign in
    let both_zero = (xr.Exponent = 0w /\ xr.Significand = 0w /\
                     yr.Exponent = 0w /\ yr.Significand = 0w) in
      if both_zero /\ xr.Sign = y_sign then xr.Sign
      else if mode = RTN then 1w else 0w
End

Theorem smtfp_addsub_zero_sign_negative:
  (smtfp_addsub_zero_sign subtract mode x y = 1w) <=>
  let xr = smtfp_rep x in
  let yr = smtfp_rep y in
  let y_sign = if subtract then ~yr.Sign else yr.Sign in
  let both_zero = (xr.Exponent = 0w /\ xr.Significand = 0w /\
                   yr.Exponent = 0w /\ yr.Significand = 0w) in
    if both_zero /\ xr.Sign = y_sign then xr.Sign = 1w
    else mode = RTN
Proof
  `(-1w : word1) = 1w` by wordsLib.WORD_DECIDE_TAC >>
  `(1w : word1) <> 0w` by wordsLib.WORD_DECIDE_TAC >>
  simp [smtfp_addsub_zero_sign_def] >>
  Cases_on `subtract` >> Cases_on `mode` >>
  wordsLib.Cases_on_word_value `(smtfp_rep x).Sign` >>
  wordsLib.Cases_on_word_value `(smtfp_rep y).Sign` >>
  Cases_on
    `(smtfp_rep x).Exponent = 0w /\
     (smtfp_rep x).Significand = 0w /\
     (smtfp_rep y).Exponent = 0w /\
     (smtfp_rep y).Significand = 0w` >>
  simp []
QED

Theorem float_to_real_bits_zero:
  (float_to_real
     (<| Sign := s; Exponent := e; Significand := m |> :
      ('t,'w) float) = 0) <=>
  e = 0w /\ m = 0w
Proof
  wordsLib.Cases_on_word_value `s` >>
  simp [binary_ieeeTheory.float_to_real_EQ0,
        binary_ieeeTheory.float_plus_zero_def,
        binary_ieeeTheory.float_minus_zero_def,
        binary_ieeeTheory.float_negate_def,
        binary_ieeeTheory.float_component_equality]
QED

Theorem smtfp_addsub_zero_toneg:
  (smtfp_addsub_zero_sign subtract mode x y = 1w) <=>
  if subtract then
    (if float_to_real (smtfp_rep x) = 0 /\
        float_to_real (smtfp_rep y) = 0 /\
        (smtfp_rep x).Sign <> (smtfp_rep y).Sign then
       (smtfp_rep x).Sign = 1w
     else mode = RTN)
  else
    (if float_to_real (smtfp_rep x) = 0 /\
        float_to_real (smtfp_rep y) = 0 /\
        (smtfp_rep x).Sign = (smtfp_rep y).Sign then
       (smtfp_rep x).Sign = 1w
     else mode = RTN)
Proof
  Cases_on `smtfp_rep x` >> Cases_on `smtfp_rep y` >>
  Cases_on `subtract` >> Cases_on `mode` >>
  wordsLib.Cases_on_word_value `c` >>
  wordsLib.Cases_on_word_value `c'` >>
  simp [smtfp_addsub_zero_sign_negative, float_to_real_bits_zero,
        binary_ieeeTheory.float_to_real_EQ0,
        binary_ieeeTheory.float_plus_zero_def,
        binary_ieeeTheory.float_minus_zero_def,
        binary_ieeeTheory.float_negate_def,
        binary_ieeeTheory.float_component_equality,
        boolTheory.CONJ_ASSOC]
QED

Theorem smtfp_addsub_zero_sign_value:
  smtfp_addsub_zero_sign subtract mode x y =
  if subtract then
    (if float_to_real (smtfp_rep x) = 0 /\
        float_to_real (smtfp_rep y) = 0 /\
        (smtfp_rep x).Sign <> (smtfp_rep y).Sign then
       if (smtfp_rep x).Sign = 1w then 1w else 0w
     else if mode = RTN then 1w else 0w)
  else
    (if float_to_real (smtfp_rep x) = 0 /\
        float_to_real (smtfp_rep y) = 0 /\
        (smtfp_rep x).Sign = (smtfp_rep y).Sign then
       if (smtfp_rep x).Sign = 1w then 1w else 0w
     else if mode = RTN then 1w else 0w)
Proof
  Cases_on `smtfp_rep x` >> Cases_on `smtfp_rep y` >>
  Cases_on `subtract` >> Cases_on `mode` >>
  wordsLib.Cases_on_word_value `c` >>
  wordsLib.Cases_on_word_value `c'` >>
  simp [smtfp_addsub_zero_sign_def, float_to_real_bits_zero,
        binary_ieeeTheory.float_to_real_EQ0,
        binary_ieeeTheory.float_plus_zero_def,
        binary_ieeeTheory.float_minus_zero_def,
        binary_ieeeTheory.float_negate_def,
        binary_ieeeTheory.float_component_equality,
        boolTheory.CONJ_ASSOC]
QED

Definition smtfp_addsub_circuit_def:
  smtfp_addsub_circuit subtract mode (x : ('t,'w) smtfp)
      (y : ('t,'w) smtfp) =
    let xr = smtfp_rep x in
    let yr = smtfp_rep y in
    let y_sign = if subtract then ~yr.Sign else yr.Sign in
    let trace = smtfp_addsub_trace subtract x y in
    let result =
      if xr.Exponent = UINT_MAXw /\ xr.Significand <> 0w \/
         yr.Exponent = UINT_MAXw /\ yr.Significand <> 0w then
        smtfp_nan
      else if xr.Exponent = UINT_MAXw /\
              yr.Exponent = UINT_MAXw then
        if xr.Sign = y_sign then smtfp_circuit_infinity x xr.Sign
        else smtfp_nan
      else if xr.Exponent = UINT_MAXw then
        smtfp_circuit_infinity x xr.Sign
      else if yr.Exponent = UINT_MAXw then
        smtfp_circuit_infinity x y_sign
      else
        let (scale, x_aligned, y_aligned, sign, magnitude) = trace in
          if yr.Exponent = 0w /\ yr.Significand = 0w /\
             magnitude <> 0 then
            x
          else
            let sign = if magnitude = 0 then
                         smtfp_addsub_zero_sign subtract mode x y
                       else sign in
              smtfp_circuit_encode mode x sign scale magnitude in
      (trace, result)
End

Theorem smt_float_round_zero:
  smt_float_round mode to_neg 0 =
  if to_neg then float_minus_zero (:'t # 'w)
  else float_plus_zero (:'t # 'w)
Proof
  Cases_on `mode` >>
  simp [smt_float_round_def, smt_round_def,
        binary_ieeeTheory.float_is_zero_to_real,
        binary_ieeeTheory.float_to_real_round0]
QED

Theorem smtfp_addsub_circuit_finite_zero:
  (smtfp_rep x).Exponent <> UINT_MAXw /\
  (smtfp_rep y).Exponent <> UINT_MAXw /\
  smtfp_addsub_magnitude subtract x y = 0 ==>
  SND (smtfp_addsub_circuit subtract mode x y) =
  smtfp_bits (smtfp_addsub_zero_sign subtract mode x y) 0w 0w
Proof
  rw [smtfp_addsub_circuit_def, smtfp_addsub_magnitude_def] >>
  pairarg_tac >> gvs []
QED

Theorem smtfp_addsub_circuit_finite_right_zero_nonzero:
  2 <= dimindex (:'w) /\
  (smtfp_rep x).Exponent <> UINT_MAXw /\
  ((smtfp_rep x).Exponent <> 0w \/
   (smtfp_rep x).Significand <> 0w) ==>
  SND (smtfp_addsub_circuit subtract mode (x : ('t,'w) smtfp)
    (smtfp_bits zero_sign 0w 0w)) = x
Proof
  strip_tac >>
  Cases_on `(smtfp_rep x).Exponent = 0w` >>
  fs [smtfp_addsub_circuit_def, smtfp_addsub_trace_def,
      smtfp_addsub_zero_sign_def, smtfp_nan_pattern_def,
      smtfp_circuit_exp_def, smtfp_circuit_sig_def, canon_def,
      wordsTheory.w2n_eq_0]
QED

Theorem smt_float_add_finite_round:
  x.Exponent <> UINT_MAXw /\ y.Exponent <> UINT_MAXw ==>
  smt_float_add mode (x : ('t,'w) float) y =
  smt_float_round mode
    (if float_to_real x = 0 /\ float_to_real y = 0 /\
        x.Sign = y.Sign then x.Sign = 1w
     else mode = RTN)
    (float_to_real x + float_to_real y)
Proof
  Cases_on `mode` >>
  simp [smt_float_add_def, to_binary_rounding_def,
        binary_ieeeTheory.float_add_def,
        binary_ieeeTheory.float_value_def,
        binary_ieeeTheory.float_round_with_flags_def,
        binary_ieeeTheory.float_round_def,
        smt_float_round_def, smt_round_def] >>
  Cases_on `x.Sign = y.Sign` >> simp []
QED

Theorem smt_float_sub_finite_round:
  x.Exponent <> UINT_MAXw /\ y.Exponent <> UINT_MAXw ==>
  smt_float_sub mode (x : ('t,'w) float) y =
  smt_float_round mode
    (if float_to_real x = 0 /\ float_to_real y = 0 /\
        x.Sign <> y.Sign then x.Sign = 1w
     else mode = RTN)
    (float_to_real x - float_to_real y)
Proof
  Cases_on `mode` >>
  simp [smt_float_sub_def, to_binary_rounding_def,
        binary_ieeeTheory.float_sub_def,
        binary_ieeeTheory.float_value_def,
        binary_ieeeTheory.float_round_with_flags_def,
        binary_ieeeTheory.float_round_def,
        smt_float_round_def, smt_round_def]
QED

Theorem smtfp_addsub_circuit_finite_right_zero_nonzero_correspondence:
  2 <= dimindex (:'w) /\
  (smtfp_rep x).Exponent <> UINT_MAXw /\
  ((smtfp_rep x).Exponent <> 0w \/
   (smtfp_rep x).Significand <> 0w) ==>
  (if subtract then
     smtfp_sub mode x (smtfp_bits zero_sign 0w 0w)
   else
     smtfp_add mode x (smtfp_bits zero_sign 0w 0w)) =
  SND (smtfp_addsub_circuit subtract mode (x : ('t,'w) smtfp)
    (smtfp_bits zero_sign 0w 0w))
Proof
  strip_tac >>
  `SND (smtfp_addsub_circuit subtract mode x
      (smtfp_bits zero_sign 0w 0w)) = x` by
    metis_tac [smtfp_addsub_circuit_finite_right_zero_nonzero] >>
  `!to_neg. smt_float_round mode to_neg
       (float_to_real (smtfp_rep x)) = smtfp_rep x` by
    (strip_tac >> irule smt_float_round_representable_nonzero >>
     simp [binary_ieeeTheory.float_is_finite_Exponent,
           GSYM binary_ieeeTheory.float_is_zero_to_real,
           binary_ieeeTheory.float_is_zero]) >>
  `!s : word1. float_to_real
       (<| Sign := s; Exponent := 0w; Significand := 0w |> :
        ('t,'w) float) = 0` by
    simp [float_to_real_bits_zero] >>
  `smt_float_add mode (smtfp_rep x)
       (smtfp_rep (smtfp_bits zero_sign 0w 0w)) = smtfp_rep x` by
    (simp [smtfp_nan_pattern_def, canon_def] >>
     rw [smt_float_add_finite_round] >>
     asm_simp_tac (srw_ss()) []) >>
  `smt_float_sub mode (smtfp_rep x)
       (smtfp_rep (smtfp_bits zero_sign 0w 0w)) = smtfp_rep x` by
    (simp [smtfp_nan_pattern_def, canon_def] >>
     rw [smt_float_sub_finite_round] >>
     asm_simp_tac (srw_ss()) []) >>
  Cases_on `subtract` >>
  simp [smtfp_add_def, smtfp_sub_def]
QED

Theorem smtfp_canon_zero_bits[simp]:
  canon (<| Sign := s; Exponent := 0w; Significand := 0w |> :
    ('t,'w) float) =
  <| Sign := s; Exponent := 0w; Significand := 0w |>
Proof
  simp [canon_def, smtfp_nan_pattern_def,
        binary_ieeeTheory.float_is_nan_def,
        binary_ieeeTheory.float_value_def]
QED

Theorem smtfp_SmtFp_round_zero:
  SmtFp (canon (smt_float_round mode to_neg 0 : ('t,'w) float)) =
  smtfp_bits (if to_neg then 1w else 0w) 0w 0w
Proof
  Cases_on `to_neg` >>
  simp [smt_float_round_zero, smtfp_bits_def,
        binary_ieeeTheory.float_plus_zero_def,
        binary_ieeeTheory.float_minus_zero_def,
        binary_ieeeTheory.float_negate_def] >>
  wordsLib.WORD_DECIDE_TAC
QED

Theorem smtfp_bool_sign_cond:
  (if (if a then b else c) then (1w : word1) else 0w) =
  (if a then if b then 1w else 0w
   else if c then 1w else 0w)
Proof
  Cases_on `a` >> Cases_on `b` >> Cases_on `c` >> simp []
QED

Theorem smtfp_addsub_circuit_exact_zero_correspondence:
  (smtfp_rep x).Exponent <> UINT_MAXw /\
  (smtfp_rep y).Exponent <> UINT_MAXw /\
  (float_to_real (smtfp_rep x) +
     (if subtract then -float_to_real (smtfp_rep y)
      else float_to_real (smtfp_rep y)) = 0) ==>
  (if subtract then smtfp_sub mode x y else smtfp_add mode x y) =
  SND (smtfp_addsub_circuit subtract mode x y)
Proof
  strip_tac >>
  `smtfp_addsub_magnitude subtract x y = 0` by
    fs [GSYM smtfp_addsub_exact_zero] >>
  drule_all_then assume_tac smtfp_addsub_circuit_finite_zero >>
  Cases_on `subtract` >>
  fs [smtfp_add_def, smtfp_sub_def, smt_float_add_finite_round,
      smt_float_sub_finite_round, smtfp_SmtFp_round_zero,
      smtfp_addsub_zero_sign_value, realTheory.real_sub] >>
  simp [smtfp_bool_sign_cond]
QED

Theorem smtfp_add_nan[simp]:
  smtfp_add mode x smtfp_nan = smtfp_nan
Proof
  Cases_on `mode` >> Cases_on `float_value (smtfp_rep x)` >>
  simp [smtfp_add_def, smt_float_add_def, smtfp_nan_def,
        smtfp_canonical_def, canon_def, to_binary_rounding_def,
        binary_ieeeTheory.float_add_def,
        binary_ieeeTheory.some_nan_properties]
QED

Theorem smtfp_sub_nan[simp]:
  smtfp_sub mode x smtfp_nan = smtfp_nan
Proof
  Cases_on `mode` >> Cases_on `float_value (smtfp_rep x)` >>
  simp [smtfp_sub_def, smt_float_sub_def, smtfp_nan_def,
        smtfp_canonical_def, canon_def, to_binary_rounding_def,
        binary_ieeeTheory.float_sub_def,
        binary_ieeeTheory.some_nan_properties]
QED

Theorem smtfp_add_circuit_nan:
  SND (smtfp_addsub_circuit F mode x smtfp_nan) = smtfp_nan
Proof
  simp [smtfp_addsub_circuit_def, smtfp_nan_def, canon_def,
        smtfp_canonical_def, float_canon_qnan_def, canon_qnan_msb]
QED

Theorem smtfp_sub_circuit_nan:
  SND (smtfp_addsub_circuit T mode x smtfp_nan) = smtfp_nan
Proof
  simp [smtfp_addsub_circuit_def, smtfp_nan_def, canon_def,
        smtfp_canonical_def, float_canon_qnan_def, canon_qnan_msb]
QED

Theorem smtfp_add_nan_circuit_correspondence:
  smtfp_add mode x smtfp_nan =
  SND (smtfp_addsub_circuit F mode x smtfp_nan)
Proof
  simp [smtfp_add_circuit_nan]
QED

Theorem smtfp_sub_nan_circuit_correspondence:
  smtfp_sub mode x smtfp_nan =
  SND (smtfp_addsub_circuit T mode x smtfp_nan)
Proof
  simp [smtfp_sub_circuit_nan]
QED

(* Arithmetic and rounding proof for the independent encoder. *)
Theorem circuit_units_log2:
  0 < scale /\ 0 < magnitude ==>
  LOG2 (magnitude * 2 ** (scale - 1)) + 1 =
  LOG2 magnitude + scale
Proof
  strip_tac >>
  fs [bitTheory.LOG2_def, logrootTheory.LOG2_MULT_EXP] >>
  decide_tac
QED

Theorem div_common_right_factor:
  0 < factor /\ 0 < divisor ==>
  (magnitude * factor) DIV (divisor * factor) =
  magnitude DIV divisor
Proof
  strip_tac >>
  mp_tac (Q.SPECL [`factor`, `divisor`]
    arithmeticTheory.DIV_DIV_DIV_MULT) >>
  impl_tac >- simp [] >>
  disch_then (qspec_then `magnitude * factor` mp_tac) >>
  simp [arithmeticTheory.MULT_DIV, arithmeticTheory.MULT_COMM]
QED

Theorem circuit_quotient_units_arithmetic:
  0 < scale /\ 0 < effective_exponent ==>
  (if scale <= effective_exponent then
     magnitude DIV 2 ** (effective_exponent - scale)
   else magnitude * 2 ** (scale - effective_exponent)) =
  (magnitude * 2 ** (scale - 1)) DIV
    2 ** (effective_exponent - 1)
Proof
  rpt strip_tac >> Cases_on `scale <= effective_exponent`
  >- (asm_rewrite_tac [] >>
      `effective_exponent - 1 =
       (effective_exponent - scale) + (scale - 1)` by decide_tac >>
      pop_assum SUBST1_TAC >>
      rewrite_tac [arithmeticTheory.EXP_ADD] >>
      irule EQ_SYM >>
      irule div_common_right_factor >> simp [])
  >> asm_rewrite_tac [] >>
  `scale - 1 =
   (scale - effective_exponent) + (effective_exponent - 1)` by
    decide_tac >>
  pop_assum SUBST1_TAC >>
  rewrite_tac [arithmeticTheory.EXP_ADD] >>
  irule EQ_TRANS >>
  qexists_tac
    `((magnitude * 2 ** (scale - effective_exponent)) *
       2 ** (effective_exponent - 1)) DIV
     2 ** (effective_exponent - 1)` >>
  conj_tac
  >- (irule EQ_SYM >>
      irule arithmeticTheory.MULT_DIV >> simp [])
  >> rewrite_tac [arithmeticTheory.MULT_ASSOC]
QED

Theorem circuit_wanted_exponent_units:
  0 < scale /\ 0 < magnitude ==>
  smtfp_circuit_wanted_exponent fraction_width scale magnitude =
  MAX 1
    (LOG2 (magnitude * 2 ** (scale - 1)) + 1 - fraction_width)
Proof
  strip_tac >>
  fs [smtfp_circuit_wanted_exponent_def,
      circuit_units_log2]
QED

Theorem mod_common_right_factor:
  0 < factor /\ 0 < divisor ==>
  (magnitude * factor) MOD (divisor * factor) =
  (magnitude MOD divisor) * factor
Proof
  strip_tac >>
  irule arithmeticTheory.MOD_UNIQUE >>
  qexists_tac `magnitude DIV divisor` >>
  conj_tac
  >- (mp_tac (Q.SPEC `divisor` arithmeticTheory.DIVISION) >>
      impl_tac >- simp [] >>
      disch_then (qspec_then `magnitude` strip_assume_tac) >>
      qpat_x_assum
        `magnitude = magnitude DIV divisor * divisor + _`
        (mp_tac o AP_TERM ``\n : num. n * factor``) >>
      simp [arithmeticTheory.LEFT_ADD_DISTRIB,
            arithmeticTheory.MULT_ASSOC] >>
      CONV_TAC (AC_CONV (arithmeticTheory.MULT_ASSOC,
                         arithmeticTheory.MULT_COMM)))
  >> simp [arithmeticTheory.LT_MULT_RCANCEL]
QED

Theorem circuit_remainder_units_arithmetic:
  0 < scale /\ 0 < effective_exponent ==>
  (magnitude * 2 ** (scale - 1)) MOD
    2 ** (effective_exponent - 1) =
  if scale <= effective_exponent then
    (magnitude MOD 2 ** (effective_exponent - scale)) *
      2 ** (scale - 1)
  else 0
Proof
  strip_tac >> Cases_on `scale <= effective_exponent`
  >- (asm_rewrite_tac [] >>
      `effective_exponent - 1 =
       (effective_exponent - scale) + (scale - 1)` by decide_tac >>
      pop_assum SUBST1_TAC >>
      rewrite_tac [arithmeticTheory.EXP_ADD] >>
      irule mod_common_right_factor >> simp [])
  >> asm_rewrite_tac [] >>
  `scale - 1 =
   (scale - effective_exponent) + (effective_exponent - 1)` by
    decide_tac >>
  pop_assum SUBST1_TAC >>
  rewrite_tac [arithmeticTheory.EXP_ADD] >>
  simp [arithmeticTheory.MULT_ASSOC,
        arithmeticTheory.MOD_EQ_0]
QED

Theorem smtfp_circuit_effective_exponent_positive[simp]:
  0 < smtfp_circuit_effective_exponent maximum_exponent
    fraction_width scale magnitude
Proof
  simp [smtfp_circuit_effective_exponent_def]
QED

Theorem circuit_divisor_units_arithmetic:
  0 < scale /\ 0 < effective_exponent ==>
  (2 : num) ** (effective_exponent - 1) =
  2 ** (effective_exponent - scale) *
    2 ** (MIN scale effective_exponent - 1)
Proof
  rpt strip_tac >> Cases_on `scale <= effective_exponent`
  >- (`effective_exponent - 1 =
      (effective_exponent - scale) + (scale - 1)` by
        decide_tac >>
      rewrite_tac [arithmeticTheory.MIN_ALT] >>
      asm_rewrite_tac [] >>
      irule arithmeticTheory.EXP_ADD)
  >> rewrite_tac [arithmeticTheory.MIN_ALT] >>
  asm_rewrite_tac [] >>
  `effective_exponent - scale = 0` by decide_tac >>
  pop_assum SUBST1_TAC >> simp []
QED

Theorem smtfp_circuit_divisor_units:
  0 < scale ==>
  2 **
    (smtfp_circuit_effective_exponent maximum_exponent
       fraction_width scale magnitude - 1) =
  smtfp_circuit_divisor maximum_exponent fraction_width scale magnitude *
    2 **
      (MIN scale
        (smtfp_circuit_effective_exponent maximum_exponent
          fraction_width scale magnitude) - 1)
Proof
  strip_tac >>
  rewrite_tac [smtfp_circuit_divisor_def,
               smtfp_circuit_shift_def] >>
  irule circuit_divisor_units_arithmetic >> simp []
QED

Theorem smtfp_circuit_quotient_units:
  0 < scale ==>
  smtfp_circuit_quotient maximum_exponent fraction_width scale magnitude =
  (magnitude * 2 ** (scale - 1)) DIV
    2 **
      (smtfp_circuit_effective_exponent maximum_exponent
        fraction_width scale magnitude - 1)
Proof
  strip_tac >>
  simp_tac pure_ss
    [smtfp_circuit_quotient_def,
     LET_THM,
     smtfp_circuit_divisor_def,
     smtfp_circuit_shift_def] >>
  irule circuit_quotient_units_arithmetic >> simp []
QED

Theorem smtfp_circuit_remainder_units:
  0 < scale ==>
  (magnitude * 2 ** (scale - 1)) MOD
    2 **
      (smtfp_circuit_effective_exponent maximum_exponent
        fraction_width scale magnitude - 1) =
  smtfp_circuit_remainder maximum_exponent fraction_width scale magnitude *
    2 **
      (MIN scale
        (smtfp_circuit_effective_exponent maximum_exponent
          fraction_width scale magnitude) - 1)
Proof
  strip_tac >>
  once_rewrite_tac [smtfp_circuit_remainder_def] >>
  simp_tac pure_ss
    [LET_THM,
     smtfp_circuit_divisor_def,
     smtfp_circuit_shift_def] >>
  mp_tac (Q.INST
    [`scale` |-> `scale`,
     `effective_exponent` |->
       `smtfp_circuit_effective_exponent maximum_exponent
         fraction_width scale magnitude`,
     `magnitude` |-> `magnitude`]
    circuit_remainder_units_arithmetic) >>
  impl_tac >- simp [] >>
  strip_tac >>
  Cases_on
    `scale <= smtfp_circuit_effective_exponent maximum_exponent
      fraction_width scale magnitude` >>
  fs [arithmeticTheory.MIN_ALT]
QED

Theorem circuit_double_mult_scale:
  (2 : num) * (residue * factor) = (2 * residue) * factor
Proof
  irule arithmeticTheory.MULT_ASSOC
QED

Theorem circuit_scaled_double_lt:
  0 < (factor : num) ==>
  (divisor * factor < 2 * (residue * factor) <=>
   divisor < 2 * residue)
Proof
  strip_tac >> rewrite_tac [circuit_double_mult_scale] >>
  simp [arithmeticTheory.LT_MULT_RCANCEL]
QED

Theorem circuit_scaled_double_le:
  0 < (factor : num) ==>
  (divisor * factor <= 2 * (residue * factor) <=>
   divisor <= 2 * residue)
Proof
  strip_tac >> rewrite_tac [circuit_double_mult_scale] >>
  simp [arithmeticTheory.LE_MULT_RCANCEL]
QED

Theorem circuit_scaled_double_eq:
  0 < (factor : num) ==>
  (divisor * factor = 2 * (residue * factor) <=>
   divisor = 2 * residue)
Proof
  strip_tac >> `factor <> 0` by (CCONTR_TAC >> fs []) >>
  rewrite_tac [circuit_double_mult_scale] >>
  rewrite_tac [arithmeticTheory.EQ_MULT_RCANCEL] >>
  decide_tac
QED

Theorem smtfp_circuit_round_up_scale:
  0 < factor ==>
  (smtfp_circuit_round_up mode sign q (residue * factor)
     (divisor * factor) <=>
   smtfp_circuit_round_up mode sign q residue divisor)
Proof
  strip_tac >> Cases_on `mode` >>
  simp [smtfp_circuit_round_up_def,
        circuit_scaled_double_lt,
        circuit_scaled_double_le,
        circuit_scaled_double_eq]
QED

Theorem smtfp_circuit_round_units:
  0 < factor ==>
  smtfp_circuit_round mode sign q (residue * factor)
    (divisor * factor) =
  smtfp_circuit_round mode sign q residue divisor
Proof
  strip_tac >>
  simp [smtfp_circuit_round_def,
        smtfp_circuit_round_up_scale]
QED

Theorem smtfp_circuit_rounded_units:
  0 < scale ==>
  smtfp_circuit_rounded mode sign maximum_exponent fraction_width
    scale magnitude =
  smtfp_circuit_round mode sign
    ((magnitude * 2 ** (scale - 1)) DIV
      2 **
        (smtfp_circuit_effective_exponent maximum_exponent
          fraction_width scale magnitude - 1))
    ((magnitude * 2 ** (scale - 1)) MOD
      2 **
        (smtfp_circuit_effective_exponent maximum_exponent
          fraction_width scale magnitude - 1))
    (2 **
      (smtfp_circuit_effective_exponent maximum_exponent
        fraction_width scale magnitude - 1))
Proof
  strip_tac >>
  simp_tac pure_ss [smtfp_circuit_rounded_def] >>
  mp_tac (Q.INST
    [`maximum_exponent` |-> `maximum_exponent`,
     `fraction_width` |-> `fraction_width`,
     `scale` |-> `scale`, `magnitude` |-> `magnitude`]
    smtfp_circuit_quotient_units) >>
  impl_tac >- simp [] >> strip_tac >>
  mp_tac (Q.INST
    [`maximum_exponent` |-> `maximum_exponent`,
     `fraction_width` |-> `fraction_width`,
     `scale` |-> `scale`, `magnitude` |-> `magnitude`]
    smtfp_circuit_remainder_units) >>
  impl_tac >- simp [] >> strip_tac >>
  mp_tac (Q.INST
    [`maximum_exponent` |-> `maximum_exponent`,
     `fraction_width` |-> `fraction_width`,
     `scale` |-> `scale`, `magnitude` |-> `magnitude`]
    smtfp_circuit_divisor_units) >>
  impl_tac >- simp [] >> strip_tac >>
  asm_rewrite_tac [] >>
  irule EQ_SYM >>
  irule smtfp_circuit_round_units >> simp []
QED

Definition smtfp_circuit_endpoint_def:
  smtfp_circuit_endpoint (format : ('t,'w) smtfp) (sign : word1)
      (exponent : num) (rounded : num) =
    if rounded < 2 ** dimindex (:'t) then
      smtfp_bits sign 0w (n2w rounded)
    else if rounded = 2 ** (dimindex (:'t) + 1) then
      smtfp_bits sign (n2w (exponent + 1)) 0w
    else
      smtfp_bits sign (n2w exponent)
        (n2w (rounded - 2 ** dimindex (:'t))) : ('t,'w) smtfp
End

Theorem smtfp_rep_finite_n2w_bits:
  exponent < dimword (:'w) - 1 ==>
  smtfp_rep
    (smtfp_bits sign (n2w exponent) (n2w significand) :
      ('t,'w) smtfp) =
  (<| Sign := sign; Exponent := n2w exponent;
      Significand := n2w significand |> : ('t,'w) float)
Proof
  strip_tac >>
  `exponent < dimword (:'w)` by decide_tac >>
  `w2n (n2w exponent : 'w word) = exponent` by
    simp [wordsTheory.w2n_n2w, arithmeticTheory.LESS_MOD] >>
  `w2n (UINT_MAXw : 'w word) = dimword (:'w) - 1` by
    simp [wordsTheory.w2n_minus1, wordsTheory.UINT_MAX_def] >>
  `(n2w exponent : 'w word) <> UINT_MAXw` by
    (strip_tac >>
     pop_assum (mp_tac o AP_TERM ``w2n : 'w word -> num``) >>
     asm_rewrite_tac [] >> decide_tac) >>
  simp [smtfp_rep_bits,
        canon_def,
        smtfp_nan_pattern_def]
QED

Theorem circuit_carry_units_arithmetic:
  1 <= exponent ==>
  (2 : num) ** exponent * 2 ** fraction_width =
  2 ** (fraction_width + 1) * 2 ** (exponent - 1)
Proof
  strip_tac >>
  rewrite_tac [GSYM arithmeticTheory.EXP_ADD] >>
  mp_tac (Q.SPEC `2` arithmeticTheory.EXP_BASE_INJECTIVE) >>
  simp [] >> decide_tac
QED

Theorem circuit_bound_arithmetic:
  (exponent : num) < dimension - 2 ==>
  exponent + 1 < dimension - 1
Proof
  decide_tac
QED

Theorem smtfp_circuit_endpoint_units:
  2 <= dimindex (:'w) /\
  1 <= exponent /\ exponent <= dimword (:'w) - 2 /\
  rounded <= 2 ** (dimindex (:'t) + 1) /\
  (rounded < 2 ** dimindex (:'t) ==> exponent = 1) /\
  (rounded = 2 ** (dimindex (:'t) + 1) ==>
   exponent < dimword (:'w) - 2) ==>
  let output = smtfp_rep
    (smtfp_circuit_endpoint (format : ('t,'w) smtfp) sign exponent rounded)
  in
    output.Sign = sign /\
    smtfp_circuit_units output.Exponent output.Significand =
      rounded * 2 ** (exponent - 1)
Proof
  simp_tac pure_ss [LET_THM] >> strip_tac >> fs [] >>
  Cases_on `rounded < 2 ** dimindex (:'t)`
  >- (`rounded < dimword (:'t)` by
        fs [wordsTheory.dimword_def] >>
      `smtfp_rep
         (smtfp_circuit_endpoint (format : ('t,'w) smtfp) sign exponent rounded) =
       (<| Sign := sign; Exponent := 0w;
           Significand := n2w rounded |> : ('t,'w) float)` by
        (simp [smtfp_circuit_endpoint_def,
               smtfp_rep_bits,
               canon_def,
               smtfp_nan_pattern_def]) >>
      qpat_x_assum `smtfp_rep _ = _`
        (fn th => once_rewrite_tac [th]) >>
      fs [smtfp_circuit_units_def,
          smtfp_circuit_sig_def,
          smtfp_circuit_exp_def,
          wordsTheory.w2n_n2w,
          arithmeticTheory.LESS_MOD])
  >> Cases_on `rounded = 2 ** (dimindex (:'t) + 1)`
  >- (qpat_x_assum `1 <= exponent`
        (fn ath => assume_tac (MATCH_MP
          (Q.SPECL [`dimindex (:'t)`, `exponent`]
            (GEN_ALL circuit_carry_units_arithmetic)) ath)) >>
      `exponent < dimword (:'w) - 2` by fs [] >>
      `exponent + 1 < dimword (:'w) - 1` by
        metis_tac [GEN_ALL circuit_bound_arithmetic] >>
      `smtfp_rep
         (smtfp_circuit_endpoint (format : ('t,'w) smtfp) sign exponent rounded) =
       (<| Sign := sign; Exponent := n2w (exponent + 1);
           Significand := 0w |> : ('t,'w) float)` by
        (simp [smtfp_circuit_endpoint_def, smtfp_rep_finite_n2w_bits]) >>
      qpat_x_assum `smtfp_rep _ = _`
        (fn th => once_rewrite_tac [th]) >>
      fs [smtfp_circuit_units_def,
          smtfp_circuit_sig_def,
          smtfp_circuit_exp_def,
          wordsTheory.w2n_n2w, wordsTheory.dimword_def,
          arithmeticTheory.LESS_MOD] >>
      qpat_x_assum
        `2 ** exponent * 2 ** dimindex (:'t) = _` ACCEPT_TAC)
  >> `rounded < 2 ** (dimindex (:'t) + 1)` by decide_tac >>
  `exponent < dimword (:'w) - 1` by decide_tac >>
  `rounded - 2 ** dimindex (:'t) < dimword (:'t)` by
    (simp_tac std_ss [wordsTheory.dimword_def,
                      arithmeticTheory.EXP_ADD] >>
     qpat_x_assum `rounded < 2 ** (dimindex (:'t) + 1)` mp_tac >>
     simp [arithmeticTheory.EXP_ADD]) >>
  `smtfp_rep
     (smtfp_circuit_endpoint (format : ('t,'w) smtfp) sign exponent rounded) =
   (<| Sign := sign; Exponent := n2w exponent;
       Significand := n2w (rounded - 2 ** dimindex (:'t)) |> :
    ('t,'w) float)` by
    (simp [smtfp_circuit_endpoint_def, smtfp_rep_finite_n2w_bits]) >>
  qpat_x_assum `smtfp_rep _ = _`
    (fn th => once_rewrite_tac [th]) >>
  fs [smtfp_circuit_units_def,
      smtfp_circuit_sig_def,
      smtfp_circuit_exp_def,
      wordsTheory.w2n_n2w, wordsTheory.dimword_def,
      arithmeticTheory.LESS_MOD] >>
  `2 ** dimindex (:'t) <= rounded` by decide_tac >>
  decide_tac
QED

Theorem smtfp_circuit_round_abs_diff:
  0 < divisor ==>
  ABS_DIFF
    (smtfp_circuit_round mode sign (units DIV divisor)
       (units MOD divisor) divisor * divisor)
    units =
  if smtfp_circuit_round_up mode sign (units DIV divisor)
       (units MOD divisor) divisor then
    divisor - units MOD divisor
  else units MOD divisor
Proof
  strip_tac >>
  mp_tac (Q.SPEC `divisor` arithmeticTheory.DIVISION) >>
  impl_tac >- simp [] >>
  disch_then (qspec_then `units` strip_assume_tac) >>
  Cases_on
    `smtfp_circuit_round_up mode sign (units DIV divisor)
       (units MOD divisor) divisor`
  >- (`units < (units DIV divisor + 1) * divisor` by
        (simp [arithmeticTheory.LEFT_ADD_DISTRIB] >>
         intLib.ARITH_TAC) >>
      simp [smtfp_circuit_round_def,
            arithmeticTheory.ABS_DIFF_def,
            arithmeticTheory.LEFT_ADD_DISTRIB] >>
      intLib.ARITH_TAC) >>
  `units DIV divisor * divisor <= units` by intLib.ARITH_TAC >>
  Cases_on `units DIV divisor * divisor < units` >>
  simp [smtfp_circuit_round_def,
        arithmeticTheory.ABS_DIFF_def,
        arithmeticTheory.LEFT_ADD_DISTRIB] >>
  intLib.ARITH_TAC
QED

Theorem circuit_nearest_multiple:
  0 < divisor /\ residue < divisor /\
  units = quotient * divisor + residue /\
  (increment ==> divisor <= 2 * residue) /\
  (~increment ==> 2 * residue <= divisor) ==>
  ABS_DIFF
    ((quotient + if increment then 1 else 0) * divisor) units <=
  ABS_DIFF (candidate * divisor) units
Proof
  strip_tac >> Cases_on `increment` >> fs []
  >- (Cases_on `quotient < candidate`
      >- (`quotient + 1 <= candidate` by decide_tac >>
          `residue + divisor * quotient <
             (quotient + 1) * divisor` by
            (simp [arithmeticTheory.LEFT_ADD_DISTRIB] >>
             intLib.ARITH_TAC) >>
          `(quotient + 1) * divisor <= candidate * divisor` by
            simp [arithmeticTheory.LE_MULT_RCANCEL] >>
          `~(candidate * divisor <
               residue + divisor * quotient)` by
            intLib.ARITH_TAC >>
          simp [arithmeticTheory.ABS_DIFF_def,
                arithmeticTheory.LEFT_ADD_DISTRIB])
      >> `candidate <= quotient` by decide_tac >>
      `candidate * divisor <= quotient * divisor` by
        simp [arithmeticTheory.LE_MULT_RCANCEL] >>
      simp [arithmeticTheory.ABS_DIFF_def,
            arithmeticTheory.LEFT_ADD_DISTRIB])
  >> Cases_on `candidate <= quotient`
  >- (`candidate * divisor <= quotient * divisor` by
        simp [arithmeticTheory.LE_MULT_RCANCEL] >>
      simp [arithmeticTheory.ABS_DIFF_def])
  >> `quotient + 1 <= candidate` by decide_tac >>
  `residue + divisor * quotient <
     (quotient + 1) * divisor` by
    (simp [arithmeticTheory.LEFT_ADD_DISTRIB] >>
     intLib.ARITH_TAC) >>
  `(quotient + 1) * divisor <= candidate * divisor` by
    simp [arithmeticTheory.LE_MULT_RCANCEL] >>
  `~(candidate * divisor < residue + divisor * quotient)` by
    intLib.ARITH_TAC >>
  simp [arithmeticTheory.ABS_DIFF_def,
        arithmeticTheory.LEFT_ADD_DISTRIB] >>
  intLib.ARITH_TAC
QED

Theorem smtfp_circuit_round_nearest_multiple:
  0 < divisor /\ (mode = RNE \/ mode = RNA) ==>
  ABS_DIFF
    (smtfp_circuit_round mode sign (units DIV divisor)
       (units MOD divisor) divisor * divisor)
    units <=
  ABS_DIFF (candidate * divisor) units
Proof
  rewrite_tac [smtfp_circuit_round_def] >>
  strip_tac >>
  irule (Q.INST [`residue` |-> `units MOD divisor`]
    circuit_nearest_multiple) >>
  simp [arithmeticTheory.DIVISION] >>
  fs [smtfp_circuit_round_up_def] >>
  decide_tac
QED

Theorem smtfp_circuit_endpoint_next_hi:
  2 <= dimindex (:'w) /\
  1 <= exponent /\ exponent <= dimword (:'w) - 2 /\
  quotient < 2 ** (dimindex (:'t) + 1) /\
  (quotient < 2 ** dimindex (:'t) ==> exponent = 1) /\
  (quotient + 1 = 2 ** (dimindex (:'t) + 1) ==>
   exponent < dimword (:'w) - 2) ==>
  next_hi
    (smtfp_rep
      (smtfp_circuit_endpoint (format : ('t,'w) smtfp) sign exponent quotient)) =
  smtfp_rep
    (smtfp_circuit_endpoint format sign exponent (quotient + 1))
Proof
  strip_tac >>
  Cases_on `quotient < 2 ** dimindex (:'t)`
  >- (`quotient < dimword (:'t)` by
        fs [wordsTheory.dimword_def] >>
      Cases_on `quotient + 1 < 2 ** dimindex (:'t)`
      >- (`quotient + 1 < dimword (:'t)` by
            fs [wordsTheory.dimword_def] >>
          simp [smtfp_circuit_endpoint_def, smtfp_rep_finite_n2w_bits,
                canon_def, float_canon_qnan_def,
                binary_ieeeTheory.float_is_nan_def,
                smtfp_nan_pattern_def,
                binary_ieeeTheory.next_hi_def,
                wordsTheory.WORD_NEG_1, wordsTheory.word_T_def,
                wordsTheory.word_lo_n2w,
                wordsTheory.word_add_n2w,
                wordsTheory.dimword_def,
                wordsTheory.UINT_MAX_def])
      >> `quotient + 1 = 2 ** dimindex (:'t)` by decide_tac >>
      simp [smtfp_circuit_endpoint_def, smtfp_rep_finite_n2w_bits,
            canon_def, float_canon_qnan_def,
            binary_ieeeTheory.float_is_nan_def,
            smtfp_nan_pattern_def,
            binary_ieeeTheory.next_hi_def,
            wordsTheory.WORD_NEG_1, wordsTheory.word_T_def,
            wordsTheory.word_lo_n2w,
            wordsTheory.word_add_n2w,
            wordsTheory.dimword_def,
            wordsTheory.UINT_MAX_def] >>
      wordsLib.WORD_DECIDE_TAC) >>
  Cases_on `quotient + 1 = 2 ** (dimindex (:'t) + 1)`
  >- (`exponent < 2 ** dimindex (:'w)` by
        fs [wordsTheory.dimword_def] >>
      `exponent MOD 2 ** dimindex (:'w) = exponent` by
        simp [arithmeticTheory.LESS_MOD] >>
      `exponent <> 2 ** dimindex (:'w) - 1` by
        fs [wordsTheory.dimword_def] >>
      `quotient - 2 ** dimindex (:'t) =
       2 ** dimindex (:'t) - 1` by
        (qpat_x_assum `quotient + 1 = _` mp_tac >>
         simp [arithmeticTheory.EXP_ADD] >> decide_tac) >>
      simp [smtfp_circuit_endpoint_def, smtfp_rep_finite_n2w_bits,
            canon_def, float_canon_qnan_def,
            binary_ieeeTheory.float_is_nan_def,
            smtfp_nan_pattern_def,
            binary_ieeeTheory.next_hi_def,
            wordsTheory.WORD_NEG_1, wordsTheory.word_T_def,
            wordsTheory.word_lo_n2w,
            wordsTheory.word_add_n2w,
            wordsTheory.dimword_def,
            wordsTheory.UINT_MAX_def]) >>
  `2 ** dimindex (:'t) <= quotient` by decide_tac >>
  `quotient + 1 < 2 ** (dimindex (:'t) + 1)` by decide_tac >>
  `quotient - 2 ** dimindex (:'t) < dimword (:'t)` by
    (rw [wordsTheory.dimword_def] >>
     qpat_x_assum `quotient + 1 < _` mp_tac >>
     simp [arithmeticTheory.EXP_ADD] >> decide_tac) >>
  `quotient + 1 - 2 ** dimindex (:'t) < dimword (:'t)` by
    (rw [wordsTheory.dimword_def] >>
     qpat_x_assum `quotient + 1 < _` mp_tac >>
     simp [arithmeticTheory.EXP_ADD] >> decide_tac) >>
  `exponent < 2 ** dimindex (:'w)` by
    fs [wordsTheory.dimword_def] >>
  `exponent MOD 2 ** dimindex (:'w) = exponent` by
    simp [arithmeticTheory.LESS_MOD] >>
  `exponent <> 2 ** dimindex (:'w) - 1` by
    fs [wordsTheory.dimword_def] >>
  `(quotient - 2 ** dimindex (:'t)) + 1 =
   quotient + 1 - 2 ** dimindex (:'t)` by decide_tac >>
  `1 < 2 ** dimindex (:'t)` by
    simp [arithmeticTheory.ONE_LT_EXP, fcpTheory.DIMINDEX_GT_0] >>
  `0 < 2 ** dimindex (:'t) - 1` by decide_tac >>
  `quotient < 2 * 2 ** dimindex (:'t) - 1` by
    (qpat_x_assum `quotient + 1 < _` mp_tac >>
     simp [arithmeticTheory.EXP_ADD] >> decide_tac) >>
  simp [smtfp_circuit_endpoint_def, smtfp_rep_finite_n2w_bits,
        canon_def, float_canon_qnan_def,
        binary_ieeeTheory.float_is_nan_def,
        smtfp_nan_pattern_def,
        binary_ieeeTheory.next_hi_def,
        wordsTheory.WORD_NEG_1, wordsTheory.word_T_def,
        wordsTheory.word_lo_n2w,
        wordsTheory.word_add_n2w,
        wordsTheory.dimword_def,
        wordsTheory.UINT_MAX_def]
QED

Theorem smtfp_circuit_endpoint_finite:
  2 <= dimindex (:'w) /\
  1 <= exponent /\ exponent <= dimword (:'w) - 2 /\
  rounded <= 2 ** (dimindex (:'t) + 1) /\
  (rounded = 2 ** (dimindex (:'t) + 1) ==>
   exponent < dimword (:'w) - 2) ==>
  float_is_finite
    (smtfp_rep
      (smtfp_circuit_endpoint (format : ('t,'w) smtfp) sign exponent rounded))
Proof
  strip_tac >>
  Cases_on `rounded < 2 ** dimindex (:'t)`
  >- (simp [smtfp_circuit_endpoint_def, smtfp_rep_finite_n2w_bits,
            binary_ieeeTheory.float_is_finite_Exponent] >>
      `0 < dimword (:'w) - 1` by decide_tac >>
      simp [wordsTheory.word_T_def, wordsTheory.UINT_MAX_def,
            wordsTheory.dimword_def]) >>
  Cases_on `rounded = 2 ** (dimindex (:'t) + 1)`
  >- (`exponent + 1 < dimword (:'w) - 1` by decide_tac >>
      simp [smtfp_circuit_endpoint_def, smtfp_rep_finite_n2w_bits,
            binary_ieeeTheory.float_is_finite_Exponent] >>
      irule wordsTheory.WORD_LOWER_NOT_EQ >>
      simp [wordsTheory.WORD_NEG_1, wordsTheory.word_T_def,
            wordsTheory.word_lo_n2w, wordsTheory.UINT_MAX_def] >>
      fs [wordsTheory.dimword_def, arithmeticTheory.LESS_MOD]) >>
  `exponent < dimword (:'w) - 1` by decide_tac >>
  simp [smtfp_circuit_endpoint_def, smtfp_rep_finite_n2w_bits,
        binary_ieeeTheory.float_is_finite_Exponent] >>
  irule wordsTheory.WORD_LOWER_NOT_EQ >>
  simp [wordsTheory.WORD_NEG_1, wordsTheory.word_T_def,
        wordsTheory.word_lo_n2w, wordsTheory.UINT_MAX_def] >>
  fs [wordsTheory.dimword_def, arithmeticTheory.LESS_MOD]
QED

Theorem smtfp_circuit_endpoint_value:
  2 <= dimindex (:'w) /\
  1 <= exponent /\ exponent <= dimword (:'w) - 2 /\
  rounded <= 2 ** (dimindex (:'t) + 1) /\
  (rounded < 2 ** dimindex (:'t) ==> exponent = 1) /\
  (rounded = 2 ** (dimindex (:'t) + 1) ==>
   exponent < dimword (:'w) - 2) ==>
  float_to_real
    (smtfp_rep
      (smtfp_circuit_endpoint (format : ('t,'w) smtfp) sign exponent rounded)) =
  (if sign = 0w then &(rounded * 2 ** (exponent - 1))
   else -&(rounded * 2 ** (exponent - 1))) *
  (2 pow 1 / 2 pow (INT_MAX (:'w) + dimindex (:'t)))
Proof
  strip_tac >>
  mp_tac (Q.INST [`format` |-> `format`, `sign` |-> `sign`,
                   `exponent` |-> `exponent`, `rounded` |-> `rounded`]
    smtfp_circuit_endpoint_units) >>
  impl_tac >- simp [] >>
  simp_tac pure_ss [LET_THM] >> strip_tac >>
  Cases_on
    `smtfp_rep
      (smtfp_circuit_endpoint (format : ('t,'w) smtfp) sign exponent rounded)` >>
  full_simp_tac pure_ss [binary_ieeeTheory.float_accessors] >>
  qpat_x_assum `c = sign` (fn th => once_rewrite_tac [th]) >>
  qpat_x_assum `smtfp_circuit_units _ _ = _`
    (fn th => once_rewrite_tac [GSYM th]) >>
  `(<| Sign := sign; Exponent := c0; Significand := c1 |> :
      ('t,'w) float) = float sign c0 c1` by
    simp [binary_ieeeTheory.float_component_equality] >>
  qpat_x_assum
    `(<| Sign := sign; Exponent := c0; Significand := c1 |> :
       ('t,'w) float) = _`
    (fn th => once_rewrite_tac [GSYM th]) >>
  MATCH_ACCEPT_TAC smtfp_circuit_units_value
QED

Theorem smtfp_circuit_endpoint_nonzero:
  2 <= dimindex (:'w) /\
  1 <= exponent /\ exponent <= dimword (:'w) - 2 /\
  0 < rounded /\
  rounded <= 2 ** (dimindex (:'t) + 1) /\
  (rounded < 2 ** dimindex (:'t) ==> exponent = 1) /\
  (rounded = 2 ** (dimindex (:'t) + 1) ==>
   exponent < dimword (:'w) - 2) ==>
  ~float_is_zero
    (smtfp_rep
      (smtfp_circuit_endpoint (format : ('t,'w) smtfp)
        sign exponent rounded))
Proof
  strip_tac >>
  `float_to_real
     (smtfp_rep
       (smtfp_circuit_endpoint (format : ('t,'w) smtfp)
         sign exponent rounded)) =
   (if sign = 0w then &(rounded * 2 ** (exponent - 1))
    else -&(rounded * 2 ** (exponent - 1))) *
   (2 pow 1 / 2 pow (INT_MAX (:'w) + dimindex (:'t)))` by
    (irule smtfp_circuit_endpoint_value >> asm_rewrite_tac []) >>
  rewrite_tac [binary_ieeeTheory.float_is_zero_to_real] >>
  pop_assum (fn th => rewrite_tac [th]) >>
  Cases_on `sign = 0w` >>
  asm_simp_tac realLib.real_ss
    [realTheory.real_div, realTheory.REAL_ENTIRE] >>
  simp [realTheory.REAL_POW_EQ_0]
QED

Theorem smtfp_circuit_adjacent_positive_closest_hi:
  float_is_finite (lo : ('t,'w) float) /\
  float_is_finite hi /\ next_hi lo = hi /\
  0 <= float_to_real lo /\
  float_to_real lo <= x /\ x <= float_to_real hi /\
  float_to_real hi - x <= x - float_to_real lo ==>
  is_closest float_is_finite x hi
Proof
  strip_tac >>
  rw [binary_ieeeTheory.is_closest_def, IN_DEF] >>
  rpt strip_tac >>
  Cases_on `abs (float_to_real b) <= abs (float_to_real lo)`
  >- (`float_to_real b <= abs (float_to_real b)` by
        MATCH_ACCEPT_TAC
          (Q.SPEC `float_to_real b` realTheory.ABS_LE) >>
      `abs (float_to_real lo) = float_to_real lo` by simp [] >>
      `float_to_real b <= x` by realLib.REAL_ASM_ARITH_TAC >>
      `0 <= float_to_real (next_hi lo) - x` by
        realLib.REAL_ASM_ARITH_TAC >>
      `0 <= x - float_to_real b` by realLib.REAL_ASM_ARITH_TAC >>
      `abs (float_to_real (next_hi lo) - x) =
       float_to_real (next_hi lo) - x` by simp [] >>
      `abs (float_to_real b - x) = x - float_to_real b` by
        (`float_to_real b - x = -(x - float_to_real b)` by
           realLib.REAL_ASM_ARITH_TAC >>
         asm_rewrite_tac [realTheory.ABS_NEG] >> simp []) >>
      realLib.REAL_ASM_ARITH_TAC) >>
  `abs (float_to_real (next_hi lo)) <= abs (float_to_real b)` by
    (irule binary_ieeeTheory.next_hi_discrete >>
     simp [] >> realLib.REAL_ASM_ARITH_TAC) >>
  Cases_on `0 <= float_to_real b`
  >- (`0 <= float_to_real (next_hi lo)` by
        realLib.REAL_ASM_ARITH_TAC >>
      `abs (float_to_real (next_hi lo)) =
       float_to_real (next_hi lo)` by simp [] >>
      `abs (float_to_real b) = float_to_real b` by simp [] >>
      `float_to_real (next_hi lo) <= float_to_real b` by
        realLib.REAL_ASM_ARITH_TAC >>
      `0 <= float_to_real (next_hi lo) - x` by
        realLib.REAL_ASM_ARITH_TAC >>
      `0 <= float_to_real b - x` by realLib.REAL_ASM_ARITH_TAC >>
      `abs (float_to_real (next_hi lo) - x) =
       float_to_real (next_hi lo) - x` by simp [] >>
      `abs (float_to_real b - x) = float_to_real b - x` by
        simp [] >>
      realLib.REAL_ASM_ARITH_TAC)
  >> `float_to_real b <= 0` by realLib.REAL_ASM_ARITH_TAC >>
  `0 <= float_to_real (next_hi lo) - x` by
    realLib.REAL_ASM_ARITH_TAC >>
  `0 <= x - float_to_real b` by realLib.REAL_ASM_ARITH_TAC >>
  `abs (float_to_real (next_hi lo) - x) =
   float_to_real (next_hi lo) - x` by simp [] >>
  `abs (float_to_real b - x) = x - float_to_real b` by
    (`float_to_real b - x = -(x - float_to_real b)` by
       realLib.REAL_ASM_ARITH_TAC >>
     asm_rewrite_tac [realTheory.ABS_NEG] >> simp []) >>
  realLib.REAL_ASM_ARITH_TAC
QED

Theorem smtfp_circuit_adjacent_positive_closest_lo:
  float_is_finite (lo : ('t,'w) float) /\
  float_is_finite hi /\ next_hi lo = hi /\
  0 <= float_to_real lo /\
  float_to_real lo <= x /\ x <= float_to_real hi /\
  x - float_to_real lo <= float_to_real hi - x ==>
  is_closest float_is_finite x lo
Proof
  strip_tac >>
  rw [binary_ieeeTheory.is_closest_def, IN_DEF] >>
  rpt strip_tac >>
  Cases_on `abs (float_to_real b) <= abs (float_to_real lo)`
  >- (`float_to_real b <= abs (float_to_real b)` by
        MATCH_ACCEPT_TAC
          (Q.SPEC `float_to_real b` realTheory.ABS_LE) >>
      `abs (float_to_real lo) = float_to_real lo` by simp [] >>
      `float_to_real b <= float_to_real lo` by
        realLib.REAL_ASM_ARITH_TAC >>
      `0 <= x - float_to_real lo` by realLib.REAL_ASM_ARITH_TAC >>
      `0 <= x - float_to_real b` by realLib.REAL_ASM_ARITH_TAC >>
      `abs (float_to_real lo - x) = x - float_to_real lo` by
        (`float_to_real lo - x = -(x - float_to_real lo)` by
           realLib.REAL_ASM_ARITH_TAC >>
         asm_rewrite_tac [realTheory.ABS_NEG] >> simp []) >>
      `abs (float_to_real b - x) = x - float_to_real b` by
        (`float_to_real b - x = -(x - float_to_real b)` by
           realLib.REAL_ASM_ARITH_TAC >>
         asm_rewrite_tac [realTheory.ABS_NEG] >> simp []) >>
      realLib.REAL_ASM_ARITH_TAC) >>
  `abs (float_to_real (next_hi lo)) <= abs (float_to_real b)` by
    (irule binary_ieeeTheory.next_hi_discrete >>
     simp [] >> realLib.REAL_ASM_ARITH_TAC) >>
  Cases_on `0 <= float_to_real b`
  >- (`0 <= float_to_real (next_hi lo)` by
        realLib.REAL_ASM_ARITH_TAC >>
      `abs (float_to_real (next_hi lo)) =
       float_to_real (next_hi lo)` by simp [] >>
      `abs (float_to_real b) = float_to_real b` by simp [] >>
      `float_to_real (next_hi lo) <= float_to_real b` by
        realLib.REAL_ASM_ARITH_TAC >>
      `0 <= x - float_to_real lo` by realLib.REAL_ASM_ARITH_TAC >>
      `0 <= float_to_real b - x` by realLib.REAL_ASM_ARITH_TAC >>
      `abs (float_to_real lo - x) = x - float_to_real lo` by
        (`float_to_real lo - x = -(x - float_to_real lo)` by
           realLib.REAL_ASM_ARITH_TAC >>
         asm_rewrite_tac [realTheory.ABS_NEG] >> simp []) >>
      `abs (float_to_real b - x) = float_to_real b - x` by
        simp [] >>
      realLib.REAL_ASM_ARITH_TAC)
  >> `float_to_real b <= 0` by realLib.REAL_ASM_ARITH_TAC >>
  `0 <= x - float_to_real lo` by realLib.REAL_ASM_ARITH_TAC >>
  `0 <= x - float_to_real b` by realLib.REAL_ASM_ARITH_TAC >>
  `abs (float_to_real lo - x) = x - float_to_real lo` by
    (`float_to_real lo - x = -(x - float_to_real lo)` by
       realLib.REAL_ASM_ARITH_TAC >>
     asm_rewrite_tac [realTheory.ABS_NEG] >> simp []) >>
  `abs (float_to_real b - x) = x - float_to_real b` by
    (`float_to_real b - x = -(x - float_to_real b)` by
       realLib.REAL_ASM_ARITH_TAC >>
     asm_rewrite_tac [realTheory.ABS_NEG] >> simp []) >>
  realLib.REAL_ASM_ARITH_TAC
QED

Theorem smtfp_circuit_effective_encoded:
  1 <= maximum_exponent ==>
  smtfp_circuit_effective_exponent maximum_exponent fraction_width
      scale magnitude =
    smtfp_circuit_encoded_exponent maximum_exponent fraction_width
      scale magnitude /\
  1 <= smtfp_circuit_encoded_exponent maximum_exponent fraction_width
      scale magnitude /\
  smtfp_circuit_encoded_exponent maximum_exponent fraction_width
      scale magnitude <= maximum_exponent
Proof
  strip_tac >>
  simp [smtfp_circuit_effective_exponent_def,
        smtfp_circuit_encoded_exponent_def,
        smtfp_circuit_wanted_exponent_def,
        arithmeticTheory.MIN_ALT, arithmeticTheory.MAX_ALT] >>
  decide_tac
QED

Theorem circuit_normalized_lower:
  0 < (units : num) /\ 1 <= maximum_exponent /\
  effective_exponent =
    MIN maximum_exponent
      (MAX 1 (LOG2 (units : num) + 1 - fraction_width)) /\
  1 < effective_exponent ==>
  2 ** fraction_width * 2 ** (effective_exponent - 1) <= (units : num)
Proof
  strip_tac >>
  rewrite_tac [GSYM arithmeticTheory.EXP_ADD] >>
  irule arithmeticTheory.LESS_EQ_TRANS >>
  qexists_tac `2 ** LOG2 units` >>
  conj_tac
  >- (simp [arithmeticTheory.EXP_BASE_LE_MONO] >>
      fs [arithmeticTheory.MIN_ALT, arithmeticTheory.MAX_ALT] >>
      decide_tac) >>
  rewrite_tac [bitTheory.LOG2_def] >>
  MATCH_MP_TAC
    (Q.SPEC `(units : num)` logrootTheory.TWO_EXP_LOG2_LE) >>
  simp []
QED

Theorem smtfp_circuit_quotient_normalized_lower:
  0 < scale /\ 0 < magnitude /\ 1 <= maximum_exponent ==>
  let exponent =
    smtfp_circuit_encoded_exponent maximum_exponent fraction_width
      scale magnitude in
  let quotient =
    smtfp_circuit_quotient maximum_exponent fraction_width scale
      magnitude in
    quotient < 2 ** fraction_width ==> exponent = 1
Proof
  simp_tac pure_ss [LET_THM] >> strip_tac >>
  mp_tac (Q.INST
    [`maximum_exponent` |-> `maximum_exponent`,
     `fraction_width` |-> `fraction_width`, `scale` |-> `scale`,
     `magnitude` |-> `magnitude`]
    smtfp_circuit_effective_encoded) >>
  impl_tac >- simp [] >> strip_tac >>
  Cases_on
    `smtfp_circuit_encoded_exponent maximum_exponent fraction_width
       scale magnitude = 1` >> simp [] >>
  `1 < smtfp_circuit_encoded_exponent maximum_exponent fraction_width
       scale magnitude` by decide_tac >>
  `0 < magnitude * 2 ** (scale - 1)` by simp [] >>
  mp_tac (Q.INST
    [`units` |-> `magnitude * 2 ** (scale - 1)`,
     `maximum_exponent` |-> `maximum_exponent`,
     `fraction_width` |-> `fraction_width`,
     `effective_exponent` |->
       `smtfp_circuit_encoded_exponent maximum_exponent fraction_width
          scale magnitude`] circuit_normalized_lower) >>
  impl_tac >-
    (simp [] >>
     fs [circuit_wanted_exponent_units,
         smtfp_circuit_encoded_exponent_def]) >>
  strip_tac >>
  mp_tac (Q.INST
    [`maximum_exponent` |-> `maximum_exponent`,
     `fraction_width` |-> `fraction_width`, `scale` |-> `scale`,
     `magnitude` |-> `magnitude`]
    smtfp_circuit_quotient_units) >>
  impl_tac >- simp [] >> strip_tac >>
  fs [] >>
  strip_tac >>
  `magnitude * 2 ** (scale - 1) <
   2 ** fraction_width *
     2 **
       (smtfp_circuit_encoded_exponent maximum_exponent fraction_width
          scale magnitude - 1)` by
    (mp_tac (Q.SPECL
      [`2 ** fraction_width`, `magnitude * 2 ** (scale - 1)`,
       `2 **
         (smtfp_circuit_encoded_exponent maximum_exponent fraction_width
            scale magnitude - 1)`] arithmeticTheory.DIV_LT_X) >>
     simp []) >>
  decide_tac
QED

Theorem smtfp_circuit_pack_endpoint:
  maximum_exponent <> 0 /\
  rounded <= 2 ** (fraction_width + 1) /\
  (rounded = 2 ** (fraction_width + 1) ==>
   exponent < maximum_exponent) ==>
  smtfp_circuit_pack mode (format : ('t,'w) smtfp) sign
      maximum_exponent fraction_width exponent rounded =
  if rounded < 2 ** fraction_width then
    smtfp_bits sign 0w (n2w rounded)
  else if rounded = 2 ** (fraction_width + 1) then
    smtfp_bits sign (n2w (exponent + 1)) 0w
  else
    smtfp_bits sign (n2w exponent)
      (n2w (rounded - 2 ** fraction_width))
Proof
  strip_tac >>
  Cases_on `rounded < 2 ** fraction_width`
  >- (`(2 : num) ** fraction_width < 2 ** (fraction_width + 1)` by
        simp [arithmeticTheory.EXP_BASE_LT_MONO] >>
      simp [smtfp_circuit_pack_def]) >>
  Cases_on `rounded = 2 ** (fraction_width + 1)`
  >- simp [smtfp_circuit_pack_def] >>
  simp [smtfp_circuit_pack_def]
QED

Theorem smtfp_circuit_pack_overflow:
  maximum_exponent <> 0 /\
  (2 ** (fraction_width + 1) < rounded \/
   rounded = 2 ** (fraction_width + 1) /\
   ~(exponent < maximum_exponent)) ==>
  smtfp_circuit_pack mode (format : ('t,'w) smtfp) sign
      maximum_exponent fraction_width exponent rounded =
  smtfp_circuit_overflow mode format sign
Proof
  simp [smtfp_circuit_pack_def]
QED

Theorem smtfp_circuit_encode_endpoint:
  2 <= dimindex (:'w) /\ 0 < magnitude /\
  (let maximum_exponent = dimword (:'w) - 2 in
   let fraction_width = dimindex (:'t) in
   let exponent =
     smtfp_circuit_encoded_exponent maximum_exponent fraction_width
       scale magnitude in
   let rounded =
     smtfp_circuit_rounded mode sign maximum_exponent fraction_width
       scale magnitude in
    rounded <= 2 ** (fraction_width + 1) /\
    (rounded = 2 ** (fraction_width + 1) ==>
     exponent < maximum_exponent)) ==>
  smtfp_circuit_encode mode (format : ('t,'w) smtfp) sign scale magnitude =
  smtfp_circuit_endpoint format sign
    (smtfp_circuit_encoded_exponent (dimword (:'w) - 2)
      (dimindex (:'t)) scale magnitude)
    (smtfp_circuit_rounded mode sign (dimword (:'w) - 2)
      (dimindex (:'t)) scale magnitude)
Proof
  simp_tac pure_ss [LET_THM] >> strip_tac >>
  `2 < dimword (:'w)` by
    (simp [wordsTheory.dimword_def] >>
     irule arithmeticTheory.LESS_LESS_EQ_TRANS >>
     qexists_tac `2 ** 2` >> simp []) >>
  simp [smtfp_circuit_encode_def,
        smtfp_circuit_pack_def,
        smtfp_circuit_endpoint_def] >>
  Cases_on
    `smtfp_circuit_rounded mode sign (dimword (:'w) - 2)
       (dimindex (:'t)) scale magnitude =
     2 ** (dimindex (:'t) + 1)`
  >- simp [arithmeticTheory.EXP_BASE_LT_MONO] >>
  Cases_on
    `smtfp_circuit_rounded mode sign (dimword (:'w) - 2)
       (dimindex (:'t)) scale magnitude <
     2 ** dimindex (:'t)` >>
  simp []
QED

Theorem smtfp_circuit_endpoint_ULP:
  2 <= dimindex (:'w) /\
  1 <= exponent /\ exponent <= dimword (:'w) - 2 /\
  rounded <= 2 ** (dimindex (:'t) + 1) /\
  (rounded < 2 ** dimindex (:'t) ==> exponent = 1) /\
  (rounded = 2 ** (dimindex (:'t) + 1) ==>
   exponent < dimword (:'w) - 2) ==>
  ULP
    ((smtfp_rep
       (smtfp_circuit_endpoint (format : ('t,'w) smtfp) sign exponent rounded)).Exponent,
     (:'t)) =
  2 pow
    (if rounded = 2 ** (dimindex (:'t) + 1) then exponent + 1
     else exponent) /
  2 pow (INT_MAX (:'w) + dimindex (:'t))
Proof
  strip_tac >>
  Cases_on `rounded < 2 ** dimindex (:'t)`
  >- (`(2 : num) ** dimindex (:'t) <
       2 ** (dimindex (:'t) + 1)` by
        simp [arithmeticTheory.EXP_BASE_LT_MONO] >>
      simp [smtfp_circuit_endpoint_def, smtfp_rep_finite_n2w_bits,
            binary_ieeeTheory.ULP_def]) >>
  Cases_on `rounded = 2 ** (dimindex (:'t) + 1)`
  >- (`exponent + 1 < dimword (:'w) - 1` by
        decide_tac >>
      `exponent + 1 < dimword (:'w)` by decide_tac >>
      simp [smtfp_circuit_endpoint_def, smtfp_rep_finite_n2w_bits,
            binary_ieeeTheory.ULP_def, wordsTheory.w2n_n2w,
            arithmeticTheory.LESS_MOD]) >>
  `exponent < dimword (:'w) - 1` by decide_tac >>
  `exponent < dimword (:'w)` by decide_tac >>
  simp [smtfp_circuit_endpoint_def, smtfp_rep_finite_n2w_bits,
        binary_ieeeTheory.ULP_def, wordsTheory.w2n_n2w,
        arithmeticTheory.LESS_MOD]
QED

Theorem smtfp_circuit_endpoint_even:
  2 <= dimindex (:'w) /\
  1 <= exponent /\ exponent <= dimword (:'w) - 2 /\
  rounded <= 2 ** (dimindex (:'t) + 1) /\
  2 ** dimindex (:'t) <= rounded /\
  (rounded = 2 ** (dimindex (:'t) + 1) ==>
   exponent < dimword (:'w) - 2) ==>
  (~word_lsb
    (smtfp_rep
      (smtfp_circuit_endpoint (format : ('t,'w) smtfp) sign exponent rounded)).Significand
   <=> EVEN rounded)
Proof
  strip_tac >>
  Cases_on `rounded = 2 ** (dimindex (:'t) + 1)`
  >- (`exponent + 1 < dimword (:'w) - 1` by decide_tac >>
      simp [smtfp_circuit_endpoint_def, smtfp_rep_finite_n2w_bits,
            arithmeticTheory.EVEN_EXP]) >>
  `rounded < 2 ** (dimindex (:'t) + 1)` by decide_tac >>
  `exponent < dimword (:'w) - 1` by decide_tac >>
  simp [smtfp_circuit_endpoint_def, smtfp_rep_finite_n2w_bits,
        wordsTheory.word_lsb_n2w] >>
  `EVEN (2 ** dimindex (:'t))` by
    simp [arithmeticTheory.EVEN_EXP] >>
  fs [arithmeticTheory.ODD_EVEN, arithmeticTheory.EVEN_SUB]
QED

Theorem smtfp_circuit_endpoint_even_finite:
  2 <= dimindex (:'w) /\
  1 <= exponent /\ exponent <= dimword (:'w) - 2 /\
  rounded <= 2 ** (dimindex (:'t) + 1) /\
  (rounded < 2 ** dimindex (:'t) ==> exponent = 1) /\
  (rounded = 2 ** (dimindex (:'t) + 1) ==>
   exponent < dimword (:'w) - 2) ==>
  (~word_lsb
    (smtfp_rep
      (smtfp_circuit_endpoint (format : ('t,'w) smtfp) sign exponent rounded)).Significand
   <=> EVEN rounded)
Proof
  strip_tac >>
  Cases_on `rounded < 2 ** dimindex (:'t)`
  >- simp [smtfp_circuit_endpoint_def, smtfp_rep_finite_n2w_bits,
           wordsTheory.word_lsb_n2w, arithmeticTheory.ODD_EVEN] >>
  Cases_on `rounded = 2 ** (dimindex (:'t) + 1)`
  >- (`exponent + 1 < dimword (:'w) - 1` by decide_tac >>
      simp [smtfp_circuit_endpoint_def, smtfp_rep_finite_n2w_bits,
            arithmeticTheory.EVEN_EXP]) >>
  `rounded < 2 ** (dimindex (:'t) + 1)` by decide_tac >>
  `exponent < dimword (:'w) - 1` by decide_tac >>
  simp [smtfp_circuit_endpoint_def, smtfp_rep_finite_n2w_bits,
        wordsTheory.word_lsb_n2w] >>
  `EVEN (2 ** dimindex (:'t))` by
    simp [arithmeticTheory.EVEN_EXP] >>
  fs [arithmeticTheory.ODD_EVEN, arithmeticTheory.EVEN_SUB]
QED

Theorem smtfp_float_value_finite:
  float_is_finite (f : ('t,'w) float) ==>
  float_value f = Float (float_to_real f)
Proof
  strip_tac >>
  Cases_on `f.Exponent = UINT_MAXw` >>
  fs [binary_ieeeTheory.float_is_finite_thm,
      binary_ieeeTheory.float_value_def] >>
  Cases_on `f.Significand = 0w` >> fs []
QED

Theorem smtfp_circuit_endpoint_boundary:
  2 <= dimindex (:'w) /\
  1 <= exponent /\ exponent <= dimword (:'w) - 2 /\
  0 < quotient /\
  quotient <= rounded /\ rounded <= quotient + 1 /\
  rounded <= 2 ** (dimindex (:'t) + 1) /\
  (quotient < 2 ** dimindex (:'t) ==> exponent = 1) /\
  rounded <> 2 ** (dimindex (:'t) + 1) /\
  (smtfp_rep
    (smtfp_circuit_endpoint (format : ('t,'w) smtfp) sign exponent
      rounded)).Significand = 0w /\
  (smtfp_rep
    (smtfp_circuit_endpoint (format : ('t,'w) smtfp) sign exponent
      rounded)).Exponent <> 1w ==>
  rounded * divisor <= quotient * divisor + residue
Proof
  strip_tac >>
  Cases_on `rounded < 2 ** dimindex (:'t)`
  >- (`smtfp_rep
         (smtfp_circuit_endpoint (format : ('t,'w) smtfp) sign exponent
           rounded) =
       (<| Sign := sign; Exponent := 0w; Significand := n2w rounded |> :
         ('t,'w) float)` by
        simp [smtfp_circuit_endpoint_def, smtfp_rep_finite_n2w_bits] >>
      fs [wordsTheory.n2w_11, wordsTheory.dimword_def,
          arithmeticTheory.LESS_MOD]) >>
  `rounded < 2 ** (dimindex (:'t) + 1)` by decide_tac >>
  `exponent < dimword (:'w) - 1` by decide_tac >>
  `rounded - 2 ** dimindex (:'t) < dimword (:'t)` by
    (simp [wordsTheory.dimword_def] >>
     qpat_x_assum `rounded < 2 ** (dimindex (:'t) + 1)` mp_tac >>
     simp [arithmeticTheory.EXP_ADD]) >>
  `smtfp_rep
     (smtfp_circuit_endpoint (format : ('t,'w) smtfp) sign exponent
       rounded) =
   (<| Sign := sign; Exponent := n2w exponent;
       Significand := n2w (rounded - 2 ** dimindex (:'t)) |> :
     ('t,'w) float)` by
    simp [smtfp_circuit_endpoint_def, smtfp_rep_finite_n2w_bits] >>
  `rounded = 2 ** dimindex (:'t)` by
    (qpat_x_assum `(smtfp_rep _).Significand = 0w` mp_tac >>
     asm_rewrite_tac [] >>
     simp [wordsTheory.n2w_11, arithmeticTheory.LESS_MOD]) >>
  Cases_on `quotient = rounded`
  >- simp [] >>
  `quotient < rounded` by decide_tac >>
  `exponent = 1` by metis_tac [] >>
  qpat_x_assum `(smtfp_rep _).Exponent <> 1w` mp_tac >>
  asm_rewrite_tac [] >> simp []
QED

Theorem smtfp_circuit_RNE_error_bound:
  residue < divisor ==>
  2 *
    (if smtfp_circuit_round_up RNE sign quotient residue divisor then
       divisor - residue
     else residue) <= divisor
Proof
  strip_tac >>
  Cases_on
    `smtfp_circuit_round_up RNE sign quotient residue divisor` >>
  fs [smtfp_circuit_round_up_def] >>
  decide_tac
QED

Theorem smtfp_circuit_scaled_abs_diff:
  abs (&left * scale - &right * scale) =
  &(ABS_DIFF left right) * abs scale
Proof
  rewrite_tac [GSYM realTheory.REAL_SUB_RDISTRIB,
               realTheory.ABS_MUL] >>
  Cases_on `left < right`
  >- (`~(right <= left)` by decide_tac >>
      simp [arithmeticTheory.ABS_DIFF_def,
            realTheory.REAL_OF_NUM_SUB,
            realTheory.REAL_SUB_LE,
            realTheory.abs] >>
      realLib.REAL_ARITH_TAC) >>
  `right <= left` by decide_tac >>
  simp [arithmeticTheory.ABS_DIFF_def,
        realTheory.REAL_OF_NUM_SUB,
        realTheory.REAL_SUB_LE,
        realTheory.abs]
QED

Theorem smtfp_circuit_scaled_abs_diff_neg:
  abs (-&left * scale - -&right * scale) =
  &(ABS_DIFF left right) * abs scale
Proof
  rewrite_tac [realTheory.REAL_MUL_LNEG,
               realTheory.REAL_SUB_NEG2] >>
  once_rewrite_tac [arithmeticTheory.ABS_DIFF_SYM] >>
  MATCH_ACCEPT_TAC smtfp_circuit_scaled_abs_diff
QED

Theorem smtfp_circuit_scaled_abs_diff_neg_left:
  abs (-(scale : real) * (&left * factor) -
       -scale * (&right * factor)) =
  &(ABS_DIFF left right) * abs (scale * factor)
Proof
  irule EQ_TRANS >>
  qexists_tac
    `abs (-&left * (scale * factor) -
          -&right * (scale * factor))` >>
  conj_tac
  >- (`scale * (&left * factor) =
       &left * (scale * factor)` by
        CONV_TAC (AC_CONV (realTheory.REAL_MUL_ASSOC,
                           realTheory.REAL_MUL_COMM)) >>
      `scale * (&right * factor) =
       &right * (scale * factor)` by
        CONV_TAC (AC_CONV (realTheory.REAL_MUL_ASSOC,
                           realTheory.REAL_MUL_COMM)) >>
      rewrite_tac [realTheory.REAL_MUL_LNEG] >>
      asm_rewrite_tac [])
  >- ACCEPT_TAC
        (Q.SPECL [`scale * factor`, `right`, `left`]
           (GEN_ALL smtfp_circuit_scaled_abs_diff_neg))
QED

Theorem smtfp_circuit_tie_divisor:
  residue < divisor /\ 0 < (scale : real) /\
  2 * &(if up then divisor - residue else residue) * scale =
    &divisor * scale ==>
  divisor = 2 * residue
Proof
  strip_tac >>
  `2 * &(if up then divisor - residue else residue) = &divisor` by
    (qpat_x_assum `_ * scale = _ * scale` mp_tac >>
     simp [realTheory.REAL_EQ_RMUL] >>
     realLib.REAL_ASM_ARITH_TAC) >>
  `(2 : real) = &(2 : num)` by simp [] >>
  `2 * (if up then divisor - residue else residue) = divisor` by
    (qpat_x_assum `2 * &_ = &divisor` mp_tac >>
     asm_rewrite_tac [realTheory.REAL_OF_NUM_MUL,
                      realTheory.REAL_OF_NUM_EQ]) >>
  Cases_on `up` >> fs [] >> decide_tac
QED

Theorem smtfp_circuit_ULP_scale:
  !d n : num.
    &(2 * d) / &(2 ** n) =
    &d * (&(2 ** 1) / &(2 ** n))
Proof
  simp [realTheory.REAL_OF_NUM_MUL, arithmeticTheory.EXP,
        realTheory.real_div] >>
  CONV_TAC RealField.REAL_RING
QED

Theorem smtfp_circuit_endpoint_ULP_divisor:
  2 <= dimindex (:'w) /\
  1 <= exponent /\ exponent <= dimword (:'w) - 2 /\
  rounded <= 2 ** (dimindex (:'t) + 1) /\
  (rounded < 2 ** dimindex (:'t) ==> exponent = 1) /\
  (rounded = 2 ** (dimindex (:'t) + 1) ==>
   exponent < dimword (:'w) - 2) /\
  divisor = 2 ** (exponent - 1) ==>
  &divisor *
    (2 pow 1 / 2 pow (INT_MAX (:'w) + dimindex (:'t))) <=
  ULP
    ((smtfp_rep
       (smtfp_circuit_endpoint (format : ('t,'w) smtfp) sign exponent
         rounded)).Exponent,
     (:'t))
Proof
  strip_tac >>
  mp_tac (Q.INST
    [`format` |-> `format`, `sign` |-> `sign`,
     `exponent` |-> `exponent`, `rounded` |-> `rounded`]
    smtfp_circuit_endpoint_ULP) >>
  impl_tac >- simp [] >>
  `exponent = exponent - 1 + 1` by decide_tac >>
  `2 ** exponent = 2 * 2 ** (exponent - 1)` by
    (qpat_x_assum `exponent = exponent - 1 + 1`
       (once_rewrite_tac o single) >>
     simp [arithmeticTheory.EXP_ADD,
           arithmeticTheory.MULT_COMM]) >>
  simp [realTheory.REAL_OF_NUM_POW,
        realTheory.REAL_POW_ADD] >>
  Cases_on `rounded = 2 ** (dimindex (:'t) + 1)` >>
  fs [] >>
  strip_tac >>
  fs [arithmeticTheory.EXP_ADD] >>
  decide_tac
QED

Theorem smtfp_circuit_RNE_positive_endpoint:
  2 <= dimindex (:'w) /\
  1 <= exponent /\ exponent <= dimword (:'w) - 2 /\
  0 < quotient /\
  quotient < 2 ** (dimindex (:'t) + 1) /\
  quotient + 1 <= 2 ** (dimindex (:'t) + 1) /\
  (quotient < 2 ** dimindex (:'t) ==> exponent = 1) /\
  (quotient + 1 = 2 ** (dimindex (:'t) + 1) ==>
   exponent < dimword (:'w) - 2) /\
  divisor = 2 ** (exponent - 1) /\
  residue < divisor ==>
  let units = quotient * divisor + residue in
  let rounded =
    smtfp_circuit_round RNE 0w quotient residue divisor in
  let output =
    smtfp_rep
      (smtfp_circuit_endpoint (format : ('t,'w) smtfp) 0w exponent rounded) in
  smt_float_round RNE F
    (&units *
      (2 pow 1 / 2 pow (INT_MAX (:'w) + dimindex (:'t)))) = output
Proof
  simp_tac pure_ss [LET_THM] >> strip_tac >>
  `0 < divisor` by simp [] >>
  `quotient <=
     smtfp_circuit_round RNE 0w quotient residue divisor /\
   smtfp_circuit_round RNE 0w quotient residue divisor <= quotient + 1` by
    (mp_tac (Q.INST
       [`mode` |-> `RNE`, `sign` |-> `(0w : word1)`,
        `q` |-> `quotient`, `residue` |-> `residue`,
        `divisor` |-> `divisor`]
       smtfp_circuit_round_bounds) >>
     decide_tac) >>
  `smtfp_circuit_round RNE 0w quotient residue divisor <=
   2 ** (dimindex (:'t) + 1)` by
    (mp_tac (Q.INST
       [`mode` |-> `RNE`, `sign` |-> `(0w : word1)`,
        `q` |-> `quotient`, `residue` |-> `residue`,
        `divisor` |-> `divisor`]
       smtfp_circuit_round_bounds) >>
     decide_tac) >>
  `(smtfp_circuit_round RNE 0w quotient residue divisor <
      2 ** dimindex (:'t) ==> exponent = 1)` by
    (mp_tac (Q.INST
       [`mode` |-> `RNE`, `sign` |-> `(0w : word1)`,
        `q` |-> `quotient`, `residue` |-> `residue`,
        `divisor` |-> `divisor`]
       smtfp_circuit_round_bounds) >>
     decide_tac) >>
  `(smtfp_circuit_round RNE 0w quotient residue divisor =
      2 ** (dimindex (:'t) + 1) ==>
    exponent < dimword (:'w) - 2)` by
    (mp_tac (Q.INST
       [`mode` |-> `RNE`, `sign` |-> `(0w : word1)`,
        `q` |-> `quotient`, `residue` |-> `residue`,
        `divisor` |-> `divisor`]
       smtfp_circuit_round_bounds) >>
     decide_tac) >>
  `float_is_finite
    (smtfp_rep
      (smtfp_circuit_endpoint (format : ('t,'w) smtfp) 0w exponent
        (smtfp_circuit_round RNE 0w quotient residue divisor)))` by
    (irule smtfp_circuit_endpoint_finite >> simp []) >>
  `float_to_real
    (smtfp_rep
      (smtfp_circuit_endpoint (format : ('t,'w) smtfp) 0w exponent
        (smtfp_circuit_round RNE 0w quotient residue divisor))) =
   &(smtfp_circuit_round RNE 0w quotient residue divisor * divisor) *
     (2 pow 1 / 2 pow (INT_MAX (:'w) + dimindex (:'t)))` by
    (irule EQ_TRANS >>
     qexists_tac
       `&(smtfp_circuit_round RNE 0w quotient residue divisor *
           2 ** (exponent - 1)) *
        (2 pow 1 / 2 pow (INT_MAX (:'w) + dimindex (:'t)))` >>
     conj_tac
     >- (mp_tac (Q.INST
           [`format` |-> `format`, `sign` |-> `(0w : word1)`,
            `exponent` |-> `exponent`,
            `rounded` |->
              `smtfp_circuit_round RNE 0w quotient residue divisor`]
           smtfp_circuit_endpoint_value) >>
         impl_tac >- simp [] >>
         simp [])
     >> fs []) >>
  `~float_is_zero
    (smtfp_rep
      (smtfp_circuit_endpoint (format : ('t,'w) smtfp) 0w exponent
        (smtfp_circuit_round RNE 0w quotient residue divisor)))` by
    (simp [binary_ieeeTheory.float_is_zero_to_real] >>
     mp_tac (Q.INST
       [`mode` |-> `RNE`, `sign` |-> `(0w : word1)`,
        `q` |-> `quotient`, `residue` |-> `residue`,
        `divisor` |-> `2 ** (exponent - 1)`]
     smtfp_circuit_round_bounds) >>
     decide_tac) >>
  `float_is_finite
    (smtfp_rep
      (smtfp_circuit_endpoint (format : ('t,'w) smtfp) 0w exponent
        (quotient + 1)))` by
    (irule smtfp_circuit_endpoint_finite >> simp [] >> decide_tac) >>
  `float_to_real
    (smtfp_rep
      (smtfp_circuit_endpoint (format : ('t,'w) smtfp) 0w exponent
        (quotient + 1))) =
   &((quotient + 1) * divisor) *
     (2 pow 1 / 2 pow (INT_MAX (:'w) + dimindex (:'t)))` by
    (mp_tac (Q.INST
       [`format` |-> `format`, `sign` |-> `(0w : word1)`,
        `exponent` |-> `exponent`, `rounded` |-> `quotient + 1`]
       smtfp_circuit_endpoint_value) >>
     impl_tac >- (simp [] >> decide_tac) >>
     fs []) >>
  `0 < quotient * divisor` by simp [] >>
  `0 < quotient * divisor + residue` by decide_tac >>
  `0 <
    &(quotient * divisor + residue) *
      (2 pow 1 / 2 pow (INT_MAX (:'w) + dimindex (:'t)))` by
    (irule realTheory.REAL_LT_MUL >>
     simp [realTheory.REAL_POW_LT]) >>
  `&(quotient * divisor + residue) *
      (2 pow 1 / 2 pow (INT_MAX (:'w) + dimindex (:'t))) <
   &((quotient + 1) * divisor) *
      (2 pow 1 / 2 pow (INT_MAX (:'w) + dimindex (:'t)))` by
    (simp [realTheory.REAL_OF_NUM_ADD,
           realTheory.REAL_OF_NUM_MUL] >>
     realLib.REAL_ASM_ARITH_TAC) >>
  `abs
    (float_to_real
      (smtfp_rep
        (smtfp_circuit_endpoint (format : ('t,'w) smtfp) 0w exponent
          (quotient + 1)))) <= largest (:'t # 'w)` by
    (mp_tac (Q.INST
       [`f` |->
          `smtfp_rep
            (smtfp_circuit_endpoint
              (format : ('t,'w) smtfp) 0w exponent (quotient + 1))`]
       (INST_TYPE [alpha |-> ``:'t``, beta |-> ``:'w``]
          binary_ieeeTheory.abs_float_bounds)) >>
     impl_tac >- simp [] >>
     rewrite_tac [binary_ieeeTheory.float_to_real_float_abs]) >>
  `&(quotient * divisor + residue) *
      (2 pow 1 / 2 pow (INT_MAX (:'w) + dimindex (:'t))) <
   largest (:'t # 'w)` by
    (assume_tac (Q.SPEC
       `float_to_real
          (smtfp_rep
            (smtfp_circuit_endpoint (format : ('t,'w) smtfp) 0w
              exponent (quotient + 1)))`
       realTheory.ABS_LE) >>
     realLib.REAL_ASM_ARITH_TAC) >>
  `&(quotient * divisor + residue) *
      (2 pow 1 / 2 pow (INT_MAX (:'w) + dimindex (:'t))) <
   threshold (:'t # 'w)` by
    (mp_tac (INST_TYPE [alpha |-> ``:'t``, beta |-> ``:'w``]
       binary_ieeeTheory.largest_lt_threshold) >>
     realLib.REAL_ASM_ARITH_TAC) >>
  `abs
    (&(quotient * divisor + residue) *
      (2 pow 1 / 2 pow (INT_MAX (:'w) + dimindex (:'t)))) =
   &(quotient * divisor + residue) *
     (2 pow 1 / 2 pow (INT_MAX (:'w) + dimindex (:'t)))` by
    (irule realTheory.ABS_REDUCE >> realLib.REAL_ASM_ARITH_TAC) >>
  `0 < residue + quotient * 2 ** (exponent - 1)` by
    (`0 < quotient * 2 ** (exponent - 1)` by (simp []) >>
     decide_tac) >>
  `ulp (:'t # 'w) <
    2 *
    abs
      (&(quotient * divisor + residue) *
       (2 pow 1 / 2 pow (INT_MAX (:'w) + dimindex (:'t))))` by
    (asm_rewrite_tac [] >>
     simp [binary_ieeeTheory.ulp_def,
           binary_ieeeTheory.ULP_def] >>
     decide_tac) >>
  `(quotient * divisor + residue) DIV divisor = quotient` by
    (irule arithmeticTheory.DIV_UNIQUE >>
     qexists_tac `residue` >>
     simp [arithmeticTheory.ADD_COMM]) >>
  `(quotient * divisor + residue) MOD divisor = residue` by
    (irule arithmeticTheory.MOD_UNIQUE >>
     qexists_tac `quotient` >>
     simp [arithmeticTheory.ADD_COMM]) >>
  `2 *
    abs
      (&(smtfp_circuit_round RNE 0w quotient residue divisor * divisor) *
       (2 pow 1 / 2 pow (INT_MAX (:'w) + dimindex (:'t))) -
       &(quotient * divisor + residue) *
       (2 pow 1 / 2 pow (INT_MAX (:'w) + dimindex (:'t)))) <=
    ULP
      ((smtfp_rep
         (smtfp_circuit_endpoint (format : ('t,'w) smtfp) 0w exponent
           (smtfp_circuit_round RNE 0w quotient residue divisor))).Exponent,
       (:'t))` by
    (`ABS_DIFF
        (smtfp_circuit_round RNE 0w quotient residue divisor * divisor)
        (quotient * divisor + residue) =
      if smtfp_circuit_round_up RNE 0w quotient residue divisor then
        divisor - residue
      else residue` by
       (Cases_on
          `smtfp_circuit_round_up RNE 0w quotient residue divisor` >>
        fs [smtfp_circuit_round_def] >>
        simp [arithmeticTheory.ABS_DIFF_def,
              arithmeticTheory.LEFT_ADD_DISTRIB] >>
        decide_tac) >>
     `abs
        (2 pow 1 / 2 pow (INT_MAX (:'w) + dimindex (:'t))) =
      2 pow 1 / 2 pow (INT_MAX (:'w) + dimindex (:'t))` by
       (irule realTheory.ABS_REDUCE >> simp []) >>
     rewrite_tac [smtfp_circuit_scaled_abs_diff] >>
     qpat_x_assum `ABS_DIFF _ _ = _`
       (fn th => rewrite_tac [th]) >>
     qpat_x_assum
       `abs (2 pow 1 / 2 pow _) = _`
       (fn th => rewrite_tac [th]) >>
     irule realTheory.REAL_LE_TRANS >>
     qexists_tac
       `&divisor *
        (2 pow 1 / 2 pow (INT_MAX (:'w) + dimindex (:'t)))` >>
     conj_tac
     >- (simp [realTheory.REAL_OF_NUM_MUL,
               realTheory.REAL_MUL_ASSOC] >>
         irule smtfp_circuit_RNE_error_bound >> simp []) >>
     irule smtfp_circuit_endpoint_ULP_divisor >> simp []) >>
  Cases_on
    `smtfp_circuit_round RNE 0w quotient residue divisor =
     2 ** (dimindex (:'t) + 1)`
  >- (
      `smtfp_circuit_round RNE 0w quotient residue divisor =
       quotient + 1` by
        (mp_tac (Q.INST
           [`mode` |-> `RNE`, `sign` |-> `(0w : word1)`,
            `q` |-> `quotient`, `residue` |-> `residue`,
            `divisor` |-> `divisor`]
           smtfp_circuit_round_bounds) >>
         decide_tac) >>
      `quotient + 1 = 2 ** (dimindex (:'t) + 1)` by
        metis_tac [] >>
      `smtfp_circuit_round_up RNE 0w quotient residue divisor` by
        (Cases_on
           `smtfp_circuit_round_up RNE 0w quotient residue divisor` >>
         fs [smtfp_circuit_round_def]) >>
      `divisor <= 2 * residue` by
        (fs [smtfp_circuit_round_up_def] >>
         decide_tac) >>
      `exponent < dimword (:'w) - 2` by metis_tac [] >>
      `exponent + 1 < dimword (:'w) - 1` by decide_tac >>
      `smtfp_rep
         (smtfp_circuit_endpoint (format : ('t,'w) smtfp) 0w exponent
           (smtfp_circuit_round RNE 0w quotient residue divisor)) =
       (<| Sign := 0w; Exponent := n2w (exponent + 1);
           Significand := 0w |> : ('t,'w) float)` by
        (qpat_x_assum
           `smtfp_circuit_round RNE 0w quotient residue divisor =
            2 ** (dimindex (:'t) + 1)`
           (fn th => once_rewrite_tac [th]) >>
         simp [smtfp_circuit_endpoint_def,
               smtfp_rep_finite_n2w_bits]) >>
      `exponent + 1 < dimword (:'w)` by decide_tac >>
      `1 < dimword (:'w)` by decide_tac >>
      `(smtfp_rep
         (smtfp_circuit_endpoint (format : ('t,'w) smtfp) 0w exponent
           (smtfp_circuit_round RNE 0w quotient residue divisor))).Significand =
       0w /\
       (smtfp_rep
         (smtfp_circuit_endpoint (format : ('t,'w) smtfp) 0w exponent
           (smtfp_circuit_round RNE 0w quotient residue divisor))).Exponent <>
       1w` by
        (asm_rewrite_tac [] >>
         simp [wordsTheory.n2w_11,
               arithmeticTheory.LESS_MOD]) >>
      `~(abs
          (&(smtfp_circuit_round RNE 0w quotient residue divisor *
             divisor) *
           (2 pow 1 / 2 pow (INT_MAX (:'w) + dimindex (:'t)))) <=
         abs
          (&(quotient * divisor + residue) *
           (2 pow 1 / 2 pow (INT_MAX (:'w) + dimindex (:'t)))))` by
        (qpat_x_assum
           `smtfp_circuit_round RNE 0w quotient residue divisor =
            quotient + 1`
           (fn th => rewrite_tac [th]) >>
         qpat_x_assum
           `abs
              (&(quotient * divisor + residue) *
               (2 pow 1 /
                2 pow (INT_MAX (:'w) + dimindex (:'t)))) = _`
           (fn th => rewrite_tac [th]) >>
         simp [realTheory.abs] >>
         qpat_x_assum
           `quotient + 1 = 2 ** (dimindex (:'t) + 1)`
           (fn th => rewrite_tac [GSYM th]) >>
         simp [arithmeticTheory.LEFT_ADD_DISTRIB,
               arithmeticTheory.RIGHT_ADD_DISTRIB] >>
         decide_tac) >>
      `4 *
        abs
          (&(smtfp_circuit_round RNE 0w quotient residue divisor *
             divisor) *
           (2 pow 1 / 2 pow (INT_MAX (:'w) + dimindex (:'t))) -
           &(quotient * divisor + residue) *
           (2 pow 1 / 2 pow (INT_MAX (:'w) + dimindex (:'t)))) <=
       ULP
         ((smtfp_rep
            (smtfp_circuit_endpoint (format : ('t,'w) smtfp) 0w
              exponent
              (smtfp_circuit_round RNE 0w quotient residue
                divisor))).Exponent,
          (:'t))` by
        (`ABS_DIFF
            (smtfp_circuit_round RNE 0w quotient residue divisor *
             divisor)
            (quotient * divisor + residue) = divisor - residue` by
           (qpat_x_assum
              `smtfp_circuit_round RNE 0w quotient residue divisor =
               quotient + 1`
              (fn th => rewrite_tac [th]) >>
            simp [arithmeticTheory.ABS_DIFF_def,
                  arithmeticTheory.LEFT_ADD_DISTRIB] >>
            decide_tac) >>
         `abs
            (2 pow 1 /
             2 pow (INT_MAX (:'w) + dimindex (:'t))) =
          2 pow 1 /
          2 pow (INT_MAX (:'w) + dimindex (:'t))` by
           (irule realTheory.ABS_REDUCE >> simp []) >>
         rewrite_tac [smtfp_circuit_scaled_abs_diff] >>
         qpat_x_assum `ABS_DIFF _ _ = divisor - residue`
           (fn th => rewrite_tac [th]) >>
         qpat_x_assum `abs (2 pow 1 / 2 pow _) = _`
           (fn th => rewrite_tac [th]) >>
         `4 * (divisor - residue) <= 2 * divisor` by decide_tac >>
         `4 * &(divisor - residue) *
            (2 pow 1 /
             2 pow (INT_MAX (:'w) + dimindex (:'t))) <=
          &(2 * divisor) *
            (2 pow 1 /
             2 pow (INT_MAX (:'w) + dimindex (:'t)))` by
           (irule realTheory.REAL_LE_RMUL_IMP >>
            simp [realTheory.REAL_OF_NUM_MUL]) >>
         `exponent = SUC (exponent - 1)` by decide_tac >>
         `exponent + 1 = SUC exponent` by decide_tac >>
         `2 ** (exponent + 1) = 4 * divisor` by
           (qpat_x_assum `exponent + 1 = SUC exponent`
              (fn th => once_rewrite_tac [th]) >>
            rewrite_tac [CONJUNCT2 arithmeticTheory.EXP] >>
            qpat_x_assum `exponent = SUC (exponent - 1)`
              (fn th => once_rewrite_tac [th]) >>
            rewrite_tac [CONJUNCT2 arithmeticTheory.EXP] >>
            qpat_x_assum `divisor = 2 ** (exponent - 1)`
              (fn th => rewrite_tac [th]) >>
            decide_tac) >>
         mp_tac (Q.INST
           [`format` |-> `format`, `sign` |-> `(0w : word1)`,
            `exponent` |-> `exponent`,
            `rounded` |->
              `smtfp_circuit_round RNE 0w quotient residue divisor`]
           smtfp_circuit_endpoint_ULP) >>
         impl_tac >- simp [] >>
         strip_tac >>
         qpat_x_assum `ULP _ = _`
           (fn th => rewrite_tac [th]) >>
         qpat_x_assum
           `smtfp_circuit_round RNE 0w quotient residue divisor =
            2 ** (dimindex (:'t) + 1)`
           (fn th => rewrite_tac [th]) >>
         simp_tac pure_ss [boolTheory.COND_CLAUSES] >>
         `&(2 * divisor) *
            (2 pow 1 /
             2 pow (INT_MAX (:'w) + dimindex (:'t))) =
          2 pow (exponent + 1) /
          2 pow (INT_MAX (:'w) + dimindex (:'t))` by
           (rewrite_tac [realTheory.REAL_OF_NUM_POW] >>
            qpat_x_assum `2 ** (exponent + 1) = 4 * divisor`
              (fn th => rewrite_tac [th]) >>
            simp [realTheory.REAL_OF_NUM_MUL] >>
            CONV_TAC RealField.REAL_RING) >>
         metis_tac [realTheory.REAL_MUL_ASSOC]) >>
      `round roundTiesToEven
          (&(quotient * divisor + residue) *
           (2 pow 1 / 2 pow (INT_MAX (:'w) + dimindex (:'t)))) =
        smtfp_rep
          (smtfp_circuit_endpoint (format : ('t,'w) smtfp) 0w exponent
            (smtfp_circuit_round RNE 0w quotient residue divisor))` by
        (irule (Q.SPECL
           [`smtfp_rep
              (smtfp_circuit_endpoint (format : ('t,'w) smtfp) 0w
                exponent
                (smtfp_circuit_round RNE 0w quotient residue divisor))`,
            `&(quotient * divisor + residue) *
              (2 pow 1 / 2 pow (INT_MAX (:'w) + dimindex (:'t)))`,
            `&(smtfp_circuit_round RNE 0w quotient residue divisor *
                divisor) *
              (2 pow 1 / 2 pow (INT_MAX (:'w) + dimindex (:'t)))`]
           binary_ieeeTheory.round_roundTiesToEven0) >>
         `float_value
            (smtfp_rep
              (smtfp_circuit_endpoint (format : ('t,'w) smtfp) 0w
                exponent
                (smtfp_circuit_round RNE 0w quotient residue divisor))) =
          Float
            (&(smtfp_circuit_round RNE 0w quotient residue divisor *
                divisor) *
             (2 pow 1 /
              2 pow (INT_MAX (:'w) + dimindex (:'t))))` by
           metis_tac [smtfp_float_value_finite] >>
         conj_tac >- first_assum ACCEPT_TAC >>
         conj_tac >- first_assum ACCEPT_TAC >>
         conj_tac >- first_assum ACCEPT_TAC >>
         conj_tac >- first_assum ACCEPT_TAC >>
         conj_tac
         >- (qpat_x_assum
               `abs
                  (&(quotient * divisor + residue) *
                   (2 pow 1 /
                    2 pow (INT_MAX (:'w) + dimindex (:'t)))) = _`
               (fn th => rewrite_tac [th]) >>
             first_assum ACCEPT_TAC) >>
         conj_tac >- first_assum ACCEPT_TAC >>
         first_assum ACCEPT_TAC) >>
      simp_tac pure_ss [smt_float_round_def, smt_round_def,
                        TypeBase.case_def_of ``:smt_rounding``, LET_THM,
                        boolTheory.COND_CLAUSES] >>
      qpat_x_assum
        `round roundTiesToEven
           (&(quotient * divisor + residue) * _) = _`
        (fn th => rewrite_tac [th]) >>
      qpat_x_assum
        `~float_is_zero
           (smtfp_rep
             (smtfp_circuit_endpoint
               (format : ('t,'w) smtfp) 0w exponent _))`
        (fn th => rewrite_tac [th]) >>
      rewrite_tac [boolTheory.COND_CLAUSES]) >>
  `(2 *
    abs
      (&(smtfp_circuit_round RNE 0w quotient residue divisor * divisor) *
       (2 pow 1 / 2 pow (INT_MAX (:'w) + dimindex (:'t))) -
       &(quotient * divisor + residue) *
       (2 pow 1 / 2 pow (INT_MAX (:'w) + dimindex (:'t)))) =
    ULP
      ((smtfp_rep
         (smtfp_circuit_endpoint (format : ('t,'w) smtfp) 0w exponent
           (smtfp_circuit_round RNE 0w quotient residue divisor))).Exponent,
       (:'t)) ==>
    ~word_lsb
     (smtfp_rep
        (smtfp_circuit_endpoint (format : ('t,'w) smtfp) 0w exponent
          (smtfp_circuit_round RNE 0w quotient residue divisor))).Significand)` by
    (strip_tac >>
     `divisor = 2 * residue` by
       (`ABS_DIFF
           (smtfp_circuit_round RNE 0w quotient residue divisor *
            divisor)
           (quotient * divisor + residue) =
         if smtfp_circuit_round_up RNE 0w quotient residue divisor then
           divisor - residue
         else residue` by
          (Cases_on
             `smtfp_circuit_round_up RNE 0w quotient residue divisor` >>
           fs [smtfp_circuit_round_def] >>
           simp [arithmeticTheory.ABS_DIFF_def,
                 arithmeticTheory.LEFT_ADD_DISTRIB] >>
           decide_tac) >>
        `abs
           (2 pow 1 /
            2 pow (INT_MAX (:'w) + dimindex (:'t))) =
         2 pow 1 /
         2 pow (INT_MAX (:'w) + dimindex (:'t))` by
          (irule realTheory.ABS_REDUCE >> simp []) >>
        `ULP
           ((smtfp_rep
              (smtfp_circuit_endpoint (format : ('t,'w) smtfp) 0w
                exponent
                (smtfp_circuit_round RNE 0w quotient residue
                  divisor))).Exponent,
            (:'t)) =
         &divisor *
           (2 pow 1 /
            2 pow (INT_MAX (:'w) + dimindex (:'t)))` by
          (mp_tac (Q.INST
             [`format` |-> `format`, `sign` |-> `(0w : word1)`,
              `exponent` |-> `exponent`,
              `rounded` |->
                `smtfp_circuit_round RNE 0w quotient residue divisor`]
             smtfp_circuit_endpoint_ULP) >>
           impl_tac >- simp [] >>
           strip_tac >>
           qpat_x_assum `ULP _ = _` (fn th => rewrite_tac [th]) >>
           qpat_x_assum
             `smtfp_circuit_round RNE 0w quotient residue divisor <>
              2 ** (dimindex (:'t) + 1)`
             (fn th => rewrite_tac [th]) >>
           simp_tac pure_ss [boolTheory.COND_CLAUSES] >>
           `exponent = SUC (exponent - 1)` by decide_tac >>
           `2 ** exponent = 2 * divisor` by
             (qpat_x_assum `exponent = SUC (exponent - 1)`
                (fn th => once_rewrite_tac [th]) >>
              rewrite_tac [CONJUNCT2 arithmeticTheory.EXP] >>
              simp []) >>
           rewrite_tac [realTheory.REAL_OF_NUM_POW] >>
           qpat_x_assum `2 ** exponent = 2 * divisor`
             (fn th => rewrite_tac [th]) >>
           simp [realTheory.REAL_OF_NUM_MUL] >>
           CONV_TAC RealField.REAL_RING) >>
        qpat_x_assum
          `2 * abs
             (&(smtfp_circuit_round RNE 0w quotient residue divisor *
                divisor) * _ - &(quotient * divisor + residue) * _) =
           ULP _`
          mp_tac >>
        rewrite_tac [smtfp_circuit_scaled_abs_diff] >>
        qpat_x_assum `ABS_DIFF _ _ = _` (fn th => rewrite_tac [th]) >>
        qpat_x_assum `abs (2 pow 1 / 2 pow _) = _`
          (fn th => rewrite_tac [th]) >>
        qpat_x_assum `ULP _ = _` (fn th => rewrite_tac [th]) >>
        `0 < 2 pow 1 /
             2 pow (INT_MAX (:'w) + dimindex (:'t))` by
          simp [] >>
        Cases_on
          `smtfp_circuit_round_up RNE 0w quotient residue divisor` >>
        simp_tac pure_ss [boolTheory.COND_CLAUSES] >>
        simp [realTheory.REAL_OF_NUM_SUB,
              realTheory.REAL_OF_NUM_MUL] >>
        realLib.REAL_ASM_ARITH_TAC) >>
     `EVEN (smtfp_circuit_round RNE 0w quotient residue divisor)` by
       (Cases_on
          `smtfp_circuit_round_up RNE 0w quotient residue divisor` >>
        fs [smtfp_circuit_round_def,
            smtfp_circuit_round_up_def,
            arithmeticTheory.ODD_EVEN] >>
        TRY decide_tac >>
        simp [arithmeticTheory.EVEN_ADD]) >>
     mp_tac (Q.INST
       [`format` |-> `format`, `sign` |-> `(0w : word1)`,
        `exponent` |-> `exponent`,
        `rounded` |->
          `smtfp_circuit_round RNE 0w quotient residue divisor`]
       smtfp_circuit_endpoint_even_finite) >>
     impl_tac >- simp [] >>
     metis_tac []) >>
  `((smtfp_rep
       (smtfp_circuit_endpoint (format : ('t,'w) smtfp) 0w exponent
         (smtfp_circuit_round RNE 0w quotient residue divisor))).Significand =
      0w /\
    (smtfp_rep
       (smtfp_circuit_endpoint (format : ('t,'w) smtfp) 0w exponent
         (smtfp_circuit_round RNE 0w quotient residue divisor))).Exponent <>
      1w ==>
    abs
      (&(smtfp_circuit_round RNE 0w quotient residue divisor * divisor) *
       (2 pow 1 / 2 pow (INT_MAX (:'w) + dimindex (:'t)))) <=
    abs
      (&(quotient * divisor + residue) *
       (2 pow 1 / 2 pow (INT_MAX (:'w) + dimindex (:'t)))))` by
    (strip_tac >>
     `smtfp_circuit_round RNE 0w quotient residue divisor * divisor <=
      quotient * divisor + residue` by
       (Cases_on
          `smtfp_circuit_round RNE 0w quotient residue divisor = quotient`
        >- (qpat_x_assum
              `smtfp_circuit_round RNE 0w quotient residue divisor =
               quotient`
              (fn th => rewrite_tac [th]) >>
            decide_tac)
        >- (TRY (metis_tac []) >>
            `smtfp_circuit_round RNE 0w quotient residue divisor =
             quotient + 1` by decide_tac >>
            mp_tac (Q.INST
              [`format` |-> `format`, `sign` |-> `(0w : word1)`,
               `exponent` |-> `exponent`, `quotient` |-> `quotient`,
               `rounded` |->
                 `smtfp_circuit_round RNE 0w quotient residue divisor`,
               `divisor` |-> `divisor`, `residue` |-> `residue`]
              smtfp_circuit_endpoint_boundary) >>
            impl_tac
            >- (asm_simp_tac pure_ss [] >> metis_tac []) >>
            simp [])) >>
     `0 < smtfp_circuit_round RNE 0w quotient residue divisor` by
       decide_tac >>
     `abs
        (&(smtfp_circuit_round RNE 0w quotient residue divisor * divisor) *
         (2 pow 1 / 2 pow (INT_MAX (:'w) + dimindex (:'t)))) =
      &(smtfp_circuit_round RNE 0w quotient residue divisor * divisor) *
       (2 pow 1 / 2 pow (INT_MAX (:'w) + dimindex (:'t)))` by
       (irule realTheory.ABS_REDUCE >>
        irule realTheory.REAL_LT_IMP_LE >>
        irule realTheory.REAL_LT_MUL >> simp []) >>
     qpat_x_assum
       `abs
          (&(quotient * divisor + residue) *
           (2 pow 1 / 2 pow _)) = _`
       (fn th => rewrite_tac [th]) >>
     qpat_x_assum
       `abs
          (&(smtfp_circuit_round RNE 0w quotient residue divisor *
             divisor) * _) = _`
       (fn th => rewrite_tac [th]) >>
     `&(smtfp_circuit_round RNE 0w quotient residue divisor * divisor) <=
      &(quotient * divisor + residue)` by
       (qpat_x_assum
          `smtfp_circuit_round RNE 0w quotient residue divisor *
             divisor <= quotient * divisor + residue`
          (fn th =>
             ACCEPT_TAC
               (EQ_MP
                  (GSYM (Q.SPECL
                     [`smtfp_circuit_round RNE 0w quotient residue divisor *
                       divisor`,
                      `quotient * divisor + residue`]
                     realTheory.REAL_OF_NUM_LE))
                  th))) >>
     `0 <
        2 pow 1 /
        2 pow (INT_MAX (:'w) + dimindex (:'t))` by
       simp [] >>
     irule realTheory.REAL_LE_RMUL_IMP >>
     conj_tac
     >- (qpat_x_assum `&_ <= &_` ACCEPT_TAC) >>
     qpat_x_assum `0 < 2 pow 1 / _`
       (fn th =>
          ACCEPT_TAC (MATCH_MP realTheory.REAL_LT_IMP_LE th))) >>
  `round roundTiesToEven
      (&(quotient * divisor + residue) *
       (2 pow 1 / 2 pow (INT_MAX (:'w) + dimindex (:'t)))) =
    smtfp_rep
      (smtfp_circuit_endpoint (format : ('t,'w) smtfp) 0w exponent
        (smtfp_circuit_round RNE 0w quotient residue divisor))` by
    (irule (Q.SPECL
       [`smtfp_rep
          (smtfp_circuit_endpoint (format : ('t,'w) smtfp) 0w exponent
            (smtfp_circuit_round RNE 0w quotient residue divisor))`,
        `&(quotient * divisor + residue) *
          (2 pow 1 / 2 pow (INT_MAX (:'w) + dimindex (:'t)))`,
       `&(smtfp_circuit_round RNE 0w quotient residue divisor * divisor) *
          (2 pow 1 / 2 pow (INT_MAX (:'w) + dimindex (:'t)))`]
       binary_ieeeTheory.round_roundTiesToEven) >>
     metis_tac [smtfp_float_value_finite]) >>
  simp_tac pure_ss [smt_float_round_def, smt_round_def,
                    TypeBase.case_def_of ``:smt_rounding``, LET_THM,
                    boolTheory.COND_CLAUSES] >>
  qpat_x_assum
    `round roundTiesToEven
       (&(quotient * divisor + residue) * _) = _`
    (fn th => rewrite_tac [th]) >>
  qpat_x_assum
    `~float_is_zero
       (smtfp_rep
         (smtfp_circuit_endpoint
           (format : ('t,'w) smtfp) 0w exponent _))`
    (fn th => rewrite_tac [th]) >>
  rewrite_tac [boolTheory.COND_CLAUSES]
QED

Theorem smtfp_circuit_scaled_midpoint_hi:
  0 < u /\ divisor <= 2 * residue ==>
  &((quotient + 1) * divisor) * u -
    &(quotient * divisor + residue) * u <=
  &(quotient * divisor + residue) * u -
    &(quotient * divisor) * u
Proof
  rpt strip_tac >>
  `(&(divisor) : real) <= 2 * &residue` by
    (`(&(divisor) : real) <= &(2 * residue)` by simp [] >>
     qpat_x_assum `(&(divisor) : real) <= _` mp_tac >>
     rewrite_tac [GSYM realTheory.REAL_OF_NUM_MUL] >> simp []) >>
  `&((quotient + 1) * divisor) * u -
     &(quotient * divisor + residue) * u =
   u * (&divisor - &residue)` by
    (rewrite_tac [GSYM realTheory.REAL_OF_NUM_ADD,
                  GSYM realTheory.REAL_OF_NUM_MUL] >>
     realLib.REAL_ARITH_TAC) >>
  `&(quotient * divisor + residue) * u -
     &(quotient * divisor) * u = u * &residue` by
    (rewrite_tac [GSYM realTheory.REAL_OF_NUM_ADD,
                  GSYM realTheory.REAL_OF_NUM_MUL] >>
     realLib.REAL_ARITH_TAC) >>
  simp [realTheory.REAL_LE_LMUL] >>
  realLib.REAL_ASM_ARITH_TAC
QED

Theorem smtfp_circuit_scaled_midpoint_lo:
  0 < u /\ 2 * residue < divisor ==>
  &(quotient * divisor + residue) * u -
    &(quotient * divisor) * u <
  &((quotient + 1) * divisor) * u -
    &(quotient * divisor + residue) * u
Proof
  rpt strip_tac >>
  `2 * (&residue : real) < &divisor` by
    (`(&(2 * residue) : real) < &divisor` by simp [] >>
     qpat_x_assum `(&(2 * residue) : real) < _` mp_tac >>
     rewrite_tac [GSYM realTheory.REAL_OF_NUM_MUL] >> simp []) >>
  `&(quotient * divisor + residue) * u -
     &(quotient * divisor) * u = u * &residue` by
    (rewrite_tac [GSYM realTheory.REAL_OF_NUM_ADD,
                  GSYM realTheory.REAL_OF_NUM_MUL] >>
     realLib.REAL_ARITH_TAC) >>
  `&((quotient + 1) * divisor) * u -
     &(quotient * divisor + residue) * u =
   u * (&divisor - &residue)` by
    (rewrite_tac [GSYM realTheory.REAL_OF_NUM_ADD,
                  GSYM realTheory.REAL_OF_NUM_MUL] >>
     realLib.REAL_ARITH_TAC) >>
  simp [realTheory.REAL_LT_LMUL] >>
  realLib.REAL_ASM_ARITH_TAC
QED

Theorem smtfp_circuit_RNA_positive_endpoint:
  2 <= dimindex (:'w) /\
  1 <= exponent /\ exponent <= dimword (:'w) - 2 /\
  0 < quotient /\
  quotient < 2 ** (dimindex (:'t) + 1) /\
  quotient + 1 <= 2 ** (dimindex (:'t) + 1) /\
  (quotient < 2 ** dimindex (:'t) ==> exponent = 1) /\
  (quotient + 1 = 2 ** (dimindex (:'t) + 1) ==>
   exponent < dimword (:'w) - 2) /\
  divisor = 2 ** (exponent - 1) /\ residue < divisor ==>
  let units = quotient * divisor + residue in
  let rounded =
    smtfp_circuit_round RNA 0w quotient residue divisor in
  let output =
    smtfp_rep
      (smtfp_circuit_endpoint (format : ('t,'w) smtfp) 0w exponent rounded) in
  smt_float_round RNA F
    (&units *
      (2 pow 1 / 2 pow (INT_MAX (:'w) + dimindex (:'t)))) = output
Proof
  simp_tac pure_ss [LET_THM] >> strip_tac >>
  `0 < divisor` by simp [] >>
  qabbrev_tac
    `u = 2 pow 1 / 2 pow (INT_MAX (:'w) + dimindex (:'t))` >>
  qabbrev_tac
    `lo = smtfp_rep
      (smtfp_circuit_endpoint (format : ('t,'w) smtfp) 0w exponent quotient)` >>
  qabbrev_tac
    `hi = smtfp_rep
      (smtfp_circuit_endpoint (format : ('t,'w) smtfp) 0w exponent
        (quotient + 1))` >>
  `float_is_finite lo /\ float_is_finite hi` by
    (simp [Abbr `lo`, Abbr `hi`] >> conj_tac >>
     irule smtfp_circuit_endpoint_finite >> simp []) >>
  `next_hi lo = hi` by
    (simp [Abbr `lo`, Abbr `hi`] >>
     irule smtfp_circuit_endpoint_next_hi >> simp []) >>
  `float_to_real lo = &(quotient * divisor) * u /\
   float_to_real hi = &((quotient + 1) * divisor) * u` by
    (conj_tac
     >- (simp_tac pure_ss [Abbr `lo`, Abbr `u`] >>
         mp_tac (Q.INST
           [`format` |-> `format`, `sign` |-> `(0w : word1)`,
            `exponent` |-> `exponent`, `rounded` |-> `quotient`]
           smtfp_circuit_endpoint_value) >>
         impl_tac >- simp [] >>
         simp [])
     >- (simp_tac pure_ss [Abbr `hi`, Abbr `u`] >>
         mp_tac (Q.INST
           [`format` |-> `format`, `sign` |-> `(0w : word1)`,
            `exponent` |-> `exponent`, `rounded` |-> `quotient + 1`]
           smtfp_circuit_endpoint_value) >>
         impl_tac >- simp [] >>
         simp [])) >>
  `0 < u` by simp [Abbr `u`] >>
  `~float_is_zero lo /\ ~float_is_zero hi` by
    (simp [binary_ieeeTheory.float_is_zero_to_real] >>
     realLib.REAL_ASM_ARITH_TAC) >>
  Cases_on `residue = 0`
  >- (`quotient * divisor + residue = quotient * divisor` by simp [] >>
      `smtfp_circuit_round RNA 0w quotient residue divisor = quotient` by
        simp [smtfp_circuit_round_def,
              smtfp_circuit_round_up_def] >>
      simp_tac pure_ss [smt_float_round_def, smt_round_def,
                        TypeBase.case_def_of ``:smt_rounding``, LET_THM,
                        boolTheory.COND_CLAUSES] >>
      `round_tiesToAway
         (&(quotient * divisor + residue) * u) = lo` by
        (qpat_x_assum
           `quotient * divisor + residue = quotient * divisor`
           (fn th => rewrite_tac [th]) >>
         qpat_x_assum `float_to_real lo = _`
           (fn th => once_rewrite_tac [GSYM th]) >>
         irule round_tiesToAway_representable_nonzero >>
         simp [binary_ieeeTheory.float_is_zero_to_real] >>
         fs [binary_ieeeTheory.float_is_zero_to_real]) >>
      qpat_x_assum `round_tiesToAway _ = lo`
        (fn th => rewrite_tac [th]) >>
      qpat_x_assum `~float_is_zero lo`
        (fn th => rewrite_tac [th]) >>
      rewrite_tac [boolTheory.COND_CLAUSES] >>
      qpat_x_assum `smtfp_circuit_round RNA _ _ _ _ = _`
        (fn th => rewrite_tac [th]) >>
      simp [Abbr `lo`]) >>
  `quotient * divisor < quotient * divisor + residue /\
   quotient * divisor + residue < (quotient + 1) * divisor` by
    simp [arithmeticTheory.LEFT_ADD_DISTRIB] >>
  `0 < float_to_real lo /\
   float_to_real lo < &(quotient * divisor + residue) * u /\
   &(quotient * divisor + residue) * u < float_to_real hi` by
    (simp [realTheory.REAL_OF_NUM_ADD,
           realTheory.REAL_OF_NUM_MUL] >>
     irule realTheory.REAL_LT_MUL >> simp []) >>
  `-threshold (:'t # 'w) <
       &(quotient * divisor + residue) * u /\
   &(quotient * divisor + residue) * u < threshold (:'t # 'w)` by
    (mp_tac (Q.INST [`f` |-> `hi`]
       (INST_TYPE [alpha |-> ``:'t``, beta |-> ``:'w``]
         binary_ieeeTheory.abs_float_bounds)) >>
     impl_tac >- simp [] >>
     rewrite_tac [binary_ieeeTheory.float_to_real_float_abs] >>
     strip_tac >>
     assume_tac (Q.SPEC `float_to_real hi` realTheory.ABS_LE) >>
     mp_tac (INST_TYPE [alpha |-> ``:'t``, beta |-> ``:'w``]
       binary_ieeeTheory.largest_lt_threshold) >>
     realLib.REAL_ASM_ARITH_TAC) >>
  Cases_on `smtfp_circuit_round_up RNA 0w quotient residue divisor`
  >- (`smtfp_circuit_round RNA 0w quotient residue divisor =
        quotient + 1` by
        simp [smtfp_circuit_round_def] >>
      `divisor <= 2 * residue` by
        fs [smtfp_circuit_round_up_def] >>
      `is_closest float_is_finite
         (&(quotient * divisor + residue) * u) hi` by
        (mp_tac (INST
           [``x:real`` |->
              ``&(quotient * divisor + residue) * u``]
           smtfp_circuit_adjacent_positive_closest_hi) >>
         impl_tac >-
           (simp [] >>
            conj_tac
            >- (irule realTheory.REAL_LE_MUL >>
                conj_tac >- realLib.REAL_ASM_ARITH_TAC >> simp [])
            >- (mp_tac smtfp_circuit_scaled_midpoint_hi >>
                impl_tac >- simp [] >> strip_tac >>
                metis_tac [arithmeticTheory.ADD_COMM,
                           arithmeticTheory.MULT_COMM,
                           realTheory.REAL_MUL_COMM])) >>
         simp []) >>
      `0 < &(quotient * divisor + residue) * u /\
       0 < float_to_real hi` by
        realLib.REAL_ASM_ARITH_TAC >>
      `abs (&(quotient * divisor + residue) * u) =
       &(quotient * divisor + residue) * u` by
        (rewrite_tac [realTheory.ABS_REFL] >>
         realLib.REAL_ASM_ARITH_TAC) >>
      `abs (float_to_real hi) = float_to_real hi` by
        (rewrite_tac [realTheory.ABS_REFL] >>
         realLib.REAL_ASM_ARITH_TAC) >>
      `abs (&(quotient * divisor + residue) * u) <=
       abs (float_to_real hi)` by
        realLib.REAL_ASM_ARITH_TAC >>
      `round_tiesToAway (&(quotient * divisor + residue) * u) = hi` by
        (mp_tac (INST
           [``x:real`` |->
              ``&(quotient * divisor + residue) * u``,
            ``y:('t,'w) float`` |-> ``hi:('t,'w) float``]
           (INST_TYPE [alpha |-> ``:'t``, beta |-> ``:'w``]
             round_tiesToAway_from_closest_away)) >>
         impl_tac >- (simp [] >> realLib.REAL_ASM_ARITH_TAC) >>
         simp []) >>
      simp_tac pure_ss [smt_float_round_def, smt_round_def,
                        TypeBase.case_def_of ``:smt_rounding``, LET_THM,
                        boolTheory.COND_CLAUSES] >>
      qpat_x_assum `round_tiesToAway _ = hi`
        (fn th => rewrite_tac [th]) >>
      qpat_x_assum `~float_is_zero hi`
        (fn th => rewrite_tac [th]) >>
      rewrite_tac [boolTheory.COND_CLAUSES] >>
      qpat_x_assum `smtfp_circuit_round RNA _ _ _ _ = _`
        (fn th => rewrite_tac [th]) >>
      simp [Abbr `hi`]) >>
  `smtfp_circuit_round RNA 0w quotient residue divisor = quotient` by
    simp [smtfp_circuit_round_def] >>
  `2 * residue < divisor` by
    fs [smtfp_circuit_round_up_def] >>
  `is_closest float_is_finite
     (&(quotient * divisor + residue) * u) lo` by
    (mp_tac (INST
       [``x:real`` |-> ``&(quotient * divisor + residue) * u``]
       smtfp_circuit_adjacent_positive_closest_lo) >>
     impl_tac >-
       (simp [] >>
        conj_tac
        >- (irule realTheory.REAL_LE_MUL >>
            conj_tac >- realLib.REAL_ASM_ARITH_TAC >> simp [])
        >- (mp_tac smtfp_circuit_scaled_midpoint_lo >>
            impl_tac >- simp [] >> strip_tac >>
            metis_tac [arithmeticTheory.ADD_COMM,
                       arithmeticTheory.MULT_COMM,
                       realTheory.REAL_MUL_COMM,
                       realTheory.REAL_LT_IMP_LE])) >>
     simp []) >>
  `&(quotient * divisor + residue) * u - float_to_real lo <
   float_to_real hi - &(quotient * divisor + residue) * u` by
    (mp_tac smtfp_circuit_scaled_midpoint_lo >>
     impl_tac >- simp [] >> strip_tac >>
     metis_tac [arithmeticTheory.ADD_COMM,
                arithmeticTheory.MULT_COMM,
                realTheory.REAL_MUL_COMM]) >>
  `abs (float_to_real lo - &(quotient * divisor + residue) * u) <
   abs (float_to_real hi - &(quotient * divisor + residue) * u)` by
    (`abs (float_to_real lo -
         &(quotient * divisor + residue) * u) =
       -(float_to_real lo -
         &(quotient * divisor + residue) * u)` by
       (irule realTheory.ABS_EQ_NEG >>
        realLib.REAL_ASM_ARITH_TAC) >>
     `abs (float_to_real hi -
         &(quotient * divisor + residue) * u) =
       float_to_real hi -
         &(quotient * divisor + residue) * u` by
       (rewrite_tac [realTheory.ABS_REFL] >>
        realLib.REAL_ASM_ARITH_TAC) >>
     realLib.REAL_ASM_ARITH_TAC) >>
  `round_tiesToAway (&(quotient * divisor + residue) * u) = lo` by
    (mp_tac (INST
       [``x:real`` |-> ``&(quotient * divisor + residue) * u``,
        ``y:('t,'w) float`` |-> ``lo:('t,'w) float``]
       (INST_TYPE [alpha |-> ``:'t``, beta |-> ``:'w``]
         round_tiesToAway_positive_inward)) >>
     impl_tac >-
       (simp [] >>
        metis_tac [arithmeticTheory.ADD_COMM,
                   arithmeticTheory.MULT_COMM,
                   realTheory.REAL_MUL_COMM]) >>
     simp []) >>
  simp_tac pure_ss [smt_float_round_def, smt_round_def,
                    TypeBase.case_def_of ``:smt_rounding``, LET_THM,
                    boolTheory.COND_CLAUSES] >>
  qpat_x_assum `round_tiesToAway _ = lo`
    (fn th => rewrite_tac [th]) >>
  qpat_x_assum `~float_is_zero lo`
    (fn th => rewrite_tac [th]) >>
  rewrite_tac [boolTheory.COND_CLAUSES] >>
  qpat_x_assum `smtfp_circuit_round RNA _ _ _ _ = _`
    (fn th => rewrite_tac [th]) >>
  simp [Abbr `lo`]
QED

Theorem smtfp_circuit_directed_positive_endpoint:
  2 <= dimindex (:'w) /\
  1 <= exponent /\ exponent <= dimword (:'w) - 2 /\
  0 < quotient /\
  quotient < 2 ** (dimindex (:'t) + 1) /\
  quotient + 1 <= 2 ** (dimindex (:'t) + 1) /\
  (quotient < 2 ** dimindex (:'t) ==> exponent = 1) /\
  (quotient + 1 = 2 ** (dimindex (:'t) + 1) ==>
   exponent < dimword (:'w) - 2) /\
  divisor = 2 ** (exponent - 1) /\ residue < divisor /\
  (mode = RTP \/ mode = RTN \/ mode = RTZ) ==>
  let units = quotient * divisor + residue in
  let rounded =
    smtfp_circuit_round mode 0w quotient residue divisor in
  let output =
    smtfp_rep
      (smtfp_circuit_endpoint (format : ('t,'w) smtfp) 0w exponent rounded) in
  smt_float_round mode F
    (&units *
      (2 pow 1 / 2 pow (INT_MAX (:'w) + dimindex (:'t)))) = output
Proof
  simp_tac pure_ss [LET_THM] >> strip_tac >>
  `0 < divisor` by simp [] >>
  qabbrev_tac
    `u = 2 pow 1 / 2 pow (INT_MAX (:'w) + dimindex (:'t))` >>
  qabbrev_tac
    `lo = smtfp_rep
      (smtfp_circuit_endpoint (format : ('t,'w) smtfp) 0w exponent quotient)` >>
  qabbrev_tac
    `hi = smtfp_rep
      (smtfp_circuit_endpoint (format : ('t,'w) smtfp) 0w exponent
        (quotient + 1))` >>
  `float_is_finite lo /\ float_is_finite hi` by
    (simp [Abbr `lo`, Abbr `hi`] >> conj_tac >>
     irule smtfp_circuit_endpoint_finite >> simp []) >>
  `next_hi lo = hi` by
    (simp [Abbr `lo`, Abbr `hi`] >>
     irule smtfp_circuit_endpoint_next_hi >> simp []) >>
  `float_to_real lo = &(quotient * divisor) * u /\
   float_to_real hi = &((quotient + 1) * divisor) * u` by
    (conj_tac
     >- (simp_tac pure_ss [Abbr `lo`, Abbr `u`] >>
         mp_tac (Q.INST
           [`format` |-> `format`, `sign` |-> `(0w : word1)`,
            `exponent` |-> `exponent`, `rounded` |-> `quotient`]
           smtfp_circuit_endpoint_value) >>
         impl_tac >- simp [] >>
         simp [])
     >- (simp_tac pure_ss [Abbr `hi`, Abbr `u`] >>
         mp_tac (Q.INST
           [`format` |-> `format`, `sign` |-> `(0w : word1)`,
            `exponent` |-> `exponent`, `rounded` |-> `quotient + 1`]
           smtfp_circuit_endpoint_value) >>
         impl_tac >- simp [] >>
         simp [])) >>
  `0 < u` by simp [Abbr `u`] >>
  `~float_is_zero lo /\ ~float_is_zero hi` by
    (simp [binary_ieeeTheory.float_is_zero_to_real] >>
     realLib.REAL_ASM_ARITH_TAC) >>
  Cases_on `residue = 0` >>
  FIRST
  [(`quotient * divisor + residue = quotient * divisor` by simp [] >>
      `smtfp_circuit_round mode 0w quotient residue divisor = quotient` by
        simp [smtfp_circuit_round_def,
              smtfp_circuit_round_up_def] >>
      qpat_x_assum
        `quotient * divisor + residue = quotient * divisor`
        (fn th => rewrite_tac [th]) >>
      qpat_x_assum `float_to_real lo = _`
        (fn th => rewrite_tac [GSYM th]) >>
      qpat_x_assum `smtfp_circuit_round mode _ _ _ _ = _`
        (fn th => rewrite_tac [th]) >>
      simp_tac pure_ss [Abbr `lo`] >>
      irule smt_float_round_representable_nonzero >>
      simp [] >>
      mp_tac (INST_TYPE [alpha |-> ``:'t``, beta |-> ``:'w``]
        binary_ieeeTheory.abs_float_bounds) >>
      simp [] >> strip_tac >>
      metis_tac [binary_ieeeTheory.float_is_zero_to_real]),
   (`quotient * divisor < quotient * divisor + residue /\
     quotient * divisor + residue < (quotient + 1) * divisor` by
      (simp [arithmeticTheory.LEFT_ADD_DISTRIB] >> decide_tac) >>
    `0 < float_to_real lo /\
     float_to_real lo < &(quotient * divisor + residue) * u /\
     &(quotient * divisor + residue) * u < float_to_real hi` by
      (simp [realTheory.REAL_OF_NUM_ADD,
             realTheory.REAL_OF_NUM_MUL] >>
       irule realTheory.REAL_LT_MUL >> simp []) >>
    `-largest (:'t # 'w) <= &(quotient * divisor + residue) * u /\
     &(quotient * divisor + residue) * u <= largest (:'t # 'w)` by
      (mp_tac (Q.INST [`f` |-> `hi`]
         (INST_TYPE [alpha |-> ``:'t``, beta |-> ``:'w``]
           binary_ieeeTheory.abs_float_bounds)) >>
       impl_tac >- simp [] >>
       rewrite_tac [binary_ieeeTheory.float_to_real_float_abs] >>
       strip_tac >>
       assume_tac (Q.SPEC `float_to_real hi` realTheory.ABS_LE) >>
       realLib.REAL_ASM_ARITH_TAC) >>
    FIRST
    [(qpat_x_assum `mode = RTP` SUBST_ALL_TAC >>
      `smtfp_circuit_round RTP 0w quotient residue divisor =
        quotient + 1` by
        simp [smtfp_circuit_round_def,
              smtfp_circuit_round_up_def] >>
      `round roundTowardPositive
         (&(quotient * divisor + residue) * u) = hi` by
        (mp_tac (INST
           [``x:real`` |->
              ``&(quotient * divisor + residue) * u``,
            ``lo:('t,'w) float`` |-> ``lo:('t,'w) float``]
           (INST_TYPE [alpha |-> ``:'t``, beta |-> ``:'w``]
             round_RTP_positive_next_hi)) >>
         impl_tac >-
           metis_tac [realTheory.REAL_LT_IMP_LE] >>
         simp []) >>
      simp [smt_float_round_def,
            smt_round_def]),
     (qpat_x_assum `mode = RTN` SUBST_ALL_TAC >>
      `smtfp_circuit_round RTN 0w quotient residue divisor = quotient` by
        simp [smtfp_circuit_round_def,
              smtfp_circuit_round_up_def] >>
      `round roundTowardNegative
         (&(quotient * divisor + residue) * u) = lo` by
        (mp_tac (INST
           [``x:real`` |->
              ``&(quotient * divisor + residue) * u``,
            ``y:('t,'w) float`` |-> ``lo:('t,'w) float``]
         (INST_TYPE [alpha |-> ``:'t``, beta |-> ``:'w``]
             round_RTN_positive_inward)) >>
         impl_tac >-
           metis_tac [realTheory.REAL_LT_IMP_LE,
                      realTheory.REAL_LT_TRANS] >>
         simp []) >>
      simp [smt_float_round_def,
            smt_round_def]),
     (qpat_x_assum `mode = RTZ` SUBST_ALL_TAC >>
      `smtfp_circuit_round RTZ 0w quotient residue divisor = quotient` by
        simp [smtfp_circuit_round_def,
              smtfp_circuit_round_up_def] >>
      `round roundTowardZero
         (&(quotient * divisor + residue) * u) = lo` by
        (irule binary_ieeeTheory.round_roundTowardZero >>
         conj_tac
         >- (qexists_tac `float_to_real lo` >>
             conj_tac
             >- (irule smtfp_float_value_finite >> simp []) >>
             conj_tac
             >- (qpat_x_assum `float_to_real lo = _`
                   (fn th => rewrite_tac [th]) >>
                 rewrite_tac [smtfp_circuit_scaled_abs_diff] >>
                 simp [arithmeticTheory.ABS_DIFF_def] >>
                 `abs u = u` by
                   (irule realTheory.ABS_REDUCE >>
                    realLib.REAL_ASM_ARITH_TAC) >>
                 qpat_x_assum `abs u = u`
                   (fn th => rewrite_tac [th]) >>
                 `u * &residue < u * &divisor` by
                   (irule realTheory.REAL_LT_LMUL_IMP >> simp []) >>
                 `&divisor * u <= ULP (lo.Exponent, (:'t))` by
                   (simp_tac pure_ss [Abbr `lo`, Abbr `u`] >>
                    irule smtfp_circuit_endpoint_ULP_divisor >>
                    simp []) >>
                 metis_tac [realTheory.REAL_LTE_TRANS,
                            realTheory.REAL_MUL_COMM]) >>
             `abs (float_to_real lo) = float_to_real lo` by
               (irule realTheory.ABS_REDUCE >>
                realLib.REAL_ASM_ARITH_TAC) >>
             `abs (&(quotient * divisor + residue) * u) =
                &(quotient * divisor + residue) * u` by
               (irule realTheory.ABS_REDUCE >>
                realLib.REAL_ASM_ARITH_TAC) >>
             realLib.REAL_ASM_ARITH_TAC) >>
         conj_tac
         >- (`abs (&(quotient * divisor + residue) * u) =
                &(quotient * divisor + residue) * u` by
               (irule realTheory.ABS_REDUCE >>
                realLib.REAL_ASM_ARITH_TAC) >>
             realLib.REAL_ASM_ARITH_TAC) >>
         `1 <= quotient * divisor + residue` by
           (simp [] >> decide_tac) >>
         `abs (&(quotient * divisor + residue) * u) =
            &(quotient * divisor + residue) * u` by
           (irule realTheory.ABS_REDUCE >>
            realLib.REAL_ASM_ARITH_TAC) >>
         simp [binary_ieeeTheory.ulp_def,
               binary_ieeeTheory.ULP_def, Abbr `u`]) >>
      simp [smt_float_round_def,
            smt_round_def])])]
QED

Theorem smtfp_circuit_RNE_negative_endpoint:
  2 <= dimindex (:'w) /\
  1 <= exponent /\ exponent <= dimword (:'w) - 2 /\
  0 < quotient /\
  quotient < 2 ** (dimindex (:'t) + 1) /\
  quotient + 1 <= 2 ** (dimindex (:'t) + 1) /\
  (quotient < 2 ** dimindex (:'t) ==> exponent = 1) /\
  (quotient + 1 = 2 ** (dimindex (:'t) + 1) ==>
   exponent < dimword (:'w) - 2) /\
  divisor = 2 ** (exponent - 1) /\ residue < divisor ==>
  let units = quotient * divisor + residue in
  let rounded =
    smtfp_circuit_round RNE 1w quotient residue divisor in
  let output =
    smtfp_rep
      (smtfp_circuit_endpoint (format : ('t,'w) smtfp) 1w exponent rounded) in
  smt_float_round RNE F
    (-&units *
      (2 pow 1 / 2 pow (INT_MAX (:'w) + dimindex (:'t)))) = output
Proof
  simp_tac pure_ss [LET_THM] >> strip_tac >>
  `0 < divisor` by simp [] >>
  `quotient <=
     smtfp_circuit_round RNE 1w quotient residue divisor /\
   smtfp_circuit_round RNE 1w quotient residue divisor <= quotient + 1` by
    (mp_tac (Q.INST
       [`mode` |-> `RNE`, `sign` |-> `(1w : word1)`,
        `q` |-> `quotient`, `residue` |-> `residue`,
        `divisor` |-> `divisor`]
       smtfp_circuit_round_bounds) >>
     decide_tac) >>
  `smtfp_circuit_round RNE 1w quotient residue divisor <=
   2 ** (dimindex (:'t) + 1)` by decide_tac >>
  `0 < smtfp_circuit_round RNE 1w quotient residue divisor` by
    decide_tac >>
  `(smtfp_circuit_round RNE 1w quotient residue divisor <
      2 ** dimindex (:'t) ==> exponent = 1)` by decide_tac >>
  `(smtfp_circuit_round RNE 1w quotient residue divisor =
      2 ** (dimindex (:'t) + 1) ==>
    exponent < dimword (:'w) - 2)` by decide_tac >>
  `float_is_finite
    (smtfp_rep
      (smtfp_circuit_endpoint (format : ('t,'w) smtfp) 1w exponent
        (smtfp_circuit_round RNE 1w quotient residue divisor)))` by
    (irule smtfp_circuit_endpoint_finite >> simp []) >>
  `float_to_real
    (smtfp_rep
      (smtfp_circuit_endpoint (format : ('t,'w) smtfp) 1w exponent
        (smtfp_circuit_round RNE 1w quotient residue divisor))) =
   -&(smtfp_circuit_round RNE 1w quotient residue divisor * divisor) *
     (2 pow 1 / 2 pow (INT_MAX (:'w) + dimindex (:'t)))` by
    (mp_tac (Q.INST
       [`format` |-> `format`, `sign` |-> `(1w : word1)`,
        `exponent` |-> `exponent`, `rounded` |->
          `smtfp_circuit_round RNE 1w quotient residue divisor`]
       smtfp_circuit_endpoint_value) >>
     impl_tac >- simp [] >>
     simp []) >>
  `~float_is_zero
    (smtfp_rep
      (smtfp_circuit_endpoint (format : ('t,'w) smtfp) 1w exponent
        (smtfp_circuit_round RNE 1w quotient residue divisor)))` by
    (simp [binary_ieeeTheory.float_is_zero_to_real] >>
     simp [realTheory.real_div] >>
     qpat_x_assum
       `0 < smtfp_circuit_round RNE 1w quotient residue divisor`
       mp_tac >>
     asm_rewrite_tac [] >>
     decide_tac) >>
  `float_is_finite
    (smtfp_rep
      (smtfp_circuit_endpoint (format : ('t,'w) smtfp) 1w exponent
        (quotient + 1)))` by
    (irule smtfp_circuit_endpoint_finite >> simp []) >>
  `float_to_real
    (smtfp_rep
      (smtfp_circuit_endpoint (format : ('t,'w) smtfp) 1w exponent
        (quotient + 1))) =
   -&((quotient + 1) * divisor) *
     (2 pow 1 / 2 pow (INT_MAX (:'w) + dimindex (:'t)))` by
    (mp_tac (Q.INST
       [`format` |-> `format`, `sign` |-> `(1w : word1)`,
        `exponent` |-> `exponent`, `rounded` |-> `quotient + 1`]
       smtfp_circuit_endpoint_value) >>
     impl_tac >- simp [] >>
     simp []) >>
  `-threshold (:'t # 'w) <
      -&(quotient * divisor + residue) *
       (2 pow 1 / 2 pow (INT_MAX (:'w) + dimindex (:'t))) /\
   -&(quotient * divisor + residue) *
       (2 pow 1 / 2 pow (INT_MAX (:'w) + dimindex (:'t))) <
      threshold (:'t # 'w)` by
    (`abs
        (float_to_real
          (smtfp_rep
            (smtfp_circuit_endpoint (format : ('t,'w) smtfp) 1w
              exponent (quotient + 1)))) <= largest (:'t # 'w)` by
       (mp_tac (Q.INST
          [`f` |->
             `smtfp_rep
               (smtfp_circuit_endpoint (format : ('t,'w) smtfp) 1w
                 exponent (quotient + 1))`]
          (INST_TYPE [alpha |-> ``:'t``, beta |-> ``:'w``]
             binary_ieeeTheory.abs_float_bounds)) >>
        simp []) >>
     `abs
        (-&(quotient * divisor + residue) *
         (2 pow 1 / 2 pow (INT_MAX (:'w) + dimindex (:'t)))) <
      abs
        (float_to_real
          (smtfp_rep
            (smtfp_circuit_endpoint (format : ('t,'w) smtfp) 1w
              exponent (quotient + 1))))` by
       (simp [realTheory.abs, realTheory.REAL_OF_NUM_ADD,
              realTheory.REAL_OF_NUM_MUL] >>
        realLib.REAL_ASM_ARITH_TAC) >>
     `abs
        (-&(quotient * divisor + residue) *
         (2 pow 1 / 2 pow (INT_MAX (:'w) + dimindex (:'t)))) <
      threshold (:'t # 'w)` by
       (mp_tac (INST_TYPE [alpha |-> ``:'t``, beta |-> ``:'w``]
          binary_ieeeTheory.largest_lt_threshold) >>
        realLib.REAL_ASM_ARITH_TAC) >>
     mp_tac (Q.SPECL
       [`-&(quotient * divisor + residue) *
         (2 pow 1 / 2 pow (INT_MAX (:'w) + dimindex (:'t)))`,
        `threshold (:'t # 'w)`]
       realTheory.ABS_BOUNDS_LT) >>
     simp []) >>
  Cases_on
    `smtfp_circuit_round RNE 1w quotient residue divisor =
     2 ** (dimindex (:'t) + 1)`
  >- (
      `smtfp_circuit_round RNE 1w quotient residue divisor =
       quotient + 1` by decide_tac >>
      `quotient + 1 = 2 ** (dimindex (:'t) + 1)` by
        metis_tac [] >>
      `smtfp_circuit_round_up RNE 1w quotient residue divisor` by
        (Cases_on
           `smtfp_circuit_round_up RNE 1w quotient residue divisor` >>
         fs [smtfp_circuit_round_def]) >>
      `divisor <= 2 * residue` by
        (fs [smtfp_circuit_round_up_def] >> decide_tac) >>
      `exponent < dimword (:'w) - 2` by metis_tac [] >>
      `exponent + 1 < dimword (:'w) - 1` by decide_tac >>
      `smtfp_rep
         (smtfp_circuit_endpoint (format : ('t,'w) smtfp) 1w exponent
           (smtfp_circuit_round RNE 1w quotient residue divisor)) =
       (<| Sign := 1w; Exponent := n2w (exponent + 1);
           Significand := 0w |> : ('t,'w) float)` by
        (qpat_x_assum
           `smtfp_circuit_round RNE 1w quotient residue divisor =
            2 ** (dimindex (:'t) + 1)`
           (fn th => once_rewrite_tac [th]) >>
         simp [smtfp_circuit_endpoint_def,
               smtfp_rep_finite_n2w_bits]) >>
      `exponent + 1 < dimword (:'w)` by decide_tac >>
      `1 < dimword (:'w)` by decide_tac >>
      `(smtfp_rep
         (smtfp_circuit_endpoint (format : ('t,'w) smtfp) 1w exponent
           (smtfp_circuit_round RNE 1w quotient residue divisor))).Significand =
       0w /\
       (smtfp_rep
         (smtfp_circuit_endpoint (format : ('t,'w) smtfp) 1w exponent
           (smtfp_circuit_round RNE 1w quotient residue divisor))).Exponent <>
       1w` by
        (asm_rewrite_tac [] >>
         simp [wordsTheory.n2w_11,
               arithmeticTheory.LESS_MOD]) >>
      `~(abs
          (-&(smtfp_circuit_round RNE 1w quotient residue divisor *
             divisor) *
           (2 pow 1 / 2 pow (INT_MAX (:'w) + dimindex (:'t)))) <=
         abs
          (-&(quotient * divisor + residue) *
           (2 pow 1 / 2 pow (INT_MAX (:'w) + dimindex (:'t)))))` by
        (qpat_x_assum
           `smtfp_circuit_round RNE 1w quotient residue divisor =
            2 ** (dimindex (:'t) + 1)`
           (fn th => rewrite_tac [th]) >>
         qpat_x_assum
           `quotient + 1 = 2 ** (dimindex (:'t) + 1)`
           (fn th => rewrite_tac [GSYM th]) >>
         simp [realTheory.abs, realTheory.REAL_OF_NUM_ADD,
               realTheory.REAL_OF_NUM_MUL,
               arithmeticTheory.LEFT_ADD_DISTRIB] >>
         decide_tac) >>
      `4 *
        abs
          (-&(smtfp_circuit_round RNE 1w quotient residue divisor *
             divisor) *
           (2 pow 1 / 2 pow (INT_MAX (:'w) + dimindex (:'t))) -
           -&(quotient * divisor + residue) *
           (2 pow 1 / 2 pow (INT_MAX (:'w) + dimindex (:'t)))) <=
       ULP
         ((smtfp_rep
            (smtfp_circuit_endpoint (format : ('t,'w) smtfp) 1w
              exponent
              (smtfp_circuit_round RNE 1w quotient residue
                divisor))).Exponent,
          (:'t))` by
        (`ABS_DIFF
            (smtfp_circuit_round RNE 1w quotient residue divisor *
             divisor)
            (quotient * divisor + residue) = divisor - residue` by
           (qpat_x_assum
              `smtfp_circuit_round RNE 1w quotient residue divisor =
               quotient + 1`
              (fn th => rewrite_tac [th]) >>
            simp [arithmeticTheory.ABS_DIFF_def,
                  arithmeticTheory.LEFT_ADD_DISTRIB] >>
            decide_tac) >>
         `abs
            (2 pow 1 /
             2 pow (INT_MAX (:'w) + dimindex (:'t))) =
          2 pow 1 /
          2 pow (INT_MAX (:'w) + dimindex (:'t))` by
           (irule realTheory.ABS_REDUCE >> simp []) >>
         rewrite_tac [smtfp_circuit_scaled_abs_diff_neg] >>
         qpat_x_assum `ABS_DIFF _ _ = divisor - residue`
           (fn th => rewrite_tac [th]) >>
         qpat_x_assum `abs (2 pow 1 / 2 pow _) = _`
           (fn th => rewrite_tac [th]) >>
         `4 * (divisor - residue) <= 2 * divisor` by decide_tac >>
         `4 * &(divisor - residue) *
            (2 pow 1 /
             2 pow (INT_MAX (:'w) + dimindex (:'t))) <=
          &(2 * divisor) *
            (2 pow 1 /
             2 pow (INT_MAX (:'w) + dimindex (:'t)))` by
           (irule realTheory.REAL_LE_RMUL_IMP >>
            simp [realTheory.REAL_OF_NUM_MUL]) >>
         `exponent = SUC (exponent - 1)` by decide_tac >>
         `exponent + 1 = SUC exponent` by decide_tac >>
         `2 ** (exponent + 1) = 4 * divisor` by
           (qpat_x_assum `exponent + 1 = SUC exponent`
              (fn th => once_rewrite_tac [th]) >>
            rewrite_tac [CONJUNCT2 arithmeticTheory.EXP] >>
            qpat_x_assum `exponent = SUC (exponent - 1)`
              (fn th => once_rewrite_tac [th]) >>
            rewrite_tac [CONJUNCT2 arithmeticTheory.EXP] >>
            qpat_x_assum `divisor = 2 ** (exponent - 1)`
              (fn th => rewrite_tac [th]) >>
            decide_tac) >>
         mp_tac (Q.INST
           [`format` |-> `format`, `sign` |-> `(1w : word1)`,
            `exponent` |-> `exponent`,
            `rounded` |->
              `smtfp_circuit_round RNE 1w quotient residue divisor`]
           smtfp_circuit_endpoint_ULP) >>
         impl_tac >- simp [] >>
         strip_tac >>
         qpat_x_assum `ULP _ = _`
           (fn th => rewrite_tac [th]) >>
         qpat_x_assum
           `smtfp_circuit_round RNE 1w quotient residue divisor =
            2 ** (dimindex (:'t) + 1)`
           (fn th => rewrite_tac [th]) >>
         simp_tac pure_ss [boolTheory.COND_CLAUSES] >>
         `&(2 * divisor) *
            (2 pow 1 /
             2 pow (INT_MAX (:'w) + dimindex (:'t))) =
          2 pow (exponent + 1) /
          2 pow (INT_MAX (:'w) + dimindex (:'t))` by
           (rewrite_tac [realTheory.REAL_OF_NUM_POW] >>
            qpat_x_assum `2 ** (exponent + 1) = 4 * divisor`
              (fn th => rewrite_tac [th]) >>
            simp [realTheory.REAL_OF_NUM_MUL] >>
            CONV_TAC RealField.REAL_RING) >>
         metis_tac [realTheory.REAL_MUL_ASSOC]) >>
      `ulp (:'t # 'w) <
       2 *
       abs
         (-&(quotient * divisor + residue) *
          (2 pow 1 / 2 pow (INT_MAX (:'w) + dimindex (:'t))))` by
        (simp [binary_ieeeTheory.ulp_def,
               binary_ieeeTheory.ULP_def, realTheory.abs] >>
         `0 < quotient * 2 ** (exponent - 1)` by simp [] >>
         decide_tac) >>
      `abs
         (-&(quotient * divisor + residue) *
          (2 pow 1 / 2 pow (INT_MAX (:'w) + dimindex (:'t)))) <
       threshold (:'t # 'w)` by
        (mp_tac (Q.SPECL
           [`-&(quotient * divisor + residue) *
             (2 pow 1 /
              2 pow (INT_MAX (:'w) + dimindex (:'t)))`,
            `threshold (:'t # 'w)`]
           realTheory.ABS_BOUNDS_LT) >>
         simp []) >>
      `round roundTiesToEven
          (-&(quotient * divisor + residue) *
           (2 pow 1 / 2 pow (INT_MAX (:'w) + dimindex (:'t)))) =
        smtfp_rep
          (smtfp_circuit_endpoint (format : ('t,'w) smtfp) 1w exponent
            (smtfp_circuit_round RNE 1w quotient residue divisor))` by
        (irule (Q.SPECL
           [`smtfp_rep
              (smtfp_circuit_endpoint (format : ('t,'w) smtfp) 1w
                exponent
                (smtfp_circuit_round RNE 1w quotient residue divisor))`,
            `-&(quotient * divisor + residue) *
              (2 pow 1 / 2 pow (INT_MAX (:'w) + dimindex (:'t)))`,
            `-&(smtfp_circuit_round RNE 1w quotient residue divisor *
                divisor) *
              (2 pow 1 / 2 pow (INT_MAX (:'w) + dimindex (:'t)))`]
           binary_ieeeTheory.round_roundTiesToEven0) >>
         `float_value
            (smtfp_rep
              (smtfp_circuit_endpoint (format : ('t,'w) smtfp) 1w
                exponent
                (smtfp_circuit_round RNE 1w quotient residue divisor))) =
          Float
            (-&(smtfp_circuit_round RNE 1w quotient residue divisor *
                divisor) *
             (2 pow 1 /
              2 pow (INT_MAX (:'w) + dimindex (:'t))))` by
           metis_tac [smtfp_float_value_finite] >>
         metis_tac []) >>

      simp_tac pure_ss [smt_float_round_def, smt_round_def,
                        TypeBase.case_def_of ``:smt_rounding``, LET_THM,
                        boolTheory.COND_CLAUSES] >>

      qpat_x_assum
        `round roundTiesToEven
           (-&(quotient * divisor + residue) * _) = _`
        (fn th => rewrite_tac [th]) >>

      asm_simp_tac pure_ss [boolTheory.COND_CLAUSES] >>
      REFL_TAC)
  >- (`round roundTiesToEven
      (-&(quotient * divisor + residue) *
       (2 pow 1 / 2 pow (INT_MAX (:'w) + dimindex (:'t)))) =
    smtfp_rep
      (smtfp_circuit_endpoint (format : ('t,'w) smtfp) 1w exponent
        (smtfp_circuit_round RNE 1w quotient residue divisor))` by
    (irule binary_ieeeTheory.round_roundTiesToEven >>
     conj_tac
     >- (mp_tac (Q.SPECL
           [`-&(quotient * divisor + residue) *
             (2 pow 1 /
              2 pow (INT_MAX (:'w) + dimindex (:'t)))`,
            `threshold (:'t # 'w)`]
           realTheory.ABS_BOUNDS_LT) >>
         simp [])
     >> conj_tac
     >- (simp [binary_ieeeTheory.ulp_def,
               binary_ieeeTheory.ULP_def, realTheory.abs] >>
         `0 < quotient * 2 ** (exponent - 1)` by simp [] >>
         decide_tac)
     >>
     qexists_tac
       `-&(smtfp_circuit_round RNE 1w quotient residue divisor * divisor) *
        (2 pow 1 / 2 pow (INT_MAX (:'w) + dimindex (:'t)))` >>
     simp [binary_ieeeTheory.float_is_finite_thm] >>
     conj_tac
     >- (mp_tac (INST
           [``f:('t,'w) float`` |->
              ``smtfp_rep
                (smtfp_circuit_endpoint
                  (format : ('t,'w) smtfp) 1w exponent
                  (smtfp_circuit_round RNE 1w quotient residue
                    divisor))``]
           smtfp_float_value_finite) >>
         simp [])
     >>
     rpt conj_tac
     >- (
         strip_tac >>

         `smtfp_circuit_round RNE 1w quotient residue divisor * divisor <=
          quotient * divisor + residue` by
           (Cases_on
              `smtfp_circuit_round RNE 1w quotient residue divisor =
               quotient`
            >- (qpat_x_assum
                  `smtfp_circuit_round RNE 1w quotient residue divisor =
                   quotient`
                  (fn th => rewrite_tac [th]) >>
                decide_tac)
            >- (TRY (metis_tac []) >>

                `smtfp_circuit_round RNE 1w quotient residue divisor =
                 quotient + 1` by decide_tac >>
                mp_tac (Q.INST
                  [`format` |-> `format`, `sign` |-> `(1w : word1)`,
                   `exponent` |-> `exponent`,
                   `quotient` |-> `quotient`,
                   `rounded` |->
                     `smtfp_circuit_round RNE 1w quotient residue divisor`,
                   `divisor` |-> `divisor`, `residue` |-> `residue`]
                  smtfp_circuit_endpoint_boundary) >>
                impl_tac
                >- (asm_simp_tac pure_ss [] >>
                    metis_tac []) >>

                simp [])) >>

         `abs
            (-2 *
             (&(quotient * 2 ** (exponent - 1)) *
              inv (2 pow (INT_MAX (:'w) + dimindex (:'t))))) =
          &(quotient * 2 ** (exponent - 1)) *
            (2 pow 1 /
             2 pow (INT_MAX (:'w) + dimindex (:'t)))` by
           (simp [realTheory.ABS_MUL, realTheory.ABS_INV,
                  realTheory.real_div] >>
            CONV_TAC RealField.REAL_RING) >>
         `abs
            (-2 *
             (&((quotient + 1) * 2 ** (exponent - 1)) *
              inv (2 pow (INT_MAX (:'w) + dimindex (:'t))))) =
          &((quotient + 1) * 2 ** (exponent - 1)) *
            (2 pow 1 /
             2 pow (INT_MAX (:'w) + dimindex (:'t)))` by
           (simp [realTheory.ABS_MUL, realTheory.ABS_INV,
                  realTheory.real_div] >>
            CONV_TAC RealField.REAL_RING) >>

         `abs
            (-2 *
             (&(residue + quotient * 2 ** (exponent - 1)) *
              inv (2 pow (INT_MAX (:'w) + dimindex (:'t))))) =
          &(residue + quotient * 2 ** (exponent - 1)) *
            (2 pow 1 /
             2 pow (INT_MAX (:'w) + dimindex (:'t)))` by
           (simp [realTheory.ABS_MUL, realTheory.ABS_INV,
                  realTheory.real_div] >>
            CONV_TAC RealField.REAL_RING) >>

         `abs
            (-2 *
             (&(2 ** (exponent - 1) *
                smtfp_circuit_round RNE 1w quotient residue
                  (2 ** (exponent - 1))) *
              inv (2 pow (INT_MAX (:'w) + dimindex (:'t))))) =
          &(2 ** (exponent - 1) *
             smtfp_circuit_round RNE 1w quotient residue
               (2 ** (exponent - 1))) *
            (2 pow 1 /
             2 pow (INT_MAX (:'w) + dimindex (:'t)))` by
           (simp [realTheory.ABS_MUL, realTheory.ABS_INV,
                  realTheory.real_div] >>
            CONV_TAC RealField.REAL_RING) >>
         `smtfp_circuit_round RNE 1w quotient residue divisor *
            2 ** (exponent - 1) <=
          residue + quotient * 2 ** (exponent - 1)` by
           (qpat_x_assum
              `smtfp_circuit_round RNE 1w quotient residue divisor *
                 divisor <= _`
              mp_tac >>
            asm_rewrite_tac [] >>
            simp [arithmeticTheory.ADD_COMM]) >>

         qpat_x_assum
           `abs
              (-2 *
               (&(2 ** (exponent - 1) * _) *
                inv (2 pow _))) = _`
           (fn th => rewrite_tac [th]) >>
         qpat_x_assum
           `abs
              (-2 *
               (&(residue + quotient * 2 ** (exponent - 1)) *
                inv (2 pow _))) = _`
           (fn th => rewrite_tac [th]) >>

         irule realTheory.REAL_LE_RMUL_IMP >>
         qpat_x_assum
           `_ <= residue + quotient * 2 ** (exponent - 1)`
           mp_tac >>
         asm_rewrite_tac [] >>
         simp [arithmeticTheory.MULT_COMM])
     >- (
         strip_tac >>
         `divisor = 2 * residue` by
           (`ABS_DIFF
               (smtfp_circuit_round RNE 1w quotient residue divisor *
                divisor)
               (quotient * divisor + residue) =
             if smtfp_circuit_round_up RNE 1w quotient residue divisor then
               divisor - residue
             else residue` by
              (Cases_on
                 `smtfp_circuit_round_up RNE 1w quotient residue divisor` >>
               fs [smtfp_circuit_round_def] >>
               simp [arithmeticTheory.ABS_DIFF_def,
                     arithmeticTheory.LEFT_ADD_DISTRIB] >>
               decide_tac) >>
            `ABS_DIFF
               (2 ** (exponent - 1) *
                smtfp_circuit_round RNE 1w quotient residue
                  (2 ** (exponent - 1)))
               (residue + quotient * 2 ** (exponent - 1)) =
             if smtfp_circuit_round_up RNE 1w quotient residue divisor then
               divisor - residue
             else residue` by
              (qpat_x_assum
                 `ABS_DIFF
                    (smtfp_circuit_round RNE 1w quotient residue divisor *
                     divisor) _ = _`
                 mp_tac >>
               asm_rewrite_tac [] >>
               simp [arithmeticTheory.MULT_COMM,
                     arithmeticTheory.ADD_COMM]) >>

            `abs
               (2 pow 1 /
                2 pow (INT_MAX (:'w) + dimindex (:'t))) =
             2 pow 1 /
             2 pow (INT_MAX (:'w) + dimindex (:'t))` by
              (irule realTheory.ABS_REDUCE >> simp []) >>

            `ULP
               ((smtfp_rep
                  (smtfp_circuit_endpoint (format : ('t,'w) smtfp) 1w
                    exponent
                    (smtfp_circuit_round RNE 1w quotient residue
                      divisor))).Exponent,
                (:'t)) =
             &divisor *
               (2 pow 1 /
                2 pow (INT_MAX (:'w) + dimindex (:'t)))` by
              (mp_tac (Q.INST
                 [`format` |-> `format`, `sign` |-> `(1w : word1)`,
                  `exponent` |-> `exponent`,
                  `rounded` |->
                    `smtfp_circuit_round RNE 1w quotient residue divisor`]
                 smtfp_circuit_endpoint_ULP) >>
               impl_tac
               >- (asm_simp_tac pure_ss [] >> metis_tac []) >>
               strip_tac >>
               `smtfp_circuit_round RNE 1w quotient residue divisor <>
                2 ** (dimindex (:'t) + 1)` by decide_tac >>
               qpat_x_assum `ULP _ = _` (fn th => rewrite_tac [th]) >>
               qpat_x_assum
                 `smtfp_circuit_round RNE 1w quotient residue divisor <>
                  2 ** (dimindex (:'t) + 1)`
                 (fn th => rewrite_tac [th]) >>

               simp_tac pure_ss [boolTheory.COND_CLAUSES] >>

               `exponent = SUC (exponent - 1)` by decide_tac >>

               `2 ** exponent = 2 * divisor` by
                 (qpat_x_assum `exponent = SUC (exponent - 1)`
                    (fn th => once_rewrite_tac [th]) >>
                  rewrite_tac [CONJUNCT2 arithmeticTheory.EXP] >>
                  simp []) >>

               rewrite_tac [realTheory.REAL_OF_NUM_POW] >>

               qpat_x_assum `2 ** exponent = _`
                 (fn th => rewrite_tac [th]) >>

               irule smtfp_circuit_ULP_scale) >>
            `ULP
               ((smtfp_rep
                  (smtfp_circuit_endpoint (format : ('t,'w) smtfp) 1w
                    exponent
                    (smtfp_circuit_round RNE 1w quotient residue
                      (2 ** (exponent - 1))))).Exponent,
                (:'t)) =
             &divisor *
               (2 pow 1 /
                2 pow (INT_MAX (:'w) + dimindex (:'t)))` by
              (qpat_x_assum `ULP _ = _` mp_tac >>
               asm_rewrite_tac []) >>

            `abs
               (2 *
                inv (2 pow (INT_MAX (:'w) + dimindex (:'t)))) =
             2 pow 1 /
             2 pow (INT_MAX (:'w) + dimindex (:'t))` by
              simp [realTheory.ABS_MUL, realTheory.ABS_INV,
                    realTheory.real_div] >>


            qpat_x_assum `residue < divisor` (fn residue_lt =>
              mp_tac (Q.INST
                [`residue` |-> `residue`, `divisor` |-> `divisor`,
                 `up` |->
                   `smtfp_circuit_round_up
                      RNE 1w quotient residue divisor`,
                 `scale` |->
                   `2 pow 1 /
                    2 pow (INT_MAX (:'w) + dimindex (:'t))`]
                smtfp_circuit_tie_divisor) >>
              impl_tac
              >- (rewrite_tac [residue_lt] >>
                  conj_tac
                  >- (
                      simp []) >>

                  qpat_x_assum `2 * abs _ = ULP _` mp_tac >>

                  rewrite_tac [smtfp_circuit_scaled_abs_diff_neg_left] >>

                  qpat_x_assum
                    `ABS_DIFF
                       (2 ** (exponent - 1) * _)
                       (residue + quotient * 2 ** (exponent - 1)) = _`
                    (fn th => rewrite_tac [th]) >>

                  qpat_x_assum `abs (2 * inv (2 pow _)) = _`
                    (fn th => rewrite_tac [th]) >>

                  qpat_x_assum
                    `ULP
                       ((smtfp_rep
                          (smtfp_circuit_endpoint
                            (format : ('t,'w) smtfp) 1w exponent
                            (smtfp_circuit_round RNE 1w quotient residue
                              (2 ** (exponent - 1))))).Exponent,
                        (:'t)) = _`
                    (fn th => rewrite_tac [th]) >>

                  simp []) >>
              simp [])) >>

         `EVEN
            (smtfp_circuit_round RNE 1w quotient residue divisor)` by
           (Cases_on
              `smtfp_circuit_round_up RNE 1w quotient residue divisor` >>
            fs [smtfp_circuit_round_def,
                smtfp_circuit_round_up_def,
                arithmeticTheory.ODD_EVEN] >>
            TRY decide_tac >>
            simp [arithmeticTheory.EVEN_ADD]) >>

         mp_tac (Q.INST
           [`format` |-> `format`, `sign` |-> `(1w : word1)`,
            `exponent` |-> `exponent`,
            `rounded` |->
              `smtfp_circuit_round RNE 1w quotient residue divisor`]
           smtfp_circuit_endpoint_even_finite) >>
         impl_tac >- simp [] >>
         metis_tac [])
     >- (
         `ABS_DIFF
            (smtfp_circuit_round RNE 1w quotient residue divisor *
             divisor)
            (quotient * divisor + residue) =
          if smtfp_circuit_round_up RNE 1w quotient residue divisor then
            divisor - residue
          else residue` by
           (Cases_on
              `smtfp_circuit_round_up RNE 1w quotient residue divisor` >>
            fs [smtfp_circuit_round_def] >>
            simp [arithmeticTheory.ABS_DIFF_def,
                  arithmeticTheory.LEFT_ADD_DISTRIB] >>
            decide_tac) >>
         `ABS_DIFF
            (2 ** (exponent - 1) *
             smtfp_circuit_round RNE 1w quotient residue
               (2 ** (exponent - 1)))
            (residue + quotient * 2 ** (exponent - 1)) =
          if smtfp_circuit_round_up RNE 1w quotient residue divisor then
            divisor - residue
          else residue` by
           (qpat_x_assum
              `ABS_DIFF
                 (smtfp_circuit_round RNE 1w quotient residue divisor *
                  divisor) _ = _`
              mp_tac >>
            asm_rewrite_tac [] >>
            simp [arithmeticTheory.MULT_COMM,
                  arithmeticTheory.ADD_COMM]) >>

         `abs
            (2 * inv
              (2 pow (INT_MAX (:'w) + dimindex (:'t)))) =
          2 pow 1 /
          2 pow (INT_MAX (:'w) + dimindex (:'t))` by
           simp [realTheory.ABS_MUL, realTheory.ABS_INV,
                 realTheory.real_div] >>

         `0 <
            2 pow 1 /
            2 pow (INT_MAX (:'w) + dimindex (:'t))` by
           simp [] >>
         `2 *
            (if smtfp_circuit_round_up
                  RNE 1w quotient residue divisor then
               divisor - residue
             else residue) <=
          divisor` by
           (Cases_on
              `smtfp_circuit_round_up RNE 1w quotient residue divisor`
            >- (fs [smtfp_circuit_round_up_def] >> decide_tac)
            >- (Cases_on `residue = 0` >>
                fs [smtfp_circuit_round_up_def] >>
                decide_tac)) >>

         `2 *
            &(if smtfp_circuit_round_up
                 RNE 1w quotient residue divisor then
               divisor - residue
             else residue) <=
          &divisor` by
           (qpat_x_assum `2 * (if _ then _ else _) <= divisor`
              mp_tac >>
            simp [realTheory.REAL_OF_NUM_MUL]) >>

         `&divisor *
            (2 pow 1 /
             2 pow (INT_MAX (:'w) + dimindex (:'t))) <=
          ULP
            ((smtfp_rep
               (smtfp_circuit_endpoint (format : ('t,'w) smtfp) 1w
                 exponent
                 (smtfp_circuit_round RNE 1w quotient residue
                   divisor))).Exponent,
             (:'t))` by
           (mp_tac (Q.INST
              [`format` |-> `format`, `sign` |-> `(1w : word1)`,
               `exponent` |-> `exponent`,
               `rounded` |->
                 `smtfp_circuit_round RNE 1w quotient residue divisor`,
               `divisor` |-> `divisor`]
              smtfp_circuit_endpoint_ULP_divisor) >>
            impl_tac
            >- (asm_simp_tac pure_ss [] >> metis_tac []) >>
            simp []) >>

         `&divisor *
            (2 pow 1 /
             2 pow (INT_MAX (:'w) + dimindex (:'t))) <=
          ULP
            ((smtfp_rep
               (smtfp_circuit_endpoint (format : ('t,'w) smtfp) 1w
                 exponent
                 (smtfp_circuit_round RNE 1w quotient residue
                   (2 ** (exponent - 1))))).Exponent,
             (:'t))` by
           (qpat_x_assum `&divisor * _ <= ULP _` mp_tac >>
            asm_rewrite_tac []) >>

         rewrite_tac [smtfp_circuit_scaled_abs_diff_neg_left] >>

         qpat_x_assum
           `ABS_DIFF
              (2 ** (exponent - 1) * _)
              (residue + quotient * 2 ** (exponent - 1)) = _`
           (fn th => rewrite_tac [th]) >>

         qpat_x_assum `abs (2 * inv (2 pow _)) = _`
           (fn th => rewrite_tac [th]) >>

         irule realTheory.REAL_LE_TRANS >>
         qexists_tac
           `&divisor *
            (2 pow 1 /
             2 pow (INT_MAX (:'w) + dimindex (:'t)))` >>

         conj_tac
         >- (`(2 *
                &(if smtfp_circuit_round_up
                     RNE 1w quotient residue divisor then
                   divisor - residue
                 else residue)) *
               (2 pow 1 /
                2 pow (INT_MAX (:'w) + dimindex (:'t))) <=
              &divisor *
               (2 pow 1 /
                2 pow (INT_MAX (:'w) + dimindex (:'t)))` by
               (
                irule realTheory.REAL_LE_RMUL_IMP >>

                conj_tac
                >- (qpat_x_assum `2 * &(if _ then _ else _) <= _`
                      ACCEPT_TAC) >>
                qpat_x_assum `0 < 2 pow 1 / _`
                      (fn th =>
                         ACCEPT_TAC
                           (MATCH_MP realTheory.REAL_LT_IMP_LE th))) >>
             metis_tac [realTheory.REAL_MUL_ASSOC]) >>
         simp [])) >>

  simp_tac pure_ss [smt_float_round_def, smt_round_def,
                    TypeBase.case_def_of ``:smt_rounding``, LET_THM,
                    boolTheory.COND_CLAUSES] >>

  qpat_x_assum
    `round roundTiesToEven
       (-&(quotient * divisor + residue) * _) = _`
    (fn th => rewrite_tac [th]) >>

  qpat_x_assum
    `~float_is_zero
       (smtfp_rep
         (smtfp_circuit_endpoint
           (format : ('t,'w) smtfp) 1w exponent _))`
    (fn th => rewrite_tac [th]) >>

  rewrite_tac [boolTheory.COND_CLAUSES])
QED

Theorem smtfp_circuit_adjacent_negative_closest_hi:
  float_is_finite (lo : ('t,'w) float) /\
  float_is_finite hi /\ next_hi lo = hi /\
  float_to_real lo <= 0 /\
  float_to_real hi <= x /\ x <= float_to_real lo /\
  x - float_to_real hi <= float_to_real lo - x ==>
  is_closest float_is_finite x hi
Proof
  strip_tac >>
  rw [binary_ieeeTheory.is_closest_def, IN_DEF] >>
  rpt strip_tac >>
  Cases_on `abs (float_to_real b) <= abs (float_to_real lo)`
  >- (`x <= float_to_real b` by
        (mp_tac (Q.SPEC `float_to_real b` realTheory.ABS_LE) >>
         simp [realTheory.abs] >> realLib.REAL_ASM_ARITH_TAC) >>
      simp [realTheory.abs] >> realLib.REAL_ASM_ARITH_TAC) >>
  `abs (float_to_real lo) < abs (float_to_real b)` by
    (qpat_x_assum
       `~(abs (float_to_real b) <= abs (float_to_real lo))`
       mp_tac >>
     rewrite_tac [realTheory.REAL_NOT_LE]) >>
  `abs (float_to_real (next_hi lo)) <= abs (float_to_real b)` by
    (irule binary_ieeeTheory.next_hi_discrete >> simp []) >>
  Cases_on `float_to_real b <= 0`
  >- (`float_to_real (next_hi lo) <= 0` by
        realLib.REAL_ASM_ARITH_TAC >>
      `abs (float_to_real (next_hi lo)) =
       -float_to_real (next_hi lo)` by
        (once_rewrite_tac [GSYM realTheory.ABS_NEG] >>
         rewrite_tac [realTheory.ABS_REFL] >>
         realLib.REAL_ASM_ARITH_TAC) >>
      `abs (float_to_real b) = -float_to_real b` by
        (once_rewrite_tac [GSYM realTheory.ABS_NEG] >>
         rewrite_tac [realTheory.ABS_REFL] >>
         realLib.REAL_ASM_ARITH_TAC) >>
      `float_to_real b <= float_to_real (next_hi lo)` by
        (qpat_x_assum
           `abs (float_to_real (next_hi lo)) <= abs (float_to_real b)`
           mp_tac >>
         asm_rewrite_tac [] >>
         realLib.REAL_ASM_ARITH_TAC) >>
      simp [realTheory.abs] >> realLib.REAL_ASM_ARITH_TAC)
  >> `0 <= float_to_real b` by realLib.REAL_ASM_ARITH_TAC >>
  simp [realTheory.abs] >> realLib.REAL_ASM_ARITH_TAC
QED

Theorem smtfp_circuit_adjacent_negative_closest_lo:
  float_is_finite (lo : ('t,'w) float) /\
  float_is_finite hi /\ next_hi lo = hi /\
  float_to_real lo <= 0 /\
  float_to_real hi <= x /\ x <= float_to_real lo /\
  float_to_real lo - x <= x - float_to_real hi ==>
  is_closest float_is_finite x lo
Proof
  strip_tac >>
  rw [binary_ieeeTheory.is_closest_def, IN_DEF] >>
  rpt strip_tac >>
  Cases_on `abs (float_to_real b) <= abs (float_to_real lo)`
  >- (`float_to_real lo <= float_to_real b` by
        (mp_tac (Q.SPEC `float_to_real b` realTheory.ABS_LE) >>
         simp [realTheory.abs] >> realLib.REAL_ASM_ARITH_TAC) >>
      simp [realTheory.abs] >> realLib.REAL_ASM_ARITH_TAC) >>
  `abs (float_to_real lo) < abs (float_to_real b)` by
    (qpat_x_assum
       `~(abs (float_to_real b) <= abs (float_to_real lo))`
       mp_tac >>
     rewrite_tac [realTheory.REAL_NOT_LE]) >>
  `abs (float_to_real (next_hi lo)) <= abs (float_to_real b)` by
    (irule binary_ieeeTheory.next_hi_discrete >> simp []) >>
  Cases_on `float_to_real b <= 0`
  >- (`float_to_real (next_hi lo) <= 0` by
        realLib.REAL_ASM_ARITH_TAC >>
      `abs (float_to_real (next_hi lo)) =
       -float_to_real (next_hi lo)` by
        (once_rewrite_tac [GSYM realTheory.ABS_NEG] >>
         rewrite_tac [realTheory.ABS_REFL] >>
         realLib.REAL_ASM_ARITH_TAC) >>
      `abs (float_to_real b) = -float_to_real b` by
        (once_rewrite_tac [GSYM realTheory.ABS_NEG] >>
         rewrite_tac [realTheory.ABS_REFL] >>
         realLib.REAL_ASM_ARITH_TAC) >>
      `float_to_real b <= float_to_real (next_hi lo)` by
        (qpat_x_assum
           `abs (float_to_real (next_hi lo)) <= abs (float_to_real b)`
           mp_tac >>
         asm_rewrite_tac [] >>
         realLib.REAL_ASM_ARITH_TAC) >>
      simp [realTheory.abs] >> realLib.REAL_ASM_ARITH_TAC)
  >> `0 <= float_to_real b` by realLib.REAL_ASM_ARITH_TAC >>
  simp [realTheory.abs] >> realLib.REAL_ASM_ARITH_TAC
QED

Theorem smtfp_circuit_RNA_negative_endpoint:
  2 <= dimindex (:'w) /\
  1 <= exponent /\ exponent <= dimword (:'w) - 2 /\
  0 < quotient /\
  quotient < 2 ** (dimindex (:'t) + 1) /\
  quotient + 1 <= 2 ** (dimindex (:'t) + 1) /\
  (quotient < 2 ** dimindex (:'t) ==> exponent = 1) /\
  (quotient + 1 = 2 ** (dimindex (:'t) + 1) ==>
   exponent < dimword (:'w) - 2) /\
  divisor = 2 ** (exponent - 1) /\ residue < divisor ==>
  let units = quotient * divisor + residue in
  let rounded =
    smtfp_circuit_round RNA 1w quotient residue divisor in
  let output =
    smtfp_rep
      (smtfp_circuit_endpoint (format : ('t,'w) smtfp) 1w exponent rounded) in
  smt_float_round RNA F
    (-&units *
      (2 pow 1 / 2 pow (INT_MAX (:'w) + dimindex (:'t)))) = output
Proof
  simp_tac pure_ss [LET_THM] >> strip_tac >>
  `0 < divisor` by simp [] >>
  qabbrev_tac
    `u = 2 pow 1 / 2 pow (INT_MAX (:'w) + dimindex (:'t))` >>
  qabbrev_tac
    `lo = smtfp_rep
      (smtfp_circuit_endpoint (format : ('t,'w) smtfp) 1w exponent quotient)` >>
  qabbrev_tac
    `hi = smtfp_rep
      (smtfp_circuit_endpoint (format : ('t,'w) smtfp) 1w exponent
        (quotient + 1))` >>
  `float_is_finite lo /\ float_is_finite hi` by
    (simp [Abbr `lo`, Abbr `hi`] >> conj_tac >>
     irule smtfp_circuit_endpoint_finite >> simp []) >>
  `next_hi lo = hi` by
    (simp [Abbr `lo`, Abbr `hi`] >>
     irule smtfp_circuit_endpoint_next_hi >> simp []) >>
  `float_to_real lo = -&(quotient * divisor) * u /\
   float_to_real hi = -&((quotient + 1) * divisor) * u` by
    (simp_tac pure_ss [Abbr `lo`, Abbr `hi`, Abbr `u`] >>
     conj_tac
     >- (mp_tac (Q.INST
           [`format` |-> `format`, `sign` |-> `(1w : word1)`,
            `exponent` |-> `exponent`, `rounded` |-> `quotient`]
           smtfp_circuit_endpoint_value) >>
         impl_tac >- simp [] >>
         simp []) >>
     mp_tac (Q.INST
       [`format` |-> `format`, `sign` |-> `(1w : word1)`,
        `exponent` |-> `exponent`, `rounded` |-> `quotient + 1`]
       smtfp_circuit_endpoint_value) >>
     impl_tac >- simp [] >>
     simp []) >>
  `0 < u` by simp [Abbr `u`] >>
  `~float_is_zero lo /\ ~float_is_zero hi` by
    (simp [binary_ieeeTheory.float_is_zero_to_real] >>
     realLib.REAL_ASM_ARITH_TAC) >>
  Cases_on `residue = 0`
  >- (
      `quotient * divisor + residue = quotient * divisor` by simp [] >>
      `smtfp_circuit_round RNA 1w quotient residue divisor = quotient` by
        simp [smtfp_circuit_round_def,
              smtfp_circuit_round_up_def] >>
      `-u * &(quotient * 2 ** (exponent - 1)) =
       float_to_real lo` by
        (qpat_x_assum `float_to_real lo = _`
           (fn th => rewrite_tac [th]) >>
         asm_rewrite_tac [] >>
         simp [realTheory.REAL_MUL_LNEG,
               realTheory.REAL_MUL_COMM]) >>
      `float_to_real lo <> 0` by
        (qpat_x_assum `~float_is_zero lo` mp_tac >>
         rewrite_tac [binary_ieeeTheory.float_is_zero_to_real]) >>
      `round_tiesToAway
         (-u * &(quotient * 2 ** (exponent - 1))) = lo` by
        (qpat_x_assum `_ = float_to_real lo`
           (fn th => rewrite_tac [th]) >>
         irule round_tiesToAway_representable_nonzero >>
         simp []) >>
      `-&(quotient * divisor + residue) * u =
       -u * &(quotient * 2 ** (exponent - 1))` by
        (asm_rewrite_tac [] >>
         simp [realTheory.REAL_MUL_LNEG,
               realTheory.REAL_MUL_COMM]) >>
      `round_tiesToAway
         (-&(quotient * divisor + residue) * u) = lo` by
        (qpat_x_assum `_ = -u * _` (fn th => rewrite_tac [th]) >>
         qpat_x_assum `round_tiesToAway _ = lo` ACCEPT_TAC) >>
      `smtfp_rep
         (smtfp_circuit_endpoint (format : ('t,'w) smtfp) 1w exponent
           (smtfp_circuit_round RNA 1w quotient residue divisor)) = lo` by
        (qpat_x_assum
           `smtfp_circuit_round RNA 1w quotient residue divisor = quotient`
         (fn th => rewrite_tac [th]) >>
         simp [Abbr `lo`]) >>
      simp_tac pure_ss [smt_float_round_def, smt_round_def,
                        TypeBase.case_def_of ``:smt_rounding``,
                        LET_THM, boolTheory.COND_CLAUSES] >>
      asm_simp_tac pure_ss [boolTheory.COND_CLAUSES] >>
      REFL_TAC) >>
  `quotient * divisor < quotient * divisor + residue /\
   quotient * divisor + residue < (quotient + 1) * divisor` by
    (simp [arithmeticTheory.LEFT_ADD_DISTRIB] >> decide_tac) >>
  `0 < quotient * 2 ** (exponent - 1)` by simp [] >>
  `0 < (&(quotient * 2 ** (exponent - 1)) : real)` by simp [] >>
  `float_to_real hi <
      -&(quotient * divisor + residue) * u /\
   -&(quotient * divisor + residue) * u < float_to_real lo /\
   float_to_real lo < 0` by
    (simp [realTheory.REAL_OF_NUM_ADD,
           realTheory.REAL_OF_NUM_MUL] >>
     rewrite_tac [realTheory.REAL_MUL_LNEG,
                  realTheory.REAL_NEG_LT0] >>
     irule realTheory.REAL_LT_MUL >> simp []) >>
  `-threshold (:'t # 'w) <
       -&(quotient * divisor + residue) * u /\
   -&(quotient * divisor + residue) * u < threshold (:'t # 'w)` by
    (mp_tac (Q.INST [`f` |-> `hi`]
       (INST_TYPE [alpha |-> ``:'t``, beta |-> ``:'w``]
         binary_ieeeTheory.abs_float_bounds)) >>
     impl_tac >- simp [] >>
     rewrite_tac [binary_ieeeTheory.float_to_real_float_abs] >>
     strip_tac >>
     assume_tac (Q.SPEC `float_to_real hi` realTheory.ABS_LE) >>
     mp_tac (INST_TYPE [alpha |-> ``:'t``, beta |-> ``:'w``]
       binary_ieeeTheory.largest_lt_threshold) >>
     realLib.REAL_ASM_ARITH_TAC) >>
  Cases_on `smtfp_circuit_round_up RNA 1w quotient residue divisor`
  >- (
      `smtfp_circuit_round RNA 1w quotient residue divisor =
        quotient + 1` by
        simp [smtfp_circuit_round_def] >>
      `divisor <= 2 * residue` by
        fs [smtfp_circuit_round_up_def] >>
      `(-&(quotient * divisor + residue) * u) -
         float_to_real hi <=
       float_to_real lo -
         (-&(quotient * divisor + residue) * u)` by
        (mp_tac smtfp_circuit_scaled_midpoint_hi >>
         impl_tac >- simp [] >> strip_tac >>
         realLib.REAL_ASM_ARITH_TAC) >>
      `float_to_real lo <= 0` by realLib.REAL_ASM_ARITH_TAC >>
      `float_to_real hi <=
         -&(quotient * divisor + residue) * u` by
        realLib.REAL_ASM_ARITH_TAC >>
      `-&(quotient * divisor + residue) * u <=
         float_to_real lo` by realLib.REAL_ASM_ARITH_TAC >>
      `is_closest float_is_finite
         (-&(quotient * divisor + residue) * u) hi` by
        (mp_tac (INST
           [``x:real`` |->
              ``-&(quotient * divisor + residue) * u``]
           smtfp_circuit_adjacent_negative_closest_hi) >>
         impl_tac >- simp [] >> simp []) >>
      `-&(quotient * divisor + residue) * u <> 0` by
        realLib.REAL_ASM_ARITH_TAC >>
      `abs (-&(quotient * divisor + residue) * u) =
       -(-&(quotient * divisor + residue) * u)` by
        (once_rewrite_tac [GSYM realTheory.ABS_NEG] >>
         rewrite_tac [realTheory.ABS_REFL] >>
         realLib.REAL_ASM_ARITH_TAC) >>
      `abs (float_to_real hi) = -float_to_real hi` by
        (once_rewrite_tac [GSYM realTheory.ABS_NEG] >>
         rewrite_tac [realTheory.ABS_REFL] >>
         realLib.REAL_ASM_ARITH_TAC) >>
      `abs (-&(quotient * divisor + residue) * u) <=
       abs (float_to_real hi)` by
        realLib.REAL_ASM_ARITH_TAC >>
      `round_tiesToAway (-&(quotient * divisor + residue) * u) = hi` by
        (mp_tac (INST
           [``x:real`` |->
              ``-&(quotient * divisor + residue) * u``,
            ``y:('t,'w) float`` |-> ``hi:('t,'w) float``]
           round_tiesToAway_from_closest_away) >>
         impl_tac >-
           simp [] >>
         simp []) >>
      simp [smt_float_round_def,
            smt_round_def]) >>
  `smtfp_circuit_round RNA 1w quotient residue divisor = quotient` by
    simp [smtfp_circuit_round_def] >>
  `2 * residue < divisor` by
    fs [smtfp_circuit_round_up_def] >>
  `float_to_real lo -
       (-&(quotient * divisor + residue) * u) <
   (-&(quotient * divisor + residue) * u) -
       float_to_real hi` by
    (mp_tac smtfp_circuit_scaled_midpoint_lo >>
     impl_tac >- simp [] >> strip_tac >>
     realLib.REAL_ASM_ARITH_TAC) >>
  `float_to_real lo -
       (-&(quotient * divisor + residue) * u) <=
   (-&(quotient * divisor + residue) * u) -
       float_to_real hi` by realLib.REAL_ASM_ARITH_TAC >>
  `float_to_real lo <= 0` by realLib.REAL_ASM_ARITH_TAC >>
  `float_to_real hi <=
     -&(quotient * divisor + residue) * u` by
    realLib.REAL_ASM_ARITH_TAC >>
  `-&(quotient * divisor + residue) * u <=
     float_to_real lo` by realLib.REAL_ASM_ARITH_TAC >>
  `is_closest float_is_finite
     (-&(quotient * divisor + residue) * u) lo` by
    (mp_tac (INST
       [``x:real`` |->
          ``-&(quotient * divisor + residue) * u``]
       smtfp_circuit_adjacent_negative_closest_lo) >>
     impl_tac >- simp [] >> simp []) >>
  `abs (float_to_real lo -
          (-&(quotient * divisor + residue) * u)) =
   float_to_real lo -
     (-&(quotient * divisor + residue) * u)` by
    (rewrite_tac [realTheory.ABS_REFL] >>
     realLib.REAL_ASM_ARITH_TAC) >>
  `abs (float_to_real hi -
          (-&(quotient * divisor + residue) * u)) =
   (-&(quotient * divisor + residue) * u) - float_to_real hi` by
    (`float_to_real hi -
        (-&(quotient * divisor + residue) * u) =
      -((-&(quotient * divisor + residue) * u) - float_to_real hi)` by
       realLib.REAL_ASM_ARITH_TAC >>
     qpat_x_assum `float_to_real hi - _ = _`
       (fn th => rewrite_tac [th]) >>
     rewrite_tac [realTheory.ABS_NEG] >>
     rewrite_tac [realTheory.ABS_REFL] >>
     realLib.REAL_ASM_ARITH_TAC) >>
  `abs (float_to_real lo -
          (-&(quotient * divisor + residue) * u)) <
   abs (float_to_real hi -
          (-&(quotient * divisor + residue) * u))` by
    realLib.REAL_ASM_ARITH_TAC >>
  `float_is_finite (next_hi lo)` by simp [] >>
  `float_to_real (next_hi lo) <
     -&(quotient * divisor + residue) * u` by
    simp [] >>
  `abs (float_to_real lo -
          (-&(quotient * divisor + residue) * u)) <
   abs (float_to_real (next_hi lo) -
          (-&(quotient * divisor + residue) * u))` by
    (qpat_x_assum `next_hi lo = hi` (fn th => rewrite_tac [th]) >>
     qpat_x_assum `abs (float_to_real lo - _) <
                     abs (float_to_real hi - _)` ACCEPT_TAC) >>
  `round_tiesToAway (-&(quotient * divisor + residue) * u) = lo` by
    (mp_tac (INST
       [``x:real`` |->
          ``-&(quotient * divisor + residue) * u``,
        ``y:('t,'w) float`` |-> ``lo:('t,'w) float``]
       round_tiesToAway_negative_inward) >>
     impl_tac >-
       (asm_simp_tac pure_ss [] >>
        simp []) >>
     simp []) >>
  simp [smt_float_round_def,
        smt_round_def]
QED
Theorem smtfp_circuit_directed_negative_endpoint:
  2 <= dimindex (:'w) /\
  1 <= exponent /\ exponent <= dimword (:'w) - 2 /\
  0 < quotient /\
  quotient < 2 ** (dimindex (:'t) + 1) /\
  quotient + 1 <= 2 ** (dimindex (:'t) + 1) /\
  (quotient < 2 ** dimindex (:'t) ==> exponent = 1) /\
  (quotient + 1 = 2 ** (dimindex (:'t) + 1) ==>
   exponent < dimword (:'w) - 2) /\
  divisor = 2 ** (exponent - 1) /\ residue < divisor /\
  (mode = RTP \/ mode = RTN \/ mode = RTZ) ==>
  let units = quotient * divisor + residue in
  let rounded =
    smtfp_circuit_round mode 1w quotient residue divisor in
  let output =
    smtfp_rep
      (smtfp_circuit_endpoint (format : ('t,'w) smtfp) 1w exponent rounded) in
  smt_float_round mode F
    (-&units *
      (2 pow 1 / 2 pow (INT_MAX (:'w) + dimindex (:'t)))) = output
Proof
  simp_tac pure_ss [LET_THM] >> disch_tac >>
  REPEAT (qpat_x_assum `_ /\ _`
    (fn th => let val (th1, th2) = CONJ_PAIR th in
                ASSUME_TAC th1 >> ASSUME_TAC th2
              end)) >>
  `0 < divisor` by simp [] >>
  qabbrev_tac
    `u = 2 pow 1 / 2 pow (INT_MAX (:'w) + dimindex (:'t))` >>
  qabbrev_tac
    `lo = smtfp_rep
      (smtfp_circuit_endpoint (format : ('t,'w) smtfp) 1w exponent quotient)` >>
  qabbrev_tac
    `hi = smtfp_rep
      (smtfp_circuit_endpoint (format : ('t,'w) smtfp) 1w exponent
        (quotient + 1))` >>
  `float_is_finite lo /\ float_is_finite hi` by
    (simp [Abbr `lo`, Abbr `hi`] >> conj_tac >>
     irule smtfp_circuit_endpoint_finite >> simp []) >>
  `next_hi lo = hi` by
    (simp [Abbr `lo`, Abbr `hi`] >>
     irule smtfp_circuit_endpoint_next_hi >> simp []) >>
  `float_to_real lo = -&(quotient * divisor) * u /\
   float_to_real hi = -&((quotient + 1) * divisor) * u` by
    (simp_tac pure_ss [Abbr `lo`, Abbr `hi`, Abbr `u`] >>
     conj_tac
     >- (mp_tac (Q.INST
           [`format` |-> `format`, `sign` |-> `(1w : word1)`,
            `exponent` |-> `exponent`, `rounded` |-> `quotient`]
           smtfp_circuit_endpoint_value) >>
         impl_tac >- simp [] >>
         simp []) >>
     mp_tac (Q.INST
       [`format` |-> `format`, `sign` |-> `(1w : word1)`,
        `exponent` |-> `exponent`, `rounded` |-> `quotient + 1`]
       smtfp_circuit_endpoint_value) >>
     impl_tac >- simp [] >>
     simp []) >>
  `0 < u` by simp [Abbr `u`] >>
  `~float_is_zero lo /\ ~float_is_zero hi` by
    (simp [binary_ieeeTheory.float_is_zero_to_real] >>
     realLib.REAL_ASM_ARITH_TAC) >>
  Cases_on `residue = 0`
  >- (
      `quotient * divisor + residue = quotient * divisor` by simp [] >>
      `smtfp_circuit_round mode 1w quotient residue divisor = quotient` by
        simp [smtfp_circuit_round_def,
              smtfp_circuit_round_up_def] >>
      `-&(quotient * divisor + residue) * u = float_to_real lo` by
        (qpat_x_assum `float_to_real lo = _`
           (fn th => rewrite_tac [th]) >>
         asm_rewrite_tac []) >>
      `float_to_real lo <> 0` by
        (qpat_x_assum `~float_is_zero lo` mp_tac >>
         rewrite_tac [binary_ieeeTheory.float_is_zero_to_real]) >>
      `smt_float_round mode F
         (-&(quotient * divisor + residue) * u) = lo` by
        (qpat_x_assum
           `-&(quotient * divisor + residue) * u = float_to_real lo`
           (fn th => rewrite_tac [th]) >>
         irule smt_float_round_representable_nonzero >>
         simp []) >>
      `smtfp_rep
         (smtfp_circuit_endpoint (format : ('t,'w) smtfp) 1w exponent
           (smtfp_circuit_round mode 1w quotient residue divisor)) = lo` by
        (qpat_x_assum
           `smtfp_circuit_round mode 1w quotient residue divisor = quotient`
         (fn th => rewrite_tac [th]) >>
         simp [Abbr `lo`]) >>
      asm_simp_tac pure_ss [] >>
      REFL_TAC) >>
  `quotient * divisor < quotient * divisor + residue /\
   quotient * divisor + residue < (quotient + 1) * divisor` by
    (simp [arithmeticTheory.LEFT_ADD_DISTRIB] >> decide_tac) >>
  `0 < (&(quotient * 2 ** (exponent - 1)) : real)` by simp [] >>
  `float_to_real hi <
      -&(quotient * divisor + residue) * u /\
   -&(quotient * divisor + residue) * u < float_to_real lo /\
   float_to_real lo < 0` by
    (simp [realTheory.REAL_OF_NUM_ADD,
           realTheory.REAL_OF_NUM_MUL] >>
     rewrite_tac [realTheory.REAL_MUL_LNEG,
                  realTheory.REAL_NEG_LT0] >>
     irule realTheory.REAL_LT_MUL >> simp []) >>
  `-largest (:'t # 'w) <= -&(quotient * divisor + residue) * u /\
   -&(quotient * divisor + residue) * u <= largest (:'t # 'w)` by
    (mp_tac (Q.INST [`f` |-> `hi`]
       (INST_TYPE [alpha |-> ``:'t``, beta |-> ``:'w``]
         binary_ieeeTheory.abs_float_bounds)) >>
     impl_tac >- simp [] >>
     rewrite_tac [binary_ieeeTheory.float_to_real_float_abs] >>
     strip_tac >>
     assume_tac (Q.SPEC `float_to_real hi` realTheory.ABS_LE) >>
     realLib.REAL_ASM_ARITH_TAC) >>
  `-largest (:'t # 'w) <=
     -&(quotient * divisor + residue) * u` by
    realLib.REAL_ASM_ARITH_TAC >>
  `-&(quotient * divisor + residue) * u <= largest (:'t # 'w)` by
    realLib.REAL_ASM_ARITH_TAC >>
  `float_is_finite (next_hi lo)` by simp [] >>
  `~float_is_zero (next_hi lo)` by simp [] >>
  `float_to_real (next_hi lo) <
     -&(quotient * divisor + residue) * u` by simp [] >>
  `float_to_real (next_hi lo) <=
     -&(quotient * divisor + residue) * u` by
    realLib.REAL_ASM_ARITH_TAC >>
  `-&(quotient * divisor + residue) * u <= float_to_real lo` by
    realLib.REAL_ASM_ARITH_TAC >>
  `float_to_real (next_hi lo) < 0` by
    realLib.REAL_ASM_ARITH_TAC >>
  Cases_on `mode`
  >- fs [smt_rounding_distinctness]
  >- fs [smt_rounding_distinctness]
  >- (
      `smtfp_circuit_round RTP 1w quotient residue divisor = quotient` by
        simp [smtfp_circuit_round_def,
              smtfp_circuit_round_up_def] >>
      `round roundTowardPositive
         (-&(quotient * divisor + residue) * u) = lo` by
        (mp_tac (INST
           [``x:real`` |->
              ``-&(quotient * divisor + residue) * u``,
            ``y:('t,'w) float`` |-> ``lo:('t,'w) float``]
           round_RTP_negative_inward) >>
         impl_tac >-
           (asm_simp_tac pure_ss [] >> simp []) >>
         simp []) >>
      simp_tac pure_ss [smt_float_round_def, smt_round_def,
                        TypeBase.case_def_of ``:smt_rounding``, LET_THM,
                        boolTheory.COND_CLAUSES] >>
      qpat_x_assum `round roundTowardPositive _ = lo`
        (fn th => rewrite_tac [th]) >>
      qpat_x_assum `~float_is_zero lo`
        (fn th => rewrite_tac [th]) >>
      rewrite_tac [boolTheory.COND_CLAUSES] >>
      qpat_x_assum `smtfp_circuit_round RTP _ _ _ _ = _`
        (fn th => rewrite_tac [th]) >>
      simp_tac pure_ss [Abbr `lo`] >> REFL_TAC)
  >- (
      `smtfp_circuit_round RTN 1w quotient residue divisor =
        quotient + 1` by
        simp [smtfp_circuit_round_def,
              smtfp_circuit_round_up_def] >>
      `round roundTowardNegative
         (-&(quotient * divisor + residue) * u) = hi` by
        (mp_tac (INST
           [``x:real`` |->
              ``-&(quotient * divisor + residue) * u``,
            ``lo:('t,'w) float`` |-> ``lo:('t,'w) float``]
           round_RTN_negative_next_hi) >>
         impl_tac >-
           (asm_simp_tac pure_ss [] >> simp []) >>
         simp []) >>
      simp_tac pure_ss [smt_float_round_def, smt_round_def,
                        TypeBase.case_def_of ``:smt_rounding``, LET_THM,
                        boolTheory.COND_CLAUSES] >>
      qpat_x_assum `round roundTowardNegative _ = hi`
        (fn th => rewrite_tac [th]) >>
      qpat_x_assum `~float_is_zero hi`
        (fn th => rewrite_tac [th]) >>
      rewrite_tac [boolTheory.COND_CLAUSES] >>
      qpat_x_assum `smtfp_circuit_round RTN _ _ _ _ = _`
        (fn th => rewrite_tac [th]) >>
      simp_tac pure_ss [Abbr `hi`] >> REFL_TAC)
  >- (
      `smtfp_circuit_round RTZ 1w quotient residue divisor = quotient` by
        simp [smtfp_circuit_round_def,
              smtfp_circuit_round_up_def] >>
      `round roundTowardZero
         (-&(quotient * divisor + residue) * u) = lo` by
        (irule binary_ieeeTheory.round_roundTowardZero >>
         conj_tac
         >- (qexists_tac `float_to_real lo` >>
             conj_tac
             >- (irule smtfp_float_value_finite >> simp []) >>
             conj_tac
             >- (qpat_x_assum `float_to_real lo = _`
                   (fn th => rewrite_tac [th]) >>
                 rewrite_tac [smtfp_circuit_scaled_abs_diff_neg] >>
                 simp [arithmeticTheory.ABS_DIFF_def] >>
                 `abs u = u` by
                   (irule realTheory.ABS_REDUCE >>
                    realLib.REAL_ASM_ARITH_TAC) >>
                 qpat_x_assum `abs u = u`
                   (fn th => rewrite_tac [th]) >>
                 `u * &residue < u * &divisor` by
                   (irule realTheory.REAL_LT_LMUL_IMP >> simp []) >>
                 `&divisor * u <= ULP (lo.Exponent, (:'t))` by
                   (simp_tac pure_ss [Abbr `lo`, Abbr `u`] >>
                    irule smtfp_circuit_endpoint_ULP_divisor >>
                    simp []) >>
                 metis_tac [realTheory.REAL_LTE_TRANS,
                            realTheory.REAL_MUL_COMM]) >>
             `abs (float_to_real lo) = -float_to_real lo` by
               (once_rewrite_tac [GSYM realTheory.ABS_NEG] >>
                rewrite_tac [realTheory.ABS_REFL] >>
                realLib.REAL_ASM_ARITH_TAC) >>
             `abs (-&(quotient * divisor + residue) * u) =
                -(-&(quotient * divisor + residue) * u)` by
               (once_rewrite_tac [GSYM realTheory.ABS_NEG] >>
                rewrite_tac [realTheory.ABS_REFL] >>
                realLib.REAL_ASM_ARITH_TAC) >>
             realLib.REAL_ASM_ARITH_TAC) >>
         conj_tac
         >- (`abs (-&(quotient * divisor + residue) * u) =
                -(-&(quotient * divisor + residue) * u)` by
               (once_rewrite_tac [GSYM realTheory.ABS_NEG] >>
                rewrite_tac [realTheory.ABS_REFL] >>
                realLib.REAL_ASM_ARITH_TAC) >>
             realLib.REAL_ASM_ARITH_TAC) >>
         `1 <= quotient * divisor + residue` by
           (simp [] >> decide_tac) >>
         `abs (-&(quotient * divisor + residue) * u) =
            &(quotient * divisor + residue) * u` by
           (once_rewrite_tac [GSYM realTheory.ABS_NEG] >>
            rewrite_tac [realTheory.ABS_REFL] >>
            realLib.REAL_ASM_ARITH_TAC) >>
         simp [binary_ieeeTheory.ulp_def,
               binary_ieeeTheory.ULP_def, Abbr `u`]) >>
      simp_tac pure_ss [smt_float_round_def, smt_round_def,
                        TypeBase.case_def_of ``:smt_rounding``, LET_THM,
                        boolTheory.COND_CLAUSES] >>
      qpat_x_assum `round roundTowardZero _ = lo`
        (fn th => rewrite_tac [th]) >>
      qpat_x_assum `~float_is_zero lo`
        (fn th => rewrite_tac [th]) >>
      rewrite_tac [boolTheory.COND_CLAUSES] >>
      qpat_x_assum `smtfp_circuit_round RTZ _ _ _ _ = _`
        (fn th => rewrite_tac [th]) >>
      simp_tac pure_ss [Abbr `lo`] >> REFL_TAC)
QED
Theorem circuit_normalized_upper:
  0 < units /\ 1 <= maximum_exponent /\
  exponent =
    MIN maximum_exponent
      (MAX 1 (LOG2 units + 1 - fraction_width)) /\
  exponent < maximum_exponent ==>
  units < 2 ** (fraction_width + 1) * 2 ** (exponent - 1)
Proof
  strip_tac >>
  `exponent = MAX 1 (LOG2 units + 1 - fraction_width)` by
    fs [arithmeticTheory.MIN_ALT] >>
  mp_tac
    (REWRITE_RULE [GSYM bitTheory.LOG2_def]
      (Q.SPEC `units` logrootTheory.LOG2_PROPERTY)) >>
  impl_tac >- simp [] >> strip_tac >>
  Cases_on `exponent = 1`
  >- (`LOG2 units + 1 <= fraction_width + 1` by
        fs [arithmeticTheory.MAX_ALT] >>
      `SUC (LOG2 units) <= fraction_width + 1` by decide_tac >>
      `2 ** SUC (LOG2 units) <= 2 ** (fraction_width + 1)` by
        simp [arithmeticTheory.EXP_BASE_LE_MONO] >>
      `units < 2 ** (fraction_width + 1)` by
        (MATCH_MP_TAC arithmeticTheory.LESS_LESS_EQ_TRANS >>
         Q.EXISTS_TAC `2 ** SUC (LOG2 units)` >>
         (CONJ_TAC THENL
            [qpat_x_assum `units < _` ACCEPT_TAC,
             qpat_x_assum `_ <= _` ACCEPT_TAC])) >>
      simp []) >>
  `1 <= exponent` by
    fs [arithmeticTheory.MAX_ALT] >>
  `1 < exponent` by decide_tac >>
  `exponent = LOG2 units + 1 - fraction_width` by
    fs [arithmeticTheory.MAX_ALT] >>
  `SUC (LOG2 units) = fraction_width + exponent` by decide_tac >>
  `units < 2 ** (fraction_width + exponent)` by
    (qpat_x_assum `units < 2 ** SUC (LOG2 units)` mp_tac >>
     simp []) >>
  `fraction_width + exponent =
   fraction_width + 1 + (exponent - 1)` by decide_tac >>
  `(2 : num) ** (fraction_width + exponent) =
   2 ** (fraction_width + 1) * 2 ** (exponent - 1)` by
    (qpat_x_assum
       `fraction_width + exponent = _`
       (fn th => once_rewrite_tac [th]) >>
     rewrite_tac [arithmeticTheory.EXP_ADD]) >>
  qpat_x_assum
    `(2 : num) ** (fraction_width + exponent) = _`
    (fn th => rewrite_tac [GSYM th]) >>
  qpat_x_assum
    `units < 2 ** (fraction_width + exponent)` ACCEPT_TAC
QED

Theorem smtfp_circuit_quotient_normalized_upper:
  0 < scale /\ 0 < magnitude /\ 1 <= maximum_exponent /\
  smtfp_circuit_encoded_exponent maximum_exponent fraction_width
      scale magnitude < maximum_exponent ==>
  smtfp_circuit_quotient maximum_exponent fraction_width scale magnitude <
    2 ** (fraction_width + 1)
Proof
  strip_tac >>
  mp_tac (Q.INST
    [`maximum_exponent` |-> `maximum_exponent`,
     `fraction_width` |-> `fraction_width`, `scale` |-> `scale`,
     `magnitude` |-> `magnitude`]
    smtfp_circuit_effective_encoded) >>
  impl_tac >- simp [] >> strip_tac >>
  `0 < magnitude * 2 ** (scale - 1)` by simp [] >>
  `magnitude * 2 ** (scale - 1) <
   2 ** (fraction_width + 1) *
   2 **
     (smtfp_circuit_encoded_exponent maximum_exponent fraction_width
        scale magnitude - 1)` by
    (irule (GEN_ALL circuit_normalized_upper) >>
     conj_tac
     >- qpat_x_assum
          `0 < magnitude * 2 ** (scale - 1)` ACCEPT_TAC >>
     qexists_tac `maximum_exponent` >> simp [] >>
     fs [circuit_wanted_exponent_units,
         smtfp_circuit_encoded_exponent_def]) >>
  mp_tac (Q.INST
    [`maximum_exponent` |-> `maximum_exponent`,
     `fraction_width` |-> `fraction_width`, `scale` |-> `scale`,
     `magnitude` |-> `magnitude`]
    smtfp_circuit_quotient_units) >>
  impl_tac >- simp [] >> strip_tac >>
  fs [] >>
  irule (iffRL arithmeticTheory.DIV_LT_X) >> simp []
QED

Theorem smtfp_circuit_endpoint_round_nonzero[local]:
  2 <= dimindex (:'w) /\
  1 <= exponent /\ exponent <= dimword (:'w) - 2 /\
  0 < quotient /\
  quotient < 2 ** (dimindex (:'t) + 1) /\
  quotient + 1 <= 2 ** (dimindex (:'t) + 1) /\
  (quotient < 2 ** dimindex (:'t) ==> exponent = 1) /\
  (quotient + 1 = 2 ** (dimindex (:'t) + 1) ==>
   exponent < dimword (:'w) - 2) /\
  divisor = 2 ** (exponent - 1) /\
  residue < divisor /\
  ~float_is_zero
    (smtfp_rep
      (smtfp_circuit_endpoint (format : ('t,'w) smtfp)
        sign exponent
        (smtfp_circuit_round mode sign quotient residue divisor))) ==>
  smt_float_round mode to_neg
    ((if sign = 0w then &(quotient * divisor + residue)
      else -&(quotient * divisor + residue)) *
     (2 pow 1 / 2 pow (INT_MAX (:'w) + dimindex (:'t)))) =
  smtfp_rep
    (smtfp_circuit_endpoint format sign exponent
      (smtfp_circuit_round mode sign quotient residue divisor))
Proof
  strip_tac >>
  irule smt_float_round_to_neg_nonzero_result >>
  conj_tac
  >- qpat_x_assum
        `~float_is_zero
           (smtfp_rep
             (smtfp_circuit_endpoint (format : ('t,'w) smtfp)
               sign exponent
               (smtfp_circuit_round mode sign quotient residue divisor)))`
        ACCEPT_TAC
  >- (`(1w : word1) <> 0w` by wordsLib.WORD_DECIDE_TAC >>
      wordsLib.Cases_on_word_value `sign` >>
      Cases_on `mode`
      >- (qpat_x_assum `(1w : word1) <> 0w`
            (fn th => simp_tac std_ss [th]) >>
          irule (SIMP_RULE pure_ss [LET_THM]
            smtfp_circuit_RNE_negative_endpoint) >>
          asm_simp_tac std_ss [])
      >- (qpat_x_assum `(1w : word1) <> 0w`
            (fn th => simp_tac std_ss [th]) >>
          irule (SIMP_RULE pure_ss [LET_THM]
            smtfp_circuit_RNA_negative_endpoint) >>
          asm_simp_tac std_ss [])
      >- (qpat_x_assum `(1w : word1) <> 0w`
            (fn th => simp_tac std_ss [th]) >>
          irule (SIMP_RULE pure_ss [LET_THM]
            smtfp_circuit_directed_negative_endpoint) >>
          asm_simp_tac std_ss [])
      >- (qpat_x_assum `(1w : word1) <> 0w`
            (fn th => simp_tac std_ss [th]) >>
          irule (SIMP_RULE pure_ss [LET_THM]
            smtfp_circuit_directed_negative_endpoint) >>
          asm_simp_tac std_ss [])
      >- (qpat_x_assum `(1w : word1) <> 0w`
            (fn th => simp_tac std_ss [th]) >>
          irule (SIMP_RULE pure_ss [LET_THM]
            smtfp_circuit_directed_negative_endpoint) >>
          asm_simp_tac std_ss [])
      >- (simp_tac std_ss [] >>
          irule (SIMP_RULE pure_ss [LET_THM]
            smtfp_circuit_RNE_positive_endpoint) >>
          asm_simp_tac std_ss [])
      >- (simp_tac std_ss [] >>
          irule (SIMP_RULE pure_ss [LET_THM]
            smtfp_circuit_RNA_positive_endpoint) >>
          asm_simp_tac std_ss [])
      >- (simp_tac std_ss [] >>
          irule (SIMP_RULE pure_ss [LET_THM]
            smtfp_circuit_directed_positive_endpoint) >>
          asm_simp_tac std_ss [])
      >- (simp_tac std_ss [] >>
          irule (SIMP_RULE pure_ss [LET_THM]
            smtfp_circuit_directed_positive_endpoint) >>
          asm_simp_tac std_ss [])
      >- (simp_tac std_ss [] >>
          irule (SIMP_RULE pure_ss [LET_THM]
            smtfp_circuit_directed_positive_endpoint) >>
          asm_simp_tac std_ss []))
QED

Theorem smtfp_circuit_quotient_encoded[local]:
  1 <= maximum_exponent /\ 0 < scale ==>
  (magnitude * 2 ** (scale - 1)) DIV
    2 **
      (smtfp_circuit_encoded_exponent maximum_exponent fraction_width
        scale magnitude - 1) =
  smtfp_circuit_quotient maximum_exponent fraction_width scale magnitude
Proof
  strip_tac >>
  `smtfp_circuit_effective_exponent maximum_exponent fraction_width
      scale magnitude =
   smtfp_circuit_encoded_exponent maximum_exponent fraction_width
      scale magnitude` by
    (mp_tac (Q.INST
       [`maximum_exponent` |-> `maximum_exponent`,
        `fraction_width` |-> `fraction_width`, `scale` |-> `scale`,
        `magnitude` |-> `magnitude`]
       smtfp_circuit_effective_encoded) >>
     simp []) >>
  mp_tac (Q.INST
    [`maximum_exponent` |-> `maximum_exponent`,
     `fraction_width` |-> `fraction_width`, `scale` |-> `scale`,
     `magnitude` |-> `magnitude`]
    smtfp_circuit_quotient_units) >>
  impl_tac >- asm_rewrite_tac [] >>
  strip_tac >> asm_rewrite_tac []
QED

Theorem smtfp_circuit_rounded_encoded[local]:
  1 <= maximum_exponent /\ 0 < scale ==>
  smtfp_circuit_round mode sign
    ((magnitude * 2 ** (scale - 1)) DIV
      2 **
        (smtfp_circuit_encoded_exponent maximum_exponent fraction_width
          scale magnitude - 1))
    ((magnitude * 2 ** (scale - 1)) MOD
      2 **
        (smtfp_circuit_encoded_exponent maximum_exponent fraction_width
          scale magnitude - 1))
    (2 **
      (smtfp_circuit_encoded_exponent maximum_exponent fraction_width
        scale magnitude - 1)) =
  smtfp_circuit_rounded mode sign maximum_exponent fraction_width
    scale magnitude
Proof
  strip_tac >>
  `smtfp_circuit_effective_exponent maximum_exponent fraction_width
      scale magnitude =
   smtfp_circuit_encoded_exponent maximum_exponent fraction_width
      scale magnitude` by
    (mp_tac (Q.INST
       [`maximum_exponent` |-> `maximum_exponent`,
        `fraction_width` |-> `fraction_width`, `scale` |-> `scale`,
        `magnitude` |-> `magnitude`]
       smtfp_circuit_effective_encoded) >>
     simp []) >>
  mp_tac (Q.INST
    [`mode` |-> `mode`, `sign` |-> `sign`,
     `maximum_exponent` |-> `maximum_exponent`,
     `fraction_width` |-> `fraction_width`, `scale` |-> `scale`,
     `magnitude` |-> `magnitude`]
    smtfp_circuit_rounded_units) >>
  impl_tac >- asm_rewrite_tac [] >>
  strip_tac >> asm_rewrite_tac []
QED

val _ = PolyML.fullGC ()

Theorem smtfp_circuit_encode_finite_correct:
  (2 <= dimindex (:'w) /\ 0 < scale /\ 0 < magnitude /\
  let maximum_exponent = dimword (:'w) - 2 in
  let fraction_width = dimindex (:'t) in
  let exponent =
    smtfp_circuit_encoded_exponent maximum_exponent fraction_width
      scale magnitude in
  let divisor = 2 ** (exponent - 1) in
  let units = magnitude * 2 ** (scale - 1) in
  let quotient = units DIV divisor in
  let residue = units MOD divisor in
  let rounded =
    smtfp_circuit_round mode sign quotient residue divisor in
  rounded <= 2 ** (fraction_width + 1) /\
    (rounded = 2 ** (fraction_width + 1) ==>
     exponent < maximum_exponent) /\
    (residue <> 0 /\ quotient + 1 = 2 ** (fraction_width + 1) ==>
     exponent < maximum_exponent)) ==>
  smt_float_round mode to_neg
    ((if sign = 0w then &(magnitude * 2 ** (scale - 1))
      else -&(magnitude * 2 ** (scale - 1))) *
     (2 pow 1 / 2 pow (INT_MAX (:'w) + dimindex (:'t)))) =
  smtfp_rep
    (smtfp_circuit_encode mode (format : ('t,'w) smtfp)
      sign scale magnitude)
Proof
  simp_tac pure_ss [LET_THM] >> strip_tac >>
  qabbrev_tac `maximum_exponent = dimword (:'w) - 2` >>
  qabbrev_tac `fraction_width = dimindex (:'t)` >>
  qabbrev_tac
    `exponent = smtfp_circuit_encoded_exponent maximum_exponent
      fraction_width scale magnitude` >>
  qabbrev_tac `divisor = (2 : num) ** (exponent - 1)` >>
  qabbrev_tac `units = magnitude * 2 ** (scale - 1)` >>
  qabbrev_tac `quotient = units DIV divisor` >>
  qabbrev_tac `residue = units MOD divisor` >>
  qabbrev_tac
    `rounded = smtfp_circuit_round mode sign quotient residue divisor` >>
  `1 <= maximum_exponent` by
    (simp [Abbr `maximum_exponent`, wordsTheory.dimword_def,
           arithmeticTheory.SUB_LEFT_LESS_EQ] >>
     irule arithmeticTheory.LESS_EQ_TRANS >>
     qexists_tac `(2 : num) ** 2` >>
     simp [arithmeticTheory.EXP_BASE_LE_MONO]) >>
  `1 <= exponent /\ exponent <= maximum_exponent` by
    (mp_tac (Q.INST
       [`maximum_exponent` |-> `maximum_exponent`,
        `fraction_width` |-> `fraction_width`, `scale` |-> `scale`,
        `magnitude` |-> `magnitude`]
       smtfp_circuit_effective_encoded) >>
     simp [Abbr `exponent`]) >>
  `exponent =
   smtfp_circuit_effective_exponent maximum_exponent fraction_width
     scale magnitude` by
    (mp_tac (Q.INST
       [`maximum_exponent` |-> `maximum_exponent`,
        `fraction_width` |-> `fraction_width`, `scale` |-> `scale`,
        `magnitude` |-> `magnitude`]
       smtfp_circuit_effective_encoded) >>
     impl_tac
     >- qpat_x_assum `1 <= maximum_exponent` ACCEPT_TAC >>
     simp [Abbr `exponent`]) >>
  `0 < units /\ 0 < divisor` by
    simp [Abbr `units`, Abbr `divisor`] >>
  `quotient =
   smtfp_circuit_quotient maximum_exponent fraction_width scale
     magnitude` by
    (simp_tac pure_ss
       [Abbr `quotient`, Abbr `units`, Abbr `divisor`,
        Abbr `exponent`] >>
     irule smtfp_circuit_quotient_encoded >>
     asm_rewrite_tac []) >>
  `rounded =
   smtfp_circuit_rounded mode sign maximum_exponent fraction_width
     scale magnitude` by
    (simp_tac pure_ss
       [Abbr `rounded`, Abbr `quotient`, Abbr `residue`,
        Abbr `units`, Abbr `divisor`, Abbr `exponent`] >>
     irule smtfp_circuit_rounded_encoded >>
     asm_rewrite_tac []) >>
  `quotient <= rounded /\ rounded <= quotient + 1` by
    (qunabbrev_tac `rounded` >>
     irule smtfp_circuit_round_bounds) >>
  `quotient < 2 ** (fraction_width + 1)` by
    (Cases_on `rounded < 2 ** (fraction_width + 1)` >- decide_tac >>
     `rounded = 2 ** (fraction_width + 1)` by decide_tac >>
     `exponent < maximum_exponent` by fs [] >>
     qpat_x_assum
       `quotient = smtfp_circuit_quotient maximum_exponent
          fraction_width scale magnitude` SUBST1_TAC >>
     irule smtfp_circuit_quotient_normalized_upper >>
     simp [Abbr `exponent`]) >>
  `quotient + 1 <= 2 ** (fraction_width + 1)` by decide_tac >>
  `(quotient < 2 ** fraction_width ==> exponent = 1)` by
    (strip_tac >>
     mp_tac (Q.INST
       [`maximum_exponent` |-> `maximum_exponent`,
        `fraction_width` |-> `fraction_width`, `scale` |-> `scale`,
        `magnitude` |-> `magnitude`]
       smtfp_circuit_quotient_normalized_lower) >>
     simp [Abbr `quotient`, Abbr `exponent`]) >>
  `0 < quotient` by
    (Cases_on `quotient = 0`
     >- (`quotient < 2 ** fraction_width` by simp [] >>
         `exponent = 1` by fs [] >>
         `divisor = 1` by simp [Abbr `divisor`] >>
         fs [Abbr `quotient`]) >>
     decide_tac) >>
  `0 < rounded` by decide_tac >>
  `residue < divisor` by
    simp [Abbr `residue`, arithmeticTheory.MOD_LESS] >>
  `units = quotient * divisor + residue` by
    (mp_tac (Q.SPEC `divisor` arithmeticTheory.DIVISION) >>
     impl_tac >- asm_rewrite_tac [] >>
     disch_then (qspec_then `units` mp_tac) >>
     asm_simp_tac std_ss
       [Abbr `quotient`, Abbr `residue`,
        arithmeticTheory.MULT_COMM]) >>
  `smtfp_circuit_encode mode (format : ('t,'w) smtfp)
       sign scale magnitude =
   smtfp_circuit_endpoint format sign exponent rounded` by
    (qpat_x_assum
       `rounded = smtfp_circuit_rounded mode sign maximum_exponent
          fraction_width scale magnitude`
       (fn th => once_rewrite_tac [th] >> assume_tac th) >>
     qunabbrev_tac `exponent` >>
     qunabbrev_tac `maximum_exponent` >>
     qunabbrev_tac `fraction_width` >>
     irule smtfp_circuit_encode_endpoint >>
     simp [LET_THM]) >>
  `~float_is_zero
     (smtfp_rep
       (smtfp_circuit_endpoint (format : ('t,'w) smtfp)
         sign exponent rounded))` by
    (irule smtfp_circuit_endpoint_nonzero >>
     simp [Abbr `maximum_exponent`, Abbr `fraction_width`] >>
     fs []) >>
  Cases_on `residue = 0`
  >- (`rounded = quotient` by
        (qunabbrev_tac `rounded` >>
         rewrite_tac [smtfp_circuit_round_def,
                      smtfp_circuit_round_up_def] >>
         qpat_x_assum `residue = 0` (fn th => rewrite_tac [th]) >>
         simp []) >>
      `units = quotient * divisor` by
        (qpat_x_assum `units = quotient * divisor + residue` mp_tac >>
         asm_simp_tac std_ss []) >>
      `float_to_real
         (smtfp_rep
           (smtfp_circuit_endpoint (format : ('t,'w) smtfp)
             sign exponent rounded)) =
       (if sign = 0w then &units else -&units) *
         (2 pow 1 / 2 pow (INT_MAX (:'w) + dimindex (:'t)))` by
        (irule EQ_TRANS >>
         qexists_tac
           `(if sign = 0w then &(rounded * 2 ** (exponent - 1))
             else -&(rounded * 2 ** (exponent - 1))) *
            (2 pow 1 / 2 pow
              (INT_MAX (:'w) + dimindex (:'t)))` >>
         conj_tac
         >- (irule smtfp_circuit_endpoint_value >>
             simp [Abbr `maximum_exponent`, Abbr `fraction_width`] >>
             fs [])
         >> simp [Abbr `divisor`]) >>
      `float_is_finite
         (smtfp_rep
           (smtfp_circuit_endpoint (format : ('t,'w) smtfp)
             sign exponent rounded))` by
        (irule smtfp_circuit_endpoint_finite >>
         simp [Abbr `maximum_exponent`, Abbr `fraction_width`] >> fs []) >>
      `~float_is_zero
         (smtfp_rep
           (smtfp_circuit_endpoint (format : ('t,'w) smtfp)
             sign exponent rounded))` by
        qpat_x_assum
          `~float_is_zero
             (smtfp_rep
               (smtfp_circuit_endpoint (format : ('t,'w) smtfp)
                 sign exponent rounded))` ACCEPT_TAC >>
      qunabbrev_tac `fraction_width` >>
      qpat_x_assum
        `smtfp_circuit_encode mode (format : ('t,'w) smtfp)
           sign scale magnitude =
         smtfp_circuit_endpoint format sign exponent rounded`
        (fn th => once_rewrite_tac [th]) >>
      qpat_x_assum
        `float_to_real
           (smtfp_rep
             (smtfp_circuit_endpoint (format : ('t,'w) smtfp)
               sign exponent rounded)) = _`
        (fn th => once_rewrite_tac [GSYM th]) >>
      irule smt_float_round_representable_nonzero >>
      conj_tac
      >- qpat_x_assum
           `float_is_finite
              (smtfp_rep
                (smtfp_circuit_endpoint (format : ('t,'w) smtfp)
                  sign exponent rounded))` ACCEPT_TAC >>
      conj_tac
      >- qpat_x_assum
           `~float_is_zero
              (smtfp_rep
                (smtfp_circuit_endpoint (format : ('t,'w) smtfp)
                  sign exponent rounded))`
           (ACCEPT_TAC o REWRITE_RULE
             [binary_ieeeTheory.float_is_zero_to_real]) >>
      qpat_x_assum `2 <= dimindex (:'w)` ACCEPT_TAC) >>
  `(quotient + 1 = 2 ** (fraction_width + 1) ==>
    exponent < maximum_exponent)` by fs [] >>
  qpat_x_assum
    `smtfp_circuit_encode mode (format : ('t,'w) smtfp)
       sign scale magnitude =
     smtfp_circuit_endpoint format sign exponent rounded`
    (fn th => once_rewrite_tac [th] >> assume_tac th) >>
  qpat_x_assum `units = quotient * divisor + residue`
    (fn th => once_rewrite_tac [th] >> assume_tac th) >>
  qunabbrev_tac `fraction_width` >>
  qunabbrev_tac `rounded` >>
  qunabbrev_tac `maximum_exponent` >>
  qunabbrev_tac `divisor` >>
  irule smtfp_circuit_endpoint_round_nonzero >>
  rpt conj_tac >> asm_rewrite_tac []
QED

Theorem smtfp_circuit_infinity_rep:
  smtfp_rep
    (smtfp_circuit_infinity (format : ('t,'w) smtfp) 0w) =
      float_plus_infinity (:'t # 'w) /\
  smtfp_rep
    (smtfp_circuit_infinity (format : ('t,'w) smtfp) 1w) =
      float_minus_infinity (:'t # 'w)
Proof
  simp [smtfp_circuit_infinity_def,
        smtfp_rep_bits,
        canon_def,
        smtfp_nan_pattern_def,
        binary_ieeeTheory.float_plus_infinity_def,
        binary_ieeeTheory.float_minus_infinity_def,
        binary_ieeeTheory.float_negate_def]
QED

Theorem smtfp_circuit_top_rep:
  2 <= dimindex (:'w) ==>
  smtfp_rep (smtfp_circuit_top (format : ('t,'w) smtfp) 0w) =
      float_top (:'t # 'w) /\
  smtfp_rep (smtfp_circuit_top (format : ('t,'w) smtfp) 1w) =
      float_bottom (:'t # 'w)
Proof
  strip_tac >>
  `2 <= dimword (:'w)` by simp [wordsTheory.dimword_def] >>
  `2 < dimword (:'w)` by
    (simp [wordsTheory.dimword_def] >>
     irule arithmeticTheory.LESS_EQ_LESS_TRANS >>
     qexists_tac `(2 : num) ** 2` >>
     simp [arithmeticTheory.EXP_BASE_LE_MONO]) >>
  simp [smtfp_circuit_top_def,
        smtfp_rep_finite_n2w_bits,
        binary_ieeeTheory.float_top_def,
        binary_ieeeTheory.float_bottom_def,
        binary_ieeeTheory.float_negate_def,
        wordsTheory.UINT_MAX_def, wordsTheory.word_T_def,
        canon_def, binary_ieeeTheory.float_is_nan_def,
        binary_ieeeTheory.float_value_def, smtfp_nan_pattern_def,
        wordsTheory.n2w_sub, wordsTheory.n2w_dimword] >>
  simp [wordsTheory.dimword_def, wordsTheory.n2w_sub,
        wordsTheory.n2w_dimword]
QED

Theorem smtfp_circuit_pack_top:
  2 <= dimindex (:'w) ==>
  smtfp_circuit_pack mode (format : ('t,'w) smtfp) sign
      (dimword (:'w) - 2) (dimindex (:'t)) (dimword (:'w) - 2)
      (2 ** (dimindex (:'t) + 1) - 1) =
    smtfp_circuit_top format sign
Proof
  strip_tac >>
  `2 < dimword (:'w)` by
    (simp [wordsTheory.dimword_def] >>
     irule arithmeticTheory.LESS_EQ_LESS_TRANS >>
     qexists_tac `(2 : num) ** 2` >>
     simp [arithmeticTheory.EXP_BASE_LE_MONO]) >>
  simp [smtfp_circuit_pack_def, smtfp_circuit_top_def,
        arithmeticTheory.EXP_ADD] >>
  `0 < 2 * 2 ** dimindex (:'t)` by simp [] >>
  simp []
QED

Theorem smtfp_circuit_overflow_rep:
  2 <= dimindex (:'w) ==>
  smtfp_rep
    (smtfp_circuit_overflow mode (format : ('t,'w) smtfp) sign) =
  case mode of
    RNE => if sign = 0w then float_plus_infinity (:'t # 'w)
           else float_minus_infinity (:'t # 'w)
  | RNA => if sign = 0w then float_plus_infinity (:'t # 'w)
           else float_minus_infinity (:'t # 'w)
  | RTP => if sign = 0w then float_plus_infinity (:'t # 'w)
           else float_bottom (:'t # 'w)
  | RTN => if sign = 1w then float_minus_infinity (:'t # 'w)
           else float_top (:'t # 'w)
  | RTZ => if sign = 0w then float_top (:'t # 'w)
           else float_bottom (:'t # 'w)
Proof
  strip_tac >> Cases_on `mode` >>
  wordsLib.Cases_on_word_value `sign` >>
  simp [smtfp_circuit_overflow_def,
        smtfp_circuit_infinity_rep, smtfp_circuit_top_rep]
QED

Theorem smtfp_circuit_threshold_algebra[local]:
  !A B C : real.
    B <> 0 /\ C <> 0 ==>
    A * (2 - 1 / 2 * B⁻¹) =
    C * (C⁻¹ * A * (2 - B⁻¹) +
         1 / 2 * (B⁻¹ * C⁻¹ * A))
Proof
  RealField.REAL_FIELD_TAC
QED

Theorem smtfp_circuit_threshold_largest:
  2 <= dimindex (:'w) ==>
  threshold (:'t # 'w) = largest (:'t # 'w) +
    ULP (n2w (dimword (:'w) - 2) : 'w word, (:'t)) / 2
Proof
  strip_tac >>
  `dimword (:'w) - 2 < dimword (:'w)` by
    (simp [wordsTheory.dimword_def] >>
     irule arithmeticTheory.LESS_EQ_LESS_TRANS >>
     qexists_tac `2 ** 2 - 2` >> simp [] >>
     irule arithmeticTheory.EXP_BASE_LE_MONO >> simp []) >>
  rewrite_tac [binary_ieeeTheory.threshold_def,
               binary_ieeeTheory.largest_def,
               binary_ieeeTheory.ULP_def] >>
  simp [wordsTheory.w2n_n2w, arithmeticTheory.LESS_MOD,
        wordsTheory.UINT_MAX_def, wordsTheory.INT_MAX_def,
        wordsTheory.dimword_def] >>
  once_rewrite_tac [realTheory.REAL_POW_ADD] >>
  rewrite_tac [arithmeticTheory.SUC_ONE_ADD] >>
  once_rewrite_tac [realTheory.REAL_POW_ADD] >>
  simp [realTheory.REAL_POW_EQ_0] >>
  `2 pow dimindex (:'t) <> 0` by
    simp [realTheory.REAL_POW_EQ_0] >>
  `2 pow (INT_MIN (:'w) - 1) <> 0` by
    simp [realTheory.REAL_POW_EQ_0] >>
  rewrite_tac [realTheory.real_div] >>
  simp [realTheory.REAL_INV_MUL, realTheory.REAL_MUL_RINV,
        realTheory.REAL_MUL_LINV] >>
  irule smtfp_circuit_threshold_algebra >>
  simp []
QED

Theorem smtfp_circuit_largest_threshold_units:
  2 <= dimindex (:'w) ==>
  let maximum_exponent = dimword (:'w) - 2 in
  let boundary = 2 ** (dimindex (:'t) + 1) in
  let divisor = 2 ** (maximum_exponent - 1) in
  let unit = 2 pow 1 /
    2 pow (INT_MAX (:'w) + dimindex (:'t)) in
  largest (:'t # 'w) = &((boundary - 1) * divisor) * unit /\
  threshold (:'t # 'w) =
    &((boundary - 1) * divisor) * unit + &divisor * unit / 2
Proof
  simp_tac pure_ss [LET_THM] >> strip_tac >>
  qabbrev_tac `maximum_exponent = dimword (:'w) - 2` >>
  qabbrev_tac `(boundary : num) = 2 ** (dimindex (:'t) + 1)` >>
  qabbrev_tac `(divisor : num) = 2 ** (maximum_exponent - 1)` >>
  qabbrev_tac
    `unit = 2 pow 1 / 2 pow (INT_MAX (:'w) + dimindex (:'t))` >>
  `1 <= maximum_exponent` by
    (simp [Abbr `maximum_exponent`, wordsTheory.dimword_def,
           arithmeticTheory.SUB_LEFT_LESS_EQ] >>
     irule arithmeticTheory.LESS_EQ_TRANS >>
     qexists_tac `2 ** 2` >>
     simp [arithmeticTheory.EXP_BASE_LE_MONO]) >>
  `2 ** dimindex (:'t) <= boundary - 1 /\
   boundary - 1 < boundary` by
    simp [Abbr `boundary`, arithmeticTheory.EXP_ADD] >>
  `smtfp_circuit_endpoint (format : ('t,'w) smtfp) 0w maximum_exponent
       (boundary - 1) = smtfp_circuit_top format 0w` by
    (simp [smtfp_circuit_endpoint_def,
           smtfp_circuit_top_def,
           Abbr `boundary`, Abbr `maximum_exponent`,
           wordsTheory.UINT_MAX_def, wordsTheory.dimword_def] >>
     simp [arithmeticTheory.EXP_ADD]) >>
  `largest (:'t # 'w) =
   float_to_real
     (smtfp_rep
       (smtfp_circuit_endpoint (format : ('t,'w) smtfp) 0w maximum_exponent
         (boundary - 1)))` by
    (simp [binary_ieeeTheory.largest_is_top,
           smtfp_circuit_top_rep] >>
     decide_tac) >>
  `largest (:'t # 'w) = &((boundary - 1) * divisor) * unit` by
    (qpat_x_assum `largest _ = float_to_real _`
       (fn th => once_rewrite_tac [th]) >>
     mp_tac (Q.INST
       [`format` |-> `format`, `sign` |-> `(0w : word1)`,
        `exponent` |-> `maximum_exponent`,
        `rounded` |-> `boundary - 1`]
       smtfp_circuit_endpoint_value) >>
     impl_tac
     >- simp [Abbr `maximum_exponent`, Abbr `boundary`]
     >> simp [Abbr `divisor`, Abbr `unit`]) >>
  `ULP (n2w maximum_exponent : 'w word, (:'t)) =
   &divisor * unit` by
    (simp [Abbr `maximum_exponent`, Abbr `divisor`, Abbr `unit`,
           binary_ieeeTheory.ULP_def, wordsTheory.w2n_n2w,
           wordsTheory.dimword_def, realTheory.REAL_OF_NUM_POW] >>
     `1 <= 2 ** dimindex (:'w) - 2` by
       (simp [arithmeticTheory.SUB_LEFT_LESS_EQ] >>
        irule arithmeticTheory.LESS_EQ_TRANS >>
        qexists_tac `2 ** 2` >>
        simp [arithmeticTheory.EXP_BASE_LE_MONO]) >>
     Cases_on `2 ** dimindex (:'w) - 2` >>
     fs [arithmeticTheory.EXP]) >>
  simp [smtfp_circuit_threshold_largest] >>
  realLib.REAL_ASM_ARITH_TAC
QED

Theorem smtfp_circuit_RNA_positive_overflow_band:
  2 <= dimindex (:'w) /\
  largest (:'t # 'w) < x /\ x < threshold (:'t # 'w) ==>
  round_tiesToAway x = float_top (:'t # 'w)
Proof
  strip_tac >>
  `is_closest float_is_finite x (float_top (:'t # 'w))` by
    (rw [binary_ieeeTheory.is_closest_def, IN_DEF] >>
     rpt strip_tac >>
     mp_tac (Q.INST [`f` |-> `b`]
       (INST_TYPE [alpha |-> ``:'t``, beta |-> ``:'w``]
         binary_ieeeTheory.abs_float_bounds)) >>
     simp [binary_ieeeTheory.largest_is_top] >>
     strip_tac >>
     `float_to_real b <= abs (float_to_real b)` by
       simp [realTheory.ABS_LE] >>
     `1 < dimindex (:'w)` by decide_tac >>
     `float_to_real (float_top (:'t # 'w)) < x` by
       fs [binary_ieeeTheory.largest_is_top] >>
     rw [realTheory.abs] >>
     realLib.REAL_ASM_ARITH_TAC) >>
  `!a : ('t,'w) float.
     is_closest float_is_finite x a ==> a = float_top (:'t # 'w)` by
    (rpt strip_tac >>
     fs [binary_ieeeTheory.is_closest_def, IN_DEF] >>
     qpat_x_assum `!b. float_is_finite b ==> _`
       (qspec_then `float_top (:'t # 'w)` mp_tac) >>
     qpat_x_assum `!b. float_is_finite b ==> _`
       (qspec_then `a` mp_tac) >>
     simp [binary_ieeeTheory.largest_is_top] >>
     mp_tac (Q.INST [`f` |-> `a`]
       (INST_TYPE [alpha |-> ``:'t``, beta |-> ``:'w``]
         binary_ieeeTheory.abs_float_bounds)) >>
     simp [] >> strip_tac >>
     rpt strip_tac >>
     `float_to_real a <= abs (float_to_real a)` by
       simp [realTheory.ABS_LE] >>
     `1 < dimindex (:'w)` by decide_tac >>
     `largest (:'t # 'w) =
      float_to_real (float_top (:'t # 'w))` by
       simp [binary_ieeeTheory.largest_is_top] >>
     `float_to_real a < x` by realLib.REAL_ASM_ARITH_TAC >>
     `float_to_real (float_top (:'t # 'w)) < x` by
       realLib.REAL_ASM_ARITH_TAC >>
     `abs (float_to_real a - x) = x - float_to_real a` by
       (rw [realTheory.abs] >> realLib.REAL_ASM_ARITH_TAC) >>
     `abs (float_to_real (float_top (:'t # 'w)) - x) =
      x - float_to_real (float_top (:'t # 'w))` by
       (rw [realTheory.abs] >> realLib.REAL_ASM_ARITH_TAC) >>
     `float_to_real a =
      float_to_real (float_top (:'t # 'w))` by
       realLib.REAL_ASM_ARITH_TAC >>
     fs [binary_ieeeTheory.float_to_real_eq] >> fs []) >>
  `round roundTiesToEven x = float_top (:'t # 'w)` by
    (qpat_x_assum `!a. _` irule >>
     irule round_RNE_is_closest >>
     mp_tac (INST_TYPE [alpha |-> ``:'t``, beta |-> ``:'w``]
       binary_ieeeTheory.largest_is_positive) >>
     mp_tac (INST_TYPE [alpha |-> ``:'t``, beta |-> ``:'w``]
       binary_ieeeTheory.threshold_is_positive) >>
     realLib.REAL_ASM_ARITH_TAC) >>
  irule EQ_TRANS >> qexists_tac `round roundTiesToEven x` >>
  conj_tac
  >- (irule round_tiesToAway_eq_RNE_when_closest_unique >>
      conj_tac
      >- (rpt strip_tac >>
          qpat_x_assum `!a. _`
            (fn th => mp_tac (Q.SPEC `a` th) >>
                      mp_tac (Q.SPEC `b` th)) >>
          metis_tac []) >>
      conj_tac
      >- simp [] >>
      mp_tac (INST_TYPE [alpha |-> ``:'t``, beta |-> ``:'w``]
        binary_ieeeTheory.largest_is_positive) >>
      mp_tac (INST_TYPE [alpha |-> ``:'t``, beta |-> ``:'w``]
        binary_ieeeTheory.threshold_is_positive) >>
      realLib.REAL_ASM_ARITH_TAC)
  >> simp []
QED

Theorem smtfp_circuit_RNA_negative_overflow_band:
  2 <= dimindex (:'w) /\
  -threshold (:'t # 'w) < x /\ x < -largest (:'t # 'w) ==>
  round_tiesToAway x = float_bottom (:'t # 'w)
Proof
  strip_tac >>
  `is_closest float_is_finite x (float_bottom (:'t # 'w))` by
    (rw [binary_ieeeTheory.is_closest_def, IN_DEF] >>
     rpt strip_tac >>
     mp_tac (Q.INST [`f` |-> `b`]
       (INST_TYPE [alpha |-> ``:'t``, beta |-> ``:'w``]
         binary_ieeeTheory.abs_float_bounds)) >>
     simp [binary_ieeeTheory.float_bottom_def,
           binary_ieeeTheory.float_to_real_negate,
           binary_ieeeTheory.largest_is_top] >>
     strip_tac >>
     `-abs (float_to_real b) <= float_to_real b` by
       (mp_tac (Q.SPEC `-float_to_real b` realTheory.ABS_LE) >>
        simp [realTheory.ABS_NEG] >>
        realLib.REAL_ASM_ARITH_TAC) >>
     `1 < dimindex (:'w)` by decide_tac >>
     `x < float_to_real (float_bottom (:'t # 'w))` by
       fs [binary_ieeeTheory.float_bottom_def,
           binary_ieeeTheory.float_to_real_negate,
           binary_ieeeTheory.largest_is_top] >>
     fs [binary_ieeeTheory.float_bottom_def,
         binary_ieeeTheory.float_to_real_negate] >>
     rw [realTheory.abs] >>
     realLib.REAL_ASM_ARITH_TAC) >>
  `!a : ('t,'w) float.
     is_closest float_is_finite x a ==> a = float_bottom (:'t # 'w)` by
    (rpt strip_tac >>
     fs [binary_ieeeTheory.is_closest_def, IN_DEF] >>
     qpat_x_assum `!b. float_is_finite b ==> _`
       (qspec_then `float_bottom (:'t # 'w)` mp_tac) >>
     qpat_x_assum `!b. float_is_finite b ==> _`
       (qspec_then `a` mp_tac) >>
     simp [binary_ieeeTheory.float_bottom_def,
           binary_ieeeTheory.float_to_real_negate,
           binary_ieeeTheory.largest_is_top] >>
     mp_tac (Q.INST [`f` |-> `a`]
       (INST_TYPE [alpha |-> ``:'t``, beta |-> ``:'w``]
         binary_ieeeTheory.abs_float_bounds)) >>
     simp [] >> strip_tac >>
     rpt strip_tac >>
     `-abs (float_to_real a) <= float_to_real a` by
       (mp_tac (Q.SPEC `-float_to_real a` realTheory.ABS_LE) >>
        simp [realTheory.ABS_NEG] >>
        realLib.REAL_ASM_ARITH_TAC) >>
     `1 < dimindex (:'w)` by decide_tac >>
     `largest (:'t # 'w) =
      float_to_real (float_top (:'t # 'w))` by
       simp [binary_ieeeTheory.largest_is_top] >>
     `float_to_real (float_bottom (:'t # 'w)) =
      -largest (:'t # 'w)` by
       simp [binary_ieeeTheory.float_bottom_def,
             binary_ieeeTheory.float_to_real_negate,
             binary_ieeeTheory.largest_is_top] >>
     `x < float_to_real a` by realLib.REAL_ASM_ARITH_TAC >>
     `x < float_to_real (float_bottom (:'t # 'w))` by
       realLib.REAL_ASM_ARITH_TAC >>
     fs [binary_ieeeTheory.float_bottom_def,
         binary_ieeeTheory.float_to_real_negate] >>
     `abs (float_to_real a - x) = float_to_real a - x` by
       (rw [realTheory.abs] >> realLib.REAL_ASM_ARITH_TAC) >>
     `abs (-largest (:'t # 'w) - x) =
      -largest (:'t # 'w) - x` by
       (rw [realTheory.abs] >> realLib.REAL_ASM_ARITH_TAC) >>
     `float_to_real a = -largest (:'t # 'w)` by
       realLib.REAL_ASM_ARITH_TAC >>
     `float_to_real a =
      float_to_real (float_negate (float_top (:'t # 'w)))` by
       (simp [binary_ieeeTheory.float_to_real_negate] >>
        realLib.REAL_ASM_ARITH_TAC) >>
     fs [binary_ieeeTheory.float_to_real_eq] >> fs []) >>
  `round roundTiesToEven x = float_bottom (:'t # 'w)` by
    (qpat_x_assum `!a. _` irule >>
     irule round_RNE_is_closest >>
     mp_tac (INST_TYPE [alpha |-> ``:'t``, beta |-> ``:'w``]
       binary_ieeeTheory.largest_is_positive) >>
     mp_tac (INST_TYPE [alpha |-> ``:'t``, beta |-> ``:'w``]
       binary_ieeeTheory.threshold_is_positive) >>
     realLib.REAL_ASM_ARITH_TAC) >>
  irule EQ_TRANS >> qexists_tac `round roundTiesToEven x` >>
  conj_tac
  >- (irule round_tiesToAway_eq_RNE_when_closest_unique >>
      conj_tac
      >- (rpt strip_tac >>
          qpat_x_assum `!a. _`
            (fn th => mp_tac (Q.SPEC `a` th) >>
                      mp_tac (Q.SPEC `b` th)) >>
          metis_tac []) >>
      conj_tac
      >- (mp_tac (INST_TYPE [alpha |-> ``:'t``, beta |-> ``:'w``]
            binary_ieeeTheory.largest_is_positive) >>
          mp_tac (INST_TYPE [alpha |-> ``:'t``, beta |-> ``:'w``]
            binary_ieeeTheory.threshold_is_positive) >>
          realLib.REAL_ASM_ARITH_TAC) >>
      simp [])
  >> simp []
QED

Theorem smtfp_circuit_RNE_positive_overflow_band:
  2 <= dimindex (:'w) /\
  largest (:'t # 'w) < x /\ x < threshold (:'t # 'w) ==>
  round roundTiesToEven x = float_top (:'t # 'w)
Proof
  strip_tac >>
  `is_closest float_is_finite x (float_top (:'t # 'w))` by
    (rw [binary_ieeeTheory.is_closest_def, IN_DEF] >>
     rpt strip_tac >>
     mp_tac (Q.INST [`f` |-> `b`]
       (INST_TYPE [alpha |-> ``:'t``, beta |-> ``:'w``]
         binary_ieeeTheory.abs_float_bounds)) >>
     simp [binary_ieeeTheory.largest_is_top] >>
     strip_tac >>
     `float_to_real b <= abs (float_to_real b)` by
       simp [realTheory.ABS_LE] >>
     `1 < dimindex (:'w)` by decide_tac >>
     `float_to_real (float_top (:'t # 'w)) < x` by
       fs [binary_ieeeTheory.largest_is_top] >>
     rw [realTheory.abs] >>
     realLib.REAL_ASM_ARITH_TAC) >>
  `!a : ('t,'w) float.
     is_closest float_is_finite x a ==> a = float_top (:'t # 'w)` by
    (rpt strip_tac >>
     fs [binary_ieeeTheory.is_closest_def, IN_DEF] >>
     qpat_x_assum `!b. float_is_finite b ==> _`
       (qspec_then `float_top (:'t # 'w)` mp_tac) >>
     qpat_x_assum `!b. float_is_finite b ==> _`
       (qspec_then `a` mp_tac) >>
     simp [binary_ieeeTheory.largest_is_top] >>
     mp_tac (Q.INST [`f` |-> `a`]
       (INST_TYPE [alpha |-> ``:'t``, beta |-> ``:'w``]
         binary_ieeeTheory.abs_float_bounds)) >>
     simp [] >> strip_tac >>
     rpt strip_tac >>
     `float_to_real a <= abs (float_to_real a)` by
       simp [realTheory.ABS_LE] >>
     `1 < dimindex (:'w)` by decide_tac >>
     `largest (:'t # 'w) =
      float_to_real (float_top (:'t # 'w))` by
       simp [binary_ieeeTheory.largest_is_top] >>
     `float_to_real a < x` by realLib.REAL_ASM_ARITH_TAC >>
     `float_to_real (float_top (:'t # 'w)) < x` by
       realLib.REAL_ASM_ARITH_TAC >>
     `abs (float_to_real a - x) = x - float_to_real a` by
       (rw [realTheory.abs] >> realLib.REAL_ASM_ARITH_TAC) >>
     `abs (float_to_real (float_top (:'t # 'w)) - x) =
      x - float_to_real (float_top (:'t # 'w))` by
       (rw [realTheory.abs] >> realLib.REAL_ASM_ARITH_TAC) >>
     `float_to_real a =
      float_to_real (float_top (:'t # 'w))` by
       realLib.REAL_ASM_ARITH_TAC >>
     fs [binary_ieeeTheory.float_to_real_eq] >> fs []) >>
  qpat_x_assum `!a. _` irule >>
  irule round_RNE_is_closest >>
  mp_tac (INST_TYPE [alpha |-> ``:'t``, beta |-> ``:'w``]
    binary_ieeeTheory.largest_is_positive) >>
  mp_tac (INST_TYPE [alpha |-> ``:'t``, beta |-> ``:'w``]
    binary_ieeeTheory.threshold_is_positive) >>
  realLib.REAL_ASM_ARITH_TAC
QED

Theorem smtfp_circuit_RNE_negative_overflow_band:
  2 <= dimindex (:'w) /\
  -threshold (:'t # 'w) < x /\ x < -largest (:'t # 'w) ==>
  round roundTiesToEven x = float_bottom (:'t # 'w)
Proof
  strip_tac >>
  `is_closest float_is_finite x (float_bottom (:'t # 'w))` by
    (rw [binary_ieeeTheory.is_closest_def, IN_DEF] >>
     rpt strip_tac >>
     mp_tac (Q.INST [`f` |-> `b`]
       (INST_TYPE [alpha |-> ``:'t``, beta |-> ``:'w``]
         binary_ieeeTheory.abs_float_bounds)) >>
     simp [binary_ieeeTheory.float_bottom_def,
           binary_ieeeTheory.float_to_real_negate,
           binary_ieeeTheory.largest_is_top] >>
     strip_tac >>
     `-abs (float_to_real b) <= float_to_real b` by
       (mp_tac (Q.SPEC `-float_to_real b` realTheory.ABS_LE) >>
        simp [realTheory.ABS_NEG] >>
        realLib.REAL_ASM_ARITH_TAC) >>
     `1 < dimindex (:'w)` by decide_tac >>
     `x < float_to_real (float_bottom (:'t # 'w))` by
       fs [binary_ieeeTheory.float_bottom_def,
           binary_ieeeTheory.float_to_real_negate,
           binary_ieeeTheory.largest_is_top] >>
     fs [binary_ieeeTheory.float_bottom_def,
         binary_ieeeTheory.float_to_real_negate] >>
     rw [realTheory.abs] >>
     realLib.REAL_ASM_ARITH_TAC) >>
  `!a : ('t,'w) float.
     is_closest float_is_finite x a ==> a = float_bottom (:'t # 'w)` by
    (rpt strip_tac >>
     fs [binary_ieeeTheory.is_closest_def, IN_DEF] >>
     qpat_x_assum `!b. float_is_finite b ==> _`
       (qspec_then `float_bottom (:'t # 'w)` mp_tac) >>
     qpat_x_assum `!b. float_is_finite b ==> _`
       (qspec_then `a` mp_tac) >>
     simp [binary_ieeeTheory.float_bottom_def,
           binary_ieeeTheory.float_to_real_negate,
           binary_ieeeTheory.largest_is_top] >>
     mp_tac (Q.INST [`f` |-> `a`]
       (INST_TYPE [alpha |-> ``:'t``, beta |-> ``:'w``]
         binary_ieeeTheory.abs_float_bounds)) >>
     simp [] >> strip_tac >>
     rpt strip_tac >>
     `-abs (float_to_real a) <= float_to_real a` by
       (mp_tac (Q.SPEC `-float_to_real a` realTheory.ABS_LE) >>
        simp [realTheory.ABS_NEG] >>
        realLib.REAL_ASM_ARITH_TAC) >>
     `1 < dimindex (:'w)` by decide_tac >>
     `largest (:'t # 'w) =
      float_to_real (float_top (:'t # 'w))` by
       simp [binary_ieeeTheory.largest_is_top] >>
     `float_to_real (float_bottom (:'t # 'w)) =
      -largest (:'t # 'w)` by
       simp [binary_ieeeTheory.float_bottom_def,
             binary_ieeeTheory.float_to_real_negate,
             binary_ieeeTheory.largest_is_top] >>
     `x < float_to_real a` by realLib.REAL_ASM_ARITH_TAC >>
     `x < float_to_real (float_bottom (:'t # 'w))` by
       realLib.REAL_ASM_ARITH_TAC >>
     fs [binary_ieeeTheory.float_bottom_def,
         binary_ieeeTheory.float_to_real_negate] >>
     `abs (float_to_real a - x) = float_to_real a - x` by
       (rw [realTheory.abs] >> realLib.REAL_ASM_ARITH_TAC) >>
     `abs (-largest (:'t # 'w) - x) =
      -largest (:'t # 'w) - x` by
       (rw [realTheory.abs] >> realLib.REAL_ASM_ARITH_TAC) >>
     `float_to_real a = -largest (:'t # 'w)` by
       realLib.REAL_ASM_ARITH_TAC >>
     `float_to_real a =
      float_to_real (float_negate (float_top (:'t # 'w)))` by
       (simp [binary_ieeeTheory.float_to_real_negate] >>
        realLib.REAL_ASM_ARITH_TAC) >>
     fs [binary_ieeeTheory.float_to_real_eq] >> fs []) >>
  qpat_x_assum `!a. _` irule >>
  irule round_RNE_is_closest >>
  mp_tac (INST_TYPE [alpha |-> ``:'t``, beta |-> ``:'w``]
    binary_ieeeTheory.largest_is_positive) >>
  mp_tac (INST_TYPE [alpha |-> ``:'t``, beta |-> ``:'w``]
    binary_ieeeTheory.threshold_is_positive) >>
  realLib.REAL_ASM_ARITH_TAC
QED

Theorem smtfp_circuit_overflow_midpoint_units:
  !unit : real. !residue divisor boundary : num.
    0 < unit ==>
    (unit * &(residue + divisor * boundary) <
       unit * &(divisor * boundary) + unit * &divisor / 2 <=>
       2 * residue < divisor) /\
    (unit * &(divisor * boundary) + unit * &divisor / 2 <=
       unit * &(residue + divisor * boundary) <=>
       divisor <= 2 * residue)
Proof
  rpt strip_tac >>
  `unit * &(divisor * boundary) + unit * &divisor / 2 =
   unit * (&(divisor * boundary) + &divisor / 2)` by
    realLib.REAL_ARITH_TAC >>
  asm_rewrite_tac [] >>
  asm_simp_tac pure_ss [realTheory.REAL_LT_LMUL,
                         realTheory.REAL_LE_LMUL] >>
  simp_tac pure_ss [GSYM realTheory.REAL_OF_NUM_LT,
                    GSYM realTheory.REAL_OF_NUM_LE] >>
  simp_tac pure_ss [GSYM realTheory.REAL_OF_NUM_ADD,
                    GSYM realTheory.REAL_OF_NUM_MUL] >>
  realLib.REAL_ARITH_TAC
QED

Theorem smtfp_circuit_strict_overflow_units:
  0 < boundary /\ 0 < divisor /\ (0 : real) < unit /\
  boundary <= quotient /\
  units = quotient * divisor + residue /\ residue < divisor ==>
  &((boundary - 1) * divisor) * unit + &divisor * unit / 2 <
    &units * unit
Proof
  strip_tac >>
  `boundary * divisor <= units` by
    (qpat_x_assum `units = _` SUBST1_TAC >>
     irule arithmeticTheory.LE_TRANS >>
     qexists_tac `quotient * divisor` >>
     simp [arithmeticTheory.LE_MULT_RCANCEL]) >>
  `boundary * divisor = (boundary - 1) * divisor + divisor` by
    (`boundary = boundary - 1 + 1` by decide_tac >>
     pop_assum SUBST1_TAC >>
     simp [arithmeticTheory.LEFT_ADD_DISTRIB]) >>
  `(&(boundary * divisor) : real) <= &units` by simp [] >>
  `0 < unit * &divisor` by
    (irule realTheory.REAL_LT_MUL >> simp []) >>
  `&((boundary - 1) * divisor) * unit + &divisor * unit / 2 <
   &(boundary * divisor) * unit` by
    (qpat_x_assum `boundary * divisor = _`
       (fn th => once_rewrite_tac [th]) >>
     simp [realTheory.REAL_OF_NUM_ADD,
           realTheory.REAL_OF_NUM_MUL] >>
     `(&(divisor + divisor * (boundary - 1)) : real) =
      &divisor + &(divisor * (boundary - 1))` by simp [] >>
     asm_rewrite_tac [] >>
     simp [realTheory.REAL_ADD_LDISTRIB] >>
     realLib.REAL_ASM_ARITH_TAC) >>
  `&(boundary * divisor) * unit <= &units * unit` by
    asm_simp_tac std_ss [realTheory.REAL_LE_RMUL] >>
  realLib.REAL_ASM_ARITH_TAC
QED

Theorem smtfp_circuit_strict_overflow_round:
  2 <= dimindex (:'w) /\
  threshold (:'t # 'w) < positive /\
  negative < -threshold (:'t # 'w) ==>
  smt_float_round mode to_neg
      (if sign = 0w then positive else negative) =
    smtfp_rep
      (smtfp_circuit_overflow mode (format : ('t,'w) smtfp) sign)
Proof
  strip_tac >>
  `~float_is_zero (float_top (:'t # 'w)) /\
   ~float_is_zero (float_bottom (:'t # 'w))` by
    simp [binary_ieeeTheory.float_top_def,
          binary_ieeeTheory.float_bottom_def,
          binary_ieeeTheory.float_negate_def,
          binary_ieeeTheory.float_is_zero_def,
          wordsTheory.word_T_def, wordsTheory.UINT_MAX_def,
          wordsTheory.dimword_def] >>
  `threshold (:'t # 'w) <= positive /\
   negative <= -threshold (:'t # 'w)` by
    realLib.REAL_ASM_ARITH_TAC >>
  `largest (:'t # 'w) < positive /\
   negative < -largest (:'t # 'w)` by
    (mp_tac (INST_TYPE [alpha |-> ``:'t``, beta |-> ``:'w``]
       binary_ieeeTheory.largest_lt_threshold) >>
     realLib.REAL_ASM_ARITH_TAC) >>
  `(1w : word1) <> 0w` by wordsLib.WORD_DECIDE_TAC >>
  wordsLib.Cases_on_word_value `sign` >> Cases_on `mode` >>
  asm_simp_tac bool_ss
    [smtfp_circuit_overflow_rep,
     TypeBase.case_def_of ``:smt_rounding``,
     smt_float_round_def, smt_round_def, LET_THM,
     binary_ieeeTheory.infinity_properties,
     round_tiesToAway_overflow,
     binary_ieeeTheory.round_roundTiesToEven_plus_infinity,
     binary_ieeeTheory.round_roundTiesToEven_minus_infinity,
     binary_ieeeTheory.round_roundTowardPositive_plus_infinity,
     binary_ieeeTheory.round_roundTowardPositive_bottom,
     binary_ieeeTheory.round_roundTowardNegative_top,
     binary_ieeeTheory.round_roundTowardNegative_minus_infinity,
     binary_ieeeTheory.round_roundTowardZero_top,
     binary_ieeeTheory.round_roundTowardZero_bottom]
QED

Theorem smtfp_circuit_encode_overflow_correct:
  2 <= dimindex (:'w) /\ 0 < scale /\ 0 < magnitude /\
  (let maximum_exponent = dimword (:'w) - 2 in
  let fraction_width = dimindex (:'t) in
  let exponent =
    smtfp_circuit_encoded_exponent maximum_exponent fraction_width
      scale magnitude in
  let divisor = 2 ** (exponent - 1) in
  let units = magnitude * 2 ** (scale - 1) in
  let quotient = units DIV divisor in
  let residue = units MOD divisor in
  let boundary = 2 ** (fraction_width + 1) in
    exponent = maximum_exponent /\
    boundary - 1 <= quotient /\
    ~(quotient = boundary - 1 /\ residue = 0)) ==>
  smt_float_round mode to_neg
    ((if sign = 0w then &(magnitude * 2 ** (scale - 1))
      else -&(magnitude * 2 ** (scale - 1))) *
     (2 pow 1 / 2 pow (INT_MAX (:'w) + dimindex (:'t)))) =
  smtfp_rep
    (smtfp_circuit_encode mode (format : ('t,'w) smtfp)
      sign scale magnitude)
Proof
  simp_tac pure_ss [LET_THM] >> strip_tac >>
  qabbrev_tac `maximum_exponent = dimword (:'w) - 2` >>
  qabbrev_tac `fraction_width = dimindex (:'t)` >>
  qabbrev_tac
    `exponent = smtfp_circuit_encoded_exponent maximum_exponent
      fraction_width scale magnitude` >>
  qabbrev_tac `(divisor : num) = 2 ** (exponent - 1)` >>
  qabbrev_tac `units = magnitude * 2 ** (scale - 1)` >>
  qabbrev_tac `quotient = units DIV divisor` >>
  qabbrev_tac `residue = units MOD divisor` >>
  qabbrev_tac `(boundary : num) = 2 ** (fraction_width + 1)` >>
  qabbrev_tac
    `unit = 2 pow 1 / 2 pow (INT_MAX (:'w) + dimindex (:'t))` >>
  qabbrev_tac
    `rounded = smtfp_circuit_round mode sign quotient residue divisor` >>
  `1 <= maximum_exponent /\ 0 < divisor /\ 0 < unit` by
    (conj_tac
     >- (simp [Abbr `maximum_exponent`, wordsTheory.dimword_def,
               arithmeticTheory.SUB_LEFT_LESS_EQ] >>
         irule arithmeticTheory.LESS_EQ_TRANS >>
         qexists_tac `2 ** 2` >>
         simp [arithmeticTheory.EXP_BASE_LE_MONO]) >>
     simp [Abbr `divisor`, Abbr `unit`]) >>
  `residue < divisor` by
    simp [Abbr `residue`, arithmeticTheory.MOD_LESS] >>
  `units = quotient * divisor + residue` by
    (mp_tac (Q.SPEC `divisor` arithmeticTheory.DIVISION) >>
     impl_tac >- simp [] >>
     disch_then (qspec_then `units` strip_assume_tac) >>
     fs [Abbr `quotient`, Abbr `residue`]) >>
  `rounded =
   smtfp_circuit_rounded mode sign maximum_exponent fraction_width
     scale magnitude` by
    (simp [Abbr `rounded`, Abbr `quotient`, Abbr `residue`,
           Abbr `units`, Abbr `divisor`, Abbr `exponent`] >>
     mp_tac (Q.INST
       [`mode` |-> `mode`, `sign` |-> `sign`,
        `maximum_exponent` |-> `maximum_exponent`,
        `fraction_width` |-> `fraction_width`,
        `scale` |-> `scale`, `magnitude` |-> `magnitude`]
       smtfp_circuit_rounded_units) >>
     simp [smtfp_circuit_effective_exponent_def,
           arithmeticTheory.MAX_DEF] >>
     Cases_on `maximum_exponent = 1` >> simp []) >>
  `smtfp_circuit_encode mode (format : ('t,'w) smtfp)
       sign scale magnitude =
   smtfp_circuit_pack mode format sign maximum_exponent fraction_width
     exponent rounded` by
    simp [smtfp_circuit_encode_def,
          Abbr `maximum_exponent`, Abbr `fraction_width`,
          Abbr `exponent`] >>
  qpat_x_assum
    `rounded =
     smtfp_circuit_rounded mode sign maximum_exponent fraction_width
       scale magnitude`
    kall_tac >>
  `0 < boundary` by simp [Abbr `boundary`] >>
  `~float_is_zero (float_top (:'t # 'w)) /\
   ~float_is_zero (float_bottom (:'t # 'w))` by
    simp [binary_ieeeTheory.float_top_def,
          binary_ieeeTheory.float_bottom_def,
          binary_ieeeTheory.float_negate_def,
          binary_ieeeTheory.float_is_zero_def,
          wordsTheory.word_T_def, wordsTheory.UINT_MAX_def,
          wordsTheory.dimword_def] >>
  `largest (:'t # 'w) = &((boundary - 1) * divisor) * unit /\
   threshold (:'t # 'w) =
     &((boundary - 1) * divisor) * unit + &divisor * unit / 2` by
    (mp_tac (INST_TYPE [alpha |-> ``:'t``, beta |-> ``:'w``]
       smtfp_circuit_largest_threshold_units) >>
     simp [Abbr `maximum_exponent`, Abbr `fraction_width`,
           Abbr `boundary`, Abbr `divisor`, Abbr `unit`]) >>
  `ODD (boundary - 1)` by
    (simp [Abbr `boundary`, arithmeticTheory.ODD_SUB] >>
     rw [GSYM arithmeticTheory.EVEN_ODD] >>
     irule arithmeticTheory.EVEN_EXP >> simp []) >>
  `((if sign = 0w then &units else -&units) *
     (2 pow 1 /
      2 pow (INT_MAX (:'w) + fraction_width))) =
   (if sign = 0w then &units else -&units) * unit` by
    simp [Abbr `fraction_width`, Abbr `unit`] >>
  qpat_x_assum
    `((if sign = 0w then &units else -&units) * _) = _`
    (fn th => once_rewrite_tac [th]) >>
  Cases_on `quotient = boundary - 1`
  >- (`residue <> 0` by fs [] >>
      `largest (:'t # 'w) < &units * unit /\
       -&units * unit < -largest (:'t # 'w)` by
        (simp [realTheory.REAL_OF_NUM_ADD,
               realTheory.REAL_OF_NUM_MUL] >>
         realLib.REAL_ASM_ARITH_TAC) >>
      `(&units * unit < threshold (:'t # 'w) <=>
        2 * residue < divisor) /\
       (threshold (:'t # 'w) <= &units * unit <=>
        divisor <= 2 * residue) /\
       (-threshold (:'t # 'w) < -&units * unit <=>
        2 * residue < divisor) /\
       (-&units * unit <= -threshold (:'t # 'w) <=>
        divisor <= 2 * residue)` by
       (mp_tac (Q.SPECL
           [`unit`, `residue`, `divisor`, `boundary - 1`]
           smtfp_circuit_overflow_midpoint_units) >>
         simp [realTheory.REAL_OF_NUM_ADD,
               realTheory.REAL_OF_NUM_MUL]) >>
      qpat_x_assum `Abbrev (units = _)` kall_tac >>
      qpat_x_assum `Abbrev (unit = _)` kall_tac >>
      qpat_x_assum `units = quotient * divisor + residue` kall_tac >>
      `-unit * &units = -&units * unit` by
        realLib.REAL_ARITH_TAC >>
      Cases_on `sign = 0w`
      >- (asm_rewrite_tac [] >> Cases_on `mode`
      >- (Cases_on `divisor <= 2 * residue`
          >- (`rounded = boundary` by
                (simp [Abbr `rounded`,
                       smtfp_circuit_round_def,
                       smtfp_circuit_round_up_def] >> decide_tac) >>
              `smtfp_rep
                 (smtfp_circuit_pack RNE format 0w maximum_exponent
                    fraction_width maximum_exponent rounded) =
               float_plus_infinity (:'t # 'w)` by
                (asm_rewrite_tac [] >>
                 simp [smtfp_circuit_pack_def,
                       smtfp_circuit_overflow_rep]) >>
              `round roundTiesToEven (&units * unit) =
               float_plus_infinity (:'t # 'w)` by
                (irule binary_ieeeTheory.round_roundTiesToEven_plus_infinity >>
                 simp []) >>
              asm_simp_tac (srw_ss())
                [smt_float_round_def, smt_round_def, LET_THM,
                 binary_ieeeTheory.infinity_properties])
          >> `rounded = boundary - 1` by
            (simp [Abbr `rounded`,
                   smtfp_circuit_round_def,
                   smtfp_circuit_round_up_def]) >>
          `smtfp_rep
             (smtfp_circuit_pack RNE format 0w maximum_exponent
                fraction_width maximum_exponent rounded) =
           float_top (:'t # 'w)` by
            (asm_rewrite_tac [] >>
             simp [smtfp_circuit_pack_top,
                   smtfp_circuit_top_rep, Abbr `maximum_exponent`,
                   Abbr `fraction_width`, Abbr `boundary`]) >>
          `round roundTiesToEven (&units * unit) =
           float_top (:'t # 'w)` by
            (irule smtfp_circuit_RNE_positive_overflow_band >> simp []) >>
          asm_simp_tac (srw_ss())
            [smt_float_round_def, smt_round_def, LET_THM])
      >- (Cases_on `divisor <= 2 * residue`
          >- (`rounded = boundary` by
                (simp [Abbr `rounded`,
                       smtfp_circuit_round_def,
                       smtfp_circuit_round_up_def] >> decide_tac) >>
              `smtfp_rep
                 (smtfp_circuit_pack RNA format 0w maximum_exponent
                    fraction_width maximum_exponent rounded) =
               float_plus_infinity (:'t # 'w)` by
                (asm_rewrite_tac [] >>
                 simp [smtfp_circuit_pack_def,
                       smtfp_circuit_overflow_rep]) >>
              `round_tiesToAway (&units * unit) =
               float_plus_infinity (:'t # 'w)` by simp [] >>
              asm_simp_tac (srw_ss())
                [smt_float_round_def, smt_round_def, LET_THM,
                 binary_ieeeTheory.infinity_properties])
          >> `rounded = boundary - 1` by
            (simp [Abbr `rounded`,
                   smtfp_circuit_round_def,
                   smtfp_circuit_round_up_def]) >>
          `smtfp_rep
             (smtfp_circuit_pack RNA format 0w maximum_exponent
                fraction_width maximum_exponent rounded) =
           float_top (:'t # 'w)` by
            (asm_rewrite_tac [] >>
             simp [smtfp_circuit_pack_top,
                   smtfp_circuit_top_rep, Abbr `maximum_exponent`,
                   Abbr `fraction_width`, Abbr `boundary`]) >>
          `round_tiesToAway (&units * unit) = float_top (:'t # 'w)` by
            (irule smtfp_circuit_RNA_positive_overflow_band >> simp []) >>
          asm_simp_tac (srw_ss())
            [smt_float_round_def, smt_round_def, LET_THM])
      >- (`rounded = boundary` by
            (simp [Abbr `rounded`,
                   smtfp_circuit_round_def,
                   smtfp_circuit_round_up_def] >> decide_tac) >>
          `smtfp_rep
             (smtfp_circuit_pack RTP format 0w maximum_exponent
                fraction_width maximum_exponent rounded) =
           float_plus_infinity (:'t # 'w)` by
            (asm_rewrite_tac [] >>
             simp [smtfp_circuit_pack_def,
                   smtfp_circuit_overflow_rep]) >>
          asm_simp_tac (srw_ss())
            [smt_float_round_def, smt_round_def, LET_THM,
             binary_ieeeTheory.infinity_properties,
             binary_ieeeTheory.round_roundTowardPositive_plus_infinity])
      >- (`rounded = boundary - 1` by
            simp [Abbr `rounded`,
                  smtfp_circuit_round_def,
                  smtfp_circuit_round_up_def] >>
          `smtfp_rep
             (smtfp_circuit_pack RTN format 0w maximum_exponent
                fraction_width maximum_exponent rounded) =
           float_top (:'t # 'w)` by
            (asm_rewrite_tac [] >>
             simp [smtfp_circuit_pack_top,
                   smtfp_circuit_top_rep, Abbr `maximum_exponent`,
                   Abbr `fraction_width`, Abbr `boundary`]) >>
          asm_simp_tac (srw_ss())
            [smt_float_round_def, smt_round_def, LET_THM,
             binary_ieeeTheory.round_roundTowardNegative_top])
      >- (`rounded = boundary - 1` by
            simp [Abbr `rounded`,
                  smtfp_circuit_round_def,
                  smtfp_circuit_round_up_def] >>
          `smtfp_rep
             (smtfp_circuit_pack RTZ format 0w maximum_exponent
                fraction_width maximum_exponent rounded) =
           float_top (:'t # 'w)` by
            (asm_rewrite_tac [] >>
             simp [smtfp_circuit_pack_top,
                   smtfp_circuit_top_rep, Abbr `maximum_exponent`,
                   Abbr `fraction_width`, Abbr `boundary`]) >>
          asm_simp_tac (srw_ss())
            [smt_float_round_def, smt_round_def, LET_THM,
             binary_ieeeTheory.round_roundTowardZero_top])) >>
      `sign = 1w` by
        (wordsLib.Cases_on_word_value `sign` >> fs []) >>
      asm_rewrite_tac [] >> Cases_on `mode`
      >- (Cases_on `divisor <= 2 * residue`
          >- (`rounded = boundary` by
                (simp [Abbr `rounded`,
                       smtfp_circuit_round_def,
                       smtfp_circuit_round_up_def] >> decide_tac) >>
              `smtfp_rep
                 (smtfp_circuit_pack RNE format 1w maximum_exponent
                    fraction_width maximum_exponent rounded) =
               float_minus_infinity (:'t # 'w)` by
                (asm_rewrite_tac [] >>
                 simp [smtfp_circuit_pack_def,
                       smtfp_circuit_overflow_rep]) >>
              asm_simp_tac (srw_ss())
                [smt_float_round_def, smt_round_def, LET_THM,
                 binary_ieeeTheory.infinity_properties,
                 binary_ieeeTheory.round_roundTiesToEven_minus_infinity])
          >> `rounded = boundary - 1` by
            (simp [Abbr `rounded`,
                   smtfp_circuit_round_def,
                   smtfp_circuit_round_up_def]) >>
          `smtfp_rep
             (smtfp_circuit_pack RNE format 1w maximum_exponent
                fraction_width maximum_exponent rounded) =
           float_bottom (:'t # 'w)` by
            (asm_rewrite_tac [] >>
             simp [smtfp_circuit_pack_top,
                   smtfp_circuit_top_rep, Abbr `maximum_exponent`,
                   Abbr `fraction_width`, Abbr `boundary`]) >>
          `round roundTiesToEven (-&units * unit) =
           float_bottom (:'t # 'w)` by
            (irule smtfp_circuit_RNE_negative_overflow_band >> simp []) >>
          asm_simp_tac (srw_ss())
            [smt_float_round_def, smt_round_def, LET_THM])
      >- (Cases_on `divisor <= 2 * residue`
          >- (`rounded = boundary` by
                (simp [Abbr `rounded`,
                       smtfp_circuit_round_def,
                       smtfp_circuit_round_up_def] >> decide_tac) >>
              `smtfp_rep
                 (smtfp_circuit_pack RNA format 1w maximum_exponent
                    fraction_width maximum_exponent rounded) =
               float_minus_infinity (:'t # 'w)` by
                (asm_rewrite_tac [] >>
                 simp [smtfp_circuit_pack_def,
                       smtfp_circuit_overflow_rep]) >>
              `round_tiesToAway (-&units * unit) =
               float_minus_infinity (:'t # 'w)` by simp [] >>
              asm_simp_tac (srw_ss())
                [smt_float_round_def, smt_round_def, LET_THM,
                 binary_ieeeTheory.infinity_properties])
          >> `rounded = boundary - 1` by
            (simp [Abbr `rounded`,
                   smtfp_circuit_round_def,
                   smtfp_circuit_round_up_def]) >>
          `smtfp_rep
             (smtfp_circuit_pack RNA format 1w maximum_exponent
                fraction_width maximum_exponent rounded) =
           float_bottom (:'t # 'w)` by
            (asm_rewrite_tac [] >>
             simp [smtfp_circuit_pack_top,
                   smtfp_circuit_top_rep, Abbr `maximum_exponent`,
                   Abbr `fraction_width`, Abbr `boundary`]) >>
          `round_tiesToAway (-&units * unit) = float_bottom (:'t # 'w)` by
            (irule smtfp_circuit_RNA_negative_overflow_band >> simp []) >>
          asm_simp_tac (srw_ss())
            [smt_float_round_def, smt_round_def, LET_THM])
      >- (`rounded = boundary - 1` by
            simp [Abbr `rounded`,
                  smtfp_circuit_round_def,
                  smtfp_circuit_round_up_def] >>
          `smtfp_rep
             (smtfp_circuit_pack RTP format 1w maximum_exponent
                fraction_width maximum_exponent rounded) =
           float_bottom (:'t # 'w)` by
            (asm_rewrite_tac [] >>
             simp [smtfp_circuit_pack_top,
                   smtfp_circuit_top_rep, Abbr `maximum_exponent`,
                   Abbr `fraction_width`, Abbr `boundary`]) >>
          asm_simp_tac (srw_ss())
            [smt_float_round_def, smt_round_def, LET_THM,
             binary_ieeeTheory.round_roundTowardPositive_bottom])
      >- (`rounded = boundary` by
            (simp [Abbr `rounded`,
                   smtfp_circuit_round_def,
                   smtfp_circuit_round_up_def] >> decide_tac) >>
          `smtfp_rep
             (smtfp_circuit_pack RTN format 1w maximum_exponent
                fraction_width maximum_exponent rounded) =
           float_minus_infinity (:'t # 'w)` by
            (asm_rewrite_tac [] >>
             simp [smtfp_circuit_pack_def,
                   smtfp_circuit_overflow_rep]) >>
          asm_simp_tac (srw_ss())
            [smt_float_round_def, smt_round_def, LET_THM,
             binary_ieeeTheory.infinity_properties,
             binary_ieeeTheory.round_roundTowardNegative_minus_infinity])
      >- (`rounded = boundary - 1` by
            simp [Abbr `rounded`,
                  smtfp_circuit_round_def,
                  smtfp_circuit_round_up_def] >>
          `smtfp_rep
             (smtfp_circuit_pack RTZ format 1w maximum_exponent
                fraction_width maximum_exponent rounded) =
           float_bottom (:'t # 'w)` by
            (asm_rewrite_tac [] >>
             simp [smtfp_circuit_pack_top,
                   smtfp_circuit_top_rep, Abbr `maximum_exponent`,
                   Abbr `fraction_width`, Abbr `boundary`]) >>
          asm_simp_tac (srw_ss())
            [smt_float_round_def, smt_round_def, LET_THM,
             binary_ieeeTheory.round_roundTowardZero_bottom])) >>
  `boundary <= quotient` by decide_tac >>
  `threshold (:'t # 'w) < &units * unit /\
   -&units * unit < -threshold (:'t # 'w)` by
    (`&((boundary - 1) * divisor) * unit +
       &divisor * unit / 2 < &units * unit` by
       (mp_tac (Q.INST
          [`boundary` |-> `boundary`, `divisor` |-> `divisor`,
           `unit` |-> `unit`, `quotient` |-> `quotient`,
           `units` |-> `units`, `residue` |-> `residue`]
          smtfp_circuit_strict_overflow_units) >>
        asm_simp_tac std_ss []) >>
     realLib.REAL_ASM_ARITH_TAC) >>
  `boundary <= rounded` by
    (simp [Abbr `rounded`, smtfp_circuit_round_def] >>
     decide_tac) >>
  `smtfp_rep
     (smtfp_circuit_encode mode (format : ('t,'w) smtfp)
       sign scale magnitude) =
   smtfp_rep (smtfp_circuit_overflow mode format sign)` by
    (asm_rewrite_tac [] >>
     simp [smtfp_circuit_pack_def] >> decide_tac) >>
  qpat_x_assum `Abbrev (units = _)` kall_tac >>
  qpat_x_assum `Abbrev (unit = _)` kall_tac >>
  qpat_x_assum `units = quotient * divisor + residue` kall_tac >>
  `((if sign = 0w then &units else -&units) * unit) =
   (if sign = 0w then &units * unit else -&units * unit)` by
    (Cases_on `sign = 0w` >> simp []) >>
  pop_assum SUBST1_TAC >>
  qpat_x_assum
    `smtfp_rep (smtfp_circuit_encode _ _ _ _ _) = _`
    (fn th => once_rewrite_tac [th]) >>
  irule smtfp_circuit_strict_overflow_round >>
  asm_simp_tac std_ss []
QED

Theorem circuit_real_scale_units[local]:
  0 < scale ==>
  (if sign = 0w then &magnitude else -&magnitude) *
    (2 pow scale / denominator) =
  (if sign = 0w then &(magnitude * 2 ** (scale - 1))
   else -&(magnitude * 2 ** (scale - 1))) *
    (2 pow 1 / denominator)
Proof
  strip_tac >>
  Cases_on `scale`
  >- fs []
  >- (Cases_on `sign = 0w` >>
      asm_simp_tac bool_ss
        [arithmeticTheory.SUC_SUB1, realTheory.pow,
         realTheory.REAL_OF_NUM_POW, arithmeticTheory.EXP,
         GSYM realTheory.REAL_OF_NUM_MUL,
         EVAL ``((2 : num) ** 1)``] >>
      RealField.REAL_FIELD_TAC)
QED

Theorem smtfp_circuit_encode_correct:
  2 <= dimindex (:'w) /\ 0 < scale /\ 0 < magnitude ==>
  smt_float_round mode to_neg
    ((if sign = 0w then &magnitude else -&magnitude) *
     (2 pow scale /
      2 pow (INT_MAX (:'w) + dimindex (:'t)))) =
  smtfp_rep
    (smtfp_circuit_encode mode (format : ('t,'w) smtfp)
      sign scale magnitude)
Proof
  strip_tac >>
  `((if sign = 0w then &magnitude else -&magnitude) *
      (2 pow scale /
       2 pow (INT_MAX (:'w) + dimindex (:'t)))) =
   (if sign = 0w then &(magnitude * 2 ** (scale - 1))
    else -&(magnitude * 2 ** (scale - 1))) *
      (2 pow 1 /
       2 pow (INT_MAX (:'w) + dimindex (:'t)))` by
    (irule circuit_real_scale_units >>
     qpat_x_assum `0 < scale` ACCEPT_TAC) >>
  pop_assum (fn th => once_rewrite_tac [th]) >>
  qabbrev_tac `maximum_exponent : num = dimword (:'w) - 2` >>
  qabbrev_tac `fraction_width : num = dimindex (:'t)` >>
  qabbrev_tac
    `exponent : num = smtfp_circuit_encoded_exponent maximum_exponent
      fraction_width scale magnitude` >>
  qabbrev_tac `divisor : num = 2 ** (exponent - 1)` >>
  qabbrev_tac `units : num = magnitude * 2 ** (scale - 1)` >>
  qabbrev_tac `quotient : num = units DIV divisor` >>
  qabbrev_tac `residue : num = units MOD divisor` >>
  qabbrev_tac `boundary : num = 2 ** (fraction_width + 1)` >>
  qabbrev_tac
    `rounded : num =
       smtfp_circuit_round mode sign quotient residue divisor` >>
  `1 <= maximum_exponent` by
    (simp [Abbr `maximum_exponent`, wordsTheory.dimword_def] >>
     `2 ** 2 <= 2 ** dimindex (:'w)` by
       (irule bitTheory.TWOEXP_MONO2 >>
        qpat_x_assum `2 <= dimindex (:'w)` ACCEPT_TAC) >>
     qpat_x_assum `2 ** 2 <= _` mp_tac >>
     rewrite_tac [EVAL ``((2 : num) ** 2)``] >>
     numLib.ARITH_TAC) >>
  `1 <= exponent /\ exponent <= maximum_exponent` by
    (mp_tac (Q.INST
       [`maximum_exponent` |-> `maximum_exponent`,
        `fraction_width` |-> `fraction_width`, `scale` |-> `scale`,
        `magnitude` |-> `magnitude`]
       smtfp_circuit_effective_encoded) >>
     simp [Abbr `exponent`]) >>
  `0 < units /\ 0 < divisor` by
    simp [Abbr `units`, Abbr `divisor`] >>
  `residue < divisor` by
    simp [Abbr `residue`, arithmeticTheory.MOD_LESS] >>
  `quotient =
   smtfp_circuit_quotient maximum_exponent fraction_width scale
    magnitude` by
    (simp_tac pure_ss
       [Abbr `quotient`, Abbr `units`, Abbr `divisor`,
        Abbr `exponent`] >>
     irule smtfp_circuit_quotient_encoded >>
     asm_rewrite_tac []) >>
  `rounded =
   smtfp_circuit_rounded mode sign maximum_exponent fraction_width
    scale magnitude` by
    (simp_tac pure_ss
       [Abbr `rounded`, Abbr `quotient`, Abbr `residue`,
        Abbr `units`, Abbr `divisor`, Abbr `exponent`] >>
     irule smtfp_circuit_rounded_encoded >>
     asm_rewrite_tac []) >>
  Cases_on
    `exponent = maximum_exponent /\
     boundary - 1 <= quotient /\
     ~(quotient = boundary - 1 /\ residue = 0)`
  >- (qpat_x_assum
        `exponent = maximum_exponent /\
         boundary - 1 <= quotient /\
         ~(quotient = boundary - 1 /\ residue = 0)`
        strip_assume_tac >>
      `0 < boundary` by simp [Abbr `boundary`] >>
      `boundary <= quotient + 1` by
        (qpat_x_assum `boundary - 1 <= quotient` mp_tac >>
         qpat_x_assum `0 < boundary` mp_tac >>
         numLib.ARITH_TAC) >>
      `quotient = boundary - 1 ==> residue <> 0` by fs [] >>
      simp_tac pure_ss [Abbr `units`, Abbr `fraction_width`] >>
      irule smtfp_circuit_encode_overflow_correct >>
      simp_tac pure_ss
        [LET_THM, Abbr `maximum_exponent`, Abbr `exponent`,
         Abbr `divisor`, Abbr `quotient`, Abbr `residue`,
         Abbr `boundary`] >>
      asm_rewrite_tac [])
  >- (`rounded <= boundary /\
   (rounded = boundary ==> exponent < maximum_exponent) /\
   (residue <> 0 /\ quotient + 1 = boundary ==>
    exponent < maximum_exponent)` by
    (mp_tac (Q.INST
       [`mode` |-> `mode`, `sign` |-> `sign`,
        `q` |-> `quotient`, `residue` |-> `residue`,
       `divisor` |-> `divisor`]
       smtfp_circuit_round_bounds) >>
     simp_tac pure_ss [Abbr `rounded`] >> strip_tac >>
     `0 < boundary` by simp [Abbr `boundary`] >>
     Cases_on `exponent < maximum_exponent`
     >- (`smtfp_circuit_quotient maximum_exponent fraction_width
           scale magnitude < 2 ** (fraction_width + 1)` by
           (irule smtfp_circuit_quotient_normalized_upper >>
            asm_simp_tac (srw_ss()) [Abbr `exponent`]) >>
         `quotient < boundary` by
           asm_simp_tac std_ss [Abbr `boundary`] >>
         conj_tac
         >- (qpat_x_assum
               `smtfp_circuit_round mode sign quotient residue divisor <=
                quotient + 1` mp_tac >>
             qpat_x_assum `quotient < boundary` mp_tac >>
             numLib.ARITH_TAC)
         >- (conj_tac
             >- (strip_tac >>
                 qpat_x_assum
                   `exponent < maximum_exponent` ACCEPT_TAC)
             >- (strip_tac >>
                 qpat_x_assum
                   `exponent < maximum_exponent` ACCEPT_TAC)))
     >- (`exponent = maximum_exponent` by
           (qpat_x_assum `~(exponent < maximum_exponent)` mp_tac >>
            qpat_x_assum `exponent <= maximum_exponent` mp_tac >>
            numLib.ARITH_TAC) >>
         Cases_on `quotient < boundary - 1`
         >- (conj_tac
             >- (qpat_x_assum
                   `smtfp_circuit_round mode sign quotient residue
                      divisor <= quotient + 1` mp_tac >>
                 qpat_x_assum `quotient < boundary - 1` mp_tac >>
                 qpat_x_assum `0 < boundary` mp_tac >>
                 intLib.ARITH_TAC)
             >- (conj_tac
                 >- (strip_tac >>
                     qpat_x_assum
                       `smtfp_circuit_round mode sign quotient residue
                          divisor <= quotient + 1` mp_tac >>
                     qpat_x_assum
                       `quotient < boundary - 1` mp_tac >>
                     qpat_x_assum `0 < boundary` mp_tac >>
                     intLib.ARITH_TAC)
                 >- (strip_tac >>
                     qpat_x_assum
                       `quotient < boundary - 1` mp_tac >>
                     qpat_x_assum
                       `quotient + 1 = boundary` mp_tac >>
                     qpat_x_assum `0 < boundary` mp_tac >>
                     intLib.ARITH_TAC)))
         >- (`boundary - 1 <= quotient` by
               (qpat_x_assum `~(quotient < boundary - 1)` mp_tac >>
                intLib.ARITH_TAC) >>
             `quotient = boundary - 1` by
               (CCONTR_TAC >>
                qpat_x_assum
                  `~(exponent = maximum_exponent /\
                     boundary - 1 <= quotient /\
                     ~(quotient = boundary - 1 /\ residue = 0))`
                  mp_tac >>
                asm_rewrite_tac []) >>
             `residue = 0` by
               (CCONTR_TAC >>
                qpat_x_assum
                  `~(exponent = maximum_exponent /\
                     boundary - 1 <= quotient /\
                     ~(quotient = boundary - 1 /\ residue = 0))`
                  mp_tac >>
                asm_rewrite_tac []) >>
             `smtfp_circuit_round mode sign quotient residue divisor =
              quotient` by
               (qpat_x_assum `residue = 0`
                  (fn th => rewrite_tac [th]) >>
                rewrite_tac [smtfp_circuit_round_exact]) >>
             fs [] >> numLib.ARITH_TAC))) >>
  simp_tac pure_ss [Abbr `units`, Abbr `fraction_width`] >>
  irule smtfp_circuit_encode_finite_correct >>
  simp_tac pure_ss
    [LET_THM, Abbr `maximum_exponent`, Abbr `exponent`,
     Abbr `divisor`, Abbr `quotient`, Abbr `residue`,
     Abbr `rounded`, Abbr `boundary`] >>
  asm_rewrite_tac [])
QED

Theorem smtfp_addsub_circuit_finite_nonzero_correspondence:
  2 <= dimindex (:'w) /\
  (smtfp_rep x).Exponent <> UINT_MAXw /\
  (smtfp_rep y).Exponent <> UINT_MAXw /\
  smtfp_addsub_magnitude subtract x y <> 0 ==>
  (if subtract then smtfp_sub mode x y else smtfp_add mode x y) =
  SND (smtfp_addsub_circuit subtract mode (x : ('t,'w) smtfp) y)
Proof
  strip_tac >>
  Cases_on
    `(smtfp_rep y).Exponent = 0w /\
     (smtfp_rep y).Significand = 0w`
  >- (`y = smtfp_bits (smtfp_rep y).Sign 0w 0w` by
        (irule (iffLR smtfp_rep_11) >>
         rewrite_tac [smtfp_rep_bits, smtfp_canon_zero_bits] >>
         simp_tac pure_ss
           [binary_ieeeTheory.float_component_equality] >>
         simp []) >>
      pop_assum SUBST_ALL_TAC >>
      irule
        smtfp_addsub_circuit_finite_right_zero_nonzero_correspondence >>
      simp [] >>
      strip_tac >>
      fs [smtfp_addsub_magnitude_def,
          smtfp_addsub_trace_def,
          smtfp_circuit_sig_def,
          smtfp_circuit_exp_def])
  >- (`smt_float_round mode
        (if subtract then
           (if float_to_real (smtfp_rep x) = 0 /\
               float_to_real (smtfp_rep y) = 0 /\
               (smtfp_rep x).Sign <> (smtfp_rep y).Sign then
              (smtfp_rep x).Sign = 1w
            else mode = RTN)
         else
           (if float_to_real (smtfp_rep x) = 0 /\
               float_to_real (smtfp_rep y) = 0 /\
               (smtfp_rep x).Sign = (smtfp_rep y).Sign then
              (smtfp_rep x).Sign = 1w
            else mode = RTN))
        (float_to_real (smtfp_rep x) +
         (if subtract then -float_to_real (smtfp_rep y)
          else float_to_real (smtfp_rep y))) =
      smtfp_rep
        (smtfp_circuit_encode mode x
          (smtfp_addsub_result_sign subtract x y)
          (smtfp_addsub_scale subtract x y)
          (smtfp_addsub_magnitude subtract x y))` by
        (rewrite_tac [smtfp_addsub_exact_value] >>
         irule smtfp_circuit_encode_correct >> simp []) >>
      `SND (smtfp_addsub_circuit subtract mode x y) =
       smtfp_circuit_encode mode x
         (smtfp_addsub_result_sign subtract x y)
         (smtfp_addsub_scale subtract x y)
         (smtfp_addsub_magnitude subtract x y)` by
        (rw [smtfp_addsub_circuit_def,
             smtfp_addsub_result_sign_def,
             smtfp_addsub_scale_def,
             smtfp_addsub_magnitude_def] >>
         pairarg_tac >> gvs [] >>
         fs [smtfp_addsub_magnitude_def] >>
         Cases_on `(smtfp_rep y).Exponent = 0w` >> fs []) >>
      Cases_on `subtract` >>
      fs [smtfp_add_def, smtfp_sub_def,
          smt_float_add_finite_round,
          smt_float_sub_finite_round,
          realTheory.real_sub])
QED

Theorem smtfp_addsub_circuit_finite_correspondence:
  2 <= dimindex (:'w) /\
  (smtfp_rep x).Exponent <> UINT_MAXw /\
  (smtfp_rep y).Exponent <> UINT_MAXw ==>
  (if subtract then smtfp_sub mode x y else smtfp_add mode x y) =
  SND (smtfp_addsub_circuit subtract mode (x : ('t,'w) smtfp) y)
Proof
  strip_tac >>
  Cases_on `smtfp_addsub_magnitude subtract x y = 0`
  >- (irule smtfp_addsub_circuit_exact_zero_correspondence >>
      simp [smtfp_addsub_exact_zero]) >>
  irule smtfp_addsub_circuit_finite_nonzero_correspondence >> simp []
QED

Theorem smtfp_infinity_rep[local]:
  (smtfp_rep x).Exponent = UINT_MAXw /\
  (smtfp_rep x).Significand = 0w ==>
  (x : ('t,'w) smtfp) =
  smtfp_bits (smtfp_rep x).Sign UINT_MAXw 0w
Proof
  strip_tac >>
  irule (iffLR smtfp_rep_11) >>
  rewrite_tac [smtfp_rep_bits] >>
  simp_tac pure_ss [canon_def, smtfp_nan_pattern_def,
    binary_ieeeTheory.float_is_nan_def,
    binary_ieeeTheory.float_value_def,
    binary_ieeeTheory.float_component_equality] >>
  simp []
QED

Theorem smtfp_nan_rep[local]:
  (smtfp_rep x).Exponent = UINT_MAXw /\
  (smtfp_rep x).Significand <> 0w ==>
  (x : ('t,'w) smtfp) = smtfp_nan
Proof
  strip_tac >>
  `float_is_nan (smtfp_rep x)` by
    simp [binary_ieeeTheory.float_is_nan_def,
          binary_ieeeTheory.float_value_def] >>
  `smtfp_rep x = (float_canon_qnan : ('t,'w) float)` by
    metis_tac [smtfp_rep_canonical, smtfp_canonical_def] >>
  `x = SmtFp (smtfp_rep x)` by simp [] >>
  asm_rewrite_tac [] >>
  simp [smtfp_nan_def, canon_def]
QED

Theorem smtfp_left_nan_circuit[local]:
  (if subtract then smtfp_sub mode smtfp_nan y
   else smtfp_add mode smtfp_nan y) =
  SND (smtfp_addsub_circuit subtract mode
    (smtfp_nan : ('t,'w) smtfp) y)
Proof
  Cases_on `subtract` >> Cases_on `mode` >>
  Cases_on `float_value (smtfp_rep y)` >>
  simp [smtfp_add_def, smtfp_sub_def,
        smt_float_add_def, smt_float_sub_def,
        smtfp_addsub_circuit_def,
        to_binary_rounding_def,
        binary_ieeeTheory.float_add_def,
        binary_ieeeTheory.float_sub_def,
        binary_ieeeTheory.float_value_def,
        binary_ieeeTheory.float_is_nan_def,
        binary_ieeeTheory.some_nan_properties,
        smtfp_nan_def, canon_def, smtfp_canonical_def,
        smtfp_nan_pattern_def, float_canon_qnan_def,
        canon_qnan_msb]
QED

Theorem smtfp_right_nan_circuit[local]:
  (if subtract then smtfp_sub mode x smtfp_nan
   else smtfp_add mode x smtfp_nan) =
  SND (smtfp_addsub_circuit subtract mode
    (x : ('t,'w) smtfp) smtfp_nan)
Proof
  Cases_on `subtract` >>
  simp [smtfp_add_nan_circuit_correspondence,
        smtfp_sub_nan_circuit_correspondence]
QED

Theorem smtfp_left_infinity_finite_circuit[local]:
  (smtfp_rep y).Exponent <> UINT_MAXw ==>
  (if subtract then
     smtfp_sub mode (smtfp_bits sign UINT_MAXw 0w) y
   else smtfp_add mode (smtfp_bits sign UINT_MAXw 0w) y) =
  SND (smtfp_addsub_circuit subtract mode
    (smtfp_bits sign UINT_MAXw 0w : ('t,'w) smtfp) y)
Proof
  strip_tac >>
  wordsLib.Cases_on_word_value `sign` >>
  Cases_on `subtract` >> Cases_on `mode` >>
  Cases_on `float_value (smtfp_rep y)` >>
  fs [smtfp_add_def, smtfp_sub_def,
      smt_float_add_def, smt_float_sub_def,
      smtfp_addsub_circuit_def, smtfp_circuit_infinity_def,
      to_binary_rounding_def,
      binary_ieeeTheory.float_add_def,
      binary_ieeeTheory.float_sub_def,
      binary_ieeeTheory.float_value_def,
      binary_ieeeTheory.float_is_nan_def,
      binary_ieeeTheory.some_nan_properties,
      smtfp_bits_def, canon_def, smtfp_canonical_def,
      smtfp_nan_pattern_def]
QED

Theorem smtfp_right_infinity_finite_circuit[local]:
  (smtfp_rep x).Exponent <> UINT_MAXw ==>
  (if subtract then smtfp_sub mode x (smtfp_bits sign UINT_MAXw 0w)
   else smtfp_add mode x (smtfp_bits sign UINT_MAXw 0w)) =
  SND (smtfp_addsub_circuit subtract mode
    (x : ('t,'w) smtfp) (smtfp_bits sign UINT_MAXw 0w))
Proof
  strip_tac >>
  wordsLib.Cases_on_word_value `sign` >>
  Cases_on `subtract` >> Cases_on `mode` >>
  Cases_on `float_value (smtfp_rep x)` >>
  fs [smtfp_add_def, smtfp_sub_def,
      smt_float_add_def, smt_float_sub_def,
      smtfp_addsub_circuit_def, smtfp_circuit_infinity_def,
      to_binary_rounding_def,
      binary_ieeeTheory.float_add_def,
      binary_ieeeTheory.float_sub_def,
      binary_ieeeTheory.float_value_def,
      binary_ieeeTheory.float_is_nan_def,
      binary_ieeeTheory.float_negate_def,
      binary_ieeeTheory.float_component_equality,
      binary_ieeeTheory.some_nan_properties,
      smtfp_bits_def, canon_def, smtfp_canonical_def,
      smtfp_nan_pattern_def]
QED

Theorem smtfp_both_infinity_circuit[local]:
  (if subtract then
     smtfp_sub mode (smtfp_bits sx UINT_MAXw 0w)
       (smtfp_bits sy UINT_MAXw 0w)
   else
     smtfp_add mode (smtfp_bits sx UINT_MAXw 0w)
       (smtfp_bits sy UINT_MAXw 0w)) =
  SND (smtfp_addsub_circuit subtract mode
    (smtfp_bits sx UINT_MAXw 0w : ('t,'w) smtfp)
    (smtfp_bits sy UINT_MAXw 0w))
Proof
  wordsLib.Cases_on_word_value `sx` >>
  wordsLib.Cases_on_word_value `sy` >>
  Cases_on `subtract` >> Cases_on `mode` >>
  simp [smtfp_add_def, smtfp_sub_def,
      smt_float_add_def, smt_float_sub_def,
      smtfp_addsub_circuit_def, smtfp_circuit_infinity_def,
      to_binary_rounding_def,
      binary_ieeeTheory.float_add_def,
      binary_ieeeTheory.float_sub_def,
      binary_ieeeTheory.float_value_def,
      binary_ieeeTheory.float_is_nan_def,
      binary_ieeeTheory.float_negate_def,
      binary_ieeeTheory.float_component_equality,
      binary_ieeeTheory.some_nan_properties,
      smtfp_bits_def, smtfp_nan_def, canon_def,
      smtfp_canonical_def, smtfp_nan_pattern_def]
QED

Theorem smtfp_addsub_circuit_correspondence:
  2 <= dimindex (:'w) ==>
  (if subtract then smtfp_sub mode x y else smtfp_add mode x y) =
  SND (smtfp_addsub_circuit subtract mode (x : ('t,'w) smtfp) y)
Proof
  strip_tac >>
  Cases_on `(smtfp_rep x).Exponent = UINT_MAXw`
  >- (Cases_on `(smtfp_rep y).Exponent = UINT_MAXw`
      >- (Cases_on `(smtfp_rep x).Significand = 0w`
          >- (Cases_on `(smtfp_rep y).Significand = 0w`
              >- (`x = smtfp_bits (smtfp_rep x).Sign UINT_MAXw 0w` by
                    metis_tac [smtfp_infinity_rep] >>
                  `y = smtfp_bits (smtfp_rep y).Sign UINT_MAXw 0w` by
                    metis_tac [smtfp_infinity_rep] >>
                  metis_tac [smtfp_both_infinity_circuit])
              >- (`y = smtfp_nan` by
                    metis_tac [smtfp_nan_rep] >>
                  metis_tac [smtfp_right_nan_circuit]))
          >- (`x = smtfp_nan` by
                metis_tac [smtfp_nan_rep] >>
              metis_tac [smtfp_left_nan_circuit]))
      >- (Cases_on `(smtfp_rep x).Significand = 0w`
          >- (`x = smtfp_bits (smtfp_rep x).Sign UINT_MAXw 0w` by
                metis_tac [smtfp_infinity_rep] >>
              metis_tac [smtfp_left_infinity_finite_circuit])
          >- (`x = smtfp_nan` by
                metis_tac [smtfp_nan_rep] >>
              metis_tac [smtfp_left_nan_circuit])))
  >- (Cases_on `(smtfp_rep y).Exponent = UINT_MAXw`
      >- (Cases_on `(smtfp_rep y).Significand = 0w`
          >- (`y = smtfp_bits (smtfp_rep y).Sign UINT_MAXw 0w` by
                metis_tac [smtfp_infinity_rep] >>
              metis_tac [smtfp_right_infinity_finite_circuit])
          >- (`y = smtfp_nan` by
                metis_tac [smtfp_nan_rep] >>
              metis_tac [smtfp_right_nan_circuit]))
      >- metis_tac [smtfp_addsub_circuit_finite_correspondence])
QED

Theorem smtfp_add_circuit_correspondence:
  2 <= dimindex (:'w) ==>
  smtfp_add mode x y =
  SND (smtfp_addsub_circuit F mode (x : ('t,'w) smtfp) y)
Proof
  metis_tac [smtfp_addsub_circuit_correspondence]
QED

Theorem smtfp_add_circuit_RTN_infinity_bits[local]:
  2 <= dimindex (:'w) ==>
  SND (smtfp_addsub_circuit F RTN
    (smtfp_bits s UINT_MAXw 0w : ('t,'w) smtfp)
    (smtfp_bits 0w 0w 0w)) = smtfp_bits s UINT_MAXw 0w
Proof
  strip_tac >> wordsLib.Cases_on_word_value `s` >>
  simp [smtfp_addsub_circuit_def, smtfp_circuit_infinity_def,
        smtfp_rep_bits, canon_def, smtfp_nan_pattern_def]
QED

Theorem smtfp_add_circuit_RTN_nan[local]:
  2 <= dimindex (:'w) ==>
  SND (smtfp_addsub_circuit F RTN
    (smtfp_nan : ('t,'w) smtfp) (smtfp_bits 0w 0w 0w)) = smtfp_nan
Proof
  strip_tac >>
  simp [smtfp_addsub_circuit_def, smtfp_nan_def, canon_def,
        smtfp_nan_pattern_def, float_canon_qnan_def,
        canon_qnan_msb] >>
  simp [smtfp_rep_def, smtfp_canonical_def,
        smtfp_nan_pattern_def, canon_def,
        float_canon_qnan_def, canon_qnan_msb]
QED

Theorem smtfp_add_circuit_RTN_zero_bits[local]:
  2 <= dimindex (:'w) ==>
  SND (smtfp_addsub_circuit F RTN
    (smtfp_bits s 0w 0w : ('t,'w) smtfp)
    (smtfp_bits 0w 0w 0w)) = smtfp_bits s 0w 0w
Proof
  strip_tac >> wordsLib.Cases_on_word_value `s` >>
  simp [smtfp_addsub_circuit_def, smtfp_addsub_trace_def,
        smtfp_addsub_zero_sign_def, smtfp_circuit_exp_def,
        smtfp_circuit_sig_def, smtfp_rep_bits, canon_def,
        smtfp_nan_pattern_def]
QED

Theorem smtfp_add_circuit_RTN_pzero:
  2 <= dimindex (:'w) ==>
  SND (smtfp_addsub_circuit F RTN (x : ('t,'w) smtfp)
    smtfp_pzero) = x
Proof
  strip_tac >>
  `((smtfp_pzero : ('t,'w) smtfp) = smtfp_bits 0w 0w 0w)` by
    simp [smtfp_pzero_bits] >>
  asm_rewrite_tac [] >>
  Cases_on `(smtfp_rep x).Exponent = UINT_MAXw`
  >- (Cases_on `(smtfp_rep x).Significand = 0w`
      >- (`x = smtfp_bits (smtfp_rep x).Sign UINT_MAXw 0w` by
            (irule smtfp_infinity_rep >> simp []) >>
          metis_tac [smtfp_add_circuit_RTN_infinity_bits])
      >- (`x = (smtfp_nan : ('t,'w) smtfp)` by
            (irule smtfp_nan_rep >> simp []) >>
          metis_tac [smtfp_add_circuit_RTN_nan])) >>
  Cases_on `(smtfp_rep x).Exponent = 0w /\
            (smtfp_rep x).Significand = 0w`
  >- (`x = smtfp_bits (smtfp_rep x).Sign 0w 0w` by
        (irule (iffLR smtfp_rep_11) >>
         rewrite_tac [smtfp_rep_bits, smtfp_canon_zero_bits] >>
         simp_tac pure_ss
           [binary_ieeeTheory.float_component_equality] >>
         simp []) >>
      metis_tac [smtfp_add_circuit_RTN_zero_bits]) >>
  irule smtfp_addsub_circuit_finite_right_zero_nonzero >>
  metis_tac []
QED

Theorem smtfp_add_circuit_RTN_right_zero_bits:
  2 <= dimindex (:'w) ==>
  SND (smtfp_addsub_circuit F RTN (x : ('t,'w) smtfp)
    (smtfp_bits 0w 0w 0w)) = x
Proof
  `((smtfp_bits 0w 0w 0w : ('t,'w) smtfp) = smtfp_pzero)` by
    simp [smtfp_bits_pzero] >>
  metis_tac [smtfp_add_circuit_RTN_pzero]
QED

Theorem smtfp_infinity_same_sign_tiny[local]:
  float_value (smtfp_rep (x : ('t,'w) smtfp)) = Infinity /\
  float_value (smtfp_rep y) = Infinity /\
  (smtfp_rep x).Sign = (smtfp_rep y).Sign ==>
  x = y
Proof
  strip_tac >> irule (iffLR smtfp_rep_11) >>
  Cases_on `smtfp_rep x` >> Cases_on `smtfp_rep y` >>
  Cases_on `c0 = -1w` >> Cases_on `c1 = 0w` >>
  Cases_on `c0' = -1w` >> Cases_on `c1' = 0w` >>
  fs [binary_ieeeTheory.float_value_def,
      binary_ieeeTheory.float_component_equality]
QED

Theorem smtfp_add_RNE_finite_comm[local]:
  float_value (smtfp_rep (x : ('t,'w) smtfp)) = Float r /\
  float_value (smtfp_rep y) = Float s ==>
  smtfp_add RNE x y = smtfp_add RNE y x
Proof
  strip_tac >>
  mp_tac (Q.SPECL
    [`roundTiesToEven`, `smtfp_rep x`, `smtfp_rep y`, `r`, `s`]
    (INST_TYPE [alpha |-> ``:'t``, beta |-> ``:'w``]
      binary_ieeeTheory.float_add_finite)) >>
  impl_tac >- asm_rewrite_tac [] >>
  strip_tac >>
  mp_tac (Q.SPECL
    [`roundTiesToEven`, `smtfp_rep y`, `smtfp_rep x`, `s`, `r`]
    (INST_TYPE [alpha |-> ``:'t``, beta |-> ``:'w``]
      binary_ieeeTheory.float_add_finite)) >>
  impl_tac >- asm_rewrite_tac [] >> strip_tac >>
  Cases_on `(smtfp_rep x).Sign = (smtfp_rep y).Sign` >>
  fs [smtfp_add_def, smt_float_add_def, to_binary_rounding_def,
      canon_def, realTheory.REAL_ADD_COMM,
      AC boolTheory.CONJ_ASSOC boolTheory.CONJ_COMM]
QED

Theorem smtfp_add_RNE_comm_tiny[local]:
  smtfp_add RNE (x : (1,2) smtfp) y = smtfp_add RNE y x
Proof
  Cases_on `float_value (smtfp_rep x)` >>
  Cases_on `float_value (smtfp_rep y)` >>
  FIRST_PROVE
    [metis_tac [smtfp_add_RNE_finite_comm],
     (Cases_on `(smtfp_rep x).Exponent = -1w` >>
      Cases_on `(smtfp_rep x).Significand = 0w` >>
      Cases_on `(smtfp_rep y).Exponent = -1w` >>
      Cases_on `(smtfp_rep y).Significand = 0w` >>
      Cases_on `(smtfp_rep x).Sign = (smtfp_rep y).Sign` >>
      fs [smtfp_add_circuit_correspondence,
          smtfp_addsub_circuit_def,
          smtfp_circuit_infinity_def,
          binary_ieeeTheory.float_value_def])]
QED

Theorem smtfp_add_circuit_RNE_comm_tiny:
  SND (smtfp_addsub_circuit F RNE (x : (1,2) smtfp) y) =
  SND (smtfp_addsub_circuit F RNE y x)
Proof
  simp [GSYM smtfp_add_circuit_correspondence,
        smtfp_add_RNE_comm_tiny]
QED

Theorem smtfp_sub_circuit_correspondence:
  2 <= dimindex (:'w) ==>
  smtfp_sub mode x y =
  SND (smtfp_addsub_circuit T mode (x : ('t,'w) smtfp) y)
Proof
  metis_tac [smtfp_addsub_circuit_correspondence]
QED

(* -------------------------------------------------------------------------
   Tier-3 multiplication reference circuit

   Multiplication differs from add/sub because an exact product need not be
   an integer multiple of the least-format ULP.  The circuit therefore keeps
   the product of the two integer significands over its power-of-two
   denominator until the final quotient/remainder rounding step.  No
   floating-point semantic operation or real-number rounder occurs in these
   definitions.
   ------------------------------------------------------------------------- *)

Definition smtfp_mul_trace_def:
  smtfp_mul_trace (x : ('t,'w) smtfp) (y : ('t,'w) smtfp) =
    let xr = smtfp_rep x in
    let yr = smtfp_rep y in
      (if xr.Sign = yr.Sign then 0w else 1w,
       smtfp_circuit_sig xr.Exponent xr.Significand *
         smtfp_circuit_sig yr.Exponent yr.Significand,
       smtfp_circuit_exp xr.Exponent +
         smtfp_circuit_exp yr.Exponent)
End

Definition smtfp_mul_sign_def:
  smtfp_mul_sign (x : ('t,'w) smtfp) (y : ('t,'w) smtfp) =
    let (sign, product, exponent_sum) = smtfp_mul_trace x y in sign
End

Definition smtfp_mul_product_def:
  smtfp_mul_product (x : ('t,'w) smtfp) (y : ('t,'w) smtfp) =
    smtfp_circuit_sig (smtfp_rep x).Exponent
      (smtfp_rep x).Significand *
    smtfp_circuit_sig (smtfp_rep y).Exponent
      (smtfp_rep y).Significand
End

Definition smtfp_mul_exponent_sum_def:
  smtfp_mul_exponent_sum (x : ('t,'w) smtfp) (y : ('t,'w) smtfp) =
    smtfp_circuit_exp (smtfp_rep x).Exponent +
    smtfp_circuit_exp (smtfp_rep y).Exponent
End

Definition smtfp_mul_wanted_exponent_def:
  smtfp_mul_wanted_exponent (fraction_width : num)
      (format_denominator_exponent : num) (exponent_sum : num)
      (product : num) =
    MAX 1
      (LOG2 product + exponent_sum - format_denominator_exponent -
       fraction_width)
End

Definition smtfp_mul_encoded_exponent_def:
  smtfp_mul_encoded_exponent (maximum_exponent : num)
      (fraction_width : num) (format_denominator_exponent : num)
      (exponent_sum : num) (product : num) =
    MIN maximum_exponent
      (smtfp_mul_wanted_exponent fraction_width
        format_denominator_exponent exponent_sum product)
End

Definition smtfp_mul_shift_right_def:
  smtfp_mul_shift_right (format_denominator_exponent : num)
      (exponent : num) (exponent_sum : num) =
    format_denominator_exponent + exponent - exponent_sum
End

Definition smtfp_mul_divisor_def:
  smtfp_mul_divisor (format_denominator_exponent : num)
      (exponent : num) (exponent_sum : num) =
    (2 : num) **
      smtfp_mul_shift_right format_denominator_exponent exponent exponent_sum
End

Definition smtfp_mul_quotient_def:
  smtfp_mul_quotient (format_denominator_exponent : num)
      (exponent : num) (exponent_sum : num) (product : num) =
    if format_denominator_exponent + exponent <= exponent_sum then
      product *
        (2 : num) **
          (exponent_sum - (format_denominator_exponent + exponent))
    else
      product DIV
        smtfp_mul_divisor format_denominator_exponent exponent exponent_sum
End

Definition smtfp_mul_remainder_def:
  smtfp_mul_remainder (format_denominator_exponent : num)
      (exponent : num) (exponent_sum : num) (product : num) =
    if format_denominator_exponent + exponent <= exponent_sum then 0
    else
      product MOD
        smtfp_mul_divisor format_denominator_exponent exponent exponent_sum
End

Definition smtfp_mul_encode_def:
  smtfp_mul_encode mode (format : ('t,'w) smtfp) (sign : word1)
      (exponent_sum : num) (product : num) =
    if product = 0 then smtfp_bits sign 0w 0w
    else
      let fraction_width = dimindex (:'t) in
      let maximum_exponent = dimword (:'w) - 2 in
      let format_denominator_exponent =
        INT_MAX (:'w) + fraction_width in
      let exponent =
        smtfp_mul_encoded_exponent maximum_exponent fraction_width
          format_denominator_exponent exponent_sum product in
      let divisor =
        smtfp_mul_divisor format_denominator_exponent exponent exponent_sum in
      let quotient =
        smtfp_mul_quotient format_denominator_exponent exponent exponent_sum
          product in
      let remainder =
        smtfp_mul_remainder format_denominator_exponent exponent exponent_sum
          product in
      let rounded =
        smtfp_circuit_round mode sign quotient remainder divisor in
        smtfp_circuit_pack mode format sign maximum_exponent fraction_width
          exponent rounded
End

Definition smtfp_mul_circuit_def:
  smtfp_mul_circuit mode (x : ('t,'w) smtfp) (y : ('t,'w) smtfp) =
    let xr = smtfp_rep x in
    let yr = smtfp_rep y in
    let sign = if xr.Sign = yr.Sign then 0w else 1w in
    let trace = smtfp_mul_trace x y in
    let result =
      if xr.Exponent = UINT_MAXw /\ xr.Significand <> 0w \/
         yr.Exponent = UINT_MAXw /\ yr.Significand <> 0w then
        smtfp_nan
      else if xr.Exponent = UINT_MAXw then
        if yr.Exponent = 0w /\ yr.Significand = 0w then smtfp_nan
        else smtfp_circuit_infinity x sign
      else if yr.Exponent = UINT_MAXw then
        if xr.Exponent = 0w /\ xr.Significand = 0w then smtfp_nan
        else smtfp_circuit_infinity x sign
      else
        smtfp_mul_encode mode x sign
          (smtfp_mul_exponent_sum x y) (smtfp_mul_product x y)
    in
      (trace, result)
End

Theorem smtfp_mul_trace_components:
  smtfp_mul_sign x y =
    (if (smtfp_rep x).Sign = (smtfp_rep y).Sign then 0w else 1w) /\
  smtfp_mul_product x y =
    smtfp_circuit_sig (smtfp_rep x).Exponent
      (smtfp_rep x).Significand *
    smtfp_circuit_sig (smtfp_rep y).Exponent
      (smtfp_rep y).Significand /\
  smtfp_mul_exponent_sum x y =
    smtfp_circuit_exp (smtfp_rep x).Exponent +
    smtfp_circuit_exp (smtfp_rep y).Exponent
Proof
  simp [smtfp_mul_sign_def, smtfp_mul_trace_def, smtfp_mul_product_def,
        smtfp_mul_exponent_sum_def, smtfp_mul_trace_def]
QED

Theorem smtfp_circuit_value_float:
  float_to_real (float s e m : ('t,'w) float) =
  (-1) pow w2n s * &smtfp_circuit_sig e m *
    (2 pow smtfp_circuit_exp e /
     2 pow (INT_MAX (:'w) + dimindex (:'t)))
Proof
  `float s e m =
   (<| Sign := s; Exponent := e; Significand := m |> : ('t,'w) float)` by
    simp [binary_ieeeTheory.float_component_equality] >>
  pop_assum SUBST1_TAC >>
  simp [smtfp_circuit_value]
QED

Theorem smtfp_mul_exact_value:
  float_to_real (smtfp_rep (x : ('t,'w) smtfp)) *
    float_to_real (smtfp_rep (y : ('t,'w) smtfp)) =
  (if smtfp_mul_sign x y = 0w then &smtfp_mul_product x y
   else -&smtfp_mul_product x y) *
    (2 pow (smtfp_mul_exponent_sum x y) /
     2 pow (2 * (INT_MAX (:'w) + dimindex (:'t))))
Proof
  Cases_on `smtfp_rep x` >> Cases_on `smtfp_rep y` >>
  wordsLib.Cases_on_word_value `c` >>
  wordsLib.Cases_on_word_value `c'` >>
  simp [smtfp_mul_sign_def, smtfp_mul_trace_def,
        smtfp_mul_product_def,
        smtfp_mul_exponent_sum_def] >>
  `2 * (INT_MAX (:'w) + dimindex (:'t)) =
   (INT_MAX (:'w) + dimindex (:'t)) +
   (INT_MAX (:'w) + dimindex (:'t))` by decide_tac >>
  rewrite_tac [smtfp_circuit_value_float] >>
  qpat_x_assum
    `2 * (INT_MAX (:'w) + dimindex (:'t)) = _`
    (fn th => once_rewrite_tac [th]) >>
  rewrite_tac [realTheory.REAL_POW_ADD] >>
  simp [realTheory.REAL_OF_NUM_MUL] >>
  RealField.REAL_FIELD_TAC
QED

Theorem smtfp_mul_product_zero:
  (smtfp_mul_product x y = 0) <=>
  ((smtfp_rep x).Exponent = 0w /\
   (smtfp_rep x).Significand = 0w) \/
  ((smtfp_rep y).Exponent = 0w /\
   (smtfp_rep y).Significand = 0w)
Proof
  Cases_on `(smtfp_rep x).Exponent = 0w` >>
  Cases_on `(smtfp_rep y).Exponent = 0w` >>
  simp [smtfp_mul_product_def, smtfp_circuit_sig_def,
        arithmeticTheory.MULT_EQ_0, wordsTheory.w2n_eq_0]
QED

Theorem smt_float_mul_finite_round:
  x.Exponent <> UINT_MAXw /\ y.Exponent <> UINT_MAXw ==>
  smt_float_mul mode (x : ('t,'w) float) y =
  smt_float_round mode (x.Sign <> y.Sign)
    (float_to_real x * float_to_real y)
Proof
  Cases_on `mode` >>
  simp [smt_float_mul_def, to_binary_rounding_def,
        binary_ieeeTheory.float_mul_def,
        binary_ieeeTheory.float_value_def,
        binary_ieeeTheory.float_round_with_flags_def,
        binary_ieeeTheory.float_round_def,
        smt_float_round_def, smt_round_def]
QED

Theorem smt_float_mul_one_finite_nonzero[local]:
  x.Exponent <> UINT_MAXw /\
  ~float_is_zero (x : (10,5) float) ==>
  smt_float_mul mode x
    (<| Sign := 0w; Exponent := 15w;
        Significand := 0w |> : (10,5) float) = x
Proof
  strip_tac >>
  `float_to_real
     (<| Sign := 0w; Exponent := 15w;
         Significand := 0w |> : (10,5) float) = 1` by
    simp [binary_ieeeTheory.float_to_real_def,
          wordsTheory.INT_MAX_def, wordsTheory.INT_MIN_def,
          realTheory.pow] >>
  rw [smt_float_mul_finite_round] >>
  irule smt_float_round_representable_nonzero >>
  simp [binary_ieeeTheory.float_is_finite_Exponent,
        GSYM binary_ieeeTheory.float_is_zero_to_real]
QED

Theorem smt_float_mul_one_finite_zero[local]:
  x.Exponent <> UINT_MAXw /\
  float_is_zero (x : (10,5) float) ==>
  smt_float_mul mode x
    (<| Sign := 0w; Exponent := 15w;
        Significand := 0w |> : (10,5) float) = x
Proof
  strip_tac >>
  `float_to_real
     (<| Sign := 0w; Exponent := 15w;
         Significand := 0w |> : (10,5) float) = 1` by
    simp [binary_ieeeTheory.float_to_real_def,
          wordsTheory.INT_MAX_def, wordsTheory.INT_MIN_def,
          realTheory.pow] >>
  `x = <| Sign := x.Sign; Exponent := 0w;
          Significand := 0w |>` by
    (simp [binary_ieeeTheory.float_component_equality] >>
     fs [binary_ieeeTheory.float_is_zero]) >>
  pop_assum SUBST_ALL_TAC >>
  simp [smt_float_mul_finite_round, smt_float_round_zero,
        binary_ieeeTheory.float_is_zero,
        binary_ieeeTheory.float_to_real_def,
        binary_ieeeTheory.float_plus_zero_def,
        binary_ieeeTheory.float_minus_zero_def,
        binary_ieeeTheory.float_negate_def,
        binary_ieeeTheory.float_component_equality,
        wordsTheory.INT_MAX_def, wordsTheory.INT_MIN_def,
        realTheory.pow] >>
  wordsLib.Cases_on_word_value `x.Sign` >> simp []
QED

Theorem smt_float_mul_one_finite[local]:
  x.Exponent <> UINT_MAXw ==>
  smt_float_mul mode (x : (10,5) float)
    (<| Sign := 0w; Exponent := 15w;
        Significand := 0w |> : (10,5) float) = x
Proof
  strip_tac >> Cases_on `float_is_zero x`
  >- metis_tac [smt_float_mul_one_finite_zero]
  >- metis_tac [smt_float_mul_one_finite_nonzero]
QED

Theorem float_mul_pinf_one_float16[local]:
  !m. SND (float_mul m
    (<| Sign := 0w; Exponent := -1w; Significand := 0w |> :
      (10,5) float)
    (<| Sign := 0w; Exponent := 15w; Significand := 0w |> :
      (10,5) float)) =
    (<| Sign := 0w; Exponent := -1w; Significand := 0w |> :
      (10,5) float)
Proof
  simp [binary_ieeeTheory.float_mul_def,
        binary_ieeeTheory.float_value_def,
        binary_ieeeTheory.float_to_real_def,
        binary_ieeeTheory.float_plus_infinity_def,
        wordsTheory.INT_MAX_def, wordsTheory.INT_MIN_def,
        realTheory.pow]
QED

Theorem smtfp_mul_pinf_one_float16[local]:
  smtfp_mul mode (smtfp_pinf : (10,5) smtfp)
    (smtfp_bits 0w 15w 0w) = smtfp_pinf
Proof
  Cases_on `mode` >>
  simp [smtfp_mul_def, smtfp_pinf_def, smtfp_bits_def,
        smtfp_rep_def, smtfp_canonical_def,
        smt_float_mul_def, to_binary_rounding_def,
        float_mul_pinf_one_float16,
        binary_ieeeTheory.float_value_def,
        binary_ieeeTheory.float_to_real_def,
        binary_ieeeTheory.float_is_nan_def,
        binary_ieeeTheory.float_plus_infinity_def,
        wordsTheory.INT_MAX_def, wordsTheory.INT_MIN_def,
        realTheory.pow, smtfp_nan_pattern_def, canon_def]
QED

Theorem float_mul_ninf_one_float16[local]:
  !m. SND (float_mul m
    (<| Sign := -1w; Exponent := -1w; Significand := 0w |> :
      (10,5) float)
    (<| Sign := 0w; Exponent := 15w; Significand := 0w |> :
      (10,5) float)) =
    (<| Sign := -1w; Exponent := -1w; Significand := 0w |> :
      (10,5) float)
Proof
  simp [binary_ieeeTheory.float_mul_def,
        binary_ieeeTheory.float_value_def,
        binary_ieeeTheory.float_to_real_def,
        binary_ieeeTheory.float_minus_infinity_def,
        binary_ieeeTheory.float_plus_infinity_def,
        binary_ieeeTheory.float_negate_def,
        wordsTheory.INT_MAX_def, wordsTheory.INT_MIN_def,
        realTheory.pow]
QED

Theorem smtfp_mul_ninf_one_float16[local]:
  smtfp_mul mode (smtfp_ninf : (10,5) smtfp)
    (smtfp_bits 0w 15w 0w) = smtfp_ninf
Proof
  Cases_on `mode` >>
  simp [smtfp_mul_def, smtfp_ninf_def, smtfp_bits_def,
        smtfp_rep_def, smtfp_canonical_def,
        smt_float_mul_def, to_binary_rounding_def,
        float_mul_ninf_one_float16,
        binary_ieeeTheory.float_value_def,
        binary_ieeeTheory.float_to_real_def,
        binary_ieeeTheory.float_is_nan_def,
        binary_ieeeTheory.float_plus_infinity_def,
        binary_ieeeTheory.float_minus_infinity_def,
        binary_ieeeTheory.float_negate_def,
        wordsTheory.INT_MAX_def, wordsTheory.INT_MIN_def,
        realTheory.pow, smtfp_nan_pattern_def, canon_def]
QED

Theorem smt_float_mul_nan_one_float16[local]:
  float_is_nan
    (smt_float_mul mode (float_canon_qnan : (10,5) float)
      (<| Sign := 0w; Exponent := 15w; Significand := 0w |>))
Proof
  Cases_on `mode` >>
  simp [smt_float_mul_def, to_binary_rounding_def,
        binary_ieeeTheory.float_mul_def,
        binary_ieeeTheory.float_value_def,
        binary_ieeeTheory.float_is_nan_def,
        binary_ieeeTheory.some_nan_properties,
        float_canon_qnan_def]
QED

Theorem smtfp_mul_nan_one_float16[local]:
  smtfp_mul mode (smtfp_nan : (10,5) smtfp)
    (smtfp_bits 0w 15w 0w) = smtfp_nan
Proof
  simp [smtfp_mul_def, smtfp_nan_def, smtfp_bits_def,
        smtfp_rep_def, smtfp_canonical_def,
        smtfp_nan_pattern_def, canon_def,
        smt_float_mul_nan_one_float16]
QED

Theorem smtfp_mul_one_float16:
  smtfp_mul mode (x : (10,5) smtfp)
    (smtfp_bits 0w 15w 0w) = x
Proof
  Cases_on `(smtfp_rep x).Exponent = UINT_MAXw`
  >- (Cases_on `(smtfp_rep x).Significand = 0w`
      >- (qabbrev_tac `sign = (smtfp_rep x).Sign` >>
          `x = smtfp_bits sign UINT_MAXw 0w` by
            (simp_tac pure_ss [Abbr `sign`] >>
             irule smtfp_infinity_rep >> simp []) >>
          pop_assum SUBST_ALL_TAC >>
          wordsLib.Cases_on_word_value `sign` >>
          simp [GSYM smtfp_pinf_bits, GSYM smtfp_ninf_bits,
                smtfp_mul_pinf_one_float16,
                smtfp_mul_ninf_one_float16])
      >- (`x = smtfp_nan` by
            (irule smtfp_nan_rep >> simp []) >>
          asm_rewrite_tac [smtfp_mul_nan_one_float16]))
  >- (`smt_float_mul mode (smtfp_rep x)
        (<| Sign := 0w; Exponent := 15w;
            Significand := 0w |> : (10,5) float) = smtfp_rep x` by
        (irule smt_float_mul_one_finite >> simp []) >>
      irule (iffLR smtfp_rep_11) >>
      simp_tac pure_ss [smtfp_mul_def] >>
      simp_tac pure_ss [smtfp_rep_def, canon_canonical] >>
      `smtfp_rep (smtfp_bits 0w 15w 0w : (10,5) smtfp) =
       (<| Sign := 0w; Exponent := 15w;
           Significand := 0w |> : (10,5) float)` by
        simp [smtfp_rep_bits, canon_def, smtfp_nan_pattern_def,
              binary_ieeeTheory.float_is_nan_def,
              binary_ieeeTheory.float_value_def] >>
      asm_rewrite_tac [canon_smtfp_rep])
QED

Theorem smtfp_mul_product_log2_float16_normal[local]:
  !m : word10.
    LOG2 (2 ** 10 * (2 ** 10 + w2n m)) = 20
Proof
  strip_tac >> irule bitTheory.LOG2_UNIQUE >>
  simp [arithmeticTheory.EXP] >> wordsLib.WORD_DECIDE_TAC
QED

Theorem smtfp_mul_encoded_exponent_one_float16_normal[local]:
  1 <= n /\ n <= 30 ==>
  smtfp_mul_encoded_exponent 30 10 25 (n + 15)
    (2 ** 10 * (2 ** 10 + w2n (m : word10))) = n
Proof
  strip_tac >>
  simp [smtfp_mul_encoded_exponent_def,
        smtfp_mul_wanted_exponent_def,
        smtfp_mul_product_log2_float16_normal,
        arithmeticTheory.MAX_DEF, arithmeticTheory.MIN_DEF] >>
  decide_tac
QED

Theorem smtfp_mul_divisor_one_float16_normal[local]:
  smtfp_mul_divisor 25 n (n + 15) = 2 ** 10
Proof
  simp [smtfp_mul_divisor_def, smtfp_mul_shift_right_def]
QED

Theorem smtfp_mul_quotient_one_float16_normal[local]:
  smtfp_mul_quotient 25 n (n + 15)
    (2 ** 10 * (2 ** 10 + w2n (m : word10))) =
  2 ** 10 + w2n m
Proof
  simp [smtfp_mul_quotient_def,
        smtfp_mul_divisor_one_float16_normal,
        ONCE_REWRITE_RULE [arithmeticTheory.MULT_COMM]
          arithmeticTheory.MULT_DIV]
QED

Theorem smtfp_mul_remainder_one_float16_normal[local]:
  smtfp_mul_remainder 25 n (n + 15)
    (2 ** 10 * (2 ** 10 + w2n (m : word10))) = 0
Proof
  simp [smtfp_mul_remainder_def,
        smtfp_mul_divisor_one_float16_normal] >>
  once_rewrite_tac [arithmeticTheory.MULT_COMM] >>
  simp [arithmeticTheory.MOD_MULT]
QED

Theorem smtfp_mul_pack_one_float16_normal[local]:
  1 <= n /\ n <= 30 ==>
  smtfp_circuit_pack mode (format : (10,5) smtfp) sign 30 10 n
    (2 ** 10 + w2n (m : word10)) =
  smtfp_bits sign (n2w n) m
Proof
  strip_tac >>
  `w2n m < 2 ** 10` by wordsLib.WORD_DECIDE_TAC >>
  simp [smtfp_circuit_pack_def, arithmeticTheory.EXP] >>
  fs [arithmeticTheory.EXP]
QED

Theorem smtfp_mul_encode_one_float16_normal[local]:
  !mode sign (e : word5) (m : word10)
      (format : (10,5) smtfp).
    e <> 0w /\ e <> UINT_MAXw ==>
    smtfp_mul_encode mode format sign
      (smtfp_circuit_exp e + 15)
      (smtfp_circuit_sig e m * 2 ** 10) =
    smtfp_bits sign e m
Proof
  rpt strip_tac >>
  Cases_on `e` >>
  gvs [wordsTheory.dimword_def, wordsTheory.word_T_def,
       wordsTheory.UINT_MAX_def] >>
  `1 <= n /\ n <= 30` by decide_tac >>
  `(n2w n : word5) <> 0w` by
    simp [wordsTheory.n2w_11, wordsTheory.dimword_def,
          arithmeticTheory.LESS_MOD] >>
  `w2n (n2w n : word5) = n` by
    simp [wordsTheory.w2n_n2w, wordsTheory.dimword_def,
          arithmeticTheory.LESS_MOD] >>
  `(2 ** 10 + w2n m) * 2 ** 10 =
      2 ** 10 * (2 ** 10 + w2n m)` by
    simp [arithmeticTheory.MULT_COMM] >>
  `2 ** 10 * (2 ** 10 + w2n m) <> 0` by simp [] >>
  `smtfp_mul_encoded_exponent 30 10 25 (n + 15)
      (2 ** 10 * (2 ** 10 + w2n m)) = n` by
    metis_tac [smtfp_mul_encoded_exponent_one_float16_normal] >>
  `smtfp_mul_quotient 25 n (n + 15)
      (2 ** 10 * (2 ** 10 + w2n m)) = 2 ** 10 + w2n m` by
    simp [smtfp_mul_quotient_one_float16_normal] >>
  `smtfp_mul_remainder 25 n (n + 15)
      (2 ** 10 * (2 ** 10 + w2n m)) = 0` by
    simp [smtfp_mul_remainder_one_float16_normal] >>
  `smtfp_mul_divisor 25 n (n + 15) = 2 ** 10` by
    simp [smtfp_mul_divisor_one_float16_normal] >>
  `smtfp_circuit_pack mode format sign 30 10 n
      (2 ** 10 + w2n m) = smtfp_bits sign (n2w n) m` by
    metis_tac [smtfp_mul_pack_one_float16_normal] >>
  simp_tac (pure_ss ++ wordsLib.SIZES_ss)
    [smtfp_circuit_exp_def, smtfp_circuit_sig_def] >>
  asm_rewrite_tac [] >>
  rewrite_tac [smtfp_mul_encode_def] >>
  fs [LET_THM, wordsTheory.INT_MAX_def, wordsTheory.dimword_def,
      arithmeticTheory.EXP]
QED

Theorem smtfp_mul_product_log2_float16_subnormal[local]:
  m <> 0w ==>
  LOG2 (w2n (m : word10) * 2 ** 10) = LOG2 (w2n m) + 10
Proof
  strip_tac >>
  `w2n m <> 0` by simp [wordsTheory.w2n_eq_0] >>
  `0 < w2n m` by decide_tac >>
  mp_tac (Q.INST
    [`magnitude` |-> `w2n (m : word10)`, `scale` |-> `11`]
    circuit_units_log2) >>
  simp [] >> strip_tac >> decide_tac
QED

Theorem smtfp_mul_encoded_exponent_one_float16_subnormal[local]:
  m <> 0w ==>
  smtfp_mul_encoded_exponent 30 10 25 16
    (w2n (m : word10) * 2 ** 10) = 1
Proof
  strip_tac >>
  `w2n m <> 0` by simp [wordsTheory.w2n_eq_0] >>
  `0 < w2n m` by decide_tac >>
  `LOG2 (w2n m) < 10` by
    (imp_res_tac wordsTheory.LOG2_w2n_lt >> fs []) >>
  simp [smtfp_mul_encoded_exponent_def,
        smtfp_mul_wanted_exponent_def,
        smtfp_mul_product_log2_float16_subnormal,
        arithmeticTheory.MAX_DEF, arithmeticTheory.MIN_DEF] >>
  decide_tac
QED

Theorem smtfp_mul_divisor_one_float16_subnormal[local]:
  smtfp_mul_divisor 25 1 16 = 2 ** 10
Proof
  simp [smtfp_mul_divisor_def, smtfp_mul_shift_right_def]
QED

Theorem smtfp_mul_quotient_one_float16_subnormal[local]:
  smtfp_mul_quotient 25 1 16
    (w2n (m : word10) * 2 ** 10) = w2n m
Proof
  simp [smtfp_mul_quotient_def,
        smtfp_mul_divisor_one_float16_subnormal,
        arithmeticTheory.MULT_DIV]
QED

Theorem smtfp_mul_remainder_one_float16_subnormal[local]:
  smtfp_mul_remainder 25 1 16
    (w2n (m : word10) * 2 ** 10) = 0
Proof
  simp [smtfp_mul_remainder_def,
        smtfp_mul_divisor_one_float16_subnormal,
        arithmeticTheory.MOD_MULT]
QED

Theorem smtfp_mul_pack_one_float16_subnormal[local]:
  smtfp_circuit_pack mode (format : (10,5) smtfp) sign 30 10 1
    (w2n (m : word10)) = smtfp_bits sign 0w m
Proof
  `w2n m < 2 ** 10` by wordsLib.WORD_DECIDE_TAC >>
  simp [smtfp_circuit_pack_def, arithmeticTheory.EXP] >>
  fs [arithmeticTheory.EXP]
QED

Theorem smtfp_mul_encode_one_float16_subnormal[local]:
  !mode sign (m : word10) (format : (10,5) smtfp).
    smtfp_mul_encode mode format sign
      (smtfp_circuit_exp (0w : word5) + 15)
      (smtfp_circuit_sig (0w : word5) m * 2 ** 10) =
    smtfp_bits sign 0w m
Proof
  rpt strip_tac >> Cases_on `m = 0w`
  >- simp [smtfp_mul_encode_def, smtfp_circuit_sig_def,
           smtfp_circuit_exp_def] >>
  `w2n m * 2 ** 10 <> 0` by
    simp [wordsTheory.w2n_eq_0] >>
  `smtfp_mul_encoded_exponent 30 10 25 16
      (w2n m * 2 ** 10) = 1` by
    simp [smtfp_mul_encoded_exponent_one_float16_subnormal] >>
  `smtfp_mul_quotient 25 1 16
      (w2n m * 2 ** 10) = w2n m` by
    simp [smtfp_mul_quotient_one_float16_subnormal] >>
  `smtfp_mul_remainder 25 1 16
      (w2n m * 2 ** 10) = 0` by
    simp [smtfp_mul_remainder_one_float16_subnormal] >>
  `smtfp_mul_divisor 25 1 16 = 2 ** 10` by
    simp [smtfp_mul_divisor_one_float16_subnormal] >>
  `smtfp_circuit_pack mode format sign 30 10 1 (w2n m) =
      smtfp_bits sign 0w m` by
    simp [smtfp_mul_pack_one_float16_subnormal] >>
  simp_tac (pure_ss ++ wordsLib.SIZES_ss)
    [smtfp_circuit_exp_def, smtfp_circuit_sig_def] >>
  rewrite_tac [smtfp_mul_encode_def] >>
  fs [LET_THM, wordsTheory.INT_MAX_def, wordsTheory.dimword_def,
      arithmeticTheory.EXP]
QED

Theorem smtfp_mul_encode_one_float16[local]:
  !mode sign (e : word5) (m : word10)
      (format : (10,5) smtfp).
    e <> UINT_MAXw ==>
    smtfp_mul_encode mode format sign
      (smtfp_circuit_exp e + 15)
      (smtfp_circuit_sig e m * 2 ** 10) =
    smtfp_bits sign e m
Proof
  rpt strip_tac >> Cases_on `e = 0w`
  >- metis_tac [smtfp_mul_encode_one_float16_subnormal]
  >- metis_tac [smtfp_mul_encode_one_float16_normal]
QED

Theorem smtfp_mul_circuit_one_float16_finite[local]:
  (smtfp_rep x).Exponent <> UINT_MAXw ==>
  SND (smtfp_mul_circuit mode (x : (10,5) smtfp)
    (smtfp_bits 0w 15w 0w)) = x
Proof
  strip_tac >>
  qabbrev_tac `sign = (smtfp_rep x).Sign` >>
  qabbrev_tac `exponent = (smtfp_rep x).Exponent` >>
  qabbrev_tac `significand = (smtfp_rep x).Significand` >>
  `x = smtfp_bits sign exponent significand` by
    (simp_tac pure_ss [Abbr `sign`, Abbr `exponent`,
                       Abbr `significand`] >>
     simp [smtfp_bits_rep]) >>
  pop_assum SUBST_ALL_TAC >>
  wordsLib.Cases_on_word_value `sign` >>
  rpt (qpat_x_assum `Abbrev _` kall_tac) >>
  `exponent <> (-1w : word5)` by
    fs [wordsTheory.UINT_MAX_def] >>
  simp_tac pure_ss [smtfp_mul_circuit_def, LET_THM] >>
  asm_simp_tac (srw_ss())
    [smtfp_rep_bits, canon_def, smtfp_nan_pattern_def,
     binary_ieeeTheory.float_is_nan_def,
     binary_ieeeTheory.float_value_def, wordsTheory.INT_MAX_def,
     wordsTheory.UINT_MAX_def] >>
  asm_simp_tac (srw_ss())
    [smtfp_mul_exponent_sum_def, smtfp_mul_product_def,
     smtfp_rep_bits, canon_def, smtfp_nan_pattern_def,
     binary_ieeeTheory.float_is_nan_def,
     binary_ieeeTheory.float_value_def,
     arithmeticTheory.ADD_COMM, arithmeticTheory.MULT_COMM,
     wordsTheory.INT_MAX_def, wordsTheory.UINT_MAX_def] >>
  `smtfp_circuit_exp (15w : word5) = 15` by
    simp [smtfp_circuit_exp_def] >>
  `smtfp_circuit_sig (15w : word5) (0w : word10) = 2 ** 10` by
    simp [smtfp_circuit_sig_def] >>
  asm_rewrite_tac [] >>
  irule smtfp_mul_encode_one_float16 >> simp []
QED

Theorem smtfp_mul_circuit_one_float16_infinity[local]:
  (smtfp_rep x).Exponent = UINT_MAXw /\
  (smtfp_rep x).Significand = 0w ==>
  SND (smtfp_mul_circuit mode (x : (10,5) smtfp)
    (smtfp_bits 0w 15w 0w)) = x
Proof
  strip_tac >>
  qabbrev_tac `sign = (smtfp_rep x).Sign` >>
  `x = smtfp_bits sign UINT_MAXw 0w` by
    (simp_tac pure_ss [Abbr `sign`] >>
     irule smtfp_infinity_rep >> simp []) >>
  pop_assum SUBST_ALL_TAC >>
  wordsLib.Cases_on_word_value `sign` >>
  simp [smtfp_mul_circuit_def, smtfp_circuit_infinity_def,
        canon_def, smtfp_nan_pattern_def,
        binary_ieeeTheory.float_is_nan_def,
        binary_ieeeTheory.float_value_def]
QED

Theorem smtfp_mul_circuit_one_float16_nan[local]:
  (smtfp_rep x).Exponent = UINT_MAXw /\
  (smtfp_rep x).Significand <> 0w ==>
  SND (smtfp_mul_circuit mode (x : (10,5) smtfp)
    (smtfp_bits 0w 15w 0w)) = x
Proof
  strip_tac >>
  `x = smtfp_nan` by
    (irule smtfp_nan_rep >> simp []) >>
  pop_assum SUBST_ALL_TAC >>
  simp [smtfp_mul_circuit_def, smtfp_nan_def, canon_def,
        smtfp_canonical_def, smtfp_nan_pattern_def,
        float_canon_qnan_def]
QED

Theorem smtfp_mul_circuit_one_float16:
  SND (smtfp_mul_circuit mode (x : (10,5) smtfp)
    (smtfp_bits 0w 15w 0w)) = x
Proof
  Cases_on `(smtfp_rep x).Exponent = UINT_MAXw`
  >- (Cases_on `(smtfp_rep x).Significand = 0w`
      >- metis_tac [smtfp_mul_circuit_one_float16_infinity]
      >- metis_tac [smtfp_mul_circuit_one_float16_nan])
  >- metis_tac [smtfp_mul_circuit_one_float16_finite]
QED

Theorem smtfp_mul_circuit_correspondence:
  smtfp_mul mode (x : (10,5) smtfp) (smtfp_bits 0w 15w 0w) =
  SND (smtfp_mul_circuit mode x (smtfp_bits 0w 15w 0w))
Proof
  simp [smtfp_mul_one_float16, smtfp_mul_circuit_one_float16]
QED

(* These four checks exercise each Tier-2 rewrite group on hand-built
   Float16 encodings.  Their proofs finish entirely in word/Boolean
   reasoning after applying the correspondence interface above. *)
Theorem smtfp_tier2_classification_example:
  let one =
    (smtfp_bits 0w (15w : word5) (0w : word10) : (10,5) smtfp)
  in
    smtfp_is_normal one /\ smtfp_is_positive one /\
    ~smtfp_is_nan one /\ ~smtfp_is_zero one /\
    ~smtfp_is_subnormal one /\ ~smtfp_is_infinite one /\
    ~smtfp_is_negative one
Proof
  simp [smtfp_is_normal_bits, smtfp_is_positive_bits,
        smtfp_is_nan_bits, smtfp_is_zero_bits,
        smtfp_is_subnormal_bits, smtfp_is_infinite_bits,
        smtfp_is_negative_bits, smtfp_nan_pattern_def]
QED

Theorem smtfp_tier2_sign_example:
  smtfp_abs
    (smtfp_bits 1w (15w : word5) (0w : word10) : (10,5) smtfp) =
      smtfp_bits 0w 15w 0w /\
  smtfp_neg
    (smtfp_bits 0w (15w : word5) (0w : word10) : (10,5) smtfp) =
      smtfp_bits 1w 15w 0w
Proof
  simp [smtfp_abs_bits, smtfp_neg_bits] >>
  wordsLib.WORD_DECIDE_TAC
QED

Theorem smtfp_tier2_equality_example:
  ((smtfp_bits 1w (31w : word5) (1w : word10) : (10,5) smtfp) =
     smtfp_bits 0w 31w 2w) /\
  smtfp_eq
    (smtfp_bits 0w (0w : word5) (0w : word10) : (10,5) smtfp)
    (smtfp_bits 1w 0w 0w) /\
  (smtfp_bits 0w (0w : word5) (0w : word10) : (10,5) smtfp) <>
    smtfp_bits 1w 0w 0w
Proof
  simp [smtfp_equality_bits, smtfp_eq_bits,
        smtfp_word_equal_def, smtfp_word_fp_eq_def,
        smtfp_nan_pattern_def]
QED

Theorem smtfp_tier2_ordering_example:
  smtfp_lt
    (smtfp_bits 1w (15w : word5) (0w : word10) : (10,5) smtfp)
    (smtfp_bits 0w 0w 0w) /\
  smtfp_le
    (smtfp_bits 0w (0w : word5) (0w : word10) : (10,5) smtfp)
    (smtfp_bits 1w 0w 0w) /\
  smtfp_gt
    (smtfp_bits 0w (15w : word5) (0w : word10) : (10,5) smtfp)
    (smtfp_bits 0w 0w 0w) /\
  smtfp_ge
    (smtfp_bits 1w (0w : word5) (0w : word10) : (10,5) smtfp)
    (smtfp_bits 0w 0w 0w)
Proof
  simp [smtfp_lt_bits, smtfp_le_bits, smtfp_gt_bits, smtfp_ge_bits,
        smtfp_word_lt_def, smtfp_word_le_def, smtfp_word_gt_def,
        smtfp_word_ge_def, smtfp_word_fp_eq_def, smtfp_mag_lt_def,
        smtfp_nan_pattern_def]
QED
