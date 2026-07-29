(* Copyright (c) 2026 The HOL4 contributors. *)

(* The SMT-LIB significand width includes the hidden bit.  Thus the HOL
   instance corresponding to (_ FloatingPoint eb sb) is ('t,'w) float with
   dimindex(:'t) = sb - 1 and dimindex(:'w) = eb.  In particular, Float32
   is (23,8) float.  The definitions in this theory remain schematic in
   both widths. *)
Theory smtfloat
Ancestors[qualified]
  binary_ieee

Datatype:
  smt_rounding = RNE | RNA | RTP | RTN | RTZ
End

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
