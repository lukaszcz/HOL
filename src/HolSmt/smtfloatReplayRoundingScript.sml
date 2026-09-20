open HolKernel Parse boolLib bossLib;
open wordsTheory smtfloatTheory binary_ieeeTheory realTheory;

val _ = new_theory "smtfloatReplayRounding";

Theorem smtfp_rounding_onehot:
  !mode.
    (mode = RNE \/ mode = RNA \/ mode = RTP \/ mode = RTN \/
     mode = RTZ) /\
    ~(mode = RNE /\ mode = RNA) /\
    ~(mode = RNE /\ mode = RTP) /\
    ~(mode = RNE /\ mode = RTN) /\
    ~(mode = RNE /\ mode = RTZ) /\
    ~(mode = RNA /\ mode = RTP) /\
    ~(mode = RNA /\ mode = RTN) /\
    ~(mode = RNA /\ mode = RTZ) /\
    ~(mode = RTP /\ mode = RTN) /\
    ~(mode = RTP /\ mode = RTZ) /\
    ~(mode = RTN /\ mode = RTZ)
Proof
  Cases_on `mode` >> simp [smt_rounding_distinctness]
QED

Theorem smtfp_bit_add:
  !i left right.
    BIT i (left + right) =
    blast$BSUM i (\j. BIT j left) (\j. BIT j right) F
Proof
  simp [blastTheory.BSUM_LEM]
QED

Theorem smtfp_bit_mod_pow2:
  !i width value.
    i < width ==>
    (BIT i (value MOD 2 ** width) = BIT i value)
Proof
  Cases_on `width` >> simp [] >>
  simp [GSYM bitTheory.BITS_ZERO3,
        bitTheory.BIT_OF_BITS_THM]
QED

Definition smtfp_rounding_canonical_def:
  smtfp_rounding_canonical (bits : 3 word) =
    if bits = 0w then 0w
    else if bits = 1w then 1w
    else if bits = 2w then 2w
    else if bits = 3w then 3w
    else 4w
End

Theorem smtfp_pack_unpack_rounding:
  smtfp_pack_rounding (smtfp_unpack_rounding bits) =
  smtfp_rounding_canonical bits
Proof
  Cases_on `bits = 0w` >>
  Cases_on `bits = 1w` >>
  Cases_on `bits = 2w` >>
  Cases_on `bits = 3w` >>
  asm_simp_tac std_ss [smtfp_unpack_rounding_def,
    smtfp_pack_rounding_def, smtfp_rounding_canonical_def] >>
  EVAL_TAC
QED

Theorem smtfp_pack_rounding_canonical:
  smtfp_pack_rounding mode =
  smtfp_rounding_canonical (smtfp_pack_rounding mode)
Proof
  Cases_on `mode` >>
  simp [smtfp_pack_rounding_def, smtfp_rounding_canonical_def]
QED

Theorem smtfp_rounding_case_unpack:
  (case smtfp_unpack_rounding bits of
     RNE => rne
   | RNA => rna
   | RTP => rtp
   | RTN => rtn
   | RTZ => rtz) =
  if bits = 0w then rne
  else if bits = 1w then rna
  else if bits = 2w then rtp
  else if bits = 3w then rtn
  else rtz
Proof
  Cases_on `bits = 0w` >>
  Cases_on `bits = 1w` >>
  Cases_on `bits = 2w` >>
  Cases_on `bits = 3w` >>
  asm_simp_tac std_ss [smtfp_unpack_rounding_def] >>
  EVAL_TAC
QED

Theorem smtfp_rounding_case_pack:
  (case mode of
     RNE => rne
   | RNA => rna
   | RTP => rtp
   | RTN => rtn
   | RTZ => rtz) =
  if smtfp_pack_rounding mode = 0w then rne
  else if smtfp_pack_rounding mode = 1w then rna
  else if smtfp_pack_rounding mode = 2w then rtp
  else if smtfp_pack_rounding mode = 3w then rtn
  else rtz
Proof
  Cases_on `mode` >> simp [smtfp_pack_rounding_def]
QED

Theorem smtfp_pack_rounding_index:
  smtfp_pack_rounding mode ' i <=>
  if mode = RNE then (0w : 3 word) ' i
  else if mode = RNA then (1w : 3 word) ' i
  else if mode = RTP then (2w : 3 word) ' i
  else if mode = RTN then (3w : 3 word) ' i
  else (4w : 3 word) ' i
Proof
  Cases_on `mode` >> simp [smtfp_pack_rounding_def]
QED

Theorem word_compare_index:
  (word_compare left right : 1 word) ' 0 <=> left = right
Proof
  Cases_on `left = right` >>
  asm_simp_tac std_ss [word_compare_def, word_index] >> EVAL_TAC
QED

Theorem word_lsl_index:
  index < dimindex (:'a) ==>
  (((word_lsl (word : 'a word) amount) ' index) <=>
   amount <= index /\ word ' (index - amount))
Proof
  simp [wordsTheory.word_lsl_def, fcpTheory.FCP_BETA]
QED

Theorem word_lsr_index:
  index < dimindex (:'a) ==>
  (((word_lsr (word : 'a word) amount) ' index) <=>
   index + amount < dimindex (:'a) /\ word ' (index + amount))
Proof
  simp [wordsTheory.word_lsr_def, fcpTheory.FCP_BETA]
QED

Theorem word_asr_index:
  index < dimindex (:'a) ==>
  (((word_asr (word : 'a word) amount) ' index) <=>
   if dimindex (:'a) <= index + amount then word_msb word
   else word ' (index + amount))
Proof
  simp [wordsTheory.word_asr_def, fcpTheory.FCP_BETA]
QED

Theorem word1_eq_index:
  ((left : 1 word) = right) <=> (left ' 0 <=> right ' 0)
Proof
  simp [GSYM WORD_EQ, GSYM word_bit]
QED

Theorem word1_cond_index:
  ((if condition then left else right) : 1 word) ' 0 <=>
  if condition then left ' 0 else right ' 0
Proof
  Cases_on `condition` >> simp []
QED

Theorem word1_neg:
  -(value : 1 word) = value
Proof
  blastLib.BBLAST_TAC
QED

Theorem smtfp_is_nan_components:
  smtfp_is_nan x <=>
  (smtfp_rep x).Exponent = -1w /\
  (smtfp_rep x).Significand <> 0w
Proof
  rw [smtfp_is_nan_def, binary_ieeeTheory.float_is_nan_def,
      binary_ieeeTheory.float_value_def]
QED

Theorem smtfp_rep_canonical_fields:
  let r = smtfp_rep x in
    ~(r.Exponent = -1w /\ r.Significand <> 0w) \/
    (r.Sign = 0w /\ r.Exponent = -1w /\
     r.Significand = 1w #>> 1)
Proof
  `smtfp_canonical (smtfp_rep x)` by simp [] >>
  qpat_x_assum `smtfp_canonical (smtfp_rep x)` mp_tac >>
  rewrite_tac [smtfp_canonical_def] >>
  simp [GSYM smtfp_is_nan_def, float_canon_qnan_def,
        binary_ieeeTheory.float_component_equality] >>
  simp [smtfp_is_nan_components]
QED

Theorem smtfp_rep_nan:
  smtfp_is_nan x ==> smtfp_rep x = float_canon_qnan
Proof
  rw [smtfp_is_nan_def] >>
  metis_tac [smtfp_rep_canonical, smtfp_canonical_def]
QED

Theorem smtfp_neg_rep_fields:
  (smtfp_rep (smtfp_neg x)).Sign =
    (if smtfp_is_nan x then (smtfp_rep x).Sign
     else ~(smtfp_rep x).Sign) /\
  (smtfp_rep (smtfp_neg x)).Exponent = (smtfp_rep x).Exponent /\
  (smtfp_rep (smtfp_neg x)).Significand = (smtfp_rep x).Significand
Proof
  simp [smtfp_neg_def] >>
  Cases_on `smtfp_is_nan x` >>
  fs [smtfp_rep_nan, smtfp_is_nan_def, canon_def,
      binary_ieeeTheory.float_negate_def]
QED

Theorem word_and_index0:
  (word_and (left : 'a word) right) ' 0 <=> left ' 0 /\ right ' 0
Proof
  srw_tac [fcpLib.FCP_ss] [word_and_def, DIMINDEX_GT_0]
QED

Theorem word_or_index0:
  (word_or (left : 'a word) right) ' 0 <=> left ' 0 \/ right ' 0
Proof
  srw_tac [fcpLib.FCP_ss] [word_or_def, DIMINDEX_GT_0]
QED

Theorem word_xor_index0:
  (word_xor (left : 'a word) right) ' 0 <=> (left ' 0 <> right ' 0)
Proof
  srw_tac [fcpLib.FCP_ss] [word_xor_def, DIMINDEX_GT_0]
QED

Theorem word_1comp_index0:
  (word_1comp (value : 'a word)) ' 0 <=> ~(value ' 0)
Proof
  srw_tac [fcpLib.FCP_ss] [word_1comp_def, DIMINDEX_GT_0]
QED

Theorem word_add_one_index0:
  ((value : 'a word) + 1w) ' 0 <=> ~(value ' 0)
Proof
  simp [WORD_ADD_BIT0, word_index]
QED

Theorem word_add_one_twice_index0:
  (((value : 'a word) + 1w) + 1w) ' 0 <=> value ' 0
Proof
  simp [WORD_ADD_BIT0, word_index]
QED

Theorem word1_minus_index:
  ((-1w * value + -1w) : 1 word) ' 0 <=> ~(value ' 0)
Proof
  blastLib.BBLAST_TAC
QED

Theorem word1_neg_minus_index:
  ((-value + -1w) : 1 word) ' 0 <=> ~(value ' 0)
Proof
  blastLib.BBLAST_TAC
QED

Theorem smtfp_float_value_negate_cases:
  float_value (float_negate x) =
  case float_value x of
    Float r => Float (-r)
  | Infinity => Infinity
  | NaN => NaN
Proof
  Cases_on `float_value x` >> simp [float_negate] >>
  fs [float_value_def, float_negate_def, AllCaseEqs()]
QED

Theorem smtfp_word1_complement_eq:
  (s = ~t : word1) <=> s <> t
Proof
  wordsLib.WORD_DECIDE_TAC
QED

Theorem smtfp_canon_sub_add_negate:
  canon (smt_float_sub mode (x : ('a,'b) float) y) =
  canon (smt_float_add mode x (float_negate y))
Proof
  Cases_on `to_binary_rounding mode` >>
  Cases_on `float_value x` >> Cases_on `float_value y` >>
  Cases_on `x.Sign = y.Sign` >>
  simp [smt_float_sub_def, smt_float_add_def,
        float_sub_def, float_add_def, smtfp_float_value_negate_cases,
        float_components, smtfp_word1_complement_eq,
        canon_def, float_is_nan_def, some_nan_properties, real_sub]
QED

Theorem smtfp_canon_add_right_canon:
  canon (smt_float_add mode x (canon y)) =
  canon (smt_float_add mode x y)
Proof
  Cases_on `float_value y` >> simp [canon_def, float_is_nan_def] >>
  Cases_on `to_binary_rounding mode` >> Cases_on `float_value x` >>
  simp [smt_float_add_def, float_add_def, canon_def,
        float_is_nan_def, some_nan_properties]
QED

Theorem smtfp_sub_add_negate:
  smtfp_sub mode (x : ('a,'b) smtfp) y =
  smtfp_add mode x (smtfp_neg y)
Proof
  simp [smtfp_sub_def, smtfp_add_def, smtfp_neg_def,
        smtfp_canon_add_right_canon, smtfp_canon_sub_add_negate]
QED

Theorem smtfp_unpack_rounding_tests:
  (smtfp_unpack_rounding bits = RNE <=> bits = 0w) /\
  (smtfp_unpack_rounding bits = RNA <=> bits = 1w) /\
  (smtfp_unpack_rounding bits = RTP <=> bits = 2w) /\
  (smtfp_unpack_rounding bits = RTN <=> bits = 3w) /\
  (smtfp_unpack_rounding bits = RTZ <=>
    bits <> 0w /\ bits <> 1w /\ bits <> 2w /\ bits <> 3w)
Proof
  Cases_on `bits = 0w` >>
  Cases_on `bits = 1w` >>
  Cases_on `bits = 2w` >>
  Cases_on `bits = 3w` >>
  asm_simp_tac std_ss [smtfp_unpack_rounding_def] >>
  EVAL_TAC
QED

val _ = export_theory ();
