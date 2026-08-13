(* Copyright (c) 2026 The HOL4 contributors. *)

(* HOL half of the ground floating-point differential battery.  The Python
   harness compares these certifying EVAL results with Z3 4.13.0. *)
open HolKernel Parse boolLib bossLib smtfloatTheory smtfloatLib

fun report (label, tm) =
  let
    val thm = EVAL tm
    val rhs = boolSyntax.rhs (Thm.concl thm)
    val clean =
      null (Thm.hyp thm) andalso
      ((Library.check_oracle_tags "HolSmtLib" ("FP differential " ^ label) thm; true)
       handle Feedback.HOL_ERR _ => false)
    val pass = rhs ~~ boolSyntax.T andalso clean
  in
    print ("HOL\t" ^ label ^ "\t" ^
           (if pass then "true\n"
            else "false: " ^ Parse.term_to_string rhs ^ "\n"));
    pass
  end
  handle e =>
    (print ("HOL\t" ^ label ^ "\terror: " ^ General.exnMessage e ^ "\n");
     false)

val one = ``(smtfp_bits 0w 15w 0w : (3,5) smtfp)``
val none = ``(smtfp_bits 1w 15w 0w : (3,5) smtfp)``
val half = ``(smtfp_bits 0w 14w 0w : (3,5) smtfp)``
val onehalf = ``(smtfp_bits 0w 15w 4w : (3,5) smtfp)``
val two = ``(smtfp_bits 0w 16w 0w : (3,5) smtfp)``
val three = ``(smtfp_bits 0w 16w 4w : (3,5) smtfp)``

val tests =
  [("literal-nan", ``(smtfp_bits 1w 31w 3w : (3,5) smtfp) =
                       smtfp_nan``),
   ("literal-positive-infinity",
    ``(smtfp_bits 0w 31w 0w : (3,5) smtfp) = smtfp_pinf``),
   ("literal-negative-infinity",
    ``(smtfp_bits 1w 31w 0w : (3,5) smtfp) = smtfp_ninf``),
   ("literal-positive-zero",
    ``(smtfp_bits 0w 0w 0w : (3,5) smtfp) = smtfp_pzero``),
   ("literal-negative-zero",
    ``(smtfp_bits 1w 0w 0w : (3,5) smtfp) = smtfp_nzero``),
   ("smallest-subnormal", ``smtfp_from_real RNA (1r / 262144) =
      (smtfp_bits 0w 0w 1w : (3,5) smtfp)``),
   ("largest-subnormal-class", ``smtfp_is_subnormal
      (smtfp_bits 0w 0w 7w : (3,5) smtfp)``),
   ("smallest-normal-class", ``smtfp_is_normal
      (smtfp_bits 0w 1w 0w : (3,5) smtfp)``),
   ("largest-finite-class", ``smtfp_is_normal
      (smtfp_bits 0w 30w 7w : (3,5) smtfp)``),
   ("rna-positive-tie", ``smtfp_from_real RNA (17r / 16) =
      (smtfp_bits 0w 15w 1w : (3,5) smtfp)``),
   ("rna-negative-tie", ``smtfp_from_real RNA (-17r / 16) =
      (smtfp_bits 1w 15w 1w : (3,5) smtfp)``),
   ("rne-positive-tie", ``smtfp_from_real RNE (17r / 16) = ^one``),
   ("rtp-positive-tie", ``smtfp_from_real RTP (17r / 16) =
      (smtfp_bits 0w 15w 1w : (3,5) smtfp)``),
   ("rtn-positive-tie", ``smtfp_from_real RTN (17r / 16) = ^one``),
   ("rtz-positive-tie", ``smtfp_from_real RTZ (17r / 16) = ^one``),
   ("rna-exponent-boundary", ``smtfp_from_real RNA (31r / 16) = ^two``),
   ("rna-overflow-midpoint", ``smtfp_from_real RNA 63488r =
      (smtfp_pinf : (3,5) smtfp)``),
   ("rna-negative-overflow-midpoint", ``smtfp_from_real RNA (-63488r) =
      (smtfp_ninf : (3,5) smtfp)``),
   ("add", ``smtfp_add RNA ^one ^half = ^onehalf``),
   ("sub", ``smtfp_sub RTP ^one ^half = ^half``),
   ("mul", ``smtfp_mul RTN ^onehalf ^two = ^three``),
   ("div", ``smtfp_div RTZ ^three ^two = ^onehalf``),
   ("sqrt", ``smtfp_sqrt RNA ^one = ^one``),
   ("fma", ``smtfp_fma RNE ^one ^two ^one = ^three``),
   ("round-to-integral-rne-tie",
    ``smtfp_round_to_integral RNE ^onehalf = ^two``),
   ("round-to-integral-rna-tie",
    ``smtfp_round_to_integral RNA ^onehalf = ^two``),
   ("round-to-integral-rtn-tie",
    ``smtfp_round_to_integral RTN ^onehalf = ^one``),
   ("minimum", ``smtfp_min ^one ^two = ^one``),
   ("maximum", ``smtfp_max ^one ^two = ^two``),
   ("remainder-quotient-tie", ``smtfp_rem ^three ^two = ^none``),
   ("to-ubv-rna-tie", ``(smtfp_to_ubv RNA ^onehalf : word8) = 2w``),
   ("to-sbv-rtz", ``(smtfp_to_sbv RTZ
      (smtfp_bits 1w 15w 4w : (3,5) smtfp) : word8) = 255w``),
   ("between-format", ``(smtfp_to_fp RNA ^one : (4,3) smtfp) =
      smtfp_bits 0w 3w 0w``),
   ("from-unsigned-bv", ``(smtfp_from_ubv RTP (1w : word8) :
      (3,5) smtfp) = ^one``),
   ("from-signed-bv", ``(smtfp_from_sbv RTN (255w : word8) :
      (3,5) smtfp) = ^none``),
   ("from-ieee-bv", ``smtfp_from_ieee_bv
      (120w : (1 + (5 + 3)) word) = ^one``),
   ("to-real", ``smtfp_to_real ^one = 1r``),
   ("comparison", ``smtfp_lt ^one ^two``),
   ("classification", ``smtfp_is_nan
      (smtfp_nan : (3,5) smtfp)``),
   ("absolute-value", ``smtfp_abs ^none = ^one``),
   ("negation", ``smtfp_neg ^one = ^none``),
   ("nan-arithmetic", ``smtfp_add RNE
      (smtfp_pinf : (3,5) smtfp) smtfp_ninf = smtfp_nan``),
   ("signed-zero-add", ``smtfp_add RNA
      (smtfp_nzero : (3,5) smtfp) smtfp_nzero = smtfp_nzero``)]

val ok = List.all Lib.I (map report tests)
val _ = OS.Process.exit (if ok then OS.Process.success else OS.Process.failure)
