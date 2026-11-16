(* Copyright (c) 2026 The HOL4 contributors. *)
signature WordCancelLiteral =
sig
  type classification = {negative:bool,minimum:bool}
  (* Sign and word_L tests for live, canonical numeric widths 1..32 and
     bounded n2w/negation/subtraction expressions, computed without
     evaluation.  NONE leaves the test to wordsLib's evaluation. *)
  val classify : Term.term -> classification option
  (* wordsLib's WORD_CANCEL_CONV/WORD_CANCEL_ss with classify; same
     theorems. *)
  val WORD_CANCEL_CONV : Conv.conv
  val WORD_CANCEL_ss : simpLib.ssfrag
  (* blastLib's word normalizer with WORD_CANCEL_ss above; same theorems. *)
  val WORD_SIMP_CONV : Conv.conv
end
