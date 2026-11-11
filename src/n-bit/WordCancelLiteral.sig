(* Copyright (c) 2026 The HOL4 contributors. *)
signature WordCancelLiteral =
sig
  type classification = {negative:bool,minimum:bool}
  (* Optional metadata for live, canonical numeric widths 1..32 and bounded
     n2w/negation/subtraction expressions. NONE selects the existing worker. *)
  val classify : Term.term -> classification option
  (* Separate copy of wordsLib's WORD_CANCEL_CONV/WORD_CANCEL_ss that routes
     coefficients through classify before the original evaluation-based
     tests. It returns the same theorems; the wordsLib originals are
     unchanged. *)
  val WORD_CANCEL_CONV : Conv.conv
  val WORD_CANCEL_ss : simpLib.ssfrag
end
