(* Copyright (c) 2026 The HOL4 contributors. *)
signature WordCancelLiteral =
sig
  type classification = {negative:bool,minimum:bool}
  (* Optional metadata for live, canonical numeric widths 1..32 and bounded
     n2w/negation/subtraction expressions. NONE selects the existing worker. *)
  val classify : Term.term -> classification option
end
