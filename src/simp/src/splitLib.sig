signature splitLib =
sig
  include Abbrev

  (* Analyse the supplied rules when the conversion is constructed. *)
  val SPLIT_CONV : thm list -> conv

  (* Split the first assumption containing an assumption-rule key. *)
  val SPLIT_ASM_TAC : thm list -> tactic

  (* Perform one split, preferring the conclusion to assumptions. *)
  val SPLIT_TAC : thm list -> tactic
end
