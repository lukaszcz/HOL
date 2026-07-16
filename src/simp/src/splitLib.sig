signature splitLib =
sig
  include Abbrev

  (* Analyse the supplied rules when the conversion is constructed. *)
  val SPLIT_CONV : thm list -> conv

  (* Split the first assumption containing an assumption-rule key. *)
  val SPLIT_ASM_TAC : thm list -> tactic

  (* Perform one split, preferring the conclusion to assumptions. *)
  val SPLIT_TAC : thm list -> tactic

  (* Cached datatype split rules. *)
  val type_split_of : hol_type -> thm
  val type_asm_split_of : hol_type -> thm

  (* The persistent [split] theorem set. *)
  val split_thms : unit -> thm list
  val named_split_thms : unit -> (string * thm) list

  (* Registration helpers used by simpLib. *)
  val is_asm_split : thm -> bool
  val split_thm_name : thm -> string
end
