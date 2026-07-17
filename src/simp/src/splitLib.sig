signature splitLib =
sig
  include Abbrev

  (* Analyse the supplied rules when the conversion is constructed. *)
  val SPLIT_CONV : thm list -> conv

  (* Split the first assumption containing an assumption-rule key. *)
  val SPLIT_ASM_TAC : thm list -> tactic

  (* Perform one split, preferring the conclusion to assumptions. *)
  val SPLIT_TAC : thm list -> tactic

  (* Derive the assumption-splitting form of a conclusion split rule. *)
  val mk_asm_split : thm -> thm

  (* Cached datatype split rules.  [type_split_rules] is the derived pair
     the splitter applies. *)
  val type_split_of : hol_type -> thm
  val type_asm_split_of : hol_type -> thm
  val type_split_rules : hol_type -> thm list

  (* The persistent [split] theorem set. *)
  val split_thms : unit -> thm list
  val named_split_thms : unit -> (string * thm) list

  (* Registration helpers used by simpLib. *)
  val is_asm_split : thm -> bool
  val split_thm_name : thm -> string
end
