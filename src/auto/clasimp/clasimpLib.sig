signature clasimpLib =
sig
  include Abbrev

  val clasimp_ss : unit -> simpLib.simpset
  val asm_full_simp : simpLib.simpset -> thm list -> tactic
  val safe_asm_full_simp : simpLib.simpset -> thm list -> tactic
end
