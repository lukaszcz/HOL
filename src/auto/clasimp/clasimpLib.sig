signature clasimpLib =
sig
  include Abbrev

  val clasimp_ss : unit -> simpLib.simpset
  val asm_full_simp : simpLib.simpset -> thm list -> tactic
  val safe_asm_full_simp : simpLib.simpset -> thm list -> tactic

  val add_simp_wrapper :
    simpLib.simpset -> clasetLib.claset -> clasetLib.claset
  val add_safe_simp_wrapper :
    simpLib.simpset -> clasetLib.claset -> clasetLib.claset

  (* Shared packaging for theorem-list clasimp tactics.  The body receives
     the temporary claset, temporary simpset, and generic simp controls. *)
  val process_clasimp_args :
    (clasetLib.claset -> simpLib.simpset -> thm list -> tactic) ->
    clasetLib.claset -> simpLib.simpset -> thm list -> tactic
end
