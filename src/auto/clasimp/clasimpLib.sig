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

  val CS_AUTO_TAC :
    {blast : int, depth : int} ->
    clasetLib.claset -> simpLib.simpset -> tactic
  val CS_FORCE_TAC :
    clasetLib.claset -> simpLib.simpset -> tactic
  val CS_FASTFORCE_TAC :
    clasetLib.claset -> simpLib.simpset -> tactic
  val CS_SLOWSIMP_TAC :
    clasetLib.claset -> simpLib.simpset -> tactic
  val CS_BESTSIMP_TAC :
    clasetLib.claset -> simpLib.simpset -> tactic
  val CS_CLARSIMP_TAC :
    clasetLib.claset -> simpLib.simpset -> tactic

  val AUTO_DEPTH_TAC :
    {blast : int, depth : int} -> thm list -> tactic
  val AUTO_TAC : thm list -> tactic
  val FORCE_TAC : thm list -> tactic
  val FASTFORCE_TAC : thm list -> tactic
  val SLOWSIMP_TAC : thm list -> tactic
  val BESTSIMP_TAC : thm list -> tactic
  val CLARSIMP_TAC : thm list -> tactic
end
