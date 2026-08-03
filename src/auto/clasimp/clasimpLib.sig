signature clasimpLib =
sig
  include Abbrev

  (* The safe side-condition solver of the clasimp simpset.  It discharges
     only goals justified without witness instantiation or unsafe search,
     which is what makes it usable in a normalisation phase.  Exported so
     that simpsets derived elsewhere (aesop) share this one solver stack
     rather than restating it. *)
  val safe_solver : Traverse.ssolver

  (* The unsafe side-condition solvers of the clasimp simpset, in the order
     the simplifier tries them.  Exported for the same reason as
     safe_solver: a simpset derived elsewhere (aesop) installs this one
     list rather than restating it, so a decision procedure added here
     reaches every derived simpset instead of only this one. *)
  val unsafe_solvers : Traverse.ssolver list

  val clasimp_ss : unit -> simpLib.simpset
  val asm_full_simp : simpLib.simpset -> thm list -> tactic
  val safe_asm_full_simp : simpLib.simpset -> thm list -> tactic

  val add_simp_wrapper :
    simpLib.simpset -> thm list -> clasetLib.claset -> clasetLib.claset
  val add_safe_simp_wrapper :
    simpLib.simpset -> thm list -> clasetLib.claset -> clasetLib.claset

  (* Pure [iff] decision tree.  Callers choose where to install the
     derived claset rules and the normalized simpset rewrite. *)
  val iff_declaration :
    string -> thm ->
    {rules :
       (clasetRules.rulespec * (string * thm)) list,
     rewrite : thm}

  (* Installs the rules of an iff_declaration.  They are derived rather than
     named by the user, so a duplicate among them is dropped silently. *)
  val add_iff_rules :
    (clasetRules.rulespec * (string * thm)) list ->
    clasetLib.claset -> clasetLib.claset

  val remove_iff : string -> unit

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
