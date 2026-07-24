signature classicalLib =
sig
  include Abbrev

  val SAFE_TAC : thm list -> tactic
  val CLARIFY_TAC : thm list -> tactic
  val SAFE_STEP_TAC : thm list -> tactic
  val CLARIFY_STEP_TAC : thm list -> tactic
  val STEP_TAC : thm list -> tactic
  val SLOW_STEP_TAC : thm list -> tactic
  val INST_STEP_TAC : thm list -> tactic

  val FAST_TAC : thm list -> tactic
  val SLOW_TAC : thm list -> tactic
  val BEST_TAC : thm list -> tactic
  val SLOW_BEST_TAC : thm list -> tactic
  val FIRST_BEST_TAC : thm list -> tactic
  val ASTAR_TAC : thm list -> tactic
  val SLOW_ASTAR_TAC : thm list -> tactic
  val DEEPEN_TAC : thm list -> tactic

  val CS_SAFE_TAC : clasetLib.claset -> NTactical.ntactic
  val CS_CLARIFY_TAC : clasetLib.claset -> NTactical.ntactic
  val CS_SAFE_STEP_TAC : clasetLib.claset -> NTactical.ntactic
  val CS_CLARIFY_STEP_TAC : clasetLib.claset -> NTactical.ntactic
  val CS_STEP_TAC : clasetLib.claset -> NTactical.ntactic
  val CS_SLOW_STEP_TAC : clasetLib.claset -> NTactical.ntactic
  val CS_INST_STEP_TAC : clasetLib.claset -> NTactical.ntactic

  val CS_FAST_TAC : clasetLib.claset -> NTactical.ntactic
  val CS_SLOW_TAC : clasetLib.claset -> NTactical.ntactic
  val CS_BEST_TAC : clasetLib.claset -> NTactical.ntactic
  val CS_SLOW_BEST_TAC : clasetLib.claset -> NTactical.ntactic
  val CS_FIRST_BEST_TAC : clasetLib.claset -> NTactical.ntactic
  val CS_ASTAR_TAC : clasetLib.claset -> NTactical.ntactic
  val CS_SLOW_ASTAR_TAC : clasetLib.claset -> NTactical.ntactic
  val CS_DEPTH_SOLVE_TAC :
    {dup : bool} -> int -> clasetLib.claset -> NTactical.ntactic
  val CS_DEEPEN_TAC : clasetLib.claset ->
                      {start : int} -> NTactical.ntactic
end
