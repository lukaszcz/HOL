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

  val safe_tac : clasetLib.claset -> NTactical.ntactic
  val clarify_tac : clasetLib.claset -> NTactical.ntactic
  val safe_step_tac : clasetLib.claset -> NTactical.ntactic
  val clarify_step_tac : clasetLib.claset -> NTactical.ntactic
  val step_tac : clasetLib.claset -> NTactical.ntactic
  val slow_step_tac : clasetLib.claset -> NTactical.ntactic
  val inst_step_tac : clasetLib.claset -> NTactical.ntactic

  val fast_tac : clasetLib.claset -> NTactical.ntactic
  val slow_tac : clasetLib.claset -> NTactical.ntactic
  val best_tac : clasetLib.claset -> NTactical.ntactic
  val slow_best_tac : clasetLib.claset -> NTactical.ntactic
  val first_best_tac : clasetLib.claset -> NTactical.ntactic
  val astar_tac : clasetLib.claset -> NTactical.ntactic
  val slow_astar_tac : clasetLib.claset -> NTactical.ntactic
  val deepen_tac : clasetLib.claset ->
                   {start : int} -> NTactical.ntactic
end
