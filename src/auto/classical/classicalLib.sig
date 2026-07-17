signature classicalLib =
sig
  include Abbrev

  val SAFE_TAC : thm list -> tactic
  val CLARIFY_TAC : thm list -> tactic
  val SAFE_STEP_TAC : thm list -> tactic
  val CLARIFY_STEP_TAC : thm list -> tactic

  val safe_tac : clasetLib.claset -> NTactical.ntactic
  val clarify_tac : clasetLib.claset -> NTactical.ntactic
  val safe_step_tac : clasetLib.claset -> NTactical.ntactic
  val clarify_step_tac : clasetLib.claset -> NTactical.ntactic
end
