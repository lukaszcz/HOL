signature linarithLib =
sig
  include Abbrev

  type linarith_config = linarithData.linarith_config
  val default_config : linarith_config

  val LINARITH_TAC : thm list -> tactic
  val SIMPLE_LINARITH_TAC : thm list -> tactic
  val CFG_LINARITH_TAC : linarith_config -> thm list -> tactic

  val LINARITH_PROVE : term -> thm
  val LINARITH_CONV : conv
end
