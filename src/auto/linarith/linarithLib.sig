signature linarithLib =
sig
  include Abbrev

  val SIMPLE_LINARITH_TAC : thm list -> tactic
  val LINARITH_PROVE : term -> thm
  val LINARITH_CONV : conv
end
