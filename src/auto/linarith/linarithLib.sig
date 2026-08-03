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

  val CACHED_LINARITH : thm list -> conv
  val LINARITH_REDUCER : Traverse.reducer
  val LINARITH_ss : simpLib.ssfrag
  val linarith_solver : Traverse.ssolver
  val clear_linarith_caches : unit -> unit
end
