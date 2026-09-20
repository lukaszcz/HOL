
signature minisatProve = sig
  exception SAT_cex of Thm.thm
  exception SAT_satisfiable of unit
  val GEN_SAT : satConfig.sat_config -> Thm.thm
  val SAT_PROVE : Term.term -> Thm.thm
  val SAT_PROVE_ONLY : Term.term -> Thm.thm
  val SAT_ORACLE : Term.term -> Thm.thm
  val ZSAT_PROVE : Term.term -> Thm.thm
  val ZSAT_ORACLE : Term.term -> Thm.thm
end
