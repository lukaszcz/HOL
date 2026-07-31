signature linarithReplay =
sig
  type instance_env
  type config = linarithData.linarith_config

  val mk_instance_env : Term.term list -> instance_env

  val generalize :
    Term.term list -> (Term.term list -> Thm.thm) -> Thm.thm

  val mkthm :
    instance_env -> Thm.thm list -> linarithSolve.injust -> Thm.thm

  val fwd_prove : config -> Thm.thm list -> Term.term -> Thm.thm

  val refute_tac :
    bool -> linarithSolve.injust list -> Abbrev.tactic
end
