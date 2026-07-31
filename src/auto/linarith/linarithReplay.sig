signature linarithReplay =
sig
  type instance_env

  val mk_instance_env : Term.term list -> instance_env

  val generalize :
    Term.term list -> (Term.term list -> Thm.thm) -> Thm.thm

  val mkthm :
    instance_env -> Thm.thm list -> linarithSolve.injust -> Thm.thm
end
