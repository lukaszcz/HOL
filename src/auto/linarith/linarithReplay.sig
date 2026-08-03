signature linarithReplay =
sig
  type config = linarithData.linarith_config

  val generalize :
    Term.term list -> (Term.term list -> Thm.thm) -> Thm.thm

  (* Replays one certificate; the theorem list is what its Asm nodes
     index. *)
  val mkthm : Thm.thm list -> linarithSolve.injust -> Thm.thm

  (* refute config assumptions conclusion searches for a certificate
     refuting those terms and returns the tactic that replays it, so
     the tactic must be applied to the goal they were taken from.  The
     terms are used as given: preprocessing is the caller's.  NONE is
     "no certificate", which for a caller that can still split the goal
     is not yet a failure; a genuine error is raised. *)
  val refute :
    config -> Term.term list -> Term.term -> Abbrev.tactic option

  val fwd_prove : config -> Thm.thm list -> Term.term -> Thm.thm
end
