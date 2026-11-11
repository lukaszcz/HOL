(* Static native specialization of the SAME checked Boolean programme. *)
structure SmtReplayNamedBooleanNative =
struct
  type context = unit
  type proof = Thm.thm
  val default_context = ()
  val concl = Thm.concl
  val hyp = Thm.hyp
  val tag = Thm.tag
  fun truth _ = boolTheory.TRUTH
  fun definition_cnf _ = SmtCircuitSat.definition_cnf
  fun balanced_equivalences _ = SmtCircuitSat.balanced_equivalences
  fun refl _ = SmtReplayRuleObservation.REFL
  fun prove_cnf _ = SmtCircuitSat.prove_cnf
end

structure SmtReplayNamedBoolean :> SmtReplayNamedBoolean =
  SmtReplayNamedBooleanFn(SmtReplayNamedBooleanNative)
