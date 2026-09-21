(* Copyright (c) 2009-2012 Tjark Weber. All rights reserved. *)

(* Entry point into HolSmtLib. Provides GENERIC_SMT_TAC and derived tactics to
   call SMT solvers. *)

structure HolSmtLib :> HolSmtLib = struct

  open Abbrev

  val op THEN = Tactical.THEN

  fun GENERIC_SMT_TAC solver goal (_ : Context.t) =
  let
    val ERR = Feedback.mk_HOL_ERR "HolSmtLib" "GENERIC_SMT_TAC"
  in
    case solver goal of
      SolverSpec.SAT NONE =>
      raise ERR "solver reports negated term to be 'satisfiable'"
    | SolverSpec.SAT (SOME _) =>
      raise ERR
        "solver reports negated term to be 'satisfiable' (model returned)"
    | SolverSpec.UNSAT NONE =>
      raise ERR "checked solver returned UNSAT without a checked theorem"
    | SolverSpec.UNSAT (SOME thm) =>
      (* 'thm' should be of the form "A' |- concl", where A' \subseteq A, and
         (A, concl) is the input goal (cf. SolverSpec.sml) *)
      let
        val () = Library.check_oracle_tags
          "HolSmtLib" "GENERIC_SMT_TAC" thm
      in
        ([], fn _ => thm)
      end
    | SolverSpec.UNKNOWN NONE =>
      raise ERR
        "solver reports 'unknown' (solver not installed/problem too hard?)"
    | SolverSpec.UNKNOWN (SOME message) =>
      raise ERR ("solver reports 'unknown' (" ^ message ^ ")")
  end

  (* Keep the oracle-producing path disjoint from GENERIC_SMT_TAC, so a
     checked tactic's call graph contains no mk_oracle_thm branch. *)
  fun ORACLE_SMT_TAC solver goal (_ : Context.t) =
  let
    val ERR = Feedback.mk_HOL_ERR "HolSmtLib" "ORACLE_SMT_TAC"
  in
    case solver goal of
      SolverSpec.SAT NONE =>
      raise ERR "solver reports negated term to be 'satisfiable'"
    | SolverSpec.SAT (SOME _) =>
      raise ERR
        "solver reports negated term to be 'satisfiable' (model returned)"
    | SolverSpec.UNSAT NONE =>
      ([], fn _ => Thm.mk_oracle_thm "HolSmtLib" goal)
    | SolverSpec.UNSAT (SOME thm) =>
      ([], fn _ => thm)
    | SolverSpec.UNKNOWN NONE =>
      raise ERR
        "solver reports 'unknown' (solver not installed/problem too hard?)"
    | SolverSpec.UNKNOWN (SOME message) =>
      raise ERR ("solver reports 'unknown' (" ^ message ^ ")")
  end

  val CVC_ORACLE_TAC = ORACLE_SMT_TAC CVC.CVC_SMT_Oracle
  val CVC_TAC = GENERIC_SMT_TAC CVC.CVC_SMT_Prover
  val YICES_ORACLE_TAC = ORACLE_SMT_TAC Yices.Yices_Oracle
  val YICES_TAC = GENERIC_SMT_TAC Yices.Yices_Prover
  val Z3_ORACLE_TAC = ORACLE_SMT_TAC Z3.Z3_SMT_Oracle
  val Z3_TAC = GENERIC_SMT_TAC Z3.Z3_SMT_Prover

  fun assume_thms thms =
    Tactical.map_every (Tactic.ASSUME_TAC o Drule.GEN_ALL) thms

  (* The tactics below accept a list of theorems, like metis_tac[] *)
  fun cvco_tac thms = assume_thms thms THEN CVC_ORACLE_TAC
  fun cvc_tac thms = assume_thms thms THEN CVC_TAC
  fun z3_tac thms = assume_thms thms THEN Z3_TAC
  fun z3o_tac thms = assume_thms thms THEN Z3_ORACLE_TAC

  fun prove (tm, tac) = Tactical.TAC_PROOF(([], tm), tac)
  fun CVC_ORACLE_PROVE tm = prove (tm, CVC_ORACLE_TAC)
  fun CVC_PROVE tm = prove (tm, CVC_TAC)
  fun YICES_ORACLE_PROVE tm = prove (tm, YICES_ORACLE_TAC)
  fun YICES_PROVE tm = prove (tm, YICES_TAC)
  fun Z3_ORACLE_PROVE tm = prove (tm, Z3_ORACLE_TAC)
  fun Z3_PROVE tm = prove (tm, Z3_TAC)

  val include_theorems = SmtLib.include_theorems

  (* Solver availability is checked when a solver is used (and by the
     selftests), rather than by running every configured solver at library
     load time.  Besides making [load "HolSmtLib"] cheaper, this keeps external
     solver diagnostics out of an otherwise side-effect-free import. *)
  val _ = ()

end
