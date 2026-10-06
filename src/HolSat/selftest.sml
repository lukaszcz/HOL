open HolKernel Parse boolLib testutils HolSatLib

val _ = set_trace "Unicode" 0

(* #1170: SAT_ORACLE used to fabricate a bogus theorem on inputs whose
   negated form has a top-level conjunct that boolean-simplifies to F.
   For ``b ==> T`` the negation is ``b /\ ~T``; presimp turns ``~T`` into
   ``F``, but the F conjunct was silently dropped from the CNF passed to
   MiniSAT, which then declared satisfiability. SAT_ORACLE skipped the
   model-check that SAT_PROVE relies on and returned a bogus
   |- b ==> ~(b ==> T). The fix short-circuits in to_cnf when a conjunct
   reduces to F, so MiniSAT is never invoked for this case (and so the
   test does not depend on a working MiniSAT installation). *)
val _ = tprint "SAT_ORACLE proves `b ==> T` (#1170)"
val _ = require_msg
          (check_result (fn th => concl th ~~ ``b ==> T``))
          thm_to_string
          SAT_ORACLE
          ``b ==> T``

(* Definitional CNF uses a shared root assumption while replaying the
   resolution trace; the returned proof must still discharge that root. *)
val _ = tprint "SAT_PROVE discharges definitional CNF roots"
val _ = require_msg
          (check_result (fn th => null (hyp th) andalso
            concl th ~~ ``(p /\ q) ==> (q /\ p)``))
          thm_to_string
          SAT_PROVE
          ``(p /\ q) ==> (q /\ p)``

(* Proof-only mode checks UNSAT certificates but never constructs a theorem
   for a satisfying assignment that the caller will discard. *)
val _ = tprint "SAT_PROVE_ONLY checks UNSAT proofs"
val _ = require_msg
          (check_result (fn th => null (hyp th) andalso
            concl th ~~ ``(p /\ q) ==> (q /\ p)``))
          thm_to_string
          SAT_PROVE_ONLY
          ``(p /\ q) ==> (q /\ p)``

val _ = tprint "SAT_PROVE_ONLY rejects SAT instances"
val _ = require_msg
          (check_result (fn rejected => rejected))
          Bool.toString
          (fn tm => (ignore (SAT_PROVE_ONLY tm); false)
             handle SAT_satisfiable _ => true)
          ``p \/ q``

(* Explicit CNF counts propositional atoms, which need not be HOL
   variables.  Here P is the only free variable but P T and P F are
   distinct DIMACS atoms.  Proof-only mode must also override an oracle
   flag supplied in the configuration. *)
val _ = tprint "explicit CNF counts compound Boolean atoms"
val _ = require_msg
          (check_result (fn th =>
            let val (oracles, axioms) = Tag.dest_tag (tag th)
            in null (hyp th) andalso
               concl th ~~ ``~((P:bool->bool) T /\ ~P T /\ P F /\ ~P F)``
               andalso List.all (fn name => name = "DISK_THM") oracles
               andalso null axioms
            end))
          thm_to_string
          (fn tm => GEN_SAT_PROVE_ONLY
            (satConfig.set_flag_is_proved false
              (satConfig.set_flag_is_cnf true
                (satConfig.set_term tm satConfig.base_config))))
          ``(P:bool->bool) T /\ ~P T /\ P F /\ ~P F``

val _ = tprint "proof-only explicit CNF rejects SAT without model checking"
val _ = require_msg
          (check_result (fn rejected => rejected))
          Bool.toString
          (fn tm =>
            (ignore (GEN_SAT_PROVE_ONLY
              (satConfig.set_flag_is_cnf true
                (satConfig.set_term tm satConfig.base_config)));
             false)
            handle SAT_satisfiable _ => true)
          ``(P:bool->bool) T /\ ~P F``
