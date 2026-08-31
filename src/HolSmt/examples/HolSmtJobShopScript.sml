Theory HolSmtJobShop
Ancestors
  integer
Libs
  HolSmtLib

(* Job-shop scheduling is the canonical SMT scheduling application (de Moura
   & Bjorner, "Satisfiability Modulo Theories: Introduction and
   Applications", CACM 54(9), 2011).  This instance has three jobs, each
   running on machine 1 and then machine 2, with durations

     job 1: 2 then 1,   job 2: 3 then 1,   job 3: 2 then 3.

   A schedule assigns a start time t_ij to job i on machine j.  It is valid
   when start times are non-negative, each job visits machine 2 after
   finishing on machine 1, and tasks sharing a machine do not overlap (for
   each pair, one finishes before the other starts — the characteristic
   disjunctive constraints of the encoding). *)
Definition valid_schedule_def:
  valid_schedule (t11 : int) t12 t21 t22 t31 t32 <=>
    0 <= t11 /\ 0 <= t21 /\ 0 <= t31 /\
    t11 + 2 <= t12 /\ t21 + 3 <= t22 /\ t31 + 2 <= t32 /\
    (t11 + 2 <= t21 \/ t21 + 3 <= t11) /\
    (t11 + 2 <= t31 \/ t31 + 2 <= t11) /\
    (t21 + 3 <= t31 \/ t31 + 2 <= t21) /\
    (t12 + 1 <= t22 \/ t22 + 1 <= t12) /\
    (t12 + 1 <= t32 \/ t32 + 3 <= t12) /\
    (t22 + 1 <= t32 \/ t32 + 3 <= t22)
End

(* Supplying the definition to z3_tac (as to metis_tac) lets the solver
   check a concrete schedule: job 3 first on machine 1, its long machine-2
   task overlapped with the other jobs' machine-1 work. *)
Theorem schedule_witness:
  valid_schedule 2 5 4 7 0 2
Proof
  z3_tac [valid_schedule_def]
QED

(* The witness finishes at time 8.  Optimality is the interesting theorem:
   *every* valid schedule has makespan at least 8.  The solver proves it by
   refuting the existence of a schedule whose three completion times all
   beat the bound — an unsatisfiability argument over the disjunctive
   constraints, which is exactly what SMT solvers are built for. *)
Theorem makespan_lower_bound:
  !t11 t12 t21 t22 t31 t32 : int.
    valid_schedule t11 t12 t21 t22 t31 t32 ==>
    8 <= int_max (t12 + 1) (int_max (t22 + 1) (t32 + 3))
Proof
  z3_tac [valid_schedule_def]
QED
