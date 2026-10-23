(* Match the unchanged original selftest's imports without its process exit.
   The launcher checks the actual loaded namespace after these dependencies. *)
open HolKernel Parse boolLib simpLib testutils boolSimps
open pureSimps combinSimps SatisfySimps Cond_rewr
val _ = Paired.check "ordinary original dependencies load independently" true
