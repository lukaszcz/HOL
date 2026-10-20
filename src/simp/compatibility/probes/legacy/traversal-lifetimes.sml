(* Identical legacy-only input in both lanes and normal selftest coverage. *)
open HolKernel testutils
val _ = new_theory "traversallifetimes"
val _ = TraversalContracts.run ()
val _ = OS.Process.exit OS.Process.success
