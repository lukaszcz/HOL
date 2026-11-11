(* Registered-theorem reduction over an authentic outbound borrow. *)
signature SmtLib_GraphCarrierResidual =
sig
  (* Each invocation gets fresh stock rewrite counters. The borrowed scratch
     algebra retains Query operands and their scope/lifetime guards; it
     never materializes the target as a native HOL tree. The supplied
     theorem is the exact object selected by the existing TypeBase
     destructor policy. No theorem or Source permission is returned. *)
  val theorem_reduces_exact_application :
    SmtLib_GraphQueryAnalysis.outbound_context -> Thm.thm ->
    SmtLib_GraphQueryAnalysis.carrier -> bool

end
