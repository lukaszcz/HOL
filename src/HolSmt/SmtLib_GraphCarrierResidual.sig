(* Captured TypeBase residual policy over an authentic outbound borrow. *)
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

  (* Instantiate the SAME shared registered-destructor/closed-constructor
     grammar with the full graph rewrite driver. metadata_error adapts only
     that grammar's isolated declaration/type failures. Matching, native
     primary failures, ownership, Work and scope errors are never caught as
     ordinary syntax mismatch. The caller fixes the existing backend context
     and retains responsibility for original-to-emitted proof transport. *)
  val make : SmtLib_GraphQueryAnalysis.outbound_context ->
    {syntax_error:string -> string -> exn,metadata_error:exn -> exn} ->
    SmtLib_GraphQueryAnalysis.carrier -> bool
end
