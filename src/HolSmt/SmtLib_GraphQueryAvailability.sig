(* Operator availability over authenticated outbound graph syntax. *)
signature SmtLib_GraphQueryAvailability =
sig
  (* sequence_emission is the caller's fixed backend decision. Uses the
     existing operator registry, version policy and exact diagnostics.
     Visits each scoped query node once, ignoring abstraction binders as
     the native term-head inventory does. Only genuine constant leaves
     enter native constant comparison. Empty inventories and cache hits
     retain borrow/lifetime guards. No Source or proof permission arises. *)
  val check : SmtLib_GraphQueryAnalysis.outbound_context ->
    {sequence_emission:bool,target:{solver:string,version:string option}} ->
    {visits:int}
end
