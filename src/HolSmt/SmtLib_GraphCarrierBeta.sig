(* Application-spine beta syntax for the shared outbound dispatcher. *)
signature SmtLib_GraphCarrierBeta =
sig
  (* Match the syntax result of Drule.LIST_BETA_CONV: reduce the rator,
     then perform one beta step. If that last step is unavailable, retain
     the original whole application, including its original rator.
     Arguments and resulting bodies are not recursively normalized.

     Substitution follows exact scoped variable identity and avoids
     capture. New syntax consists only of outbound recipes and fresh
     atomic Bound IDs in the borrow's construction child. Successful DAG
     observations are memoized locally to this call and substitution;
     borrow/scope guards precede cache use. No HOL body is materialized.

     This returns syntax DATA, not a theorem or Source permission. Checked
     original-to-emitted transport remains the caller's responsibility. *)
  val reduce : SmtLib_GraphQueryAnalysis.outbound_context ->
    SmtLib_GraphQueryAnalysis.carrier ->
    SmtLib_GraphQueryAnalysis.carrier
end
