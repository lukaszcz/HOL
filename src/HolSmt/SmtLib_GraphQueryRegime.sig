(* Automatic regime selection through the shared native decision grammar. *)
signature SmtLib_GraphQueryRegime =
sig
  type result = {regime:SmtLib.regime,reason:string,visits:int}
  (* Uses actual carrier syntax and the existing TypeBase case peel.
     Selector-variable inheritance and scoped syntax both enter the local
     memo key. Only successful completed reasons, including NONE, cache.
     An explicit override skips every syntax-classification callback while
     still checking the authenticated borrow. No proof or Source is added. *)
  val select : SmtLib_GraphQueryAnalysis.outbound_context ->
    {operations:SmtLib_GraphQueryAnalysis.carrier
       SmtLib.outbound_term_translation_operations,
     request:SmtLib.outbound_regime_request} -> result
end
