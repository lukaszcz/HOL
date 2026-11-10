(* The shared semantic dispatcher with persistent graph output scheduling. *)
signature SmtLib_GraphDispatcher =
sig
  type root =
    {occurrence:int,syntax:SmtLib_GraphQueryAnalysis.carrier,
     declarations:SmtLib_OutputFragments.doc list,
     expression:SmtLib_OutputFragments.doc}
  type result =
    {types:(Type.hol_type,string) Redblackmap.dict,
     symbols:SmtLib_GraphCarrierStore.symbol list,
     encodings:SmtLib_GraphCarrierStore.encoding list,roots:root list}

  (* Run inside the authenticated outbound borrow and the caller's fixed
     SmtLib backend context. Operations must instantiate the complete shared
     semantic registry, including checked datatype/residual policies.
     Occurrence numbers distinguish the original assertion positions.

     Each lexical environment has a persistent document memo. Binder/LET
     bodies close their local lets; LET RHS retains its incoming region.
     Generated global definition bodies close their reachable references
     under their own quantified dependencies. All speculative symbol, sort
     and output changes travel together through the worker accumulator.

     No whole query Term is materialized, no second encoder is selected,
     and no Source/proof permission is produced. The caller must supply
     checked preprocessing/definition transport and authenticated parser
     mappings before invoking a checked solver. This component does not
     change the public solver defaults. Export the result during the borrow;
     retained syntax carriers expire with it. *)
  val emit : SmtLib_GraphQueryAnalysis.outbound_context ->
    {operations:SmtLib_GraphQueryAnalysis.carrier
       SmtLib.outbound_term_translation_operations,
     regime:SmtLib.regime,
     apply_operator:SmtLib.standard27_apply_operator,prefix:string,
     roots:(int * SmtLib_GraphQueryAnalysis.carrier) list} -> result
end
