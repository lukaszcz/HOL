signature SmtLib_GraphCarrierDatatype =
sig
  type errors =
    {syntax_error : string -> string -> exn, is_mismatch : exn -> bool}
  type hooks =
    {parser_case : SmtLib_GraphQueryAnalysis.carrier ->
       SmtLib_GraphQueryAnalysis.carrier
         SmtLib.outbound_carrier_parser_case option,
     datatype_selector_term : Type.hol_type -> Term.term -> int ->
       SmtLib_GraphQueryAnalysis.carrier -> SmtLib_GraphQueryAnalysis.carrier,
     is_case : SmtLib_GraphQueryAnalysis.carrier -> bool,
     case_view : SmtLib_GraphQueryAnalysis.carrier ->
       {scrutinee:SmtLib_GraphQueryAnalysis.carrier,
        clauses:(SmtLib_GraphQueryAnalysis.carrier list *
          SmtLib_GraphQueryAnalysis.carrier) list} option}

  (* Borrow-local declaration templates and recipes. Native operands remain
     authenticated carriers; only fresh holes, atomic declarations and the
     public parser templates are inspected as HOL syntax. The callbacks and
     every cached result expire with the supplied outbound context. *)
  val make : SmtLib_GraphQueryAnalysis.outbound_context -> errors -> hooks
end
