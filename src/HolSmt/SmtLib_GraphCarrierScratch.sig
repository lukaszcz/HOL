(* Borrowed mixed syntax for matching captured theorem declarations. *)
signature SmtLib_GraphCarrierScratch =
sig
  type term
  exception Mismatch of string
  type interface =
    {operations:term SmtLib_CarrierHoMatch.operations,
     of_query:SmtLib_GraphQueryAnalysis.carrier -> term,
     of_template:Term.term -> term,
     variant:term list -> term -> term,
     variable_name:term -> string,
     atomic_term:term -> Term.term option}

  (* Templates are actual captured declaration/theorem syntax, never a
     materialized query. Query syntax is exposed only through its borrowed
     carrier. Native free variables share their typed name with genuine
     RigidSource leaves. Other Query variable kinds retain their exact
     graph identity independently of their printed name.

     Scratch construction, matching, substitution and type instantiation
     produce DATA only. They grant no theorem, Source, parser declaration
     or graph-construction permission. Each operation guards the borrow
     and its retained Query operands, including successful cache hits.
     Scratch variables cannot be exported as new Query variables.

     Substitution is simultaneous and capture avoiding. Type instantiation
     preserves binding even when distinct native variable types coalesce.
     Free-variable summaries are cached only for explicitly requested
     roots; traversal does not save a full variable set at every node. *)
  val create : SmtLib_GraphQueryAnalysis.outbound_context -> interface
end
