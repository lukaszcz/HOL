(* The theorem-instance finishing protocol of Drule.HO_PART_MATCH as DATA. *)
signature SmtLib_CarrierHoPartMatch =
sig
  type term = SmtLib_GraphCarrierScratch.term
  type instance = {conditions:term list,left:term,right:term}

  (* Compile once for the captured theorem and native declaration selector.
     The returned function matches a scratch target and returns the entire
     instantiated conclusion. Only captured theorem syntax and atomic
     target binder metadata enter native theorem/binder operations. Query
     bodies and substitution residues remain scratch DAGs throughout.

     Binder-name avoidance, bound-to-abstraction repair and BETA_VAR plans
     preserve the separate stock phases. Beta steps occur only at those
     captured sites, not throughout the instantiated conclusion. Results
     carry no checked equality, theorem, Source or parser permission. *)
  val prepare : SmtLib_GraphCarrierScratch.interface ->
    {part:Term.term -> Term.term,theorem:Thm.thm} -> term -> term

  (* The exact Cond_rewr selected part is lhs o snd o strip_imp. Preparation
     happens once when this function is partially applied to the theorem;
     every target attempt uses that same compiled declaration programme. *)
  val part_match : SmtLib_GraphCarrierScratch.interface ->
    Thm.thm -> term -> instance
end
