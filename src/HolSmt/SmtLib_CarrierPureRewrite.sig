(* Syntax result of the captured TypeBase theorem's PURE_ss programme. *)
signature SmtLib_CarrierPureRewrite =
sig
  type 'term operations =
    {syntax:'term SmtLib_CarrierHoMatch.operations,
     of_template:Term.term -> 'term,variable_name:'term -> string,
     variant:'term list -> 'term -> 'term,
     part_match:Thm.thm -> 'term ->
       {conditions:'term list,left:'term,right:'term}}

  (* The theorem is the exact object selected by the existing registered
     TypeBase unary-destructor selector. It is not an arbitrary simpset
     directive or user conversion programme. Cond_rewr supplies the stock
     canonical rules, including looping/fresh-RHS EQT wrappers. Hypothesis
     carried bounded rewrites and tactic requirements keep their stock
     semantics; discarded assumption directives are not rewrite facts.

     part_match must implement Drule.HO_PART_MATCH's COMPLETE finishing
     algorithm, not just ho_match_term or general RHS beta normalization.
     Its first application prepares that theorem's captured plans; the
     returned target function is retained once per canonical rewrite rule.
     variant follows Term.variant on guarded atomic variable metadata;
     fresh binder identity remains local to the scratch syntax algebra.
     Observations and cache hits retain the supplied live algebra guards.
     No target HOL tree, theorem or Source permission is constructed.

     Conversion success differs from final alpha change: a bounded cycle
     may produce a successful reflexive conversion. The conditional solver
     retains that distinction. Rewrite counters are local to this call,
     shared by canonical rules from the same theorem and decremented only
     after that rule and all its conditions have succeeded. *)
  val normalize : 'term operations -> Thm.thm -> 'term ->
    {term:'term,converted:bool}
  val reduces : 'term operations -> Thm.thm -> 'term -> bool
end
