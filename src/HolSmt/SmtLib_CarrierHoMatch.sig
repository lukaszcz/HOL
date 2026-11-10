(* Higher-order matching DATA; no theorem, Source or normalization receipt. *)
signature SmtLib_CarrierHoMatch =
sig
  datatype 'term view =
      Variable
    | Constant of {name:string,theory:string}
    | Application of 'term * 'term
    | Abstraction of 'term * 'term
  type 'term substitution = {redex:'term,residue:'term} list
  type type_substitution =
    {redex:Type.hol_type,residue:Type.hol_type} list
  type 'term operations =
    {view:'term -> 'term view,type_of:'term -> Type.hol_type,
     same:'term * 'term -> bool,free_variables:'term -> 'term list,
     substitute:'term substitution -> 'term -> 'term,
     instantiate_type:type_substitution -> 'term -> 'term,
     variable_with_type:'term * Type.hol_type -> 'term,
     fresh_variable:Type.hol_type -> 'term,
     dummy_variable:Type.hol_type -> 'term,
     application:'term * 'term -> 'term,
     abstraction:'term * 'term -> 'term,
     key:'term -> int,guard:'term -> unit,alive:unit -> unit,step:unit -> unit,
     is_mismatch:exn -> bool}
  exception Mismatch of string
  type 'term result =
    {beta_counts:{redex:'term,residue:int} list,
     terms:'term substitution,types:type_substitution}

  (* These are the HolKernel matching algorithms, over a supplied algebra.
     substitute must be simultaneous, capture avoiding Term.subst;
     instantiate_type must match Term.inst, including binder avoidance.
     same must be typed alpha equality with exact external variable identity.
     variable_with_type keeps that variable's identity/name at its new type.
     dummy_variable uses ONE private dummy identity at every supplied type.
     is_mismatch classifies shape/matching failures only; authentication,
     native primary exceptions and resource failures must escape unchanged.

     Keys are per-live-algebra syntax identities, not alpha/proof authority.
     Guards precede beta memo lookup and validate retained results. Memo is
     local to each call; exceptions are never cached. All constructors and
     observations must retain authentic Query carriers and their lifetime.

     This is ho_match_term, NOT Drule.HO_PART_MATCH: the latter additionally
     repairs theorem binder names/bound-to-abs substitutions and applies
     its captured BETA_VAR plans. Arbitrary full beta normalization of an
     instantiated theorem is not a replacement for those plans. Rewrite
     counters, Cond_rewr orientation and candidate order belong to the
     enclosing simplifier, not this pure per-match operation. *)
  val match : 'term operations ->
    {rigid_types:Type.hol_type list,rigid_variables:'term list,
     pattern:'term,target:'term} -> 'term result
  (* The distinct Term.match_terml branch used by HO_PART_MATCH when the
     captured theorem body has no function-typed free variables. *)
  val match_first_order : 'term operations ->
    {rigid_types:Type.hol_type list,rigid_variables:'term list,
     pattern:'term,target:'term} ->
    {terms:'term substitution,types:type_substitution}
  val beta_normalise : 'term operations -> 'term -> 'term
  val all_abconv : 'term operations -> 'term list * 'term list -> bool
end
