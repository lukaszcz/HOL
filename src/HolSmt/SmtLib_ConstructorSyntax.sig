(* Ordinary-source metadata, not a semantic graph or proof API. *)
signature SmtLib_ConstructorSyntax =
sig
  type syntax
  (* Native and template free variables are lexical Variable leaves.
     Only explicit private_atom operands introduce private Atom leaves.
     Private atoms are never bound, renamed, or substituted by a lexical
     namesake, even at the same type. Constants are Atom leaves; compound
     native fragments are opened only as source syntax, never assembled
     from synthetic operands. Atom descriptors confer no proof authority. *)
  datatype view = Variable of Term.term | Atom of Term.term
                | Apply of syntax * syntax
                | Abstract of Term.term * syntax

  val identity : syntax -> IntInf.int
  val view : (IntInf.int -> unit) -> syntax -> view
  val dest_comb : (IntInf.int -> unit) -> syntax ->
    (syntax * syntax) option
  (* Lexical dependencies only; private atom names are not free variables. *)
  val free_variables : (IntInf.int -> unit) -> syntax -> Term.term list
  (* Charged, query-local source alpha comparison. Private atoms compare
     only with atoms, independently of lexical binder environments. *)
  val aconv : (IntInf.int -> unit) -> syntax * syntax -> bool

  val native : Term.term -> syntax
  val variable : Term.term -> syntax
  (* An explicitly generated free marker, disjoint from lexical domains. *)
  val private_atom : Term.term -> syntax
  val application : syntax * syntax -> syntax
  val abstraction : Term.term * syntax -> syntax
  (* Retains the caller-admitted native template and shares operand syntax;
     validates only hole variables and list arity, not the template body.
     Source queries expand it locally, charging their observation callback.
     Non-hole free variables stay lexical, as in native source syntax.
     Holes are inserted under named template binders. A source lexical body
     may intentionally refer to those same binder descriptors; other operand
     variables must be fresh for the template binders. *)
  val from_template :
    {template : Term.term, holes : Term.term list,
     operands : syntax list} -> syntax
  (* Capture-avoiding ordinary substitution, retaining stored binder names.
     The operand-variable query is shared and charged before expansion. *)
  val from_substitution : (IntInf.int -> unit) ->
    {template : Term.term, holes : Term.term list,
     operands : syntax list} -> syntax
  (* Existing native source fragment only: NEVER materializes a syntax
     application/binder/LET. A returned variable may describe a private
     atom; use view to determine lexical provenance. The caller must admit
     the returned fragment before an index callback can inspect it. *)
  val retained_native : (IntInf.int -> unit) -> syntax -> Term.term option
  (* The native numeral grammar, observed on source syntax without either
     evaluating LETs or projecting semantic graph values. *)
  val is_numeric_literal : (IntInf.int -> unit) -> syntax -> bool
  (* Match CPC's post-term LET normalization on the syntax DAG. Original
     native Source atoms stay atomic; no semantic operand is projected. *)
  val normalize_lets : (IntInf.int -> unit) -> syntax -> syntax
  val is_constant : (IntInf.int -> unit) -> Term.term -> syntax -> bool
  val let_expression : (Term.term * syntax) list * syntax -> syntax

  val contains_constant : (IntInf.int -> unit) ->
    {Thy : string, Name : string} -> syntax -> bool
  (* Repeated ordinary dest_abs, NOT Term.strip_abs's simultaneous naming. *)
  val strip_abs : (IntInf.int -> unit) -> syntax -> Term.term list * syntax
  (* Includes private atom names and stored binders for freshness. *)
  val all_variables : (IntInf.int -> unit) -> syntax list -> Term.term list
  val type_of : syntax -> Type.hol_type

  (* Ordinary qualified application observes one abstraction, then performs
     capture-avoiding source substitution. Operands remain shared syntax,
     never native terms. These are observations, not proof authority. *)
  val dest_abs : (IntInf.int -> unit) -> syntax ->
    (Term.term * syntax) option
  (* Replaces lexical free variables only, never private atoms. *)
  val substitute : (IntInf.int -> unit) ->
    (Term.term * syntax) list -> syntax -> syntax
end
