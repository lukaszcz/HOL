(* Ordinary-source metadata, not a term encoding, equality, or proof API. *)
signature SmtLib_ConstructorSyntax =
sig
  type syntax

  val native : Term.term -> syntax
  val variable : Term.term -> syntax
  val application : syntax * syntax -> syntax
  val abstraction : Term.term * syntax -> syntax
  (* Retains the caller-admitted native template and shares operand syntax;
     validates only hole variables and list arity, not the template body.
     Source queries expand it locally, charging their observation callback.
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
  val is_constant : (IntInf.int -> unit) -> Term.term -> syntax -> bool
  val let_expression : (Term.term * syntax) list * syntax -> syntax

  val contains_constant : (IntInf.int -> unit) ->
    {Thy : string, Name : string} -> syntax -> bool
  (* Repeated ordinary dest_abs, NOT Term.strip_abs's simultaneous naming. *)
  val strip_abs : (IntInf.int -> unit) -> syntax -> Term.term list * syntax
  val all_variables : (IntInf.int -> unit) -> syntax list -> Term.term list
  val type_of : syntax -> Type.hol_type
end
