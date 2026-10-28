(* Bounded operator obligations for the existing checked arithmetic workers. *)
signature SmtReplayArithmetic =
sig
  (* Keep admission exceptions terminal through nested fallback ladders;
     restore the exact primary exception at the outermost consumer scope.
     Without an active scope, propagation raises the primary directly. *)
  val with_admission_errors : (unit -> 'a) -> 'a
  val propagate_admission_error : exn -> 'a
  (* Invocation-local syntax admission with the original primitive-Type
     allowance/diagnostic, without evaluating word dimensions. *)
  val new_type_check : (unit -> unit) -> Type.hol_type -> unit
  (* Complete native obligation admission, including buried annotations. *)
  val new_term_check : {limit:int,observe:unit -> unit} -> Term.term -> unit
  val has_numeric_operand : SmtReplayGraph.graph -> SmtReplayGraph.scope ->
    {inputs:SmtReplayGraph.node list,observe:unit -> unit} -> bool
  (* The procedure receives complete, bounded operator syntax, with one typed
     hole per graph operand. Binder syntax uses a separately admitted bounded
     variable-only schema. It must return a closed, clean Boolean theorem
     over those holes. No source assignment
     or native graph substitution is available to the procedure. *)
  (* Generated obligations must use this admission continuation BEFORE any
     generic proving. The continuation has this invocation's actual cap. *)
  val prove_admitted : SmtReplayGraph.graph -> SmtReplayGraph.scope ->
    {inputs : SmtReplayGraph.node list, template_limit : int,
     observe : IntInf.int -> unit,
     procedure : (Term.term -> unit) -> Term.term list -> Thm.thm} ->
    {theorem : Thm.thm, node : SmtReplayGraph.node}
  val prove : SmtReplayGraph.graph -> SmtReplayGraph.scope ->
    {inputs : SmtReplayGraph.node list, template_limit : int,
     observe : IntInf.int -> unit, procedure : Term.term list -> Thm.thm} ->
    {theorem : Thm.thm, node : SmtReplayGraph.node}
end
