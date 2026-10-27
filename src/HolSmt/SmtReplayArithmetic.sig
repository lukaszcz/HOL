(* Bounded operator obligations for the existing checked arithmetic workers. *)
signature SmtReplayArithmetic =
sig
  (* Invocation-local syntax admission with the original primitive-Type
     allowance/diagnostic, without evaluating word dimensions. *)
  val new_type_check : (unit -> unit) -> Type.hol_type -> unit
  val has_numeric_operand : SmtReplayGraph.graph -> SmtReplayGraph.scope ->
    {inputs:SmtReplayGraph.node list,observe:unit -> unit} -> bool
  (* The procedure receives complete, bounded operator syntax, with one typed
     hole per graph operand. Binder syntax uses a separately admitted bounded
     variable-only schema. It must return a closed, clean Boolean theorem
     over those holes. No source assignment
     or native graph substitution is available to the procedure. *)
  val prove : SmtReplayGraph.graph -> SmtReplayGraph.scope ->
    {inputs : SmtReplayGraph.node list, template_limit : int,
     observe : IntInf.int -> unit, procedure : Term.term list -> Thm.thm} ->
    {theorem : Thm.thm, node : SmtReplayGraph.node}
end
