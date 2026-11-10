(* Same typed Value cells; no caller metadata grants native proof rights. *)
signature SmtReplayValueInterpretation =
sig
  datatype cell_body = Borrowed of SmtReplayGraph.node
    | Atomic of Term.term | Application of (int * int) * (int * int)
  type cell =
    {key:int * int,name:Term.term,hol_type:Type.hol_type,body:cell_body}
  (* Direct already-held callbacks/map. The owner admits every actual
     native input/output and Type forest first. This function constructs
     no theorem, graph binder or original Source and opens no raw body. *)
  val interpret : (unit -> unit) -> (unit -> unit) ->
    SmtReplayGraph.graph -> SmtReplayGraph.scope ->
    (int * int -> Term.term * Type.hol_type) ->
    (Type.hol_type -> Type.hol_type -> bool) ->
    (int * int,Term.term * Type.hol_type) Redblackmap.dict ref ->
    (string -> string -> exn) -> cell list ->
    (Term.term,Term.term) Lib.subst -> (Term.term,Term.term) Lib.subst
end
