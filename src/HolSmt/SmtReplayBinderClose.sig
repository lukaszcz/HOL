(* The existing bounded binder-equality native worker, without admission. *)
signature SmtReplayBinderClose =
sig
  datatype kind = Forall | Exists | Lambda
  (* Callers establish actual input/Hyp/Type/output quotas and authentic
     binder ownership before this fixed kernel programme. No syntax or
     Source authority is inferred from the supplied metadata. *)
  val run : ('variable -> Term.term) ->
    {entries:(kind * 'variable) list,theorem:Thm.thm,
     target:unit -> Term.term} ->
    Thm.thm
end
