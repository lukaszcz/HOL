(* Optional actual closed-constructor rung; no descriptor/Source authority. *)
signature CPC_GraphClosedPrivateComponent =
sig
  val admit : int -> Term.term -> bool
  val prove :
    {target : Term.term,limit : int,check_type : Type.hol_type -> unit} ->
    Thm.thm option
end
