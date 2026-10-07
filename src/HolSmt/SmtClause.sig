(* Ordered, kernel-checked Boolean clause occurrences. *)
signature SmtClause =
sig
  type clause
  val term : Term.term list -> Term.term
  val from_literals : Term.term list -> Thm.thm -> clause
  val literals : clause -> Term.term list
  val theorem : clause -> Thm.thm
  val contains : Term.term -> clause -> bool
  val resolve : Term.term -> clause -> clause -> clause option
  val resolve_or_weaken : Term.term -> clause -> clause -> clause
  val resolve_chain :
    {pivots : Term.term list, premises : clause list,
     target : Term.term list option} -> clause option
  val align : Term.term list -> clause -> clause option
  val factor : clause -> clause
  (* Every bridge is closed and checked at its exact literal endpoints.
     Reuse and eviction affect conversion work, never proof availability. *)
  val new_normalizer_using :
    {reuse : bool, capacity : int, conversion : Conv.conv} ->
    (Term.term list -> Term.term list * Thm.thm)
  val new_normalizer : Conv.conv ->
    (Term.term list -> Term.term list * Thm.thm)
end
