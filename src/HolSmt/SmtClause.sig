(* Ordered, kernel-checked Boolean clause occurrences. *)
signature SmtClause =
sig
  type clause
  (* Same lower-engine domains on both benchmark builds; no Work credit.
     Selected returns are explicit kernel/library boundaries, not hidden
     primitive calls or the separate P.edge allocation domain. *)
  type clause_statistics =
    {clause_objects:IntInf.int,clause_accesses:IntInf.int,
     selected_proof_returns:IntInf.int,inst_calls:IntInf.int,
     schema_raw_nodes:IntInf.int,index_hits:IntInf.int,index_misses:IntInf.int}
  val with_clause_statistics : (unit -> 'a) -> 'a * clause_statistics
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
  (* Actual checked clause occurrence DATA, never original Source credit. *)
  type owned_witness
  val retain_with_work : SmtReplayInvocationWork.portfolio -> clause ->
    owned_witness
  val description_for : SmtReplayInvocationWork.portfolio -> owned_witness ->
    {theorem:Thm.thm,
     occurrences:{literal:Term.term,negative:bool,atom:Term.term} list}
end
