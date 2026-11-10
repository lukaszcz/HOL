signature SmtReplaySchemaBuilder =
sig
  type context
  val new_context : unit -> context
  val new_recent_context : unit -> context
  val application : context -> Term.term * Term.term -> Term.term
  val stats_for_test : context -> {entries:int, retained_nodes:int}
  (* One synchronous traversal with a stable resolver and declaration
     lifetime. Only completed physical IDs are retained. *)
  val node_ids_for_call : (Term.term -> int) -> Term.term -> int
  (* Positive physical hints for one owning replay declaration epoch.
     Reset this wrapper together with the resolver on signature changes. *)
  val node_ids_for_recent_replay :
    (Term.term -> int option) -> Term.term -> int option
  val node_ids_for_replay :
    (Term.term -> int option) -> Term.term -> int option
end
