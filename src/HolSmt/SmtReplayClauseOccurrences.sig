(* Pure ordered occurrence metadata; never theorem or Source authority. *)
signature SmtReplayClauseOccurrences =
sig
  val alignment_mapping :
    (('literal -> int option) -> 'literal list -> int option list) ->
    ('literal -> 'falsity -> bool) -> 'falsity ->
    ('literal -> 'destination -> int option) -> 'destination ->
    'literal list -> int option list
end
