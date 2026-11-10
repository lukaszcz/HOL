(* SAME exact occurrence map used by the native clause alignment. *)
structure SmtReplayClauseOccurrences :> SmtReplayClauseOccurrences =
struct
  fun alignment_mapping map same falsity find destination source_literals =
    map(fn literal=>if same literal falsity then SOME(~1)
      else find literal destination)source_literals
end
