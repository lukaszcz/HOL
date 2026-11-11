(* Preserve the exact public requirement datatype, including constructors,
   while the sparse instance seals its distinct private plan and result.
   Written as an explicit sig ... end body: the help indexer (makebase)
   only parses that form and loops on a bare signature abbreviation. *)
signature SmtReplaySparseValueRealization =
sig
  include SmtReplayValueRealization
    where type requirement = SmtReplayValueRealization.requirement
end
