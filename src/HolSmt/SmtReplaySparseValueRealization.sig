(* Preserve the exact public requirement datatype, including constructors,
   while the sparse instance seals its distinct private plan and result. *)
signature SmtReplaySparseValueRealization =
  SmtReplayValueRealization
    where type requirement=SmtReplayValueRealization.requirement
