(* Copyright (c) 2026 The HOL4 contributors. *)
signature SmtReplayClosedSourceImages =
sig
  type admission =
    {metric : SmtReplayGraph.metric, limit : int,
     check_type : Type.hol_type -> unit}
  (* Entire actual original/current participating portfolio is bounded before
     type callbacks and INST. Only checked CLOSED original laws are imaged;
     indices retain original Source occurrences. Opaque dependencies decline.
     This instantiates each bounded local law, never the replay theorem. *)
  val prepare : SmtReplayGraph.graph ->
    {scope : SmtReplayGraph.scope,
     resolution : SmtReplayResolve.resolution,
     sources : SmtReplayGraph.node list, laws : (int * Thm.thm) list,
     admission : admission} -> (int * Thm.thm) list
end
