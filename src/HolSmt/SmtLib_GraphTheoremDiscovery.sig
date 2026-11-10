(* Copyright (c) 2026 The HOL4 contributors. *)
signature SmtLib_GraphTheoremDiscovery =
sig
  type discovery
  (* Exact stock constant selector over admitted constructor IDs. This does
     not claim parity with get_thms recursive num-transfer normalization. *)
  val discover : SmtReplayGraph.graph -> SmtReplayGraph.scope ->
    {roots : SmtReplayGraph.node list, input_limit : int,
     template_limit : int, check_type : Type.hol_type -> unit} -> discovery
  (* Exact selected stock theorem identities must already have genuine
     bounded graph binder records. Missing records remain explicit gaps. *)
  val discover_recorded_laws : SmtReplayGraph.graph ->
    SmtReplayGraph.scope ->
    {roots : SmtReplayGraph.node list, input_limit : int,
     template_limit : int, check_type : Type.hol_type -> unit,
     records : SmtReplayProof.closed_fact list} -> discovery
  val facts : discovery -> SmtLib_GraphSourcePortfolio.fact list
  val gaps : discovery -> (SmtReplayGraph.node * string) list
end
