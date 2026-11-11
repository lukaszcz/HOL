(* Copyright (c) 2026 The HOL4 contributors. *)
signature SmtLib_GraphProof =
sig
  type 'proof packet
  type versions = {requested : string, resolved : string}
  (* A packet retains parser ownership metadata; it certifies no inference. *)
  val new :
    {reader : SmtLib_GraphFrontend.reader, proof : 'proof,
     requested_version : string, close : unit -> unit} -> 'proof packet
  val proof : 'proof packet -> 'proof
  val graph : 'proof packet -> SmtReplayGraph.graph
  val scope : 'proof packet -> SmtReplayGraph.scope
  val solver : 'proof packet -> string
  val versions : 'proof packet -> versions
  val variables : 'proof packet -> SmtLib_GraphFrontend.solver_variable list
  val private_bindings : 'proof packet ->
    SmtLib_GraphFrontend.private_binding list
  val close : 'proof packet -> unit
end
