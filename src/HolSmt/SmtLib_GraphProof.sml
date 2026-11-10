(* Copyright (c) 2026 The HOL4 contributors. *)
structure SmtLib_GraphProof :> SmtLib_GraphProof =
struct
  open SmtLib_GraphFrontend SmtReplayGraph
  structure F = SmtLib_GraphFrontend
  structure G = SmtReplayGraph
  type versions = {requested : string, resolved : string}
  datatype 'proof packet = Packet of
    {proof : 'proof, graph : G.graph, scope : G.scope, solver : string,
     versions : versions, variables : F.solver_variable list,
     private_bindings : F.private_binding list, close : unit -> unit}
  val ERR = Feedback.mk_HOL_ERR "SmtLib_GraphProof"
  fun new {reader : F.reader, proof, requested_version, close} =
    let
      val graph = #graph reader
      val _ = G.validate_scope graph (#scope reader)
      val variables = (#solver_variables reader) ()
      val bindings = (#private_bindings reader) ()
      fun owned_variable ({node, lexical, scope} : F.solver_variable) =
        (if Type.compare (G.type_of graph node, Term.type_of lexical) = EQUAL
           andalso G.node_scope graph node = scope then () else
           raise ERR "new" "incompatible solver-variable descriptor";
         case G.view graph node of G.Variable (G.SolverFlexible, _) => ()
           | _ => raise ERR "new" "solver inventory contains a rigid node")
      fun binding ({scope, marker, source, ...} : F.private_binding) =
        (if G.node_scope graph marker = scope then () else
           raise ERR "new" "private marker scope mismatch";
         (case G.view graph marker of
            G.Variable (G.SolverFlexible, _) => ()
          | _ => raise ERR "new" "private marker is not solver-flexible");
         Option.app (fn node => ignore (G.type_of graph node)) source)
      val _ = List.app owned_variable variables
      val _ = List.app binding bindings
      val closed = ref false
      fun finish () = if !closed then () else (closed := true; close ())
    in Packet {proof = proof, graph = graph, scope = #scope reader,
      solver = #solver reader,
      versions = {requested = requested_version, resolved = #version reader},
      variables = variables, private_bindings = bindings, close = finish} end
  fun proof (Packet {proof, ...}) = proof
  fun graph (Packet {graph, ...}) = graph
  fun scope (Packet {scope, ...}) = scope
  fun solver (Packet {solver, ...}) = solver
  fun versions (Packet {versions, ...}) = versions
  fun variables (Packet {variables, ...}) = variables
  fun private_bindings (Packet {private_bindings, ...}) = private_bindings
  fun close (Packet {close, ...}) = close ()
end
