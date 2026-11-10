(* Copyright (c) 2026 The HOL4 contributors. *)
structure SmtReplayDependencies :> SmtReplayDependencies =
struct
  open SmtReplayGraph
  structure G = SmtReplayGraph

  fun graph_summary {graph, root, admit_binder} =
    let
      val memo = ref (Redblackmap.mkDict Int.compare)
      fun admitted node =
        case Redblackmap.peek (!memo, G.node_id node) of
          SOME saved => saved
        | NONE =>
            let
              val saved = case G.view graph node of
                  G.Application (left, right) =>
                    G.application graph (G.node_scope graph node)
                      (admitted left, admitted right)
                | G.OpaqueRetained =>
                    let val term = G.representative graph node in
                      case admit_binder term of
                        NONE => node
                      | SOME limit => #node (G.admit_binder graph
                          (G.node_scope graph node) limit term)
                    end
                | _ => node
              val _ = memo := Redblackmap.insert
                (!memo, G.node_id node, saved)
            in saved end
    in G.free_variables graph (admitted root) end

  fun source_summary {dag_limit, admit_binder} term =
    let
      val graph = G.new ()
      val source = G.import graph (G.root_scope graph) dag_limit term
    in graph_summary
      {graph = graph, root = #node source, admit_binder = admit_binder} end

  fun source_presence {dag_limit, admit_binder} term =
    let
      val graph = G.new ()
      val source = G.import graph (G.root_scope graph) dag_limit term
      fun exposed ([], _) = false
        | exposed (node :: pending, seen) =
            if Redblackset.member (seen, G.node_id node) then
              exposed (pending, seen)
            else
              let val seen = Redblackset.add (seen, G.node_id node) in
                case G.view graph node of
                    G.Variable (G.RigidSource, _) => true
                  | G.Application (left, right) =>
                      exposed (left :: right :: pending, seen)
                  (* Binder bodies have their own lexical frame. Even an
                     admitted body's Bound IDs are not source witnesses. *)
                  | _ => exposed (pending, seen)
              end
    in
      if exposed ([#node source], Redblackset.empty Int.compare) then
        SOME true
      else case graph_summary
          {graph = graph, root = #node source, admit_binder = admit_binder} of
          G.Known variables => SOME (not (List.null variables))
        | G.Unknown => NONE
    end
end
