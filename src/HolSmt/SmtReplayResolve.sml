(* Copyright (c) 2026 The HOL4 contributors. *)
structure SmtReplayResolve :> SmtReplayResolve =
struct
  open SmtReplayGraph SmtReplayUnify
  structure G = SmtReplayGraph
  val ERR = Feedback.mk_HOL_ERR "SmtReplayResolve"
  datatype failure = TypeMismatch | CyclicAssignments | EscapingScope
    | NeedsBinderAdmission | ChangedPreservedRoot
  datatype resolution = Resolution of
    {graph : G.graph, scope : G.scope,
     nodes : (int,G.node) Redblackmap.dict,
     roots : G.node list, assignments : G.node list,
     assignment_ids : int Redblackset.set,
     assigned_variables : int Redblackset.set}
  datatype outcome = Resolved of resolution | Refused of failure
  exception Refusal of failure
  fun active (Resolution {graph,scope,...}) = G.validate_scope graph scope
  fun validate graph scope (resolution as Resolution
      {graph = owner,scope = frame,...}) =
    (active resolution;G.validate_scope graph scope;
     if G.root_scope graph = G.root_scope owner andalso scope = frame then ()
     else raise ERR "validate" "resolution belongs to another graph/scope")
  fun roots (resolution as Resolution {roots,...}) =
    (active resolution;roots)
  fun assignment_sources (resolution as Resolution {assignments,...}) =
    (active resolution;assignments)
  fun node (resolution as Resolution {graph,nodes,...}) original =
    (active resolution;ignore (G.type_of graph original);
     case Redblackmap.peek (nodes,G.node_id original) of
         SOME result => result
       | NONE => raise ERR "node" "node outside recorded resolution")
  fun is_assignment_source
      (resolution as Resolution {graph,assignment_ids,...}) original =
    (active resolution;ignore (G.type_of graph original);
     Redblackset.member (assignment_ids,G.node_id original))

  fun record_assignment_sources
      (resolution as Resolution {graph,scope,nodes,roots,assignments,
                                 assignment_ids,assigned_variables}) sources =
    let
      val _ = active resolution
      fun assigned node =
        case G.view graph node of G.Variable (G.SolverFlexible,_) =>
            Redblackset.member (assigned_variables,G.node_id node)
          | _ => false
      fun endpoints source = case G.view graph source of
          G.Application (operator,right) =>
            (case G.view graph operator of G.Application (head,left) =>
               (case G.view graph head of G.Constant _ =>
                  if Term.same_const (G.representative graph head)
                      boolSyntax.equality then (left,right) else
                    raise ERR "record_assignment_sources"
                      "stored source is not an equality"
                | _ => raise ERR "record_assignment_sources"
                    "stored source is not an equality")
             | _ => raise ERR "record_assignment_sources"
                 "stored source is not an equality")
        | _ => raise ERR "record_assignment_sources"
            "stored source is not an equality"
      fun record (source,(recorded,ids)) =
        let
          val _ = ignore (node resolution source)
          val _ = if G.scope_visible graph scope (G.node_scope graph source)
            then () else raise ERR "record_assignment_sources"
              "stored source is outside the resolution scope"
          val (left,right) = endpoints source
          val _ = if assigned left orelse assigned right then () else
            raise ERR "record_assignment_sources"
              "stored source has no assigned solver endpoint"
          val _ = if node resolution left = node resolution right then () else
            raise ERR "record_assignment_sources"
              "stored definition does not resolve to reflexivity"
        in if Redblackset.member (ids,G.node_id source) then (recorded,ids)
          else (source :: recorded,Redblackset.add (ids,G.node_id source)) end
      val (recorded,ids) = List.foldl record ([],assignment_ids) sources
    in Resolution {graph = graph,scope = scope,nodes = nodes,roots = roots,
      assignments = assignments @ List.rev recorded,assignment_ids = ids,
      assigned_variables = assigned_variables} end

  fun prepare_using graph scope binder
      {flexible,assignments,roots,preserved} =
    let
      val _ = G.validate_scope graph scope
      fun visible node =
        if G.scope_visible graph scope (G.node_scope graph node) then ()
        else raise Refusal EscapingScope
      fun permission (node,table) =
        (visible node;
         case G.view graph node of G.Variable (G.SolverFlexible,_) =>
             Redblackset.add (table,G.node_id node)
           | _ => raise ERR "prepare" "permission to assign a rigid variable")
      val permitted = List.foldl permission
        (Redblackset.empty Int.compare) flexible
      fun assignment ({variable,residue},table) =
        let
          val _ = visible variable
          val _ = visible residue
          val _ = if Redblackset.member (permitted,G.node_id variable) then ()
            else raise ERR "prepare" "assignment outside permitted solver set"
          val _ = if G.type_id graph variable = G.type_id graph residue then ()
            else raise Refusal TypeMismatch
          val _ = if Redblackmap.inDomain (table,G.node_id variable) then
              raise ERR "prepare" "duplicate solver assignment"
            else ()
        in Redblackmap.insert (table,G.node_id variable,residue) end
      val substitutions = List.foldl assignment
        (Redblackmap.mkDict Int.compare) assignments
      val memo = ref (Redblackmap.mkDict Int.compare)
      val visiting = ref (Redblackset.empty Int.compare)
      fun scoped_residue variable residue =
        let
          val declaration = G.node_scope graph variable
          val variables = case G.free_variable_nodes graph residue of
              SOME variables => variables
            | NONE => raise Refusal NeedsBinderAdmission
        in List.app (fn free =>
          if G.scope_visible graph declaration (G.node_scope graph free)
          then () else raise Refusal EscapingScope) variables end
      fun resolve original =
        case Redblackmap.peek (!memo,G.node_id original) of
          SOME node => node
        | NONE =>
          let
            val _ = visible original
            val _ = if Redblackset.member (!visiting,G.node_id original) then
                raise Refusal CyclicAssignments
              else visiting := Redblackset.add (!visiting,G.node_id original)
            val result = case Redblackmap.peek
                (substitutions,G.node_id original) of
                SOME residue =>
                  (scoped_residue original residue;resolve residue)
              | NONE => case G.view graph original of
                  G.Application (operator,operand) =>
                    let val left = resolve operator
                        val right = resolve operand in
                      if left = operator andalso right = operand then original
                      else G.application graph scope (left,right) end
                | G.OpaqueRetained =>
                    if Redblackmap.numItems substitutions = 0 then original
                    else raise Refusal NeedsBinderAdmission
                | G.AdmittedBinder _ =>
                    let
                      val variables = case G.free_variable_nodes graph original
                        of SOME variables => variables
                         | NONE => raise Refusal NeedsBinderAdmission
                      val affected = List.exists (fn variable =>
                        Redblackmap.inDomain
                          (substitutions,G.node_id variable)) variables
                    in if affected then
                         (case binder {node = original,resolve = resolve} of
                              SOME result =>
                                (visible result;
                                 if G.type_id graph result =
                                    G.type_id graph original then result
                                 else raise Refusal TypeMismatch)
                            | NONE => raise Refusal NeedsBinderAdmission)
                       else original end
                | _ => original
            val _ = memo := Redblackmap.insert
              (!memo,G.node_id original,result)
            val _ = visiting := Redblackset.delete
              (!visiting,G.node_id original)
          in result end
      fun equality {variable,residue} =
        let
          val marker = Term.genvar (G.type_of graph variable)
          val operator = G.constant graph scope (Term.rator (Term.rator
            (boolSyntax.mk_eq (marker,marker))))
        in G.application graph scope
          (G.application graph scope (operator,variable),residue) end
      fun finish () =
        let
          val assignment_sources = List.map equality assignments
          val originals = G.block_reachable graph
            (roots @ preserved @ assignment_sources)
          (* Resolve assignments even if a caller supplied no reachable use. *)
          val _ = List.app (ignore o resolve o #variable) assignments
          val _ = List.app (ignore o resolve) originals
          val _ = List.app (fn original =>
            if resolve original = original then ()
            else raise Refusal ChangedPreservedRoot) preserved
          val resolved = List.map resolve originals
          (* Newly rebuilt constructors already contain resolved children. *)
          val nodes = List.foldl (fn (node,table) =>
            Redblackmap.insert (table,G.node_id node,node)) (!memo) resolved
        in Resolved (Resolution
          {graph = graph,scope = scope,nodes = nodes,
           roots = originals @ resolved,assignments = assignment_sources,
           assignment_ids = Redblackset.addList
             (Redblackset.empty Int.compare,
              List.map G.node_id assignment_sources),
           assigned_variables = Redblackset.addList
             (Redblackset.empty Int.compare,
              List.map #1 (Redblackmap.listItems substitutions))}) end
    in finish () end handle Refusal reason => Refused reason
  fun prepare graph scope input = prepare_using graph scope
    (fn _ => NONE) input
end
