(* Copyright (c) 2026 The HOL4 contributors. *)
structure SmtReplayDefinitionEnvironment :> SmtReplayDefinitionEnvironment =
struct
  structure G = SmtReplayGraph
  structure U = SmtReplayUnify
  structure R = SmtReplayResolve
  val ERR = Feedback.mk_HOL_ERR "SmtReplayDefinitionEnvironment"
  type definition =
    {occurrence : int, stored : G.node, variable : G.node,
     residue : G.node, name_on_left : bool}
  datatype selection = Empty | Reflexive of definition list
    | Leaf of {variable : G.node, anchor : definition,
               definitions : definition list}
    | DuplicateSCC of
        {variable : G.node, anchor : definition, definitions : definition list,
         component : G.node list}
    | Unresolved of {definitions : int, variables : int, direct_self : int}
  datatype outcome = Resolved of R.resolution | RequiresWitness of selection
    | UnificationRefused of U.failure | ResolutionRefused of R.failure
  datatype environment = Environment of
    {graph : G.graph, scope : G.scope, allocated : G.node list,
     sources : G.node list, needed : G.node list, roots : G.node list,
     definitions : definition list, selection : selection}
  datatype task = Enter of int | Leave of int
  fun empty () = Redblackmap.mkDict Int.compare
  fun set () = Redblackset.empty Int.compare
  fun member ids node = Redblackset.member (ids,G.node_id node)
  fun need ok message = if ok then () else raise ERR "prepare" message
  fun visible graph scope node =
    need (G.scope_visible graph scope (G.node_scope graph node))
      "foreign or retired definition environment node"
  fun get table id = case Redblackmap.peek (table,id) of
      SOME nodes => nodes | NONE => []
  fun equation graph node = case G.view graph node of
      G.Application (inner,right) =>
        (case G.view graph inner of G.Application (head,left) =>
           (case G.view graph head of G.Constant _ =>
              if Term.same_const (G.representative graph head)
                  boolSyntax.equality then SOME (left,right) else NONE
            | _ => NONE)
         | _ => NONE)
    | _ => NONE

  (* Iterative Kosaraju; both traversals visit each ID/edge once. *)
  fun visit [] adjacency seen order = (seen,order)
    | visit (Leave id :: rest) adjacency seen order =
        visit rest adjacency seen (id :: order)
    | visit (Enter id :: rest) adjacency seen order =
        if Redblackset.member (seen,id) then visit rest adjacency seen order
        else visit (List.map Enter (get adjacency id) @ Leave id :: rest)
          adjacency (Redblackset.add (seen,id)) order
  fun components names adjacency =
    let
      val (_,order) = List.foldl
        (fn (id,(seen,order)) => visit [Enter id] adjacency seen order)
        (set (),[]) names
      val reversed = Redblackmap.foldl
        (fn (id,children,table) => List.foldl
          (fn (child,table) => Redblackmap.insert
            (table,child,id :: get table child)) table children)
        (empty ()) adjacency
      fun collect (id,(seen,table)) =
        if Redblackset.member (seen,id) then (seen,table)
        else let
          val (seen,part) = visit [Enter id] reversed seen []
          val part_set = Redblackset.addList (set (),part)
          val table = List.foldl
            (fn (member,table) => Redblackmap.insert (table,member,part_set))
            table part
        in (seen,table) end
    in #2 (List.foldl collect (set (),empty ()) order) end

  fun prepare graph {scope,allocated,sources,needed,roots} =
    let
      val _ = G.validate_scope graph scope
      val _ = List.app (visible graph scope) (allocated @ sources @ roots)
      val allocated_ids = Redblackset.addList
        (set (),List.map G.node_id allocated)
      val _ = need (Redblackset.numItems allocated_ids = List.length allocated)
        "duplicate allocation declaration"
      val _ = List.app (fn node => case G.view graph node of
          G.Variable (G.SolverFlexible,_) => ()
        | _ => raise ERR "prepare" "allocation is not SolverFlexible") allocated
      val _ = List.app (fn node => need
        (Type.compare (G.type_of graph node,Type.bool) = EQUAL)
        "Source is not Boolean") sources
      val source_ids = Redblackset.addList (set (),List.map G.node_id sources)
      val _ = List.app (fn node =>
        (visible graph scope node;
         need (member source_ids node) "needed node is not an actual Source"))
        needed
      val needed_ids = Redblackset.addList (set (),List.map G.node_id needed)
      fun row (occurrence,stored) =
        if not (member needed_ids stored) then NONE
        else case equation graph stored of
          NONE => NONE
        | SOME (left,right) =>
            if member allocated_ids left then SOME
              {occurrence = occurrence,stored = stored,variable = left,
               residue = right,name_on_left = true}
            else if member allocated_ids right then SOME
              {occurrence = occurrence,stored = stored,variable = right,
               residue = left,name_on_left = false}
            else NONE
      val rows = List.mapPartial row
        (ListPair.zip (List.tabulate (List.length sources,fn n => n),sources))
      val variables = List.foldl
        (fn ({variable,...} : definition,table) =>
          Redblackmap.insert (table,G.node_id variable,variable))
        (empty ()) rows
      val names = List.map #1 (Redblackmap.listItems variables)
      val residue_cache = ref (empty ())
      fun dependencies residue =
        case Redblackmap.peek (!residue_cache,G.node_id residue) of
          SOME ids => ids
        | NONE => let
            val free = case G.free_variable_nodes graph residue of
                SOME nodes => nodes
              | NONE => raise ERR "prepare" "unknown opaque/binder dependencies"
            val ids = List.map G.node_id (List.filter (fn node =>
              Option.isSome (Redblackmap.peek (variables,G.node_id node))) free)
            val _ = residue_cache := Redblackmap.insert
              (!residue_cache,G.node_id residue,ids)
          in ids end
      val by_name = List.foldl
        (fn (row as {variable,residue,...} : definition,table) =>
          let val id = G.node_id variable in Redblackmap.insert
            (table,id,(row,dependencies residue) :: get table id) end)
        (empty ()) rows
      (* Restore the original occurrence order in every indexed bucket. *)
      val by_name = Redblackmap.map (fn (_,entries) => List.rev entries) by_name
      val adjacency = Redblackmap.map (fn (_,entries) =>
        Redblackset.listItems (List.foldl
          (fn ((_,ids),seen) => Redblackset.addList (seen,ids))
          (set ()) entries))
        by_name
      val referenced = Redblackmap.foldl
        (fn (_,ids,seen) => Redblackset.addList (seen,ids)) (set ()) adjacency
      val identities = List.filter
        (fn ({variable,residue,...} : definition) => variable = residue) rows
      fun definitions id = List.map #1 (get by_name id)
      val leaves = List.filter (fn id =>
        not (Redblackset.member (referenced,id))) names
      val choice = if List.null rows then Empty
        else if not (List.null identities) then Reflexive identities
        else case leaves of id :: _ => Leaf
          {variable = Redblackmap.find (variables,id),
           anchor = List.hd (definitions id),definitions = definitions id}
        | [] => let
            val parts = components names adjacency
            fun self id = Redblackset.member
              (Redblackset.addList (set (),get adjacency id),id)
            fun distinct_definitions id = Redblackset.numItems
              (Redblackset.addList (set (),List.map
                (fn (row : definition,_) => G.node_id (#stored row))
                (get by_name id)))
            fun candidate id =
              if self id orelse distinct_definitions id <= 1 then NONE
              else let val part = Redblackmap.find (parts,id) in
                case List.find (fn (_,ids) => List.all
                    (fn dependency =>
                      not (Redblackset.member (part,dependency)))
                    ids) (get by_name id) of
                  SOME (anchor,_) => SOME (id,anchor,part)
                | NONE => NONE
              end
          in case List.mapPartial candidate names of
              (id,anchor,part) :: _ => DuplicateSCC
                {variable = Redblackmap.find (variables,id),anchor = anchor,
                 definitions = definitions id,component = List.map
                   (fn member => Redblackmap.find (variables,member))
                   (Redblackset.listItems part)}
            | [] => Unresolved {definitions = List.length rows,
                variables = List.length names,
                direct_self = List.length (List.filter self names)}
          end
    in Environment {graph = graph,scope = scope,allocated = allocated,
      sources = sources,needed = needed,roots = roots,definitions = rows,
      selection = choice} end

  fun active (Environment {graph,scope,allocated,sources,roots,...}) =
    (G.validate_scope graph scope;
     List.app (visible graph scope) (allocated @ sources @ roots))
  fun definitions (env as Environment {definitions,...}) =
    (active env;definitions)
  fun sources (env as Environment {sources,...}) = (active env;sources)
  fun selection (env as Environment {selection,...}) = (active env;selection)

  fun resolve_internal (env as Environment
      {graph,scope,allocated,sources,needed,roots,definitions,selection})
      preserved closed only_needed =
    let
      val _ = active env
      val _ = List.app (visible graph scope) preserved
      val permitted = case closed of NONE => set () | SOME laws =>
        let val original_ids = Redblackset.addList
              (set (),List.map G.node_id sources)
        in List.foldl (fn ((node,proof),ids) =>
          let
            val _ = visible graph scope node
            val (tags,_) = Tag.dest_tag (Thm.tag proof)
            val _ = if member original_ids node andalso
                List.null (Thm.hyp proof) andalso
                List.all (fn tag => tag = "DISK_THM") tags andalso
                List.null (Tag.axioms_of (Thm.tag proof)) andalso
                Portable.pointer_eq (Thm.concl proof,
                  G.representative graph node) then () else
              raise ERR "resolve" "closed original Source witness differs"
          in Redblackset.add (ids,G.node_id node) end) (set ()) laws end
      fun run () = case U.unify graph
          {scope = scope,flexible = allocated,equations = List.map
            (fn ({variable,residue,...} : definition) => (variable,residue))
            definitions} of
          U.NoMatch failure => UnificationRefused failure
        | U.Unified result => let
            val _ = U.validate_result graph scope result
            val stored = List.map #stored definitions
            val selected = Redblackset.addList
              (set (),List.map G.node_id stored)
            val relevant = if not only_needed then sources else needed
            val stable = List.filter (fn node =>
              not (member selected node) andalso
              not (member permitted node)) relevant
          in case R.prepare graph scope
              {flexible = allocated,assignments = U.assignments result,
               roots = roots @ sources @ U.roots result,
               preserved = preserved @ stable} of
              R.Refused failure => ResolutionRefused failure
            | R.Resolved resolution =>
                Resolved (R.record_assignment_sources resolution stored)
          end
    in case selection of Empty => run () | Leaf _ => run ()
      | _ => RequiresWitness selection end
  fun resolve env {preserved} = resolve_internal env preserved NONE false
  fun resolve_with_closed_sources env {preserved,laws} =
    resolve_internal env preserved (SOME laws) false
  fun resolve_needed_with_closed_sources env {preserved,laws} =
    resolve_internal env preserved (SOME laws) true
  (* Bounded, explicit opt-in. Pure variable cycles use actual U orientation;
     an unassigned reflexivity remains an ordinary closed Source witness. *)
  fun resolve_checked_variables_internal only_needed
      (env as Environment
      {graph,scope,allocated,sources,needed,roots,definitions,selection})
      {preserved,laws,admission = {metric,limit,check_type}} =
    let
      val _ = active env
      val _ = List.app (visible graph scope) preserved
      val allocated_ids = Redblackset.addList
        (set (),List.map G.node_id allocated)
      fun flexible node = member allocated_ids node andalso
        (case G.view graph node of G.Variable (G.SolverFlexible,_) => true
         | _ => false)
      fun variable_pair ({variable,residue,...} : definition) =
        flexible variable andalso flexible residue
      val reflexive = List.filter
        (fn ({variable,residue,...} : definition) => variable = residue)
        definitions
      val ordinary = List.filter
        (fn ({variable,residue,...} : definition) => variable <> residue)
        definitions
      (* Reflexivity is a closed obligation, not a dependency edge. Decide
         the remaining portfolio after removing just those exact Sources. *)
      val Environment {selection = remaining_selection,...} =
        prepare graph {scope = scope,allocated = allocated,
        sources = sources,needed = List.filter (fn node => not (List.exists
          (fn (row : definition) => #stored row = node) reflexive)) needed,
        roots = roots}
      val supported = case remaining_selection of
          Empty => true | Leaf _ => true
        | _ => List.all variable_pair ordinary
      fun run () =
        let
          val source_ids = Redblackset.addList
            (set (),List.map G.node_id sources)
          fun validate_law ((node,proof),permitted) =
            let
              val _ = visible graph scope node
              val (tags,_) = Tag.dest_tag (Thm.tag proof)
              val _ = if member source_ids node andalso
                  List.null (Thm.hyp proof) andalso
                  List.all (fn tag => tag = "DISK_THM") tags andalso
                  List.null (Tag.axioms_of (Thm.tag proof)) andalso
                  Portable.pointer_eq (Thm.concl proof,
                    G.representative graph node) then () else raise ERR
                "resolve_checked_variables" "closed original Source differs"
            in Redblackset.add (permitted,G.node_id node) end
          val original_permitted =
            List.foldl validate_law (set ()) laws
          val _ = if limit > 0 then () else
            raise ERR "resolve_checked_variables" "nonpositive witness limit"
          (* All new REFL/ALPHA operands are admitted before type callbacks. *)
          val operands = List.map #stored reflexive
          val _ = List.app (fn node =>
            case G.unfolded_nodes graph metric limit node of SOME size =>
                if size <= limit then () else raise ERR
                  "resolve_checked_variables" "reflexive witness exceeds limit"
              | NONE => raise ERR "resolve_checked_variables"
                  "unknown reflexive witness size") operands
          val _ = List.app (check_type o G.type_of graph)
            (G.reachable graph operands)
          val _ = active env
          fun witness ({stored,variable,...} : definition) =
            let
              val proof = Thm.REFL (G.representative graph variable)
              val proof = Thm.EQ_MP (Thm.ALPHA (Thm.concl proof)
                (G.representative graph stored)) proof
            in (stored,proof) end
          val reflexive_sources = List.map witness reflexive
          val permitted = List.foldl validate_law
            original_permitted reflexive_sources
          val selected = Redblackset.addList
            (set (),List.map (G.node_id o #stored) ordinary)
          val relevant = if only_needed then needed else sources
          val stable = List.filter (fn node =>
            not (member selected node) andalso not (member permitted node))
            relevant
          val outcome = if not supported then RequiresWitness selection
            else case U.unify_with_binders graph
              (fn (left,right) => Option.map
                SmtReplayUnifyBinder.assignments
                (SmtReplayUnifyBinder.discover_raw graph scope
                  {left=left,right=right,flexible=allocated,limit=limit}))
              {scope = scope,binders=[],
              flexible = allocated,equations = List.map
                (fn ({variable,residue,...} : definition) =>
                  (variable,residue)) definitions} of
              U.NoMatch failure => UnificationRefused failure
            | U.Unified result =>
                (U.validate_result graph scope result;
                 case R.prepare_using graph scope
                     (fn {node,resolve} =>
                       let
                         val (normalized,_) =
                           SmtReplayUnifyBinder.normalize_raw graph scope
                             {node=node,resolve=resolve,limit=limit}
                         (* Reuse bounded alpha admission across separately
                            cloned lexical frames. IDs alone cannot identify
                            two normalized lambda spellings. *)
                       in SOME (#node (G.admit_binder graph scope limit
                         (G.representative graph normalized))) end)
                     {flexible = allocated,
                     assignments = U.assignments result,
                     roots = roots @ sources @ U.roots result,
                     preserved = preserved @ stable} of
                   R.Refused failure => ResolutionRefused failure
                 | R.Resolved resolution => Resolved
                     (R.record_assignment_sources resolution
                       (List.map #stored ordinary)))
        in {outcome = outcome,reflexive_sources = reflexive_sources} end
    in run () end
  fun resolve_checked_variables env request =
    resolve_checked_variables_internal false env request
  fun resolve_needed_checked_variables env request =
    resolve_checked_variables_internal true env request
end
