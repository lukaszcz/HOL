(* Copyright (c) 2026 The HOL4 contributors. *)
(* Checked resolved laws retain strict ordinary source validation. *)
structure SmtReplayResolvedLaw :> SmtReplayResolvedLaw =
struct
  open SmtReplayGraph SmtReplayResolve SmtReplayUnify
    SmtReplayUnifyPlan SmtReplayProof SmtReplayRules
  structure G = SmtReplayGraph
  structure R = SmtReplayResolve
  structure U = SmtReplayUnify
  structure N = SmtReplayUnifyPlan
  structure P = SmtReplayProof
  structure Rules = SmtReplayRules
  val ERR = Feedback.mk_HOL_ERR "SmtReplayResolvedLaw"
  type assignment =
    {stored_source : G.node,variable : G.node,residue : G.node}
  datatype plan = Plan of
    {graph : G.graph,scope : G.scope,original_law : G.node,
     resolved_law : G.node,theorem : Thm.thm,assignments : assignment list,
     bridge : N.plan,roots : G.node list}
  fun clean theorem =
    let val (tags,_) = Tag.dest_tag (Thm.tag theorem) in
      List.all (fn tag => tag = "DISK_THM") tags andalso
      List.null (Tag.axioms_of (Thm.tag theorem)) end
  fun equality graph node = case G.view graph node of
      G.Application (operator,right) =>
        (case G.view graph operator of G.Application (head,left) =>
           (case G.view graph head of G.Constant _ =>
              if Term.same_const (G.representative graph head)
                  boolSyntax.equality then (left,right)
              else raise ERR "equality" "stored source is not HOL equality"
            | _ => raise ERR "equality" "stored source is not HOL equality")
         | _ => raise ERR "equality" "stored source is not HOL equality")
    | _ => raise ERR "equality" "stored source is not HOL equality"
  fun orientation graph source variable residue =
    let val (left,right) = equality graph source in
      if left = variable andalso right = residue then true
      else if right = variable andalso left = residue then false
      else raise ERR "orientation" "assignment lacks its exact stored source"
    end
  fun validate graph scope resolution original_law resolved_law assignments =
    let
      val _ = R.validate graph scope resolution
      val _ = if G.type_id graph original_law = G.type_id graph resolved_law
          andalso Type.compare (G.type_of graph original_law,Type.bool) = EQUAL
        then () else raise ERR "validate" "law is not Boolean"
      val _ = if R.node resolution original_law = resolved_law andalso
          R.node resolution resolved_law = resolved_law then () else
        raise ERR "validate" "resolved-law endpoint is not exact and stable"
      val _ = List.app (fn {stored_source,variable,residue} =>
        let val _ = ignore (orientation graph stored_source variable residue)
            val _ = case G.view graph variable of
                G.Variable (G.SolverFlexible,_) => ()
              | _ => raise ERR "validate" "assignment name is not flexible"
        in if R.is_assignment_source resolution stored_source andalso
            R.node resolution variable <> variable andalso
            R.node resolution variable = R.node resolution residue then ()
           else raise ERR "validate" "unregistered or unresolved assignment"
        end) assignments
    in () end
  fun active (Plan {graph,scope,...}) = G.validate_scope graph scope
  fun roots (plan as Plan {roots,...}) = (active plan;roots)
  fun sources (plan as Plan {resolved_law,assignments,...}) =
    (active plan;resolved_law :: List.map #stored_source assignments)
  fun discover graph scope
      {resolution,original_law,resolved_law,theorem,assignments} =
    let
      val _ = validate graph scope resolution original_law resolved_law
        assignments
      val _ = if List.null (Thm.hyp theorem) andalso clean theorem andalso
          Portable.pointer_eq (Thm.concl theorem,
            G.representative graph resolved_law) then () else
        raise ERR "discover" "resolved-law witness is not closed clean and exact"
      val result = case U.unify graph
          {scope = scope,flexible = List.map #variable assignments,
           equations = List.map (fn {variable,residue,...} => (variable,residue))
             assignments @ [(original_law,resolved_law)]} of
          U.Unified result => result
        | U.NoMatch _ => raise ERR "discover"
            "bridge needs a separate assignment or bounded binder relation"
      (* This prototype supplies direct stored assignment edges only. A later
         full state engine can derive additional explicit compact equalities;
         an unconstrained unifier result does not supply their authority. *)
      val _ = List.app (fn {variable,residue} =>
        if List.exists (fn {stored_source,...} =>
          (ignore (orientation graph stored_source variable residue);true)
          handle Feedback.HOL_ERR _ => false) assignments then () else
          raise ERR "discover" "bridge introduced an unwitnessed assignment")
        (U.assignments result)
      val bridge = N.discover graph scope result
      val _ = if List.null (N.binder_relations bridge) then () else
        raise ERR "discover" "binder relation requires a separate witness"
      val roots = original_law :: resolved_law ::
        List.map #stored_source assignments @ N.roots bridge
    in Plan {graph = graph,scope = scope,original_law = original_law,
      resolved_law = resolved_law,theorem = theorem,assignments = assignments,
      bridge = bridge,roots = roots} end
  fun assemble block resolution (plan as Plan
      {graph,scope,original_law,resolved_law,theorem,assignments,bridge,...})
      {law_index,assignment_indices} =
    let
      val _ = active plan
      val _ = if P.scope block = scope then () else
        raise ERR "assemble" "wrong proof scope"
      val _ = validate graph scope resolution original_law resolved_law
        assignments
      val inventory = P.sources block
      fun occurrence index node =
        if index >= 0 andalso index < List.length inventory andalso
            List.nth (inventory,index) = node then () else
          raise ERR "assemble" "source occurrence does not match the plan"
      val _ = occurrence law_index resolved_law
      val _ = if List.length assignments = List.length assignment_indices
        then () else raise ERR "assemble" "wrong assignment occurrence count"
      val entries = ListPair.zip (assignments,assignment_indices)
      val _ = List.app (fn ({stored_source,...},index) =>
        occurrence index stored_source) entries
      fun assignment (obligation : N.obligation) =
        let val {variable,residue} = #assignment obligation
            fun find ([] : (assignment * int) list) =
                  raise ERR "assemble" "missing direct assignment edge"
              | find (({stored_source,...},index) :: rest) =
                  let val forward = SOME (orientation graph stored_source
                        variable residue) handle Feedback.HOL_ERR _ => NONE
                  in case forward of NONE => find rest
                    | SOME true => P.source block index
                    | SOME false => Rules.assemble graph block
                        {rule = "symm",target = #equation obligation,
                         premises = [(stored_source,P.source block index)]}
                  end
        in find entries end
      val edges = N.assemble block bridge assignment
      val target = #target (List.last (N.equations bridge))
      val relation = P.compose block
        (fn [constructor,fact] => Thm.EQ_MP constructor fact
          | _ => raise ERR "assemble" "missing equality premises")
        [P.constructor block target,List.last edges]
      val edge = P.compose block
        (fn [relation,fact] => Thm.EQ_MP (Thm.SYM relation) fact
          | _ => raise ERR "assemble" "missing law premises")
        [relation,P.source block law_index]
      fun witness (index,node) =
        if index = law_index andalso node = resolved_law then SOME theorem
        else NONE
    in {edge = edge,witness = witness} end
end
