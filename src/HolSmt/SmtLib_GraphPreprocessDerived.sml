(* Copyright (c) 2026 The HOL4 contributors. *)
structure SmtLib_GraphPreprocessDerived :> SmtLib_GraphPreprocessDerived =
struct
  open SmtLib_GraphPreprocessFacts SmtReplayCanonGraph SmtReplayRules
    SmtReplayGraph SmtReplayProof
  structure F = SmtLib_GraphPreprocessFacts
  structure C = SmtReplayCanonGraph
  structure G = SmtReplayGraph
  structure P = SmtReplayProof
  structure R = SmtReplayRules
  val ERR = Feedback.mk_HOL_ERR "SmtLib_GraphPreprocessDerived"
  datatype rule = Rule of
    {fact : F.fact, law : G.node, premises : G.node list, target : G.node}
  datatype validation = Validation of
    {base : F.validation, graph : G.graph, scope : G.scope,
     assumptions : G.node list, rules : rule list}

  fun checked_rule graph scope
      {theorem,holes,operands,premises,target,template_limit} =
    let
      (* F checks the actual closed law and whole equality-to-true schema
         before any traversal of its HOL syntax. C recovers the exact graph
         endpoint of that same bounded schema; no claimed rewrite is added
         to constructor definitions. *)
      val fact = F.checked_fact graph scope
        {theorem = theorem,holes = holes,operands = operands,
         template_limit = template_limit}
      val schema = C.checked_graph_schema graph scope
        {theorem = Drule.EQT_INTRO theorem,holes = holes,operands = operands,
         template_limit = template_limit}
      val law = C.graph_schema_source schema
      val expected = R.implication graph scope premises target
      val _ = if law = expected then () else raise ERR "checked_rule"
        "checked conditional law does not match its dependency endpoints"
    in Rule {fact = fact,law = law,premises = premises,target = target} end

  fun active (Validation {base,graph,scope,...}) =
    (G.validate_scope graph scope;ignore (F.original_sources base))
  fun original_sources (validation as Validation {base,...}) =
    (active validation;F.original_sources base)
  fun processed_assumptions (validation as Validation {assumptions,...}) =
    (active validation;assumptions)
  fun processed_denied_goal (validation as Validation {base,...}) =
    (active validation;F.processed_denied_goal base)
  fun source_nodes (validation as Validation {base,...}) =
    (active validation;F.source_nodes base)
  fun roots (validation as Validation {base,rules,...}) =
    (active validation;F.roots base @
     List.concat (List.map (fn Rule {target,premises,...} =>
       target :: premises) rules))
  fun processed_goal (validation as Validation {base,graph,...}) =
    (active validation;
     (List.map (G.representative graph)
       (processed_assumptions validation),#2 (F.processed_goal base)))

  fun discover graph scope
      {goal,import_limit,revisit,check_type,conversion,facts,rules} =
    let
      val base = F.discover graph scope
        {goal = goal,import_limit = import_limit,revisit = revisit,
         check_type = check_type,conversion = conversion,
         facts = facts @ List.map (fn Rule {fact,...} => fact) rules}
      val all = F.processed_assumptions base
      val count = List.length all - List.length rules
      val initial = List.take (all,count)
      val available = ref (Redblackset.addList
        (Redblackset.empty Int.compare,List.map G.node_id initial))
      fun dependency (Rule {premises,target,...}) =
        let
          val _ = List.app (fn node =>
            if Redblackset.member (!available,G.node_id node) then () else
              raise ERR "discover"
                "dependency is not an original or earlier derived fact")
            premises
          val _ = available := Redblackset.add (!available,G.node_id target)
        in target end
      val added = List.map dependency rules
    in Validation {base = base,graph = graph,scope = scope,
                   assumptions = initial @ added,rules = rules} end

  fun assembler
      (validation as Validation {base,graph,rules,...}) block =
    let
      val _ = active validation
      val original = F.assembler base block
      val memo = ref (Redblackmap.mkDict Int.compare)
      fun assemble node =
        let
          val _ = active validation
          val _ = ignore (P.name block node)
        in case Redblackmap.peek (!memo,G.node_id node) of
            SOME edge => SOME edge
          | NONE => case original node of
              SOME edge => SOME edge
            | NONE =>
                let
                  (* Discovery validates dependency order. Construct in that
                     order rather than recursively following untrusted IDs. *)
                  fun step (Rule {law,premises,target,...}) =
                    if Option.isSome (Redblackmap.peek
                        (!memo,G.node_id target)) orelse
                       Option.isSome (original target) then () else
                      let
                        fun required premise = case original premise of
                            SOME edge => (premise,edge)
                          | NONE => case Redblackmap.peek
                              (!memo,G.node_id premise) of
                              SOME edge => (premise,edge)
                            | NONE => raise ERR "assembler"
                                "missing earlier dependency proof"
                        val edge = R.apply_law graph block
                          {law = required law,target = target,
                           premises = List.map required premises}
                      in memo := Redblackmap.insert
                        (!memo,G.node_id target,edge) end
                  val _ = List.app step rules
                in Redblackmap.peek (!memo,G.node_id node) end
        end
    in assemble end
end
