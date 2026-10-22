(* Copyright (c) 2026 The HOL4 contributors. *)
structure SmtLib_GraphPreprocess :> SmtLib_GraphPreprocess =
struct
  open SmtReplayGraph SmtReplayProof SmtReplaySource SmtReplayCanonGraph
  structure G = SmtReplayGraph
  structure P = SmtReplayProof
  structure S = SmtReplaySource
  structure C = SmtReplayCanonGraph
  structure V = SmtLib_GraphSourcePortfolio
  structure W = SmtReplayInvocationWork
  val _ = SmtLib_GraphSourcePortfolio.validate_with_work
  val _ = SmtReplayProof.validate_block_for
  val ERR = Feedback.mk_HOL_ERR "SmtLib_GraphPreprocess"
  datatype validation = Validation of
    {graph : G.graph, scope : G.scope, sources : S.sources,
     assumptions : C.graph_conversion list,
     goal : C.graph_conversion, denied : G.node, roots : G.node list}
    | Portfolio of V.validation
  fun active (Portfolio value) = ignore (V.original_sources value)
    | active (Validation {graph,scope,...}) = G.validate_scope graph scope
  fun from_portfolio value =
    (ignore (V.original_sources value);Portfolio value)
  fun portfolio_validation (Portfolio value) =
        (active (Portfolio value);SOME value)
    | portfolio_validation (v as Validation _) = (active v;NONE)
  (* Owner authentication precedes this Idle/Busy guard programme. Charge
     occurrence-list traversal as well as every underlying recipe/map scan;
     duplicate assumptions are paid and checked on every invocation. *)
  fun validate_conversions work assumptions goal =
    let
      fun visit [] = W.spend_guard_policy work 1
        | visit (conversion::rest) =
            (W.spend_guard_policy work 2;
             C.validate_conversion_with_policy work conversion;visit rest)
    in visit assumptions;C.validate_conversion_with_policy work goal end
  fun validate_with_work work (Portfolio value) =
        V.validate_with_work work value
    | validate_with_work work (validation as Validation
        {graph,scope,sources,assumptions,goal,...}) =
      ((let val expected = W.original_sources work
            val owner = S.owning_graph expected
            val root = S.owning_scope expected
            val limits = W.semantic_limits work
            val _ = W.validate work owner root expected limits
            val _ = if Portable.pointer_eq (graph,owner) andalso scope = root
                andalso Portable.pointer_eq (sources,expected) then () else
              raise ERR "validate_with_work" "different original invocation"
            val _ = validate_conversions work assumptions goal
        in active validation end)
       handle primary => (W.close work;raise primary))
  fun from_portfolio_with_work work value =
    (V.validate_with_work work value;from_portfolio value)
  fun portfolio_validation_with_work work value =
    (validate_with_work work value;portfolio_validation value)
  fun original_sources (Portfolio value) = V.original_sources value
    | original_sources (validation as Validation {sources,...}) =
    (active validation;sources)
  fun processed_assumptions (Portfolio value) =
      V.processed_assumptions value
    | processed_assumptions
      (validation as Validation {assumptions,...}) =
    (active validation;List.map C.graph_result assumptions)
  fun processed_denied_goal (Portfolio value) = V.processed_denied_goal value
    | processed_denied_goal (validation as Validation {denied,...}) =
    (active validation;denied)
  fun processed_goal (Portfolio value) = V.processed_goal value
    | processed_goal
      (validation as Validation {graph,assumptions,goal,...}) =
    (active validation;
     (List.map (G.representative graph o C.graph_result) assumptions,
      G.representative graph (C.graph_result goal)))
  fun source_nodes validation =
    let val sources = original_sources validation in
      S.assumption_nodes sources @ [S.denied_goal_node sources] end
  fun roots (Portfolio value) = V.roots value
    | roots (validation as Validation {roots,...}) =
    (active validation;roots)

  fun template_limit (Portfolio value) = SOME (V.template_limit value)
    | template_limit (validation as Validation _) = (active validation;NONE)
  fun conversions (Portfolio value) = V.conversions value
    | conversions (validation as Validation _) = (active validation;[])
  fun closed_facts (Portfolio value) = V.closed_facts value
    | closed_facts (validation as Validation _) = (active validation;[])

  fun discover graph scope
      {goal = (assumptions,goal),import_limit,revisit,check_type,conversion} =
    let
      val sources = S.new graph scope import_limit
        {goal = goal,assumptions = assumptions}
      val original_goal = #node (G.import graph scope import_limit goal)
      val original_assumptions = S.assumption_nodes sources
      val original_denied = S.denied_goal_node sources
      val admitted = ref (Redblackset.empty Int.compare)
      fun admit node =
        let val id = G.type_id graph node in
          if Redblackset.member (!admitted,id) then () else
            (check_type (G.type_of graph node);
             admitted := Redblackset.add (!admitted,id)) end
      val _ = List.app admit (G.block_reachable graph
        (original_goal :: original_denied :: original_assumptions))
      fun propose node = (admit node;conversion node)
      val assumptions = List.map
        (C.graph_conversion graph scope revisit propose) original_assumptions
      val goal = C.graph_conversion graph scope revisit propose original_goal
      val operator = G.constant graph scope
        (Term.rator (boolSyntax.mk_neg boolSyntax.T))
      val denied = G.application graph scope (operator,C.graph_result goal)
      val roots = original_denied :: denied ::
        List.concat (List.map C.graph_roots (goal :: assumptions))
      val _ = List.app admit (G.block_reachable graph roots)
    in Validation {graph = graph,scope = scope,sources = sources,
      assumptions = assumptions,goal = goal,denied = denied,roots = roots} end

  fun discover_from_sources graph scope sources
      {import_limit,revisit,check_type,conversion} =
    let
      val _ = G.validate_scope graph scope
      val _ = List.app (fn node =>
        if G.scope_visible graph scope (G.node_scope graph node) then ()
        else raise ERR "discover_from_sources" "foreign original Source")
        (S.denied_goal_node sources :: S.assumption_nodes sources)
      val original_goal = #node (G.import graph scope import_limit
        (S.canonical_goal sources))
      val original_assumptions = S.assumption_nodes sources
      val original_denied = S.denied_goal_node sources
      val admitted = ref (Redblackset.empty Int.compare)
      fun admit node =
        let val id = G.type_id graph node in
          if Redblackset.member (!admitted,id) then () else
            (check_type (G.type_of graph node);
             admitted := Redblackset.add (!admitted,id)) end
      val _ = List.app admit (G.block_reachable graph
        (original_goal :: original_denied :: original_assumptions))
      fun propose node = (admit node;conversion node)
      val assumptions = List.map
        (C.graph_conversion graph scope revisit propose) original_assumptions
      val goal = C.graph_conversion graph scope revisit propose original_goal
      val operator = G.constant graph scope
        (Term.rator (boolSyntax.mk_neg boolSyntax.T))
      val denied = G.application graph scope (operator,C.graph_result goal)
      val roots = original_denied :: denied ::
        List.concat (List.map C.graph_roots (goal :: assumptions))
      val _ = List.app admit (G.block_reachable graph roots)
    in Validation {graph = graph,scope = scope,sources = sources,
      assumptions = assumptions,goal = goal,denied = denied,roots = roots} end

  fun assembler (Portfolio value) block = V.assembler value block
    | assembler
      (validation as Validation {graph,scope,sources,assumptions,goal,
                                denied,...}) block =
    let
      val _ = active validation
      val _ = if G.scope_visible graph (P.scope block) scope then () else
        raise ERR "assembler" "replay block is outside preprocessing scope"
      val indices = ListPair.zip
        (P.sources block,List.tabulate (List.length (P.sources block),
          fn index => index))
      fun index node = case List.find
          (fn (source,_) => source = node) indices of
          SOME (_,index) => index
        | NONE => raise ERR "assembler" "original source is absent from block"
      val _ = List.app (ignore o index) (source_nodes validation)
      fun source node = P.source block (index node)
      fun equality conversion =
        P.compose block
          (fn [equality,bridge] => Thm.EQ_MP bridge equality
            | _ => raise Fail "preprocessing equality constructor")
          [C.graph_assemble graph block conversion,
           P.constructor block (C.graph_equality conversion)]
      fun assumption conversion =
        if C.graph_source conversion = C.graph_result conversion then
          source (C.graph_source conversion)
        else P.compose block
          (fn [equality,fact] => Thm.EQ_MP equality fact
            | _ => raise Fail "preprocessing source transport")
          [equality conversion,source (C.graph_source conversion)]
      fun denied_goal () =
        let val original = S.denied_goal_node sources in
          if original = denied then source original
          else P.compose block
            (fn [equality,fact,old_bridge,new_bridge] =>
              let
                val operator = Term.rator
                  (boolSyntax.mk_neg (P.name block (C.graph_source goal)))
                val negative = Thm.AP_TERM operator equality
                val fact = Thm.EQ_MP old_bridge fact
              in Thm.EQ_MP (Thm.SYM new_bridge)
                (Thm.EQ_MP negative fact) end
              | _ => raise Fail "preprocessing denied-goal transport")
            [equality goal,source original,P.constructor block original,
             P.constructor block denied]
        end
      val memo = ref (Redblackmap.mkDict Int.compare)
      fun assemble node =
        let
          val _ = active validation
          val _ = ignore (P.name block node)
        in case Redblackmap.peek (!memo,G.node_id node) of
            SOME edge => SOME edge
          | NONE =>
              let val edge =
                case List.find (fn conversion =>
                    C.graph_result conversion = node) assumptions of
                  SOME conversion => SOME (assumption conversion)
                | NONE => if node = denied then SOME (denied_goal ()) else NONE
                  val _ = Option.app (fn edge => memo := Redblackmap.insert
                    (!memo,G.node_id node,edge)) edge
              in edge end
        end
    in assemble end
  fun prepare_final_frontier_with_work work validation {roots = extra} =
    (validate_with_work work validation;
     let val root_nodes = roots validation
         val facts = closed_facts validation
         val conversions = conversions validation
         val _ = validate_with_work work validation
         val combined = W.with_step work (fn () =>
           let fun prepend [] = root_nodes
                 | prepend (node :: rest) =
                   (W.spend work 2;node :: prepend rest)
           in prepend extra end)
     in P.prepare_original_realization_frontier work
       {roots = combined,closed_facts = facts,
        conversions = conversions} end)
  fun assembler_with_work work validation block =
    (validate_with_work work validation;P.validate_block_for work block;
     let val build = assembler validation block
     in fn node =>
       (validate_with_work work validation;P.validate_block_for work block;
        let val result = build node
        in validate_with_work work validation;
           P.validate_block_for work block;result end) end)

  fun from_portfolio_with_policy work value =
    (V.validate_with_policy work value;from_portfolio value)
  fun validate_with_policy work (Portfolio value) =
        V.validate_with_policy work value
    | validate_with_policy work (validation as Validation
        {graph,scope,sources,assumptions,goal,...}) =
      ((let val expected = W.original_sources work
            val owner = S.owning_graph expected
            val root = S.owning_scope expected
            val limits = W.semantic_policy work
            val _ = W.validate_policy work owner root expected limits
            val _ = if Portable.pointer_eq (graph,owner) andalso scope=root
                andalso Portable.pointer_eq (sources,expected) then () else
              raise ERR "validate_with_policy" "different original invocation"
            val _ = validate_conversions work assumptions goal
        in active validation end)
       handle primary => (W.close work;raise primary))
  fun template_policy (Portfolio value) = SOME (V.template_policy value)
    | template_policy (validation as Validation _) =
        (active validation;NONE)

  (* Copy graph metadata while the caller's same Work owns this action.
     No representative, expanded term, native effect or fresh Source is
     obtained. Ordered duplicate assumptions remain separate occurrences. *)
  fun processed_nodes_with_policy_for expected validation =
    ((validate_with_policy expected validation;
      W.with_step expected (fn () =>
        let
          val _ = validate_with_policy expected validation
          val _ = W.spend_policy expected 16
          val result = case validation of
              Portfolio value =>
                let val {assumptions,goal} =
                      V.processed_nodes_in_action_with_policy_for
                        expected value
                in {assumptions=assumptions,goal=goal,
                    denied=V.processed_denied_goal value} end
            | Validation {assumptions,goal,denied,...} =>
                let
                  fun copy [] = (W.spend_policy expected 1; [])
                    | copy (conversion :: rest) =
                        (W.spend_policy expected 3;
                         C.graph_result conversion :: copy rest)
                in {assumptions=copy assumptions,
                    goal=C.graph_result goal,denied=denied} end
          val _ = validate_with_policy expected validation
        in result end))
     handle primary => (W.close expected;raise primary))

  datatype graph_query = GraphQuery of
    {work:W.portfolio,preprocessing:validation,
     graph:G.graph,scope:G.scope,sources:S.sources,
     assumptions:G.node list,goal:G.node,denied:G.node,
     epoch:int,symbols:int}

  fun validate_query_with_policy expected
      (GraphQuery {work,preprocessing,graph,scope,sources,epoch,symbols,...}) =
    ((if Portable.pointer_eq (expected,work) then () else
        raise ERR "validate_query_with_policy" "different original Work";
      (* The immutable owner check above precedes held GP/Source activation.
         Genuine graph growth is allowed: no revision snapshot is frozen. *)
      validate_with_policy expected preprocessing;
      W.validate_policy expected graph scope sources
        (W.semantic_policy expected);
      if Type.type_epoch () = epoch andalso Term.term_epoch () = symbols
        then () else raise ERR "validate_query_with_policy"
          "query declaration lifetime changed")
     handle primary => (W.close expected;raise primary))

  fun query_preprocessing_with_policy_for expected
      (query as GraphQuery {work,preprocessing,...}) =
    ((if Portable.pointer_eq (expected,work) then () else
        raise ERR "query_preprocessing" "different original Work";
      validate_query_with_policy expected query;
      W.with_step expected (fn () =>
        let val _ = validate_query_with_policy expected query
            val _ = W.spend_policy expected 1
            val result = preprocessing
            val _ = validate_query_with_policy expected query
        in result end))
     handle primary => (W.close expected;raise primary))

  fun prepare_query_with_policy expected preprocessing =
    ((let
        val {assumptions,goal,denied} =
          processed_nodes_with_policy_for expected preprocessing
      in W.with_step expected (fn () =>
        let
          val _ = validate_with_policy expected preprocessing
          val _ = W.spend_policy expected 64
          val sources = W.original_sources expected
          val {graph,scope} = S.owner_for_scope_guard sources
          val result = GraphQuery
            {work=expected,preprocessing=preprocessing,
             graph=graph,scope=scope,sources=sources,
             assumptions=assumptions,goal=goal,denied=denied,
             epoch=Type.type_epoch (),symbols=Term.term_epoch ()}
          val _ = validate_query_with_policy expected result
        in result end) end)
     handle primary => (W.close expected;raise primary))

  fun query_nodes_with_policy_for expected
      (query as GraphQuery {graph,scope,sources,assumptions,goal,denied,...}) =
    ((validate_query_with_policy expected query;
      W.with_step expected (fn () =>
        let
          val _ = validate_query_with_policy expected query
          val _ = W.spend_policy expected 16
          (* Immutable list sharing needs no second occurrence copy. *)
          val result = {graph=graph,scope=scope,sources=sources,
            assumptions=assumptions,goal=goal,denied=denied}
          val _ = validate_query_with_policy expected query
        in result end))
     handle primary => (W.close expected;raise primary))

  (* Preserve the actual original Source prefix and genuine checked leaves.
     Policy metadata carries no native realization or binder permission. *)
  fun prepare_final_frontier_with_policy work validation {roots=extra} =
    ((validate_with_policy work validation;
      let
        val root_nodes=roots validation
        val facts=closed_facts validation
        val held_conversions=conversions validation
        val _=validate_with_policy work validation
        val combined=W.with_step work (fn () =>
          let
            val _=validate_with_policy work validation
            fun prepend []=root_nodes
              | prepend (node::rest)=
                  (W.spend_policy work 2;node::prepend rest)
            val result=prepend extra
            val _=validate_with_policy work validation
          in result end)
        val result=P.prepare_original_realization_frontier_with_policy work
          {roots=combined,closed_facts=facts,conversions=held_conversions}
        val _=validate_with_policy work validation
      in result end)
     handle primary=>(W.close work;raise primary))

  (* The public route validates expected ownership before activating the
     retained portfolio or native block. No arbitrary theorem callback. *)
  fun assembler_with_policy work (Portfolio value) block =
        V.assembler_with_policy work value block
    | assembler_with_policy work (Validation _) _ =
        (W.close work;raise ERR "policy_assembler"
          "graph conversion needs its policy assembler")

  (* Graph preprocessing uses the same original Work and native block as
     portfolio preprocessing. Each proof step is a fixed policy primitive. *)
  structure OrdinaryPolicyAssembly=SmtReplayPreprocessAssemblyFn
    (struct
       type block=P.block
       type edge=P.edge
       datatype validation = datatype validation
       val validate_with_policy=validate_with_policy
       val source_nodes=source_nodes
       val error=ERR
       val owner_for=P.policy_native_block_owner_for
       fun sources _ block=P.sources block
       fun source _ block index=P.source block index
       fun name _ block node=P.name block node
       fun derive work block opcode inputs=
         P.execute_primitive_with_policy work
           (P.prepare_primitive_with_policy work block opcode inputs)
       val constructor=P.constructor_with_policy
       fun definition _ block node=P.definition block node
       val graph_assemble=C.graph_assemble_with_policy
       val portfolio_assemble=V.assembler_with_policy
     end)
  val assembler_with_policy=OrdinaryPolicyAssembly.assembler_with_policy

  structure SparsePolicyAssembly=SmtReplayPreprocessAssemblyFn
    (struct
       type block=P.policy_sparse_block
       type edge=P.policy_sparse_edge
       datatype validation = datatype validation
       val validate_with_policy=validate_with_policy
       val source_nodes=source_nodes
       val error=ERR
       val owner_for=P.policy_sparse_owner_for
       val sources=P.policy_sparse_sources_for
       val source=P.policy_sparse_source_for
       val name=P.policy_sparse_name_for
       val derive=P.policy_sparse_primitive_for
       val constructor=P.policy_sparse_constructor_for
       val definition=P.policy_sparse_definition_for
       val graph_assemble=C.graph_assemble_sparse_with_policy
       val portfolio_assemble=V.assembler_sparse_with_policy
     end)
  val assembler_sparse_with_policy=SparsePolicyAssembly.assembler_with_policy

end
