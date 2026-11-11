(* Copyright (c) 2026 The HOL4 contributors. *)
structure SmtLib_GraphOrderedValidation :> SmtLib_GraphOrderedValidation =
struct
  open SmtReplayGraph SmtReplayProof SmtReplaySource
    SmtLib_GraphOrderedConversionScoped
  structure G = SmtReplayGraph
  structure P = SmtReplayProof
  structure S = SmtReplaySource
  structure O = SmtLib_GraphOrderedConversionScoped
  type pass = SmtLib_GraphOrderedConversionScoped.pass
  type trace = (string * G.node * G.node) list
  val ERR = Feedback.mk_HOL_ERR "SmtLib_GraphOrderedValidation"
  datatype pipeline = Pipeline of
    {options : O.options,memo : (int,O.conversion) Redblackmap.dict ref}
  fun pipeline (options : O.options) =
    let val _ = G.validate_scope (#graph options) (#scope options)
        val _ = if #template_limit options > 0 andalso
            #input_limit (#admission options) > 0 andalso
            #output_limit (#admission options) > 0 then () else
          raise ERR "pipeline" "nonpositive ordered contract"
    in Pipeline {options = options,memo = ref (Redblackmap.mkDict Int.compare)}
    end
  fun owned graph scope (Pipeline {options,...}) =
    (G.validate_scope (#graph options) (#scope options);
     if G.root_scope graph = G.root_scope (#graph options) andalso
         scope = #scope options then () else
       raise ERR "owned" "pipeline belongs to another graph or scope")
  fun convert graph scope (plan as Pipeline {options,memo}) node =
    let val _ = owned graph scope plan
        val _ = ignore (G.type_of graph node)
        val _ = if G.scope_visible graph scope (G.node_scope graph node)
          then () else raise ERR "convert" "source escapes active scope"
    in case Redblackmap.peek (!memo,G.node_id node) of SOME proof => proof
      | NONE => let val proof = O.discover options node
                    val _ = memo := Redblackmap.insert
                      (!memo,G.node_id node,proof)
                in proof end end
  datatype validation = Validation of
    {graph : G.graph, scope : G.scope, sources : S.sources,
     assumptions : O.conversion list,
     goal : O.conversion, denied : G.node, roots : G.node list}
  fun active (Validation {graph,scope,...}) = G.validate_scope graph scope
  fun original_sources (validation as Validation {sources,...}) =
    (active validation;sources)
  fun processed_assumptions
      (validation as Validation {assumptions,...}) =
    (active validation;List.map O.result assumptions)
  fun processed_denied_goal (validation as Validation {denied,...}) =
    (active validation;denied)
  fun processed_goal
      (validation as Validation {graph,assumptions,goal,...}) =
    (active validation;
     (List.map (G.representative graph o O.result) assumptions,
      G.representative graph (O.result goal)))
  fun witnesses (validation as Validation {assumptions,goal,...}) =
    let val _ = active validation
        val seen = ref (Redblackset.empty Int.compare)
        fun retain (value as (node,_),result) =
          if Redblackset.member (!seen,G.node_id node) then result else
            (seen := Redblackset.add (!seen,G.node_id node);value :: result)
    in List.rev (List.foldl retain []
      (List.concat (List.map O.witnesses (goal :: assumptions)))) end
  fun source_nodes validation =
    let val sources = original_sources validation in
      S.assumption_nodes sources @ [S.denied_goal_node sources] @
        List.map #1 (witnesses validation) end
  fun stages (validation as Validation {assumptions,goal,...}) =
    (active validation;
     {goal = O.stages goal,assumptions = List.map O.stages assumptions})
  fun gaps (validation as Validation {assumptions,goal,...}) =
    (active validation;
     List.concat (List.map O.gaps (goal :: assumptions)))
  fun roots (validation as Validation {roots,...}) =
    (active validation;roots)

  fun discover graph scope
      {goal = (assumptions,goal),import_limit,
       assumption_pipeline,goal_pipeline} =
    let
      val _ = G.validate_scope graph scope
      val _ = if import_limit > 0 then () else
        raise ERR "discover" "nonpositive import contract"
      val _ = List.app (owned graph scope)
        [assumption_pipeline,goal_pipeline]
      val sources = S.new graph scope import_limit
        {goal = goal,assumptions = assumptions}
      val original_goal = #node (G.import graph scope import_limit goal)
      val original_denied = S.denied_goal_node sources
      val assumptions = List.map (convert graph scope assumption_pipeline)
        (S.assumption_nodes sources)
      val goal = convert graph scope goal_pipeline original_goal
      val denied = G.application graph scope
        (G.constant graph scope boolSyntax.negation,O.result goal)
      val roots = original_denied :: denied ::
        List.concat (List.map O.roots (goal :: assumptions))
    in Validation {graph = graph,scope = scope,sources = sources,
      assumptions = assumptions,goal = goal,denied = denied,roots = roots} end

  fun active_block (validation as Validation {graph,scope,...}) block =
    (active validation;
     if G.scope_visible graph (P.scope block) scope then () else
       raise ERR "active_block" "block is outside preprocessing scope")

  fun goal_equality
      (validation as Validation {goal,...}) block =
    (active_block validation block;
     P.compose block
       (fn [proof,constructor] => Thm.EQ_MP constructor proof
         | _ => raise Fail "ordered goal equality")
       [O.assemble goal block,P.constructor block (O.equality goal)])

  fun assembler
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
          [O.assemble conversion block,
           P.constructor block (O.equality conversion)]
      fun assumption conversion =
        if O.source conversion = O.result conversion then
          source (O.source conversion)
        else P.compose block
          (fn [equality,fact] => Thm.EQ_MP equality fact
            | _ => raise Fail "preprocessing source transport")
          [equality conversion,source (O.source conversion)]
      fun denied_goal () =
        let val original = S.denied_goal_node sources in
          if original = denied then source original
          else P.compose block
            (fn [equality,fact,old_bridge,new_bridge] =>
              let
                val operator = Term.rator
                  (boolSyntax.mk_neg (P.name block (O.source goal)))
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
                    O.result conversion = node) assumptions of
                  SOME conversion => SOME (assumption conversion)
                | NONE => if node = denied then SOME (denied_goal ()) else NONE
                  val _ = Option.app (fn edge => memo := Redblackmap.insert
                    (!memo,G.node_id node,edge)) edge
              in edge end
        end
    in assemble end
  fun realize_contradiction validation block falsehood edge =
    let
      val _ = active_block validation block
      fun witness (_,node) = Option.map #2 (List.find
        (fn (owned,_) => owned = node) (witnesses validation))
      val theorem = S.close_contradiction (original_sources validation)
        (P.realize_with_sources block falsehood edge witness)
      val _ = S.check_goal (original_sources validation) theorem
    in theorem end

end
