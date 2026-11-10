(* Copyright (c) 2026 The HOL4 contributors. *)
(* Added preprocessing facts are derived compact proof edges. *)
structure SmtLib_GraphPreprocessFacts :> SmtLib_GraphPreprocessFacts =
struct
  open SmtLib_GraphPreprocess SmtReplayCanonGraph SmtReplayProof
    SmtReplayGraph SmtReplayImport
  structure V = SmtLib_GraphPreprocess
  structure C = SmtReplayCanonGraph
  structure P = SmtReplayProof
  structure G = SmtReplayGraph
  val ERR = Feedback.mk_HOL_ERR "SmtLib_GraphPreprocessFacts"
  datatype fact = Fact of C.graph_schema
  datatype validation = Validation of
    {base : V.validation, graph : G.graph, scope : G.scope,
     facts : (G.node * C.graph_conversion) list, truth : G.node}
  fun clean theorem =
    let val (tags,_) = Tag.dest_tag (Thm.tag theorem) in
      List.all (fn tag => tag = "DISK_THM") tags andalso
      List.null (Tag.axioms_of (Thm.tag theorem)) end
  fun checked_fact graph scope {theorem,holes,operands,template_limit} =
    let
      val _ = G.validate_scope graph scope
      val _ = case SmtReplayImport.bounded_raw_size template_limit
          (Thm.concl theorem) of SOME _ => ()
        | NONE => raise ERR "checked_fact" "expanded auxiliary fact schema"
      val _ = if List.null (Thm.hyp theorem) andalso clean theorem then ()
        else raise ERR "checked_fact" "auxiliary fact is not a closed law"
    in Fact (C.checked_graph_schema graph scope
      {theorem = Drule.EQT_INTRO theorem,holes = holes,operands = operands,
       template_limit = template_limit}) end
  fun active (Validation {base,graph,scope,...}) =
    (G.validate_scope graph scope;ignore (V.original_sources base))
  fun original_sources (validation as Validation {base,...}) =
    (active validation;V.original_sources base)
  fun source_nodes (validation as Validation {base,...}) =
    (active validation;V.source_nodes base)
  fun processed_denied_goal (validation as Validation {base,...}) =
    (active validation;V.processed_denied_goal base)
  fun processed_assumptions
      (validation as Validation {base,facts,...}) =
    (active validation;V.processed_assumptions base @ List.map #1 facts)
  fun processed_goal (validation as Validation {base,graph,...}) =
    (active validation;
     (List.map (G.representative graph) (processed_assumptions validation),
      #2 (V.processed_goal base)))
  fun roots (validation as Validation {base,facts,truth,...}) =
    (active validation;truth :: V.roots base @
      List.concat (List.map (C.graph_roots o #2) facts))
  fun discover graph scope
      {goal,import_limit,revisit,check_type,conversion,facts} =
    let
      val base = V.discover graph scope
        {goal = goal,import_limit = import_limit,revisit = revisit,
         check_type = check_type,conversion = conversion}
      val truth = G.constant graph scope boolSyntax.T
      fun discover_fact (Fact schema) =
        let
          val source = C.graph_schema_source schema
          val _ = if C.graph_schema_result schema = truth then () else
            raise ERR "discover" "auxiliary fact is not checked true"
          val proof = C.graph_conversion graph scope false
            (fn node => if node = source then SOME schema else NONE) source
          val _ = List.app (check_type o G.type_of graph)
            (G.block_reachable graph (C.graph_roots proof))
        in (source,proof) end
      val facts = List.map discover_fact facts
    in Validation {base = base,graph = graph,scope = scope,
                   facts = facts,truth = truth} end
  fun assembler
      (validation as Validation {base,graph,facts,truth,...}) block =
    let
      val _ = active validation
      val original = V.assembler base block
      val memo = ref (Redblackmap.mkDict Int.compare)
      fun added node = case Redblackmap.peek (!memo,G.node_id node) of
          SOME edge => SOME edge
        | NONE => case List.find (fn (source,_) => source = node) facts of
            NONE => NONE
          | SOME (_,proof) =>
              let
                val equality = P.compose block
                  (fn [fact,constructor] => Thm.EQ_MP constructor fact
                    | _ => raise Fail "auxiliary equality constructor")
                  [C.graph_assemble graph block proof,
                   P.constructor block (C.graph_equality proof)]
                val edge = P.compose block
                  (fn [equality,truth] =>
                     Drule.EQT_ELIM (Thm.TRANS equality truth)
                    | _ => raise Fail "auxiliary true fact")
                  [equality,P.definition block truth]
                val _ = memo := Redblackmap.insert
                  (!memo,G.node_id node,edge)
              in SOME edge end
      fun assemble node =
        (active validation;ignore (P.name block node);
         case original node of SOME edge => SOME edge | NONE => added node)
    in assemble end
end
