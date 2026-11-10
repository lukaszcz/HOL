(* Copyright (c) 2026 The HOL4 contributors. *)

structure SmtReplaySupport :> SmtReplaySupport =
struct
  open SmtReplayGraph SmtReplayProof
  structure G = SmtReplayGraph
  structure P = SmtReplayProof
  val ERR = Feedback.mk_HOL_ERR "SmtReplaySupport"
  type discovery =
    {name : G.node -> Term.term, constructor : G.node -> Thm.thm,
     premise : int -> Thm.thm}
  datatype tree = Empty | Leaf of int | Split of tree * tree
  datatype certificate = Certificate of
    {graph : G.graph, scope : G.scope, roots : G.node list,
     names : (G.node * Term.term) list, target : G.node,
     selected : (int * G.node) list, constructors : G.node list,
     tree : tree, needs_context : bool, law : Thm.thm}
  fun clean theorem =
    let val (tags,_) = Tag.dest_tag (Thm.tag theorem) in
      List.all (fn tag => tag = "DISK_THM") tags andalso
      List.null (Tag.axioms_of (Thm.tag theorem)) end
  fun active (Certificate {graph,scope,...}) =
    G.validate_scope graph scope
  fun roots (certificate as Certificate {roots,...}) =
    (active certificate;roots)
  fun selected (certificate as Certificate {selected,...}) =
    (active certificate;List.map #1 selected)
  fun shape start count = if count = 0 then Empty
    else if count = 1 then Leaf start
    else let val half = count div 2 in
      Split (shape start half,shape (start+half) (count-half)) end
  fun tree_term terms Empty = boolSyntax.T
    | tree_term terms (Leaf index) = Vector.sub (terms,index)
    | tree_term terms (Split (left,right)) =
        boolSyntax.mk_conj (tree_term terms left,tree_term terms right)
  fun tree_proof proofs Empty = boolTheory.TRUTH
    | tree_proof proofs (Leaf index) = Vector.sub (proofs,index)
    | tree_proof proofs (Split (left,right)) =
        Thm.CONJ (tree_proof proofs left) (tree_proof proofs right)
  fun discover graph scope
      {roots,premises,target,template_limit,check_type,prove} =
    let
      val _ = G.validate_scope graph scope
      val _ = if template_limit > 0 then () else
        raise ERR "discover" "nonpositive template bound"
      val roots = target :: premises @ roots
      val nodes = G.block_reachable graph roots
      val _ = List.app (check_type o G.type_of graph) nodes
      val names = List.map (fn node => (node,G.placeholder graph node)) nodes
      val block = P.freeze graph {scope = scope,roots = roots,sources = [],
                                 template_limit = template_limit}
      val context = P.context block
      val named = HOLset.addList (HOLset.empty Term.compare,List.map #2 names)
      (* Actual size precedes binder opening, type queries, FV collection,
         hypothesis equality and discharge. Inserted graph residues are
         never inspected here: this entire boundary contains names only. *)
      fun guard term =
        let
          val _ = case SmtReplayImport.bounded_raw_size template_limit term of
              SOME _ => () | NONE =>
                raise ERR "guard" "expanded discovery template"
          fun inspect under_binder term =
            (check_type (Term.type_of term);
             if Term.is_var term then
               if under_binder andalso HOLset.member (named,term) then
                 raise ERR "guard" "graph name below binder" else ()
             else if Term.is_comb term then
               let val (operator,operand) = Term.dest_comb term in
                 inspect under_binder operator;
                 inspect under_binder operand end
             else if Term.is_abs term then
               let val (variable,body) = Term.dest_abs term in
                 check_type (Term.type_of variable);inspect true body end
             else ())
          val _ = inspect false term
          val _ = if HOLset.isSubset
              (Term.FVL [term] (HOLset.empty Term.compare),named) then ()
            else raise ERR "guard" "unowned discovery variable"
        in () end
      val _ = guard context
      val _ = List.app (fn node =>
        if Type.compare (G.type_of graph node,Type.bool) = EQUAL then ()
        else raise ERR "discover" "non-Boolean premise") (target :: premises)
      val constructors = List.filter (fn node => case G.view graph node of
          G.Application _ => true | G.Constant _ => true | _ => false) nodes
      val tree = shape 0 (List.length constructors)
      val terms = Vector.fromList (List.map
        (Thm.concl o P.theorem block o P.definition block) constructors)
      val _ = if Term.aconv (tree_term terms tree) context then () else
        raise ERR "discover" "constructor context shape mismatch"
      fun premise index = if index < 0 orelse index >= List.length premises
        then raise ERR "premise" "unknown recorded premise" else
          Thm.ASSUME (P.name block (List.nth (premises,index)))
      val result = prove {name = P.name block,
        constructor = P.theorem block o P.constructor block,premise = premise}
      val _ = List.app guard (Thm.concl result :: Thm.hyp result)
      val _ = if clean result andalso
          Term.aconv (Thm.concl result) (P.name block target) then () else
        raise ERR "discover" "invalid tags or discovery endpoint"
      val indexed = Lib.mapi (fn index => fn node => (index,node)) premises
      fun occurrence hypothesis = case List.find
          (fn (_,node) => Term.aconv hypothesis (P.name block node)) indexed of
          SOME entry => entry
        | NONE => raise ERR "discover" "hypothesis outside discovery inputs"
      val hypotheses = Thm.hyp result
      val needs_context = List.exists (fn hypothesis =>
        Term.aconv hypothesis context) hypotheses
      val selected = List.map occurrence (List.filter
        (fn hypothesis => not (Term.aconv hypothesis context)) hypotheses)
      val selected = Listsort.sort (fn ((i,_),(j,_)) => Int.compare (i,j))
        selected
      val law = List.foldr (fn ((_,node),proof) =>
        Thm.DISCH (P.name block node) proof) result selected
      val law = if needs_context then Thm.DISCH context law else law
      val _ = guard (Thm.concl law)
      val _ = if List.null (Thm.hyp law) andalso clean law then () else
        raise ERR "discover" "support schema is not closed and clean"
    in Certificate {graph = graph,scope = scope,roots = roots,names = names,
      target = target,selected = selected,constructors = constructors,
      tree = tree,needs_context = needs_context,law = law} end
  fun assemble block (certificate as Certificate
      {scope,names,target,selected,constructors,tree,needs_context,law,...})
      supplied =
    let
      val _ = active certificate
      val _ = if P.scope block = scope then () else
        raise ERR "assemble" "support certificate belongs to another scope"
      val _ = List.app (fn (node,name) =>
        if Term.aconv (P.name block node) name then () else
          raise ERR "assemble" "owned graph name changed") names
      val _ = if List.length supplied = List.length selected andalso
          ListPair.allEq
            (fn ({index,node,...},(expected,source)) =>
              index = expected andalso node = source) (supplied,selected)
        then () else raise ERR "assemble" "wrong selected premise occurrences"
      val _ = List.app (fn {node,edge,...} =>
        if Term.aconv (Thm.concl (P.theorem block edge)) (P.name block node)
        then () else raise ERR "assemble" "wrong selected premise endpoint")
        supplied
      val definitions = if needs_context then
          List.map (P.definition block) constructors else []
      fun apply proofs =
        let
          val (definition_proofs,premise_proofs) =
            Lib.split_after (List.length definitions) proofs
          val initial = if needs_context then Thm.MP law
            (tree_proof (Vector.fromList definition_proofs) tree) else law
          val result = List.foldl (fn (premise,proof) => Thm.MP proof premise)
            initial premise_proofs
        in result end
      val result = P.compose block apply
        (definitions @ List.map #edge supplied)
      val _ = if Term.aconv (Thm.concl (P.theorem block result))
          (P.name block target) then () else
        raise ERR "assemble" "checked support endpoint changed"
    in result end
end
