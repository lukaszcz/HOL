(* Copyright (c) 2026 The HOL4 contributors. *)
structure SmtReplayUnifyPlan :> SmtReplayUnifyPlan =
struct
  open SmtReplayGraph SmtReplayProof SmtReplayUnify
  structure G = SmtReplayGraph
  structure P = SmtReplayProof
  structure U = SmtReplayUnify
  val ERR = Feedback.mk_HOL_ERR "SmtReplayUnifyPlan"
  type obligation = {assignment : U.assignment, equation : G.node}
  type equation = {left : G.node, right : G.node, target : G.node}
  type binder_relation = {left : G.node, right : G.node, equation : G.node}
  datatype plan = Plan of
    {graph : G.graph, scope : G.scope, result : U.result,
     roots : G.node list, obligations : obligation list,
     equations : equation list, binders : binder_relation list, anchor : G.node}
  fun active (Plan {graph,scope,result,...}) =
    U.validate_result graph scope result
  fun roots (plan as Plan {roots,...}) = (active plan;roots)
  fun obligations (plan as Plan {obligations,...}) =
    (active plan;obligations)
  fun equations (plan as Plan {equations,...}) = (active plan;equations)
  fun binder_relations (plan as Plan {binders,...}) = (active plan;binders)

  fun discover graph scope result =
    let
      val _ = U.validate_result graph scope result
      fun equality (left,right) =
        let
          val marker = Term.genvar (G.type_of graph left)
          val operator = G.constant graph scope (Term.rator (Term.rator
            (boolSyntax.mk_eq (marker,marker))))
        in G.application graph scope
          (G.application graph scope (operator,left),right) end
      val obligations = List.map
        (fn assignment as {variable,residue} =>
          {assignment = assignment,equation = equality (variable,residue)})
        (U.assignments result)
      val equations = List.map (fn ((left,right),_) =>
        {left = left,right = right,target = equality (left,right)})
        (U.proofs result)
      val binders = List.mapPartial (fn {kind,...} => case kind of
          U.BinderEquality (left,right) =>
            SOME {left = left,right = right,equation = equality (left,right)}
        | _ => NONE) (U.assumptions result)
      (* Even an empty plan checks the owning block by a graph reference. *)
      val anchor = G.constant graph scope boolSyntax.T
      val roots = anchor :: U.roots result @
        List.map #equation obligations @ List.map #target equations @
        List.map #equation binders
    in Plan {graph = graph,scope = scope,result = result,roots = roots,
      obligations = obligations,equations = equations,binders = binders,
      anchor = anchor} end

  fun assemble_with_relations block (plan as Plan
      {result,obligations,equations,binders,anchor,...})
      {assignment = witness,binder = binder_witness} =
    let
      val _ = active plan
      val _ = ignore (P.name block anchor)
      val assignment_edges = List.map (fn obligation =>
        let
          val edge = witness obligation
          val target = P.name block (#equation obligation)
          val theorem = P.theorem block edge
          val _ = if Portable.pointer_eq (Thm.concl theorem,target) then ()
            else raise ERR "assemble" "wrong assignment witness endpoint"
          val relation = P.compose block
            (fn [constructor,fact] => Thm.EQ_MP constructor fact
              | _ => raise ERR "assemble" "incorrect assignment premises")
            [P.constructor block (#equation obligation),edge]
        in (#variable (#assignment obligation),relation) end) obligations
      val assignments = List.foldl (fn ((variable,edge),table) =>
        Redblackmap.insert (table,G.node_id variable,edge))
        (Redblackmap.mkDict Int.compare) assignment_edges
      fun pair left right = (G.node_id left,G.node_id right)
      fun pair_compare ((a,b),(c,d)) = case Int.compare (a,c) of
          EQUAL => Int.compare (b,d) | order => order
      val binder_edges = List.map (fn relation =>
        let
          val edge = binder_witness relation
          val target = P.name block (#equation relation)
          val _ = if Portable.pointer_eq
              (Thm.concl (P.theorem block edge),target) then () else
            raise ERR "assemble" "wrong binder witness endpoint"
          val proof = P.compose block
            (fn [constructor,fact] => Thm.EQ_MP constructor fact
              | _ => raise ERR "assemble" "incorrect binder premises")
            [P.constructor block (#equation relation),edge]
        in (pair (#left relation) (#right relation),proof) end) binders
      val binder_table = List.foldl (fn ((key,edge),table) =>
        Redblackmap.insert (table,key,edge))
        (Redblackmap.mkDict pair_compare) binder_edges
      val leaves = List.map (fn {kind,...} => case kind of
          U.ConstructorEquation node => P.definition block node
        | U.SolverAssignment {variable,...} =>
            Redblackmap.find (assignments,G.node_id variable)
        | U.BinderEquality (left,right) =>
            Redblackmap.find (binder_table,pair left right))
        (U.assumptions result)
      val leaf_proofs = Vector.fromList (List.map (P.theorem block) leaves)
      fun balanced start count =
        if count = 0 then boolTheory.TRUTH
        else if count = 1 then Vector.sub (leaf_proofs,start)
        else let val half = count div 2 in
          Thm.CONJ (balanced start half)
            (balanced (start+half) (count-half)) end
      val context_witness = balanced 0 (Vector.length leaf_proofs)
      (* This comparison contains compact names and small constructor
         equations only. Align once, then all repeated proofs share it. *)
      val context_witness = Thm.EQ_MP
        (Thm.ALPHA (Thm.concl context_witness) (U.context result))
        context_witness
      (* Retain the dependency collection once in the block's DAG. The
         kernel context witness above was derived from these exact edges;
         every output below uses it and retains this common dependency. *)
      val dependency = P.compose block
        (fn _ => Thm.ASSUME (P.context block)) leaves
      fun prove ((_,theorem),{target,...} : equation) =
        let
          val relation = P.compose block
            (fn [_] => Drule.PROVE_HYP context_witness theorem
              | _ => raise ERR "assemble" "incorrect context premises")
            [dependency]
        in P.compose block
          (fn [constructor,fact] => Thm.EQ_MP (Thm.SYM constructor) fact
            | _ => raise ERR "assemble" "incorrect equality premises")
          [P.constructor block target,relation] end
    in ListPair.mapEq prove (U.proofs result,equations) end
  (* The legacy demanded-binder caller has already admitted its original
     result Types and every native local binder operand/output. Its old
     fallback did not admit every internal annotation. Realize the unifier's
     closed compact law directly, rather than introduce a new canonical-Type
     cutoff through general block definition/source alignment. No native
     substitution or equality search runs over the realized input DAG. *)
  fun realize_local (plan as Plan {graph,result,obligations,binders,...})
      {assignment,binder} =
    let
      val _ = active plan
      fun clean theorem =
        let val (oracles,_) = Tag.dest_tag (Thm.tag theorem) in
          null oracles andalso null (Tag.axioms_of (Thm.tag theorem)) end
      fun source hypothesis = List.exists (fn {equation,...} =>
        Portable.pointer_eq (hypothesis,G.representative graph equation))
        obligations
      fun witness equation theorem =
        if Portable.pointer_eq
            (Thm.concl theorem,G.representative graph equation) andalso
            clean theorem andalso List.all source (Thm.hyp theorem) then
          theorem
        else raise ERR "realize_local" "invalid local equality witness"
      val assignments = List.foldl (fn (obligation,table) =>
        Redblackmap.insert (table,
          G.node_id (#variable (#assignment obligation)),
          witness (#equation obligation) (assignment obligation)))
        (Redblackmap.mkDict Int.compare) obligations
      val relations = List.foldl (fn (relation,table) =>
        Redblackmap.insert (table,
          (G.node_id (#left relation),G.node_id (#right relation)),
          witness (#equation relation) (binder relation)))
        (Redblackmap.mkDict (fn ((a,b),(c,d)) =>
          case Int.compare (a,c) of EQUAL => Int.compare (b,d)
            | order => order)) binders
      fun fact {kind,...} = case kind of
          U.ConstructorEquation node =>
            (case G.view graph node of G.Application (operator,operand) =>
              let
                val term = G.representative graph node
                val left = G.representative graph operator
                val right = G.representative graph operand
                val (actual_left,actual_right) = Term.dest_comb term
                val _ = if Portable.pointer_eq (left,actual_left) andalso
                    Portable.pointer_eq (right,actual_right) then () else
                  raise ERR "realize_local" "constructor children changed"
                val target = boolSyntax.mk_eq (term,Term.mk_comb (left,right))
                val reflexive = Thm.REFL term
              in Thm.EQ_MP (Thm.ALPHA (Thm.concl reflexive) target)
                reflexive end
             | _ => raise ERR "realize_local" "invalid constructor")
        | U.SolverAssignment {variable,...} =>
            Redblackmap.find (assignments,G.node_id variable)
        | U.BinderEquality (left,right) => Redblackmap.find
            (relations,(G.node_id left,G.node_id right))
      val (endpoint,proof) = case List.rev (U.proofs result) of
          last::_ => last
        | [] => raise ERR "realize_local" "empty equation portfolio"
      val compact = Thm.DISCH (U.context result) proof
      val _ = if null (Thm.hyp compact) andalso clean compact then () else
        raise ERR "realize_local" "unifier law is not closed and clean"
      val facts = Vector.fromList (List.map fact (U.assumptions result))
      fun balanced start count = if count=0 then boolTheory.TRUTH
        else if count=1 then Vector.sub (facts,start)
        else let val half=count div 2 in
          Thm.CONJ (balanced start half) (balanced (start+half) (count-half))
        end
      val substitution = List.map (fn node =>
        {redex=G.placeholder graph node,residue=G.representative graph node})
        (U.roots result)
      val law = Thm.INST substitution compact
      val theorem = Thm.MP law (balanced 0 (Vector.length facts))
      val (left,right) = Term.dest_eq (Thm.concl theorem)
      val _ = if Portable.pointer_eq
          (left,G.representative graph (#1 endpoint)) andalso
          Portable.pointer_eq (right,G.representative graph (#2 endpoint))
          andalso clean theorem andalso List.all source (Thm.hyp theorem)
        then () else raise ERR "realize_local" "realization changed endpoints"
    in theorem end

  fun assemble block plan assignment = assemble_with_relations block plan
    {assignment = assignment,binder = fn _ => raise ERR "assemble"
      "binder relation requires a checked witness"}
end
