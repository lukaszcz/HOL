(* SAME canonical-conversion assembler over static authentic owner ports.
   The actual conversion datatypes stay private to CanonGraph. *)
functor SmtReplayCanonAssemblyFn
  (Input:sig
     type block
     type edge
     type inst_plan
  datatype graph_template = Operand of SmtReplayGraph.node
    | Literal of SmtReplayGraph.node * Term.term
    | Constructor of SmtReplayGraph.node * graph_template * graph_template
  datatype graph_schema = GraphSchema of
    {left : graph_template, right : graph_template,
     holes : Term.term list,  operands : SmtReplayGraph.node list,  theorem :
       Thm.thm,
     admitted_size : int}
  datatype graph_step = GraphStep of
    {source : SmtReplayGraph.node,  current : SmtReplayGraph.node,  result :
       SmtReplayGraph.node,
     children : (SmtReplayGraph.node * SmtReplayGraph.node) option,
     schema : graph_schema option, closed : SmtReplayProof.closed_fact option,
     conversion : SmtReplayProof.closed_conversion option, continuation :
       SmtReplayGraph.node option}
  datatype graph_conversion = GraphConversion of
    {source : SmtReplayGraph.node,  result : SmtReplayGraph.node,  equality :
       SmtReplayGraph.node,
     steps : (int,graph_step) Redblackmap.dict,
     guard_slots : SmtReplayProof.closed_conversion list option ref}
    | SequenceGraphConversion of
      {source : SmtReplayGraph.node, result : SmtReplayGraph.node, equality :
       SmtReplayGraph.node,
       first : graph_conversion,second : graph_conversion,
       guard_leaves : graph_conversion list option ref}
    | DirectRealizedSequence of
      {source : SmtReplayGraph.node, result : SmtReplayGraph.node, equality :
       SmtReplayGraph.node,
       first : graph_conversion,second : graph_conversion,
       first_slot : SmtReplayProof.closed_conversion, second_slot :
       SmtReplayProof.closed_conversion,
       guard_leaves : graph_conversion list option ref}
    | ApplicationGraphConversion of
      {source : SmtReplayGraph.node, result : SmtReplayGraph.node, equality :
       SmtReplayGraph.node,
       left : graph_conversion,right : graph_conversion,
       guard_leaves : graph_conversion list option ref}
    | RealizedGraphConversion of
      {legacy : graph_conversion,realization : SmtReplayProof.realization}
    | PolicyGraphConversion of
      {work:SmtReplayInvocationWork.portfolio,
       frame:SmtReplayOwnedScopeReceipt.receipt,
       legacy:graph_conversion,slot:SmtReplayProof.closed_conversion,
       realization:SmtReplayProof.policy_source_realization option,
       canonical_cut:SmtReplayProof.policy_closed_fact_cut option}
    | PolicySequenceGraphConversion of
      {work:SmtReplayInvocationWork.portfolio,
       frame:SmtReplayOwnedScopeReceipt.receipt,
       source:SmtReplayGraph.node, result:SmtReplayGraph.node,
       equality:SmtReplayGraph.node,
       first:graph_conversion,second:graph_conversion}
     val owner_for:SmtReplayInvocationWork.portfolio -> block ->
       {graph:SmtReplayGraph.graph,scope:SmtReplayGraph.scope,
        contract:SmtReplayNativeContract.contract}
     val name:SmtReplayInvocationWork.portfolio -> block ->
       SmtReplayGraph.node -> Term.term
     val definition:SmtReplayInvocationWork.portfolio -> block ->
       SmtReplayGraph.node -> edge
     val constructor:SmtReplayInvocationWork.portfolio -> block ->
       SmtReplayGraph.node -> edge
     val closed:SmtReplayInvocationWork.portfolio -> block ->
       SmtReplayProof.closed_fact -> edge
     val conversion:SmtReplayInvocationWork.portfolio -> block ->
       SmtReplayProof.closed_conversion -> edge
     val derive:SmtReplayInvocationWork.portfolio -> block ->
       SmtReplayProof.compact_primitive -> edge list -> edge
     val prepare_inst:SmtReplayInvocationWork.portfolio -> block ->
       {substitution:(Term.term,Term.term)Lib.subst,theorem:Thm.thm} ->
       inst_plan
     val execute_inst:SmtReplayInvocationWork.portfolio -> inst_plan -> edge
     val validate_conversion_for:SmtReplayInvocationWork.portfolio ->
       graph_conversion -> unit
     val policy_graph_guard:SmtReplayInvocationWork.portfolio ->
       graph_conversion -> unit
     val graph_equality:graph_conversion -> SmtReplayGraph.node
     val visible:SmtReplayGraph.graph -> SmtReplayGraph.scope ->
       SmtReplayGraph.node -> unit
     val observe_schema:SmtReplayGraph.graph -> IntInf.int -> IntInf.int ->
       IntInf.int -> bool -> unit
     val error:string -> string -> exn
   end) =
struct
  structure G=SmtReplayGraph
  structure P=SmtReplayProof
  structure W=SmtReplayInvocationWork
  open Input
  val ERR=Input.error
  fun graph_assemble_with_policy expected graph block converted =
    ((let
      val owner=Input.owner_for expected block
      val _=if Portable.pointer_eq(graph,#graph owner) then () else
        raise ERR "graph_assemble_with_policy" "different original graph"
      val _=validate_conversion_for expected converted
      val _=W.spend_policy expected 0
      val scope= #scope owner
      fun spend n=W.spend_policy expected n
      fun valid ()=
        (ignore(Input.owner_for expected block);
         validate_conversion_for expected converted)
      fun primitive recipe edges=Input.derive expected block recipe edges
      fun reflexive node=primitive (P.ReflexiveName node) []
      fun trans a b=primitive P.Transitivity [a,b]
      fun symmetry edge=primitive P.Symmetry [edge]
      fun equality_mp equation proof=
        primitive P.EqualityMP [equation,proof]
      val plans=ref ([]:(graph_schema * Input.inst_plan) list)
      val schema_proofs=ref ([]:(graph_schema * Input.edge) list)
      fun find _ []=NONE
        | find object ((held,value)::rest)=
            (spend 1;if Portable.pointer_eq(object,held) then SOME value
             else find object rest)
      fun prepare (schema as GraphSchema {holes,operands,theorem,...})=
        case find schema (!plans) of SOME _=>()
        | NONE=>
          let val _=valid ()
              val substitution=ListPair.mapEq (fn(hole,node)=>
                (spend 2;visible graph scope node;
                 {redex=hole,residue=Input.name expected block node}))
                (holes,operands)
              val plan=Input.prepare_inst expected block
                {substitution=substitution,theorem=theorem}
              val _=spend 1
          in plans:=(schema,plan):: !plans end
      val seen=ref ([]:graph_conversion list)
      fun seen_before _ []=false
        | seen_before object (held::rest)=
            (spend 1;Portable.pointer_eq(object,held) orelse
             seen_before object rest)
      fun collect object=
        if seen_before object (!seen) then () else
          (spend 1;seen:=object:: !seen;
           case object of GraphConversion {steps,...}=>
             Redblackmap.app (fn(_,GraphStep {schema,...})=>
               (spend 1;Option.app prepare schema)) steps
           | RealizedGraphConversion {legacy,...}=>collect legacy
           | saved as PolicyGraphConversion _=>
               policy_graph_guard expected saved
           | saved as PolicySequenceGraphConversion
               {first,second,...}=>
               (policy_graph_guard expected saved;
                collect first;collect second)
           | SequenceGraphConversion {first,second,...}=>
               (collect first;collect second)
           | DirectRealizedSequence _=>()
           | ApplicationGraphConversion {left,right,...}=>
               (collect left;collect right))
      (* Every genuine schema INST is prepared before any native rule. *)
      val _=collect converted
      fun expansion (Operand node)=reflexive node
        | expansion (Literal(node,_))=Input.definition expected block node
        | expansion (Constructor(node,left,right))=
            (spend 1;trans (Input.definition expected block node)
              (primitive P.Congruence [expansion left,expansion right]))
      fun schema_proof (schema as GraphSchema
          {left,right,admitted_size,...})=
        case find schema (!schema_proofs) of SOME proof=>proof
        | NONE=>
          let val plan=case find schema (!plans) of SOME plan=>plan
                | NONE=>raise ERR "graph_assemble_with_policy"
                    "unprepared original schema"
              val instantiated=Input.execute_inst
                expected plan
              val _=observe_schema graph 1
                (IntInf.fromInt admitted_size) 1 true
              val proof=trans (expansion left)
                (trans instantiated (symmetry(expansion right)))
              val _=spend 1
          in schema_proofs:=(schema,proof):: !schema_proofs;proof end
      fun constructor node=Input.constructor expected block node
      fun named equality proof=
        equality_mp (symmetry(constructor equality)) proof
      val memo=ref ([]:(graph_conversion * Input.edge) list)
      fun assemble object=
        (valid ();spend 1;
         case find object (!memo) of SOME proof=>proof
         | NONE=>let val proof=fresh object val _=spend 1
                 in memo:=(object,proof):: !memo;proof end)
      and opened object=equality_mp (constructor(graph_equality object))
        (assemble object)
      and fresh (GraphConversion {source,equality,steps,...})=
            legacy source equality steps
        | fresh (RealizedGraphConversion {legacy=object,...})=assemble object
        | fresh (object as PolicyGraphConversion {slot,...})=
            (policy_graph_guard expected object;
             named (graph_equality object)
               (Input.conversion expected block slot))
        | fresh (object as PolicySequenceGraphConversion
            {first,second,...})=
            (policy_graph_guard expected object;
             named (graph_equality object)
               (trans (opened first) (opened second)))
        | fresh (object as DirectRealizedSequence
            {first_slot,second_slot,...})=
            named (graph_equality object)
              (trans (Input.conversion expected block first_slot)
                     (Input.conversion expected block second_slot))
        | fresh (object as SequenceGraphConversion {first,second,...})=
            named (graph_equality object) (trans (opened first) (opened
              second))
        | fresh (object as ApplicationGraphConversion
            {source,result,left,right,...})=
            let val combined=primitive P.Congruence [opened left,opened right]
            in named (graph_equality object)
              (trans (Input.definition expected block source)
                (trans combined
                  (symmetry(Input.definition expected block result)))) end
      and legacy source equality steps=
        let
          val cache=ref ([]:(G.node * Input.edge) list)
          val pending=ref ([]:G.node list)
          fun lookup _ []=NONE
            | lookup node ((held,proof)::rest)=
                (spend 1;if node=held then SOME proof else lookup node rest)
          fun member _ []=false
            | member node (held::rest)=
                (spend 1;node=held orelse member node rest)
          fun visit node=
            (spend 1;visible graph scope node;
             case lookup node (!cache) of SOME proof=>proof
             | NONE=>
               let val _=if member node (!pending) then
                     raise ERR "graph_assemble_with_policy" "cyclic recipe"
                       else ()
                   val old= !pending
                   val _=spend 1
                   val _=pending:=node::old
                   val GraphStep {current,children,schema,closed,conversion,
                     continuation,...}=Redblackmap.find(steps,G.node_id node)
                   val initial=case children of NONE=>reflexive node
                     | SOME(a,b)=>if current=node then reflexive node else
                         trans (Input.definition expected block node)
                           (trans (primitive P.Congruence [visit a,visit b])
                             (symmetry(Input.definition
                               expected block current)))
                   val oriented=case (schema,closed,conversion) of
                       (NONE,NONE,NONE)=>initial
                     | (SOME law,NONE,NONE)=>trans initial (schema_proof law)
                     | (NONE,SOME fact,NONE)=>trans initial
                         (equality_mp (constructor(P.closed_node fact))
                           (Input.closed expected block fact))
                     | (NONE,NONE,SOME leaf)=>
                         trans initial (Input.conversion expected block leaf)
                     | _=>raise ERR "graph_assemble_with_policy"
                         "multiple semantic witnesses"
                   val proof=case continuation of NONE=>oriented
                     | SOME next=>trans oriented (visit next)
                   val _=spend 1
                   val _=cache:=(node,proof):: !cache
                   val _=pending:=old
               in proof end)
        in named equality (visit source) end
      val result=assemble converted
      val _=valid ()
    in result end)
     handle primary=>(W.close expected;raise primary))

end
