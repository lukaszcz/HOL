(* Packet ownership and original query correspondence are sealed here. *)
structure SmtReplayOwnedValueProof :> SmtReplayOwnedValueProof =
struct
  structure W = SmtReplayInvocationWork
  structure G = SmtReplayGraph
  structure GP = SmtLib_GraphPreprocess
  structure VP = SmtLib_GraphValueProof
  structure PV = SmtLib_GraphParserValue
  structure NC = SmtReplayNativeContract
  structure N = SmtReplayNamedContext
  structure Boolean = SmtReplayNamedBoolean
  structure Binder = SmtReplayOwnedValueBinder
  structure BinderScope=SmtReplayOwnedScopeReceipt
  structure Specialize = SmtReplayOwnedValueSpecialize
  val ERR = Feedback.mk_HOL_ERR "SmtReplayOwnedValueProof"
  datatype source_lineage = Current of int | Original of int
  type formal_source = {lineage:source_lineage,node:G.node,value:PV.value}
  type original_entry = {index:int,node:G.node,value:PV.value}
  type closed_witness =
    {receipt:Specialize.closed_law,node:G.node,value:PV.value}
  type binder_witness =
    {receipt:Binder.closed_law,node:G.node,value:PV.value}
  datatype block = Block of
    {work:W.portfolio,query:GP.graph_query,owner:unit ref,active:bool ref,
     guard:unit -> unit,native_contract:NC.contract,
     context:PV.context,named:PV.proof_term N.block,
     nodes:PV.proof_term list,
     assertions:(G.node * PV.value) vector,
     originals:original_entry vector option,
     closed_laws:closed_witness vector option,
     binder_laws:binder_witness vector option}
  datatype edge = Edge of {owner:unit ref,edge:N.edge}
  datatype source_port = SourcePort of {block:block,index:int}
  datatype original_source_port = OriginalSourcePort of
    {block:block,position:int}
  datatype closed_law_port = ClosedLawPort of {block:block,position:int}
  datatype binder_law_port = BinderLawPort of
    {block:block,position:int}
  datatype preparation = Prepared of block
    | NeedsOpening of (G.scope * G.node) list
  fun protected expected action = action ()
    handle primary => (W.close expected;raise primary)
  fun validate expected (Block {work,active,guard,native_contract,...}) =
    protected expected (fn () =>
      (if Portable.pointer_eq (expected,work) then () else
         raise ERR "validate" "different original Work";
       if !active then () else raise ERR "validate" "Value block closed";
       guard ();NC.validate_for expected native_contract))
  fun metadata_step expected block =
    (validate expected block;W.spend_policy expected 1)
  fun metadata_map expected block action [] =
        (validate expected block;[])
    | metadata_map expected block action (value::rest) =
        (metadata_step expected block;
         action value :: metadata_map expected block action rest)
  fun metadata_filter expected block predicate [] =
        (validate expected block;[])
    | metadata_filter expected block predicate (value::rest) =
        (metadata_step expected block;
         if predicate value then
           value::metadata_filter expected block predicate rest
         else metadata_filter expected block predicate rest)
  fun compare_pair expected block ((a,b),(c,d)) =
    (metadata_step expected block;
     case Int.compare (a,c) of EQUAL=>
       (metadata_step expected block;Int.compare (b,d)) | order=>order)
  fun close (Block {active,named,...}) =
    (active:=false;N.retire named)
  fun name expected (block as Block {named,...}) node =
    protected expected (fn () =>
      let val _=validate expected block
          val Block {context,...}=block
      in N.name named (PV.proof_term context node) end)
  fun edge_for expected (block as Block {owner,...})
      (Edge {owner=held,edge}) =
    (validate expected block;
     if Portable.pointer_eq (owner,held) then edge else
       raise ERR "edge" "different Value proof block")
  fun compact_theorem_for expected (block as Block {named,...}) edge =
    protected expected (fn () =>
      N.theorem named (edge_for expected block edge))
  fun wrap expected (block as Block {owner,...}) edge =
    (validate expected block;Edge {owner=owner,edge=edge})
  fun source_port_for expected
      (block as Block {assertions,...}) index =
    protected expected (fn () =>
      (validate expected block;
       if index>=0 andalso index<Vector.length assertions then
         SourcePort {block=block,index=index}
       else raise ERR "source" "unknown original query occurrence"))
  fun source_data_for expected
      (SourcePort {block=block as Block {query,assertions,...},index}) =
    protected expected (fn () =>
      let val _=validate expected block
          val (node,value)=Vector.sub (assertions,index)
      in {query=query,index=index,node=node,value=value} end)
  fun source expected (block as Block {owner,named,...})
      (SourcePort {block=held as Block {owner=actual,...},index}) =
    protected expected (fn () =>
      (validate expected block;
       if Portable.pointer_eq (owner,actual) then () else
         raise ERR "source" "different original query block";
       validate expected held;wrap expected block (N.source named index)))
  (* Position is a PRIVATE reservation slot, not an original occurrence.
     The authoritative original occurrence is retained in its entry. *)
  fun original_entry_for expected
      (block as Block {originals,...}) position =
    (validate expected block;
     case originals of NONE=>raise ERR "original_source" "no reservation"
       | SOME entries=>
           (metadata_step expected block;
            if position>=0 andalso position<Vector.length entries then
              Vector.sub(entries,position)
            else raise ERR "original_source" "unknown reservation"))
  fun original_source_ports_for expected (block as Block {originals,...}) =
    protected expected (fn()=>
      let val _=validate expected block
          val count=case originals of NONE=>0 | SOME entries=>
            Vector.length entries
          fun loop position=
            if position=count then (validate expected block;[]) else
              (metadata_step expected block;
               OriginalSourcePort {block=block,position=position}::
                 loop(position+1))
      in loop 0 end)
  fun original_source_data_for expected
      (OriginalSourcePort {block=block as Block {query,...},position}) =
    protected expected (fn()=>
      let val {index,node,value}=original_entry_for expected block position
      in {query=query,index=index,node=node,value=value} end)
  fun original_source expected
      (block as Block {owner,named,assertions,...})
      (OriginalSourcePort
        {block=held as Block {owner=actual,...},position}) =
    protected expected (fn()=>
      let val _=validate expected block
          val _=if Portable.pointer_eq(owner,actual) then () else
            raise ERR "original_source" "different Value proof block"
          val _=ignore(original_entry_for expected held position)
          val _=metadata_step expected block
          val slot=Vector.length assertions+position
      in wrap expected block (N.source named slot) end)
  fun constructor expected (block as Block {named,...}) node =
    protected expected (fn () =>
      let val _=validate expected block val Block {context,...}=block
      in wrap expected block
        (N.constructor named (PV.proof_term context node)) end)
  fun primitive context (N.ReflexiveName node)=
        N.ReflexiveName (PV.proof_term context node)
    | primitive _ N.Symmetry=N.Symmetry
    | primitive _ N.Transitivity=N.Transitivity
    | primitive _ N.Congruence=N.Congruence
    | primitive _ N.EqualityMP=N.EqualityMP
    | primitive context (N.ApplyNamedArgument node)=
        N.ApplyNamedArgument (PV.proof_term context node)
    | primitive _ N.ImplicationMP=N.ImplicationMP
  fun derive expected (block as Block {named,...}) recipe edges =
    protected expected (fn () =>
      let val _=validate expected block
          val Block {context,...}=block
          val actual=metadata_map expected block
            (edge_for expected block) edges
      in wrap expected block
        (N.derive named (primitive context recipe) actual) end)
  fun boolean_primitive _ N.PolicyImplicationMP=N.PolicyImplicationMP
    | boolean_primitive _ N.PolicyConjunction=N.PolicyConjunction
    | boolean_primitive _ N.PolicyConjunctLeft=N.PolicyConjunctLeft
    | boolean_primitive _ N.PolicyConjunctRight=N.PolicyConjunctRight
    | boolean_primitive _ N.PolicyNotIntro=N.PolicyNotIntro
    | boolean_primitive _ N.PolicyNotElim=N.PolicyNotElim
    | boolean_primitive _ N.PolicyEqTrueElim=N.PolicyEqTrueElim
    | boolean_primitive _ N.PolicyEqFalseElim=N.PolicyEqFalseElim
    | boolean_primitive context (N.PolicyContradiction node)=
        N.PolicyContradiction (PV.proof_term context node)
  fun derive_boolean expected (block as Block {context,named,...})
      recipe edges = protected expected (fn () =>
    let val _=validate expected block
        val actual=metadata_map expected block
          (edge_for expected block) edges
    in wrap expected block
      (N.derive_boolean named (boolean_primitive context recipe) actual) end)
  fun needed_source_ports_for expected
      (block as Block {named,assertions,originals,...}) edge =
    protected expected (fn () =>
      let val actual=edge_for expected block edge
          val needed=N.needed_sources named actual
          val Block {closed_laws,binder_laws,...}=block
          val indices=case (originals,closed_laws,binder_laws) of
              (NONE,NONE,NONE)=>needed
            | _=>metadata_filter expected block
                (fn index=>index<Vector.length assertions) needed
      in metadata_map expected block
        (source_port_for expected block) indices end)
  fun source_dependencies_for expected
      (block as Block {named,assertions,...}) edge =
    protected expected (fn () =>
      let val actual=edge_for expected block edge
          val indices=metadata_filter expected block
            (fn index=>index<Vector.length assertions)
            (N.dependencies named actual)
      in metadata_map expected block
        (source_port_for expected block) indices end)

  fun assemble_equality_using equations expected
      (block as Block {context,named,...}) {rule,target,premises} =
    protected expected (fn () =>
    let
      val _=validate expected block
      fun syntax value=PV.proof_term context value
      val target=syntax target
      val premises=metadata_map expected block (fn (value,edge)=>
        (syntax value,edge_for expected block edge)) premises
      fun view value=case PV.proof_view context value of
          PV.ProofConstant atom=>N.Constant atom
        | PV.ProofApplication pair=>N.Application pair | _=>N.Atom
      fun application value=case PV.proof_view context value of
          PV.ProofApplication pair=>SOME pair | _=>NONE
      val indices=ref (Redblackmap.mkDict (compare_pair expected block))
      val next=ref 0
      fun index node=
        let val _=validate expected block
            val actual=PV.proof_key context node
            val _=W.spend_policy expected 1
        in case Redblackmap.peek (!indices,actual) of SOME id=>id | NONE=>
          let val id= !next val _=next:=id+1
              val _=indices:=Redblackmap.insert (!indices,actual,id)
          in id end end
      val result=(case equations of []=>SmtReplayNamedEquality.assemble
        | _=>(W.spend_policy expected 1;
            SmtReplayNamedEquality.assemble_with_equations equations))
        {guard=fn()=>validate expected block,
         tick=fn()=>W.spend_policy expected 1,key=index,
         compare_keys=fn (a,b)=>
           (metadata_step expected block;Int.compare (a,b)),
         same=fn (a,b)=>PV.proof_key context a=PV.proof_key context b,
         equality=N.equality view,application=application,
         name=N.name named,theorem=N.theorem named,
         constructor=N.constructor named,definition=N.definition named,
         reflexive=fn value=>N.derive named (N.ReflexiveName value) [],
         symmetry=N.derive named N.Symmetry,
         transitivity=N.derive named N.Transitivity,
         congruence=N.derive named N.Congruence,
         equality_mp=N.derive named N.EqualityMP,
         conjunction=N.derive_boolean named N.PolicyConjunction,
         conjunct_left=N.derive_boolean named N.PolicyConjunctLeft,
         error=ERR "policy_equality"}
        {rule=rule,target=target,premises=premises}
    in wrap expected block result end)

  fun assemble_boolean_using equations clauses expected
      (block as Block {context,named,native_contract,...}) {target,premises} =
    protected expected (fn () =>
    let
      val _=validate expected block
      val native=NC.for_work expected native_contract
      fun syntax value=PV.proof_term context value
      val target=syntax target
      val premises=metadata_map expected block (fn (value,edge)=>
        (syntax value,edge_for expected block edge)) premises
      fun view value=case PV.proof_view context value of
          PV.ProofApplication pair=>Boolean.Application pair
        | PV.ProofConstant _=>Boolean.Constant | _=>Boolean.Atom
      fun constant value=case PV.proof_view context value of
          PV.ProofConstant atom=>atom
        | _=>raise ERR "boolean_rule" "constant head changed"
      val result=(case clauses of []=>
        (case equations of []=>Boolean.assemble
        | _=>(W.spend_policy expected 1;
            Boolean.assemble_with_equations equations))
      | _=>(W.spend_policy expected 1;
          Boolean.assemble_with_equations_and_clauses equations clauses))
        {native=native,
         spend=fn amount=>W.spend_policy expected (IntInf.fromInt amount),
         pay=W.spend_policy expected,guard=fn()=>validate expected block,
         profile=N.compact_profile named,
         type_weight=N.native_type_weight named,
         type_of=PV.proof_type_of context,view=view,constant=constant,
         same=fn (a,b)=>PV.proof_key context a=PV.proof_key context b,
         name=N.name named,theorem=N.theorem named,
         constructor=N.constructor named,closed=N.closed named,
         equality_mp=N.derive named N.EqualityMP,
         conjunction=N.derive_boolean named N.PolicyConjunction,
         implication_mp=N.derive_boolean named N.PolicyImplicationMP,
         error=ERR "policy_sat"} {root=target,premises=premises}
    in wrap expected block result end)

  fun assemble_equality expected block inputs=
    assemble_equality_using [] expected block inputs
  fun assemble_boolean expected block inputs=
    assemble_boolean_using [] [] expected block inputs

  (* Actual typed constructor equations, produced privately from this
     SAME block. Input cursors confer no theorem or Source authority. *)
  fun prepare_atom_equations expected
      (block as Block{context,named,...}) aliases=
    let
      val _=validate expected block
      (* Actual semantic policy read, template projection and pair helper.
         A fully applied metadata_map creates no partial application. *)
      val _=W.spend_policy expected 3
      val metadata_template= #template_limit(W.semantic_policy expected)
      fun prepare_pair(pair as(left,right))=
        let
          val _=validate expected block
          val _=W.spend_policy expected 6
          val left_type=PV.proof_type_of context left
          val right_type=PV.proof_type_of context right
          val a=N.native_type_weight named left_type
          val b=N.native_type_weight named right_type
          val _=W.spend_policy expected(1+a+b)
          val _=if Type.compare(left_type,right_type)=EQUAL then ()else
            raise ERR "atom_aliases" "actual atom pair Type differs"
          (* Four argument fields/record plus retained pair/plan pair.
             All genuine plans are prepared before their first effect. *)
          val _=W.spend_policy expected 5
          val plan=N.prepare_atom_congruence named
            {left=left,right=right,metadata_template=metadata_template}
        in (pair,plan)end
    in metadata_map expected block prepare_pair aliases end
  fun execute_atom_equations expected block plans=
    let val _=validate expected block
        (* One actual execute callback; the map is fully applied. *)
        val _=W.spend_policy expected 1
        fun execute(pair,plan)=
          let val _=validate expected block
              val _=W.spend_policy expected 1
              val proof=N.execute_atom_congruence plan
          in (pair,proof)end
    in metadata_map expected block execute plans end
  fun atom_equations expected block aliases=
    execute_atom_equations expected block
      (prepare_atom_equations expected block aliases)

  fun assemble_boolean_with_atom_aliases expected block
      {target,premises,aliases}=
    let
      val _=validate expected block
      (* One projection callback and the final two fields/record, before
         producing any additional native constructor equations. *)
      val _=W.spend_policy expected 4
      val equations=atom_equations expected block aliases
      val proofs=metadata_map expected block #2 equations
    in assemble_boolean_using proofs [] expected block
      {target=target,premises=premises}end
    handle primary=>(W.close expected;raise primary)
  (* Genuine fixed Boolean definitions are separate private equations,
     never caller-provided theorem/edge fields or Source slots. *)
  fun assemble_boolean_with_fixed_xors expected
      (block as Block{context,named,...})
      {target,premises,aliases,xors,clause}=
    let
      val _=validate expected block
      (* Policy read/projection2, two helpers, projection selector and
         final target/premises record3. All before added native effects. *)
      val _=W.spend_policy expected 8
      val alias_plans=prepare_atom_equations expected block aliases
      val metadata_template= #template_limit(W.semantic_policy expected)
      fun prepare node=
        let
          val _=validate expected block
          val _=W.spend_policy expected 3
          val(partial,right)=case PV.proof_view context node of
              PV.ProofApplication pair=>pair
            | _=>raise ERR "fixed_xor" "actual XOR is not an application"
          val _=W.spend_policy expected 3
          val(_,left)=case PV.proof_view context partial of
              PV.ProofApplication pair=>pair
            | _=>raise ERR "fixed_xor" "actual XOR is not binary"
          val _=W.spend_policy expected 6
        in N.prepare_fixed_xor named
          {node=node,left=left,right=right,clause=clause,
           metadata_template=metadata_template}end
      val xor_plans=metadata_map expected block prepare xors
      fun execute plan=
        (validate expected block;N.execute_fixed_xor plan)
      val equations=execute_atom_equations expected block alias_plans
      val aliases=metadata_map expected block #2 equations
      val fixed=metadata_map expected block execute xor_plans
    in assemble_boolean_using aliases fixed expected block
      {target=target,premises=premises}end
    handle primary=>(W.close expected;raise primary)
  fun assemble_equality_with_atom_aliases expected block
      {rule,target,premises,aliases}=
    let
      val _=validate expected block
      (* Final rule/target/premises fields and record before production. *)
      val _=W.spend_policy expected 4
      val equations=atom_equations expected block aliases
    in assemble_equality_using equations expected block
      {rule=rule,target=target,premises=premises}end
    handle primary=>(W.close expected;raise primary)
  fun prepare_using binder_laws expected query packet
      {assertions,originals,closed_laws,roots,native_contract,check_type} =
    protected expected (fn () =>
    let
      (* This owning getter is deliberately outside the action below. *)
      val nodes=GP.query_nodes_with_policy_for expected query
      val graph= #graph nodes val scope= #scope nodes
      val native=NC.for_work expected native_contract
    in W.with_step expected (fn () =>
      let
        (* The actual original Work is fenced BEFORE held packet/Value
           activation. No caller node or current-query index is adopted. *)
        val original_backing=case originals of []=>NONE | _=>
          let val sources=W.original_sources expected
              val original_graph=SmtReplaySource.owning_graph sources
              val original_scope=SmtReplaySource.owning_scope sources
              val _=W.validate_policy expected original_graph original_scope
                sources (W.semantic_policy expected)
              val assumptions=SmtReplaySource.assumption_nodes sources
              (* Quote this actual snapshot read/copy before any held
                 packet is activated. The later indexed walks are paid
                 separately at each real visit. *)
              fun snapshot []=W.spend_policy expected 1
                | snapshot (_::rest)=
                    (W.spend_policy expected 2;snapshot rest)
              val _=snapshot assumptions
          in SOME {assumptions=assumptions,
            denied=SmtReplaySource.denied_goal_node sources} end
        val contents=VP.contents_with_policy_for expected query packet
        val context= #context contents
        val lifetime=ref NONE
        fun closed_guard []=()
          | closed_guard (receipt::rest)=
              let val _=W.spend_policy expected 1
                  val data=Specialize.data_for expected receipt
                  val _=if Portable.pointer_eq (#query data,query) andalso
                      Portable.pointer_eq (#context data,context) andalso
                      Portable.pointer_eq
                        (#native_contract data,native_contract) then () else
                    raise ERR "closed_law" "different original Value owner"
              in closed_guard rest end
        fun binder_guard []=()
          | binder_guard(receipt::rest)=
              let val _=W.spend_policy expected 1
                  val data=Binder.data_for expected receipt
                  val _=if Portable.pointer_eq(#query data,query) andalso
                      Portable.pointer_eq(#context data,context) andalso
                      Portable.pointer_eq
                        (#native_contract data,native_contract) then () else
                    raise ERR "binder_law" "different original Value owner"
              in binder_guard rest end
        fun guard () =
          (ignore (VP.contents_with_policy_for expected query packet);
           NC.validate_for expected native_contract;
           closed_guard closed_laws;binder_guard binder_laws;
           case !lifetime of NONE=>() | SOME held=>
             PV.validate_paid_lifetime_guard held)
        fun step ()=(guard ();W.spend_policy expected 1)
        fun copy_map action []=(guard ();[])
          | copy_map action (value::rest)=
              (step ();action value::copy_map action rest)
        fun append [] tail=(guard ();tail)
          | append (value::rest) tail=(step ();value::append rest tail)
        fun reverse values=
          let fun loop [] result=(guard ();result)
                | loop (value::rest) result=
                    (step ();loop rest (value::result))
          in loop values [] end
        fun compare_ids (a,b)=(step ();Int.compare (a,b))
        fun zip [] []=(guard ();[])
          | zip (left::rest) (right::more)=
              (step ();(left,right)::zip rest more)
          | zip _ _=raise ERR "prepare" "assertion count changed"
        fun vector values=
          let fun quote []=guard ()
                | quote (_::rest)=(step ();quote rest)
              val _=quote values
          in Vector.fromList values end
        fun assertion_nodes []=[#denied nodes]
          | assertion_nodes (node::rest)=
              (step ();node::assertion_nodes rest)
        val actual_assertions=assertion_nodes (#assumptions nodes)
        fun correspond [] [] missing=reverse missing
          | correspond (value::rest) (node::more) missing=
              (step ();case PV.corresponds_to_graph_with_policy context
                  graph scope {value=value,node=node} of
                  PV.Corresponding => correspond rest more missing
                | PV.NeedsGraphOpening held =>
                    correspond rest more (held::missing)
                | PV.DifferentGraphSyntax => raise ERR "prepare"
                    "Value assertion differs from the actual query")
          | correspond _ _ _=raise ERR "prepare" "assertion count changed"
        val current_missing=correspond assertions actual_assertions []
        fun original_node index=
          if index<0 then raise ERR "prepare" "unknown original occurrence"
          else case original_backing of NONE=>
              raise ERR "prepare" "missing original Source owner"
            | SOME {assumptions,denied}=>
                let fun find [] 0=(step ();denied)
                      | find [] _=raise ERR "prepare"
                          "unknown original occurrence"
                      | find (node::rest) remaining=
                          (step ();if remaining=0 then node else
                            find rest (remaining-1))
                in find assumptions index end
        fun reserve []=(guard ();[])
          | reserve ((index,value)::rest)=
              let val _=step () val node=original_node index
                  val _=PV.usable context scope value
              in {index=index,node=node,value=value}::reserve rest end
        val reserved=case originals of []=>[] | _=>reserve originals
        fun original_correspond [] missing=reverse missing
          | original_correspond (({node,value,...}:original_entry)::rest)
              missing=
              (step ();case PV.corresponds_to_graph_with_policy context
                  graph scope {value=value,node=node} of
                  PV.Corresponding=>original_correspond rest missing
                | PV.NeedsGraphOpening held=>
                    original_correspond rest (held::missing)
                | PV.DifferentGraphSyntax=>raise ERR "prepare"
                    "Value differs from the original Source occurrence")
        val missing=case reserved of []=>current_missing | _=>
          append current_missing (original_correspond reserved [])
        val all_assertions=case reserved of []=>assertions | _=>
          append assertions (copy_map (fn {value,...}:original_entry=>value)
            reserved)
        fun retain_closed receipt =
          let val _=step ()
              val data=Specialize.data_for expected receipt
              val _=ignore(G.closure_root graph scope (#law_node data))
              val _=case PV.corresponds_to_graph_with_policy context
                  graph scope {value= #statement data,node= #law_node data} of
                  PV.Corresponding=>()
                | _=>raise ERR "closed_law" "changed genuine law syntax"
          in {receipt=receipt,node= #law_node data,value= #statement data}
            :closed_witness end
        val retained_closed=case closed_laws of []=>[]
          | _=>copy_map retain_closed closed_laws
        fun retain_binder receipt=
          let val _=step () val data=Binder.data_for expected receipt
              val _=ignore(G.closure_root graph scope(#law_node data))
              val parent=BinderScope.description_with_policy_for
                expected(#frame data)
              val _=if #scope parent=scope then () else
                raise ERR "binder_law" "different actual parent Scope"
              val _=case PV.corresponds_to_graph_with_policy context
                  graph scope{value= #statement data,node= #law_node data}of
                  PV.Corresponding=>()
                | _=>raise ERR "binder_law" "changed genuine binder law"
              val _=W.spend_policy expected 4
          in {receipt=receipt,node= #law_node data,value= #statement data}
            :binder_witness end
        val retained_binders=case binder_laws of []=>[]
          | _=>copy_map retain_binder binder_laws
        val ordinary_formals=case retained_closed of []=>all_assertions
          | _=>append all_assertions
              (copy_map (fn {value,...}:closed_witness=>value)
                retained_closed)
        val all_formals=case retained_binders of []=>ordinary_formals
          | _=>append ordinary_formals
              (copy_map(fn {value,...}:binder_witness=>value)
                retained_binders)
      in if not (null missing) then (guard ();NeedsOpening missing) else
        let
          val held=PV.prepare_paid_lifetime_guard context
            {remaining_work=fn()=>W.remaining_policy expected,
             scopes=[scope],values=append all_formals roots}
          val _=lifetime:=SOME held
          fun compare_key ((a,b),(c,d))=
            (step ();case Int.compare (a,c) of EQUAL=>
               (step ();Int.compare (b,d)) | order=>order)
          val keys=ref (Redblackmap.mkDict compare_key)
          val next_key=ref 0
          fun key value=
            let val _=guard () val actual=PV.proof_key context value
                val _=W.spend_policy expected 1
            in case Redblackmap.peek (!keys,actual) of SOME id=>id
              | NONE=>
                  let val id= !next_key val _=next_key:=id+1
                      val _=keys:=Redblackmap.insert (!keys,actual,id)
                  in id end
            end
          val seen=ref (Redblackset.empty compare_ids)
          fun collect [] result=reverse result
            | collect (value::rest) result=
                let val _=step () val id=key value in
                  if Redblackset.member (!seen,id) then collect rest result
                  else
                    let val _=seen:=Redblackset.add (!seen,id)
                        val children=case PV.proof_view context value of
                            PV.ProofApplication (a,b)=>[a,b] | _=>[]
                    in collect (append children rest) (value::result) end
                end
          val source_values=copy_map (PV.proof_term context) all_formals
          val reachable=collect
            (append source_values (copy_map (PV.proof_term context) roots)) []
          val spend=W.spend_policy expected
          val allocated=SmtReplayValueNames.allocate guard step spend
            context key native check_type ERR append append copy_map copy_map
            all_formals roots source_values reachable
          fun view value=case PV.proof_view context value of
              PV.ProofConstant atom=>N.Constant atom
            | PV.ProofApplication pair=>N.Application pair
            | _=>N.Atom
          val named=N.freeze
            {guard=guard,spend=spend,
             key=key,type_of=PV.proof_type_of context,view=view,
             name=allocated,
             check_type=check_type,
             native_limits=fn()=>NC.for_work expected native_contract}
            {nodes=reachable,sources=source_values,
             template_limit= #template_limit (#semantic_limits native)}
          val result=Block {work=expected,query=query,owner=ref (),
            active=ref true,guard=guard,native_contract=native_contract,
            context=context,named=named,nodes=reachable,
            assertions=vector (zip actual_assertions assertions),
            originals=case reserved of []=>NONE | _=>SOME(vector reserved),
            closed_laws=case retained_closed of []=>NONE
              | _=>SOME(vector retained_closed),
            binder_laws=case retained_binders of []=>NONE
              | _=>(W.spend_policy expected 3;
                  SOME(vector retained_binders))}
          val _=validate expected result
        in Prepared result end
      end)
    end)
  fun prepare_with_closed_laws expected query packet options =
    prepare_using [] expected query packet options

  fun prepare_with_binder_laws expected query packet
      {assertions,originals,closed_laws,binder_laws,roots,
       native_contract,check_type} =
    prepare_using binder_laws expected query packet
      {assertions=assertions,originals=originals,closed_laws=closed_laws,
       roots=roots,native_contract=native_contract,check_type=check_type}

  fun binder_law_ports_for expected
      (block as Block {binder_laws,...})=protected expected(fn()=>
    let val _=validate expected block
        val count=case binder_laws of NONE=>0 | SOME rows=>Vector.length rows
        fun loop position=if position=count then
              (validate expected block;[]) else
            (metadata_step expected block;
             W.spend_policy expected 5;
             BinderLawPort{block=block,position=position}::loop(position+1))
    in loop 0 end)
  fun binder_law_source expected
      (block as Block {owner,named,assertions,originals,closed_laws,...})
      (BinderLawPort{block=held as Block {owner=actual,binder_laws,...},
                     position})=protected expected(fn()=>
    let val _=validate expected block
        val _=if Portable.pointer_eq(owner,actual) then () else
          raise ERR "binder_law" "different actual Value block"
        val _=validate expected held
        val rows=case binder_laws of SOME rows=>rows | NONE=>
          raise ERR "binder_law" "no binder reservation"
        val _=metadata_step expected block
        val _=if position>=0 andalso position<Vector.length rows then ()else
          raise ERR "binder_law" "unknown binder reservation"
        val _=W.spend_policy expected 10
        val original_count=case originals of NONE=>0
          | SOME entries=>Vector.length entries
        val closed_count=case closed_laws of NONE=>0
          | SOME entries=>Vector.length entries
        val _=metadata_step expected block
        val slot=Vector.length assertions+original_count+
          closed_count+position
    in wrap expected block(N.source named slot)end)

  (* Empty closed-law specialization preserves the original programme. *)
  fun prepare_with_originals expected query packet
      {assertions,originals,roots,native_contract,check_type} =
    prepare_with_closed_laws expected query packet
      {assertions=assertions,originals=originals,closed_laws=[],roots=roots,
       native_contract=native_contract,check_type=check_type}

  fun closed_law_ports_for expected
      (block as Block {closed_laws,...}) = protected expected (fn()=>
    let val _=validate expected block
        val count=case closed_laws of NONE=>0 | SOME rows=>Vector.length rows
        fun loop position=if position=count then
              (validate expected block;[])
            else (metadata_step expected block;
              ClosedLawPort {block=block,position=position}::loop(position+1))
    in loop 0 end)
  fun closed_law_source expected
      (block as Block {owner,named,assertions,originals,...})
      (ClosedLawPort {block=held as Block
          {owner=actual,closed_laws,...},position}) =
    protected expected (fn()=>
      let val _=validate expected block
          val _=if Portable.pointer_eq(owner,actual) then () else
            raise ERR "closed_law" "different Value proof block"
          val _=validate expected held
          val rows=case closed_laws of SOME rows=>rows
            | NONE=>raise ERR "closed_law" "missing private reservation"
          val _=metadata_step expected block
          val row=Vector.sub(rows,position)
          val _=ignore(Specialize.data_for expected (#receipt row))
          val original_count=case originals of NONE=>0
            | SOME rows=>Vector.length rows
          val slot=Vector.length assertions+original_count+position
      in wrap expected block (N.source named slot) end)

  (* Existing callers retain precisely the current-query source programme.
     The empty original branch performs no original-Source lookup. *)
  fun prepare expected query packet
      {assertions,roots,native_contract,check_type} =
    prepare_with_originals expected query packet
      {assertions=assertions,originals=[],roots=roots,
       native_contract=native_contract,check_type=check_type}
  (* A passive typed witness for one ACTUAL private edge. It is not a
     native realization and cannot admit arbitrary theorem input. The
     separate finalizer must still construct original-Source witnesses. *)
  datatype realization_input = RealizationInput of
    {work:W.portfolio,block:block,proof:edge,theorem:Thm.thm,
     dependencies:int list,formal_sources:formal_source vector}
  fun realization_input_for expected
      (block as Block {named,assertions,originals,...}) proof =
    protected expected (fn () =>
      let val _=validate expected block
          val actual=edge_for expected block proof
          val theorem=N.theorem named actual
          val current_count=Vector.length assertions
          val original_count=case originals of NONE=>0 | SOME entries=>
            Vector.length entries
          fun current position=
            if position=current_count then (validate expected block;[])
            else
              let val _=metadata_step expected block
                  val (node,value)=Vector.sub(assertions,position)
              in {lineage=Current position,node=node,value=value}::
                current(position+1) end
          fun original position=
            if position=original_count then (validate expected block;[])
            else
              let val {index,node,value}=
                    original_entry_for expected block position
              in {lineage=Original index,node=node,value=value}::
                original(position+1) end
          fun append [] tail=(validate expected block;tail)
            | append (head::tail) rest=
                (metadata_step expected block;head::append tail rest)
          val entries=append (current 0) (original 0)
          val _=metadata_map expected block (fn _=>()) entries
          val formal_sources=Vector.fromList entries
          val dependencies=metadata_filter expected block
            (fn index=>index<current_count+original_count)
            (N.dependencies named actual)
          val _=metadata_step expected block
      in RealizationInput {work=expected,block=block,proof=proof,
        theorem=theorem,dependencies=dependencies,
        formal_sources=formal_sources} end)
  fun realization_input_data_for expected
      (saved as RealizationInput {work,...}) =
    protected expected (fn () =>
      (if Portable.pointer_eq(expected,work) then () else
         raise ERR "realization_input" "different original Work";
       let val RealizationInput
             {block,proof,theorem,dependencies,formal_sources,...}=saved
           val _=validate expected block
           val Block {query,context,named,nodes,assertions,
             native_contract,closed_laws,binder_laws,...}=block
           val current=N.theorem named (edge_for expected block proof)
           val _=if Portable.pointer_eq(theorem,current) then () else
             raise ERR "realization_input" "private theorem changed"
           val _=metadata_step expected block
       in {query=query,context=context,named=named,nodes=nodes,
         assertions=assertions,native_contract=native_contract,
         theorem=theorem,dependencies=dependencies,
         formal_sources=formal_sources,closed_witnesses=closed_laws,
         binder_witnesses=(case binder_laws of NONE=>NONE
           | SOME _=>(metadata_step expected block;binder_laws))} end))
  fun validate_with_policy_for expected block =
    protected expected (fn()=>validate expected block)
  (* Actual packet/context and private named edges are retained together.
     Recorded syntax is not an original Source or an equality receipt. *)
  datatype unit_resolution_plan=UnitResolutionPlan of
    {work:W.portfolio,block:block,factory:SmtReplayValueClause.factory,
     target:SmtReplayValueClause.occurrences,
     premises:(SmtReplayValueClause.occurrences * edge) list,
     plan:PV.proof_term N.unit_resolution_plan}
  fun prepare_unit_resolution_using aliases fallbacks expected
      (block as Block{context,named,...}) {factory,premises,target}=
    protected expected(fn()=>
      let
        val _=validate expected block
        val _=SmtReplayValueClause.validate_context_for expected factory
          context
        fun data saved=SmtReplayValueClause.data_for expected factory saved
        val target_data=data target
        val inputs=metadata_map expected block(fn(occurrences,edge)=>
          let val saved=data occurrences
          in {tree= #tree saved,edge=edge_for expected block edge}end)premises
        val prepare=case aliases of []=>N.prepare_unit_resolution
          | _=>N.prepare_unit_resolution_with_atom_aliases aliases
        val plan=prepare named
          {premises=inputs,target= #tree target_data,
           target_expanded= #expanded target_data,fallbacks=fallbacks,
           tree_view=SmtReplayValueClause.view,
           metadata_template= #template_limit(W.semantic_policy expected)}
        val _=metadata_step expected block
      in UnitResolutionPlan{work=expected,block=block,factory=factory,
        target=target,premises=premises,plan=plan}end)
  (* The old recorded specialization retains the SAME empty fallbacks. *)
  fun prepare_unit_resolution expected block options=
    prepare_unit_resolution_using [] [] expected block options
  fun execute_unit_resolution expected
      (UnitResolutionPlan{work,block=block as Block{context,...},factory,
        target,premises,plan})=protected expected(fn()=>
      let
        val _=if Portable.pointer_eq(expected,work)then ()else
          raise ERR "unit_resolution" "different original Work"
        fun guards()=
          (validate expected block;
           SmtReplayValueClause.validate_context_for expected factory context;
           ignore(SmtReplayValueClause.data_for expected factory target);
           ignore(metadata_map expected block(fn(occurrences,edge)=>
             (ignore(SmtReplayValueClause.data_for expected factory
                occurrences);
              ignore(edge_for expected block edge)))premises))
        val _=guards()
        val result=N.execute_unit_resolution plan
        val _=guards()
      in wrap expected block result end)

  datatype raw_unit_resolution_plan=RawUnitResolutionPlan of
    {work:W.portfolio,block:block,factory:SmtReplayValueClause.factory,
     batch:SmtReplayValueClause.raw_occurrences,plan:unit_resolution_plan}
  fun prepare_raw_unit_resolution expected
      (block as Block{context,...}){factory,batch,premises}=
    protected expected(fn()=>
    let
      val _=validate expected block
      val _=SmtReplayValueClause.validate_context_for expected factory context
      val data=SmtReplayValueClause.raw_data_for expected factory batch
      val _=metadata_step expected block
      val sources= #head data:: #units data
      fun pair [] []=(validate expected block;[])
        | pair(occurrences::rest)(edge::more)=
            let val _=metadata_step expected block
                val saved=SmtReplayValueClause.data_for expected factory
                  occurrences
                val proof=compact_theorem_for expected block edge
                val wanted=name expected block(#root saved)
                val _=metadata_step expected block
                val _=if Portable.pointer_eq(Thm.concl proof,wanted)then()
                  else raise ERR "raw_resolution" "actual premise differs"
                val _=metadata_step expected block
                val _=metadata_step expected block
            in (occurrences,edge)::pair rest more end
        | pair _ _=raise ERR "raw_resolution" "ordered premise arity changed"
      val inputs=pair sources premises
      val plan=prepare_unit_resolution_using(#atom_aliases data)
        (#fallbacks data)expected block
        {factory=factory,premises=inputs,target= #target data}
      val _=ignore(SmtReplayValueClause.raw_data_for expected factory batch)
      val _=metadata_step expected block
    in RawUnitResolutionPlan{work=expected,block=block,factory=factory,
      batch=batch,plan=plan}end)
  fun execute_raw_unit_resolution expected
      (RawUnitResolutionPlan{work,block,factory,batch,plan})=
    protected expected(fn()=>
    let val _=if Portable.pointer_eq(expected,work)then()else
          raise ERR "raw_resolution" "different original Work"
        val _=validate expected block
        val _=ignore(SmtReplayValueClause.raw_data_for expected factory batch)
        val edge=execute_unit_resolution expected plan
        val _=ignore(SmtReplayValueClause.raw_data_for expected factory batch)
        val _=validate expected block
    in edge end)
end
