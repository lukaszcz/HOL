(* SAME complete Value realization, statically specialized to Source ports. *)
functor SmtReplayValueRealizationFn
  (Source:sig
     type block
     type edge
     type freeze_plan
     type batch
     type receipt
  datatype requirement = ScopedBinderProgramme of
      SmtLib_GraphParserValue.proof_term
    | SourceCorrespondence of
        {value:SmtLib_GraphParserValue.proof_term,node:SmtReplayGraph.node}
     val prepare_freeze:SmtReplayInvocationWork.portfolio ->
       {tables:SmtReplayProof.policy_realization_tables_plan,
        contract:SmtReplayNativeContract.contract,
        profiles:SmtReplayGraph.policy_opaque_profile list,ordinal:int,
        check_type:Type.hol_type -> unit} -> freeze_plan
     val execute_freeze:SmtReplayInvocationWork.portfolio -> freeze_plan ->
       block
     val owner_for:SmtReplayInvocationWork.portfolio -> block ->
       {graph:SmtReplayGraph.graph,scope:SmtReplayGraph.scope,
        contract:SmtReplayNativeContract.contract}
     val sources:SmtReplayInvocationWork.portfolio -> block ->
       SmtReplayGraph.node list
     val source:SmtReplayInvocationWork.portfolio -> block -> int -> edge
     val assembler:SmtReplayInvocationWork.portfolio ->
       SmtLib_GraphPreprocess.validation -> block -> SmtReplayGraph.node ->
       edge option
     val prepare_batch:SmtReplayInvocationWork.portfolio -> block ->
       (SmtReplayGraph.node * edge) list -> batch
     val execute_batch:SmtReplayInvocationWork.portfolio -> batch ->
       receipt list
     val receipt_theorem:SmtReplayInvocationWork.portfolio -> receipt ->
       Thm.thm
   end) =
struct
  structure W=SmtReplayInvocationWork
  structure G=SmtReplayGraph
  structure PV=SmtLib_GraphParserValue
  structure GP=SmtLib_GraphPreprocess
  structure V=SmtReplayOwnedValueProof
  structure P=SmtReplayProof
  structure N=SmtReplayNamedContext
  structure NC=SmtReplayNativeContract
  structure O=SmtReplayRuleObservation
  structure S=SmtReplaySource
  structure Binder=SmtReplayOwnedValueBinder
  structure Specialize=SmtReplayOwnedValueSpecialize
  val ERR=Feedback.mk_HOL_ERR "SmtReplayValueRealization"
  datatype requirement=datatype Source.requirement
  datatype cell_body=datatype SmtReplayValueInterpretation.cell_body
  type cell=SmtReplayValueInterpretation.cell
  datatype witness = Source of V.source_lineage | Reflexive of int * int
    | ClosedWitness of Specialize.closed_law
    | ClosedBinder of Binder.closed_law
  datatype plan = Plan of
    {work:W.portfolio,input:V.realization_input,query:GP.graph_query,
     graph:G.graph,scope:G.scope,sources:S.sources,contract:NC.contract,
     proof:Thm.thm,contexts:Term.term list,cells:cell list,
     witnesses:witness list,source_entries:(V.source_lineage * G.node) list,
     source_batch:Source.batch,
     dependencies:V.source_lineage list,
     epoch:int,symbols:int,used:bool ref}
  datatype result = Result of
    {work:W.portfolio,input:V.realization_input,query:GP.graph_query,
     sources:S.sources,contract:NC.contract,theorem:Thm.thm,
     receipts:Source.receipt list,
     dependencies:V.source_lineage list,
     epoch:int,symbols:int}
  datatype preparation = Prepared of plan | Needs of requirement list
  datatype inventory = Inventory of
    {proof:Thm.thm,contexts:Term.term list,cells:cell list,
     witnesses:witness list,source_entries:(V.source_lineage * G.node) list,
     requirements:requirement list,dependencies:V.source_lineage list}
  fun protected expected action = action ()
    handle primary => (W.close expected;raise primary)
  fun input_data expected input = V.realization_input_data_for expected input
  fun guard expected input query contract epoch symbols =
    (ignore (input_data expected input);
     GP.validate_query_with_policy expected query;
     NC.validate_for expected contract;
     if Type.type_epoch ()=epoch andalso Term.term_epoch ()=symbols then ()
     else raise ERR "guard" "declaration lifetime changed")

  fun check_original expected valid graph sources theorem =
    let
      fun pay amount=(valid ();W.spend_policy expected amount)
      fun tick ()=pay 1
      val _=valid ()
      val assumptions=S.assumption_nodes sources
      fun copied []=valid ()
        | copied (_::rest)=(pay 2;copied rest)
      val _=copied assumptions
      val denied=S.denied_goal_node sources
      val _=tick ()
      fun permitted term =
        let fun seek []=(valid ();false)
              | seek (node::rest)=
                  (tick ();Portable.pointer_eq
                    (term,G.representative graph node) orelse seek rest)
        in seek (denied::assumptions) end
      fun hypotheses []=valid ()
        | hypotheses (term::rest)=
            (tick ();if permitted term then hypotheses rest else
               raise ERR "result" "Hyp is not an original Source")
      val _=tick ()
      val _=if Portable.pointer_eq(Thm.concl theorem,boolSyntax.F) orelse
          (Term.is_const (Thm.concl theorem) andalso
           Term.same_const (Thm.concl theorem) boolSyntax.F) then () else
        raise ERR "result" "realization did not prove F"
      val (oracles,_)=Tag.dest_tag (Thm.tag theorem)
      fun tags []=valid ()
        | tags (tag::rest)=
            (pay (1+IntInf.fromInt (String.size tag));
             if tag="DISK_THM" then tags rest else
               raise ERR "result" "unexpected native oracle")
      val _=tags oracles
      val _=tick ()
      val _=if null (Tag.axioms_of (Thm.tag theorem)) then () else
        raise ERR "result" "unexpected native axioms"
      val _=hypotheses (Thm.hyp theorem)
    in valid () end

  (* The complete typed interpretation is planned before syntax or theorem
     construction. Every Source alias comes from the actual current query
     vector in the sealed input, and its whole App correspondence is checked
     against real graph children. No free leaf is matched by spelling. *)
  fun inventory expected input graph scope =
    let
      val data=input_data expected input
      val context= #context data val named= #named data
      val proof= #theorem data
      val native=NC.for_work expected (#native_contract data)
      val ceiling=IntInf.fromInt (#type_work_limit native)
      val cap=IntInf.fromInt (#template_limit (#semantic_limits native))
      fun valid ()=ignore (input_data expected input)
      fun pay amount=(valid ();W.spend_policy expected amount)
      fun tick ()=pay 1
      fun map action []=(valid ();[])
        | map action (value::rest)=
            (tick ();action value::map action rest)
      fun reverse values=
        let fun loop [] acc=(valid ();acc)
              | loop (value::rest) acc=(tick ();loop rest (value::acc))
        in loop values [] end
      fun append [] tail=(valid ();tail)
        | append (value::rest) tail=(tick ();value::append rest tail)
      fun same_type left right=
        let val a=N.type_weight_using pay (ERR "type") ceiling left
            val b=N.type_weight_using pay (ERR "type") ceiling right
            val _=pay (1+a+b)
        in Type.compare(left,right)=EQUAL end
      fun compare_key ((a,b),(c,d))=
        (tick ();case Int.compare(a,c) of EQUAL=>
          (tick ();Int.compare(b,d)) | order=>order)
      val requirements=ref ([]:requirement list)
      fun need value=(tick ();requirements:=value:: !requirements)
      fun key value=PV.proof_key context value
      fun formal ()= #formal_sources (input_data expected input)
      val contexts=Thm.hyp proof
      val (oracles,_)=Tag.dest_tag (Thm.tag proof)
      fun check_tags []=(tick ();())
        | check_tags (tag::rest)=
            (pay (1+IntInf.fromInt (String.size tag));
             if tag="DISK_THM" then check_tags rest else
               raise ERR "prepare" "unclean native oracle")
      val _=check_tags oracles
      val _=tick ()
      val _=if null (Tag.axioms_of (Thm.tag proof)) then () else
        raise ERR "prepare" "unclean native axioms"
      val conclusion=N.compact_profile named (Thm.concl proof)
      fun closing [] raw inc ann count=(raw,inc,ann,count)
        | closing (term::rest) raw inc ann count=
            let val _=tick () val p=N.compact_profile named term
            in closing rest (3+ #raw p+raw) (3+ #inc p+inc)
              (9+ #ann p+ann) (count+1) end
      val (raw,inc,ann,count)=closing contexts
        (#raw conclusion) (#inc conclusion) (#ann conclusion) (0:IntInf.int)
      val _=if raw<=cap andalso inc<=cap andalso ann<=ceiling then () else
        raise ERR "prepare" "compact closing law exceeds native cap"
      (* Same kind of actual compact closing/projection quote as P. Large
         typed residues are shared DATA, not expanded syntax forecasts. *)
      val _=pay (1+raw+inc+ann+8*count+count*(count+2))
      val variables=ref ([]:Term.term list)
      fun remember term=
        let fun known []=(valid ();false)
              | known (held::rest)=
                  (tick ();Portable.pointer_eq(term,held) orelse known rest)
        in if known (!variables) then ()
          else (tick ();variables:=term:: !variables) end
      fun compact []=valid ()
        | compact (term::rest)=
            (tick ();if Term.is_var term then
                (remember term;compact rest)
              else if Term.is_const term then compact rest
              else if Term.is_comb term then
                let val (left,right)=Term.dest_comb term
                in compact (left::right::rest) end
              else raise ERR "prepare" "compact law contains a binder")
      val _=compact (Thm.concl proof::contexts)
      fun used term=
        let fun search []=(valid ();false)
              | search (held::rest)=
                  (tick ();Portable.pointer_eq(term,held) orelse search rest)
        in search (!variables) end
      val aliases=ref (Redblackmap.mkDict compare_key)
      fun alias value node =
        let val _=tick () val id=key value
            val _=ignore (G.closure_root graph scope node)
            val _=if same_type (PV.proof_type_of context value)
                (G.type_of graph node) then () else
              raise ERR "prepare" "Source alias Type changed"
        in case Redblackmap.peek (!aliases,id) of
            SOME previous=>if previous=node then () else
              need (SourceCorrespondence {value=value,node=node})
          | NONE=>aliases:=Redblackmap.insert (!aliases,id,node)
        end
      val pairs=ref (Redblackset.empty (fn ((a,b),(c,d))=>
        (tick ();case compare_key(a,c) of EQUAL=>
          (tick ();Int.compare(b,d)) | order=>order)))
      fun correspond value node =
        let val _=tick () val id=(key value,G.node_id node)
            val _=ignore (G.closure_root graph scope node)
        in if Redblackset.member(!pairs,id) then () else
          let val _=pairs:=Redblackset.add (!pairs,id)
          in case PV.proof_graph_reference context value of
              SOME actual=>if Portable.pointer_eq(#graph actual,graph)
                  andalso #node actual=node then alias value node
                else structural value node
            | NONE=>structural value node
          end
        end
      and structural value node =
        case (PV.proof_view context value,G.view graph node) of
            (PV.ProofApplication(left,right),G.Application(f,x))=>
              (correspond left f;correspond right x;alias value node)
          | (PV.ProofConstant atom,G.Constant _)=>
              let val actual=G.representative graph node
                  val _=tick ()
              in if Term.same_const atom actual andalso
                  same_type (Term.type_of atom) (G.type_of graph node)
                then alias value node else
                  need (SourceCorrespondence {value=value,node=node}) end
          | _=>need (SourceCorrespondence {value=value,node=node})
      fun dependent slot =
        let fun search []=(valid ();false)
              | search (index::rest)=
                  (tick ();slot=index orelse search rest)
        in search (#dependencies data) end
      fun source_index term =
        let val vector=formal () val length=Vector.length vector
            fun search index =
              if index=length then NONE else
                let val _=tick ()
                    val {node,value,lineage}=Vector.sub(vector,index)
                    val cursor=PV.proof_term context value
                    val name=N.name named cursor
                in if dependent index andalso
                    Portable.pointer_eq(term,name) then
                    (correspond cursor node;SOME(lineage,node))
                  else search (index+1) end
        in search 0 end
      fun definition term [] =
            (valid ();raise ERR "prepare" "unknown compact hypothesis")
        | definition term (value::rest)=
            (tick ();case PV.proof_view context value of
                PV.ProofConstant _=>test_definition term value rest
              | PV.ProofApplication _=>test_definition term value rest
              | _=>definition term rest)
      and test_definition term value rest =
        let val actual=Thm.concl (N.theorem named (N.definition named value))
        in if Portable.pointer_eq(term,actual) then Reflexive(key value)
          else definition term rest end
      val entries=ref ([]:(V.source_lineage * G.node) list)
      fun same_lineage (V.Current left,V.Current right)=
            (tick ();left=right)
        | same_lineage (V.Original left,V.Original right)=
            (tick ();left=right)
        | same_lineage _=(tick ();false)
      fun add_entry (lineage,node)=
        let fun member []=(valid ();false)
              | member ((old,_)::rest)=
                  (tick ();same_lineage(lineage,old) orelse member rest)
        in if member (!entries) then () else
          (tick ();entries:=(lineage,node):: !entries) end
      fun closed_witness term=case #closed_witnesses data of NONE=>NONE
        | SOME rows=>
          let val count=Vector.length rows
              fun seek position=if position=count then (valid ();NONE) else
                let val _=tick ()
                    val {receipt,node,value}=Vector.sub(rows,position)
                    val cursor=PV.proof_term context value
                    val saved=Specialize.data_for expected receipt
                    val _=if #law_node saved=node then () else
                      raise ERR "prepare" "changed private closed law"
                in if Portable.pointer_eq(term,N.name named cursor) then
                    (correspond cursor node;SOME(ClosedWitness receipt))
                  else seek(position+1) end
          in seek 0 end
      fun closed_binder term=case #binder_witnesses data of NONE=>NONE
        | SOME rows=>
          let val count=Vector.length rows
              fun seek position=
                (tick ();if position=count then (valid ();NONE) else
                let val _=pay 2
                    val {receipt,node,value}=Vector.sub(rows,position)
                    val cursor=PV.proof_term context value
                    val saved=Binder.data_for expected receipt
                    val _=if #law_node saved=node then () else
                      raise ERR "prepare" "changed private binder law"
                    val _=tick ()
                in if Portable.pointer_eq(term,N.name named cursor) then
                    let fun install []=valid ()
                          | install((value,actual)::rest)=
                              (tick ();
                               ignore(G.closure_root graph scope actual);
                               alias value actual;install rest)
                        val _=install(#aliases saved)
                        val _=pay 2
                    in SOME(ClosedBinder receipt)end
                  else(tick ();seek(position+1))end)
          in seek 0 end
      fun witness term=case source_index term of SOME entry=>
            (add_entry entry;Source(#1 entry))
        | NONE=>(case closed_witness term of SOME held=>held
            | NONE=>(case closed_binder term of SOME held=>held
                | NONE=>definition term (#nodes data)))
      val witnesses=map witness contexts
      val selected=ref ([]:PV.proof_term list)
      fun select []=valid ()
        | select (value::rest)=
            (tick ();if used (N.name named value) then
               (selected:=value:: !selected;select rest) else select rest)
      val _=select (#nodes data)
      val visited=ref (Redblackset.empty compare_key)
      val cells=ref ([]:cell list)
      fun collect value =
        let val _=tick () val id=key value
        in if Redblackset.member(!visited,id) then () else
          let
            val _=visited:=Redblackset.add (!visited,id)
            val name=N.name named value
            val ty=PV.proof_type_of context value
            val body=case Redblackmap.peek (!aliases,id) of
                SOME node=>Borrowed node
              | NONE=>case PV.proof_graph_reference context value of
                  SOME actual=>
                    if Portable.pointer_eq(#graph actual,graph) then
                      (ignore (G.closure_child_node graph (#scope actual)
                        (#child actual));
                       if G.scope_visible graph scope
                           (G.node_scope graph (#node actual)) then
                         (ignore (G.closure_root graph scope (#node actual));
                          Borrowed (#node actual))
                       else (need (ScopedBinderProgramme value);Atomic name))
                    else raise ERR "prepare" "different graph backing"
                | NONE=>case PV.proof_view context value of
                    PV.ProofVariable _=>Atomic name
                  | PV.ProofConstant atom=>Atomic atom
                  | PV.ProofApplication(left,right)=>
                      (collect left;collect right;
                       Application(key left,key right))
                  | _=>(need (ScopedBinderProgramme value);Atomic name)
            val _=tick ()
          in cells:={key=id,name=name,hol_type=ty,body=body}:: !cells end
        end
      val _=List.app collect (!selected)
      fun target []=false
        | target (value::rest)=
            (tick ();if Portable.pointer_eq(N.name named value,
                Thm.concl proof) then
               (case PV.proof_view context value of
                  PV.ProofConstant atom=>Term.same_const atom boolSyntax.F
                | _=>false)
             else target rest)
      val _=if target (#nodes data) then () else
        raise ERR "prepare" "checked edge is not a contradiction"
      val _=valid ()
    in Inventory {proof=proof,contexts=contexts,cells=reverse (!cells),
      witnesses=witnesses,source_entries=reverse (!entries),
      requirements=reverse (!requirements),
      dependencies=map (fn slot=> #lineage (Vector.sub(formal (),slot)))
        (#dependencies data)} end

  fun prepare_with_profiles expected input {profiles,check_type} =
    protected expected (fn () =>
    let
      (* Fenced input data needs the original Busy action. The two GP
         owning getters below run outside it, under that same expected W. *)
      val query=W.with_step expected (fn () =>
        #query (input_data expected input))
      val current=GP.query_nodes_with_policy_for expected query
      val preprocessing=GP.query_preprocessing_with_policy_for expected query
      val saved=W.with_step expected (fn () =>
        inventory expected input (#graph current) (#scope current))
      val Inventory {requirements,...}=saved
    in if not (null requirements) then Needs requirements else
      let
        val Inventory {proof,contexts,cells,witnesses,source_entries,
          dependencies,...}=saved
        val contract=W.with_step expected (fn () =>
          #native_contract (input_data expected input))
        fun roots []=[]
          | roots ((_,node)::rest)=
              (ignore (input_data expected input);
               W.spend_policy expected 1;node::roots rest)
        val targets=W.with_step expected (fn () => roots source_entries)
        val frontier=GP.prepare_final_frontier_with_policy expected
          preprocessing {roots=targets}
        val tables=W.with_step expected (fn () =>
          P.prepare_owned_realization_tables_with_policy expected frontier)
        val freeze=W.with_step expected (fn () =>
          let val ordinal=W.unused_policy_ordinal expected
                {role=W.FinalFreeze,minimum=0}
              fun checked_type ty=
                (ignore (input_data expected input);
                 check_type ty;ignore (input_data expected input))
          in Source.prepare_freeze expected
            {tables=tables,contract=contract,profiles=profiles,ordinal=ordinal,
             check_type=checked_type} end)
        val native_block=W.with_step expected (fn () =>
          Source.execute_freeze expected freeze)
        fun original index node=W.with_step expected (fn () =>
          let val _=ignore (input_data expected input)
              val _=ignore(Source.owner_for
                expected native_block)
              fun at [] _=raise ERR "prepare" "original Source slot absent"
                | at (held::rest) remaining=
                    (W.spend_policy expected 1;
                     if remaining=0 then held else at rest (remaining-1))
              val actual=at (Source.sources expected native_block) index
              val _=if actual=node then () else
                raise ERR "prepare" "original Source occurrence changed"
          in Source.source expected native_block index end)
        fun edges []=[]
          | edges ((lineage,target)::rest)=
              let
                val edge=case lineage of
                    V.Current _=>
                      (case Source.assembler expected
                          preprocessing native_block target of
                          SOME edge=>edge
                        | NONE=>raise ERR "prepare"
                            "current Source has no checked witness")
                  | V.Original index=>original index target
                val _=W.with_step expected (fn () =>
                  (ignore (input_data expected input);
                   W.spend_policy expected 2))
              in (target,edge)::edges rest end
        val requests=edges source_entries
        val batch=W.with_step expected (fn () =>
          Source.prepare_batch
            expected native_block requests)
        val epoch=Type.type_epoch () val symbols=Term.term_epoch ()
        val _=W.with_step expected (fn () =>
          (guard expected input query contract epoch symbols;
           W.spend_policy expected 2))
      in Prepared (Plan {work=expected,input=input,query=query,
        graph= #graph current,scope= #scope current,sources= #sources current,
        contract=contract,proof=proof,contexts=contexts,cells=cells,
        witnesses=witnesses,source_entries=source_entries,
        source_batch=batch,dependencies=dependencies,
        epoch=epoch,symbols=symbols,used=ref false}) end
    end)

  fun prepare expected input {check_type} =
    prepare_with_profiles expected input {profiles=[],check_type=check_type}

  fun execute expected (saved as Plan {work,...}) =
    protected expected (fn () =>
      (if Portable.pointer_eq(expected,work) then () else
         raise ERR "execute" "different original Work";
       W.with_step expected (fn () =>
       let
         val Plan {input,query,graph,scope,sources,contract,proof,contexts,
           cells,witnesses,source_entries,source_batch,dependencies,
           epoch,symbols,used,...}=saved
         fun valid ()=guard expected input query contract epoch symbols
         fun pay amount=(valid ();W.spend_policy expected amount)
         fun tick ()=pay 1
         val _=valid ()
         val _=if !used then raise ERR "execute" "used realization"
           else (tick ();used:=true)
         val native=NC.for_work expected contract
         val ceiling=IntInf.fromInt (#type_work_limit native)
         fun same_type left right=
           let val a=N.type_weight_using pay (ERR "type") ceiling left
               val b=N.type_weight_using pay (ERR "type") ceiling right
               val _=pay (1+a+b)
           in Type.compare(left,right)=EQUAL end
         fun compare_key ((a,b),(c,d))=
           (tick ();case Int.compare(a,c) of EQUAL=>
              (tick ();Int.compare(b,d)) | order=>order)
         val terms=ref (Redblackmap.mkDict compare_key)
         fun typed key=(tick ();case Redblackmap.peek (!terms,key) of
             SOME actual=>actual
           | NONE=>raise ERR "execute" "interpretation dependency absent")
         fun term key= #1 (typed key)
         val substitution=SmtReplayValueInterpretation.interpret
           valid tick graph scope typed same_type terms ERR cells []
         val receipts=Source.execute_batch
           expected source_batch
         fun pair [] []=[]
           | pair ((lineage,_)::rest) (receipt::more)=
               (tick ();(lineage,receipt)::pair rest more)
           | pair _ _=raise ERR "execute" "Source witness count changed"
         val ports=pair source_entries receipts
         fun same_lineage (V.Current left,V.Current right)=
               (tick ();left=right)
           | same_lineage (V.Original left,V.Original right)=
               (tick ();left=right)
           | same_lineage _=(tick ();false)
         fun source_proof lineage=
           let fun seek []=raise ERR "execute" "Source witness absent"
                 | seek ((held,receipt)::rest)=
                     (tick ();if same_lineage(held,lineage) then
                        Source.receipt_theorem
                          expected receipt else seek rest)
           in seek ports end
         fun witness (Source lineage)=source_proof lineage
           | witness (ClosedWitness receipt)=
               let val _=valid ()
                   val saved=Specialize.data_for expected receipt
                   val proof=P.closed_original (#fact saved)
                   val _=valid ()
               in proof end
           | witness (ClosedBinder receipt)=
               let val _=valid ()
                   val saved=Binder.data_for expected receipt
                   val proof=P.closed_original(#fact saved)
                   val _=valid ()
               in proof end
           | witness (Reflexive key)=
               let val actual=term key val _=valid ()
                   val proof=O.REFL actual val _=valid ()
               in proof end
         fun proofs []=(valid ();[])
           | proofs (item::rest)=
               let val _=tick () val proof=witness item
                   val _=valid () val tail=proofs rest
                   val _=tick ()
               in proof::tail end
         val instantiated=SmtReplaySimultaneousRealization.instantiate
           {guard=valid,error=ERR "execute",contexts=contexts,
            proof=proof,substitution=substitution}
         val genuine=proofs witnesses
         val theorem=SmtReplaySimultaneousRealization.apply
           {guard=valid,law=instantiated,witnesses=genuine}
         val _=valid ()
         val _=check_original expected valid graph sources theorem
         val _=valid ()
       in Result {work=expected,input=input,query=query,sources=sources,
         contract=contract,theorem=theorem,receipts=receipts,
         dependencies=dependencies,epoch=epoch,symbols=symbols} end)))

  fun result_data expected (saved as Result {work,...}) =
    protected expected (fn () =>
      (if Portable.pointer_eq(expected,work) then () else
         raise ERR "result" "different original Work";
       let val Result {input,query,sources,contract,theorem,receipts,
             dependencies,epoch,symbols,...}=saved
           val _=guard expected input query contract epoch symbols
           fun validate_receipts []=()
             | validate_receipts (receipt::rest)=
                 (W.spend_policy expected 1;
                  ignore (Source.receipt_theorem
                    expected receipt);validate_receipts rest)
           val _=validate_receipts receipts
           val {graph,...}=S.owner_for_scope_guard sources
           val _=check_original expected
             (fn()=>guard expected input query contract epoch symbols)
             graph sources theorem
           val _=W.spend_policy expected 1
       in (theorem,dependencies) end))
  fun contradiction_for expected result= #1 (result_data expected result)
  fun source_dependencies_for expected result= #2 (result_data expected result)
  fun current_dependencies_for expected result=
    let val dependencies= #2 (result_data expected result)
        fun current []=[]
          | current (V.Current index::rest)=
              (W.spend_policy expected 1;index::current rest)
          | current (_::rest)=(W.spend_policy expected 1;current rest)
    in current dependencies end
end
