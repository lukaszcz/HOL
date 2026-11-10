(* SAME recorded clause grammar over authentic Value syntax cursors. *)
structure SmtReplayValueClause :> SmtReplayValueClause =
struct
  structure W=SmtReplayInvocationWork
  structure G=SmtReplayGraph
  structure GP=SmtLib_GraphPreprocess
  structure VP=SmtLib_GraphValueProof
  structure PV=SmtLib_GraphParserValue
  structure F=SmtLib_GraphFrontend
  structure Parser=SmtLib_Parser
  structure C=SmtReplayNamedClause
  val ERR=Feedback.mk_HOL_ERR "SmtReplayValueClause"
  datatype tree = False of PV.proof_term
    | Literal of {node:PV.proof_term,atom:PV.proof_term,negative:bool}
    | Or of {node:PV.proof_term,left:tree,right:tree}
  datatype factory=Factory of
    {work:W.portfolio,owner:unit ref,graph:G.graph,scope:G.scope,
     context:PV.context,guard:unit -> unit}
  datatype occurrences=Occurrences of
    {work:W.portfolio,owner:unit ref,root:PV.value,tree:tree,
     expanded:tree option,guard:unit -> unit}
  fun protected work action=action()
    handle primary=>(W.close work;raise primary)
  fun header expected (Factory{work,...})=
    if Portable.pointer_eq(expected,work)then ()else
      raise ERR "owner" "different original Work"
  fun live expected (saved as Factory{guard,...})=
    (header expected saved;guard())
  fun validate_context_for expected
      (saved as Factory{context,...}) actual=protected expected(fn()=>
    (header expected saved;
     if Portable.pointer_eq(context,actual)then ()else
       raise ERR "owner" "different actual Value context";
     live expected saved))
  fun root(False node)=node
    | root(Literal{node,...})=node | root(Or{node,...})=node
  fun view(False node)=C.ClauseFalse node
    | view(Literal entry)=C.ClauseLiteral entry
    | view(Or entry)=C.ClauseOr entry
  fun create expected query packet=protected expected(fn()=>
    let
      val _=GP.validate_query_with_policy expected query
      val data=VP.contents_with_policy_for expected query packet
      val graph= #graph data val scope= #scope data
      val context= #context data
      fun guard()=
        (GP.validate_query_with_policy expected query;
         ignore(VP.contents_with_policy_for expected query packet);
         PV.validate_for context graph scope)
      val _=guard() val _=W.spend_policy expected 2
    in Factory{work=expected,owner=ref(),graph=graph,scope=scope,
      context=context,guard=guard}end)
  fun create_scoped expected query packet binding=((let
      val _=GP.validate_query_with_policy expected query
      val data=VP.contents_with_policy_for expected query packet
      val actual=VP.binding_frame_data_for expected query binding
      (* Real packet/header projections, four captured comparisons, the
         guard closure, seven Factory fields/constructor and owner ref. *)
      val _=W.spend_policy expected 21
      val graph= #graph data val root= #scope data
      val context= #context data val scope= #scope actual
      fun geometry()=
        let val held=VP.binding_frame_data_for expected query binding
            val _=W.spend_policy expected 4
        in
         if Portable.pointer_eq(#context held,context)andalso
             Portable.pointer_eq(#graph held,graph)andalso
             #root held=root andalso #scope held=scope then ()else
           raise ERR "create_scoped" "different actual binding frame"end
      fun guard()=
        (GP.validate_query_with_policy expected query;
         ignore(VP.contents_with_policy_for expected query packet);
         geometry();
         PV.validate_for context graph root)
      val _=guard()
    in Factory{work=expected,owner=ref(),graph=graph,scope=scope,
      context=context,guard=guard}end)
    handle primary=>(W.close expected;raise primary))
  fun discover_role observed unit_atom expand expected
      (saved as Factory{owner,graph,scope,context,...})
      (term:F.value_term)=protected expected(fn()=>
    let
      val _=live expected saved
      fun tick()=(live expected saved;W.spend_policy expected 1)
      fun compare_key((a,b),(c,d))=
        (tick();case Int.compare(a,c)of EQUAL=>
           (tick();Int.compare(b,d))|order=>order)
      fun same_node(left,right)=compare_key
        (PV.proof_key context left,PV.proof_key context right)=EQUAL
      val seen=ref(Redblackmap.mkDict compare_key)
      val semantic_memo=ref(Redblackmap.mkDict compare_key)
      fun own node=
        let val _=tick()val key=PV.proof_key context node
        in if Redblackmap.inDomain(!seen,key)then ()else
          (tick();seen:=Redblackmap.insert(!seen,key,node))end
      fun boolean node=
        (own node;if Type.compare(PV.proof_type_of context node,Type.bool)
            =EQUAL then ()else
          raise ERR "occurrences" "non-Boolean clause node")
      fun count [] total=(live expected saved;total)
        | count(_::rest)total=(tick();count rest(total+1))
      fun is_constant constant node=
        (tick();case PV.proof_view context node of PV.ProofConstant atom=>
           Term.same_const atom constant | _=>false)
      fun operands constant arity node=
        let fun walk current arguments=
          (tick();case PV.proof_view context current of
              PV.ProofApplication(operator,operand)=>
                (tick();walk operator(operand::arguments))
            | PV.ProofConstant atom=>
                if Term.same_const atom constant andalso
                    count arguments 0=arity then SOME arguments else NONE
            | _=>NONE)
        in walk node []end
      fun need_constructor node=
        (own node;case PV.proof_view context node of
            PV.ProofApplication(operator,_)=>need_constructor operator
          | PV.ProofConstant _=>()
          | _=>raise ERR "occurrences"
              "requested constructor has no fixed rator spine")
      fun memo_semantic node compute=
        let val key=PV.proof_key context node
        in case Redblackmap.peek(!semantic_memo,key)of SOME tree=>tree
          | NONE=>let val tree=compute()val _=tick()
              val _=semantic_memo:=Redblackmap.insert(!semantic_memo,key,tree)
            in tree end end
      val {literal_node,recorded,semantic}=C.discover
        {node=boolean,is_constant=is_constant,operands=operands,
         need_constructor=need_constructor,same_node=same_node,
         occurrence_node=PV.proof_term context o Parser.construction_value,
         root=root,clause_false=False,clause_literal=Literal,clause_or=Or,
         memo_semantic=memo_semantic,error=ERR "occurrences"}
      val _=tick()val target= #node term val lexical= #scope term
      val _=PV.usable context scope target
      val _=if G.scope_visible graph lexical scope orelse
          G.scope_visible graph scope lexical then ()else
        raise ERR "occurrences" "unrelated parsed lexical frame"
      val target_cursor=PV.proof_term context target
      val _=boolean target_cursor
      fun reversed values=
        let fun walk [] result=(live expected saved;result)
              | walk(value::rest)result=
                  (tick();tick();walk rest(value::result))
        in walk values []end
      val entries=if observed then
          F.value_clause_occurrences_with_observer
            {visit=tick,token_work=fn text=>
               (live expected saved;W.spend_policy expected
                 (3+IntInf.fromInt(String.size text))),reverse=reversed}term
        else F.value_clause_occurrences term
      val entries=case entries of [_]=>
            if is_constant boolSyntax.F target_cursor then []else entries
          | _=>entries
      val(tree,_)=if unit_atom then
          let val(tree,value)=literal_node target_cursor
          in(tree,[value])end
        else recorded entries target_cursor
      val expanded=if expand then SOME(semantic target_cursor)else NONE
      fun guard()=
        (live expected saved;PV.usable context scope target;
         Redblackmap.app(fn(_,node)=>
           (tick();ignore(PV.proof_key context node)))(!seen))
      val _=guard()val _=tick()
    in Occurrences{work=expected,owner=owner,root=target,tree=tree,
      expanded=expanded,guard=guard}end)
  fun discover expand expected saved term=
    discover_role false false expand expected saved term
  fun discover_recorded expected saved term=discover false expected saved term
  fun discover_target expected saved term=discover true expected saved term
  fun data_for expected (saved as Factory{owner,...})
      (Occurrences{work,owner=held,root,tree,expanded,guard})=
    protected expected(fn()=>
      (header expected saved;
       if Portable.pointer_eq(expected,work)then ()else
         raise ERR "owner" "different original Work";
       if Portable.pointer_eq(owner,held)then ()else
         raise ERR "owner" "different actual clause factory";
       live expected saved;guard();
       {root=root,tree=tree,expanded=expanded}))

  datatype raw_occurrences=RawOccurrences of
    {work:W.portfolio,owner:unit ref,head:occurrences,
     units:occurrences list,target:occurrences,fallbacks:tree list,
     atom_aliases:(PV.proof_term * PV.proof_term)list,
     guard:unit -> unit}
  fun raw_data_for expected (saved as Factory{owner,...})
      (RawOccurrences{work,owner=held,head,units,target,fallbacks,
        atom_aliases,guard})=
    protected expected(fn()=>
      (header expected saved;
       if Portable.pointer_eq(expected,work)then ()else
         raise ERR "raw_resolution" "different original Work";
       if Portable.pointer_eq(owner,held)then ()else
         raise ERR "raw_resolution" "different actual clause factory";
       live expected saved;guard();
       W.spend_policy expected 1;
       {head=head,units=units,target=target,fallbacks=fallbacks,
        atom_aliases=atom_aliases}))
  (* Caller remains in the SAME active Work action. Head/target retain
     recorded boundaries; each unit is one actual semantic literal. *)
  fun discover_raw expected
      (saved as Factory{owner,context,scope,...}){head,units,target}=
    protected expected(fn()=>
    let
      val _=live expected saved
      fun tick()=(live expected saved;W.spend_policy expected 1)
      fun copy action []=(live expected saved;[])
        | copy action(value::rest)=
            (tick();action value::copy action rest)
      fun reverse values=
        let fun walk [] result=(live expected saved;result)
              | walk(value::rest)result=(tick();walk rest(value::result))
        in walk values []end
      val first=discover_role true false false expected saved head
      val rest=copy(discover_role true true false expected saved)units
      val wanted=discover_role true false true expected saved target
      val _=tick()val _=tick()
      val tokens=first::wanted::rest
      fun guard()=
        List.app(fn held=>(tick();ignore(data_for expected saved held)))tokens
      fun compare_key((a,b),(c,d))=
        (tick();case Int.compare(a,c)of EQUAL=>
          (tick();Int.compare(b,d))|order=>order)
      val _=tick()val _=tick()
      val held=ref(Redblackmap.mkDict compare_key)
      fun own node=
        let val _=tick()val key=PV.proof_key context node
        in if Redblackmap.inDomain(!held,key)then ()else
          (tick();held:=Redblackmap.insert(!held,key,node))end
      fun boolean node=
        (own node;tick();
         if Type.compare(PV.proof_type_of context node,Type.bool)=EQUAL
           then ()else raise ERR "raw_resolution"
             "non-Boolean dictionary key")
      fun constructor node=
        (own node;case PV.proof_view context node of
            PV.ProofConstant _=>()
          | PV.ProofApplication(operator,operand)=>
              (own operand;constructor operator)
          | _=>raise ERR "raw_resolution"
              "fallback lacks actual constructor spine")
      fun constant wanted node=
        (boolean node;case PV.proof_view context node of
            PV.ProofConstant atom=>Term.same_const atom wanted|_=>false)
      fun count [] result=(live expected saved;result)
        | count(_::rest)result=(tick();count rest(result+1))
      fun operands wanted arity node=
        let fun walk current arguments=
          (own current;case PV.proof_view context current of
              PV.ProofApplication(operator,operand)=>
                (own operand;tick();walk operator(operand::arguments))
            | PV.ProofConstant atom=>
                if Term.same_const atom wanted andalso
                    count arguments 0=arity then SOME arguments else NONE
            | _=>NONE)
        in walk node []end
      (* Exact typed syntax only. This is a dictionary key, not proof:
         the named programme must later prove every demanded alias. *)
      datatype shape=Leaf of int * int | Atom of Term.term
        | App of int * int
      fun type_weight ty=
        let val _=tick()
        in if Type.is_vartype ty then
            let val text=Type.dest_vartype ty
                val amount=IntInf.fromInt(String.size text)
                val _=W.spend_policy expected(1+amount)
            in 1+amount end
          else
            let val(name,arguments)=Type.dest_type ty
                val _=W.spend_policy expected
                  (1+IntInf.fromInt(String.size name))
                fun sum [] total=(tick();total)
                  | sum(arg::rest)total=
                      (tick();sum rest(total+type_weight arg))
            in sum arguments 1 end
        end
      fun atom_weight atom=
        let val {Thy,Name,Ty}=Term.dest_thy_const atom
            val amount=1+IntInf.fromInt(String.size Thy)+
              IntInf.fromInt(String.size Name)+type_weight Ty
            val _=W.spend_policy expected amount
        in amount end
      fun tag(Leaf _)=0 | tag(Atom _)=1 | tag(App _)=2
      fun compare_shape(a,b)=
        (tick();case Int.compare(tag a,tag b)of EQUAL=>
           (case(a,b)of(Leaf x,Leaf y)=>compare_key(x,y)
            | (App x,App y)=>compare_key(x,y)
            | (Atom x,Atom y)=>
                let val a=atom_weight x val b=atom_weight y
                    val _=W.spend_policy expected(1+a+b)
                in Term.compare(x,y)end
            | _=>EQUAL)
         | result=>result)
      val _=W.spend_policy expected 6
      val canonical_nodes=ref(Redblackmap.mkDict compare_key)
      val shapes=ref(Redblackmap.mkDict compare_shape)
      val next=ref 0
      val aliases=ref([]:(PV.proof_term * PV.proof_term)list)
      fun intern node=
        let val _=own node val key=PV.proof_key context node
        in case Redblackmap.peek(!canonical_nodes,key)of SOME entry=>entry
          | NONE=>
            let val shape=case PV.proof_view context node of
                    PV.ProofApplication(f,x)=>
                      let val(a,_)=intern f val(b,_)=intern x
                      in tick();App(a,b)end
                  | PV.ProofConstant atom=>(tick();Atom atom)
                  | _=>(tick();Leaf key)
                val entry=case Redblackmap.peek(!shapes,shape)of
                    SOME held=>held
                  | NONE=>
                      let val id= !next val _=tick()val _=tick()
                          val _=next:=id+1
                          val _=tick()val _=tick()
                          val entry=(id,node)
                          val _=shapes:=Redblackmap.insert
                            (!shapes,shape,entry)
                      in entry end
                val(_,canonical)=entry
                val _=if compare_key(key,PV.proof_key context canonical)
                    =EQUAL then ()else
                  (W.spend_policy expected 3;
                   aliases:=(node,canonical):: !aliases)
                val _=tick()
                val _=canonical_nodes:=Redblackmap.insert
                  (!canonical_nodes,key,entry)
            in entry end
        end
      fun seed tree=(tick();ignore(intern(root tree)))
      val _=seed(#tree(data_for expected saved first))
      fun seed_units []=tick()
        | seed_units(current::rest)=
            (tick();seed(#tree(data_for expected saved current));
             seed_units rest)
      val _=seed_units rest
      val _=seed(#tree(data_for expected saved wanted))
      fun canonical_id node= #1(intern node)
      val reversed=SmtReplayRawClause.discover
        {tick=tick,header=guard,error=ERR "raw_resolution",
         boolean=boolean,constructor=constructor,constant=constant,
         operands=operands,node_key=PV.proof_key context,
         compare_node=fn(a,b)=>
           let val left=canonical_id a val right=canonical_id b
           in tick();Int.compare(left,right)end,
         compare_key=compare_key,
         compare_ordinal=fn(a,b)=>(tick();IntInf.compare(a,b)),
         root=root,view=view,literal=Literal,disjunction=Or,
         copy=tick,write=tick}
        {head=fn()=> #tree(data_for expected saved first),units=rest,
         unit_tree=fn current=> #tree(data_for expected saved current),
         target=fn()=>case #expanded(data_for expected saved wanted)of
             SOME tree=>tree|NONE=>raise ERR "raw_resolution"
               "actual target expansion missing"}
      fun retained()=
        (guard();Redblackmap.app(fn(_,node)=>
          (tick();ignore(PV.proof_key context node)))(!held))
      val _=retained()
      val fallbacks=reverse reversed
      val _=tick()val _=tick()
    in RawOccurrences{work=expected,owner=owner,head=first,units=rest,
      target=wanted,fallbacks=fallbacks,atom_aliases=reverse(!aliases),
      guard=retained}end)
end
