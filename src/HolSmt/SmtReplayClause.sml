(* Copyright (c) 2026 The HOL4 contributors. *)
structure SmtReplayClause :> SmtReplayClause =
struct
  open SmtReplayGraph SmtReplayProof SmtClause
  structure G = SmtReplayGraph
  structure P = SmtReplayProof
  structure C = SmtClause
  val ERR = Feedback.mk_HOL_ERR "SmtReplayClause"
  type literal = {atom : G.node, negative : bool}
  datatype tree = Empty of G.node
                | Literal of G.node * literal
                | Disjunction of G.node * tree * tree
  datatype occurrences = Occurrences of
    {graph : G.graph, scope : G.scope, root : G.node,
     literals : literal list, tree : tree}
  datatype clause = Clause of
    {block : P.block, graph : G.graph, scope : G.scope,
     literals : literal list, compact : C.clause, proof : P.edge,
     layout : occurrences option}

  fun active graph scope = G.validate_scope graph scope
  fun root (Occurrences {graph,scope,root,...}) =
    (active graph scope; root)
  fun recorded (Occurrences {graph,scope,literals,...}) =
    (active graph scope; literals)
  fun tree_root (Empty node) = node
    | tree_root (Literal (node,_)) = node
    | tree_root (Disjunction (node,_,_)) = node

  fun discover graph scope literals =
    let
      val _ = active graph scope
      val negation = G.constant graph scope boolSyntax.negation
      val disjunction = G.constant graph scope boolSyntax.disjunction
      fun literal (entry as {atom,negative} : literal) =
        let
          val _ = if Type.compare (G.type_of graph atom,Type.bool) = EQUAL
            then () else raise ERR "discover" "non-Boolean clause atom"
          (* The constructor checks graph ownership and lexical visibility
             for positive atoms too, without introducing an extra node. *)
          val _ = if G.scope_visible graph scope (G.node_scope graph atom)
            then () else raise ERR "discover" "clause atom escapes scope"
          val node = if negative then
            G.application graph scope (negation,atom) else atom
        in Literal (node,entry) end
      fun join [] = Empty (G.constant graph scope boolSyntax.F)
        | join [entry] = literal entry
        | join (entry::rest) =
            let
              val left = literal entry
              val right = join rest
              val node = G.application graph scope
                (G.application graph scope
                  (disjunction,tree_root left),tree_root right)
            in Disjunction (node,left,right) end
      val tree = join literals
    in Occurrences {graph = graph,scope = scope,root = tree_root tree,
      literals = literals,tree = tree} end

  fun constant graph atom =
    case G.view graph atom of
      G.Constant _ =>
        let val term = G.representative graph atom in
          if Term.same_const term boolSyntax.T orelse
              Term.same_const term boolSyntax.F then SOME term else NONE
        end
    | _ => NONE
  fun compact_atom graph block atom =
    let val name = P.name block atom in
      case constant graph atom of SOME term => term | NONE => name
    end
  fun compact_literal graph block ({atom,negative} : literal) =
    let val term = compact_atom graph block atom in
      if negative then boolSyntax.mk_neg term else term
    end
  fun compact_literals graph block =
    List.map (compact_literal graph block)

  (* Each step exposes just the recorded constructor. Literal atoms stop
     here; their internal disjunctions and conjunctions are never opened. *)
  fun bridge block (Occurrences {graph,scope,root,tree,...}) =
    let
      val _ = active graph scope
      val _ = ignore (P.name block root)
      fun atom node = case constant graph node of
          SOME _ => P.definition block node
        | NONE => P.checked block (Thm.REFL (P.name block node))
      fun walk (Empty node) = P.definition block node
        | walk (Literal (node,{atom = operand,negative = false})) =
            atom operand
        | walk (Literal (node,{atom = operand,negative = true})) =
            P.compose block
              (fn [constructor,child] => Thm.TRANS constructor
                  (Thm.AP_TERM boolSyntax.negation child)
                | _ => raise ERR "bridge" "incorrect negation premises")
              [P.constructor block node,atom operand]
        | walk (Disjunction (node,left,right)) =
            P.compose block
              (fn [constructor,left,right] => Thm.TRANS constructor
                  (Thm.MK_COMB
                    (Thm.AP_TERM boolSyntax.disjunction left,right))
                | _ => raise ERR "bridge" "incorrect disjunction premises")
              [P.constructor block node,walk left,walk right]
    in walk tree end

  fun from_source block (layout as Occurrences
      {graph,scope,root,literals,...}) fact =
    let
      val _ = active graph scope
      val _ = if Term.aconv (Thm.concl (P.theorem block fact))
          (P.name block root) then () else
        raise ERR "from_source" "incorrect named source endpoint"
      val edge = P.compose block
        (fn [equation,fact] => Thm.EQ_MP equation fact
          | _ => raise ERR "from_source" "incorrect source premises")
        [bridge block layout,fact]
      val compact = C.from_literals (compact_literals graph block literals)
        (P.theorem block edge)
    in Clause {block = block,graph = graph,scope = scope,literals = literals,
      compact = compact,proof = edge,layout = SOME layout} end

  fun literals (Clause {graph,scope,literals,...}) =
    (active graph scope; literals)
  fun proof (Clause {block,graph,scope,proof,...}) =
    (active graph scope; ignore (P.theorem block proof); proof)
  fun contains literal (clause as Clause {block,graph,compact,...}) =
    (ignore (proof clause);
     C.contains (compact_literal graph block literal) compact)

  fun same_literal ({atom = left,negative = l} : literal)
      ({atom = right,negative = r} : literal) = left = right andalso l = r
  fun same_literals left right =
    List.length left = List.length right andalso
    ListPair.allEq (fn (left,right) => same_literal left right) (left,right)

  (* The old clause procedure returns only recorded compact literals.
     Recover identities from that bounded vocabulary, never from residues. *)
  fun finish (Clause {block,graph,scope,...}) vocabulary premises layout
      compact =
    let
      val _ = active graph scope
      val _ = List.app (fn clause => ignore
        (P.theorem block (proof clause))) premises
      fun occurrence term =
        case List.find (fn literal => Term.aconv term
            (compact_literal graph block literal)) vocabulary of
          SOME literal => literal
        | NONE => raise ERR "finish" "unrecorded compact literal"
      val literals = List.map occurrence (C.literals compact)
      val edge = P.compose block (fn _ => C.theorem compact)
        (List.map proof premises)
    in Clause {block = block,graph = graph,scope = scope,literals = literals,
      compact = compact,proof = edge,layout = layout} end

  fun checked_pair (first as Clause {block,...}) second =
    (ignore (proof first);ignore (P.theorem block (proof second)))
  fun resolve pivot (first as Clause {block,graph,compact,...})
      (second as Clause {compact = next,...}) =
    (checked_pair first second;
     Option.map (finish first (literals first @ literals second)
       [first,second] NONE)
       (C.resolve (compact_literal graph block pivot) compact next))
  fun resolve_or_weaken pivot
      (first as Clause {block,graph,compact,...})
      (second as Clause {compact = next,...}) =
    (checked_pair first second;
     finish first (literals first @ literals second) [first,second] NONE
       (C.resolve_or_weaken (compact_literal graph block pivot) compact next))

  fun to_target (target as Occurrences {graph,scope,root,literals,...})
      (clause as Clause {block,literals = source_literals,...}) =
    let
      val _ = active graph scope
      val _ = ignore (P.name block root)
      val _ = if same_literals literals source_literals
        then () else raise ERR "to_target" "different recorded literals"
    in P.compose block
      (fn [equation,fact] => Thm.EQ_MP (Thm.SYM equation) fact
        | _ => raise ERR "to_target" "incorrect target premises")
      [bridge block target,proof clause] end

  fun align (target as Occurrences {graph,scope,literals = destination,...})
      (source as Clause {block,compact,layout,...}) =
    let
      val _ = active graph scope
      val _ = ignore (P.name block (root target))
      val _ = ignore (proof source)
      val small = C.align (compact_literals graph block destination) compact
    in case small of
        SOME result => SOME (finish source destination [source]
          (SOME target) result)
      | NONE => case layout of
          SOME original => if root original = root target then
            (* Two recorded outer boundaries for the same semantic root.
               Reframe through its compact name and checked constructors. *)
            SOME (from_source block target (to_target original source))
            else NONE
        | NONE => NONE
    end

  fun factor (source as Clause {compact,...}) =
    (ignore (proof source);
     finish source (literals source) [source] NONE (C.factor compact))

  fun resolve_chain {pivots,premises,target} =
    case premises of
      [] => raise ERR "resolve_chain" "empty premise list"
    | (first as Clause {block,graph,...})::_ =>
        let
          val _ = List.app (checked_pair first) premises
          val _ = case target of NONE => ()
            | SOME layout => ignore (P.name block (root layout))
          val vocabulary = List.concat (List.map literals premises) @
            (case target of NONE => [] | SOME layout => recorded layout)
          val result = C.resolve_chain
            {pivots = compact_literals graph block pivots,
             premises = List.map (fn Clause {compact,...} => compact) premises,
             target = Option.map
               (compact_literals graph block o recorded) target}
        in Option.map (finish first vocabulary premises target) result end
  structure W=SmtReplayInvocationWork
  structure Scope=SmtReplayOwnedScopeReceipt
  structure F=SmtLib_GraphFrontend
  structure Parser=SmtLib_Parser
  val _=SmtReplayInvocationWork.semantic_policy
  val _=SmtReplayOwnedScopeReceipt.description_with_policy_for
  val _=SmtLib_GraphFrontend.clause_occurrences
  val _=SmtLib_Parser.construction_value
  datatype policy_occurrences=PolicyOccurrences of
    {work:W.portfolio,graph:G.graph,scope:G.scope,frame:Scope.receipt,
     root:G.node,tree:P.policy_clause_tree,
     expanded:P.policy_clause_tree option,literals:literal list,
     roots:G.node list,names:G.node list,guard:unit->unit}
  fun policy_tree_root(P.PolicyClauseFalse node)=node
    | policy_tree_root(P.PolicyClauseLiteral{node,...})=node
    | policy_tree_root(P.PolicyClauseOr{node,...})=node
  fun po_header expected(PolicyOccurrences{work,...})=
    if Portable.pointer_eq(expected,work)then ()else
      raise ERR "policy_occurrences" "different original Work"
  fun po_data expected
      (held as PolicyOccurrences{graph,scope,frame,root,tree,expanded,
        literals,roots,names,guard,...})=
    (po_header expected held;guard();
     {graph=graph,scope=scope,frame=frame,root=root,tree=tree,
      expanded=expanded,literals=literals,roots=roots,names=names})

  (* Factory owns one action. An alias remains one literal in tree;
     expanded is separate actual target-only constructor evidence. *)
  fun po_discover_role unit_atom expand_target expected frame
      (term:F.term)=
    ((let
        val owner=Scope.description_with_policy_for expected frame
        val graph= #graph owner val scope= #scope owner
        val sources= #sources owner val root_scope= #root owner
        val policy=W.semantic_policy expected
        val epoch=Type.type_epoch()val symbols=Term.term_epoch()
        val lexical= #scope term val target= #node term
        val nodes=ref([]:G.node list)
        val definitions=ref([]:G.node list)
        fun valid()=
          let val current=Scope.description_with_policy_for expected frame
              val _=W.validate_policy expected graph root_scope sources policy
              val _=G.validate_scope graph lexical
          in if Portable.pointer_eq(graph,#graph current)andalso
              scope= #scope current andalso
              Portable.pointer_eq(sources,#sources current)andalso
              root_scope= #root current andalso
              Type.type_epoch()=epoch andalso Term.term_epoch()=symbols
            then ()else raise ERR "policy_occurrences"
              "actual Source frame or epochs changed"end
        fun tick()=(valid();W.spend_policy expected 1)
        fun own current=
          (tick();G.validate_scope graph(G.node_scope graph current);
           if G.scope_visible graph scope(G.node_scope graph current)then ()
           else raise ERR "policy_occurrences" "clause node escapes frame";
           if List.exists(fn saved=>(tick();saved=current))(!nodes)then ()
           else nodes:=current:: !nodes)
        fun node current=
          (own current;
           if Type.compare(G.type_of graph current,Type.bool)=EQUAL then ()
           else raise ERR "policy_occurrences" "non-Boolean clause node")
        fun need_constructor current=
          let val _=own current
              val _=if List.exists(fn saved=>(tick();saved=current))
                  (!definitions)then ()else
                    definitions:=current:: !definitions
          in case G.view graph current of
              G.Application(operator,_)=>need_constructor operator
            | G.Constant _=>()
            | _=>raise ERR "policy_occurrences"
                "requested constructor has no fixed rator spine"end
        fun is_constant constant current=
          (tick();case G.view graph current of G.Constant _=>
            Term.same_const(G.representative graph current)constant
           | _=>false)
        fun operands constant arity current=
          let fun walk current arguments=
                (tick();case G.view graph current of
                    G.Application(operator,operand)=>
                      walk operator(operand::arguments)
                  | G.Constant _=>
                      if Term.same_const(G.representative graph current)
                          constant andalso List.length arguments=arity
                        then SOME arguments else NONE
                  | _=>NONE)
          in walk current []end
        val semantic_memo=ref
          (Redblackmap.mkDict Int.compare:
            (int,P.policy_clause_tree)Redblackmap.dict)
        fun memo_semantic current compute=
          let val key=G.node_id current
          in case Redblackmap.peek(!semantic_memo,key)of SOME tree=>tree
            | NONE=>
              let val tree=compute()
                  val _=tick()
                  val _=semantic_memo:=Redblackmap.insert
                    (!semantic_memo,key,tree)
              in tree end
          end
        val {literal_node,recorded,semantic}=SmtReplayNamedClause.discover
          {node=node,is_constant=is_constant,operands=operands,
           need_constructor=need_constructor,same_node=op =,
           occurrence_node=Parser.construction_value,root=policy_tree_root,
           clause_false=P.PolicyClauseFalse,
           clause_literal=P.PolicyClauseLiteral,clause_or=P.PolicyClauseOr,
           memo_semantic=memo_semantic,error=ERR "policy_occurrences"}
        fun build()=
          let val _=valid()
              val _=if G.scope_visible graph lexical scope orelse
                  G.scope_visible graph scope lexical then ()else
                raise ERR "policy_occurrences"
                  "parsed lexical frame is unrelated to requester"
              val _=node target
              val entries=F.clause_occurrences term
              val entries=case entries of [_]=>
                    if is_constant boolSyntax.F target then []else entries
                | _=>entries
              val(tree,literals)=if unit_atom then
                  let val(tree,value)=literal_node target
                  in(tree,[value])end
                else recorded entries target
              val expanded=if expand_target then SOME(semantic target)
                else NONE
              val _=valid()
              fun guard()=
                (valid();List.app(fn held=>
                  (G.validate_scope graph(G.node_scope graph held);
                   ignore(G.view graph held)))(!nodes))
              val _=guard()
          in PolicyOccurrences{work=expected,graph=graph,scope=scope,
            frame=frame,root=target,tree=tree,expanded=expanded,
            literals=literals,roots=List.rev(!definitions),
            names=List.rev(!nodes),guard=guard}end
    in W.with_step expected build end)
     handle primary=>(W.close expected;raise primary))

  fun po_discover expand_target expected frame term=
    po_discover_role false expand_target expected frame term

  fun discover_recorded_with_policy expected frame term=
    po_discover false expected frame term
  fun discover_target_with_policy expected frame term=
    po_discover true expected frame term

  fun roots_with_policy_for expected saved=
    ((#roots(po_data expected saved))
     handle primary=>(W.close expected;raise primary))
  fun recorded_with_policy_for expected saved=
    ((#literals(po_data expected saved))
     handle primary=>(W.close expected;raise primary))

  fun names_with_policy_for expected saved=
    ((#names(po_data expected saved))
     handle primary=>(W.close expected;raise primary))

  datatype policy_clause=PolicyClause of
    {work:W.portfolio,block:P.block,occurrences:policy_occurrences,
     edge:P.edge}
  datatype policy_resolution=PolicyResolution of
    {work:W.portfolio,block:P.block,target:policy_occurrences,
     premises:policy_clause list,plan:P.policy_unit_resolution_plan}
  val _=SmtReplayProof.policy_native_block_owner_for
  val _=SmtReplayProof.prepare_unit_resolution_with_policy
  val _=SmtReplayProof.execute_unit_resolution_with_policy
  fun pc_header expected(PolicyClause{work,...})=
    if Portable.pointer_eq(expected,work)then ()else
      raise ERR "policy_clause" "different original Work"
  fun po_for_block expected block
      (saved as PolicyOccurrences{graph,scope,...})=
    let val _=po_header expected saved
        val owner=P.policy_native_block_owner_for expected block
        (* Immutable headers precede either occurrence's retained guards. *)
        val _=if Portable.pointer_eq(graph,#graph owner)andalso
            scope= #scope owner then ()else
          raise ERR "policy_clause" "different actual Block frame"
    in po_data expected saved end
  fun pc_data expected
      (saved as PolicyClause{block,occurrences,edge,...})=
    let val _=pc_header expected saved
        val data=po_for_block expected block occurrences
    in{block=block,occurrences=occurrences,edge=edge,tree= #tree data}end
  (* Factories and both native phases own their Work action. They never
     call GP factories/queries or another action-owning clause operation. *)
  fun from_source_with_policy expected block occurrences edge=
    ((let val _=po_header expected occurrences
      in W.with_step expected(fn()=>
        let val data=po_for_block expected block occurrences
            val proof=P.theorem block edge
            val _=if Portable.pointer_eq(Thm.concl proof,
                P.name block(#root data))then ()else
              raise ERR "policy_clause" "edge has another actual root"
        in PolicyClause{work=expected,block=block,
          occurrences=occurrences,edge=edge}end)end)
     handle primary=>(W.close expected;raise primary))
  fun prepare_resolution_with_policy expected
      {premises,target,check_type}=
    ((let val _=List.app(pc_header expected)premises
          val _=po_header expected target
          val first=case premises of []=>raise ERR "policy_clause"
              "empty ordered resolution"|held::_=>held
          val PolicyClause{block,...}=first
          val _=List.app(fn PolicyClause{block=other,...}=>
            if Portable.pointer_eq(block,other)then ()else
              raise ERR "policy_clause" "different actual Blocks")premises
      in W.with_step expected(fn()=>
        let val target_data=po_for_block expected block target
            val inputs=List.map(fn clause=>
              let val data=pc_data expected clause
              in{tree= #tree data,edge= #edge data}end)premises
            fun guards()=
              (ignore(po_for_block expected block target);
               List.app(fn held=>ignore(pc_data expected held))premises)
            fun admitted_type ty=
              (guards();check_type ty;guards())
            val plan=P.prepare_unit_resolution_with_policy expected block
              {premises=inputs,target= #tree target_data,
               target_expanded= #expanded target_data,
               check_type=admitted_type}
        in PolicyResolution{work=expected,block=block,target=target,
          premises=premises,plan=plan}end)end)
     handle primary=>(W.close expected;raise primary))
  fun execute_resolution_with_policy expected
      (saved as PolicyResolution{work,...})=
    ((if Portable.pointer_eq(expected,work)then ()else
        raise ERR "policy_clause" "different original Work";
      let val PolicyResolution{block,target,premises,plan,...}=saved
          val _=po_header expected target
          val _=List.app(pc_header expected)premises
      in W.with_step expected(fn()=>
        let val _=ignore(po_for_block expected block target)
            val _=List.app(fn held=>ignore(pc_data expected held))premises
            val edge=P.execute_unit_resolution_with_policy expected plan
            val _=ignore(po_for_block expected block target)
            val _=List.app(fn held=>ignore(pc_data expected held))premises
        in edge end)end)
     handle primary=>(W.close expected;raise primary))

  (* Distinct Boolean tags model compact named syntax, not equality of
     original semantic Terms. Node keys denote authentic typed names only. *)
  datatype policy_raw_occurrences=PolicyRawOccurrences of
    {work:W.portfolio,graph:G.graph,scope:G.scope,
     head:policy_occurrences,units:policy_occurrences list,
     target:policy_occurrences,fallbacks:P.policy_clause_tree list,
     roots:G.node list,names:G.node list,guard:unit->unit}
  fun raw_header expected(PolicyRawOccurrences{work,...})=
    if Portable.pointer_eq(expected,work)then ()else
      raise ERR "raw_resolution" "different original Work"
  fun raw_data expected
      (saved as PolicyRawOccurrences{head,units,target,fallbacks,
        roots,names,guard,...})=
    (raw_header expected saved;guard();
     {head=head,units=units,target=target,fallbacks=fallbacks,
      roots=roots,names=names})

  fun discover_raw_resolution_with_policy expected frame
      {head,units,target}=
    ((let
        val data=Scope.description_with_policy_for expected frame
        val graph= #graph data val scope= #scope data
        (* These factories own separate actions. No caller action encloses
           them; the following metadata phase has no external callback. *)
        val first=discover_recorded_with_policy expected frame head
        val rest=List.map(po_discover_role true false expected frame)units
        val wanted=discover_target_with_policy expected frame target
        val tokens=first::wanted::rest
        val epoch=Type.type_epoch()val symbols=Term.term_epoch()
        fun guard()=
          (List.app(fn held=>ignore(po_data expected held))tokens;
           if Type.type_epoch()=epoch andalso Term.term_epoch()=symbols
             then ()else raise ERR "raw_resolution" "epochs changed")
        fun header()=
          let val now=Scope.description_with_policy_for expected frame
          in if Portable.pointer_eq(graph,#graph now)andalso
              scope= #scope now andalso Type.type_epoch()=epoch andalso
              Term.term_epoch()=symbols then ()else
            raise ERR "raw_resolution" "actual frame changed"end
        fun tick()=(header();W.spend_policy expected 1)
        fun fail text=raise ERR "raw_resolution" text
        fun metadata()=
          let
            val _=guard()
            val roots=ref(List.concat(List.map
              (fn saved=> #roots(po_data expected saved))tokens))
            val names=ref(List.concat(List.map
              (fn saved=> #names(po_data expected saved))tokens))
            val held_nodes=ref([]:G.node list)
            fun own node=
              (tick();G.validate_scope graph(G.node_scope graph node);
               if G.scope_visible graph scope(G.node_scope graph node)then ()
               else fail "fallback node escapes actual frame";
               if List.exists(fn held=>(tick();held=node))(!held_nodes)
                 then ()else held_nodes:=node:: !held_nodes;
               if List.exists(fn held=>(tick();held=node))(!names)then ()
               else names:=node:: !names)
            fun boolean node=
              (own node;if Type.compare(G.type_of graph node,Type.bool)=EQUAL
                then ()else fail "non-Boolean dictionary key")
            fun constructor node=
              (own node;
               if List.exists(fn held=>(tick();held=node))(!roots)then ()
               else roots:=node:: !roots;
               case G.view graph node of G.Constant _=>()
                 | G.Application(operator,operand)=>
                     (own operand;constructor operator)
                 | _=>fail "fallback lacks actual constructor spine")
            fun constant wanted node=
              (boolean node;case G.view graph node of G.Constant _=>
                 Term.same_const(G.representative graph node)wanted
               | _=>false)
            fun operands wanted arity node=
              let fun walk current arguments=
                    (own current;case G.view graph current of
                        G.Application(operator,operand)=>
                          (own operand;walk operator(operand::arguments))
                      | G.Constant _=>
                          if Term.same_const(G.representative graph current)
                              wanted andalso List.length arguments=arity
                            then SOME arguments else NONE
                      | _=>NONE)
              in walk node []end
            val reversed_fallbacks=SmtReplayRawClause.discover
              {tick=tick,header=header,error=ERR "raw_resolution",
               boolean=boolean,constructor=constructor,constant=constant,
               operands=operands,node_key=G.node_id,
               compare_node=fn(x,y)=>Int.compare(G.node_id x,G.node_id y),
               compare_key=Int.compare,compare_ordinal=IntInf.compare,
               root=policy_tree_root,
               view=fn tree=>case tree of
                   P.PolicyClauseFalse node=>
                     SmtReplayNamedClause.ClauseFalse node
                 | P.PolicyClauseLiteral data=>
                     SmtReplayNamedClause.ClauseLiteral data
                 | P.PolicyClauseOr data=>SmtReplayNamedClause.ClauseOr data,
               literal=P.PolicyClauseLiteral,
               disjunction=P.PolicyClauseOr,
               copy=fn()=>(),write=fn()=>()}
              {head=fn()=> #tree(po_data expected first),units=rest,
               unit_tree=fn saved=> #tree(po_data expected saved),
               target=fn()=>
                 let val wanted_data=po_data expected wanted
                 in case #expanded wanted_data of SOME tree=>tree
                   | NONE=>fail "actual target expansion missing"end}
            fun retained_guard()=
              ((guard();List.app(fn node=>
                  (G.validate_scope graph(G.node_scope graph node);
                   ignore(G.view graph node)))(!held_nodes))
               handle primary=>(W.close expected;raise primary))
            val _=retained_guard()
          in PolicyRawOccurrences{work=expected,graph=graph,scope=scope,
            head=first,units=rest,target=wanted,
            fallbacks=List.rev reversed_fallbacks,roots= !roots,names= !names,
            guard=retained_guard}end
    in W.with_step expected metadata end)
     handle primary=>(W.close expected;raise primary))

  fun raw_roots_with_policy_for expected saved=
    ((#roots(raw_data expected saved))
     handle primary=>(W.close expected;raise primary))
  fun raw_names_with_policy_for expected saved=
    ((#names(raw_data expected saved))
     handle primary=>(W.close expected;raise primary))
  fun raw_fallback_count_with_policy_for expected saved=
    ((List.length(#fallbacks(raw_data expected saved)))
     handle primary=>(W.close expected;raise primary))

  fun prepare_raw_resolution_with_policy expected block
      (saved as PolicyRawOccurrences{work,graph,scope,...})
      {premises,check_type}=
    ((raw_header expected saved;
      let val owner=P.policy_native_block_owner_for expected block
          val _=if Portable.pointer_eq(graph,#graph owner)andalso
              scope= #scope owner then ()else
            raise ERR "raw_resolution" "different actual Block frame"
      in W.with_step expected(fn()=>
        let val data=raw_data expected saved
            val sources= #head data:: #units data
            val _=if List.length premises=List.length sources then ()else
              raise ERR "raw_resolution" "ordered premise arity changed"
            fun source(occurrences,edge)=
              let val actual=po_for_block expected block occurrences
                  val proof=P.theorem block edge
                  val _=if Portable.pointer_eq(Thm.concl proof,
                      P.name block(#root actual))then ()else
                    raise ERR "raw_resolution" "actual premise differs"
              in PolicyClause{work=expected,block=block,
                occurrences=occurrences,edge=edge}end
            val clauses=ListPair.mapEq source(sources,premises)
            val target= #target data
            val wanted=po_for_block expected block target
            fun guards()=
              (ignore(raw_data expected saved);
               ignore(po_for_block expected block target);
               List.app(fn held=>ignore(pc_data expected held))clauses)
            fun admitted_type ty=(guards();check_type ty;guards())
            val inputs=List.map(fn held=>
              let val actual=pc_data expected held
              in{tree= #tree actual,edge= #edge actual}end)clauses
            val plan=P.prepare_raw_unit_resolution_with_policy expected block
              {premises=inputs,target= #tree wanted,
               target_expanded= #expanded wanted,fallbacks= #fallbacks data,
               check_type=admitted_type}
            val _=guards()
        in PolicyResolution{work=expected,block=block,target=target,
          premises=clauses,plan=plan}end)end)
     handle primary=>(W.close expected;raise primary))

end
