(* Immutable lexical DATA; no parser, Source or proof authority. *)
structure SmtLib_GraphParserMapping :> SmtLib_GraphParserMapping =
struct
  structure G = SmtReplayGraph
  structure Q = SmtLib_GraphQueryAnalysis
  structure S = SmtLib_GraphCarrierStore
  val ERR = Feedback.mk_HOL_ERR "SmtLib_GraphParserMapping"
  type node_id = int
  type slot = int
  datatype arity = Exact of int | AtMost of int
  datatype graph_reference = Reference of
    {owner:unit ref,node:G.node,closure:G.closure_child,free:G.node list,
     hol_type:Type.hol_type}
  datatype form =
      ExistingGraph of graph_reference
    | Constant of Term.term
    | FreeVariable of
        {identity:int,kind:G.variable_kind,lexical:Term.term}
    | BoundSlot of slot
    | Application of node_id * node_id
    | Abstraction of {slot:slot,lexical:Term.term,body:node_id}
  type entry = {id:node_id,hol_type:Type.hol_type,form:form}
  type dependency =
    {slot:slot,kind:G.variable_kind,lexical:Term.term,
     hol_type:Type.hol_type}
  datatype origin = Ordinary of node_id
    | Fallback of {dependencies:dependency list,expression:node_id}
  type declaration =
    {token:string,rank:int,arity:arity,value:node_id,origin:origin,
     hol_type:Type.hol_type,sorts:(string list * string) option}
  datatype mapping = Mapping of
    {owner:unit ref,graph:G.graph,scope:G.scope,epoch:int,symbols:int,
     nodes:(node_id,entry) Redblackmap.dict,declarations:declaration list,
     types:(Type.hol_type,string) Redblackmap.dict}

  fun header (Mapping {graph,scope,epoch,symbols,...}) =
    (G.validate_semantic_scope graph scope;
     if Type.type_epoch () = epoch andalso Term.term_epoch () = symbols
       then () else raise ERR "mapping" "Type or Term epoch changed")
  fun reference_node (mapping as Mapping {owner,graph,scope,...})
      (Reference {owner=held,node,closure,free,hol_type}) =
    (if Portable.pointer_eq (owner,held) then () else
       raise ERR "reference" "different parser mapping";
     header mapping;
     if G.closure_child_node graph scope closure = node then () else
       raise ERR "reference" "graph alias endpoint changed";
     if Type.compare (G.type_of graph node,hol_type) = EQUAL then () else
       raise ERR "reference" "graph alias type changed";
     List.app (fn current =>
       if G.scope_visible graph scope (G.node_scope graph current) then ()
       else raise ERR "reference" "free ID escaped its original scope") free;
     node)
  fun check_entry mapping ({form=ExistingGraph reference,...}:entry) =
        ignore (reference_node mapping reference)
    | check_entry _ _ = ()
  fun validate (mapping as Mapping {nodes,...}) =
    (header mapping;
     Redblackmap.foldl (fn (_,value,()) => check_entry mapping value) () nodes)
  fun validate_for expected scope
      (mapping as Mapping {graph,scope=held,...}) =
    (if Portable.pointer_eq (expected,graph) andalso scope=held then () else
       raise ERR "mapping" "different expected graph or scope";
     validate mapping)
  fun entries (mapping as Mapping {nodes,...}) =
    (validate mapping;List.map #2 (Redblackmap.listItems nodes))
  fun entry (mapping as Mapping {nodes,...}) id =
    let val _ = header mapping
        val result = case Redblackmap.peek (nodes,id) of
            SOME result => result
          | NONE => raise ERR "entry" "unknown lexical node"
        val _ = check_entry mapping result
    in result end
  fun declarations (mapping as Mapping {declarations,...}) =
    (validate mapping;declarations)
  fun types (mapping as Mapping {types,...}) = (header mapping;types)

  type environment = (int * slot) list
  type memo_key = (int * int) * environment
  fun compare_pair ((a,b),(c,d)) =
    case Int.compare (a,c) of EQUAL => Int.compare (b,d) | order => order
  fun compare_memo ((left,le),(right,re)) =
    case compare_pair (left,right) of
      EQUAL => List.collate compare_pair (le,re) | order => order
  datatype task = Visit of Q.carrier * environment
    | FinishApplication of Q.carrier * environment * Type.hol_type *
        Q.carrier * Q.carrier
    | FinishAbstraction of Q.carrier * environment * Type.hol_type *
        slot * Term.term * Q.carrier * environment

  fun freeze_with_inputs (context:Q.outbound_context)
      {graph,scope,regime,types,symbols,inputs} =
    let
      val owner = ref ()
      val epoch = Type.type_epoch () val signature_epoch = Term.term_epoch ()
      fun live () =
        (ignore ((#key context) (#goal context));
         G.validate_semantic_scope graph scope;
         if Type.type_epoch () = epoch andalso
             Term.term_epoch () = signature_epoch then () else
           raise ERR "freeze" "Type or Term epoch changed")
      val _ = live ()
      (* Copy entries rather than retaining a caller-supplied comparator. *)
      val frozen_types = Redblackmap.foldl
        (fn (ty,name,dictionary) => Redblackmap.insert (dictionary,ty,name))
        (Redblackmap.mkDict Type.compare) types
      val roots = #roots (#set_analysis (#analysis context))
      val _ = List.app (fn {scope=held,node} =>
        (if held=scope then () else
           raise ERR "freeze" "different query scope";
         if G.scope_visible graph scope (G.node_scope graph node) then () else
           raise ERR "freeze" "query root escaped its original scope")) roots
      val memo = ref (Redblackmap.mkDict compare_memo)
      val nodes = ref (Redblackmap.mkDict Int.compare)
      val next_node = ref 0 val next_slot = ref 0 val next_free = ref 0
      val free_ids = ref (Redblackmap.mkDict Int.compare)
      fun fresh counter =
        let val value = !counter val _ = counter := value+1 in value end
      fun key current environment : memo_key =
        ((#key context) current,environment)
      fun remember current environment ty form =
        let val index = key current environment
            val id = fresh next_node
            val _ = nodes := Redblackmap.insert
              (!nodes,id,{id=id,hol_type=ty,form=form}:entry)
            val _ = memo := Redblackmap.insert (!memo,index,id)
        in id end
      fun saved current environment =
        Redblackmap.find (!memo,key current environment)
      fun bind current environment =
        let val _ = live ()
            val (kind,lexical) = case (#view context) current of
                Q.VariableView pair => pair
              | _ => raise ERR "freeze" "abstraction binder is not a variable"
            val identity = (#semantic_key context) current
            val slot = fresh next_slot
            val dependency : dependency =
              {slot=slot,kind=kind,lexical=lexical,
               hol_type=(#type_of context) current}
        in (dependency,(identity,slot)::environment) end
      (* Only atomic aliases use G's free-ID scan. Scanning every composite
         prefix separately would repeatedly traverse the same descendants. *)
      fun existing current ty =
        case (#graph_node context) current of NONE => NONE
          | SOME {node,...} =>
            if not (G.scope_visible graph scope (G.node_scope graph node))
              then NONE else
              let
                val atomic = case G.view graph node of
                    G.Variable _ => true | G.Constant _ => true | _ => false
                val free = if atomic then G.free_variable_nodes graph node
                  else NONE
                val _ = ignore ((#key context) current)
              in case free of NONE => NONE | SOME free =>
                if List.all (fn current => G.scope_visible graph scope
                    (G.node_scope graph current)) free then
                  SOME (ExistingGraph (Reference
                    {owner=owner,node=node,
                     closure=G.closure_root graph scope node,
                     free=free,hol_type=ty}))
                else NONE end
      fun variable current environment kind lexical =
        let val identity = (#semantic_key context) current
        in case List.find (fn (held,_) => held=identity) environment of
            SOME (_,slot) => BoundSlot slot
          | NONE =>
              let val id = case Redblackmap.peek (!free_ids,identity) of
                      SOME id => id
                    | NONE =>
                        let val id = fresh next_free
                            val _ = free_ids := Redblackmap.insert
                              (!free_ids,identity,id)
                        in id end
              in FreeVariable {identity=id,kind=kind,lexical=lexical} end
        end
      fun run [] = ()
        | run (Visit (current,environment)::rest) =
            let val _ = live () val index = key current environment
            in case Redblackmap.peek (!memo,index) of
                SOME _ => run rest
              | NONE =>
                let val _ = (#step context) ()
                    val ty = (#type_of context) current
                    val observed = (#view context) current
                    val candidate = case observed of
                        Q.VariableView _ =>
                          let val identity = (#semantic_key context) current
                          in case List.find (fn (held,_) => held=identity)
                              environment of
                              SOME (_,slot) => SOME (BoundSlot slot)
                            | NONE => existing current ty end
                      | Q.ConstantView _ => existing current ty
                      | _ => NONE
                in case candidate of
                    SOME form =>
                      (ignore (remember current environment ty form);run rest)
                  | NONE => (case observed of
                      Q.ConstantView atom =>
                        (ignore (remember current environment ty
                          (Constant atom));run rest)
                    | Q.VariableView (kind,lexical) =>
                        (ignore (remember current environment ty
                          (variable current environment kind lexical));
                         run rest)
                    | Q.ApplicationView (function,argument) =>
                        run (Visit (function,environment)::
                          Visit (argument,environment)::
                          FinishApplication (current,environment,ty,
                            function,argument)::rest)
                    | Q.AbstractionView (binder,body) =>
                        let val (dependency,inner) = bind binder environment
                        in run (Visit (body,inner)::FinishAbstraction
                          (current,environment,ty,#slot dependency,
                           #lexical dependency,body,inner)::rest) end)
                end
            end
        | run (FinishApplication
            (current,environment,ty,function,argument)::rest) =
            let val left = saved function environment
                val right = saved argument environment
                val (domain,range) = Type.dom_rng
                  (#hol_type (Redblackmap.find (!nodes,left)))
                val _ = if Type.compare (domain,
                    #hol_type (Redblackmap.find (!nodes,right))) = EQUAL
                    andalso Type.compare (range,ty) = EQUAL then () else
                  raise ERR "freeze" "application type mismatch"
                val _ = remember current environment ty
                  (Application (left,right))
            in run rest end
        | run (FinishAbstraction
            (current,environment,ty,slot,lexical,body,inner)::rest) =
            let val body = saved body inner
                val expected = Type.--> (Term.type_of lexical,
                  #hol_type (Redblackmap.find (!nodes,body)))
                val _ = if Type.compare (expected,ty) = EQUAL then () else
                  raise ERR "freeze" "abstraction type mismatch"
                val _ = remember current environment ty
                  (Abstraction {slot=slot,lexical=lexical,body=body})
            in run rest end
      fun freeze_value current environment =
        (run [Visit (current,environment)];saved current environment)
      fun add_abstraction (dependency:dependency,body) =
        let val id = fresh next_node
            val ty = Type.--> (#hol_type dependency,
              #hol_type (Redblackmap.find (!nodes,body)))
            val _ = nodes := Redblackmap.insert (!nodes,id,
              {id=id,hol_type=ty,form=Abstraction
                {slot= #slot dependency,lexical= #lexical dependency,
                 body=body}}:entry)
        in id end
      fun dependencies [] environment = ([],environment)
        | dependencies (current::rest) environment =
            let val (dependency,environment) = bind current environment
                val (tail,environment) = dependencies rest environment
            in (dependency::tail,environment) end
      fun function_arity ty count =
        case Lib.total Type.dom_rng ty of
          NONE => count | SOME (_,range) => function_arity range (count+1)
      fun declaration
          ({name,arity=rank,syntax,origin,sorts,...}:S.symbol) : declaration =
        let
          val _ = live () val _ = ignore ((#key context) syntax)
          val ty = (#type_of context) syntax
          val (value,origin) = case origin of
              S.Ordinary original =>
                let val value = freeze_value original []
                in (value,Ordinary value) end
            | S.Fallback {dependencies=inputs,expression} =>
                let val (parameters,environment) = dependencies inputs []
                    val body = freeze_value expression environment
                    val value = List.foldr add_abstraction body parameters
                in (value,Fallback
                  {dependencies=parameters,expression=body}) end
          val _ = if rank >= 0 andalso Type.compare
              (ty,#hol_type (Redblackmap.find (!nodes,value))) = EQUAL
              then () else raise ERR "freeze" "declaration contract mismatch"
          val arity = case regime of
              SmtLib.FirstOrder => Exact rank
            | SmtLib.HigherOrder _ => AtMost (function_arity ty 0)
          val _ = ignore ((#key context) syntax)
        in {token=name,rank=rank,arity=arity,value=value,origin=origin,
          hol_type=ty,sorts=sorts} end
      val declarations = List.map declaration symbols
      val inputs = List.map (fn current =>
        ((#step context) ();freeze_value current [])) inputs
      val _ = live ()
      val mapping = Mapping {owner=owner,graph=graph,scope=scope,
        epoch=epoch,symbols=signature_epoch,nodes= !nodes,
        declarations=declarations,types=frozen_types}
      val _ = validate mapping
    in {mapping=mapping,inputs=inputs} end
  fun freeze context {graph,scope,regime,types,symbols} =
    #mapping (freeze_with_inputs context
      {graph=graph,scope=scope,regime=regime,types=types,symbols=symbols,
       inputs=[]})
end
