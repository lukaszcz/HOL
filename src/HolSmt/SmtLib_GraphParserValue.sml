(* Typed parser DATA, with genuine graph leaves and owned closure frames. *)
structure SmtLib_GraphParserValue :> SmtLib_GraphParserValue =
struct
  structure G = SmtReplayGraph
  val ERR = Feedback.mk_HOL_ERR "SmtLib_GraphParserValue"
  datatype value = Value of {owner:unit ref,id:int}
  datatype view = Variable of G.variable_kind * Term.term
    | Constant of Term.term | RetainedGraph
    | Application of value * value
    | Abstraction of {binder:value,body:value,body_frame:G.scope}
  type entry =
    {scope:G.scope,hol_type:Type.hol_type,view:view,free:int list,
     graph_node:G.node option,closure:G.closure_child option,
     checked:(IntInf.int * IntInf.int) option ref}
  type owned_scope =
    {scope:G.scope,parent:G.scope,bindings:(Term.term * value) list,
     active:bool ref}
  datatype context = Context of
    {owner:unit ref,graph:G.graph,scope:G.scope,
     validate_owner:unit -> unit,spend_owner:IntInf.int -> unit,
     retire_owner:unit -> unit,
     epoch:int,symbols:int,active:bool ref,next:int ref,
     entries:(int,entry) Redblackmap.dict ref,
     leaves:(int,value) Redblackmap.dict ref,
     constructor_children:(int,value) Redblackmap.dict ref,
     mapped:(int,value) Redblackmap.dict ref,
     applications:((int * int * int),value) Redblackmap.dict ref,
     scopes:(int,owned_scope) Redblackmap.dict ref,order:owned_scope list ref}
  fun compare_application ((ls,lf,la),(rs,rf,ra)) =
    case Int.compare (ls,rs) of EQUAL =>
      (case Int.compare (lf,rf) of EQUAL => Int.compare (la,ra)
         | result => result) | result => result
  fun close (Context {active,graph,order,...}) =
    let
      val _ = active := false
      fun release ({scope,active,...}:owned_scope) =
        if not (!active) then () else
          (G.close_scope graph scope;active := false)
      fun releases [] failure =
            Option.app (fn primary => raise primary) failure
        | releases (scope::rest) failure =
            let val outcome = Exn.capture release scope
                val failure = case (failure,outcome) of
                    (NONE,Exn.Exn primary) => SOME primary | _ => failure
            in releases rest failure end
    in releases (!order) NONE end
  fun protected (context as Context {retire_owner,...}) action = action ()
    handle primary =>
      ((retire_owner () handle _ => ());
       (close context handle _ => ());raise primary)
  fun validate (context as Context
      {active,validate_owner,graph,scope,epoch,symbols,...}) =
    protected context (fn () =>
      (if !active then () else raise ERR "value" "parser value context closed";
       validate_owner ();
       G.validate_semantic_scope graph scope;
       if Type.type_epoch ()=epoch andalso Term.term_epoch ()=symbols then ()
       else raise ERR "value" "parser value declaration lifetime changed"))
  fun validate_for (context as Context {graph=held,scope=original,...})
      graph scope =
    protected context (fn () =>
      (if Portable.pointer_eq (graph,held) andalso scope=original then () else
         raise ERR "value" "different expected graph or scope";
       validate context))
  fun tick (context as Context {spend_owner,...}) amount =
    protected context (fn () => (validate context;spend_owner amount))
  val spend = tick
  fun protect context action = protected context
    (fn () => (tick context 0;action ()))
  fun create {graph,scope,validate=validate_owner,spend=spend_owner,
      retire=retire_owner} =
    ((let
      val _ = validate_owner ()
      val _ = G.validate_semantic_scope graph scope
    in Context {owner=ref (),graph=graph,scope=scope,
      validate_owner=validate_owner,spend_owner=spend_owner,
      retire_owner=retire_owner,epoch=Type.type_epoch (),
      symbols=Term.term_epoch (),active=ref true,next=ref 0,
      entries=ref (Redblackmap.mkDict Int.compare),
      leaves=ref (Redblackmap.mkDict Int.compare),
      constructor_children=ref (Redblackmap.mkDict Int.compare),
      mapped=ref (Redblackmap.mkDict Int.compare),
      applications=ref (Redblackmap.mkDict compare_application),
      scopes=ref (Redblackmap.mkDict Int.compare),order=ref []} end)
     handle primary => ((retire_owner () handle _ => ());raise primary))
  fun confined (context as Context {graph,scope,...}) caller =
    protected context (fn () =>
      (tick context 0;
       if G.scope_visible graph caller scope then () else
         raise ERR "scope" "caller is outside parser context root"))
  fun index (context as Context {owner,...}) (Value {owner=held,id}) =
    (validate context;
     if Portable.pointer_eq (owner,held) then id else
       raise ERR "value" "foreign parser value")
  fun saved (Context {entries,...}) id = Redblackmap.find (!entries,id)
  fun children ({view,...}:entry) = case view of
      Application (left,right) => [left,right]
    | Abstraction {binder,body,...} => [binder,body] | _ => []
  datatype guard_task = Enter of value | Leave of value
  fun guard context current = protected context (fn () =>
    let
      val _ = tick context 0
      val Context {graph,scope,...} = context
      val revision = G.validation_revision graph scope
      val retirement = G.scope_retirement_epoch graph scope
      val witness = (revision,retirement)
      fun run [] = ()
        | run (Leave current::rest) =
            let val row = saved context (index context current)
                val _ = #checked row := SOME witness
            in run rest end
        | run (Enter current::rest) =
            let val row = saved context (index context current) in
              if !(#checked row)=SOME witness then run rest else
                let
                  val _ = tick context 1
                  val _ = G.validate_scope graph (#scope row)
                  val _ = case (#graph_node row,#closure row) of
                      (SOME node,SOME closure) =>
                        if G.closure_child_node graph (#scope row) closure=node
                          then () else raise ERR "value" "graph leaf changed"
                    | (NONE,NONE) => ()
                    | _ => raise ERR "value" "invalid leaf backing"
                  val _ = case #view row of
                      Abstraction {body_frame,...} =>
                        G.validate_scope graph body_frame | _ => ()
                in run (List.map Enter (children row) @
                  (Leave current::rest)) end
            end
      val _ = run [Enter current]
    in validate context end)
  fun key context current = (guard context current;index context current)
  fun row context current = saved context (key context current)
  fun view context current = #view (row context current)
  fun type_of context current = #hol_type (row context current)
  fun scope_of context current = #scope (row context current)
  fun value (Context {owner,...}) id = Value {owner=owner,id=id}
  fun free_variables context current =
    let fun copy [] = []
          | copy (id::rest) =
              (tick context 1;value context id :: copy rest)
    in copy (#free (row context current)) end
  fun usable context caller current = protected context (fn () =>
    let val _ = confined context caller
        val row = row context current val Context {graph,...} = context
    in if G.scope_visible graph caller (#scope row) then () else
      raise ERR "value" "parser value escapes construction scope" end)
  fun remember (context as Context {entries,next,...}) scope ty syntax free
      graph_node =
    let
      val _ = tick context 1 val Context {graph,...} = context
      val _ = G.validate_scope graph scope
      val id = !next val _ = next := id+1
      val closure = Option.map (G.closure_root graph scope) graph_node
      val row:entry = {scope=scope,hol_type=ty,view=syntax,free=free,
        graph_node=graph_node,closure=closure,checked=ref NONE}
      val _ = entries := Redblackmap.insert (!entries,id,row)
    in value context id end
  fun graph_leaf context caller node = protected context (fn () =>
    let
      val _ = tick context 1 val _ = confined context caller
      val Context {graph,leaves,next,...} = context
      val scope = G.node_scope graph node
      val _ = if G.scope_visible graph caller scope then () else
        raise ERR "leaf" "graph leaf escapes caller"
    in case Redblackmap.peek (!leaves,G.node_id node) of
        SOME current => (guard context current;current)
      | NONE =>
          let val (syntax,free) = case G.view graph node of
                  G.Variable (kind,lexical) =>
                    (Variable (kind,lexical),[!next])
                | G.Constant _ =>
                    (Constant (G.representative graph node),[])
                | _ => raise ERR "leaf" "graph leaf is not atomic"
              val current = remember context scope (G.type_of graph node)
                syntax free (SOME node)
              val _ = leaves := Redblackmap.insert
                (!leaves,G.node_id node,current)
          in current end
    end)
  fun variable context scope kind lexical = protected context (fn () =>
    let val _ = tick context 1 val _ = confined context scope
        val Context {graph,...} = context
        val node = G.variable graph scope kind lexical
    in graph_leaf context scope node end)
  fun fresh_bound context scope lexical = protected context (fn () =>
    let val _ = tick context 1 val _ = confined context scope
        val Context {graph,...} = context
    in graph_leaf context scope
      (G.fresh_bound_variable graph scope lexical) end)
  fun fresh_flexible context scope lexical = protected context (fn () =>
    let val _ = tick context 1 val _ = confined context scope
        val Context {graph,...} = context
    in graph_leaf context scope
      (G.fresh_flexible_variable graph scope lexical) end)
  fun mapped_variable context scope {identity,kind,lexical} =
    protected context (fn () =>
      let val _ = tick context 1 val _ = confined context scope
          val Context {mapped,...} = context in
        case Redblackmap.peek (!mapped,identity) of
          SOME current =>
            let val _ = usable context scope current
                val _ = case view context current of
                    Variable (held,name) =>
                      if held=kind andalso Term.aconv name lexical then () else
                        raise ERR "mapped_variable" "mapping identity changed"
                  | _ => raise ERR "mapped_variable" "mapping identity changed"
            in current end
        | NONE =>
            let val Context {scope=root,next,...} = context
                val _ = if Term.is_var lexical then () else
                  raise ERR "mapped_variable" "mapping variable is not atomic"
                val current = remember context root (Term.type_of lexical)
                  (Variable (kind,lexical)) [!next] NONE
                val _ = mapped := Redblackmap.insert (!mapped,identity,current)
            in current end
      end)
  fun import context scope maximum original = protected context (fn () =>
    let
      val _ = tick context 1 val _ = confined context scope
      val Context {graph,...} = context
      val _ = case SmtReplayImport.raw_size_with_policy maximum original of
          SOME size => tick context size
        | NONE => raise ERR "import" "source exceeds bounded contract"
      val source = G.import_with_policy graph scope maximum original
      val node = #node source
    in case G.view graph node of
        G.Variable _ => graph_leaf context scope node
      | G.Constant _ => graph_leaf context scope node
      | _ =>
          let val free = List.map (fn lexical => graph_leaf context scope
                (G.resolve_variable graph scope lexical))
                (Term.free_vars original)
          in remember context scope (G.type_of graph node) RetainedGraph
            (List.map (key context) free) (SOME node) end
    end)
  fun constructor_view context current = protected context (fn () =>
    let
      val original = row context current
      val Context {graph,constructor_children,...} = context
      fun observed G.DependencyVisit = tick context 1
        | observed G.DependencyCompare = tick context 1
        | observed (G.DependencyExcluded entries) =
            tick context (IntInf.fromInt (length entries)+1)
        | observed (G.DependencyVisited entries) =
            tick context (IntInf.fromInt (length entries)+1)
        | observed _ = tick context 1
      fun child node =
        let val _ = tick context 1 in
          case Redblackmap.peek (!constructor_children,G.node_id node) of
            SOME value => (guard context value;SOME value)
          | NONE => case G.view graph node of
              G.Variable _ => SOME (graph_leaf context (#scope original) node)
            | G.Constant _ => SOME (graph_leaf context (#scope original) node)
            | _ => case G.free_variable_nodes_observed observed graph node of
                NONE => NONE
              | SOME variables =>
                  let val free = List.map (fn variable =>
                        (tick context 1;
                         key context (graph_leaf context
                           (#scope original) variable))) variables
                      val value = remember context (#scope original)
                        (G.type_of graph node) RetainedGraph free (SOME node)
                      val _ = constructor_children := Redblackmap.insert
                        (!constructor_children,G.node_id node,value)
                  in SOME value end
        end
    in case (#view original,#graph_node original) of
        (RetainedGraph,SOME node) =>
          (case G.view graph node of
             G.Application (f,x) =>
               (case (child f,child x) of
                  (SOME f,SOME x) => Application (f,x)
                | _ => RetainedGraph)
           | _ => RetainedGraph)
      | _ => #view original
    end)

  fun literal context scope maximum original = protected context (fn () =>
    let val _ = tick context 1 val _ = confined context scope
        val _ = case SmtReplayImport.raw_size_with_policy maximum original of
            SOME _ => () | NONE =>
              raise ERR "literal" "literal exceeds bounded contract"
        val _ = if null (Term.free_vars original) then () else
          raise ERR "literal" "literal contains an unowned free variable"
    in if Term.is_const original then
        let val Context {graph,...} = context
        in graph_leaf context scope (G.constant graph scope original) end
      else import context scope maximum original end)
  fun union context left right =
    let val _ = tick context (IntInf.fromInt (length left+length right))
    in Redblackset.listItems (Redblackset.addList
      (Redblackset.addList (Redblackset.empty Int.compare,left),right)) end
  fun application_body on_type_error context scope (function,argument) =
    let
      val _ = tick context 1
      val _ = usable context scope function
      val _ = usable context scope argument
      val (domain,range) = Type.dom_rng (type_of context function)
        handle error as Feedback.HOL_ERR _ =>
          (on_type_error error;raise error)
      val _ = if Type.compare (domain,type_of context argument)=EQUAL then ()
        else let val error=ERR "application" "application operand type mismatch"
             in on_type_error error;raise error end
      val index = (G.scope_id scope,key context function,key context argument)
      val Context {applications,...} = context
    in case Redblackmap.peek (!applications,index) of
        SOME current => (guard context current;current)
      | NONE =>
          let val free = union context (#free (row context function))
                (#free (row context argument))
              val current = remember context scope range
                (Application (function,argument)) free NONE
              val _ = applications := Redblackmap.insert
                (!applications,index,current)
          in current end
    end
  fun application context scope operands =
    protected context (fn () => application_body ignore context scope operands)
  exception IndexApplicationTypeError of exn
  fun index_application context scope operands =
    application_body (fn error => raise IndexApplicationTypeError error)
      context scope operands
    handle typed as IndexApplicationTypeError _ => raise typed
      | primary => protected context (fn () => raise primary)
  fun abstraction context scope {binder,body,body_frame} =
    protected context (fn () =>
      let
        val _ = tick context 1 val _ = confined context scope
        val _ = confined context body_frame
        val Context {graph,...} = context
        val _ = usable context body_frame binder
        val _ = usable context body_frame body
        val _ = case view context binder of Variable (G.Bound,_) => ()
          | _ => raise ERR "abstraction" "binder is not an owned Bound value"
        val Context {scopes,...} = context
        val binder_row = row context binder
        val _ = case (#graph_node binder_row,
            Redblackmap.peek (!scopes,G.scope_id (#scope binder_row))) of
            (SOME _,SOME {active,...}) =>
              if !active then () else
                raise ERR "abstraction" "binder construction frame closed"
          | _ => raise ERR "abstraction" "binder lacks owned graph identity"
        val _ = if G.scope_visible graph body_frame scope then () else
          raise ERR "abstraction" "body frame outside declaring scope"
        val identity = key context binder
        fun exclude [] = []
          | exclude (id::rest) =
              (tick context 1;
               if id=identity then exclude rest else id::exclude rest)
        val free = exclude (#free (row context body))
        val _ = List.app (fn id =>
          usable context scope (value context id)) free
        val ty = Type.--> (type_of context binder,type_of context body)
      in remember context scope ty
        (Abstraction {binder=binder,body=body,body_frame=body_frame}) free NONE
      end)
  fun register_scope (context as Context {scopes,order,...}) scope parent
      bindings =
    let val row:owned_scope =
          {scope=scope,parent=parent,bindings=bindings,active=ref true}
        val _ = order := row :: !order
        val _ = scopes := Redblackmap.insert (!scopes,G.scope_id scope,row)
    in scope end
  fun new_scope context parent bindings = protected context (fn () =>
    let val _ = tick context 2 val _ = confined context parent
        val Context {graph,...} = context
        val _ = List.app (fn (lexical,current) =>
          (usable context parent current;
           if Term.is_var lexical andalso
               Type.compare
                 (Term.type_of lexical,type_of context current)=EQUAL
             then () else raise ERR "scope" "ill-typed lexical binding"))
          bindings
        val scope = G.new_scope graph parent []
    in register_scope context scope parent bindings end)
  fun new_construction_scope context
      (request as {lexical,construction}) =
    protected context (fn () =>
      let
        val _ = tick context 2
        val _ = confined context lexical
        val _ = confined context construction
        val Context {graph,scopes,...} = context
        fun collect current =
          if current=construction then [] else
            case Redblackmap.peek (!scopes,G.scope_id current) of
                NONE => []
              | SOME {scope=held,parent,bindings,active} =>
                  let val _ = tick context 1
                      val _ = if held=current andalso !active then () else
                        raise ERR "scope" "lexical alias frame retired"
                      fun append [] tail = tail
                        | append (binding::rest) tail =
                            (tick context 1;binding::append rest tail)
                  in append bindings (collect parent) end
        val bindings = collect lexical
        val scope = G.new_construction_scope graph request
      in register_scope context scope construction bindings end)
  (* Scope creation prepays its eventual release. Cleanup must remain
     available after Work/context retirement and must not mask a Primary.
     Only scopes found in this context's private owned table can close. *)
  fun close_scope (Context {graph,scopes,...}) scope =
    case Redblackmap.peek (!scopes,G.scope_id scope) of
        SOME {scope=held,active,...} =>
          if held<>scope then raise ERR "scope" "foreign owned scope"
          else if !active then
            (G.close_scope graph scope;active := false) else ()
      | NONE => raise ERR "scope" "scope is not owned by parser values"
  fun lexical_lookup context caller lexical =
    let
      val _ = confined context caller
      val Context {graph,scopes,...} = context
      fun lookup scope =
        let val _ = tick context 1 val _ = G.validate_scope graph scope in
          case Redblackmap.peek (!scopes,G.scope_id scope) of NONE => NONE
          | SOME {parent,bindings,...} =>
              (case List.find (fn (name,_) => Term.aconv name lexical)
                  bindings of
                 SOME (_,current) => SOME current | NONE => lookup parent)
        end
    in lookup caller end
  fun resolve_variable context caller lexical = protected context (fn () =>
    case lexical_lookup context caller lexical of
        SOME current => (usable context caller current;current)
      | NONE => let val Context {graph,...} = context in
          graph_leaf context caller (G.resolve_variable graph caller lexical)
        end)
  fun reference context caller (lexical,default) = protected context (fn () =>
    let
      val _ = confined context caller
      val _ = guard context default val Context {graph,...} = context
    in case lexical_lookup context caller lexical of
        SOME current => (usable context caller current;current)
      | NONE =>
          (case #graph_node (row context default) of
             SOME node =>
               (case view context default of Variable _ =>
                  graph_leaf context caller
                    (G.resolve_reference graph caller lexical node)
                | _ => (usable context caller default;default))
           | NONE => (usable context caller default;default))
    end)

  datatype natural_index = NaturalIndex of Arbnum.num
    | ExpandedIndex | OpaqueIndex | NonNaturalIndex
  datatype index_term = ParserIndexTerm of value | GraphIndexTerm of G.node
  datatype index_view = IndexAtom of Term.term
    | IndexApplication of index_term * index_term
    | IndexBinder of index_term
    | IndexOther of IntInf.int option

  fun natural_index_with_policy context maximum original =
    protected context (fn () =>
    let
      val _ = guard context original
      val _ = tick context 64
      val Context {graph,scope,...} = context
      exception NotNumber
      fun normalize (current as ParserIndexTerm value) =
            let val held = row context value in
              case (#view held,#graph_node held) of
                  (RetainedGraph,SOME node) => GraphIndexTerm node
                | (RetainedGraph,NONE) =>
                    raise ERR "natural_index" "missing retained backing"
                | _ => current
            end
        | normalize current = current
      fun guarded action = protected context (fn () =>
        (guard context original;tick context 4;action ()))
      fun identity current = guarded (fn () => case normalize current of
          ParserIndexTerm value => (0,key context value)
        | GraphIndexTerm node =>
            (ignore (G.type_of graph node);(1,G.node_id node)))
      fun compare_key ((lr,lk,ln),(rr,rk,rn)) =
        (tick context 1;
         case IntInf.compare (lr,rr) of EQUAL =>
           (case Int.compare (lk,rk) of EQUAL => Int.compare (ln,rn)
              | result => result)
         | result => result)
      val sizes = ref (Redblackmap.mkDict compare_key)
      val bit_values = ref (Redblackmap.mkDict compare_key)
      val naturals = ref (Redblackmap.mkDict compare_key)
      val integers = ref (Redblackmap.mkDict compare_key)
      fun memo table current compute =
        let val _ = guard context original
            val (kind,id) = identity current
            val revision = G.validation_revision graph scope
            val index = (revision,kind,id)
            val _ = tick context 1
        in case Redblackmap.peek (!table,index) of
            SOME answer => (guard context original;answer)
          | NONE =>
              let val answer = compute ()
                  val _ = guard context original
                  val _ = if G.validation_revision graph scope=revision then
                    (tick context 1;
                     table:=Redblackmap.insert (!table,index,answer)) else ()
              in answer end
        end
      fun observe current = guarded (fn () => case normalize current of
          ParserIndexTerm value =>
            (case view context value of
                Constant atom => IndexAtom atom
              | Application (left,right) => IndexApplication
                  (ParserIndexTerm left,ParserIndexTerm right)
              | Abstraction {body,...} => IndexBinder (ParserIndexTerm body)
              | Variable _ => IndexOther (SOME 1)
              | RetainedGraph =>
                  raise ERR "natural_index" "unresolved retained backing")
        | GraphIndexTerm node =>
            (case G.view graph node of
                G.Constant _ => IndexAtom (G.representative graph node)
              | G.Application (left,right) => IndexApplication
                  (GraphIndexTerm left,GraphIndexTerm right)
              | G.Variable _ => IndexOther (SOME 1)
              | _ => IndexOther (G.unfolded_nodes_with_policy graph
                  G.RawNodes maximum node)))
      fun bounded amount = case maximum of
          SmtReplayResourcePolicy.Uncapped => amount
        | SmtReplayResourcePolicy.AtMost bound =>
            if amount<=bound then amount else bound+1
      fun amount current =
        let val (kind,id) = identity current
            val revision = G.validation_revision graph scope
            val index = (revision,kind,id)
            val _ = tick context 1
        in case Redblackmap.peek (!sizes,index) of
            SOME answer => (guard context original;SOME answer)
          | NONE =>
              let val answer = case observe current of
                      IndexAtom _ => SOME 1
                    | IndexOther amount => amount
                    | IndexBinder body =>
                        Option.map (fn n => bounded (n+1)) (amount body)
                    | IndexApplication (left,right) =>
                        let val left = amount left val right = amount right
                        in case (left,right) of (SOME a,SOME b) =>
                          SOME (bounded (1+a+b)) | _ => NONE end
                  val _ = guard context original
                  val _ = case answer of NONE => () | SOME n =>
                    if G.validation_revision graph scope=revision then
                      (tick context 1;
                       sizes:=Redblackmap.insert (!sizes,index,n)) else ()
              in answer end
        end
      fun matches current expected = case observe current of
          IndexAtom atom => Term.same_const atom expected | _ => false
      fun application current = case observe current of
          IndexApplication pair => pair | _ => raise NotNumber
      fun unary expected current =
        let val (head,argument) = application current in
          if matches head expected then argument else raise NotNumber end
      fun bits current = memo bit_values current (fn () =>
        if matches current numSyntax.alt_zero_tm then (Arbnum.zero,0)
        else
          let val (head,argument) = application current
              val addition = if matches head numSyntax.bit1_tm then Arbnum.one
                else if matches head numSyntax.bit2_tm then Arbnum.two
                else raise NotNumber
              val (previous,depth) = bits argument
              val _ = tick context (depth+1)
          in (Arbnum.+ (Arbnum.* (Arbnum.two,previous),addition),depth+1) end)
      fun natural current = memo naturals current (fn () =>
        if matches current numSyntax.zero_tm then Arbnum.zero else
          #1 (bits (unary numSyntax.numeral_tm current)))
      fun integer current = memo integers current (fn () =>
        let val (head,argument) = application current in
          if matches head intSyntax.negate_tm then Arbint.~ (integer argument)
          else if matches head intSyntax.int_injection then
            Arbint.fromNat (natural argument)
          else raise NotNumber end)
      val root = ParserIndexTerm original
      val result = case amount root of NONE => OpaqueIndex
        | SOME size => if not (SmtReplayResourcePolicy.allows maximum size)
            then ExpandedIndex
            else
              ((NaturalIndex (natural root)
                handle NotNumber => NaturalIndex
                  (Arbint.toNat (integer root)))
               handle NotNumber => NonNaturalIndex)
      val _ = guard context original
    in result end)

  datatype lifetime_guard = LifetimeGuard of
    {context:context,paths:(G.scope * G.scope_path) list,
     leaves:(G.scope * G.node * G.closure_child) list,work:IntInf.int}
  fun prepare_lifetime_guard context {remaining_work,scopes,values} =
    protected context (fn () =>
    let
      val _ = tick context 1
      val Context {graph,...} = context
      val paths = ref ([]:(G.scope * G.scope_path) list)
      val leaves = ref ([]:(G.scope * G.node * G.closure_child) list)
      val seen = ref (Redblackset.empty (fn (a,b) =>
        (tick context 1;Int.compare (a,b))))
      fun known scope [] = (tick context 1;false)
        | known scope ((held,_)::rest) =
            (tick context 1;scope=held orelse known scope rest)
      fun capture scope =
        (confined context scope;
         if known scope (!paths) then () else
           let val path = G.prepare_scope_path_with_policy graph scope
                 {remaining_work=remaining_work ()}
               val _ = tick context (G.scope_path_setup_work path)
               val _ = tick context 2
           in paths := (scope,path):: !paths end)
      fun visit [] = tick context 1
        | visit (current::rest) =
          let val _ = guard context current val id = index context current in
            if Redblackset.member (!seen,id) then visit rest else
              let val _ = seen := Redblackset.add (!seen,id)
                  val row = saved context id
                  val _ = capture (#scope row)
                  val _ = case #view row of
                      Abstraction {body_frame,...} => capture body_frame
                    | _ => ()
                  val _ = case (#graph_node row,#closure row) of
                      (SOME node,SOME child) =>
                        (tick context 3;
                         leaves := (#scope row,node,child):: !leaves)
                    | (NONE,NONE) => ()
                    | _ => raise ERR "lifetime" "invalid retained backing"
              in visit (children row @ rest) end
          end
      val _ = List.app capture scopes
      val _ = visit values
      val actual_paths = List.rev (!paths)
      val actual_leaves = List.rev (!leaves)
      val work = List.foldl (fn ((_,path),total) =>
          (tick context 2;total+G.scope_path_validation_work path+3))
        (8:IntInf.int) actual_paths
      val work = List.foldl (fn (_,total) =>
          (tick context 2;total+6)) work actual_leaves
      val _ = validate context
    in LifetimeGuard {context=context,paths=actual_paths,
      leaves=actual_leaves,work=work} end)
  fun lifetime_guard_work (LifetimeGuard {work,...}) = work
  fun validate_lifetime_guard
      (LifetimeGuard {context,paths,leaves,...}) = protected context (fn () =>
    let val _ = validate context val Context {graph,...} = context
        val _ = List.app (fn (scope,path) =>
          G.validate_scope_path graph scope path) paths
        val _ = List.app (fn (scope,node,child) =>
          if G.closure_child_node graph scope child=node then () else
            raise ERR "lifetime" "retained parser leaf changed") leaves
    in validate context end)
  (* The old token remains read-only after an external fixed prequote.
     This separate token pays its actual branch inside the owning action.
     The original Context payer is the actual factory's same Work spender;
     using tick or a named/Upper payer here would repeat owner callbacks. *)
  datatype paid_lifetime_guard = PaidLifetimeGuard of
    {legacy:lifetime_guard,path:G.scope_path,common_work:IntInf.int,
     miss_work:IntInf.int,stamp:IntInf.int option ref}
  fun paid_lifetime_failure
      (context as Context {retire_owner,...}) primary =
    ((retire_owner () handle _ => ());
     (close context handle _ => ());raise primary)
  fun paid_lifetime_leaf_work (pay:IntInf.int -> unit) [] =
        (pay 1;0:IntInf.int)
    | paid_lifetime_leaf_work pay (_::rest) =
        (pay 3;6+paid_lifetime_leaf_work pay rest)
  fun prepare_paid_lifetime_guard context
      (request as {remaining_work,scopes,values}) =
    let val legacy=prepare_lifetime_guard context request in
    (let
      val LifetimeGuard {leaves,work,...}=legacy
      val Context {graph,scope,spend_owner=pay,...}=context
      (* Extra old-worker call1, remaining-policy bound26, path dispatch11,
         cost observations4, scalar arithmetic6, private envelope8, walker1.
         Destructuring the actual private records creates no new record. *)
      val _=pay 57
      val path=G.prepare_scope_path_with_policy graph scope
        {remaining_work=remaining_work ()}
      val setup=G.scope_path_setup_work path
      val _=pay setup
      val revision_work=G.scope_path_revision_work path
      val leaf_work=paid_lifetime_leaf_work pay leaves
      (* Retain only amounts derived from this actual guarded inventory.
         These six arithmetic operations are paid once above, not per hit. *)
      val common_work=work-leaf_work+2*revision_work+12
      val miss_work=leaf_work+revision_work+2
      (* The one additional context validation is actual: active2,
         owner call1, semantic-scope call1, epoch/control6, protection1. *)
      val _=pay 11
      val _=validate context
    in PaidLifetimeGuard {legacy=legacy,path=path,common_work=common_work,
      miss_work=miss_work,stamp=ref NONE}end)
    handle primary=>paid_lifetime_failure context primary
    end
  fun validate_paid_lifetime_guard
      (PaidLifetimeGuard {legacy=LifetimeGuard {context,paths,leaves,...},
        path,common_work,miss_work,stamp}) =
    (let
      val _=validate context
      val Context {graph,scope,spend_owner=pay,...}=context
      (* Retained common amount includes stamp read/case/equality3,
         hit/leaf branches2, final control2, publication at most2,
         query applications2 and failure-helper application1. No amount
         arithmetic or separate metadata payer is performed here. Both
         root queries and all context/path guards remain additional. *)
      val _=pay common_work
      (* A payer/owner callback may publish graph DATA: observe only after
         the preceding payer, never predict a hit from an earlier read. *)
      val revision=G.validation_revision_with_scope_path graph scope path
      val hit=case !stamp of SOME held=>held=revision | NONE=>false
      val checked_revision=if hit then revision else
        let
          (* Retained miss amount includes query application1/NONE write1.
             The sole miss payer can mutate declarations/scopes/graph. *)
          val _=pay miss_work
          val _=stamp:=NONE
        in G.validation_revision_with_scope_path graph scope path end
      (* Every actual captured live path is checked after the last payer,
         on hits as well as misses. The old leaf loop below is literal. *)
      val _ = List.app (fn (scope,path) =>
        G.validate_scope_path graph scope path) paths
      val _=if hit then () else
        List.app (fn (scope,node,child) =>
          if G.closure_child_node graph scope child=node then () else
            raise ERR "lifetime" "retained parser leaf changed") leaves
      val _=validate context
      (* Final owner callbacks are real. Changed graph publication does
         not bless a leaf scan from the preceding revision. No payer or
         external callback lies between this read and stamp publication. *)
      val after=G.validation_revision_with_scope_path graph scope path
      val _=if checked_revision=after then stamp:=SOME after else stamp:=NONE
    in ()end)
    handle primary=>paid_lifetime_failure context primary
  datatype graph_correspondence = Corresponding | DifferentGraphSyntax
    | NeedsGraphOpening of G.scope * G.node
  datatype comparison_term = ParserTerm of value
    | GraphTerm of G.scope * G.node
  fun corresponds_to_graph_with_policy context expected caller
      {value=original,node=target} = protected context (fn () =>
    let
      val Context {graph,scope,...} = context
      val _ = if Portable.pointer_eq (expected,graph) then () else
        raise ERR "correspondence" "different expected graph"
      val _ = validate context
      val _ = confined context caller
      val _ = usable context caller original
      val _ = ignore (G.closure_root graph caller target)
      fun step () = (guard context original;tick context 1)
      fun normalize (ParserTerm current) =
            let val held = row context current
            in case #graph_node held of SOME node =>
                  GraphTerm (#scope held,node)
              | NONE => ParserTerm current end
        | normalize current = current
      fun identity current =
        (step ();case normalize current of
            ParserTerm value => (0,key context value)
          | GraphTerm (frame,node) =>
              (ignore (G.closure_root graph frame node);(1,G.node_id node)))
      fun compare_pair ((la,lb),(ra,rb)) =
        (tick context 1;case Int.compare (la,ra) of
            EQUAL => Int.compare (lb,rb) | order => order)
      fun compare_environment ((left,a),(right,b)) =
        case compare_pair (left,right) of EQUAL => Int.compare (a,b)
          | order => order
      fun compare_key ((la,lf,ls,ln,le),(ra,rf,rs,rn,re)) =
        case compare_pair (la,ra) of EQUAL =>
          (case Int.compare (lf,rf) of EQUAL =>
          (case Int.compare (ls,rs) of EQUAL =>
             (case Int.compare (ln,rn) of EQUAL =>
                List.collate compare_environment (le,re) | order => order)
           | order => order) | order => order) | order => order
      val memo = ref (Redblackmap.mkDict compare_key)
      val type_weights=ref ([]:(Type.hol_type * IntInf.int) list)
      fun type_weight ty =
        let
          fun lookup []=NONE
            | lookup ((held,amount)::rest)=
                (step ();if Portable.pointer_eq (ty,held) then SOME amount
                 else lookup rest)
        in case lookup (!type_weights) of SOME amount=>amount
          | NONE=>
              let val _=step ()
                  val amount=if Type.is_vartype ty then
                      1+IntInf.fromInt (String.size (Type.dest_vartype ty))
                    else List.foldl (fn (child,total)=>
                      total+type_weight child) 1 (#2 (Type.dest_type ty))
                  val _=step ()
                  val _=type_weights:=(ty,amount):: !type_weights
              in amount end
        end
      fun same_type left right =
        let val a=type_weight left val b=type_weight right
            val _=tick context (1+a+b)
        in Type.compare (left,right)=EQUAL end
      fun same_constant left right =
        let val {Thy=a,Name=b,...}=Term.dest_thy_const left
            val {Thy=c,Name=d,...}=Term.dest_thy_const right
            val _=tick context (1+IntInf.fromInt (String.size a)+
              IntInf.fromInt (String.size b)+IntInf.fromInt (String.size c)+
              IntInf.fromInt (String.size d))
        in Term.same_const left right end
      fun compare current frame node environment =
        let
          val _ = step ()
          val current = normalize current
          val _ = G.validate_scope graph frame
          val _ = ignore (G.closure_root graph frame node)
          val id = identity current
          val environment_key = List.map (fn (left,right) =>
            (step ();(left,G.node_id right))) environment
          val left_frame = case current of ParserTerm value =>
                scope_of context value | GraphTerm (scope,_) => scope
          val _ = G.validate_scope graph left_frame
          val index = (id,G.scope_id left_frame,G.scope_id frame,
            G.node_id node,environment_key)
          fun result () =
            let
              val bound = List.find (fn (held,_) => (step ();held=id))
                environment
              val captured = List.exists (fn (_,held) => (step ();held=node))
                environment
              val ty = case current of ParserTerm value =>
                    type_of context value
                | GraphTerm (_,left) => G.type_of graph left
              val _ = tick context 1
            in if not (same_type ty (G.type_of graph node)) then
                DifferentGraphSyntax
              else case bound of SOME (_,actual) =>
                  if actual=node then Corresponding else DifferentGraphSyntax
                | NONE => if captured then DifferentGraphSyntax else
                  compare_unbound current frame node environment
            end
        in case Redblackmap.peek (!memo,index) of
            SOME answer => (step ();answer)
          | NONE =>
              let val answer = result () val _ = step ()
                  val _ = G.validate_scope graph frame
                  val _ = ignore (G.closure_root graph frame node)
                  val _ = memo := Redblackmap.insert (!memo,index,answer)
              in answer end
        end
      and compare_unbound current frame node environment =
        case current of GraphTerm (_,left) =>
            if left=node andalso null environment then Corresponding else
              compare_views current frame node environment
          | _ => compare_views current frame node environment
      and compare_views current frame node environment =
        let
          fun application (left,right) (a,b) =
            case compare left frame a environment of Corresponding =>
              compare right frame b environment | result => result
          fun binder left body left_frame =
            let
              val closure = G.binder_closure graph frame node
              val data = G.binder_closure_data graph frame closure
              val left_id = identity left
              val _ = G.validate_scope graph left_frame
              val _ = if same_type
                  (case left of ParserTerm value => type_of context value
                     | GraphTerm (_,value) => G.type_of graph value)
                  (G.type_of graph (#binder data)) then () else
                raise ERR "correspondence" "binder type differs"
            in compare body (#body_frame data) (#body data)
              ((left_id,#binder data)::environment) end
          val right = G.view graph node
        in case right of G.OpaqueRetained => NeedsGraphOpening (frame,node)
          | _ =>
            (case current of ParserTerm value =>
                (case view context value of
                    Constant atom =>
                      (case right of G.Constant _ =>
                         if same_constant atom (G.representative graph node)
                           then Corresponding else DifferentGraphSyntax
                       | _ => DifferentGraphSyntax)
                  | Application (left,right_value) =>
                      (case right of G.Application pair =>
                         application (ParserTerm left,ParserTerm right_value)
                           pair | _ => DifferentGraphSyntax)
                  | Abstraction {binder=left,body,body_frame} =>
                      (case right of G.AdmittedBinder _ =>
                         binder (ParserTerm left) (ParserTerm body) body_frame
                       | _ => DifferentGraphSyntax)
                  | Variable _ => DifferentGraphSyntax
                  | RetainedGraph =>
                      raise ERR "correspondence" "missing retained backing")
              | GraphTerm (left_frame,value) =>
                  (case (G.view graph value,right) of
                      (G.Variable _,G.Variable _) =>
                        if value=node then Corresponding
                        else DifferentGraphSyntax
                    | (G.Constant _,G.Constant _) =>
                        if same_constant (G.representative graph value)
                            (G.representative graph node) then Corresponding
                        else DifferentGraphSyntax
                    | (G.Application (left,right),G.Application pair) =>
                        application (GraphTerm (left_frame,left),
                          GraphTerm (left_frame,right)) pair
                    | (G.AdmittedBinder _,G.AdmittedBinder _) =>
                        let val data = G.binder_closure_data graph left_frame
                              (G.binder_closure graph left_frame value)
                        in binder
                          (GraphTerm (#binder_frame data,#binder data))
                          (GraphTerm (#body_frame data,#body data))
                          (#body_frame data) end
                    | (G.OpaqueRetained,_) =>
                        NeedsGraphOpening (left_frame,value)
                    | _ => DifferentGraphSyntax))
        end
      val answer = compare (ParserTerm original) caller target []
      val _ = guard context original
      val _ = G.validate_scope graph caller
      val _ = ignore (G.closure_root graph caller target)
    in answer end)
  datatype proof_term = ProofValue of context * value
    | ProofGraph of context * value * G.scope * G.closure_child
  datatype proof_view = ProofVariable of G.variable_kind * Term.term
    | ProofConstant of Term.term | ProofApplication of proof_term * proof_term
    | ProofAbstraction of
        {binder:proof_term,body:proof_term,body_frame:G.scope}
    | ProofOpaque
  fun proof_term context current = protected context (fn () =>
    let val held=row context current in
      case (#graph_node held,#closure held) of
          (SOME _,SOME child)=>ProofGraph (context,current,#scope held,child)
        | (NONE,NONE)=>ProofValue (context,current)
        | _=>raise ERR "proof_view" "invalid retained backing"
    end)
  fun proof_guard context term = protected context (fn () =>
    let val actual=case term of ProofValue (held,_)=>held
          | ProofGraph (held,_,_,_)=>held
        val _=if Portable.pointer_eq (context,actual) then () else
          raise ERR "proof_view" "different parser value context"
        val _=validate context
        val _=tick context 1
        val Context {graph,...}=context
    in case term of ProofValue (_,current)=>guard context current
      | ProofGraph (_,anchor,caller,child)=>
          (guard context anchor;
           ignore (G.closure_child_node graph caller child)) end)
  fun proof_key context term = protected context (fn () =>
    let val _=proof_guard context term val Context {graph,...}=context
    in case term of ProofValue (_,current)=>(0,key context current)
      | ProofGraph (_,_,caller,child)=>
          (1,G.node_id (G.closure_child_node graph caller child)) end)
  fun proof_graph_reference context term = protected context (fn () =>
    let val _ = proof_guard context term
        val _ = tick context 2
        val Context {graph,...} = context
    in case term of ProofValue _ => NONE
      | ProofGraph (_,_,caller,child) =>
          let val _ = tick context 4
              val node = G.closure_child_node graph caller child
              val _ = proof_guard context term
          in SOME {graph=graph,scope=caller,child=child,node=node} end
    end)
  fun proof_type_of context term = protected context (fn () =>
    let val _=proof_guard context term val Context {graph,...}=context
    in case term of ProofValue (_,current)=>type_of context current
      | ProofGraph (_,_,caller,child)=>
          G.type_of graph (G.closure_child_node graph caller child) end)
  fun proof_view context term = protected context (fn () =>
    let val _=proof_guard context term val _=tick context 1
        val Context {graph,...}=context
    in case term of ProofValue (_,current)=>
        (case view context current of
            Variable pair=>ProofVariable pair
          | Constant atom=>ProofConstant atom
          | Application (left,right)=>ProofApplication
              (proof_term context left,proof_term context right)
          | Abstraction {binder,body,body_frame}=>ProofAbstraction
              {binder=proof_term context binder,body=proof_term context body,
               body_frame=body_frame}
          | RetainedGraph=>
              raise ERR "proof_view" "unresolved retained backing")
      | ProofGraph (_,anchor,caller,child)=>
          let val node=G.closure_child_node graph caller child
              fun retained child=ProofGraph (context,anchor,caller,child)
          in case G.view graph node of
              G.Variable pair=>ProofVariable pair
            | G.Constant _=>ProofConstant (G.representative graph node)
            | G.Application _=>
                let val (left,right)=G.closure_application_children graph
                      caller child
                in ProofApplication (retained left,retained right) end
            | G.AdmittedBinder _=>
                let val closure=G.closure_child_binder graph caller child
                    val data=G.binder_closure_data graph caller closure
                    val binder=G.closure_root graph (#binder_frame data)
                      (#binder data)
                    val body=G.binder_closure_body graph caller closure
                in ProofAbstraction
                  {binder=ProofGraph (context,anchor,#binder_frame data,
                     binder),body=retained body,body_frame= #body_frame data}
                end
            | G.OpaqueRetained=>ProofOpaque
          end
    end)
end
