structure SmtLib_GraphQueryAnalysis :> SmtLib_GraphQueryAnalysis =
struct
  structure G = SmtReplayGraph
  structure W = SmtReplayInvocationWork
  structure GP = SmtLib_GraphPreprocess
  structure A = SmtLib_CollectionApplicationAnalysis
  structure M = SmtLib_CollectionMarkers
  structure L = SmtLib_CarrierLetBindings
  structure R = SmtLib_RawNumAnalysis
  val ERR = Feedback.mk_HOL_ERR "SmtLib_GraphQueryAnalysis"
  type scoped_node = {scope:G.scope,node:G.node}
  type marker_seeds =
    {graph:G.graph,scope:G.scope,sets:scoped_node list,
     bags:scoped_node list,raw_numbers:scoped_node list}
  type options =
    {collections:G.node list,declared_const_arity:G.node -> int,
     open_opaque:G.scope -> G.node -> unit}
  type result =
    {roots:scoped_node list,inventory:scoped_node list,
     openings:{scope:G.scope,original:G.node,opened:G.node} list,
     computed_applications:(scoped_node * int * scoped_node) list,
     mixed_argument:bool,bound_application:bool,visits:int,bound_visits:int}
  type native_syntax =
    {set_role:{head:G.node,atomic:bool} -> M.role,
     bag_role:{head:G.node,atomic:bool} -> M.role,
     is_set_type:Type.hol_type -> bool,is_bag_type:Type.hol_type -> bool,
     is_cond:G.node -> bool,is_let:G.node -> bool,is_uncurry:G.node -> bool,
     pair_constant:Type.hol_type * Type.hol_type -> Term.term,
     is_integer_coercion:G.node -> bool,is_num_head:G.node -> bool,
     is_bag_card_head:G.node -> bool,number_type:Type.hol_type}
  type native_options =
    {syntax:native_syntax,declared_const_arity:G.node -> int,
     open_opaque:G.scope -> G.node -> unit}
  type native_result =
    {sets:scoped_node list,bags:scoped_node list,
     set_analysis:result,bag_analysis:result,
     set_marker_visits:int,bag_marker_visits:int,
     raw_numbers:scoped_node list,raw_number_visits:int}
  datatype selection = Explicit of G.node list | Native of native_syntax
    | SeededNative of native_syntax * marker_seeds
  exception NotSyntax
  fun syntax_error NotSyntax = true | syntax_error _ = false
  datatype term = Term of
    {scope:G.scope,node:G.node,caller:G.scope,child:G.closure_child}
    | Pattern of {id:int,ty:Type.hol_type,function:term,argument:term}
    | LetPattern of {id:int,value:term}
    | RecipeApp of {owner:unit ref,id:int,ty:Type.hol_type,
                    function:term,argument:term}
    | RecipeAbs of {owner:unit ref,id:int,ty:Type.hol_type,
                    binder:term,body:term}
  datatype kind = Variable | Constant | Application | Abstraction
  type carrier = term
  datatype carrier_view =
      VariableView of G.variable_kind * Term.term
    | ConstantView of Term.term
    | ApplicationView of carrier * carrier
    | AbstractionView of carrier * carrier
  type native_context =
    {analysis:native_result,goal:carrier,assumptions:carrier list,
     denied:carrier,view:carrier -> carrier_view,
     type_of:carrier -> Type.hol_type,same:carrier * carrier -> bool,
     free_variables:carrier -> carrier list,
     strip_comb:carrier -> carrier * carrier list,
     is_set:carrier -> bool,is_bag:carrier -> bool,
     is_raw_number:carrier -> bool,
     contextual_argument:carrier * int -> carrier option,
     describe:carrier -> scoped_node,key:carrier -> int * int,
     constant:Term.term -> carrier,mk_comb:carrier * carrier -> carrier,
     step:unit -> unit}
  type outbound_context =
    {analysis:native_result,goal:carrier,assumptions:carrier list,
     denied:carrier,view:carrier -> carrier_view,
     type_of:carrier -> Type.hol_type,same:carrier * carrier -> bool,
     free_variables:carrier -> carrier list,
     strip_comb:carrier -> carrier * carrier list,
     is_set:carrier -> bool,is_bag:carrier -> bool,
     is_raw_number:carrier -> bool,
     contextual_argument:carrier * int -> carrier option,
     graph_node:carrier -> scoped_node option,key:carrier -> int * int,
     semantic_key:carrier -> int,
     collection_terms:unit ->
       {sets:carrier list,bags:carrier list,raw_numbers:carrier list,
        shadow_same:carrier * carrier -> bool},
     constant:Term.term -> carrier,mk_comb:carrier * carrier -> carrier,
     genvar:Type.hol_type -> carrier,
     list_mk_abs:carrier list * carrier -> carrier,step:unit -> unit}
  fun node (Term {node,...}) = node
    | node _ = raise ERR "node" "analysis pattern has no graph ID"
  fun scope (Term {scope,...}) = scope
    | scope _ = raise ERR "scope" "analysis pattern has no frame"
  fun key (LetPattern {id,...}) = (~2,id)
    | key (Pattern {id,...}) = (~1,id)
    | key (RecipeApp {id,...}) = (~3,id)
    | key (RecipeAbs {id,...}) = (~4,id)
    | key term = (G.scope_id (scope term),G.node_id (node term))
  fun describe term : scoped_node = {scope=scope term,node=node term}
  fun compare_key ((ls,ln),(rs,rn)) =
    case Int.compare (ls,rs) of EQUAL => Int.compare (ln,rn)
      | order => order
  fun compare_bound ((left,lb),(right,rb)) =
    case compare_key (left,right) of
      EQUAL => List.collate compare_key (lb,rb)
    | order => order

  fun native_result_of
      ([(sets,set_count),(bags,bag_count)],[set_analysis,bag_analysis],
       numbers,number_count) : native_result =
        {sets=sets,bags=bags,set_analysis=set_analysis,
         bag_analysis=bag_analysis,set_marker_visits=set_count,
         bag_marker_visits=bag_count,raw_numbers=numbers,
         raw_number_visits=number_count}
    | native_result_of _ =
        raise ERR "analyse" "internal native analysis count"

  fun analyse_with_policy expected query declared_const_arity open_opaque
      selection consume =
    ((let
        val data = GP.query_nodes_with_policy_for expected query
        val graph = #graph data val root = #scope data
        val _ = case selection of SeededNative (_,seeds) =>
            if Portable.pointer_eq (#graph seeds,graph) andalso
                #scope seeds=root then () else
              raise ERR "seeds" "different query graph or root"
          | _ => ()
      in W.with_step expected (fn () =>
        let
          fun full_valid () = GP.validate_query_with_policy expected query
          (* The fixed traversal and each private carrier operation are
             callback-free between their external boundaries. Validate the
             complete retained query at those boundaries, not recursively
             for every borrowed syntax field. Scope/closure checks and all
             original Work debits still run at every observation. *)
          val pure = ref true
          fun valid () = if !pure then W.spend_policy expected 0
            else full_valid ()
          fun external operation argument =
            let val _=full_valid ()
                val answer=operation argument
                val _=full_valid ()
            in answer end
          val declared_const_arity=external declared_const_arity
          fun call_open caller node = external
            (fn (caller,node)=>open_opaque caller node) (caller,node)
          fun spend n = W.spend_policy expected n
          val positions = ref (Redblackmap.mkDict compare_key)
          val opened = ref (Redblackmap.mkDict compare_key)
          val openings = ref
            ([] : (G.scope * G.node * G.source) list)
          val visited = ref (Redblackset.empty compare_key)
          val inventory = ref ([]:term list)
          val visits = ref 0
          val recipe_owner = ref ()
          val next_recipe = ref 0
          val recipe_guards = ref (Redblackmap.mkDict compare_key)
          fun recipe_id () =
            let val _ = spend 8 val id = !next_recipe
            in next_recipe := id+1;id end
          fun guard (LetPattern {value,...}) = guard value
            | guard (Pattern {function,argument,...}) =
            (guard function;guard argument)
            | guard (term as RecipeApp {owner,function,argument,...}) =
                guard_recipe owner term (fn () =>
                  (guard function;guard argument))
            | guard (term as RecipeAbs {owner,binder,body,...}) =
                guard_recipe owner term (fn () => (guard binder;guard body))
            | guard (Term {scope,node,caller,child}) =
            (valid ();
             if G.closure_child_node graph caller child = node andalso
                 G.closure_child_scope graph caller child = scope then ()
             else raise ERR "scope" "recorded closure position changed")
          and guard_recipe owner term inspect =
            let
              val _ = if Portable.pointer_eq (owner,recipe_owner) then ()
                else raise ERR "borrow" "foreign outbound recipe"
              val _ = valid ()
              val stamp = (G.validation_revision graph root,
                           G.scope_retirement_epoch graph root)
              fun check () =
                (inspect ();valid ();spend 4;
                 recipe_guards := Redblackmap.insert
                   (!recipe_guards,key term,stamp))
            in case Redblackmap.peek (!recipe_guards,key term) of
                SOME old => if old = stamp then () else check ()
              | NONE => check ()
            end
          fun make caller child =
            let
              val node = G.closure_child_node graph caller child
              val scope = G.closure_child_scope graph caller child
              val index = (G.scope_id scope,G.node_id node)
            in case Redblackmap.peek (!positions,index) of
                SOME term => (guard term;term)
              | NONE =>
                  let val _ = spend 8
                      val term = Term
                        {node=node,scope=scope,caller=caller,child=child}
                      val _ = positions := Redblackmap.insert
                        (!positions,index,term)
                  in guard term;term end
            end
          fun at caller node = make caller (G.closure_root graph caller node)
          fun resolve (term as LetPattern _) = (guard term;term)
            | resolve (term as Pattern _) = (guard term;term)
            | resolve (term as RecipeApp _) = (guard term;term)
            | resolve (term as RecipeAbs _) = (guard term;term)
            | resolve term =
            let val _ = guard term in
              case Redblackmap.peek (!opened,key term) of
                SOME (target,source) =>
                  (G.validate_opened_view graph
                     (scope term) (node term) source;
                   guard target;target)
              | NONE => case G.view graph (node term) of
                  G.OpaqueRetained =>
                    let
                      val _ = spend 16
                      val _ = call_open (scope term) (node term)
                      val _ = valid ()
                      val source = G.cached_opened_view graph
                        (scope term) (node term)
                      val _ = G.validate_opened_view graph
                        (scope term) (node term) source
                      val target = at (scope term) (#node source)
                      val _ = if node target <> node term then () else
                        raise ERR "open_opaque"
                          "authenticated opening left syntax opaque"
                      val result = resolve target
                      val _ = opened := Redblackmap.insert
                        (!opened,key term,(result,source))
                      val _ = openings :=
                        (scope term,node term,source) :: !openings
                    in result end
                | _ => term
            end
          val applications = ref (Redblackmap.mkDict compare_key)
          val abstractions = ref (Redblackmap.mkDict compare_key)
          fun application (LetPattern {value,...}) = application value
            | application (Pattern {function,argument,...}) =
            (guard function;guard argument;(function,argument))
            | application (term as RecipeApp {function,argument,...}) =
                (guard term;(function,argument))
            | application (term as RecipeAbs _) =
                (guard term;raise NotSyntax)
            | application current =
            let val term as Term {caller,child,...} = resolve current in
              case Redblackmap.peek (!applications,key term) of
                SOME (left,right) => (guard left;guard right;(left,right))
              | NONE =>
                  (case G.view graph (node term) of
                     G.Application _ =>
                       let
                         val (left,right) =
                           G.closure_application_children graph caller child
                         val pair = (make caller left,make caller right)
                         val _ = spend 4
                         val _ = applications := Redblackmap.insert
                           (!applications,key term,pair)
                       in pair end
                   | _ => raise ERR "dest_comb" "not an application")
            end
          fun abstraction (LetPattern {value,...}) = abstraction value
            | abstraction (Pattern _) = raise NotSyntax
            | abstraction (term as RecipeAbs {binder,body,...}) =
                (guard term;(binder,body))
            | abstraction (term as RecipeApp _) =
                (guard term;raise NotSyntax)
            | abstraction current =
            let val term as Term {caller,child,...} = resolve current in
              case Redblackmap.peek (!abstractions,key term) of
                SOME (binder,body) =>
                  (guard binder;guard body;(binder,body))
              | NONE =>
                  (case G.view graph (node term) of
                     G.AdmittedBinder _ =>
                       let
                         val closure = G.closure_child_binder
                           graph caller child
                         val saved = G.binder_closure_data
                           graph caller closure
                         val binder = at (#binder_frame saved) (#binder saved)
                         val body = make caller
                           (G.binder_closure_body graph caller closure)
                         val _ = spend 4
                         val _ = abstractions := Redblackmap.insert
                           (!abstractions,key term,(binder,body))
                       in (binder,body) end
                   | _ => raise ERR "dest_abs" "not an admitted binder")
            end
          fun view current = case resolve current of
              LetPattern {value,...} => view value
            | Pattern _ => Application
            | RecipeApp _ => Application
            | RecipeAbs _ => Abstraction
            | term => case G.view graph (node term) of
                G.Variable _ => Variable | G.Constant _ => Constant
              | G.Application _ => Application
              | G.AdmittedBinder _ => Abstraction
              | G.OpaqueRetained => raise ERR "view" "unopened opaque syntax"
          fun type_of current = case resolve current of
              LetPattern {value,...} => type_of value
            | Pattern {ty,...} => ty
            | RecipeApp {ty,...} => ty
            | RecipeAbs {ty,...} => ty
            | term => G.type_of graph (node term)
          fun visit current =
            let val term = resolve current val index = key term in
              if Redblackset.member (!visited,index) then guard term
              else
                let val _ = spend 8
                    val _ = visited := Redblackset.add (!visited,index)
                    val _ = inventory := term :: !inventory
                    val _ = visits := !visits + 1
                in case view term of
                    Application =>
                      let val (left,right) = application term
                      in visit left;visit right end
                  | Abstraction =>
                      let val (binder,body) = abstraction term
                      in visit binder;visit body end
                  | Variable => ()
                  | Constant => ()
                end
            end
          val roots = List.map (at root) (#goal data :: #assumptions data)
          val _ = List.app visit roots
          (* Inventory is complete before Lib.total in the generic helper
             can classify a nonapplication. Opening errors escape here. *)
          val ordered = List.rev (!inventory)
          val spines = ref (Redblackmap.mkDict compare_key)
          fun strip_comb current =
            let val term = resolve current in
              case Redblackmap.peek (!spines,key term) of
                SOME (function,arguments) =>
                  (guard function;List.app guard arguments;
                   (function,arguments))
              | NONE =>
                  let
                    fun walk current arguments =
                      case view current of
                        Application =>
                          let val (function,argument) = application current
                          in walk function (argument :: arguments) end
                      | _ => (resolve current,arguments)
                    val pair = walk term []
                    val _ = spend 4
                    val _ = spines := Redblackmap.insert
                      (!spines,key term,pair)
                  in pair end
            end
          val free = ref (Redblackmap.mkDict compare_key)
          fun free_variables current =
            let val term = resolve current in
              case Redblackmap.peek (!free,key term) of
                SOME variables => (List.app guard variables;variables)
              | NONE =>
                  let
                    fun merge variables = List.map #2
                      (Redblackmap.listItems (List.foldl
                        (fn (variable,table) => Redblackmap.insert
                          (table,G.node_id (node variable),variable))
                        (Redblackmap.mkDict Int.compare) variables))
                    val metadata = case term of LetPattern _ => NONE
                      | Pattern _ => NONE
                      | RecipeApp _ => NONE
                      | RecipeAbs _ => NONE
                      | _ => G.free_variable_nodes graph (node term)
                    val variables = case metadata of
                        SOME variables => List.map
                          (fn variable => at (G.node_scope graph variable)
                            variable) variables
                      | NONE =>
                          (case view term of
                             Variable => [term]
                           | Constant => []
                           | Application =>
                               let val (left,right) = application term
                               in merge (free_variables left @
                                 free_variables right) end
                           | Abstraction =>
                               let val (binder,body) = abstraction term
                               in List.filter (fn variable =>
                                 node variable <> node binder)
                                 (free_variables body) end)
                    val _ = spend 4
                    val _ = free := Redblackmap.insert
                      (!free,key term,variables)
                  in variables end
            end
          fun arity term =
            let val actual = resolve term in case view actual of
                Constant =>
                  let val _ = valid ()
                      val rank = declared_const_arity (node actual)
                      val _ = valid ()
                  in rank end
              | _ => raise ERR "arity" "constant leaf required" end
          (* These are semantic analysis keys, never an equality proof.
             Scope salts application IDs, so inherited compound syntax
             needs structural keys. Only variables local to an actual
             admitted abstraction use de Bruijn indices; external Bound,
             rigid, generated and solver variables keep their exact IDs. *)
          val semantic_types = ref (Redblackmap.mkDict Type.compare)
          val next_type = ref 0
          fun type_id term =
            let val ty = type_of term in
              case Redblackmap.peek (!semantic_types,ty) of
                SOME id => id
              | NONE => let val _ = spend 4 val id = !next_type
                            val _ = next_type := id + 1
                            val _ = semantic_types := Redblackmap.insert
                              (!semantic_types,ty,id)
                        in id end
            end
          val semantic_nodes = ref
            (Redblackmap.mkDict (List.collate Int.compare))
          val semantic_memo = ref (Redblackmap.mkDict compare_bound)
          val next_semantic = ref 0
          fun semantic_id variables current =
            let
              val actual = resolve current
              val _ = List.app guard variables
              val index = (key actual,List.map key variables)
            in case Redblackmap.peek (!semantic_memo,index) of
                SOME id => id
              | NONE =>
                  let
                    val ty = type_id actual
                    fun bound_index [] _ = NONE
                      | bound_index (variable :: rest) depth =
                          if node variable = node actual then SOME depth
                          else bound_index rest (depth + 1)
                    val shape = case view actual of
                        Variable =>
                          (case bound_index variables 0 of
                             SOME depth => [0,ty,depth]
                           | NONE => [1,ty,G.node_id (node actual)])
                      | Constant => [2,ty,G.node_id (node actual)]
                      | Application =>
                          let val (function,argument) = application actual
                          in [3,ty,semantic_id variables function,
                            semantic_id variables argument] end
                      | Abstraction =>
                          let val (binder,body) = abstraction actual
                          in [4,type_id binder,
                            semantic_id (binder :: variables) body] end

                    val id = case Redblackmap.peek (!semantic_nodes,shape) of
                        SOME id => id
                      | NONE =>
                          let val _ = spend 4
                              val id = !next_semantic
                              val _ = next_semantic := id + 1
                              val _ = semantic_nodes := Redblackmap.insert
                                (!semantic_nodes,shape,id)
                          in id end
                    val _ = guard actual
                    val _ = List.app guard variables
                    val _ = spend 4
                    val _ = semantic_memo := Redblackmap.insert
                      (!semantic_memo,index,id)
                  in id end
            end
          val operations : term A.operations =
            {same=fn (left,right) =>
               semantic_id [] left = semantic_id [] right,
             type_of=type_of,
             is_variable=fn term =>
               (case view term of Variable => true | _ => false),
             is_constant=fn term =>
               (case view term of Constant => true | _ => false),
             declared_const_arity=arity,strip_comb=strip_comb,
             dest_comb=application,
             is_abstraction=fn term =>
               (case view term of Abstraction => true | _ => false),
             dest_abs=abstraction,free_variables=free_variables}
          val next_pattern = ref 0
          fun synthetic function argument ty =
            let val _ = spend 8 val id = !next_pattern
                val _ = next_pattern := id + 1
            in Pattern {id=id,ty=ty,function=function,argument=argument} end
          (* Stock function-let fixup can join parameters from sibling
             binder frames. Its pattern is analysis DATA, not visible graph
             syntax. Prefer authentic graph applications when co-visible. *)
          fun mk_application (function,argument) =
            let val function = resolve function
                val argument = resolve argument
                val (domain,range) = Type.dom_rng (type_of function)
                val _ = if Type.compare (domain,type_of argument) = EQUAL
                  then () else raise ERR "let_pattern" "argument type mismatch"
                fun genuine left right =
                  let val left_scope = scope left
                      val right_scope = scope right
                      val caller =
                        if G.scope_visible graph left_scope right_scope
                        then SOME left_scope
                        else if G.scope_visible graph right_scope left_scope
                        then SOME right_scope else NONE
                  in case caller of
                      NONE => synthetic function argument range
                    | SOME caller =>
                        (spend 8;at caller (G.application graph caller
                          (node function,node argument)))
                  end
            in case (function,argument) of
                (Term _,Term _) => genuine function argument
              | _ => synthetic function argument range
            end
          fun let_pattern value =
            let val _ = spend 4 val id = !next_pattern
                val _ = next_pattern := id + 1
            in LetPattern {id=id,value=value} end
          (* The stock LET heuristic and finite-evidence shadow guard use
             lexical equality, not scoped semantic identity. Keep that
             compatibility relation separate from same/semantic_id and
             grant it no declaration, Source or proof authority. Variable
             leaves retain the spelling actually held by the graph; known
             admitted binders retain their original atomic binder_term. *)
          val lexical_matches = ref
            (Redblackmap.mkDict (List.collate Int.compare))
          fun lexical_compare left_bound right_bound left right =
            let
              val left = resolve left val right = resolve right
              val _ = List.app guard (left_bound @ right_bound)
              fun keys terms = List.concat
                (List.map (fn term => let val (scope,node) = key term
                  in [scope,node] end) terms)
              val index = keys [left,right] @
                (length left_bound :: keys left_bound @ keys right_bound)
              fun bound_index current [] _ = NONE
                | bound_index current (binder::rest) index =
                    if node current = node binder then SOME index
                    else bound_index current rest (index+1)
            in case Redblackmap.peek (!lexical_matches,index) of
                SOME result => result
              | NONE =>
                  let
                    val _ = spend 4
                    val result = Type.compare
                        (type_of left,type_of right) = EQUAL andalso
                      (case (view left,view right) of
                         (Variable,Variable) =>
                           (case (bound_index left left_bound 0,
                                  bound_index right right_bound 0) of
                              (SOME l,SOME r) => l=r
                            | (NONE,NONE) =>
                                (case (G.view graph (node left),
                                       G.view graph (node right)) of
                                   (G.Variable (_,l),G.Variable (_,r)) =>
                                     Term.aconv l r | _ => false)
                            | _ => false)
                       | (Constant,Constant) => node left = node right
                       | (Application,Application) =>
                           let val (lf,la) = application left
                               val (rf,ra) = application right
                           in lexical_compare left_bound right_bound lf rf
                             andalso lexical_compare left_bound right_bound
                               la ra end
                       | (Abstraction,Abstraction) =>
                           let val (lb,lbody) = abstraction left
                               val (rb,rbody) = abstraction right
                           in lexical_compare (lb::left_bound)
                             (rb::right_bound) lbody rbody end
                       | _ => false)
                    val _ = guard left val _ = guard right
                    val _ = List.app guard (left_bound @ right_bound)
                    val _ = lexical_matches := Redblackmap.insert
                      (!lexical_matches,index,result)
                  in result end
            end
          fun lexical_same (left,right) = lexical_compare [] [] left right
          fun collect_native (raw:native_syntax) seeds =
            let
              val syntax:native_syntax =
                {set_role=external (#set_role raw),
                 bag_role=external (#bag_role raw),
                 is_set_type=external (#is_set_type raw),
                 is_bag_type=external (#is_bag_type raw),
                 is_cond=external (#is_cond raw),
                 is_let=external (#is_let raw),
                 is_uncurry=external (#is_uncurry raw),
                 pair_constant=external (#pair_constant raw),
                 is_integer_coercion=external (#is_integer_coercion raw),
                 is_num_head=external (#is_num_head raw),
                 is_bag_card_head=external (#is_bag_card_head raw),
                 number_type= #number_type raw}
              fun seed ({scope=caller,node}:scoped_node) =
                (G.validate_scope graph caller;
                 if G.scope_visible graph caller root then
                   resolve (at caller node) else
                   raise ERR "seeds" "marker is outside the original root")
              val (seed_sets,seed_bags,seed_numbers) = case seeds of
                  NONE => ([],[],[])
                | SOME (saved:marker_seeds) =>
                    (List.map seed (#sets saved),List.map seed (#bags saved),
                     List.map seed (#raw_numbers saved))
              fun constant_test test term = case view term of
                  Constant =>
                    let val _ = valid () val result = test (node term)
                        val _ = valid () in result end
                | _ => false
              fun dest_abs term = case view term of
                  Abstraction => abstraction term | _ => raise NotSyntax
              fun dest_comb term = case view term of
                  Application => application term | _ => raise NotSyntax
              fun dest_operator test count term =
                let val (head,arguments) = strip_comb term
                in if List.length arguments = count andalso
                    constant_test test head then arguments
                  else raise NotSyntax end
              fun dest_let term = case dest_operator (#is_let syntax) 2 term of
                  [function,value] => (function,value)
                | _ => raise NotSyntax
              fun dest_uncurry term =
                case dest_operator (#is_uncurry syntax) 1 term of
                  [function] => function | _ => raise NotSyntax
              fun mk_pair (left,right) =
                let val raw = (#pair_constant syntax)
                      (type_of left,type_of right)
                    val _ = spend 8
                    val constant = at root (G.constant graph root raw)
                in mk_application (mk_application (constant,left),right) end
              val pabs : term L.pabs_operations =
                {dest_abs=dest_abs,dest_uncurry=dest_uncurry,
                 mk_pair=mk_pair,is_syntax_error=syntax_error}
              val let_ops : term L.operations =
                {dest_abs=dest_abs,dest_let=dest_let,
                 dest_plet=fn term =>
                   let val (function,value) = dest_let term
                       val (pattern,body) = L.dest_pabs pabs function
                   in (pattern,value,body) end,
                 strip_pabs=L.strip_pabs pabs,
                 list_mk_comb=fn (head,args) => case args of
                   [] => head
                 | _ => let_pattern (List.foldl
                     (fn (arg,f) => mk_application (f,arg)) head args),
                 is_let=fn term =>
                   ((ignore (dest_let term);true)
                    handle NotSyntax => false),
                 is_syntax_error=syntax_error,not_a_let=fn () => NotSyntax}
              val let_bindings = ref (Redblackmap.mkDict compare_key)
              fun bindings term =
                let val term = resolve term in
                  case Redblackmap.peek (!let_bindings,key term) of
                    SOME result =>
                      (List.app (fn (left,right) =>
                        (guard left;guard right)) result;result)
                  | NONE =>
                      let val result = #1 (L.dest_anylet let_ops term)
                          val _ = spend 4
                          val _ = let_bindings := Redblackmap.insert
                            (!let_bindings,key term,result)
                      in result end
                end
              fun condition term =
                ((case dest_operator (#is_cond syntax) 3 term of
                    [test,left,right] => SOME (test,left,right)
                  | _ => NONE) handle NotSyntax => NONE)
              (* Stock function-let fixup compares its artificial LHS
                 against markers by lexical variable spelling. Preserve
                 that heuristic only for this private tagged pattern.
                 Marker deduplication and argument analysis still compare
                 authentic scoped variable IDs, never these leaf names. *)
              fun member (LetPattern {value,...}) terms =
                    List.exists (fn term => lexical_same (value,term)) terms
                | member term terms = List.exists
                    (fn saved => (#same operations) (term,saved)) terms
              fun collect role is_collection policy initial =
                let
                  fun add term terms =
                    if is_collection (type_of term) andalso
                        not (member term terms)
                    then (spend 4;term :: terms) else terms
                  fun classify (term,head) = case view head of
                      Constant =>
                        let val _ = valid ()
                            val result = role
                              {head=node head,atomic=case view term of
                                Constant => true | _ => false}
                            val _ = valid () in result end
                    | _ => M.Other
                  val marker_ops : term M.operations =
                    {strip_comb=strip_comb,dest_abs=dest_abs,
                     dest_comb=dest_comb,condition=condition,
                     bindings=bindings,add=add,member=member,
                     is_collection_type=is_collection o type_of,
                     classify=classify}
                  fun compare_state ((left,ls),(right,rs)) =
                    case compare_key (left,right) of
                      EQUAL => Int.compare (ls,rs) | order => order
                  val states = ref ([]:(term list * int) list)
                  val next_state = ref 0
                  fun state_id terms =
                    case List.find (fn (saved,_) =>
                        Portable.pointer_eq (terms,saved)) (!states) of
                      SOME (_,id) => id
                    | NONE =>
                        let val _ = spend 4 val id = !next_state
                            val _ = next_state := id + 1
                            val _ = states := (terms,id) :: !states
                        in id end
                  val walk_cache = ref (Redblackmap.mkDict compare_state)
                  val mark_cache = ref (Redblackmap.mkDict compare_state)
                  val walks = ref 0
                  fun memo cache walking current incoming compute =
                    let val term = resolve current
                        val _ = List.app guard incoming
                        val index = (key term,state_id incoming)
                    in case Redblackmap.peek (!cache,index) of
                        SOME result => (List.app guard result;result)
                      | NONE =>
                          let val _ = spend 4
                              val _ = if walking then walks := !walks + 1
                                else ()
                              val result = compute ()
                              val _ = guard term
                              val _ = List.app guard result
                              val _ = cache := Redblackmap.insert
                                (!cache,index,result)
                          in result end
                    end
                  val hooks : term M.memo_hooks =
                    {walk=memo walk_cache true,mark=memo mark_cache false}
                  val walk = M.collect_with_memo_and_syntax_errors
                    marker_ops syntax_error hooks policy
                  val terms = List.foldl (fn (term,terms) => walk term terms)
                    initial roots
                in (terms,!walks) end
              val sets = collect (#set_role syntax) (#is_set_type syntax)
                {propagate_bindings=true,visit_prefix=false} seed_sets
              val bags = collect (#bag_role syntax) (#is_bag_type syntax)
                {propagate_bindings=false,visit_prefix=true} seed_bags
              val number_ops : term R.operations =
                {same= #same operations,type_of=type_of,
                 is_abstraction=fn term => case view term of
                   Abstraction => true | _ => false,
                 dest_abs=abstraction,
                 is_combination=fn term => case view term of
                   Application => true | _ => false,
                 dest_comb=application,strip_comb=strip_comb,
                 is_integer_coercion=constant_test
                   (#is_integer_coercion syntax),
                 is_num_head=constant_test (#is_num_head syntax),
                 is_bag_card_head=constant_test (#is_bag_card_head syntax),
                 number_type= #number_type syntax}
              fun compare_expected (NONE,NONE) = EQUAL
                | compare_expected (NONE,SOME _) = LESS
                | compare_expected (SOME _,NONE) = GREATER
                | compare_expected (SOME left,SOME right) =
                    Type.compare (left,right)
              fun compare_number ((le,ln,ls),(re,rn,rs)) =
                case compare_expected (le,re) of
                  EQUAL => (case compare_key (ln,rn) of
                    EQUAL => Int.compare (ls,rs) | order => order)
                | order => order
              val number_states = ref ([]:(term list * int) list)
              val next_number_state = ref 0
              fun number_state terms =
                case List.find (fn (saved,_) =>
                    Portable.pointer_eq (terms,saved)) (!number_states) of
                  SOME (_,id) => id
                | NONE =>
                    let val _ = spend 4 val id = !next_number_state
                        val _ = next_number_state := id + 1
                        val _ = number_states := (terms,id) :: !number_states
                    in id end
              val number_cache = ref (Redblackmap.mkDict compare_number)
              val number_visits = ref 0
              fun number_memo expected current incoming compute =
                let val term = resolve current
                    val _ = List.app guard incoming
                    val index = (expected,key term,number_state incoming)
                in case Redblackmap.peek (!number_cache,index) of
                    SOME result => (List.app guard result;result)
                  | NONE =>
                      let val _ = spend 4
                          val _ = number_visits := !number_visits + 1
                          val result = compute ()
                          val _ = guard term
                          val _ = List.app guard result
                          val _ = number_cache := Redblackmap.insert
                            (!number_cache,index,result)
                      in result end
                end
              (* Keep the helper's separate empty accumulator per root and
                 final outer merge; one expected-type visit is not another. *)
              val numbers = R.collect_with_memo
                number_ops number_memo (#1 bags) roots
              val numbers = case seeds of NONE => numbers | SOME _ =>
                List.foldr (fn (current,terms) =>
                  if List.exists (fn saved =>
                      (#same operations) (current,saved)) terms
                  then terms else current::terms) seed_numbers numbers
            in ([sets,bags],numbers,!number_visits) end
          fun argument_analysis collection_terms =
            let
              val bound_visits = ref 0
              val computed = A.computed_applications
                operations collection_terms ordered
              val mixed = A.has_mixed_argument
                operations collection_terms ordered
              val bound = ref (Redblackmap.mkDict compare_bound)
              fun memoize variables term compute =
                let
                  val actual = resolve term
                  val _ = List.app guard variables
                  val index =
                    (key actual,List.map (key o resolve) variables)
                in case Redblackmap.peek (!bound,index) of
                    SOME result => result
                  | NONE =>
                      let val _ = spend 4
                          val _ = bound_visits := !bound_visits + 1
                          val result = compute ()
                          val _ = guard actual
                          val _ = List.app guard variables
                          val _ = bound := Redblackmap.insert
                            (!bound,index,result)
                      in result end
                end
              val bound_application = A.has_bound_application_with_memo
                operations memoize collection_terms roots
            in (computed,mixed,bound_application,!bound_visits) end
          val (groups,numbers,number_visits) = case selection of
              Explicit collections => ([(List.map (fn current =>
                let val _ = ignore (G.type_of graph current)
                in resolve (at (G.node_scope graph current) current) end)
                collections,0)],[],0)
            | Native syntax => collect_native syntax NONE
            | SeededNative (syntax,seeds) =>
                collect_native syntax (SOME seeds)
          val analyses = List.map (argument_analysis o #1) groups
          val _ = Redblackmap.foldl
            (fn (_,term,()) => guard term) () (!positions)
          val _ = List.app (fn (scope,original,source) =>
            G.validate_opened_view graph scope original source) (!openings)
          val _ = pure := false
          val _ = full_valid ()
          fun result (computed,mixed,bound_application,bound_visits) =
            {roots=List.map describe roots,inventory=List.map describe ordered,
             openings=List.map (fn (scope,original,source) =>
               {scope=scope,original=original,opened= #node source})
               (List.rev (!openings)),
             computed_applications=List.map (fn (variable,index,argument) =>
               (describe variable,index,describe argument)) computed,
             mixed_argument=mixed,bound_application=bound_application,
             visits= !visits,bound_visits=bound_visits}
          val output = (List.map (fn (terms,count) =>
              (List.map describe terms,count)) groups,
            List.map result analyses,List.map describe numbers,number_visits)
          fun borrow action =
            let
              val active = ref true
              val construction = ref (NONE:G.scope option)
              fun borrowed () = if !active then () else
                raise ERR "borrow" "borrowed graph analysis expired"
              fun protected compute =
                ((borrowed ();
                  let val _ = full_valid ()
                      val old = !pure
                      val _ = pure := true
                      val outcome = Exn.capture compute ()
                      val _ = pure := old
                      val answer = Exn.release outcome
                      val _ = borrowed () val _ = full_valid ()
                  in answer end)
                 handle primary => (W.close expected;raise primary))
              fun unary function current = protected (fn () =>
                (guard current;function current))
              fun binary function (left,right) = protected (fn () =>
                (guard left;guard right;function (left,right)))
              fun inspect current =
                let val actual = resolve current in case view actual of
                    Variable => (case G.view graph (node actual) of
                      G.Variable value => VariableView value
                    | _ => raise ERR "borrow" "variable view changed")
                  | Constant => ConstantView
                      (G.representative graph (node actual))
                  | Application => ApplicationView (application actual)
                  | Abstraction => AbstractionView (abstraction actual)
                end
              fun contains terms current = List.exists
                (fn saved => (#same operations) (current,saved)) terms
              val (sets,bags) = case groups of
                  [(sets,_),(bags,_)] => (sets,bags)
                | _ => raise ERR "borrow" "native analysis required"
              val computed = List.concat
                (List.map (fn (entries,_,_,_) => entries) analyses)
              fun contextual (function,index) =
                Option.map (fn (_,_,argument) => argument)
                  (List.find (fn (other,other_index,_) =>
                    index = other_index andalso
                    (#same operations) (function,other)) computed)
              fun constant raw = protected (fn () =>
                (spend 8;at root (G.constant graph root raw)))
              fun combine (left,right) = protected (fn () =>
                let
                  val _ = guard left val _ = guard right
                  val left = resolve left val right = resolve right
                  val caller =
                    if G.scope_visible graph (scope left) (scope right)
                    then scope left
                    else if G.scope_visible graph (scope right) (scope left)
                    then scope right else raise ERR "borrow"
                      "application operands have no common lexical frame"
                  val _ = spend 8
                in at caller (G.application graph caller
                  (node left,node right)) end)
              val context : native_context =
                {analysis=native_result_of output,goal=hd roots,
                 assumptions=tl roots,denied=at root (#denied data),
                 view=unary inspect,type_of=unary type_of,
                 same=binary (#same operations),
                 free_variables=unary free_variables,
                 strip_comb=unary strip_comb,
                 is_set=unary (contains sets),
                 is_bag=unary (contains bags),
                 is_raw_number=unary (contains numbers),
                 contextual_argument=fn (current,index) =>
                   unary (fn current => contextual (current,index)) current,
                 describe=unary describe,key=unary (key o resolve),
                 constant=constant,mk_comb=combine,
                 step=fn () => protected (fn () => spend 1)}
              fun outbound () : outbound_context = protected (fn () =>
                let
                  fun genvar ty = protected (fn () =>
                    let
                      val frame = case !construction of
                          SOME frame => (G.validate_scope graph frame;frame)
                        | NONE =>
                            let val _ = spend 8
                                val frame = G.new_construction_scope graph
                                  {lexical=root,construction=root}
                            in construction := SOME frame;frame end
                      val _ = spend 8
                    in at frame (G.fresh_bound_variable graph frame
                      (Term.genvar ty)) end)
                  fun application (function,argument) = protected (fn () =>
                    let
                      val _ = guard function val _ = guard argument
                      val (domain,range) = Type.dom_rng (type_of function)
                      val _ = if Type.compare
                          (domain,type_of argument) = EQUAL then () else
                        raise ERR "outbound" "application type mismatch"
                      val term = RecipeApp {owner=recipe_owner,
                        id=recipe_id (),ty=range,function=function,
                        argument=argument}
                    in guard term;term end)
                  fun abstractions (variables,body) = protected (fn () =>
                    let
                      val _ = guard body val _ = List.app guard variables
                      fun bind (variable,body) =
                        let
                          val actual = resolve variable
                          val _ = case view actual of
                              Variable => (case G.view graph (node actual) of
                                  G.Variable (G.Bound,_) => ()
                                | _ => raise ERR "outbound"
                                    "binder is not a scoped Bound variable")
                            | _ => raise ERR "outbound"
                                "binder is not a scoped Bound variable"
                          val ty = Type.--> (type_of actual,type_of body)
                          val term = RecipeAbs {owner=recipe_owner,
                            id=recipe_id (),ty=ty,binder=actual,body=body}
                        in guard term;term end
                    in List.foldr bind body variables end)
                in
                  {analysis= #analysis context,goal= #goal context,
                   assumptions= #assumptions context,denied= #denied context,
                   view= #view context,type_of= #type_of context,
                   same= #same context,free_variables= #free_variables context,
                   strip_comb= #strip_comb context,is_set= #is_set context,
                   is_bag= #is_bag context,
                   is_raw_number= #is_raw_number context,
                   contextual_argument= #contextual_argument context,
                   graph_node=unary (fn term => case resolve term of
                       actual as Term _ => SOME (describe actual)
                     | _ => NONE),
                   key= #key context,semantic_key=unary (semantic_id []),
                   collection_terms=fn () => protected (fn () =>
                     (List.app guard (sets @ bags @ numbers);
                      {sets=sets,bags=bags,raw_numbers=numbers,
                       shadow_same=binary lexical_same})),
                   constant=constant,mk_comb=application,
                   genvar=genvar,list_mk_abs=abstractions,step= #step context}
                end)
              val outcome = Exn.capture action (context,outbound)
              val _ = active := false
              val checked = Exn.capture (fn () => case outcome of Exn.Res _ =>
                    (Redblackmap.foldl (fn (_,term,()) => guard term)
                       () (!positions);
                     List.app (fn (scope,original,source) =>
                       G.validate_opened_view graph scope original source)
                       (!openings);valid ())
                | Exn.Exn _ => ()) ()
              val cleanup = Exn.capture (fn () =>
                Option.app (G.close_scope graph) (!construction)) ()
            in case outcome of Exn.Exn primary => raise primary
              | Exn.Res result =>
                  (Exn.release checked;Exn.release cleanup;result) end
        in consume (output,borrow)
        end) end)
     handle primary => (W.close expected;raise primary))

  fun analyse_collections_with_policy expected query
      ({collections,declared_const_arity,open_opaque}:options) : result =
    analyse_with_policy expected query declared_const_arity open_opaque
      (Explicit collections) (fn (output,_) =>
        case output of (_, [result],_,_) => result
          | _ => raise ERR "analyse" "internal explicit analysis count")

  fun analyse_native_collections_with_policy expected query
      ({syntax,declared_const_arity,open_opaque}:native_options) =
    analyse_with_policy expected query declared_const_arity open_opaque
      (Native syntax) (fn (output,_) => native_result_of output)

  fun with_native_analysis_with_policy expected query
      ({syntax,declared_const_arity,open_opaque}:native_options) action =
    analyse_with_policy expected query declared_const_arity open_opaque
      (Native syntax) (fn (_,borrow) => borrow (fn (context,_) =>
        action context))

  fun with_outbound_analysis_with_policy expected query
      ({syntax,declared_const_arity,open_opaque}:native_options) action =
    analyse_with_policy expected query declared_const_arity open_opaque
      (Native syntax) (fn (_,borrow) => borrow (fn (_,outbound) =>
        action (outbound ())))

  fun with_outbound_seeded_analysis_with_policy expected query
      ({syntax,declared_const_arity,open_opaque}:native_options) seeds action =
    analyse_with_policy expected query declared_const_arity open_opaque
      (SeededNative (syntax,seeds)) (fn (_,borrow) =>
        borrow (fn (_,outbound) => action (outbound ())))
end
