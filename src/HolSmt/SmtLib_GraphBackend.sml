(* Copyright (c) 2026 The HOL4 contributors. *)

structure SmtLib_GraphBackend :> SmtLib_GraphBackend =
struct
  open SmtReplayGraph
  structure G = SmtReplayGraph
  structure R = ReplayRedblackPrivateWork
  structure C = SmtLib_ConstructorSyntax
  structure PV = SmtLib_GraphParserValue
  type constructor_inputs =
    {indices:C.syntax list,arguments:C.syntax list}
  type constructor_state =
    {inputs:constructor_inputs option ref,result:C.syntax option ref,
     forall_blocks:(C.syntax * int list) list option ref}
  fun new_constructor_state () : constructor_state =
    {inputs=ref NONE,result=ref NONE,forall_blocks=ref NONE}
  val ERR = Feedback.mk_HOL_ERR "SmtLib_GraphBackend"
  type environment = {lexical : G.scope, construction : G.scope} option
  type 'a solver_variable =
    {node : 'a, lexical : Term.term, scope : G.scope option}
  datatype 'a view = Atom of Term.term | Apply of 'a * 'a | Opaque
  type index_callback =
    string * (string -> Term.term list -> Term.term list -> Term.term) *
    Term.term option
  datatype 'a backend = Backend of
    {owner : unit ref, graph : G.graph option, initial : environment,
     index_callbacks : {depth:int ref, history:index_callback list ref},
     constructor_state : constructor_state,
     syntax_spend : IntInf.int -> unit,
     source_syntax : environment -> 'a -> C.syntax,
     failure_requires_propagation : unit -> bool,
     validate_environment : environment -> unit,
     type_of : 'a -> Type.hol_type,
     view : environment -> 'a -> 'a view,
     same_value : 'a * 'a -> bool,
     variable_descriptor : 'a -> Term.term option,
     private_variable : 'a -> bool,
     solver_variables : unit -> 'a solver_variable list,
     mk_bound_var : string * Type.hol_type -> Term.term,
     source : environment -> Term.term -> 'a,
     literal : environment -> Term.term -> 'a,
     variable : environment -> G.variable_kind -> Term.term -> 'a,
     fresh_solver_variable : environment -> Term.term -> 'a,
     reference : environment -> Term.term * 'a -> 'a,
     capture_alias : environment -> ('a * 'a) list ->
       'a * (string * int * 'a) list -> 'a * (string * int * 'a) list,
     bound_variable : environment -> Term.term -> 'a,
     application : environment -> 'a * 'a -> 'a,
     new_scope : environment -> (Term.term * 'a) list -> environment,
     new_let_scope : environment -> (Term.term * 'a) list -> environment,
     close_scope : environment -> unit,
     abstraction : environment -> environment -> 'a * 'a -> 'a,
     new_abstraction_scope : environment -> environment,
     abort_abstraction_scope : environment -> unit,
     let_binding : Term.term * 'a -> 'a,
     finish_let : (string * Term.term * 'a) list * 'a -> 'a}
  datatype 'a frame = Frame of
    {owner : unit ref, active : bool ref, environment : environment,
     bindings : (string, 'a) Redblackmap.dict, blocked : string HOLset.set,
     identities : ('a * 'a) list}
  type 'a binder = (string * string * Type.hol_type) * 'a option

  datatype 'a binding_origin = BindingOrigin of
    {backend : 'a backend,parent : 'a frame,child : 'a frame,
     graph : G.graph,parent_scope : G.scope,scope : G.scope,
     variables : 'a list,descriptors : (string * string * Type.hol_type) list,
     binders : bool,epoch : int,symbols : int}

  fun new_index_callbacks () = {depth=ref 0,history=ref []}
  fun capture_index_callbacks
      (Backend {index_callbacks={depth,history},...}) action =
    let
      val saved = !history
      val _ = depth := !depth + 1
      val result = Exn.capture action ()
      val after = !history
      val _ = depth := !depth - 1
      val _ = if !depth=0 then history := [] else ()
      fun prefix pending accumulated =
        if Portable.pointer_eq (saved,pending) then accumulated
        else case pending of x::xs => prefix xs (x::accumulated)
          | [] => raise ERR "index" "invalid callback history"
      val last = if Portable.pointer_eq (saved,after) then NONE
                 else SOME (hd after)
    in (Exn.release result,{last=last,callbacks=fn () => prefix after []}) end
  fun note_index_callback (Backend {index_callbacks={depth,history},...})
      entry =
    if !depth=0 then () else history := entry :: !history
  fun index_source_active (Backend {index_callbacks={depth,...},...}) = !depth>0
  fun failure_requires_propagation
      (Backend {failure_requires_propagation,...}) =
    failure_requires_propagation ()
  exception IndexSyntaxError of exn
  exception IndexBinderError of exn
  fun index_callback backend action =
    action () handle error as Feedback.HOL_ERR _ =>
      if index_source_active backend andalso
         not (failure_requires_propagation backend) then
        raise IndexSyntaxError error
      else raise error

  fun with_constructor_sources
      (Backend {constructor_state={inputs,result,...},...}) sources action =
    let
      val saved_inputs = !inputs
      val saved_result = !result
      val _ = inputs := SOME sources
      val _ = result := NONE
      val outcome = Exn.capture action ()
      val annotation = !result
      val _ = inputs := saved_inputs
      val _ = result := saved_result
    in (Exn.release outcome,annotation) end
  fun constructor_sources (Backend {constructor_state={inputs,...},...}) =
    !inputs
  fun constructor_source (Backend {constructor_state={result,...},...}) =
    !result
  fun note_constructor_source
      (Backend {constructor_state={inputs,result,...},...}) syntax =
    case !inputs of NONE => () | SOME _ => result := SOME syntax
  fun syntax_spend (Backend {syntax_spend,...}) amount = syntax_spend amount
  fun enable_forall_blocks
      (Backend {constructor_state={forall_blocks,...},...}) =
    forall_blocks := SOME []
  fun record_source_binder
      (backend as Backend {constructor_state={forall_blocks,...},...})
      (kind,count,source) =
    if kind<>"forall" then () else case !forall_blocks of NONE => ()
    | SOME entries =>
      (* Recording is constant-time even for exponentially shared binder
         bodies. Defer ordinary alpha queries until a constructor needs the
         block boundary; ordinary parsing must not compare every binder. *)
      (syntax_spend backend 1;
       forall_blocks := SOME ((source,[count])::entries))
  fun forall_block
      (backend as Backend {constructor_state={forall_blocks,...},...})
      source =
    let
      val spend = syntax_spend backend
      fun lookup [] found = found
        | lookup ((candidate,counts)::rest) found =
            if C.aconv spend (candidate,source) then
              (case (counts,found) of
                 ([count],NONE) => lookup rest (SOME (candidate,count))
               | ([count],SOME (_,old)) =>
                   if count=old then lookup rest found else ambiguous ()
               | _ => ambiguous ())
            else lookup rest found
      and ambiguous () = raise Feedback.mk_HOL_ERR "CPC_ProofParser"
        "cpc_quantifiers_skolemize_parsefn"
        "source FORALL binder-block metadata is ambiguous"
    in lookup (case !forall_blocks of NONE => []
      | SOME entries => (spend (IntInf.fromInt (List.length entries));
                         List.rev entries)) NONE end

  fun type_of (Backend {type_of, ...}) value = type_of value
  fun variable_descriptor (Backend {variable_descriptor, ...}) value =
    variable_descriptor value
  fun binder_reference
      (backend as Backend {private_variable,...}) key node =
    case variable_descriptor backend node of
      SOME variable =>
        let val (name,ty) = Term.dest_var variable
        in ((key,name,ty),if private_variable node then SOME node else NONE)
        end
    | NONE => raise Feedback.mk_HOL_ERR "SmtLib_Parser" "parse_binder_term"
        "CPC @list binder contains a non-variable term"
  fun solver_variables (Backend {solver_variables, ...}) = solver_variables ()
  fun root (Backend {owner, initial, ...}) =
    Frame {owner = owner, active = ref true, environment = initial,
           bindings = Redblackmap.mkDict String.compare,
           blocked = HOLset.empty String.compare, identities = []}
  fun checked_frame (Backend {owner, validate_environment, ...})
      (Frame {owner = frame_owner, active, environment, bindings, ...}) =
    if owner <> frame_owner then
      raise ERR "frame" "lexical frame belongs to another backend"
    else if not (!active) then raise ERR "frame" "lexical frame is closed"
    else (validate_environment environment; (environment, bindings))
  fun scoped_body (frame as Frame {active, ...}) body =
    let val result = body frame
          handle error => (active := false; raise error)
    in active := false; result end
  fun finish_scopes close_scope environments action =
    let
      fun close () = List.app close_scope environments
      val result = action () handle error =>
        ((close () handle _ => ()); raise error)
    in close (); result end
  fun frame_blockers (Frame {blocked, ...}) = blocked
  fun frame_identities (Frame {identities,...}) = identities
  fun is_blocked backend frame key =
    (ignore (checked_frame backend frame);
     HOLset.member (frame_blockers frame, key))
  fun binder_operand (backend as Backend {same_value,...})
      frame source node =
    let
      val _ = checked_frame backend frame
      val spend = syntax_spend backend
      fun lexical variable =
        let val (name,ty) = Term.dest_var variable
        in ((name,name,ty),NONE) end
      fun original [] = node
        | original ((old,bound)::rest) =
            (spend 1;
             if same_value (bound,node) then old else original rest)
    in case C.view spend source of
        C.Variable variable => lexical variable
      | C.Atom atom =>
          if Term.is_var atom then
            binder_reference backend (#1 (Term.dest_var atom))
              (original (frame_identities frame))
          else raise Feedback.mk_HOL_ERR "SmtLib_Parser" "parse_binder_term"
            "CPC @list binder contains a non-variable term"
      | _ => raise Feedback.mk_HOL_ERR "SmtLib_Parser" "parse_binder_term"
          "CPC @list binder contains a non-variable term"
    end
  fun check_blocked blocked key =
    if HOLset.member (blocked, key) then
      raise ERR "lookup" "proof binding is not a term"
    else ()
  fun lookup backend frame key =
    let val bindings = #2 (checked_frame backend frame)
        val _ = check_blocked (frame_blockers frame) key
    in Redblackmap.peek (bindings, key) end
  fun binding_type_lookup backend frame =
    let val bindings = #2 (checked_frame backend frame)
        val blocked = frame_blockers frame
    in fn key =>
      (check_blocked blocked key;
       Option.map (type_of backend) (Redblackmap.peek (bindings,key)))
    end
  fun source (backend as Backend {source, ...}) frame term =
    source (#1 (checked_frame backend frame)) term
  fun source_syntax (backend as Backend {source_syntax,...}) frame value =
    source_syntax (#1 (checked_frame backend frame)) value
  fun literal (backend as Backend {literal, ...}) frame term =
    literal (#1 (checked_frame backend frame)) term
  fun variable (backend as Backend {variable, mk_bound_var, ...}) frame kind
      (name, ty) =
    variable (#1 (checked_frame backend frame)) kind (mk_bound_var (name, ty))
  fun fresh_solver_variable
      (backend as Backend {fresh_solver_variable, mk_bound_var, ...})
      frame descriptor =
    fresh_solver_variable (#1 (checked_frame backend frame))
      (mk_bound_var descriptor)
  fun capture_alias (backend as Backend {capture_alias,...}) frame value =
    capture_alias (#1 (checked_frame backend frame))
      (frame_identities frame) value

  fun reference (backend as Backend {reference, ...}) frame declaration =
    reference (#1 (checked_frame backend frame)) declaration
  fun application (backend as Backend {application,view,...}) frame
      (function,argument) =
    let val environment = #1 (checked_frame backend frame)
    in application environment (function,argument)
      handle error as Feedback.HOL_ERR detail =>
        if index_source_active backend andalso
           not (failure_requires_propagation backend) andalso
           Feedback.top_function_of detail = "application" andalso
           Feedback.message_of detail = "application operand type mismatch"
        then
          let val binder = case view environment function of
                Atom term => Term.is_const term andalso
                  let val {Thy,Name,...} = Term.dest_thy_const term
                  in Thy="bool" andalso List.exists (fn n => n=Name)
                    ["!","?","@"] end
              | _ => false
          in if binder then raise IndexBinderError error
             else raise IndexSyntaxError error end
        else raise error
    end
  fun view (backend as Backend {view, ...}) frame value =
    view (#1 (checked_frame backend frame)) value
  fun same_value (backend as Backend {same_value, ...}) (left,right) =
    (ignore (type_of backend left); ignore (type_of backend right);
     same_value (left,right))

  fun small_index_with_policy backend frame limit value =
    let
      val used = ref (0:IntInf.int)
      fun admit current =
        (used := !used + 1;
         if SmtReplayResourcePolicy.allows limit (!used) then () else
           raise ERR "index" "expanded literal index";
         case view backend frame current of
           Atom term => term
         | Apply (f,x) => Term.mk_comb (admit f,admit x)
         | Opaque => raise ERR "index" "opaque literal index")
      (* Reconstruct only explicitly admitted index syntax, never a graph
         operand. No binder opening, evaluation or substitution occurs. *)
    in admit value end

  fun term_view term =
    if Term.is_var term orelse Term.is_const term then Atom term
    else if Term.is_comb term then Apply (Term.dest_comb term)
    else Opaque
  fun graph_view graph node = case G.view graph node of
      G.Variable (_,term) => Atom term
    | G.Constant _ => Atom (G.representative graph node)
    | G.Application pair => Apply pair
    | _ => Opaque

  (* Query-local sharing only. Keys authenticate before memo lookup; a
     cached syntax result grants neither lifetime nor proof authority.
     Variable descriptors travel with syntax so binder and body visits use
     the same lexical spelling without visiting a shared binder twice. *)
  fun source_syntax_walk (spend : IntInf.int -> unit)
      compare key expand original =
    let
      val memo = ref (Redblackmap.mkDict
        (fn pair => (spend 1;compare pair)))
      fun visit current =
        let
          val _ = spend 1
          val id = key current
        in case Redblackmap.peek (!memo,id) of
            SOME result => result
          | NONE =>
              let val result = expand visit current
                  val _ = spend 1
                  val _ = memo := Redblackmap.insert (!memo,id,result)
              in result end
        end
    in case visit original of (syntax,_) => syntax end

  fun graph_source_syntax graph descriptor original =
    let
      fun key node = (ignore (G.type_of graph node);G.node_id node)
      fun expand (visit : G.node -> C.syntax * Term.term option) node =
        case G.view graph node of
          G.Variable (_,term) =>
            let val lexical = case descriptor node of
                    SOME lexical => lexical | NONE => term
            in (C.variable lexical,SOME lexical) end
        | G.Constant _ => (C.native (G.representative graph node),NONE)
        | G.Application (f,x) =>
            (C.application (#1 (visit f),#1 (visit x)),NONE)
        | G.AdmittedBinder {binder,body,frame} =>
            let val _ = G.validate_scope graph frame
                val (_,variable) = visit binder
                val lexical = case variable of SOME term => term
                  | NONE => raise ERR "source_syntax" "nonvariable binder"
            in (C.abstraction (lexical,#1 (visit body)),NONE) end
        | G.OpaqueRetained =>
            (* The existing original only, not constructed graph syntax. *)
            (C.native (G.representative graph node),NONE)
    in source_syntax_walk (fn _ => ()) Int.compare key expand original end

  fun value_source_syntax context descriptor original =
    PV.protect context (fn () =>
      let
        fun compare ((lk,li),(rk,ri)) =
          case Int.compare (lk,rk) of EQUAL => Int.compare (li,ri)
            | order => order
        fun expand
            (visit : PV.proof_term -> C.syntax * Term.term option) current =
          case PV.proof_view context current of
            PV.ProofVariable (_,term) =>
              let val lexical = case descriptor
                        (PV.proof_key context current) of
                      SOME lexical => lexical | NONE => term
              in (C.variable lexical,SOME lexical) end
          | PV.ProofConstant term => (C.native term,NONE)
          | PV.ProofApplication (f,x) =>
              (C.application (#1 (visit f),#1 (visit x)),NONE)
          | PV.ProofAbstraction {binder,body,...} =>
              let val (_,variable) = visit binder
                  val lexical = case variable of SOME term => term
                    | NONE => raise ERR "source_syntax" "nonvariable binder"
              in (C.abstraction (lexical,#1 (visit body)),NONE) end
          | PV.ProofOpaque =>
              (case PV.proof_graph_reference context current of
                 SOME {graph,node,...} =>
                   (case G.view graph node of
                      G.OpaqueRetained =>
                        (PV.spend context 1;
                         (C.native (G.representative graph node),NONE))
                    | _ => raise ERR "source_syntax" "not original syntax")
               | NONE => raise ERR "source_syntax" "missing original syntax")
      in source_syntax_walk (PV.spend context) compare
        (PV.proof_key context) expand (PV.proof_term context original) end)

  datatype 'a alias_view = AliasAtom
    | AliasApplication of 'a * 'a | AliasBinder of 'a * 'a
  fun scoped_alias
      {spend,key,free,resolve,visible,atom,view,apply,abstract}
      base root =
    let
      fun compare ((ls,ln),(rs,rn)) =
        (spend 1;case Int.compare (ls,rs) of
           EQUAL => Int.compare (ln,rn) | order => order)
      val memo = ref (Redblackmap.mkDict compare)
      val translated = ref (Redblackmap.mkDict
        (fn (a,b) => (spend 1;Int.compare (a,b))))
      fun same (a,b) = (spend 1;key a=key b)
      fun replacement bindings node =
        case List.find (fn (old,_,_) => same (old,node)) bindings of
          SOME (_,value,_) => value | NONE => resolve node
      fun changed bindings node =
        case free node of NONE => true
        | SOME variables => List.exists (fn variable =>
            not (same (variable,replacement bindings variable))) variables
      fun visit caller bindings node =
        let val _ = spend 1
            (* Unrelated inner binders must not split shared-suffix caches.
               Build in the outermost scope containing the actual captures,
               not whichever irrelevant binder happened to visit first. *)
            val (scope,bindings) = case free node of NONE => (caller,bindings)
              | SOME variables =>
                  let val relevant = List.filter (fn (old,_,_) =>
                        List.exists (fn variable => same (old,variable))
                          variables) bindings
                  in (case relevant of [] => base | (_,_,scope)::_ => scope,
                      relevant) end
            val index = (G.scope_id scope,key node)
        in case Redblackmap.peek (!memo,index) of SOME result => result
         | NONE =>
          let
            val result = if not (changed bindings node) andalso
                visible scope node then node else
              case view node of AliasAtom =>
                atom scope (replacement bindings node)
              | AliasApplication (f,x) =>
                  let val f' = visit scope bindings f
                      val x' = visit scope bindings x
                  in if same (f,f') andalso same (x,x') andalso
                      visible scope node then node
                     else apply scope (f',x') end
              | AliasBinder (binder,body) =>
                  abstract scope binder (fn child => fn variable =>
                    visit child ((binder,variable,child)::bindings) body)
            val _ = memo := Redblackmap.insert (!memo,index,result)
            val previous = case Redblackmap.peek (!translated,key node) of
                NONE => [] | SOME nodes => nodes
            val next = if List.exists (fn saved => same (saved,result))
                previous then previous else previous @ [result]
            val _ = translated := Redblackmap.insert
              (!translated,key node,next)
          in result end
        end
      val value = visit base [] root
      fun translate node =
        case Redblackmap.peek (!translated,key node) of
          SOME nodes => nodes | NONE => [node]
    in {value=value,translate=translate} end

  fun graph_lexical_alias graph variables descriptors node =
    case Redblackmap.peek (!descriptors,G.node_id node) of NONE => NONE
    | SOME term =>
        (case Redblackmap.peek (!variables,
            (G.scope_id (G.node_scope graph node),term)) of
           SOME original => if original=node then SOME term else NONE
         | NONE => NONE)
  fun capture_blocks {value,translate} blocks =
    (value,List.concat (List.map (fn (kind,count,node) =>
      List.map (fn node => (kind,count,node)) (translate node)) blocks))
  fun graph_capture_alias graph regular maximum literal_limit lexical scope
      identities (root,blocks) =
    capture_blocks (scoped_alias
      {spend=fn _ => (),key=G.node_id,free=G.free_variable_nodes graph,
       resolve=fn node =>
         case List.find (fn (old,_) => old=node) identities of
           SOME (_,bound) => bound
         | NONE => case regular node of NONE => node
           | SOME term => G.resolve_reference graph lexical term node,
       visible=fn scope => fn node =>
         G.scope_visible graph scope (G.node_scope graph node),
       atom=fn scope => fn node =>
         case G.view graph node of
           G.OpaqueRetained =>
             (* Capture may carry a retained ORIGINAL below a new binder.
                Admit its bounded public opening, never assume an unknown
                FV set is empty and never open a constructed operand Term.
                Ordinary source imports keep their lazy opaque contract. *)
             (case G.source_anchor graph node of
                SOME {original,...} =>
                  (case SmtReplayImport.raw_size_with_policy maximum original
                     of NONE => node
                   | SOME _ => #node (G.record_opened_view_with_policy graph
                       scope maximum node))
              | NONE => node)
         | _ => if G.scope_visible graph scope (G.node_scope graph node)
             then node else case G.view graph node of
               G.Constant _ => G.constant graph scope
                 (G.representative graph node)
             | _ => case G.source_anchor graph node of
                 SOME {original,...} => #node (G.import_with_policy graph
                   scope literal_limit original)
               | NONE => node,
       view=fn node => case G.view graph node of
           G.Application pair => AliasApplication pair
         | G.AdmittedBinder {binder,body,...} => AliasBinder (binder,body)
         | _ => AliasAtom,
       apply=G.application graph,
       abstract=fn parent => fn old => fn body =>
         let val child = G.new_construction_scope graph
               {lexical=lexical,construction=parent}
             fun build () =
               let val binder = G.fresh_bound_variable graph child
                     (G.representative graph old)
               in G.recorded_abstraction_with_policy graph parent maximum
                 {binder=binder,body=body child binder,body_frame=child} end
         in build () handle primary =>
           ((G.close_scope graph child handle _ => ());raise primary) end}
      scope root) blocks

  fun terms {mk_bound_var, mk_let} = Backend
    {owner = ref (), graph = NONE, initial = NONE, type_of = Term.type_of,
     index_callbacks = new_index_callbacks (),
     constructor_state = new_constructor_state (),
     syntax_spend = fn _ => (),
     source_syntax = fn _ => C.native,
     failure_requires_propagation = fn () => false,
     view = fn _ => term_view, same_value = Portable.pointer_eq,
     variable_descriptor = fn term =>
       if Term.is_var term then SOME term else NONE,
     private_variable = fn _ => false,
     solver_variables = fn () => [],
     validate_environment = fn _ => (),
     mk_bound_var = mk_bound_var, source = fn _ => fn term => term,
     literal = fn _ => fn term => term,
     variable = fn _ => fn _ => fn term => term,
     fresh_solver_variable = fn _ => Term.genvar o Term.type_of,
     reference = fn _ => #2, capture_alias = fn _ => fn _ => Lib.I,
     bound_variable = fn _ => fn term => term,
     application = fn _ => Term.mk_comb,
     new_scope = fn _ => fn _ => NONE,
     new_let_scope = fn _ => fn _ => NONE,
     close_scope = fn _ => (),
     abstraction = fn _ => fn _ => Term.mk_abs,
     new_abstraction_scope = fn _ => NONE,
     abort_abstraction_scope = fn _ => (),
     let_binding = fn (variable, _) => variable, finish_let = mk_let}

  fun graphs {graph, scope, import_limit, literal_limit, binder_limit} =
    let
      val _ = G.validate_scope graph scope
      val _ = if import_limit > 0 andalso literal_limit > 0 andalso
          binder_limit > 0 then ()
        else raise ERR "graphs" "nonpositive public import contract"
      fun scopes (SOME scopes) = scopes
        | scopes NONE = raise ERR "graphs" "missing graph environment"
      fun lexical environment = #lexical (scopes environment)
      fun construction environment = #construction (scopes environment)
      val lexical_descriptors = ref
        (Redblackmap.mkDict Int.compare : (int, Term.term) Redblackmap.dict)
      fun retain_variable term node =
        (lexical_descriptors := Redblackmap.insert
           (!lexical_descriptors, G.node_id node, term); node)
      fun compare_private ((left_scope, left_term),
                           (right_scope, right_term)) =
        case Int.compare (left_scope, right_scope) of
          EQUAL => Term.compare (left_term, right_term) | order => order
      val private_variables = ref (Redblackmap.mkDict compare_private)
      val solver_variables = ref ([] : G.node solver_variable list)
      val recorded_variables = ref (HOLset.empty Int.compare)
      fun record_flexible term node =
        (if HOLset.member (!recorded_variables, G.node_id node) then () else
           (recorded_variables := HOLset.add
              (!recorded_variables, G.node_id node);
            solver_variables :=
              {node = node, lexical = term,
               scope = SOME (G.node_scope graph node)} :: !solver_variables);
         node)
      fun fresh_flexible environment term =
        record_flexible term (retain_variable term
          (G.fresh_flexible_variable graph (construction environment) term))
      fun flexible environment term =
        let
          val scope = construction environment
          val key = (G.scope_id scope, term)
          val default = case Redblackmap.peek (!private_variables, key) of
              SOME node => node
            | NONE =>
                let val node = retain_variable term
                      (G.fresh_flexible_variable graph scope term)
                in private_variables := Redblackmap.insert
                     (!private_variables, key, node); node end
          val node = G.resolve_reference graph
            (lexical environment) term default
          val _ = case G.view graph node of
              G.Variable (G.SolverFlexible, _) =>
                ignore (record_flexible term node)
            | _ => ()
        in node end
      fun import environment term =
        #node (G.import graph (construction environment) import_limit term)
      fun source _ term =
        let val node = #node (G.import graph scope import_limit term)
        in if Term.is_var term then retain_variable term node else node end
      fun literal environment term =
        let
          val _ = case SmtReplayImport.bounded_raw_size literal_limit term of
              SOME _ => ()
            | NONE => raise ERR "literal" "literal exceeds bounded contract"
          val _ = if List.null (Term.free_vars term) then () else
            raise ERR "literal" "literal contains an unowned free variable"
        in if Term.is_const term then
          G.constant graph (construction environment) term
        else import environment term end
    in Backend
      {owner = ref (), graph = SOME graph,
       initial = SOME {lexical = scope, construction = scope},
       validate_environment = fn environment =>
         (G.validate_scope graph (lexical environment);
          G.validate_scope graph (construction environment)),
       type_of = G.type_of graph, view = fn _ => graph_view graph,
       same_value = op=,
       variable_descriptor = fn node =>
         (ignore (G.type_of graph node);
          Redblackmap.peek (!lexical_descriptors, G.node_id node)),
       solver_variables = fn () => List.rev (!solver_variables),
       mk_bound_var = Term.mk_var, source = source, literal = literal,
       fresh_solver_variable = fresh_flexible,
       variable = fn environment => fn kind => fn term =>
         case kind of G.RigidSource =>
           G.resolve_variable graph (lexical environment) term
         | G.SolverFlexible => flexible environment term
         | _ => G.variable graph (construction environment) kind term,
       reference = fn environment => fn (term, value) =>
         G.resolve_reference graph (lexical environment) term value,
       capture_alias = fn environment => graph_capture_alias graph
         (graph_lexical_alias graph private_variables lexical_descriptors)
         (SmtReplayResourcePolicy.AtMost (IntInf.fromInt binder_limit))
         (SmtReplayResourcePolicy.AtMost (IntInf.fromInt literal_limit))
         (lexical environment) (construction environment),
       private_variable = fn node =>
         (case G.view graph node of G.Variable (G.SolverFlexible,_) =>
            not (Option.isSome (graph_lexical_alias graph
              private_variables lexical_descriptors node))
          | _ => false),
       bound_variable = fn environment => fn term => retain_variable term
         (G.fresh_bound_variable graph (construction environment) term),
       application = fn environment =>
         G.application graph (construction environment),
       new_scope = fn environment => fn bindings =>
         let val scope = G.new_scope graph (lexical environment) bindings
         in SOME {lexical = scope, construction = scope} end,
       (* Let aliases affect name resolution, while constructed values
          retain the enclosing proof block's construction scope. *)
       new_let_scope = fn environment => fn bindings =>
         SOME {lexical = G.new_scope graph (lexical environment) bindings,
               construction = construction environment},
       close_scope = fn environment => G.close_scope graph
         (lexical environment),
       constructor_state = new_constructor_state (),
       syntax_spend = fn _ => (),
       source_syntax = fn _ => graph_source_syntax graph
         (fn node => Redblackmap.peek (!lexical_descriptors,G.node_id node)),
       abstraction = fn environment => fn body_environment =>
         fn (binder,body) =>
           G.recorded_abstraction graph (construction environment) binder_limit
             {binder = binder,body = body,
              body_frame = construction body_environment},
       index_callbacks = new_index_callbacks (),
       failure_requires_propagation = fn () => false,
       new_abstraction_scope = fn environment =>
         let val retained = G.new_construction_scope graph
               {lexical = lexical environment,
                construction = construction environment}
             val lexical = G.new_scope graph retained []
               handle primary =>
                 ((G.close_scope graph retained handle _ => ());raise primary)
         in SOME {lexical = lexical,construction = retained} end,
       abort_abstraction_scope = fn environment =>
         G.close_scope graph (construction environment),
       let_binding = #2, finish_let = #2}
    end

  fun unique_key (key, seen) =
    if HOLset.member (seen, key) then
      raise ERR "let_expression" "duplicate simultaneous binding key"
    else HOLset.add (seen, key)
  fun unique_keys entries =
    ignore (List.foldl (fn ((key, _, _), seen) => unique_key (key, seen))
      (HOLset.empty String.compare) entries)

  (* No entry traversal or set rebuilding on the ordinary blocker-free
     path. Blockers are lexical metadata, never graph operands or sources. *)
  fun shadow_blockers parent entries =
    let val blocked = frame_blockers parent
    in if HOLset.isEmpty blocked then blocked else
      List.foldl (fn ((key, _, _), blocked) =>
        if HOLset.member (blocked, key) then HOLset.delete (blocked, key)
        else blocked) blocked entries
    end
  fun mixed_blockers parent entries keys =
    let val inherited = shadow_blockers parent entries
    in case keys of [] => inherited
      | _ =>
        let
          val added = List.foldl unique_key
            (HOLset.empty String.compare) keys
          val _ = List.app (fn (key, _, _) =>
            if HOLset.member (added, key) then
              raise ERR "let_expression" "duplicate simultaneous binding key"
            else ()) entries
        in HOLset.union (inherited, added) end
    end

  fun let_expression
      (backend as Backend {owner, mk_bound_var, new_let_scope, close_scope,
                           let_binding, finish_let, ...}) parent entries body =
    let
      val (environment, dictionary) = checked_frame backend parent
      val _ = unique_keys entries
      (* RHS elaboration precedes every dictionary/scope extension. *)
      val values = List.map (fn (key, name, action) =>
        let val value = action parent in
          (key, mk_bound_var (name, type_of backend value), value)
        end) entries
      val bindings = List.map (fn (key, variable, value) =>
        (key, variable, let_binding (variable, value))) values
      val environment = new_let_scope environment
        (List.map (fn (_, variable, value) => (variable, value)) bindings)
      val dictionary = List.foldl (fn ((key, _, value), dictionary) =>
        Redblackmap.insert (dictionary, key, value)) dictionary bindings
      val child = Frame {owner = owner, active = ref true,
                         environment = environment,
                         bindings = dictionary,
                         blocked = shadow_blockers parent entries,
                         identities = frame_identities parent}
    in finish_scopes close_scope [environment] (fn () =>
      let
        val result = scoped_body child body
        val _ = ignore (type_of backend result)
      in finish_let (values, result) end) end

  fun abstraction_with_identity (backend as Backend
      {owner, mk_bound_var, bound_variable, new_abstraction_scope,
       new_let_scope, close_scope, abstraction, abort_abstraction_scope, ...})
      parent
      {dictionary_binding,binder=((key, name, ty), original)} body =
    let
      val (environment, dictionary) = checked_frame backend parent
      val term = mk_bound_var (name, ty)
      val binder_frame = new_abstraction_scope environment
      val environments = ref [binder_frame]
      fun close_lexical () = List.app
        (fn frame => close_scope frame handle _ => ()) (!environments)
      fun abort primary =
        (close_lexical ();
         (abort_abstraction_scope binder_frame handle _ => ());raise primary)
      fun construct () =
        let
          val binder = bound_variable binder_frame term
          val body_environment = new_let_scope binder_frame
            (case original of NONE => [(term,binder)] | SOME _ => [])
          val _ = environments := body_environment :: !environments
          (* Native CPC binders capture existing lexical variables, not
             arbitrary proof-dictionary entries with the same spelling.
             An inherited frame entry is a lexical LET/sorted binder. *)
          val bind_dictionary = not (Option.isSome original) andalso
            (dictionary_binding orelse
             (case Redblackmap.peek (dictionary,key) of
                SOME value => Type.compare (type_of backend value,ty)=EQUAL
              | NONE => false))
          val child = Frame {owner = owner, active = ref true,
            environment = body_environment,
            bindings = if bind_dictionary then
                Redblackmap.insert (dictionary,key,binder) else dictionary,
            blocked = if bind_dictionary then
                shadow_blockers parent [(key, name, ty)]
              else frame_blockers parent,
            identities = case original of NONE => frame_identities parent
              | SOME old => (old,binder)::frame_identities parent}
          val result = scoped_body child body
        in abstraction environment body_environment (binder,result) end
      val result = construct () handle primary => abort primary
      val _ = List.app close_scope (!environments)
        handle primary => abort primary
    in result end

  fun abstraction backend parent descriptor body =
    abstraction_with_identity backend parent
      {dictionary_binding=true,binder=(descriptor,NONE)} body

  fun frame_scope backend frame =
    case #1 (checked_frame backend frame) of
      NONE => NONE | SOME {construction, ...} => SOME construction

  fun frame_lexical_scope backend frame =
    case #1 (checked_frame backend frame) of
      NONE => NONE | SOME {lexical, ...} => SOME lexical

  (* No caller scope, frame guard callback or origin constructor is public. *)
  fun opened_origin (backend as Backend {graph,...}) parent child
      variables descriptors binders =
    case graph of NONE => NONE
      | SOME graph => SOME (BindingOrigin
          {backend = backend,parent = parent,child = child,graph = graph,
           parent_scope = valOf (frame_scope backend parent),
           scope = valOf (frame_scope backend child),variables = variables,
           descriptors = descriptors,binders = binders,
           epoch = Type.type_epoch (),symbols = Term.term_epoch ()})
  fun binding_origin_owner (BindingOrigin {graph,parent_scope,scope,...}) =
    {graph = graph,parent_scope = parent_scope,scope = scope}
  fun binding_origin_data graph parent_scope
      (BindingOrigin {backend,parent,child,graph = held,
       parent_scope = original,scope,variables,descriptors,binders,
       epoch,symbols}) =
    let
      val _ = if Portable.pointer_eq (graph,held) andalso
          parent_scope = original then () else
        raise ERR "binding_origin" "different graph or genuine parent"
      fun guard () =
        (if Type.type_epoch () = epoch andalso
            Term.term_epoch () = symbols then () else
           raise ERR "binding_origin" "origin retirement epoch changed";
         if frame_scope backend parent = SOME original andalso
             frame_scope backend child = SOME scope then () else
           raise ERR "binding_origin" "actual lexical frame changed")
      val _ = guard ()
      val _ = if G.scope_visible graph scope original then () else
        raise ERR "binding_origin" "child escaped its genuine parent"
      val _ = List.app (fn node =>
        if G.scope_visible graph scope (G.node_scope graph node) then () else
          raise ERR "binding_origin" "variable escaped its actual child")
        variables
      val _ = guard ()
    in {scope = scope,variables = variables,descriptors = descriptors,
      binders = binders} end

  (* Constructed only from an authentic private BindingOrigin. The meter
     is supplied internally by the original Work consumer, not by a proof
     caller. Frame environments, owner fields and node scopes are immutable;
     every mutable lexical active ref remains in the retained program. *)
  datatype binding_guard = BindingGuard of
    {meter:R.scope_meter,graph:G.graph,parent_scope:G.scope,scope:G.scope,
     parent_active:bool ref,child_active:bool ref,
     parent_paths:(G.scope * G.scope_path) list,
     child_paths:(G.scope * G.scope_path) list,
     visible:G.binding_scope_path,
     variables:(G.scope * G.binding_scope_path) list,
     epoch:int,symbols:int,work:IntInf.int,
     data:{scope:G.scope,variables:G.node list,
       descriptors:(string * string * Type.hol_type) list,binders:bool}}
  fun binding_guard_uses expected (BindingGuard {meter,...}) =
    R.same_scope_meter (expected,meter)
  fun binding_guard_work (BindingGuard {work,...}) = work
  fun binding_guard_data (BindingGuard {data,...}) = data
  fun prepare_binding_guard graph caller
      (BindingOrigin {backend=Backend {owner,graph=original,...},
        parent,child,graph=held,parent_scope,scope,variables,descriptors,
        binders,epoch,symbols}) meter =
    let
      val _ = R.scope_meter_charge meter 8
      val _ = if Portable.pointer_eq (graph,held) andalso
          caller = parent_scope then () else
        raise ERR "binding_guard" "different graph or genuine parent"
      val _ = case original of SOME actual =>
          if Portable.pointer_eq (actual,graph) then () else
            raise ERR "binding_guard" "different private backend graph"
        | NONE => raise ERR "binding_guard" "ordinary backend has no origin"
      fun frame (Frame {owner=actual,active,environment,...}) expected =
        let
          val _ = R.scope_meter_charge meter 7
          val _ = if actual = owner then () else
            raise ERR "binding_guard" "different private lexical owner"
          val (lexical,construction) = case environment of
              SOME {lexical,construction} => (lexical,construction)
            | NONE => raise ERR "binding_guard" "no graph environment"
          val _ = R.scope_meter_charge meter 3
          val _ = if construction = expected then () else
            raise ERR "binding_guard" "actual lexical frame differs"
          fun path scope =
            let val (program,_) = G.prepare_shared_scope_path graph scope meter
                val _ = R.scope_meter_charge meter 2
            in (scope,program) end
          val lexical_path = path lexical
          val construction_path = path construction
          val _ = R.scope_meter_charge meter 3
        in (active,[lexical_path,construction_path]) end
      val (parent_active,parent_paths) = frame parent parent_scope
      val (child_active,child_paths) = frame child scope
      val visible = G.prepare_binding_scope_path graph scope parent_scope meter
      fun node_paths [] = (R.scope_meter_charge meter 1;[])
        | node_paths (node::rest) =
          let
            val _ = R.scope_meter_charge meter 2
            val required = G.binding_node_scope graph node meter
            val program = G.prepare_binding_scope_path graph scope required
              meter
            val tail = node_paths rest
            val _ = R.scope_meter_charge meter 2
          in (required,program)::tail end
      val paths = node_paths variables
      fun sum [] = (R.scope_meter_charge meter 1;1:IntInf.int)
        | sum ((_,path)::rest) =
            (R.scope_meter_charge meter 3;
             G.scope_path_validation_work path+sum rest+2)
      fun variable_sum [] = (R.scope_meter_charge meter 1;1:IntInf.int)
        | variable_sum ((_,path)::rest) =
            (R.scope_meter_charge meter 3;
             G.binding_scope_path_work path+variable_sum rest+2)
      val frame_work = sum parent_paths + sum child_paths + 4
      (* Both original guard calls retain epoch checks and frame checks;
         between them every actual variable visibility path is validated. *)
      val work = 2*(frame_work+6) +
        G.binding_scope_path_work visible + variable_sum paths + 8
      val _ = R.scope_meter_charge meter 16
    in BindingGuard {meter=meter,graph=graph,parent_scope=parent_scope,
      scope=scope,parent_active=parent_active,child_active=child_active,
      parent_paths=parent_paths,child_paths=child_paths,visible=visible,
      variables=paths,epoch=epoch,symbols=symbols,work=work,
      data={scope=scope,variables=variables,descriptors=descriptors,
        binders=binders}} end
  fun validate_binding_guard graph caller
      (BindingGuard {graph=held,parent_scope,scope,parent_active,child_active,
        parent_paths,child_paths,visible,variables,epoch,symbols,...}) =
    let
      val _ = if Portable.pointer_eq (graph,held) andalso
          caller = parent_scope then () else
        raise ERR "binding_guard" "different graph or genuine parent"
      fun paths [] = ()
        | paths ((scope,path)::rest) =
            (G.validate_scope_path graph scope path;paths rest)
      fun guard () =
        (if Type.type_epoch () = epoch andalso Term.term_epoch () = symbols
           then () else raise ERR "binding_guard" "origin epoch changed";
         if !parent_active then () else
           raise ERR "binding_guard" "private parent lexical frame closed";
         paths parent_paths;
         if !child_active then () else
           raise ERR "binding_guard" "private child lexical frame closed";
         paths child_paths)
      val _ = guard ()
      val _ = G.validate_binding_scope_path graph scope parent_scope visible
      val _ = List.app (fn (required,path) =>
        G.validate_binding_scope_path graph scope required path) variables
      val _ = guard ()
    in () end

  fun open_mixed_bindings (backend as Backend
      {owner, mk_bound_var, new_let_scope, close_scope, let_binding, ...})
      parent entries blocked_keys =
    let
      val _ = unique_keys entries
      val (environment, dictionary) = checked_frame backend parent
      val blocked = mixed_blockers parent entries blocked_keys
      val bindings = List.map (fn (key, name, value) =>
        let val variable = mk_bound_var (name, type_of backend value)
        in (key, variable, let_binding (variable, value)) end) entries
      val environment = new_let_scope environment
        (List.map (fn (_, term, value) => (term, value)) bindings)
      val dictionary = List.foldl (fn ((key, _, value), dictionary) =>
        Redblackmap.insert (dictionary, key, value)) dictionary bindings
      val active = ref true
      val frame = Frame {owner = owner, active = active,
                         environment = environment, bindings = dictionary,
                         blocked = blocked,
                         identities = frame_identities parent}
      fun close () = if not (!active) then () else
        (active := false; close_scope environment)
      val origin = (case backend of Backend {graph = NONE,...} => NONE
        | _ => opened_origin backend parent frame []
            (ListPair.map (fn ((key,name,_),(_,variable,_)) =>
              (key,name,Term.type_of variable)) (entries,bindings))
            false)
        handle primary => ((close () handle _ => ());raise primary)
    in {frame = frame, scope = frame_scope backend frame, close = close,
      origin = origin} end

  fun open_bindings backend parent entries =
    open_mixed_bindings backend parent entries []

  fun open_binders (backend as Backend
      {owner, mk_bound_var, bound_variable, new_scope, new_let_scope,
       close_scope, ...}) parent descriptors =
    let
      val environments = ref ([] : environment list)
      val closed = ref false
      val (initial, dictionary) = checked_frame backend parent
      fun close_environments () = List.app close_scope (!environments)
      fun bind [] environment dictionary variables =
            (environment, dictionary, List.rev variables)
        | bind ((key, name, ty) :: rest) environment dictionary variables =
            let
              val lexical = mk_bound_var (name, ty)
              val binder_frame = new_scope environment []
              val _ = environments := binder_frame :: !environments
              val variable = bound_variable binder_frame lexical
              val body_environment = new_let_scope
                binder_frame [(lexical, variable)]
              val _ = environments := body_environment :: !environments
            in bind rest body_environment
              (Redblackmap.insert (dictionary, key, variable))
              (variable :: variables) end
      val (environment, dictionary, variables) =
        bind descriptors initial dictionary []
        handle error =>
          ((close_environments () handle _ => ()); raise error)
      val active = ref true
      val frame = Frame {owner = owner, active = active,
                         environment = environment, bindings = dictionary,
                         blocked = shadow_blockers parent descriptors,
                         identities = frame_identities parent}
      fun close () = if !closed then () else
        (closed := true; active := false; close_environments ())
      val origin = opened_origin backend parent frame variables descriptors true
        handle primary => ((close () handle _ => ());raise primary)
    in {frame = frame, variables = variables,
        scope = frame_scope backend frame, close = close,origin = origin} end

  datatype syntax = Hole of int | Constant of Term.term
                  | BoundVariable of int
                  | Application of syntax * syntax
                  | Abstraction of Term.term * syntax
  datatype recipe = Recipe of
    {syntax : syntax, holes : Type.hol_type vector,
     result : Type.hol_type, size : int}

  fun recipe_type (Recipe {result, ...}) = result
  fun recipe_size (Recipe {size, ...}) = size

  fun compile_recipe {template, holes, template_limit} =
    let
      val size = case SmtReplayImport.bounded_raw_size template_limit
          template of SOME size => size
        | NONE => raise ERR "compile_recipe" "expanded operator template"
      val _ = List.app (fn hole => if Term.is_var hole then () else
        raise ERR "compile_recipe" "operand hole is not a typed variable")
        holes
      val _ = List.foldl (fn (hole, previous) =>
        if List.exists (Term.aconv hole) previous then
          raise ERR "compile_recipe" "duplicate typed operand hole"
        else hole :: previous) [] holes
      fun index variable terms =
        let fun seek [] _ = NONE
              | seek (term :: rest) i =
                  if Term.aconv variable term then SOME i else seek rest (i+1)
        in seek terms 0 end
      fun compile binders term =
        if Term.is_var term then
          (case index term binders of
             SOME i => BoundVariable i
           | NONE => case index term holes of
               SOME i => if List.null binders then Hole i else
                 raise ERR "compile_recipe" "operand insertion below binder"
             | NONE => raise ERR "compile_recipe" "unowned schema variable")
        else if Term.is_const term then Constant term
        else if Term.is_comb term then
          let val (operator, operand) = Term.dest_comb term in
            Application (compile binders operator, compile binders operand)
          end
        else
          let val (binder, body) = Term.dest_abs term in
            Abstraction (binder, compile (binder :: binders) body)
          end
    in Recipe {syntax = compile [] template,
      holes = Vector.fromList (List.map Term.type_of holes),
      result = Term.type_of template, size = size} end

  fun construct_with_branches backend frame
      (Recipe {syntax, holes, result, ...}) arguments =
    let
      val _ = ignore (checked_frame backend frame)
      val values = Vector.fromList arguments
      val _ = if Vector.length holes = Vector.length values then () else
        raise ERR "construct" "operator recipe arity mismatch"
      val _ = Vector.appi (fn (index, expected) =>
        if Type.compare (expected, type_of backend
            (Vector.sub (values, index))) = EQUAL then ()
        else raise ERR "construct" "operator recipe operand type mismatch")
        holes
      val branches = ref []
      fun build frame bound (Hole index) = Vector.sub (values, index)
        | build frame bound (Constant term) = literal backend frame term
        | build frame bound (BoundVariable index) = List.nth (bound, index)
        | build frame bound (Application (operator, operand)) =
            application backend frame
              (build frame bound operator, build frame bound operand)
        | build frame bound (Abstraction (binder, body)) =
            let
              val (name, ty) = Term.dest_var binder
              val branch = abstraction backend frame
                (name, name, ty) (fn child =>
                  let val value = valOf (lookup backend child name) in
                    build child (value :: bound) body
                  end)
              val _ = branches := branch :: !branches
            in branch end
      val value = build frame [] syntax
      val _ = if Type.compare (type_of backend value, result) = EQUAL then ()
        else raise ERR "construct" "operator recipe result type mismatch"
    in {value = value, branches = List.rev (!branches)} end

  fun construct backend frame recipe arguments =
    #value (construct_with_branches backend frame recipe arguments)
  fun prepare_binding_guard_policy graph caller
      (BindingOrigin {backend=Backend {owner,graph=original,...},
        parent,child,graph=held,parent_scope,scope,variables,descriptors,
        binders,epoch,symbols}) meter =
    let
      val _ = R.scope_meter_charge meter 8
      val _ = if Portable.pointer_eq (graph,held) andalso
          caller = parent_scope then () else
        raise ERR "binding_guard" "different graph or genuine parent"
      val _ = case original of SOME actual =>
          if Portable.pointer_eq (actual,graph) then () else
            raise ERR "binding_guard" "different private backend graph"
        | NONE => raise ERR "binding_guard" "ordinary backend has no origin"
      fun frame (Frame {owner=actual,active,environment,...}) expected =
        let
          val _ = R.scope_meter_charge meter 7
          val _ = if actual = owner then () else
            raise ERR "binding_guard" "different private lexical owner"
          val (lexical,construction) = case environment of
              SOME {lexical,construction} => (lexical,construction)
            | NONE => raise ERR "binding_guard" "no graph environment"
          val _ = R.scope_meter_charge meter 3
          val _ = if construction = expected then () else
            raise ERR "binding_guard" "actual lexical frame differs"
          fun path scope =
            let val (program,_) =
                  G.prepare_shared_scope_path_policy graph scope meter
                val _ = R.scope_meter_charge meter 2
            in (scope,program) end
          val lexical_path = path lexical
          val construction_path = path construction
          val _ = R.scope_meter_charge meter 3
        in (active,[lexical_path,construction_path]) end
      val (parent_active,parent_paths) = frame parent parent_scope
      val (child_active,child_paths) = frame child scope
      val visible = G.prepare_binding_scope_path_policy graph scope
        parent_scope meter
      fun node_paths [] = (R.scope_meter_charge meter 1;[])
        | node_paths (node::rest) =
          let
            val _ = R.scope_meter_charge meter 2
            val required = G.binding_node_scope graph node meter
            val program = G.prepare_binding_scope_path_policy graph scope required
              meter
            val tail = node_paths rest
            val _ = R.scope_meter_charge meter 2
          in (required,program)::tail end
      val paths = node_paths variables
      fun sum [] = (R.scope_meter_charge meter 1;1:IntInf.int)
        | sum ((_,path)::rest) =
            (R.scope_meter_charge meter 3;
             G.scope_path_validation_work path+sum rest+2)
      fun variable_sum [] = (R.scope_meter_charge meter 1;1:IntInf.int)
        | variable_sum ((_,path)::rest) =
            (R.scope_meter_charge meter 3;
             G.binding_scope_path_work path+variable_sum rest+2)
      val frame_work = sum parent_paths + sum child_paths + 4
      (* Both original guard calls retain epoch checks and frame checks;
         between them every actual variable visibility path is validated. *)
      val work = 2*(frame_work+6) +
        G.binding_scope_path_work visible + variable_sum paths + 8
      val _ = R.scope_meter_charge meter 16
    in BindingGuard {meter=meter,graph=graph,parent_scope=parent_scope,
      scope=scope,parent_active=parent_active,child_active=child_active,
      parent_paths=parent_paths,child_paths=child_paths,visible=visible,
      variables=paths,epoch=epoch,symbols=symbols,work=work,
      data={scope=scope,variables=variables,descriptors=descriptors,
        binders=binders}} end

  (* Additive exact recipe; original recipe representation stays literal. *)
  datatype policy_recipe = FinitePolicyRecipe of recipe
    | ExactPolicyRecipe of
        {syntax : syntax,holes : Type.hol_type vector,
         result : Type.hol_type,size : IntInf.int}
  fun recipe_policy_int_limit SmtReplayResourcePolicy.Uncapped = NONE
    | recipe_policy_int_limit (SmtReplayResourcePolicy.AtMost limit) =
        (SOME (IntInf.toInt limit) handle Overflow => NONE)
  fun recipe_type_with_policy (FinitePolicyRecipe recipe) =
        recipe_type recipe
    | recipe_type_with_policy (ExactPolicyRecipe {result,...}) = result
  fun recipe_size_with_policy (FinitePolicyRecipe recipe) =
        IntInf.fromInt (recipe_size recipe)
    | recipe_size_with_policy (ExactPolicyRecipe {size,...}) = size
  fun compile_exact_policy_recipe {template, holes, template_limit} =
    let
      val size = case SmtReplayImport.raw_size_with_policy template_limit
          template of SOME size => size
        | NONE => raise ERR "compile_recipe" "expanded operator template"
      val _ = List.app (fn hole => if Term.is_var hole then () else
        raise ERR "compile_recipe" "operand hole is not a typed variable")
        holes
      val _ = List.foldl (fn (hole, previous) =>
        if List.exists (Term.aconv hole) previous then
          raise ERR "compile_recipe" "duplicate typed operand hole"
        else hole :: previous) [] holes
      fun index variable terms =
        let fun seek [] _ = NONE
              | seek (term :: rest) i =
                  if Term.aconv variable term then SOME i else seek rest (i+1)
        in seek terms 0 end
      fun compile binders term =
        if Term.is_var term then
          (case index term binders of
             SOME i => BoundVariable i
           | NONE => case index term holes of
               SOME i => if List.null binders then Hole i else
                 raise ERR "compile_recipe" "operand insertion below binder"
             | NONE => raise ERR "compile_recipe" "unowned schema variable")
        else if Term.is_const term then Constant term
        else if Term.is_comb term then
          let val (operator, operand) = Term.dest_comb term in
            Application (compile binders operator, compile binders operand)
          end
        else
          let val (binder, body) = Term.dest_abs term in
            Abstraction (binder, compile (binder :: binders) body)
          end
    in ExactPolicyRecipe {syntax = compile [] template,
      holes = Vector.fromList (List.map Term.type_of holes),
      result = Term.type_of template, size = size} end

  fun compile_recipe_with_policy
      (request as {template,holes,template_limit}) =
    case recipe_policy_int_limit template_limit of
        SOME finite => FinitePolicyRecipe (compile_recipe
          {template=template,holes=holes,template_limit=finite})
      | NONE => compile_exact_policy_recipe request
  fun construct_with_branches_with_policy backend frame
      (FinitePolicyRecipe recipe) arguments =
        construct_with_branches backend frame recipe arguments
    | construct_with_branches_with_policy backend frame
        (ExactPolicyRecipe {syntax, holes, result, ...}) arguments =
    let
      val _ = ignore (checked_frame backend frame)
      val values = Vector.fromList arguments
      val _ = if Vector.length holes = Vector.length values then () else
        raise ERR "construct" "operator recipe arity mismatch"
      val _ = Vector.appi (fn (index, expected) =>
        if Type.compare (expected, type_of backend
            (Vector.sub (values, index))) = EQUAL then ()
        else raise ERR "construct" "operator recipe operand type mismatch")
        holes
      val branches = ref []
      fun build frame bound (Hole index) = Vector.sub (values, index)
        | build frame bound (Constant term) = literal backend frame term
        | build frame bound (BoundVariable index) = List.nth (bound, index)
        | build frame bound (Application (operator, operand)) =
            application backend frame
              (build frame bound operator, build frame bound operand)
        | build frame bound (Abstraction (binder, body)) =
            let
              val (name, ty) = Term.dest_var binder
              val branch = abstraction backend frame
                (name, name, ty) (fn child =>
                  let val value = valOf (lookup backend child name) in
                    build child (value :: bound) body
                  end)
              val _ = branches := branch :: !branches
            in branch end
      val value = build frame [] syntax
      val _ = if Type.compare (type_of backend value, result) = EQUAL then ()
        else raise ERR "construct" "operator recipe result type mismatch"
    in {value = value, branches = List.rev (!branches)} end

  fun construct_with_policy backend frame recipe arguments =
    #value (construct_with_branches_with_policy backend frame recipe arguments)

  fun exact_graphs_with_policy {graph, scope, import_limit, literal_limit, binder_limit} =
    let
      val _ = G.validate_scope graph scope
      val _ = if SmtReplayResourcePolicy.positive import_limit andalso
          SmtReplayResourcePolicy.positive literal_limit andalso
          SmtReplayResourcePolicy.positive binder_limit then ()
        else raise ERR "graphs" "nonpositive public import contract"
      fun scopes (SOME scopes) = scopes
        | scopes NONE = raise ERR "graphs" "missing graph environment"
      fun lexical environment = #lexical (scopes environment)
      fun construction environment = #construction (scopes environment)
      val lexical_descriptors = ref
        (Redblackmap.mkDict Int.compare : (int, Term.term) Redblackmap.dict)
      fun retain_variable term node =
        (lexical_descriptors := Redblackmap.insert
           (!lexical_descriptors, G.node_id node, term); node)
      fun compare_private ((left_scope, left_term),
                           (right_scope, right_term)) =
        case Int.compare (left_scope, right_scope) of
          EQUAL => Term.compare (left_term, right_term) | order => order
      val private_variables = ref (Redblackmap.mkDict compare_private)
      val solver_variables = ref ([] : G.node solver_variable list)
      val recorded_variables = ref (HOLset.empty Int.compare)
      fun record_flexible term node =
        (if HOLset.member (!recorded_variables, G.node_id node) then () else
           (recorded_variables := HOLset.add
              (!recorded_variables, G.node_id node);
            solver_variables :=
              {node = node, lexical = term,
               scope = SOME (G.node_scope graph node)} :: !solver_variables);
         node)
      fun fresh_flexible environment term =
        record_flexible term (retain_variable term
          (G.fresh_flexible_variable graph (construction environment) term))
      fun flexible environment term =
        let
          val scope = construction environment
          val key = (G.scope_id scope, term)
          val default = case Redblackmap.peek (!private_variables, key) of
              SOME node => node
            | NONE =>
                let val node = retain_variable term
                      (G.fresh_flexible_variable graph scope term)
                in private_variables := Redblackmap.insert
                     (!private_variables, key, node); node end
          val node = G.resolve_reference graph
            (lexical environment) term default
          val _ = case G.view graph node of
              G.Variable (G.SolverFlexible, _) =>
                ignore (record_flexible term node)
            | _ => ()
        in node end
      fun import environment term =
        #node (G.import_with_policy graph (construction environment) import_limit term)
      fun source _ term =
        let val node = #node (G.import_with_policy graph scope import_limit term)
        in if Term.is_var term then retain_variable term node else node end
      fun literal environment term =
        let
          val _ = case SmtReplayImport.raw_size_with_policy literal_limit term of
              SOME _ => ()
            | NONE => raise ERR "literal" "literal exceeds bounded contract"
          val _ = if List.null (Term.free_vars term) then () else
            raise ERR "literal" "literal contains an unowned free variable"
        in if Term.is_const term then
          G.constant graph (construction environment) term
        else import environment term end
    in Backend
      {owner = ref (), graph = SOME graph,
       initial = SOME {lexical = scope, construction = scope},
       validate_environment = fn environment =>
         (G.validate_scope graph (lexical environment);
          G.validate_scope graph (construction environment)),
       type_of = G.type_of graph, view = fn _ => graph_view graph,
       same_value = op=,
       variable_descriptor = fn node =>
         (ignore (G.type_of graph node);
          Redblackmap.peek (!lexical_descriptors, G.node_id node)),
       solver_variables = fn () => List.rev (!solver_variables),
       mk_bound_var = Term.mk_var, source = source, literal = literal,
       fresh_solver_variable = fresh_flexible,
       variable = fn environment => fn kind => fn term =>
         case kind of G.RigidSource =>
           G.resolve_variable graph (lexical environment) term
         | G.SolverFlexible => flexible environment term
         | _ => G.variable graph (construction environment) kind term,
       reference = fn environment => fn (term, value) =>
         G.resolve_reference graph (lexical environment) term value,
       capture_alias = fn environment => graph_capture_alias graph
         (graph_lexical_alias graph private_variables lexical_descriptors)
         binder_limit literal_limit
         (lexical environment) (construction environment),
       private_variable = fn node =>
         (case G.view graph node of G.Variable (G.SolverFlexible,_) =>
            not (Option.isSome (graph_lexical_alias graph
              private_variables lexical_descriptors node))
          | _ => false),
       bound_variable = fn environment => fn term => retain_variable term
         (G.fresh_bound_variable graph (construction environment) term),
       application = fn environment =>
         G.application graph (construction environment),
       new_scope = fn environment => fn bindings =>
         let val scope = G.new_scope graph (lexical environment) bindings
         in SOME {lexical = scope, construction = scope} end,
       (* Let aliases affect name resolution, while constructed values
          retain the enclosing proof block's construction scope. *)
       new_let_scope = fn environment => fn bindings =>
         SOME {lexical = G.new_scope graph (lexical environment) bindings,
               construction = construction environment},
       close_scope = fn environment => G.close_scope graph
         (lexical environment),
       constructor_state = new_constructor_state (),
       syntax_spend = fn _ => (),
       source_syntax = fn _ => graph_source_syntax graph
         (fn node => Redblackmap.peek (!lexical_descriptors,G.node_id node)),
       abstraction = fn environment => fn body_environment =>
         fn (binder,body) =>
           G.recorded_abstraction_with_policy graph (construction environment)
             binder_limit
             {binder = binder,body = body,
              body_frame = construction body_environment},
       index_callbacks = new_index_callbacks (),
       failure_requires_propagation = fn () => false,
       new_abstraction_scope = fn environment =>
         let val retained = G.new_construction_scope graph
               {lexical = lexical environment,
                construction = construction environment}
             val lexical = G.new_scope graph retained []
               handle primary =>
                 ((G.close_scope graph retained handle _ => ());raise primary)
         in SOME {lexical = lexical,construction = retained} end,
       abort_abstraction_scope = fn environment =>
         G.close_scope graph (construction environment),
       let_binding = #2, finish_let = #2}
    end

  fun graphs_with_policy
      (request as {graph,scope,import_limit,literal_limit,binder_limit}) =
    case (recipe_policy_int_limit import_limit,
          recipe_policy_int_limit literal_limit,
          recipe_policy_int_limit binder_limit) of
        (SOME imports,SOME literals,SOME binders) => graphs
          {graph=graph,scope=scope,import_limit=imports,
           literal_limit=literals,binder_limit=binders}
      | _ => exact_graphs_with_policy request

  datatype value_factory_token = ValueFactoryToken of
    {backend:PV.value backend,context:PV.context}
  type value_backend =
    {backend:PV.value backend,context:PV.context,
     factory_token:value_factory_token,
     binding_origin_data:G.scope -> PV.value binding_origin ->
       {scope:G.scope,variables:PV.value list,
        descriptors:(string * string * Type.hol_type) list,binders:bool},
     close:unit -> unit}
  fun values_with_policy
      {context,graph,scope,import_limit,literal_limit,binder_limit}
      : value_backend =
    let
      val _ = if List.all SmtReplayResourcePolicy.positive
          [import_limit,literal_limit,binder_limit] then () else
        raise ERR "values" "nonpositive public import contract"
      val _ = PV.validate_for context graph scope
      val owner = ref ()
      val index_callbacks = new_index_callbacks ()
      fun step () = PV.spend context 1
      fun protect action = PV.protect context action
      fun scopes (SOME fields) = fields
        | scopes NONE = raise ERR "values" "missing value environment"
      fun lexical environment = #lexical (scopes environment)
      fun construction environment = #construction (scopes environment)
      val descriptors = ref (Redblackmap.mkDict Int.compare)
      fun proof_compare ((lk,li),(rk,ri)) =
        (step ();
         case Int.compare (lk,rk) of EQUAL => Int.compare (li,ri)
           | order => order)
      val proof_descriptors = ref (Redblackmap.mkDict proof_compare)
      fun retain lexical value = protect (fn () =>
        (descriptors := Redblackmap.insert
           (!descriptors,PV.key context value,lexical);
         step ();
         proof_descriptors := Redblackmap.insert
           (!proof_descriptors,
            PV.proof_key context (PV.proof_term context value),lexical);
         value))
      fun descriptor value =
        case Redblackmap.peek (!descriptors,PV.key context value) of
          SOME term => SOME term
        | NONE => (case PV.view context value of
            PV.Variable (_,term) => SOME term | _ => NONE)
      val variables = ref ([] : PV.value solver_variable list)
      val recorded = ref (Redblackset.empty Int.compare)
      fun record lexical value =
        let val id = PV.key context value in
          if Redblackset.member (!recorded,id) then () else
            (recorded := Redblackset.add (!recorded,id);
             variables := {node=value,lexical=lexical,
               scope=SOME (PV.scope_of context value)} :: !variables);
          retain lexical value
        end
      fun private_compare ((ls,lt),(rs,rt)) =
        case Int.compare (ls,rs) of EQUAL => Term.compare (lt,rt)
          | result => result
      val private_variables = ref (Redblackmap.mkDict private_compare)
      fun fresh environment term = record term
        (PV.fresh_flexible context (construction environment) term)
      fun flexible environment term =
        let val index = (G.scope_id (construction environment),term)
            val fallback = case Redblackmap.peek (!private_variables,index) of
                SOME value => value
              | NONE => let val value = fresh environment term
                            val _ = private_variables := Redblackmap.insert
                              (!private_variables,index,value)
                        in value end
            val value = PV.reference context (lexical environment)
              (term,fallback)
        in case PV.view context value of PV.Variable (G.SolverFlexible,_) =>
            record term value | _ => value end
      fun regular value =
        case descriptor value of NONE => NONE
        | SOME term =>
            (case Redblackmap.peek (!private_variables,
                (G.scope_id (PV.scope_of context value),term)) of
               SOME original => if PV.key context original=
                   PV.key context value then SOME term else NONE
             | NONE => NONE)
      fun capture environment identities (root,blocks) =
        capture_blocks (scoped_alias
        {spend=PV.spend context,key=PV.key context,
         free=fn value => SOME (PV.free_variables context value),
         resolve=fn value =>
           case List.find (fn (old,_) =>
               (step ();PV.key context old=PV.key context value)) identities of
             SOME (_,bound) => bound
           | NONE => case regular value of NONE => value
             | SOME term => PV.reference context (lexical environment)
                 (term,value),
         visible=fn scope => fn value =>
           G.scope_visible graph scope (PV.scope_of context value),
         atom=fn scope => fn value =>
           if G.scope_visible graph scope (PV.scope_of context value) then
             value
           else case PV.view context value of
               PV.Constant term => PV.literal context scope literal_limit term
             | _ => case PV.proof_graph_reference context
                   (PV.proof_term context value) of
                 SOME {graph,node,...} =>
                   (case G.source_anchor graph node of
                      SOME {original,...} =>
                        PV.import context scope literal_limit original
                    | NONE => value)
               | NONE => value,
         view=fn value => case PV.constructor_view context value of
             PV.Application pair => AliasApplication pair
           | PV.Abstraction {binder,body,...} => AliasBinder (binder,body)
           | _ => AliasAtom,
         apply=PV.application context,
         abstract=fn parent => fn old => fn body =>
           let val child = PV.new_construction_scope context
                 {lexical=lexical environment,construction=parent}
               fun build () =
                 let val variable = case descriptor old of
                         SOME variable => variable
                       | NONE => Term.mk_var ("cpc_alias_binder",
                           PV.type_of context old)
                     val binder = retain variable
                       (PV.fresh_bound context child variable)
                 in PV.abstraction context parent
                   {binder=binder,body=body child binder,body_frame=child} end
           in build () handle primary =>
             ((PV.close_scope context child handle _ => ());raise primary)
           end}
        (construction environment) root) blocks
      val backend = Backend
        {owner=owner,graph=SOME graph,index_callbacks=index_callbacks,
         constructor_state=new_constructor_state (),
         syntax_spend=PV.spend context,
         source_syntax=fn _ => value_source_syntax context
           (fn key => (step ();Redblackmap.peek (!proof_descriptors,key))),
         initial=SOME {lexical=scope,construction=scope},
         failure_requires_propagation=fn () =>
           PV.failure_requires_propagation context,
         validate_environment=fn environment =>
           (PV.spend context 0;
            G.validate_scope graph (lexical environment);
            G.validate_scope graph (construction environment)),
         type_of=PV.type_of context,
         view=fn environment => fn value =>
           (case PV.constructor_view context value of
              PV.Variable (_,term) => Atom term
            | PV.Constant term => Atom term
            | PV.Application pair => Apply pair
            | _ => Opaque),
         same_value=fn (left,right) =>
           PV.proof_key context (PV.proof_term context left) =
           PV.proof_key context (PV.proof_term context right),
         variable_descriptor=descriptor,
         private_variable=fn value =>
           (case PV.view context value of
              PV.Variable (G.SolverFlexible,_) =>
                not (Option.isSome (regular value))
            | _ => false),
         solver_variables=fn () =>
           (PV.spend context 1;List.rev (!variables)),
         mk_bound_var=fn pair => (step ();Term.mk_var pair),
         source=fn _ => PV.import context scope import_limit,
         literal=fn environment =>
           PV.literal context (construction environment) literal_limit,
         variable=fn environment => fn kind => fn term =>
           (case kind of G.RigidSource =>
              (step ();PV.resolve_variable context
                (lexical environment) term)
            | G.SolverFlexible => flexible environment term
            | _ => retain term
                (PV.variable context (construction environment) kind term)),
         fresh_solver_variable=fresh,
         reference=fn environment => PV.reference context
           (lexical environment),
         capture_alias=capture,
         bound_variable=fn environment => fn term => retain term
           (PV.fresh_bound context (construction environment) term),
         application=fn environment => fn operands =>
           if !(#depth index_callbacks)=0 then
             PV.application context (construction environment) operands
           else (PV.index_application context (construction environment)
             operands handle PV.IndexApplicationTypeError error => raise error),
         new_scope=fn environment => fn bindings =>
           let val child = PV.new_scope context (lexical environment) bindings
           in SOME {lexical=child,construction=child} end,
         new_let_scope=fn environment => fn bindings =>
           SOME {lexical=PV.new_scope context (lexical environment) bindings,
             construction=construction environment},
         close_scope=fn environment =>
           PV.close_scope context (lexical environment),
         abstraction=fn environment => fn body_environment =>
           fn (binder,body) =>
             PV.abstraction context (construction environment)
               {binder=binder,body=body,
                body_frame=construction body_environment},
         new_abstraction_scope=fn environment =>
           let val retained = PV.new_construction_scope context
                 {lexical=lexical environment,
                  construction=construction environment}
               val child = PV.new_scope context retained []
           in SOME {lexical=child,construction=retained} end,
         abort_abstraction_scope=fn environment =>
           PV.close_scope context (construction environment),
         let_binding= #2,finish_let= #2}
      fun origin_data parent_scope (BindingOrigin
          {backend=Backend {owner=held,...},parent,child,graph=held_graph,
           parent_scope=original,scope=child_scope,variables,descriptors,
           binders,epoch,symbols}) = protect (fn () =>
        let val _ = PV.validate context
            val _ = if Portable.pointer_eq (owner,held) andalso
                Portable.pointer_eq (graph,held_graph) andalso
                parent_scope=original then () else
              raise ERR "binding_origin" "different value backend or parent"
            val _ = if Type.type_epoch ()=epoch andalso
                Term.term_epoch ()=symbols then () else
              raise ERR "binding_origin" "origin retirement epoch changed"
            val _ = if frame_scope backend parent=SOME original andalso
                frame_scope backend child=SOME child_scope then () else
              raise ERR "binding_origin" "actual lexical frame changed"
            val _ = List.app (PV.usable context child_scope) variables
        in {scope=child_scope,variables=variables,descriptors=descriptors,
          binders=binders} end)
    in {backend=backend,context=context,
      factory_token=ValueFactoryToken {backend=backend,context=context},
      binding_origin_data=origin_data,
      close=fn () => PV.close context} end

  datatype value_binding_guard = ValueBindingGuard of
    {graph:G.graph,parent_scope:G.scope,parent_active:bool ref,
     child_active:bool ref,epoch:int,symbols:int,
     lifetime:PV.lifetime_guard,work:IntInf.int,
     data:{scope:G.scope,variables:PV.value list,
       descriptors:(string * string * Type.hol_type) list,binders:bool}}
  fun value_binding_origin_owner
      (BindingOrigin {graph,parent_scope,scope,...}:PV.value binding_origin) =
    {graph=graph,parent_scope=parent_scope,scope=scope}
  fun prepare_value_binding_guard (factory:value_backend) graph caller
      (origin as BindingOrigin
        {backend=held,parent=Frame {active=parent_active,...},
         child=Frame {active=child_active,...},graph=owner,parent_scope,
         scope=child_scope,variables,descriptors,binders,
         epoch,symbols}) {root_scope,remaining_work} =
    let
      val context = #context factory
      val backend = #backend factory
      val ValueFactoryToken {backend=actual,context=actual_context} =
        #factory_token factory
      val _ = if Portable.pointer_eq (backend,actual) andalso
          Portable.pointer_eq (context,actual_context) then () else
        raise ERR "value_binding_guard" "Value factory fields changed"
      val _ = if Portable.pointer_eq (#backend factory,held) andalso
          Portable.pointer_eq (graph,owner) andalso caller=parent_scope
        then () else raise ERR "value_binding_guard"
          "different genuine Value backend or parent"
      val _ = PV.validate_for context graph root_scope
      val _ = if Type.type_epoch ()=epoch andalso
          Term.term_epoch ()=symbols then () else
        raise ERR "value_binding_guard" "origin declaration lifetime changed"
      val BindingOrigin {parent,child,...} = origin
      val _ = if frame_scope backend parent=SOME caller andalso
          frame_scope backend child=SOME child_scope then () else
        raise ERR "value_binding_guard" "actual lexical frame changed"
      val _ = List.app (PV.usable context child_scope) variables
      val data = {scope=child_scope,variables=variables,
        descriptors=descriptors,binders=binders}
      fun frame (Frame {environment,...}) = case environment of
          SOME {lexical,construction} => [lexical,construction]
        | NONE => raise ERR "value_binding_guard" "missing Value environment"
      val lifetime = PV.prepare_lifetime_guard context
        {remaining_work=remaining_work,scopes=frame parent @ frame child,
         values= #variables data}
      val _ = PV.spend context 12
    in ValueBindingGuard {graph=graph,parent_scope=caller,
      parent_active=parent_active,child_active=child_active,
      epoch=epoch,symbols=symbols,lifetime=lifetime,
      work=PV.lifetime_guard_work lifetime+12,data=data} end
  fun value_binding_guard_work (ValueBindingGuard {work,...}) = work
  fun value_binding_guard_data (ValueBindingGuard {data,...}) = data
  (* Metadata-only port. In particular, do not enter the lifetime program
     (or claim its leaf/path checks) on this shallow path. *)
  fun validate_value_binding_header graph caller
      (ValueBindingGuard {graph=held,parent_scope,parent_active,
                         child_active,epoch,symbols,...}) =
    (if Portable.pointer_eq (graph,held) andalso caller=parent_scope then ()
     else raise ERR "value_binding_guard" "different graph or parent";
     if Type.type_epoch ()=epoch andalso Term.term_epoch ()=symbols then ()
     else raise ERR "value_binding_guard"
       "origin declaration lifetime changed";
     if !parent_active andalso !child_active then () else
       raise ERR "value_binding_guard" "actual Value lexical frame closed")
  fun validate_value_binding_guard graph caller
      (ValueBindingGuard {graph=held,parent_scope,parent_active,
                         child_active,epoch,symbols,lifetime,...}) =
    (if Portable.pointer_eq (graph,held) andalso caller=parent_scope then ()
     else raise ERR "value_binding_guard" "different graph or parent";
     if Type.type_epoch ()=epoch andalso Term.term_epoch ()=symbols then ()
     else raise ERR "value_binding_guard"
       "origin declaration lifetime changed";
     if !parent_active andalso !child_active then () else
       raise ERR "value_binding_guard" "actual Value lexical frame closed";
     PV.validate_lifetime_guard lifetime;
     if !parent_active andalso !child_active then () else
       raise ERR "value_binding_guard" "actual Value lexical frame closed")
end
