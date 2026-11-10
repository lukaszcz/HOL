(* Copyright (c) 2026 The HOL4 contributors. *)
structure SmtLib_GraphFrontend =
struct
  open SmtReplayGraph SmtLib_GraphBackend SmtLib_GraphTheories SmtLib_Parser
  structure G = SmtReplayGraph
  structure B = SmtLib_GraphBackend
  structure R = SmtLib_GraphTheories
  structure P = SmtLib_Parser
  structure PV = SmtLib_GraphParserValue
  structure M = SmtLib_GraphParserMapping
  val ERR = Feedback.mk_HOL_ERR "SmtLib_GraphFrontend"
  (* Inspect retained lexical metadata only; generated private markers and
     compound operands are not variable binders. *)
  fun binder_variable backend key node =
    case B.variable_descriptor backend node of
      SOME variable =>
        let val (name, ty) = Term.dest_var variable
        in (key, name, ty) end
    | NONE => raise (Feedback.mk_HOL_ERR "SmtLib_Parser"
        "parse_binder_term"
        "CPC @list binder contains a non-variable term")

  fun binder_list backend descriptors values =
    case values of
      NONE => List.map (fn descriptor => (descriptor,NONE)) descriptors
    | SOME values => ListPair.map
        (fn (descriptor,value) =>
          let val (_,identity) = B.binder_reference backend
                (#1 descriptor) value
          in (descriptor,identity) end) (descriptors,values)

  (* A retained non-variable list is distinct from an unknown alias. Keep
     its operand identities available without expanding the shared terms;
     the parser decides when invalid operands must be rejected. *)
  fun binder_list_lookup backend descriptors values =
    case descriptors of
      SOME descriptors =>
        SOME (List.map SOME (binder_list backend descriptors values))
    | NONE => Option.map (List.map (fn value =>
        case B.variable_descriptor backend value of
          NONE => NONE
        | SOME variable => SOME (B.binder_reference backend
            (#1 (Term.dest_var variable)) value))) values

  (* Native private FP abbreviations retain their operand OUTSIDE the
     surrounding term binder. Snapshot that lexical source at the proof
     root, rather than moving a child-owned semantic value across a guard.
     Construction is typed/nodewise; private leaves resolve only through
     the authentic private allocation inventory, never ordinary solver
     variables with equal lexical descriptors. Relevant lexical environments
     keep shared suffixes shared even below unrelated source binders. *)
  fun detached_private_source backend private_allocations syntax =
    let
      val root = B.root backend
      val spend = B.syntax_spend backend
      fun compare ((li,le),(ri,re)) =
        (spend 1;case IntInf.compare (li,ri) of EQUAL =>
           Lib.list_compare Int.compare (le,re) | order => order)
      val memo = ref (Redblackmap.mkDict compare)
      val serial = ref 0
      fun private variable =
        case List.find (fn node =>
            (spend 1;case B.variable_descriptor backend node of
               SOME lexical => Term.compare (lexical,variable)=EQUAL
             | NONE => false)) private_allocations of
            SOME node => node
          | NONE => raise ERR "private_source" "unknown private allocation"
      fun walk frame environment syntax =
        let
          val free = if null environment then []
            else C.free_variables spend syntax
          val relevant = List.filter (fn (variable,_,_,_) =>
            List.exists (fn current => Term.compare (variable,current)=EQUAL)
              free) environment
          val frame = case relevant of [] => root | (_,_,_,owner)::_ => owner
          val key = (C.identity syntax,List.map #3 relevant)
        in case Redblackmap.peek (!memo,key) of SOME value => value
         | NONE =>
          let
            val value = case C.view spend syntax of
                C.Variable variable =>
                  (case List.find (fn (bound,_,_,_) =>
                      Term.compare (bound,variable)=EQUAL) relevant of
                       SOME (_,value,_,_) => value
                     | NONE => B.source backend root variable)
              | C.Atom atom => if Term.is_var atom then private atom
                  else B.source backend root atom
              | C.Apply (f,x) => B.application backend frame
                  (walk frame relevant f,walk frame relevant x)
              | C.Abstract (variable,body) =>
                  let val (name,ty) = Term.dest_var variable
                  in B.abstraction backend frame (name,name,ty) (fn child =>
                    let
                      val value = valOf (B.lookup backend child name)
                      val id = !serial
                      val _ = serial := id+1
                      val outer = List.filter (fn (bound,_,_,_) =>
                        Term.compare (bound,variable)<>EQUAL) relevant
                    in walk child ((variable,value,id,child)::outer)
                      body end) end
            val _ = memo := Redblackmap.insert (!memo,key,value)
          in value end
        end
    in walk root [] syntax end

  datatype lexical_policy = CPC | Z3
  datatype source_arity = Exact of int | AtMost of int
  type source_declaration =
    {token : string, original : Term.term, arity : source_arity}
  (* Lexical declaration data supplied by the outbound serializer. These
     existing graph IDs grant neither new Sources nor proof assumptions. *)
  type graph_source_declaration =
    {token : string, node : G.node, arity : source_arity}
  type 'a constructed_solver_variable =
    {node : 'a, lexical : Term.term, scope : G.scope}
  type solver_variable = G.node constructed_solver_variable
  type 'a constructed_term =
    {node : 'a, scope : G.scope,
     source_syntax : C.syntax option,
     occurrence : 'a P.construction_occurrence,
     binder_blocks : (string * int * 'a) list}
  type term = G.node constructed_term
  fun capture_table (backend:'a B.backend) =
    ref (Redblackmap.mkDict
      (fn ((lk,li),(rk,ri)) =>
        (B.syntax_spend backend
           (1+IntInf.fromInt (String.size lk+String.size rk));
         case String.compare (lk,rk) of
           EQUAL => Int.compare (li,ri) | order => order))
      : (string * int,(string * int * 'a) list) Redblackmap.dict)
  (* Binder-block lookup records possible immediate sizes, not occurrence
     multiplicity. Keep the latter in the occurrence DAG. Repeated aliases
     of one binder must not double this lookup list at each definition. *)
  fun unique_blocks backend identity blocks =
    let
      fun compare ((lk,lc,li),(rk,rc,ri)) =
        (B.syntax_spend backend
           (1+IntInf.fromInt (String.size lk+String.size rk));
         case String.compare (lk,rk) of EQUAL =>
           (case Int.compare (lc,rc) of EQUAL => Int.compare (li,ri)
            | order => order) | order => order)
      fun add ((entry as (kind,count,node)),(seen,result)) =
        let val key = (kind,count,identity node)
        in if Redblackset.member (seen,key) then (seen,result)
           else (Redblackset.add (seen,key),entry::result) end
    in List.rev (#2 (List.foldl add
      (Redblackset.empty compare,[]) blocks)) end

  type 'rule step =
    {id : string, rule : 'rule, premises : string list,
     conclusion : term option, arguments : term list}
  type 'a constructed_ascription =
    {name : string, constructor : string option, sort : Type.hol_type,
     arguments : 'a list}
  type ascription = G.node constructed_ascription
  type options =
    {graph : G.graph, scope : G.scope, logic : string,
     sources : (string * Term.term) list,
     sorts : Type.hol_type P.dict,
     binder_lists : (string * (string * string * Type.hol_type) list) list,
     import_limit : int, literal_limit : int, binder_limit : int,
     recipe_limits : R.limits,
     special : G.node B.backend -> R.entry ->
       G.node P.construction_parse_fn option,
     ascribed : G.node B.backend -> G.node B.frame -> ascription ->
       G.node option}
  type 'a constructed_private_binding =
    {scope : G.scope, marker : 'a, kind : string,source : 'a option}
  type private_binding = G.node constructed_private_binding
  type 'a constructed_reader =
    {graph : G.graph, scope : G.scope, backend : 'a B.backend,
     solver : string, version : string, coverage : R.entry list,
     parse_next : unit -> 'a constructed_term,
     solver_variables : unit -> 'a constructed_solver_variable list,
     private_bindings : unit -> 'a constructed_private_binding list}
  type reader = G.node constructed_reader
  type configured_options =
    {base : options, source_declarations : source_declaration list}

  type namespace =
    {reserved : string HOLset.set, source_terms : string HOLset.set,
     source_sorts : string HOLset.set, proof_terms : string HOLset.set,
     proof_sorts : string HOLset.set}
  (* The origin constructor is private even though ScopedSession remains
     public. Its exact retained session/frame cannot be supplied by callers. *)
  local
    datatype 'a constructed_origin_private = ScopedOrigin of
      {graph : G.graph,parent_scope : G.scope,scope : G.scope,
       session : 'a constructed_session,variables : 'a list,
       descriptors : (string * string * Type.hol_type) list,
       close : unit -> unit,parent_guard : unit -> unit,
       child_guard : unit -> unit,epoch : int,symbols : int,
       binders : bool,binding : 'a B.binding_origin}
    and 'a constructed_scoped_session = ScopedSession of
    {session : 'a constructed_session, variables : 'a list,
     descriptors : (string * string * Type.hol_type) list,
     parent_scope : G.scope, scope : G.scope, close : unit -> unit,
     origin : 'a constructed_origin_private option}
  withtype 'a constructed_session =
    {reader : 'a constructed_reader, symbol_key : string -> string,
     namespace : unit -> namespace,
     sort_dictionary : unit -> Type.hol_type P.dict,
     parse_from : (unit -> string) -> 'a constructed_term,
     add_literal_parser : (string -> Term.term) -> unit,
     add_recipe_parser : string *
       (string -> Term.term list -> Term.term list -> Term.term) -> unit,
     add_constructor_parser : string * 'a P.construction_parse_fn
       -> unit,
     add_source_parser : string * Type.hol_type *
       'a P.construction_parse_fn -> unit,
     replace_source_parser : string * Type.hol_type *
       'a P.construction_parse_fn -> unit,
     add_symbolic_index : string * string -> unit,
     private_symbol : 'a B.frame ->
       {kind : string, hol_type : Type.hol_type,
        source : 'a option, stable : bool} -> 'a,
     parse_sort : (unit -> string) -> Type.hol_type,
     declare : string * Type.hol_type -> unit,
     private_variable : string * Type.hol_type -> 'a constructed_term,
     define : string * 'a constructed_term -> unit,
     define_opaque : string -> unit,
     define_variable : string * string * Type.hol_type -> 'a constructed_term,
     define_list : string * 'a constructed_term list -> unit,
     lookup_list : string -> 'a constructed_term list option,
     declare_sort : string * int -> unit,
     open_binders : (string * string * Type.hol_type) list ->
       'a constructed_scoped_session,
     open_bindings : (string * 'a constructed_term) list ->
       'a constructed_scoped_session,
     open_mixed_bindings : (string * 'a constructed_term) list ->
       string list -> 'a constructed_scoped_session}
  in
  type 'a constructed_origin = 'a constructed_origin_private
  type 'a constructed_session = 'a constructed_session
  datatype constructed_scoped_session = datatype constructed_scoped_session
  type scoped_origin = G.node constructed_origin
  type session = G.node constructed_session
  type scoped_session = G.node constructed_scoped_session

  (* Pure expected-owner peek. No held graph/frame/session is activated. *)
  fun scoped_origin_owner (ScopedOrigin {graph,parent_scope,scope,...}) =
    {graph = graph,parent_scope = parent_scope,scope = scope}
  (* Public record fields cannot replace the genuine producer's exact
     child session, variables, descriptors, scope or close callback. NONE
     remains available to generic clients on the unchanged old call path. *)
  fun scoped_session_origin (ScopedSession
      {session,variables,descriptors,parent_scope,scope,close,origin}) =
    case origin of NONE => raise ERR "scoped_origin" "no genuine scoped origin"
      | SOME (held as ScopedOrigin
          {session = actual,variables = saved,descriptors = declared,
           parent_scope = parent,scope = child,close = finish,...}) =>
        if Portable.pointer_eq (session,actual) andalso
            Portable.pointer_eq (variables,saved) andalso
            Portable.pointer_eq (descriptors,declared) andalso
            parent_scope = parent andalso scope = child andalso
            Portable.pointer_eq (close,finish) then held else
          raise ERR "scoped_origin" "scoped session fields differ"
  (* Pure public-record authentication before yielding the genuine
     low-level origin. A copied or forged record cannot replace its fields. *)
  fun scoped_session_binding_origin scoped =
    case scoped_session_origin scoped of ScopedOrigin {binding,...} => binding
  fun scoped_origin_data graph parent
      (ScopedOrigin {graph = held,parent_scope,scope,variables,descriptors,
       parent_guard,child_guard,epoch,symbols,binders,...}) =
    let
      val _ = if Portable.pointer_eq (graph,held) andalso
          parent = parent_scope then () else
        raise ERR "scoped_origin" "different graph or genuine parent scope"
      val _ = G.validate_scope graph parent
      val _ = if Type.type_epoch () = epoch andalso
          Term.term_epoch () = symbols then () else
        raise ERR "scoped_origin" "origin retirement epoch changed"
      val _ = parent_guard ()
      val _ = child_guard ()
      val _ = G.validate_scope graph scope
      val _ = if G.scope_visible graph scope parent then () else
        raise ERR "scoped_origin" "child escaped its genuine parent"
      val _ = List.app (fn node =>
        if G.scope_visible graph scope (G.node_scope graph node) then () else
          raise ERR "scoped_origin" "variable escaped its actual child")
        variables
      val _ = parent_guard ()
      val _ = child_guard ()
    in {scope = scope,variables = variables,descriptors = descriptors,
      binders = binders} end

  (* Follow recorded transparent syntax only. A lexical alias remains a
     single occurrence even when its graph value happens to be an OR. *)
  fun disjunction_children_using {visit,token_work,reverse}
      (P.ConstructionOccurrence {role, token, children, ...}) =
    (visit();case role of
      P.ConstructionApplication =>
        (token_work token;if token = "or" then SOME children else NONE)
    | P.ConstructionLet _ =>
        (case reverse children of body :: _ =>
           disjunction_children_using
             {visit=visit,token_work=token_work,reverse=reverse}body
         | [] => NONE)
    | P.ConstructionAnnotation =>
        (case children of [body] =>disjunction_children_using
           {visit=visit,token_work=token_work,reverse=reverse}body
         | _ => NONE)
    | _ => NONE)
  fun disjunction_children occurrence=disjunction_children_using
    {visit=fn()=>(),token_work=fn _=>(),reverse=List.rev}occurrence
  fun clause_occurrences ({occurrence, ...} : term) =
    case disjunction_children occurrence of
      SOME children => children | NONE => [occurrence]

  fun cpc_normalized_source backend policy occurrence source =
    let fun has_let (P.ConstructionOccurrence {role,children,...}) =
          (case role of P.ConstructionLet _ => true | _ => false) orelse
          List.exists has_let children
    in if policy=CPC andalso has_let occurrence then
        C.normalize_lets (B.syntax_spend backend) source
      else source end

  fun create_session_aux (options : options) source_declarations
      {solver, version, policy, reserved_names} get_token : session =
    let
      val graph = #graph options
      val scope = #scope options
      val backend = B.graphs
        {graph = graph, scope = scope, import_limit = #import_limit options,
         literal_limit = #literal_limit options,
         binder_limit = #binder_limit options}
      val root = B.root backend
      val private_count = ref 0
      val private_bindings = ref ([] : private_binding list)
      val symbolic_indices = ref (Redblackmap.mkDict String.compare)
      fun solver_variables () : solver_variable list = List.map
        (fn {node, lexical, scope} =>
          {node = node, lexical = lexical, scope = valOf scope})
        (B.solver_variables backend)
      fun compare_private ((ls, lk, lt, li), (rs, rk, rt, ri)) =
        case Int.compare (ls, rs) of EQUAL =>
          (case String.compare (lk, rk) of EQUAL =>
             (case Type.compare (lt, rt) of EQUAL => IntInf.compare (li, ri)
              | order => order)
           | order => order)
        | order => order
      val private_symbols = ref (Redblackmap.mkDict compare_private)
      val sourced_symbols = ref []
      fun private_symbol frame {kind, hol_type, source, stable} =
        let
          val active = valOf (B.frame_scope backend frame)
          val _ = Option.app (fn node =>
            (ignore (G.type_of graph node);
             if G.scope_visible graph active (G.node_scope graph node) then
               () else raise ERR "private_symbol"
                 "private source escapes construction scope")) source
          (* Private FP identity is native SOURCE alpha identity, not graph
             equality (a graph LET may already have been substituted). *)
          val syntax = Option.map (fn node =>
            case B.constructor_sources backend of
                SOME {arguments=[_,original],...} => original
              | _ => B.source_syntax backend frame node) source
          val source_id = case syntax of NONE => ~1
            | SOME syntax => C.identity syntax
          fun retained_source () =
            case (source,syntax) of (SOME node,SOME syntax) =>
                if G.scope_visible graph scope (G.node_scope graph node)
                then source else SOME (detached_private_source backend
                  (List.map #marker (!private_bindings)) syntax)
            | _ => source
          val owner = root
          val scope = valOf (B.frame_scope backend owner)
          fun same (saved_scope,saved_kind,saved_type,saved_source,_) =
            (B.syntax_spend backend 1;
             kind=saved_kind andalso Type.compare (hol_type,saved_type)=EQUAL
             andalso G.scope_visible graph active saved_scope andalso
             case syntax of SOME current => C.aconv
               (B.syntax_spend backend) (current,saved_source)
             | NONE => false)
          val key = (G.scope_id scope, kind, hol_type, source_id)
          fun allocate () =
            let
              val serial = !private_count
              val _ = private_count := serial + 1
              val node = B.fresh_solver_variable backend owner
                (kind ^ "#" ^ Int.toString serial, hol_type)
              val _ = private_bindings :=
                {scope = scope, marker = node, kind = kind,
                 source = retained_source ()} :: !private_bindings
              val _ = if stable then private_symbols :=
                Redblackmap.insert (!private_symbols, key, node) else ()
              val _ = if stable then Option.app (fn syntax =>
                sourced_symbols := (scope,kind,hol_type,syntax,node) ::
                  !sourced_symbols) syntax else ()
            in node end
        in if stable then case Redblackmap.peek (!private_symbols, key) of
            SOME node => node
          | NONE => (case source of NONE => allocate () | SOME _ =>
              case List.find same (!sourced_symbols) of
                SOME (_,_,_,_,node) =>
                  (private_symbols := Redblackmap.insert
                     (!private_symbols,key,node);node)
              | NONE => allocate ())
          else allocate () end
      val selected = R.select_with backend (#recipe_limits options)
        ((#special options) backend)
        {logic = #logic options, solver = SOME solver}
      val (sorts, dictionary) = #dictionaries selected
      (* CPC prints a function declaration's sort as (-> domains range).
         This is the legacy CPC type parser, not a Boolean term alias. *)
      val sorts = case policy of Z3 => sorts | CPC =>
        let
          fun function_sort token indices args =
            if token = "->" andalso List.null indices andalso
                List.length args >= 2 then
              let val (domains,range) = Lib.front_last args
              in boolSyntax.list_mk_fun (domains,range) end
            else raise ERR "cpc_function_sort"
              "expected a function sort with a domain and range"
        in Library.extend_dict (("->",function_sort),sorts) end
      val reserved = Redblackmap.foldl
        (fn (name, _, set) => HOLset.add (set, name))
        (Redblackmap.foldl (fn (name, _, set) => HOLset.add (set, name))
          (HOLset.addList (HOLset.empty String.compare, reserved_names)) sorts)
        dictionary
      fun symbol_key token = case policy of
          Z3 => P.proof_symbol_text token
        | CPC => case P.proof_quoted_symbol_token token of
            SOME name => if HOLset.member (reserved, name) then token else name
          | NONE => token
      fun unique kind dictionary key =
        if Redblackmap.inDomain (dictionary, key) then
          raise ERR "create" ("duplicate " ^ kind ^ " declaration " ^ key)
        else ()
      fun declaration_key kind token =
        if Option.isSome (P.proof_string_token token) then
          raise ERR "create" ("string literal used as " ^ kind ^ " name")
        else symbol_key token
      val variable_descriptors = ref
        (Redblackmap.mkDict Int.compare :
          (int, string * string * Type.hol_type) Redblackmap.dict)
      fun retain_descriptor node descriptor =
        variable_descriptors := Redblackmap.insert
          (!variable_descriptors, G.node_id node, descriptor)
      fun declared ((token, original, arity), (dictionary, variables)) =
        let
          val key = declaration_key "term" token
          val _ = unique "term" dictionary key
          val node = B.source backend root original
          val descriptor = if Term.is_var original then
            SOME (Term.dest_var original) else NONE
          fun parse frame name indices arguments =
            let
              (* Retain the source bridge above, but a binder-list alias can
                 resolve the same lexical variable to a fresh Bound node. *)
              val value = case descriptor of
                  SOME variable => B.reference backend frame
                    (Term.mk_var variable, node)
                | NONE => node
              val count = List.length arguments
              val accepted = case arity of NONE => true
                | SOME (Exact expected) => count = expected
                | SOME (AtMost maximum) => count <= maximum
              val _ = if accepted orelse value <> node then () else
                SmtLib_Theories.decline ("<" ^ name ^ ">")
                  "wrong number of arguments"
            in P.construction_value_parsefn backend value
              frame name indices arguments end
          val variables = case descriptor of
              SOME (name, ty) =>
                (retain_descriptor node (key, name, ty);
                 Redblackmap.insert (variables, key, (key, name, ty)))
            | NONE => variables
        in (Library.extend_dict ((key, parse), dictionary), variables) end
      val source_types = ref (List.foldl
        (fn ((token, original, arity), types) =>
          let val count = case arity of NONE => 0
                | SOME (Exact count) => count
                | SOME (AtMost count) => count
              val _ = if count >= 0 then () else
                raise ERR "source" "negative source arity"
          in Redblackmap.insert (types, declaration_key "term" token,
              [Term.type_of original]) end)
        (Redblackmap.mkDict String.compare) source_declarations)
      val (dictionary, variables) = List.foldl declared
        (dictionary, Redblackmap.mkDict String.compare) source_declarations
      val sorts = Redblackmap.foldl (fn (token, callbacks, sorts) =>
        let val key = declaration_key "sort" token
            val _ = unique "sort" sorts key
        in Redblackmap.insert (sorts, key, callbacks) end)
        sorts (#sorts options)
      val binder_lists = List.foldl (fn ((token, entries), lists) =>
        let val key = declaration_key "binder list" token
            val _ = unique "binder list" lists key
            fun variable (token, name, ty) =
              case Redblackmap.peek (variables, symbol_key token) of
                SOME (key, actual_name, actual_ty) =>
                  if actual_name = name andalso
                     Type.compare (actual_ty, ty) = EQUAL then
                    (key, name, ty)
                  else raise ERR "binder_list" "variable descriptor mismatch"
              | NONE => raise ERR "binder_list"
                  "binder-list entry is not a retained source variable"
        in Redblackmap.insert (lists, key, List.map variable entries) end)
        (Redblackmap.mkDict String.compare) (#binder_lists options)
      fun keys dictionary = Redblackmap.foldl
        (fn (key, _, set) => HOLset.add (set, key))
        (HOLset.empty String.compare) dictionary
      val source_terms = ref (HOLset.difference (keys dictionary, reserved))
      val source_sorts = HOLset.difference (keys sorts, reserved)
      val captured_blocks = capture_table backend
      fun context root scope dictionary_ref variables_ref sorts_ref
          binder_lists_ref lists_ref proof_terms proof_sorts aliases_ref
          : session =
      let
      fun check () = ignore (B.frame_scope backend root)
      fun check_reserved kind token =
        if HOLset.member (reserved, P.proof_symbol_text token) then
          raise ERR "declaration" (kind ^ " may not shadow builtin symbol")
        else ()
      fun fresh_term token =
        let val _ = check ()
            val key = declaration_key "term" token
            val _ = check_reserved "term" token
        in if HOLset.member (!proof_terms, key) then
             raise (case policy of CPC => Feedback.mk_HOL_ERR
                 "CPC_ProofParser" "parse_define"
                 ("duplicate CPC declaration or definition of symbol " ^
                  P.proof_symbol_text token)
               | Z3 => ERR "create"
                   ("duplicate term declaration " ^ key))
           else ();
           unique "term" (!dictionary_ref) key;
           if Redblackmap.inDomain (!lists_ref, key) then
             raise ERR "define" "duplicate list declaration" else ();
           key end
      fun add_literal_parser literal =
        let
          val _ = check ()
          fun parse frame token indices arguments =
            if String.size token > #token_limit (#recipe_limits options) then
              raise ERR "literal" "literal token exceeds admitted bound"
            else if null indices andalso null arguments then
              B.literal backend frame (literal token)
            else SmtLib_Theories.decline "graph_literal"
              "not a nullary literal"
        in dictionary_ref := Library.extend_dict
          (("_", parse), !dictionary_ref) end
      fun add_recipe_parser (name, parse) =
        let val _ = check ()
            val parse = R.recipe_parsefn backend (#recipe_limits options) parse
        in dictionary_ref := Library.extend_dict
          ((name, parse), !dictionary_ref) end
      fun add_symbolic_index (head, token) =
        let
          val _ = check ()
          val limit = #token_limit (#recipe_limits options)
          val _ = if String.size head <= limit andalso
              String.size token <= limit then () else
            raise ERR "index" "symbolic index exceeds bounded contract"
          val key = symbol_key head
          val names = case Redblackmap.peek (!symbolic_indices, key) of
              NONE => HOLset.empty String.compare | SOME names => names
        in symbolic_indices := Redblackmap.insert
          (!symbolic_indices, key, HOLset.add (names, symbol_key token)) end
      fun symbolic_index head token =
        case Redblackmap.peek (!symbolic_indices, symbol_key head) of
          NONE => NONE
        | SOME names => if HOLset.member (names, symbol_key token) then
            SOME (P.proof_symbol_text token) else NONE
      fun add_constructor_parser (name, parse) =
        let
          val _ = check ()
          fun admitted frame token indices arguments =
            if String.size token > #token_limit (#recipe_limits options)
                orelse List.length arguments >
                  #operand_limit (#recipe_limits options) orelse
                List.length indices > #operand_limit (#recipe_limits options)
            then raise ERR "constructor" "private constructor exceeds contract"
            else parse frame token indices arguments
        in dictionary_ref := Library.extend_dict
          ((name, admitted), !dictionary_ref) end
      fun add_source_parser (name, ty, parse) =
        let
          val _ = check_reserved "term" name
          val key = declaration_key "term" name
          val types = case Redblackmap.peek (!source_types, key) of
              NONE => [] | SOME types => types
          val _ = add_constructor_parser (key, parse)
          val _ = source_types := Redblackmap.insert
            (!source_types, key, ty :: types)
        in source_terms := HOLset.add (!source_terms, key) end
      fun parse_sort tokens =
        (check (); P.parse_type_with_key
          (case policy of CPC => symbol_key | Z3 => Lib.I)
          tokens (!sorts_ref))
      fun install key value descriptor =
        let
          fun parse frame name indices arguments =
            let val value = case descriptor of
                SOME lexical => B.reference backend frame (lexical, value)
              | NONE => value
            in P.construction_value_parsefn backend value
              frame name indices arguments end
          val _ = dictionary_ref := Library.extend_dict
            ((key, parse), !dictionary_ref)
          val _ = proof_terms := HOLset.add (!proof_terms, key)
        in case descriptor of
            SOME lexical =>
              let val (name, ty) = Term.dest_var lexical in
                variables_ref := Redblackmap.insert
                  (!variables_ref, key, (key, name, ty)) end
          | NONE => () end
      fun atomic node : term =
        {node = node, scope = scope, source_syntax = NONE, binder_blocks = [],
         occurrence = P.ConstructionOccurrence
           {value = node, role = P.ConstructionAtom,
            token = "@declaration", children = []}}
      fun define_opaque token =
        let val key = fresh_term token
        in proof_terms := HOLset.add (!proof_terms, key) end
      fun define (token, value : term) =
        let val key = fresh_term token
            val _ = B.type_of backend (#node value)
            (* Binder references name the original variable, not its value
               after capture by a later lexical LET. Retain metadata only. *)
            val _ = case B.variable_descriptor backend (#node value) of
                SOME variable =>
                  let val (name, ty) = Term.dest_var variable
                  in variables_ref := Redblackmap.insert
                    (!variables_ref, key, (key, name, ty)) end
              | NONE => ()
            fun parse frame name indices arguments =
              let val original = (#node value,#binder_blocks value)
                  val (node,blocks) = if policy=CPC then
                    B.capture_alias backend frame original else original
                  val _ = if policy<>CPC orelse null blocks then () else
                    captured_blocks :=
                    Redblackmap.insert (!captured_blocks,
                      (key,G.node_id node),blocks)
                  val result = P.construction_value_parsefn backend
                    node frame name indices arguments
                  val _ = case B.constructor_sources backend of
                      NONE => ()
                    | SOME {arguments,...} =>
                      let
                        val source = case #source_syntax value of
                            SOME source => source
                          | NONE => B.source_syntax backend frame (#node value)
                        fun apply (argument,function) =
                          (B.syntax_spend backend 1;
                           C.application (function,argument))
                      in B.note_constructor_source backend
                        (List.foldl apply source arguments) end
              in result end
        in dictionary_ref := Library.extend_dict
             ((key, parse), !dictionary_ref);
           proof_terms := HOLset.add (!proof_terms, key);
           aliases_ref := Redblackmap.insert (!aliases_ref, key, value) end
      fun private_variable (name, ty) =
        let val node = B.variable backend root G.SolverFlexible (name, ty)
        in retain_descriptor node (name, name, ty); atomic node end
      fun define_variable (token, name, ty) =
        let val key = fresh_term token
            val lexical = Term.mk_var (name, ty)
            val node = B.variable backend root G.SolverFlexible (name, ty)
        in install key node (SOME lexical);
           retain_descriptor node (key, name, ty); atomic node end
      fun declare (token, ty) =
        let val _ = check ()
            val key = declaration_key "term" token
            val _ = check_reserved "term" token
        in if policy = CPC andalso HOLset.member (!proof_terms, key) then
             raise (Feedback.mk_HOL_ERR "CPC_ProofParser" "parse_declaration"
               ("duplicate CPC declaration of symbol " ^
                P.proof_symbol_text token))
           else ();
           case Redblackmap.peek (!source_types, key) of
            SOME actual =>
              if List.exists (fn expected =>
                  Type.compare (expected, ty) = EQUAL) actual then () else
                raise ERR "declare" "incompatible source declaration"
          | NONE =>
              (case Redblackmap.peek (dictionary, key) of
                 SOME _ =>
                   let val value = P.apply_construction_symbol
                         (configuration root) dictionary root key [] []
                   in if Type.compare (B.type_of backend value, ty) = EQUAL
                     then () else raise ERR "declare"
                       "incompatible source declaration" end
               | NONE => ignore (define_variable
                   (token, P.proof_symbol_text token, ty)))
        end
      and configuration frame : G.node P.construction_cfg =
        {backend = backend, frame = frame, symbol_key = symbol_key,
         type_symbol_key = case policy of CPC => symbol_key | Z3 => Lib.I,
         index_limit = #index_limit (#recipe_limits options),
         parse_choice = false, parse_lambda = true,
         lookup_binder_list = fn token => binder_list_lookup backend
           (Redblackmap.peek (!binder_lists_ref, symbol_key token))
           (Option.map (List.map #node)
             (Redblackmap.peek (!lists_ref, symbol_key token))),
         binder_reference = fn frame => fn token =>
           let val key = symbol_key token in
             case B.lookup backend frame key of
               (* A lexical LET binds a variable even when its eliminated
                  graph value is compound. Bind its declared name/type, not
                  the descriptor (if any) of the substituted operand. *)
               SOME node => ((key, P.proof_symbol_text token,
                 B.type_of backend node),NONE)
             | NONE => case Redblackmap.peek (!aliases_ref,key) of
                 SOME alias => B.binder_reference backend key (#node alias)
               | NONE => case Redblackmap.peek (!variables_ref, key) of
                   SOME variable => (variable,NONE)
                 | NONE => B.binder_reference backend key
                     (P.apply_construction_symbol
                       (configuration frame) (!dictionary_ref) frame token [] [])
           end,
         record_binder_block = fn _ => (), ascribed_symbol = ascribed,
         coerce_arguments = R.coerce_arguments backend}
      and ascribed frame
          (description as {name, constructor, sort, arguments}) =
        let val builtin = ref false
            val value = case (#ascribed options) backend frame description of
          SOME node => node
        | NONE =>
          (case R.ascribed backend frame (#recipe_limits options)
              description of SOME value => (builtin := true;value)
           | NONE => if null arguments then
              let
                val value = case B.lookup backend frame (symbol_key name) of
                    SOME value => value
                  | NONE => P.apply_construction_symbol
                      (configuration frame) (!dictionary_ref) frame name [] []
              in if Type.compare (B.type_of backend value, sort) = EQUAL
                then value else raise ERR "ascribed" "qualified sort mismatch"
              end
            else raise ERR "ascribed"
              "qualified constructor requires a scoped graph adapter")
        in if !builtin orelse
              Type.compare (B.type_of backend value, sort) = EQUAL then value
          else raise ERR "ascribed" "graph adapter qualified sort mismatch"
        end
      fun define_list (token, values) =
        let val key = fresh_term token
            fun descriptor (value : term) =
              let val _ = B.type_of backend (#node value)
              in case Redblackmap.peek
                  (!variable_descriptors, G.node_id (#node value)) of
                  SOME descriptor => SOME descriptor
                | NONE => Option.map (fn variable =>
                    let val (name, ty) = Term.dest_var variable
                    in (name, name, ty) end)
                    (B.variable_descriptor backend (#node value)) end
            val descriptors = List.mapPartial descriptor values
            val _ = lists_ref := Redblackmap.insert
              (!lists_ref, key, values)
            val _ = proof_terms := HOLset.add (!proof_terms, key)
        in if List.length descriptors = List.length values then
            binder_lists_ref := Redblackmap.insert
              (!binder_lists_ref, key, descriptors)
          else () end
      fun declare_sort (token, arity) =
        let val _ = check ()
            val key = declaration_key "sort" token
            val _ = check_reserved "sort" token
            val _ = if HOLset.member (!proof_sorts, key) then
              raise ERR "declare_sort" "duplicate proof sort" else ()
            fun compatible parse =
              (ignore (parse (P.proof_symbol_text token) []
                (List.tabulate (arity, fn index => Type.mk_vartype
                  ("'cpc_sort_arg" ^ Int.toString index)))); true)
              handle Feedback.HOL_ERR _ => false
            val _ = if arity < 0 then
              raise ERR "declare_sort" "negative sort arity" else ()
        in case Redblackmap.peek (#sorts options, key) of
            SOME callbacks =>
              if List.exists compatible callbacks then () else
                raise ERR "declare_sort" "incompatible source sort"
          | NONE =>
              let val _ = unique "sort" (!sorts_ref) key
                  val _ = if arity = 0 then () else
                    raise ERR "declare_sort" "non-nullary proof sort"
                  val ty = Type.mk_vartype
                    ("'cpc_" ^ P.proof_symbol_text token)
                  fun parse _ indices arguments =
                    if null indices andalso null arguments then ty else
                      raise ERR "declare_sort" "wrong sort arity"
              in sorts_ref := Library.extend_dict
                ((key, parse), !sorts_ref);
                proof_sorts := HOLset.add (!proof_sorts, key) end
        end
      fun blocks (P.ConstructionOccurrence
          {value, role, token, children, ...}) =
        let val nested = List.concat (List.map blocks children) in
          case role of P.ConstructionBinder {kind, variables} =>
            (kind, List.length variables, value) :: nested
          | P.ConstructionAtom =>
              (case (if policy=CPC then Redblackmap.peek
                  (!captured_blocks,(symbol_key token,G.node_id value))
                else NONE) of SOME captured => captured @ nested
               | NONE => case Redblackmap.peek
                   (!aliases_ref,symbol_key token) of
                 SOME (alias : term) =>
                   if G.node_id (#node alias) = G.node_id value then
                     #binder_blocks alias @ nested else nested
               | NONE => nested)
          | _ => nested
        end
      fun parse_from tokens =
        let val _ = check ()
            val (occurrence, source) =
              P.parse_term_sourced_with_backend_and_indices
                (configuration root) symbolic_index tokens
                (!sorts_ref, !dictionary_ref)
            val source = cpc_normalized_source backend policy
              occurrence source
            val blocks = blocks occurrence
            val blocks = if policy=CPC then
              unique_blocks backend G.node_id blocks else blocks
        in {node = P.construction_value occurrence, scope = scope,
            source_syntax = SOME source,
            occurrence = occurrence, binder_blocks = blocks} end
      val reader : reader =
        {graph = graph, scope = scope, backend = backend, solver = solver,
         version = version, coverage = #entries selected,
         parse_next = fn () => parse_from get_token,
         solver_variables = solver_variables,
         private_bindings = fn () => List.rev (!private_bindings)}
      fun child_context frame scope = context frame scope
        (ref (!dictionary_ref)) (ref (!variables_ref))
        (ref (!sorts_ref)) (ref (!binder_lists_ref))
        (ref (!lists_ref)) (ref (!proof_terms)) (ref (!proof_sorts))
        (ref (!aliases_ref))
      fun open_mixed_bindings values blocked_keys =
        let
          val entries = List.map (fn (name, value : term) =>
            (symbol_key name, P.proof_symbol_text name, #node value)) values
          val descriptors = List.map (fn (key, name, node) =>
            (key, name, B.type_of backend node)) entries
          val opened = B.open_mixed_bindings backend root entries
            (List.map symbol_key blocked_keys)
          val inner_scope = valOf (#scope opened)
          val child = child_context (#frame opened) inner_scope
            handle error => ((#close opened) (); raise error)
          val origin = ScopedOrigin
            {graph = graph,parent_scope = scope,scope = inner_scope,
             session = child,variables = [],descriptors = descriptors,
             close = #close opened,parent_guard = check,
             child_guard = fn () =>
               if B.frame_scope backend (#frame opened) = SOME inner_scope
                 then () else raise ERR "scoped_origin" "child frame changed",
             epoch = Type.type_epoch (),symbols = Term.term_epoch (),
             binders = false,binding = valOf (#origin opened)}
        in ScopedSession
          {session = child, variables = [], descriptors = descriptors,
           parent_scope = scope, scope = inner_scope,
           close = #close opened,origin = SOME origin} end
      fun open_bindings values = open_mixed_bindings values []
      fun open_binders descriptors =
        let
          val opened = B.open_binders backend root descriptors
          val inner_scope = valOf (#scope opened)
          val child = child_context (#frame opened) inner_scope
            handle error => ((#close opened) (); raise error)
          val origin = ScopedOrigin
            {graph = graph,parent_scope = scope,scope = inner_scope,
             session = child,variables = #variables opened,
             descriptors = descriptors,close = #close opened,
             parent_guard = check,
             child_guard = fn () =>
               if B.frame_scope backend (#frame opened) = SOME inner_scope
                 then () else raise ERR "scoped_origin" "child frame changed",
             epoch = Type.type_epoch (),symbols = Term.term_epoch (),
             binders = true,binding = valOf (#origin opened)}
        in ScopedSession
          {session = child, variables = #variables opened,
           descriptors = descriptors, parent_scope = scope,
           scope = inner_scope, close = #close opened,origin = SOME origin} end
    in {reader = reader, open_mixed_bindings = open_mixed_bindings,
        define_opaque = define_opaque,
        symbol_key = symbol_key,
        namespace = fn () =>
          {reserved = reserved, source_terms = !source_terms,
           source_sorts = source_sorts, proof_terms = !proof_terms,
           proof_sorts = !proof_sorts},
        sort_dictionary = fn () => (check (); !sorts_ref),
        parse_from = parse_from,
        add_literal_parser = add_literal_parser,
        add_recipe_parser = add_recipe_parser,
        add_constructor_parser = add_constructor_parser,
        add_source_parser = add_source_parser,
        replace_source_parser = fn entry as (name,_,_) =>
          (check ();check_reserved "term" name;
           dictionary_ref := Redblackmap.insert
             (!dictionary_ref,declaration_key "term" name,[]);
           add_source_parser entry),
        add_symbolic_index = add_symbolic_index,
        private_symbol = private_symbol,
        parse_sort = parse_sort, declare = declare, define = define,
        private_variable = private_variable,
        define_variable = define_variable, define_list = define_list,
        lookup_list = fn token =>
          (check (); Redblackmap.peek (!lists_ref, symbol_key token)),
        declare_sort = declare_sort, open_binders = open_binders,
        open_bindings = open_bindings} end
      val dictionary_ref = ref dictionary
      val variables_ref = ref variables
      val sorts_ref = ref sorts
      val binder_lists_ref = ref binder_lists
      val lists_ref = ref
        (Redblackmap.mkDict String.compare :
          (string, term list) Redblackmap.dict)
      val proof_terms = ref (HOLset.empty String.compare)
      val proof_sorts = ref (HOLset.empty String.compare)
      val aliases_ref = ref
        (Redblackmap.mkDict String.compare : (string, term) Redblackmap.dict)
    in context root scope dictionary_ref variables_ref sorts_ref
      binder_lists_ref lists_ref proof_terms proof_sorts aliases_ref end

  fun create_session (options : options) description tokens =
    create_session_aux options
      (List.map (fn (token, original) => (token, original, NONE))
        (#sources options)) description tokens

  fun create_configured_session
      ({base, source_declarations} : configured_options) description tokens =
    create_session_aux base
      (List.map (fn {token, original, arity} =>
        (token, original, SOME arity)) source_declarations) description tokens

  fun create options description tokens =
    #reader (create_session options description tokens)
  type 'a constructed_policy_options =
    {graph : G.graph, scope : G.scope, logic : string,
     sources : (string * Term.term) list,
     sorts : Type.hol_type P.dict,
     binder_lists : (string * (string * string * Type.hol_type) list) list,
     import_limit : SmtReplayResourcePolicy.limit,
     literal_limit : SmtReplayResourcePolicy.limit,
     binder_limit : SmtReplayResourcePolicy.limit,
     recipe_limits : R.policy_limits,
     special : 'a B.backend -> R.entry ->
       'a P.construction_parse_fn option,
     ascribed : 'a B.backend -> 'a B.frame -> 'a constructed_ascription ->
       'a option}
  type policy_options = G.node constructed_policy_options
  type policy_configured_options =
    {base:policy_options,source_declarations:source_declaration list}
  type graph_policy_configured_options =
    {base:policy_options,
     graph_source_declarations:graph_source_declaration list}
  fun policy_frontend_length pending =
    let fun count [] (n:IntInf.int) = n
          | count (_::rest) n = count rest (n+1)
    in count pending 0 end
  fun constructed_declaration_parser backend same_identity
      node descriptor arity guard frame name indices arguments =
    let
      val _ = guard frame
      val value = case descriptor of
          SOME variable => B.reference backend frame
            (Term.mk_var variable,node)
        | NONE => node
      val count = List.length arguments
      val accepted = case arity of NONE => true
        | SOME (Exact expected) => count=expected
        | SOME (AtMost maximum) => count<=maximum
      val _ = if accepted orelse not (same_identity (value,node)) then () else
        SmtLib_Theories.decline ("<" ^ name ^ ">") "wrong number of arguments"
    in P.construction_value_parsefn backend value
      frame name indices arguments end

  (* One policy grammar for genuine graph nodes and typed parser values.
     Native admission remains in its original initializer below; the value
     initializer consumes every durable Mapping declaration. *)
  fun create_policy_session_for_backend
      (options : 'a constructed_policy_options) backend
      {identity,same_identity,guard_private,guard_observation,private_scope,
       source_scope,private_label}
      source_declarations
      initialise_extra {solver,version,policy,reserved_names} get_token
      : 'a constructed_session =
    let
      val graph = #graph options
      val scope = #scope options
      val root = B.root backend
      val private_count = ref 0
      val private_bindings = ref ([] : 'a constructed_private_binding list)
      val symbolic_indices = ref (Redblackmap.mkDict String.compare)
      fun solver_variables () : 'a constructed_solver_variable list = List.map
        (fn {node, lexical, scope} =>
          {node = node, lexical = lexical, scope = valOf scope})
        (B.solver_variables backend)
      fun compare_private ((ls, lk, lt, li), (rs, rk, rt, ri)) =
        case Int.compare (ls, rs) of EQUAL =>
          (case String.compare (lk, rk) of EQUAL =>
             (case Type.compare (lt, rt) of EQUAL => IntInf.compare (li, ri)
              | order => order)
           | order => order)
        | order => order
      val private_symbols = ref (Redblackmap.mkDict compare_private)
      val sourced_symbols = ref []
      fun private_symbol frame {kind, hol_type, source, stable} =
        let
          val active = private_scope frame
          val _ = Option.app (guard_private active) source
          (* Use the actual operand syntax before semantic construction,
             not a possibly substituted/lambda-lifted graph recipe. *)
          val syntax = Option.map (fn node =>
            case B.constructor_sources backend of
                SOME {arguments=[_,original],...} => original
              | _ => B.source_syntax backend frame node) source
          val source_id = case syntax of NONE => ~1
            | SOME syntax => C.identity syntax
          fun retained_source () =
            case (source,syntax) of (SOME node,SOME syntax) =>
                if G.scope_visible graph scope (source_scope node)
                then source else SOME (detached_private_source backend
                  (List.map #marker (!private_bindings)) syntax)
            | _ => source
          val owner = root
          val scope = private_scope owner
          fun same (saved_scope,saved_kind,saved_type,saved_source,_) =
            (B.syntax_spend backend 1;
             kind=saved_kind andalso Type.compare (hol_type,saved_type)=EQUAL
             andalso G.scope_visible graph active saved_scope andalso
             case syntax of SOME current => C.aconv
               (B.syntax_spend backend) (current,saved_source)
             | NONE => false)
          val key = (G.scope_id scope, kind, hol_type, source_id)
          fun allocate () =
            let
              val serial = !private_count
              val _ = private_count := serial + 1
              val node = B.fresh_solver_variable backend owner
                (kind ^ "#" ^ Int.toString serial, hol_type)
              val _ = private_bindings :=
                {scope = private_label frame owner,
                 marker = node, kind = kind,
                 source = retained_source ()} :: !private_bindings
              val _ = if stable then private_symbols :=
                Redblackmap.insert (!private_symbols, key, node) else ()
              val _ = if stable then Option.app (fn syntax =>
                sourced_symbols := (scope,kind,hol_type,syntax,node) ::
                  !sourced_symbols) syntax else ()
            in node end
        in if stable then case Redblackmap.peek (!private_symbols, key) of
            SOME node => node
          | NONE => (case source of NONE => allocate () | SOME _ =>
              case List.find same (!sourced_symbols) of
                SOME (_,_,_,_,node) =>
                  (private_symbols := Redblackmap.insert
                     (!private_symbols,key,node);node)
              | NONE => allocate ())
          else allocate () end
      val selected = R.select_with_policy backend (#recipe_limits options)
        ((#special options) backend)
        {logic = #logic options, solver = SOME solver}
      val (sorts, dictionary) = #dictionaries selected
      (* CPC prints a function declaration's sort as (-> domains range).
         This is the legacy CPC type parser, not a Boolean term alias. *)
      val sorts = case policy of Z3 => sorts | CPC =>
        let
          fun function_sort token indices args =
            if token = "->" andalso List.null indices andalso
                List.length args >= 2 then
              let val (domains,range) = Lib.front_last args
              in boolSyntax.list_mk_fun (domains,range) end
            else raise ERR "cpc_function_sort"
              "expected a function sort with a domain and range"
        in Library.extend_dict (("->",function_sort),sorts) end
      val reserved = Redblackmap.foldl
        (fn (name, _, set) => HOLset.add (set, name))
        (Redblackmap.foldl (fn (name, _, set) => HOLset.add (set, name))
          (HOLset.addList (HOLset.empty String.compare, reserved_names)) sorts)
        dictionary
      fun symbol_key token = case policy of
          Z3 => P.proof_symbol_text token
        | CPC => case P.proof_quoted_symbol_token token of
            SOME name => if HOLset.member (reserved, name) then token else name
          | NONE => token
      fun unique kind dictionary key =
        if Redblackmap.inDomain (dictionary, key) then
          raise ERR "create" ("duplicate " ^ kind ^ " declaration " ^ key)
        else ()
      fun declaration_key kind token =
        if Option.isSome (P.proof_string_token token) then
          raise ERR "create" ("string literal used as " ^ kind ^ " name")
        else symbol_key token
      val variable_descriptors = ref
        (Redblackmap.mkDict Int.compare :
          (int, string * string * Type.hol_type) Redblackmap.dict)
      fun retain_descriptor node descriptor =
        variable_descriptors := Redblackmap.insert
          (!variable_descriptors, identity node, descriptor)
      fun declared ((token, original, arity), (dictionary, variables)) =
        let
          val key = declaration_key "term" token
          val _ = unique "term" dictionary key
          val node = B.source backend root original
          val descriptor = if Term.is_var original then
            SOME (Term.dest_var original) else NONE
          val parse = constructed_declaration_parser backend same_identity
            node descriptor arity (fn _ => ())
          val variables = case descriptor of
              SOME (name, ty) =>
                (retain_descriptor node (key, name, ty);
                 Redblackmap.insert (variables, key, (key, name, ty)))
            | NONE => variables
        in (Library.extend_dict ((key, parse), dictionary), variables) end
      val source_types = ref (List.foldl
        (fn ((token, original, arity), types) =>
          let val count = case arity of NONE => 0
                | SOME (Exact count) => count
                | SOME (AtMost count) => count
              val _ = if count >= 0 then () else
                raise ERR "source" "negative source arity"
          in Redblackmap.insert (types, declaration_key "term" token,
              [Term.type_of original]) end)
        (Redblackmap.mkDict String.compare) source_declarations)
      val (dictionary, variables) = List.foldl declared
        (dictionary, Redblackmap.mkDict String.compare) source_declarations
      val (dictionary,variables) = initialise_extra
        {root=root,dictionary=dictionary,variables=variables,
         source_types=source_types,
         retain_descriptor=retain_descriptor,declaration_key=declaration_key}
      val sorts = Redblackmap.foldl (fn (token, callbacks, sorts) =>
        let val key = declaration_key "sort" token
            val _ = unique "sort" sorts key
        in Redblackmap.insert (sorts, key, callbacks) end)
        sorts (#sorts options)
      val binder_lists = List.foldl (fn ((token, entries), lists) =>
        let val key = declaration_key "binder list" token
            val _ = unique "binder list" lists key
            fun variable (token, name, ty) =
              case Redblackmap.peek (variables, symbol_key token) of
                SOME (key, actual_name, actual_ty) =>
                  if actual_name = name andalso
                     Type.compare (actual_ty, ty) = EQUAL then
                    (key, name, ty)
                  else raise ERR "binder_list" "variable descriptor mismatch"
              | NONE => raise ERR "binder_list"
                  "binder-list entry is not a retained source variable"
        in Redblackmap.insert (lists, key, List.map variable entries) end)
        (Redblackmap.mkDict String.compare) (#binder_lists options)
      fun keys dictionary = Redblackmap.foldl
        (fn (key, _, set) => HOLset.add (set, key))
        (HOLset.empty String.compare) dictionary
      val source_terms = ref (HOLset.difference (keys dictionary, reserved))
      val source_sorts = HOLset.difference (keys sorts, reserved)
      val captured_blocks = capture_table backend
      fun context root scope dictionary_ref variables_ref sorts_ref
          binder_lists_ref lists_ref proof_terms proof_sorts aliases_ref
          : 'a constructed_session =
      let
      fun check () = ignore (B.frame_scope backend root)
      fun check_reserved kind token =
        if HOLset.member (reserved, P.proof_symbol_text token) then
          raise ERR "declaration" (kind ^ " may not shadow builtin symbol")
        else ()
      fun fresh_term token =
        let val _ = check ()
            val key = declaration_key "term" token
            val _ = check_reserved "term" token
        in if HOLset.member (!proof_terms, key) then
             raise (case policy of CPC => Feedback.mk_HOL_ERR
                 "CPC_ProofParser" "parse_define"
                 ("duplicate CPC declaration or definition of symbol " ^
                  P.proof_symbol_text token)
               | Z3 => ERR "create"
                   ("duplicate term declaration " ^ key))
           else ();
           unique "term" (!dictionary_ref) key;
           if Redblackmap.inDomain (!lists_ref, key) then
             raise ERR "define" "duplicate list declaration" else ();
           key end
      fun add_literal_parser literal =
        let
          val _ = check ()
          fun parse frame token indices arguments =
            if not (SmtReplayResourcePolicy.allows
              (#token_limit (#recipe_limits options))
              (IntInf.fromInt (String.size token))) then
              raise ERR "literal" "literal token exceeds admitted bound"
            else if null indices andalso null arguments then
              B.literal backend frame (literal token)
            else SmtLib_Theories.decline "graph_literal"
              "not a nullary literal"
        in dictionary_ref := Library.extend_dict
          (("_", parse), !dictionary_ref) end
      fun add_recipe_parser (name, parse) =
        let val _ = check ()
            val parse = R.recipe_parsefn_with_policy backend
              (#recipe_limits options) parse
        in dictionary_ref := Library.extend_dict
          ((name, parse), !dictionary_ref) end
      fun add_symbolic_index (head, token) =
        let
          val _ = check ()
          val limit = #token_limit (#recipe_limits options)
          val _ = if SmtReplayResourcePolicy.allows limit
              (IntInf.fromInt (String.size head)) andalso
              SmtReplayResourcePolicy.allows limit
                (IntInf.fromInt (String.size token)) then () else
            raise ERR "index" "symbolic index exceeds bounded contract"
          val key = symbol_key head
          val names = case Redblackmap.peek (!symbolic_indices, key) of
              NONE => HOLset.empty String.compare | SOME names => names
        in symbolic_indices := Redblackmap.insert
          (!symbolic_indices, key, HOLset.add (names, symbol_key token)) end
      fun symbolic_index head token =
        case Redblackmap.peek (!symbolic_indices, symbol_key head) of
          NONE => NONE
        | SOME names => if HOLset.member (names, symbol_key token) then
            SOME (P.proof_symbol_text token) else NONE
      fun add_constructor_parser (name, parse) =
        let
          val _ = check ()
          fun admitted frame token indices arguments =
            if not (SmtReplayResourcePolicy.allows
              (#token_limit (#recipe_limits options))
              (IntInf.fromInt (String.size token)))
                orelse not (SmtReplayResourcePolicy.allows
                  (#operand_limit (#recipe_limits options))
                  (policy_frontend_length arguments)) orelse
                not (SmtReplayResourcePolicy.allows
                  (#operand_limit (#recipe_limits options))
                  (policy_frontend_length indices))
            then raise ERR "constructor" "private constructor exceeds contract"
            else parse frame token indices arguments
        in dictionary_ref := Library.extend_dict
          ((name, admitted), !dictionary_ref) end
      fun add_source_parser (name, ty, parse) =
        let
          val _ = check_reserved "term" name
          val key = declaration_key "term" name
          val types = case Redblackmap.peek (!source_types, key) of
              NONE => [] | SOME types => types
          val _ = add_constructor_parser (key, parse)
          val _ = source_types := Redblackmap.insert
            (!source_types, key, ty :: types)
        in source_terms := HOLset.add (!source_terms, key) end
      fun parse_sort tokens =
        (check (); P.parse_type_with_key
          (case policy of CPC => symbol_key | Z3 => Lib.I)
          tokens (!sorts_ref))
      fun install key value descriptor =
        let
          fun parse frame name indices arguments =
            let val value = case descriptor of
                SOME lexical => B.reference backend frame (lexical, value)
              | NONE => value
            in P.construction_value_parsefn backend value
              frame name indices arguments end
          val _ = dictionary_ref := Library.extend_dict
            ((key, parse), !dictionary_ref)
          val _ = proof_terms := HOLset.add (!proof_terms, key)
        in case descriptor of
            SOME lexical =>
              let val (name, ty) = Term.dest_var lexical in
                variables_ref := Redblackmap.insert
                  (!variables_ref, key, (key, name, ty)) end
          | NONE => () end
      fun atomic node : 'a constructed_term =
        {node = node, scope = scope, source_syntax = NONE, binder_blocks = [],
         occurrence = P.ConstructionOccurrence
           {value = node, role = P.ConstructionAtom,
            token = "@declaration", children = []}}
      fun define_opaque token =
        let val key = fresh_term token
        in proof_terms := HOLset.add (!proof_terms, key) end
      fun define (token, value : 'a constructed_term) =
        let val key = fresh_term token
            val _ = B.type_of backend (#node value)
            (* Binder references name the original variable, not its value
               after capture by a later lexical LET. Retain metadata only. *)
            val _ = case B.variable_descriptor backend (#node value) of
                SOME variable =>
                  let val (name, ty) = Term.dest_var variable
                  in variables_ref := Redblackmap.insert
                    (!variables_ref, key, (key, name, ty)) end
              | NONE => ()
            fun parse frame name indices arguments =
              let val original = (#node value,#binder_blocks value)
                  val (node,blocks) = if policy=CPC then
                    B.capture_alias backend frame original else original
                  val _ = if policy<>CPC orelse null blocks then () else
                    captured_blocks :=
                    Redblackmap.insert (!captured_blocks,
                      (key,identity node),blocks)
                  val result = P.construction_value_parsefn backend
                    node frame name indices arguments
                  val _ = case B.constructor_sources backend of
                      NONE => ()
                    | SOME {arguments,...} =>
                      let
                        val source = case #source_syntax value of
                            SOME source => source
                          | NONE => B.source_syntax backend frame (#node value)
                        fun apply (argument,function) =
                          (B.syntax_spend backend 1;
                           C.application (function,argument))
                      in B.note_constructor_source backend
                        (List.foldl apply source arguments) end
              in result end
        in dictionary_ref := Library.extend_dict
             ((key, parse), !dictionary_ref);
           proof_terms := HOLset.add (!proof_terms, key);
           aliases_ref := Redblackmap.insert (!aliases_ref, key, value) end
      fun private_variable (name, ty) =
        let val node = B.variable backend root G.SolverFlexible (name, ty)
        in retain_descriptor node (name, name, ty); atomic node end
      fun define_variable (token, name, ty) =
        let val key = fresh_term token
            val lexical = Term.mk_var (name, ty)
            val node = B.variable backend root G.SolverFlexible (name, ty)
        in install key node (SOME lexical);
           retain_descriptor node (key, name, ty); atomic node end
      fun declare (token, ty) =
        let val _ = check ()
            val key = declaration_key "term" token
            val _ = check_reserved "term" token
        in if policy = CPC andalso HOLset.member (!proof_terms, key) then
             raise (Feedback.mk_HOL_ERR "CPC_ProofParser" "parse_declaration"
               ("duplicate CPC declaration of symbol " ^
                P.proof_symbol_text token))
           else ();
           case Redblackmap.peek (!source_types, key) of
            SOME actual =>
              if List.exists (fn expected =>
                  Type.compare (expected, ty) = EQUAL) actual then () else
                raise ERR "declare" "incompatible source declaration"
          | NONE =>
              (case Redblackmap.peek (dictionary, key) of
                 SOME _ =>
                   let val value = P.apply_construction_symbol_with_policy
                         (configuration root) dictionary root key [] []
                   in if Type.compare (B.type_of backend value, ty) = EQUAL
                     then () else raise ERR "declare"
                       "incompatible source declaration" end
               | NONE => ignore (define_variable
                   (token, P.proof_symbol_text token, ty)))
        end
      and configuration frame : 'a P.policy_construction_cfg =
        {backend = backend, frame = frame, symbol_key = symbol_key,
         type_symbol_key = case policy of CPC => symbol_key | Z3 => Lib.I,
         index_limit = #index_limit (#recipe_limits options),
         parse_choice = false, parse_lambda = true,
         lookup_binder_list = fn token => binder_list_lookup backend
           (Redblackmap.peek (!binder_lists_ref, symbol_key token))
           (Option.map (List.map #node)
             (Redblackmap.peek (!lists_ref, symbol_key token))),
         binder_reference = fn frame => fn token =>
           let val key = symbol_key token in
             case B.lookup backend frame key of
               (* A lexical LET binds a variable even when its eliminated
                  graph value is compound. Bind its declared name/type, not
                  the descriptor (if any) of the substituted operand. *)
               SOME node => ((key, P.proof_symbol_text token,
                 B.type_of backend node),NONE)
             | NONE => case Redblackmap.peek (!aliases_ref,key) of
                 SOME alias => B.binder_reference backend key (#node alias)
               | NONE => case Redblackmap.peek (!variables_ref, key) of
                   SOME variable => (variable,NONE)
                 | NONE => B.binder_reference backend key
                     (P.apply_construction_symbol_with_policy
                       (configuration frame) (!dictionary_ref) frame token [] [])
           end,
         record_binder_block = fn _ => (), ascribed_symbol = ascribed,
         coerce_arguments = R.coerce_arguments backend}
      and ascribed frame
          (description as {name, constructor, sort, arguments}) =
        let val builtin = ref false
            val value = case (#ascribed options) backend frame description of
          SOME node => node
        | NONE =>
          (case R.ascribed_with_policy backend frame (#recipe_limits options)
              description of SOME value => (builtin := true;value)
           | NONE => if null arguments then
              let
                val value = case B.lookup backend frame (symbol_key name) of
                    SOME value => value
                  | NONE => P.apply_construction_symbol_with_policy
                      (configuration frame) (!dictionary_ref) frame name [] []
              in if Type.compare (B.type_of backend value, sort) = EQUAL
                then value else raise ERR "ascribed" "qualified sort mismatch"
              end
            else raise ERR "ascribed"
              "qualified constructor requires a scoped graph adapter")
        in if !builtin orelse
              Type.compare (B.type_of backend value, sort) = EQUAL then value
          else raise ERR "ascribed" "graph adapter qualified sort mismatch"
        end
      fun define_list (token, values) =
        let val key = fresh_term token
            fun descriptor (value : 'a constructed_term) =
              let val _ = B.type_of backend (#node value)
              in case Redblackmap.peek
                  (!variable_descriptors, identity (#node value)) of
                  SOME descriptor => SOME descriptor
                | NONE => Option.map (fn variable =>
                    let val (name, ty) = Term.dest_var variable
                    in (name, name, ty) end)
                    (B.variable_descriptor backend (#node value)) end
            val descriptors = List.mapPartial descriptor values
            val _ = lists_ref := Redblackmap.insert
              (!lists_ref, key, values)
            val _ = proof_terms := HOLset.add (!proof_terms, key)
        in if List.length descriptors = List.length values then
            binder_lists_ref := Redblackmap.insert
              (!binder_lists_ref, key, descriptors)
          else () end
      fun declare_sort (token, arity) =
        let val _ = check ()
            val key = declaration_key "sort" token
            val _ = check_reserved "sort" token
            val _ = if HOLset.member (!proof_sorts, key) then
              raise ERR "declare_sort" "duplicate proof sort" else ()
            fun compatible parse =
              (ignore (parse (P.proof_symbol_text token) []
                (List.tabulate (arity, fn index => Type.mk_vartype
                  ("'cpc_sort_arg" ^ Int.toString index)))); true)
              handle Feedback.HOL_ERR _ => false
            val _ = if arity < 0 then
              raise ERR "declare_sort" "negative sort arity" else ()
        in case Redblackmap.peek (#sorts options, key) of
            SOME callbacks =>
              if List.exists compatible callbacks then () else
                raise ERR "declare_sort" "incompatible source sort"
          | NONE =>
              let val _ = unique "sort" (!sorts_ref) key
                  val _ = if arity = 0 then () else
                    raise ERR "declare_sort" "non-nullary proof sort"
                  val ty = Type.mk_vartype
                    ("'cpc_" ^ P.proof_symbol_text token)
                  fun parse _ indices arguments =
                    if null indices andalso null arguments then ty else
                      raise ERR "declare_sort" "wrong sort arity"
              in sorts_ref := Library.extend_dict
                ((key, parse), !sorts_ref);
                proof_sorts := HOLset.add (!proof_sorts, key) end
        end
      fun blocks (P.ConstructionOccurrence
          {value, role, token, children, ...}) =
        let val nested = List.concat (List.map blocks children) in
          case role of P.ConstructionBinder {kind, variables} =>
            (kind, List.length variables, value) :: nested
          | P.ConstructionAtom =>
              (case (if policy=CPC then Redblackmap.peek
                  (!captured_blocks,(symbol_key token,identity value))
                else NONE) of SOME captured => captured @ nested
               | NONE => case Redblackmap.peek
                   (!aliases_ref,symbol_key token) of
                 SOME (alias : 'a constructed_term) =>
                   if same_identity (#node alias,value) then
                     #binder_blocks alias @ nested else nested
               | NONE => nested)
          | _ => nested
        end
      fun parse_from tokens =
        let val _ = check ()
            val (occurrence, source) =
              P.parse_term_sourced_with_policy_and_indices
                (configuration root) symbolic_index tokens
                (!sorts_ref, !dictionary_ref)
            val source = cpc_normalized_source backend policy
              occurrence source
            val blocks = blocks occurrence
            val blocks = if policy=CPC then
              unique_blocks backend identity blocks else blocks
        in {node = P.construction_value occurrence, scope = scope,
            source_syntax = SOME source,
            occurrence = occurrence, binder_blocks = blocks} end
      val reader : 'a constructed_reader =
        {graph = graph, scope = scope, backend = backend, solver = solver,
         version = version, coverage = #entries selected,
         parse_next = fn () => parse_from get_token,
         solver_variables = solver_variables,
         private_bindings = fn () =>
           (guard_observation check;List.rev (!private_bindings))}
      fun child_context frame scope = context frame scope
        (ref (!dictionary_ref)) (ref (!variables_ref))
        (ref (!sorts_ref)) (ref (!binder_lists_ref))
        (ref (!lists_ref)) (ref (!proof_terms)) (ref (!proof_sorts))
        (ref (!aliases_ref))
      fun open_mixed_bindings values blocked_keys =
        let
          val entries = List.map (fn (name, value : 'a constructed_term) =>
            (symbol_key name, P.proof_symbol_text name, #node value)) values
          val descriptors = List.map (fn (key, name, node) =>
            (key, name, B.type_of backend node)) entries
          val opened = B.open_mixed_bindings backend root entries
            (List.map symbol_key blocked_keys)
          val inner_scope = valOf (#scope opened)
          val child = child_context (#frame opened) inner_scope
            handle error => ((#close opened) (); raise error)
          val origin = ScopedOrigin
            {graph = graph,parent_scope = scope,scope = inner_scope,
             session = child,variables = [],descriptors = descriptors,
             close = #close opened,parent_guard = check,
             child_guard = fn () =>
               if B.frame_scope backend (#frame opened) = SOME inner_scope
                 then () else raise ERR "scoped_origin" "child frame changed",
             epoch = Type.type_epoch (),symbols = Term.term_epoch (),
             binders = false,binding = valOf (#origin opened)}
        in ScopedSession
          {session = child, variables = [], descriptors = descriptors,
           parent_scope = scope, scope = inner_scope,
           close = #close opened,origin = SOME origin} end
      fun open_bindings values = open_mixed_bindings values []
      fun open_binders descriptors =
        let
          val opened = B.open_binders backend root descriptors
          val inner_scope = valOf (#scope opened)
          val child = child_context (#frame opened) inner_scope
            handle error => ((#close opened) (); raise error)
          val origin = ScopedOrigin
            {graph = graph,parent_scope = scope,scope = inner_scope,
             session = child,variables = #variables opened,
             descriptors = descriptors,close = #close opened,
             parent_guard = check,
             child_guard = fn () =>
               if B.frame_scope backend (#frame opened) = SOME inner_scope
                 then () else raise ERR "scoped_origin" "child frame changed",
             epoch = Type.type_epoch (),symbols = Term.term_epoch (),
             binders = true,binding = valOf (#origin opened)}
        in ScopedSession
          {session = child, variables = #variables opened,
           descriptors = descriptors, parent_scope = scope,
           scope = inner_scope, close = #close opened,origin = SOME origin} end
    in {reader = reader, open_mixed_bindings = open_mixed_bindings,
        define_opaque = define_opaque,
        symbol_key = fn token => (guard_observation check;symbol_key token),
        namespace = fn () =>
          (guard_observation check;
           {reserved = reserved, source_terms = !source_terms,
            source_sorts = source_sorts, proof_terms = !proof_terms,
            proof_sorts = !proof_sorts}),
        sort_dictionary = fn () => (check (); !sorts_ref),
        parse_from = parse_from,
        add_literal_parser = add_literal_parser,
        add_recipe_parser = add_recipe_parser,
        add_constructor_parser = add_constructor_parser,
        add_source_parser = add_source_parser,
        replace_source_parser = fn entry as (name,_,_) =>
          (guard_observation check;check_reserved "term" name;
           dictionary_ref := Redblackmap.insert
             (!dictionary_ref,declaration_key "term" name,[]);
           add_source_parser entry),
        add_symbolic_index = add_symbolic_index,
        private_symbol = private_symbol,
        parse_sort = parse_sort, declare = declare, define = define,
        private_variable = private_variable,
        define_variable = define_variable, define_list = define_list,
        lookup_list = fn token =>
          (check (); Redblackmap.peek (!lists_ref, symbol_key token)),
        declare_sort = declare_sort, open_binders = open_binders,
        open_bindings = open_bindings} end
      val dictionary_ref = ref dictionary
      val variables_ref = ref variables
      val sorts_ref = ref sorts
      val binder_lists_ref = ref binder_lists
      val lists_ref = ref
        (Redblackmap.mkDict String.compare :
          (string, 'a constructed_term list) Redblackmap.dict)
      val proof_terms = ref (HOLset.empty String.compare)
      val proof_sorts = ref (HOLset.empty String.compare)
      val aliases_ref = ref
        (Redblackmap.mkDict String.compare :
          (string, 'a constructed_term) Redblackmap.dict)
    in context root scope dictionary_ref variables_ref sorts_ref
      binder_lists_ref lists_ref proof_terms proof_sorts aliases_ref end

  fun create_policy_session_aux_with_graph_declarations
      (options:policy_options) source_declarations graph_declarations
      description get_token : session =
    let
      val graph = #graph options val scope = #scope options
      val backend = B.graphs_with_policy
        {graph=graph,scope=scope,import_limit= #import_limit options,
         literal_limit= #literal_limit options,
         binder_limit= #binder_limit options}
      fun initialise_extra
          {root,dictionary,variables,source_types,retain_descriptor,
           declaration_key} =
        let
          fun unique kind dictionary key =
            if Redblackmap.inDomain (dictionary,key) then
              raise ERR "create"
                ("duplicate " ^ kind ^ " declaration " ^ key)
            else ()
      (* A graph declaration is lexical data. Validate the owned graph
         and all free IDs without importing its expanded representative. *)
      fun declared_graph
          (({token,node,arity}:graph_source_declaration),
           (dictionary,variables)) =
        let
          val key = declaration_key "term" token
          val _ = unique "term" dictionary key
          val ty = G.type_of graph node
          val free = case G.free_variable_nodes graph node of
              SOME nodes => nodes
            | NONE => raise ERR "graph_source"
                "graph declaration has unknown free IDs"
          fun visible caller current =
            if G.scope_visible graph caller (G.node_scope graph current)
              then () else raise ERR "graph_source"
                "graph declaration escapes its lexical scope"
          val _ = visible scope node
          val _ = List.app (visible scope) free
          val count = case arity of Exact n => n | AtMost n => n
          fun typed_arity remaining current =
            if remaining = 0 then () else
              case Lib.total Type.dom_rng current of
                SOME (_,range) => typed_arity (remaining - 1) range
              | NONE => raise ERR "graph_source"
                  "graph declaration arity exceeds its function type"
          val _ = if count >= 0 then typed_arity count ty else
            raise ERR "graph_source" "negative source arity"
          val descriptor = case G.view graph node of
              G.Variable (_,lexical) => SOME (Term.dest_var lexical)
            | _ => NONE
          fun guard frame =
            let val caller = valOf (B.frame_scope backend frame)
                val _ = visible caller node
            in List.app (visible caller) free end
          val parse = constructed_declaration_parser backend (op =)
            node descriptor (SOME arity) guard
          val variables = case descriptor of
              SOME (name,ty) =>
                (retain_descriptor node (key,name,ty);
                 Redblackmap.insert (variables,key,(key,name,ty)))
            | NONE => variables
          val _ = source_types := Redblackmap.insert
            (!source_types,key,[ty])
        in (Library.extend_dict ((key,parse),dictionary),variables) end
      val (dictionary,variables) = List.foldl declared_graph
        (dictionary,variables) graph_declarations
        in (dictionary,variables) end
      fun guard_private scope node =
        (ignore (G.type_of graph node);
         if G.scope_visible graph scope (G.node_scope graph node) then ()
         else raise ERR "private_symbol"
           "private source escapes construction scope")
    in create_policy_session_for_backend options backend
      {identity=G.node_id,same_identity=op =,guard_private=guard_private,
       guard_observation=fn _ => (),
       private_scope=fn frame => valOf (B.frame_scope backend frame),
       source_scope=G.node_scope graph,
       private_label=fn _ => fn owner => valOf (B.frame_scope backend owner)}
      source_declarations initialise_extra description get_token end

  (* Preserve the existing raw declaration route and evaluation order. *)
  fun create_policy_session_aux options declarations =
    create_policy_session_aux_with_graph_declarations
      options declarations []

  fun create_session_with_policy (options:policy_options) description tokens =
    create_policy_session_aux options
      (List.map (fn (token, original) => (token, original, NONE))
        (#sources options)) description tokens

  fun create_configured_session_with_policy
      ({base,source_declarations}:policy_configured_options)
      description tokens =
    create_policy_session_aux base
      (List.map (fn {token, original, arity} =>
        (token, original, SOME arity)) source_declarations) description tokens

  (* The caller supplies the exact serializer's lexical mapping, just as
     for source_declarations. This stage creates no source bridge, query,
     assertion or proof assumption, and does not attest emitted syntax. *)
  fun create_graph_configured_session_with_policy
      ({base,graph_source_declarations}:graph_policy_configured_options)
      description tokens =
    if List.null (#sources base) then
      create_policy_session_aux_with_graph_declarations
        base [] graph_source_declarations description tokens
    else raise ERR "graph_source"
      "graph declarations require an empty raw source list"

  type value_term = SmtLib_GraphParserValue.value constructed_term
  type value_reader = SmtLib_GraphParserValue.value constructed_reader
  type value_ascription =
    SmtLib_GraphParserValue.value constructed_ascription
  type value_solver_variable =
    SmtLib_GraphParserValue.value constructed_solver_variable
  type value_private_binding =
    SmtLib_GraphParserValue.value constructed_private_binding
  type value_session = SmtLib_GraphParserValue.value constructed_session
  type value_scoped_session =
    SmtLib_GraphParserValue.value constructed_scoped_session
  type value_scoped_origin = SmtLib_GraphParserValue.value constructed_origin
  type value_options =
    SmtLib_GraphParserValue.value constructed_policy_options

  fun value_clause_occurrences ({occurrence,...}:value_term) =
    case disjunction_children occurrence of
        SOME children => children | NONE => [occurrence]

  (* Same occurrence grammar with actual new-client accounting. A
     callback only observes syntax DATA; it grants no origin or Scope. *)
  fun value_clause_occurrences_with_observer observer
      ({occurrence,...}:value_term)=
    case disjunction_children_using observer occurrence of
        SOME children=>children|NONE=>[occurrence]

  (* The supplied actual Mapping factory owns its construction children.
     Session construction and every parse/mutation use the caller's SAME
     active Work action; no with_step is entered here. The caller closes
     the factory on all final outcomes. No Mapping declaration is filtered,
     and no metadata closure is reified as a native term or G.node. *)
  fun create_mapping_session_with_policy
      (factory:SmtLib_GraphParserMappingBackend.value_backend)
      (options:value_options) description tokens : value_session =
    let
      val backend = #backend factory val context = #context factory
      val _ = PV.validate_for context (#graph options) (#scope options)
      fun initialise_extra
          {root,dictionary,variables,source_types,retain_descriptor,
           declaration_key} =
        let
          fun declared ((entry:M.declaration,node),(dictionary,variables)) =
            let
              val key = declaration_key "term" (#token entry)
              val _ = if Redblackmap.inDomain (dictionary,key) then
                raise ERR "create" ("duplicate term declaration " ^ key)
                else ()
              val _ = PV.usable context (#scope options) node
              val ty = B.type_of backend node
              val _ = if Type.compare (ty,#hol_type entry)=EQUAL then () else
                raise ERR "mapping_source" "mapping declaration type changed"
              val arity = case #arity entry of M.Exact count => Exact count
                | M.AtMost count => AtMost count
              val descriptor = Option.map Term.dest_var
                (B.variable_descriptor backend node)
              fun guard frame =
                PV.usable context (valOf (B.frame_scope backend frame)) node
              val ordinary_parse = constructed_declaration_parser backend
                (op =) node descriptor (SOME arity) guard
              val parse = case #selector_body entry of NONE => ordinary_parse
                | SOME _ => fn frame => fn token => fn indices =>
                    fn arguments =>
                      let val _ = ordinary_parse frame token indices arguments
                      in (#apply_declaration factory) frame entry arguments end
              val variables = case descriptor of SOME (name,ty) =>
                    (retain_descriptor node (key,name,ty);
                     Redblackmap.insert (variables,key,(key,name,ty)))
                | NONE => variables
              val _ = source_types := Redblackmap.insert
                (!source_types,key,[ty])
            in (Library.extend_dict ((key,parse),dictionary),variables) end
        in List.foldl declared (dictionary,variables)
          ((#declarations factory) root) end
    in PV.protect context (fn () =>
      create_policy_session_for_backend options backend
        {identity=PV.key context,same_identity=op =,
         guard_private=PV.usable context,
         guard_observation=fn check => PV.protect context check,
         private_scope=fn frame => valOf
           (B.frame_lexical_scope backend frame),
         source_scope=PV.scope_of context,
         private_label=fn frame => fn _ => valOf
           (B.frame_lexical_scope backend frame)}
        (List.map (fn (token,original) => (token,original,NONE))
          (#sources options)) initialise_extra description tokens) end

  fun create_with_policy options description tokens =
    #reader (create_session_with_policy options description tokens)
  end (* private origin constructor *)
  (* Construction-layer policy only. These entry points accept the
     SAME backend/frame and already parsed literal/symbol/value indices.
     They do not claim to replace the finite full token-session grammar. *)
  type constructor_policy_options =
    {recipe_limits : R.policy_limits,
     special : G.node B.backend -> R.entry ->
       G.node P.construction_parse_fn option}
  fun create_constructor_dictionary_with_policy backend
      ({recipe_limits,special}:constructor_policy_options) description =
    R.select_with_policy backend recipe_limits (special backend) description
  fun recipe_parser_with_policy backend
      ({recipe_limits,...}:constructor_policy_options) parse =
    R.recipe_parsefn_with_policy backend recipe_limits parse
  fun parse_recipe_constructor_with_policy backend frame options parse
      token indices arguments =
    recipe_parser_with_policy backend options parse frame token
      indices arguments

end
