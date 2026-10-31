(* Copyright (c) 2026 The HOL4 contributors. *)
structure SmtReplayGraph :> SmtReplayGraph =
struct
  structure R = ReplayRedblackPrivateWork
  val _ = ReplayRedblackPrivateWork.lookup_int
  val ERR = Feedback.mk_HOL_ERR "SmtReplayGraph"
  datatype node = Node of {owner : unit ref, id : int}
  datatype scope = Scope of {owner : unit ref, id : int}
  datatype variable_kind = RigidSource | SolverFlexible | Generated | Bound
  datatype view =
      Variable of variable_kind * Term.term
    | Constant of KernelSig.kernelid
    | Application of node * node
    | OpaqueRetained
    | AdmittedBinder of {binder : node, body : node, frame : scope}
  datatype metric = RawNodes | BinderInclusiveNodes
  datatype variable_summary = Known of Term.term list | Unknown
  type source = {node : node, original : Term.term, bridge : Thm.thm}
  (* Captured only by genuine initial admission, never reconstructed by a
     getter or adopted from a later canonical/source-anchor lookup. *)
  type admitted_binder_origin =
    {identity : unit ref,owner : unit ref,scope : scope,first_input :
      Term.term,
     binder_term : Term.term,binder : node,frame : scope,
     body_frame : scope,body : source,node : node,first_whole : source}
  datatype binder_origin = BinderOrigin of
    {owner : unit ref,scope : scope,original : node,whole : source,
     admission : admitted_binder_origin}
  (* Only private constructors establish structural child links. The
     caller scope stays the original opened-root owner; effective child
     scopes are taken from its retained admission records, never node_scope. *)
  datatype canonical_child =
      CanonicalBody of binder_origin
    | CanonicalApplicationChild of
        {parent : canonical_child,operator : bool,node : node}
    | CanonicalNestedBody of
        {parent : canonical_child,admission : admitted_binder_origin}
  datatype nested_binder_origin = NestedBinderOrigin of
    {child : canonical_child,admission : admitted_binder_origin}
  (* Closure provenance is canonical constructor metadata, not raw Source. *)
  type binder_closure_creation =
    {identity : unit ref,node : node,declaring_scope : scope,
     binder : node,binder_term : Term.term,binder_frame : scope,
     body : node,body_frame : scope}
  datatype binder_closure_record = ClosureRecord of
    {identity : unit ref,owner : unit ref,node : node,node_frame : scope,
     creation : binder_closure_creation,
     backing : binder_closure_record option}
  datatype closure_child =
      ClosureRoot of {owner : unit ref,caller : scope,node : node}
    | ClosureApplicationChild of
        {parent : closure_child,operator : bool,node : node}
    | ClosureBodyChild of
        {parent : closure_child,record : binder_closure_record}
  datatype binder_closure = BinderClosure of
    {child : closure_child,record : binder_closure_record}
  datatype opened_recipe = OpenedAtom
    | OpenedBinder of admitted_binder_origin
    | OpenedApplication of node * node
  type opened_record = {source : source, recipe : opened_recipe}
  datatype discovered_alpha = DiscoveredAlpha of
    {owner : unit ref,scope : scope,original : node,source : source,
     rows : (node * opened_record) list,roots : closure_child list,
     annotation : closure_child,epoch : int,symbols : int,visits : int}
  type identity_opened_record =
    {source : source,roots : closure_child list,guard : unit -> unit}
  datatype partial_recipe =
      PartialAtom of node * source
    | PartialRetained of node * source
    | PartialFull of node * source
    | PartialApplication of node * source * partial_recipe * partial_recipe
  datatype partial_discovery = PartialDiscovery of
    {owner : unit ref,scope : scope,original : node,
     recipe : partial_recipe option,guard : unit -> unit}
  datatype discovery_heads = DiscoveryHeads of
    {owner : unit ref,identity : unit ref,scope : scope,
     epoch : int,symbols : int,
     rows : (node * KernelSig.kernelid * int) list}
  datatype selected_partial_discovery = SelectedPartialDiscovery of
    {heads : discovery_heads,plan : partial_discovery}
  datatype opaque_profile = OpaqueProfile of
    {owner : unit ref,scope : scope,node : node,original : Term.term,
     raw : int,inc : int,ann : IntInf.int,ty : IntInf.int,
     type_bytes : IntInf.int,types : Type.hol_type list,
     ready : unit -> bool,guard : unit -> unit}
  (* Projection DATA is captured by the completed no-op scanner. It never
     opens an opaque binder or claims that its whole body is bounded. *)
  datatype opaque_projection_path =
      ProjectionAtom of {term : Term.term,variable : bool}
    | ProjectionApplication of Term.term * opaque_projection_path
    | ProjectionBinder of Term.term * Type.hol_type * opaque_projection_path
  datatype opaque_type_projection = OpaqueTypeProjection of
    {profile : opaque_profile,path : opaque_projection_path}
    | OpenedTypeProjection of
      {owner : unit ref,scope : scope,node : node,original : Term.term,
       path : opaque_projection_path,guard : unit -> unit,
       ready : unit -> bool,visits : int}
  datatype carrier_alpha =
      CarrierPartial of {plan : partial_discovery,recipe : partial_recipe,
                         annotation : closure_child}
    | CarrierFull of discovered_alpha
    | CarrierIdentity of {owner : unit ref,scope : scope,original : node,
        source : source,annotation : closure_child,
        epoch : int,symbols : int}
  datatype origin = ImportedSource | ConstructedSyntax
  datatype role = Atom | Conjunction | Disjunction | Clause | Context
                | Let | ProofBoundary
  datatype occurrence = Occurrence of
    {node : node, scope : scope, role : role, children : occurrence list}

  datatype type_key = TypeVariable of string
    | TypeOperator of KernelSig.kernelid * int list
  datatype key = VariableKey of int * int * string * int
    | ConstantKey of KernelSig.kernelid * int
    | ApplicationKey of int * int * int
  type entry = {scope : scope, ty : Type.hol_type, type_id : int,
                term : Term.term, view : view,
                raw : int option, inclusive : int option,
                source : source option ref}
  (* Exactly one authoritative semantic representation per graph.
     FixedStorage metadata IDs below are a separate, unchanged API. *)
  type legacy_index_state =
    {types:(type_key,int) Redblackmap.dict ref,
     keys:(key,node) Redblackmap.dict ref,
     recent:(Type.hol_type * int) list ref}
  type paid_index_state =
    {owner:unit ref,root:scope,meter:R.scope_meter,epoch:int,symbols:int,
     types:int R.graph_key_map ref,keys:node R.graph_key_map ref,
     recent:(Type.hol_type * int) list ref,
     empty_placeholders:Term.term R.int_map}
  datatype semantic_indices = LegacyIndices of legacy_index_state
    | PaidIndices of paid_index_state
  type frame = {parent : scope option, active : bool ref,
                bindings : ((string * int), node) Redblackmap.dict}
  datatype node_observation = NodeObservation of
    {creations : IntInf.int ref,accesses : IntInf.int ref,
     hits : IntInf.int ref,misses : IntInf.int ref}
  type node_statistics =
    {node_creations : IntInf.int,node_accesses : IntInf.int,
     intern_hits : IntInf.int,intern_misses : IntInf.int,total_nodes : int}
  type graph =
    {owner : unit ref, next : int ref, next_scope : int ref,
     node_observation : node_observation option ref,
     scope_retirements : IntInf.int ref,
     validation_changes : IntInf.int ref,
     nodes : entry R.int_map ref,
     scopes : frame R.int_map ref,
     indices : semantic_indices,
     imports : (Term.term * int * source) list Array.array,
     binders : (int, (Term.term, admitted_binder_origin) Redblackmap.dict)
               Redblackmap.dict ref,
     binder_origins : (int, admitted_binder_origin) Redblackmap.dict ref,
     binder_closures : (int,binder_closure_record) Redblackmap.dict ref,
     opened_views : ((int * int), opened_record) Redblackmap.dict ref,
     identity_views : ((int * int),identity_opened_record list)
       Redblackmap.dict ref,
     partial_sources : ((int * int),partial_discovery list)
       Redblackmap.dict ref,
     partial_projections : (int,opaque_type_projection list)
       Redblackmap.dict ref,
     partial_running : bool ref option ref,
     partial_profiles : (int,opaque_profile list) Redblackmap.dict ref,
     reserved : R.string_set ref,
     placeholders : Term.term R.int_map ref,
     next_name : int ref, next_bound_name : int ref,
     next_flexible_name : int ref,
     equalities : ((int * int), Thm.thm) Redblackmap.dict ref}

  fun node_id (Node {id, ...}) = id
  fun scope_id (Scope {id, ...}) = id
  fun pair_compare compare1 compare2 ((a,b), (c,d)) =
    case compare1 (a,c) of EQUAL => compare2 (b,d) | order => order
  fun list_compare _ ([], []) = EQUAL
    | list_compare _ ([], _) = LESS
    | list_compare _ (_, []) = GREATER
    | list_compare compare (x::xs, y::ys) =
        (case compare (x,y) of EQUAL => list_compare compare (xs,ys)
         | order => order)
  fun type_compare (TypeVariable a, TypeVariable b) = String.compare (a,b)
    | type_compare (TypeVariable _, _) = LESS
    | type_compare (_, TypeVariable _) = GREATER
    | type_compare (TypeOperator (a,xs), TypeOperator (b,ys)) =
        pair_compare KernelSig.id_compare (list_compare Int.compare)
          ((a,xs), (b,ys))
  fun key_compare (VariableKey (s,k,n,t), VariableKey (s',k',n',t')) =
        pair_compare (pair_compare Int.compare Int.compare)
          (pair_compare String.compare Int.compare)
          (((s,k),(n,t)), ((s',k'),(n',t')))
    | key_compare (VariableKey _, _) = LESS
    | key_compare (_, VariableKey _) = GREATER
    | key_compare (ConstantKey x, ConstantKey y) =
        pair_compare KernelSig.id_compare Int.compare (x,y)
    | key_compare (ConstantKey _, _) = LESS
    | key_compare (_, ConstantKey _) = GREATER
    | key_compare (ApplicationKey (s,l,r), ApplicationKey (s',l',r')) =
        pair_compare Int.compare (pair_compare Int.compare Int.compare)
          ((s,(l,r)), (s',(l',r')))

  val cap = case Int.maxInt of SOME maximum => maximum
    | NONE => 1073741823
  fun plus a b = if a >= cap - b then cap else a + b
  fun sum a b = case (a,b) of
      (SOME x, SOME y) => SOME (plus 1 (plus x y))
    | _ => NONE
  fun new () : graph =
    let val owner = ref () in
      {owner = owner, next = ref 0, next_scope = ref 1,
       node_observation = ref NONE,
       scope_retirements = ref 0,
       validation_changes = ref 0,
       nodes = ref (R.empty_int ()),
       scopes = ref (R.put_int
         (R.empty_int (), 0,
          {parent = NONE, active = ref true,
           bindings = Redblackmap.mkDict
             (pair_compare String.compare Int.compare)})),
       indices = LegacyIndices
         {keys=ref (Redblackmap.mkDict key_compare),
          types=ref (Redblackmap.mkDict type_compare),recent=ref []},
       imports = Array.array (4093, []),
       binders = ref (Redblackmap.mkDict Int.compare),
       binder_origins = ref (Redblackmap.mkDict Int.compare),
       binder_closures = ref (Redblackmap.mkDict Int.compare),
       opened_views = ref (Redblackmap.mkDict
         (pair_compare Int.compare Int.compare)),
       identity_views = ref (Redblackmap.mkDict
         (pair_compare Int.compare Int.compare)),
       partial_sources = ref (Redblackmap.mkDict
         (pair_compare Int.compare Int.compare)),
       partial_projections = ref (Redblackmap.mkDict Int.compare),
       partial_running = ref NONE,
       partial_profiles = ref (Redblackmap.mkDict Int.compare),
       reserved = ref (R.empty_string ()),
       placeholders = ref (R.empty_int ()),
       next_name = ref 0, next_bound_name = ref 0,
       next_flexible_name = ref 0,
       equalities = ref (Redblackmap.mkDict
         (pair_compare Int.compare Int.compare))}
    end
  fun root_scope (g : graph) = Scope {owner = #owner g, id = 0}
  fun scope_frame (g : graph) (Scope {owner,id}) =
    case #indices g of
        LegacyIndices _ =>
          if owner <> #owner g then
            raise ERR "scope" "scope belongs to a different graph"
          else (case R.peek_int (!(#scopes g),id) of
              SOME frame => frame
            | NONE => raise ERR "scope" "unknown scope")
      | PaidIndices p =>
          let val meter= #meter p
              val _=R.scope_meter_charge meter 64
              val _=if owner= #owner g then () else
                raise ERR "scope" "scope belongs to a different graph"
              val _=if #owner p= #owner g then () else
                raise ERR "paid_indices" "different graph owner"
              val _=if Type.type_epoch ()= #epoch p andalso
                  Term.term_epoch ()= #symbols p then () else
                raise ERR "paid_indices" "Type or Term epoch changed"
          in case R.scope_lookup_int meter (!(#scopes g),id) of
              SOME frame => frame
            | NONE => raise ERR "scope" "unknown scope" end
  (* Genuine immutable Scope records; only their active refs can retire.
     New scopes append new keys. Retain this actual path after quoting the
     private fixed-map lookups; no caller scope/guard program is adopted. *)
  datatype scope_path = ScopePath of
    {owner:unit ref,scope:scope,frames:bool ref list,
     setup:IntInf.int,validation:IntInf.int}
  fun scope_path_setup_work (ScopePath {setup,...}) = setup
  fun scope_path_validation_work (ScopePath {validation,...}) = validation
  fun prepare_scope_path (g:graph) caller {remaining_work} =
    let
      val _ = if remaining_work >= 2 then () else
        raise ERR "prepare_scope_path" "remaining Work cannot create meter"
      val ceiling = IntInf.fromInt remaining_work
      val used = ref (2:IntInf.int)
      fun spend amount =
        if amount >= 0 andalso amount <= ceiling - !used then
          used := !used+amount else
          raise ERR "prepare_scope_path" "original remaining Work exhausted"
      fun tick () = spend 1
      val _ = tick ()
      val table = !(#scopes g)
      fun capture (current as Scope {owner,id}) =
        let val _ = spend 4
            val _ = if owner = #owner g then () else
              raise ERR "prepare_scope_path" "different graph scope"
            val _ = tick ()
            val lookup = R.lookup_int (table,id,ceiling - !used)
            val _ = tick ()
            val _ = spend (#work (R.int_lookup_cost lookup))
            val _ = spend 2
            val frame = case R.int_lookup_value (table,lookup) of
                SOME value => value | NONE =>
                  raise ERR "prepare_scope_path" "unknown scope"
            val _ = tick ()
            val parent = #parent frame
            val _ = tick ()
            val (tail,future) = case parent of NONE =>
                (tick ();([],1:IntInf.int))
              | SOME outer => capture outer
            (* Ref selection, private cons, return pair; every future
               retained frame has list-pattern/ref-read/branch events. *)
            val _ = spend 4
        in (#active frame::tail,future+3) end
      val (frames,validation) = capture caller
      (* Owner and caller comparisons/branches precede every held frame. *)
      val _ = spend 1
      val validation = validation+5
      val _ = spend 3
    in ScopePath {owner= #owner g,scope=caller,frames=frames,
      setup= !used,validation=validation} end
  fun validate_scope_path (g:graph) caller
      (ScopePath {owner,scope,frames,...}) =
    if owner = #owner g andalso caller = scope then
      let fun alive [] = ()
            | alive (active::rest) =
                if !active then alive rest else
                  raise ERR "scope" "scope is closed"
      in alive frames end
    else raise ERR "scope" "scope path belongs to another graph/caller"

  (* DATA only. SAME graph/caller live path is validated on EVERY read.
     No current scope-map lookup, Work grant or retained liveness lease. *)
  fun scope_path_revision_work path =
    scope_path_validation_work path + 3
  fun validation_revision_with_scope_path (g:graph) caller path =
    (validate_scope_path g caller path;!(#validation_changes g))

  (* Same-counter setup for genuine Backend programs. Each private field,
     lookup and retained cell is paid before effect. This is not a second
     Work allowance; the opaque meter is captured by the original Work. *)
  fun prepare_shared_scope_path (g:graph) caller meter =
    let
      val initial = R.scope_meter_charged meter
      val _ = R.scope_meter_charge meter 2
      val table = !(#scopes g)
      fun capture (current as Scope {owner,id}) =
        let
          val _ = R.scope_meter_charge meter 4
          val _ = if owner = #owner g then () else
            raise ERR "prepare_shared_scope_path" "different graph scope"
          val _ = R.scope_meter_charge meter 2
          val frame = case R.scope_lookup_int meter (table,id) of
              SOME value => value | NONE =>
                raise ERR "prepare_shared_scope_path" "unknown scope"
          val _ = R.scope_meter_charge meter 2
          val (tail,chain,future) = case #parent frame of NONE =>
              (R.scope_meter_charge meter 2;([],[],1:IntInf.int))
            | SOME parent => capture parent
          val _ = R.scope_meter_charge meter 6
        in (#active frame::tail,current::chain,future+3) end
      val (frames,chain,validation) = capture caller
      val _ = R.scope_meter_charge meter 6
      val path = ScopePath {owner= #owner g,scope=caller,frames=frames,
        setup=IntInf.fromInt (R.scope_meter_charged meter-initial),
        validation=validation+5}
    in (path,chain) end

  datatype binding_scope_path = BindingScopePath of
    {owner:unit ref,active:scope,required:scope,
     active_path:scope_path,required_path:scope_path,
     visible:bool,validation:IntInf.int}
  fun binding_scope_path_work
      (BindingScopePath {validation,...}) = validation
  fun prepare_binding_scope_path (g:graph) active required meter =
    let
      val (active_path,chain) = prepare_shared_scope_path g active meter
      val (required_path,_) = prepare_shared_scope_path g required meter
      fun contains [] = (R.scope_meter_charge meter 1;false)
        | contains (current::rest) =
            (R.scope_meter_charge meter 3;
             current = required orelse contains rest)
      val visible = contains chain
      val _ = R.scope_meter_charge meter 8
      val validation = scope_path_validation_work active_path +
        scope_path_validation_work required_path + 8
    in BindingScopePath {owner= #owner g,active=active,required=required,
      active_path=active_path,required_path=required_path,visible=visible,
      validation=validation} end
  fun validate_binding_scope_path (g:graph) active required
      (BindingScopePath {owner,active=held,required=original,
        active_path,required_path,visible,...}) =
    if owner = #owner g andalso active = held andalso required = original then
      (validate_scope_path g active active_path;
       validate_scope_path g required required_path;
       if visible then () else
         raise ERR "binding_scope_path" "not in genuine ancestor path")
    else raise ERR "binding_scope_path" "different graph or visibility pair"


  fun check_scope g scope =
    let val {parent,active,...} = scope_frame g scope in
      if not (!active) then raise ERR "scope" "scope is closed"
      else case parent of NONE => () | SOME parent => check_scope g parent
    end
  val validate_scope = check_scope
  fun observe_node (g : graph) select =
    case !(#node_observation g) of NONE => ()
      | SOME (NodeObservation fields) =>
          let val cell = select fields in cell := !cell+1 end
  (* A node's scope is an immutable entry field. Only fresh node identifiers
     are appended; this typed lookup accepts no caller payload or scope. *)
  fun binding_node_scope (g:graph) (Node {owner,id}) meter =
    let
      val _ = R.scope_meter_charge meter 4
      val _ = if owner = #owner g then () else
        raise ERR "binding_node_scope" "different graph node"
      val _ = R.scope_meter_charge meter 2
      val table = !(#nodes g)
      val fields = case R.scope_lookup_int meter (table,id) of
          SOME fields => fields | NONE =>
            raise ERR "binding_node_scope" "unknown node"
      val _ = R.scope_meter_charge meter 7
      val _ = observe_node g #accesses
    in #scope fields end


  fun with_node_statistics (g : graph) scope action =
    let
      val _ = check_scope g scope
      val _ = case !(#node_observation g) of NONE => ()
        | SOME _ => raise ERR "with_node_statistics" "observation reentry"
      val fields = {creations = ref (0 : IntInf.int),
        accesses = ref (0 : IntInf.int),hits = ref (0 : IntInf.int),
        misses = ref (0 : IntInf.int)}
      val epoch = Type.type_epoch () val symbols = Term.term_epoch ()
      val _ = #node_observation g := SOME (NodeObservation fields)
      val outcome = Exn.capture (fn () =>
        let val result = action ()
            val _ = check_scope g scope
            val _ = if Type.type_epoch () = epoch andalso
                Term.term_epoch () = symbols then () else
              raise ERR "with_node_statistics" "observation epoch retired"
        in result end) ()
      val _ = #node_observation g := NONE
    in case outcome of Exn.Exn primary => raise primary
      | Exn.Res result =>
        let
      val counts : node_statistics =
        {node_creations = !(#creations fields),
         node_accesses = !(#accesses fields),intern_hits = !(#hits fields),
         intern_misses = !(#misses fields),total_nodes = !(#next g)}
        in (result,counts) end
    end
  fun descendant g scope ancestor =
    if scope = ancestor then true else
    case #parent (scope_frame g scope) of NONE => false
      | SOME parent => descendant g parent ancestor
  fun scope_visible g active required =
    (check_scope g active;
     if !(#active (scope_frame g required)) then descendant g active required
     else false)
  (* DATA invalidation witness, not admission or Work credit. Old node
     geometry is immutable. Every publication that can change an existing
     guard's registry lookup, and every scope retirement, advances it. *)
  fun validation_change (g : graph) =
    #validation_changes g := !(#validation_changes g) + 1
  fun validation_revision (g : graph) caller =
    (check_scope g caller;!(#validation_changes g))
  fun scope_retirement_epoch (g : graph) caller =
    (check_scope g caller;!(#scope_retirements g))
  fun close_scope (g : graph) (Scope {owner,id}) =
    let
        (* Retirement is cleanup, not a productive semantic lookup. It must
           work after the captured meter or Type/Term epoch has retired.
           Authenticate THIS exact frame without reopening paid indices or
           touching any other graph/store. Ordinary scope_frame stays paid. *)
        val _ = if owner = #owner g then () else
          raise ERR "scope" "scope belongs to a different graph"
        val frame = case R.peek_int (!(#scopes g),id) of
            SOME frame => frame
          | NONE => raise ERR "scope" "unknown scope"
        (* Allocate the unbounded next witness BEFORE changing frame state.
           Foreign scope failure cannot advance another graph's witness. *)
        val next = !(#scope_retirements g) + 1
    in validation_change g;
       #active frame := false;#scope_retirements g := next end
  fun entry (g : graph) (Node {owner,id}) : entry =
    case #indices g of
        LegacyIndices _ =>
          if owner <> #owner g then
            raise ERR "node" "node belongs to a different graph"
          else (case R.peek_int (!(#nodes g), id) of
              SOME result => (observe_node g #accesses;result)
            | NONE => raise ERR "node" "unknown node")
      | PaidIndices p =>
          let val meter= #meter p
              val _=R.scope_meter_charge meter 64
              val _=if owner= #owner g then () else
                raise ERR "node" "node belongs to a different graph"
              val _=check_scope g (#root p)
          in case R.scope_lookup_int meter (!(#nodes g),id) of
              SOME result => (observe_node g #accesses;result)
            | NONE => raise ERR "node" "unknown node" end
  fun node_scope g node = #scope (entry g node)
  fun type_of g node = #ty (entry g node)
  fun type_id g node = #type_id (entry g node)
  fun representative g node = #term (entry g node)
  fun view g node = #view (entry g node)
  fun source_anchor g node = !(#source (entry g node))
  fun origin g node = if Option.isSome (source_anchor g node) then
      ImportedSource else ConstructedSyntax

  fun usable g scope node =
    let val fields = entry g node in
      if scope_visible g scope (#scope fields) then () else
        raise ERR "scope" "node is outside the active scope"
    end

  type paid_index_snapshot =
    {types:int R.graph_key_map,keys:node R.graph_key_map,
     recent:(Type.hol_type * int) list,nodes:entry R.int_map,
     scopes:frame R.int_map,reserved:R.string_set,next:int,
     next_scope:int,retirements:IntInf.int,revision:IntInf.int}
  fun paid_indices_live (g:graph) (p:paid_index_state) =
    (R.scope_meter_charge (#meter p) 128;
     if #owner p= #owner g then () else
       raise ERR "paid_indices" "different graph owner";
     if #root p=root_scope g then () else
       raise ERR "paid_indices" "different original root";
     if Type.type_epoch ()= #epoch p andalso
         Term.term_epoch ()= #symbols p then () else
       raise ERR "paid_indices" "Type or Term epoch changed";
     check_scope g (#root p))
  fun validate_semantic_scope (g:graph) scope =
    (check_scope g scope;
     case #indices g of LegacyIndices _ => ()
       | PaidIndices p => paid_indices_live g p)
  fun paid_index_snapshot (g:graph) (p:paid_index_state) =
    (paid_indices_live g p;
     R.scope_meter_charge (#meter p) 128;
     {types= !(#types p),keys= !(#keys p),recent= !(#recent p),
      nodes= !(#nodes g),scopes= !(#scopes g),reserved= !(#reserved g),
      next= !(#next g),next_scope= !(#next_scope g),
      retirements= !(#scope_retirements g),
      revision= !(#validation_changes g)} : paid_index_snapshot)
  fun paid_index_close (g:graph) (p:paid_index_state)
      (saved:paid_index_snapshot) =
    (paid_indices_live g p;
     R.scope_meter_charge (#meter p) 128;
     if R.scope_same_graph_key (#meter p) (#types saved,!(#types p))
         andalso R.scope_same_graph_key (#meter p)
           (#keys saved,!(#keys p)) andalso
         Portable.pointer_eq (#recent saved,!(#recent p)) andalso
         R.same_int (#nodes saved,!(#nodes g)) andalso
         R.same_int (#scopes saved,!(#scopes g)) andalso
         R.same_string (#reserved saved,!(#reserved g)) andalso
         #next saved= !(#next g) andalso
         #next_scope saved= !(#next_scope g) andalso
         #retirements saved= !(#scope_retirements g) andalso
         #revision saved= !(#validation_changes g) then () else
       raise ERR "paid_indices" "semantic roots changed")
  fun paid_first_indices (g:graph) meter =
    case #indices g of
        LegacyIndices _ =>
          raise ERR "paid_indices" "paid original graph required"
      | PaidIndices p =>
          (R.scope_meter_charge meter 32;
           if R.same_scope_meter (meter,#meter p) then () else
             raise ERR "paid_indices" "different original meter";
           paid_indices_live g p;p)
  fun semantic_entry_charge (g:graph) amount =
    case #indices g of LegacyIndices _ => ()
      | PaidIndices p =>
          (paid_indices_live g p;R.scope_meter_charge (#meter p) amount)
  fun semantic_member_name (g:graph) name =
    case #indices g of
        LegacyIndices _ => R.member_string (!(#reserved g),name)
      | PaidIndices p =>
          (paid_indices_live g p;
           R.scope_meter_charge (#meter p) 32;
           R.scope_member_string (#meter p) (!(#reserved g),name))
  fun legacy_recent_type (state:legacy_index_state) ty =
    let fun seek _ [] = NONE
          | seek previous ((item as (saved,id))::rest) =
              if Portable.pointer_eq (saved,ty) then
                (#recent state := item :: List.revAppend (previous,rest);
                 SOME id)
              else seek (item::previous) rest
    in seek [] (!(#recent state)) end
  fun paid_recent_type (g:graph) (p:paid_index_state) ty =
    let val meter= #meter p
        val saved=paid_index_snapshot g p
        fun rebuild previous tail =
          (R.scope_meter_charge meter 32;
           case previous of [] => tail
             | item::rest => rebuild rest (item::tail))
        fun seek previous current =
          (R.scope_meter_charge meter 32;
           case current of [] => NONE
             | (item as (held,id))::rest =>
                 if Portable.pointer_eq (held,ty) then
                   (case previous of [] => SOME id
                    | _ =>
                      let val _=R.scope_meter_charge meter 16
                          val next=item::rebuild previous rest
                          val _=R.scope_meter_charge meter 128
                          val revision= #revision saved+1
                          val _=paid_index_close g p saved
                      in #recent p := next;
                         #validation_changes g := revision;SOME id end)
                 else seek (item::previous) rest)
    in seek [] (#recent saved) end
  fun recent_type (g:graph) ty =
    case #indices g of LegacyIndices state => legacy_recent_type state ty
      | PaidIndices state => paid_recent_type g state ty
  fun intern_type (g:graph) ty =
    case #indices g of
        LegacyIndices state =>
          (case legacy_recent_type state ty of SOME id => id
           | NONE =>
             let val key=if Type.is_vartype ty then
                   TypeVariable (Type.dest_vartype ty)
                 else TypeOperator (#Tyop (Type.dest_thy_typeid ty),
                   List.map (intern_type g) (#2 (Type.dest_type ty)))
                 val id=case Redblackmap.peek (!(#types state),key) of
                     SOME id => id
                   | NONE =>
                     let val id=Redblackmap.numItems (!(#types state))
                     in #types state := Redblackmap.insert
                          (!(#types state),key,id);id end
                 val _= #recent state := (ty,id):: !(#recent state)
             in id end)
      | PaidIndices state =>
          (case paid_recent_type g state ty of SOME id => id
           | NONE =>
             let val meter= #meter state
                 val _=paid_indices_live g state
                 val _=R.scope_meter_charge meter 64
                 fun children current =
                   (R.scope_meter_charge meter 32;
                    case current of [] => []
                      | child::rest =>
                        let val id=intern_type g child
                            val tail=children rest
                            val _=R.scope_meter_charge meter 8
                        in id::tail end)
                 val key=if Type.is_vartype ty then
                     (R.scope_meter_charge meter 32;
                      R.GraphTypeVariable (Type.dest_vartype ty))
                   else
                     let val _=R.scope_meter_charge meter 64
                         val {Tyop,Args,...}=Type.dest_thy_typeid ty
                         val ids=children Args
                         val _=R.scope_meter_charge meter 16
                     in R.GraphTypeOperator(Tyop,ids) end
                 (* Child-Type progress is retained and witnessed. Only
                    this local parent publication is staged here. *)
                 val saved=paid_index_snapshot g state
                 val _=R.scope_meter_charge meter 64
                 val (id,next)=case R.scope_lookup_graph_key meter
                     (#types saved,key) of
                     SOME id => (id,#types saved)
                   | NONE =>
                       let val id=R.scope_graph_key_count meter (#types saved)
                           val next=R.scope_put_graph_key meter
                             (#types saved,key,id)
                       in (id,next) end
                 val _=R.scope_meter_charge meter 128
                 val recent=(ty,id):: !(#recent state)
                 val revision= #revision saved+1
                 val _=paid_index_close g state saved
             in #types state := next;#recent state := recent;
                #validation_changes g := revision;id end)
  fun paid_node_key meter key =
    (R.scope_meter_charge meter 64;
     case key of
         VariableKey(s,k,n,t) => R.GraphVariable(s,k,n,t)
       | ConstantKey(n,t) => R.GraphConstant(n,t)
       | ApplicationKey(s,l,r) => R.GraphApplication(s,l,r))
  fun paid_node_stage (g:graph) (p:paid_index_state)
      (saved:paid_index_snapshot) (fields:entry) =
    let val meter= #meter p
        val _=R.scope_meter_charge meter 128
        val _=check_scope g (#scope fields)
        val id= #next saved
        val node=Node {owner= #owner g,id=id}
        val next=id+1
        val nodes=R.scope_put_int meter (#nodes saved,id,fields)
    in (node,next,nodes) end
  fun reserve_names (g:graph) variables =
    case #indices g of
        LegacyIndices _ =>
          let fun reserve variable =
                let val name= #1 (Term.dest_var variable)
                in if List.exists
                    (fn (_,allocated) => #1 (Term.dest_var allocated)=name)
                    (R.list_int (!(#placeholders g))) then
                      raise ERR "reserve_names"
                  "frame/schema variable reserved after placeholder allocation"
                   else (validation_change g;
                     #reserved g := R.add_string (!(#reserved g),name)) end
          in List.app reserve variables end
      | PaidIndices p =>
          let val meter= #meter p
              val _=paid_indices_live g p
              fun collision name =
                let val _=R.scope_meter_charge meter 64
                    val table= !(#placeholders g)
                    val bound= !(#next g)
                    fun scan index =
                      (R.scope_meter_charge meter 64;
                       if index=bound then false else
                         case R.scope_lookup_int meter (table,index) of
                             NONE => scan(index+1)
                           | SOME term =>
                               let val _=R.scope_meter_charge meter 64
                                   val held= #1 (Term.dest_var term)
                               in if R.scope_compare_graph_key meter
                                   (R.GraphTypeVariable held,
                                    R.GraphTypeVariable name)=EQUAL
                                  then true else scan(index+1) end)
                in if R.same_int (table,#empty_placeholders p) then false
                   else scan 0 end
              fun reserve current =
                (R.scope_meter_charge meter 64;
                 case current of [] => () | term::rest =>
                   let val name= #1 (Term.dest_var term)
                       val _=if collision name then
                         raise ERR "reserve_names"
                  "frame/schema variable reserved after placeholder allocation"
                         else ()
                       val saved=paid_index_snapshot g p
                       val next=R.scope_add_string meter
                         (#reserved saved,name)
                       val _=R.scope_meter_charge meter 128
                       val revision= #revision saved+1
                       val _=paid_index_close g p saved
                       val _= #reserved g := next
                       val _= #validation_changes g := revision
                   in reserve rest end)
          in reserve variables end
  fun fresh (g:graph) fields =
    case #indices g of
        LegacyIndices _ =>
          let val id= !(#next g)
              val node=Node {owner= #owner g,id=id}
          in validation_change g;#next g := id+1;
             #nodes g := R.put_int (!(#nodes g),id,fields);
             observe_node g #creations;node end
      | PaidIndices p =>
          let val saved=paid_index_snapshot g p
              val (node,next,nodes)=paid_node_stage g p saved fields
              val _=R.scope_meter_charge (#meter p) 128
              val revision= #revision saved+1
              val _=paid_index_close g p saved
          in #nodes g := nodes;#next g := next;
             #validation_changes g := revision;
             observe_node g #creations;node end
  fun intern (g:graph) key fields =
    case #indices g of
        LegacyIndices state =>
          (case Redblackmap.peek (!(#keys state),key) of
              SOME node => (observe_node g #hits;node)
            | NONE =>
                let val _=observe_node g #misses
                    val node=fresh g fields
                in #keys state := Redblackmap.insert
                     (!(#keys state),key,node);node end)
      | PaidIndices p =>
          let val meter= #meter p
              val key=paid_node_key meter key
              val saved=paid_index_snapshot g p
              val found=R.scope_lookup_graph_key meter (#keys saved,key)
              val _=R.scope_meter_charge meter 64
          in case found of
              SOME node =>
                (paid_index_close g p saved;observe_node g #hits;node)
            | NONE =>
                let val (node,next,nodes)=paid_node_stage g p saved fields
                    val keys=R.scope_put_graph_key meter
                      (#keys saved,key,node)
                    (* Every persistent root and commit instruction is
                       admitted before publishing either new root. *)
                    val _=R.scope_meter_charge meter 128
                    val revision= #revision saved+1
                    val _=paid_index_close g p saved
                in #nodes g := nodes;#keys p := keys;#next g := next;
                   #validation_changes g := revision;
                   observe_node g #misses;observe_node g #creations;
                   node end
          end
  fun kind_id RigidSource = 0 | kind_id SolverFlexible = 1
    | kind_id Generated = 2 | kind_id Bound = 3
  fun variable g scope kind term =
    let
      val _ = check_scope g scope
      val _ = semantic_entry_charge g 128
      val scope = case kind of RigidSource => root_scope g | _ => scope
      val (name,ty) = Term.dest_var term
      val tid = intern_type g ty
      val _ = reserve_names g [term]
    in intern g (VariableKey (scope_id scope, kind_id kind, name, tid))
      {scope = scope, ty = ty, type_id = tid, term = term,
       view = Variable (kind,term), raw = SOME 1, inclusive = SOME 1,
       source = ref NONE}
    end
  fun fresh_bound_variable (g : graph) scope lexical =
    let
      val _ = check_scope g scope
      val (requested,ty) = Term.dest_var lexical
      fun available name = not (semantic_member_name g name)
      fun choose () =
        let
          val _ = semantic_entry_charge g 64
          val index = !(#next_bound_name g)
          val _ = #next_bound_name g := index + 1
          val name = requested ^ "_" ^ Int.toString index
        in if available name then name else choose () end
      val name = if available requested then requested else choose ()
    in variable g scope Bound (Term.mk_var (name,ty)) end
  fun fresh_flexible_variable (g : graph) scope lexical =
    let
      val _ = check_scope g scope
      val (requested,ty) = Term.dest_var lexical
      fun choose () =
        let
          val _ = semantic_entry_charge g 64
          val index = !(#next_flexible_name g)
          val _ = #next_flexible_name g := index + 1
          val name = "smt_solver_" ^ requested ^ "_" ^ Int.toString index
        in if semantic_member_name g name then choose ()
           else name end
    in variable g scope SolverFlexible (Term.mk_var (choose (),ty)) end
  fun constant g scope term =
    let
      val _ = check_scope g scope
      val _ = semantic_entry_charge g 128
      val scope = root_scope g
      val {Name,Ty,...} = Term.dest_thy_constid term
      val tid = intern_type g Ty
    in intern g (ConstantKey (Name,tid))
      {scope = scope, ty = Ty, type_id = tid, term = term,
       view = Constant Name, raw = SOME 1, inclusive = SOME 1,
       source = ref NONE}
    end
  fun new_scope (g : graph) parent bindings =
    let
      val _ = check_scope g parent
      fun bind ((term,node),table) =
        let
          val (name,ty) = Term.dest_var term
          val tid = intern_type g ty
          val _ = usable g parent node
          val _ = if tid = type_id g node then () else
            raise ERR "new_scope" "binding type mismatch"
          val _ = reserve_names g [term]
        in Redblackmap.insert (table, (name,tid), node) end
      val table = List.foldl bind
        (Redblackmap.mkDict (pair_compare String.compare Int.compare))
        bindings
      val id = !(#next_scope g)
      val scope = Scope {owner = #owner g, id = id}
    in
      validation_change g;#next_scope g := id + 1;
      #scopes g := R.put_int (!(#scopes g), id,
        {parent = SOME parent, active = ref true, bindings = table}); scope
    end
  (* Retain exact typed lexical aliases at genuine NEW construction. The
     new child's lifetime follows the construction ancestor, while temporary
     lexical frames can close after the parser returns its abstraction. *)
  fun new_construction_scope (g : graph) {lexical,construction} =
    let
      val _ = check_scope g construction
      val _ = check_scope g lexical
      val _ = if scope_visible g lexical construction then () else
        raise ERR "new_construction_scope" "different construction ancestry"
      fun collect current =
        if current = construction then
          Redblackmap.mkDict (pair_compare String.compare Int.compare)
        else
          let val {parent,bindings,...} = scope_frame g current
              val previous = case parent of SOME parent => collect parent
                | NONE => raise ERR "new_construction_scope"
                    "lexical path lost its construction ancestor"
          in Redblackmap.foldl (fn (key,node,table) =>
               (usable g construction node;
                Redblackmap.insert (table,key,node))) previous bindings end
      val table = collect lexical
      val _ = check_scope g lexical
      val _ = check_scope g construction
      val id = !(#next_scope g)
      val scope = Scope {owner = #owner g,id = id}
    in validation_change g;#next_scope g := id+1;
       #scopes g := R.put_int (!(#scopes g),id,
         {parent = SOME construction,active = ref true,bindings = table});
       scope
    end

  fun lookup_binding (g : graph) scope term =
    let
      val key = (#1 (Term.dest_var term), intern_type g (Term.type_of term))
      fun seek scope =
        let val {parent,bindings,...} =
          case R.peek_int (!(#scopes g), scope_id scope) of
            SOME frame => frame | NONE => raise Redblackmap.NotFound
        in case Redblackmap.peek (bindings,key) of SOME node => SOME node
          | NONE => case parent of NONE => NONE | SOME scope => seek scope
        end
    in seek scope end
  fun declaration_variable_key g scope term =
    let
      val _ = check_scope g scope
      val (name,ty) = Term.dest_var term
    in (name,intern_type g ty) end
  fun resolve_variable g scope term =
    (check_scope g scope;
     case lookup_binding g scope term of SOME node => node
       | NONE => variable g (root_scope g) RigidSource term)
  fun resolve_reference g scope term default =
    let
      val _ = check_scope g scope
      val _ = usable g scope default
      val _ = if intern_type g (Term.type_of term) = type_id g default then ()
        else raise ERR "resolve_reference" "declaration type mismatch"
      val result = case lookup_binding g scope term of
          SOME node => node | NONE => default
      val _ = usable g scope result
    in result end
  fun application g scope (operator,operand) =
    let
      val _ = check_scope g scope
      val _ = semantic_entry_charge g 128
      val _ = usable g scope operator
      val _ = usable g scope operand
      val left = entry g operator
      val right = entry g operand
      val (domain,range) = Type.dom_rng (#ty left)
      val _ = if intern_type g domain = #type_id right then () else
        raise ERR "application" "application operand type mismatch"
      val tid = intern_type g range
      val term = SmtReplayLeafProof.application (semantic_entry_charge g)
        (#term left) (#term right)
    in intern g
      (ApplicationKey (scope_id scope,node_id operator,node_id operand))
      {scope = scope, ty = range, type_id = tid, term = term,
       view = Application (operator,operand),
       raw = sum (#raw left) (#raw right),
       inclusive = sum (#inclusive left) (#inclusive right), source = ref NONE}
    end

  (* A deliberately fixed Boolean grammar: general constructors may contain
     arbitrarily large Types/strings and cannot use this quotation. Each
     constructor below interns at most seven fixed Boolean Type incidences
     (arity <= 2), and adds at most one node. Caller separately prepays native
     Term.mk_comb operand/type walks; these graph fees do not inspect operand
     syntax. The debit is bookkeeping, never proof or native admission. *)
  fun implication_with_graph_debit (g:graph) scope debit premises target =
    let
      (* Red-black height <= 2 ceil(log2(n+1)); include empty leaves
         and prospective growth. Quote arithmetic preparation too. *)
      fun height count =
        let fun bits n = (debit 4;
              if n = 0 then 1 else 2 + bits (n div 2))
        in bits (IntInf.fromInt count + 8) end
      fun prepay annotations =
        (debit 32;
         case #indices g of PaidIndices _ => () (* already internally paid *)
         | LegacyIndices state =>
           let
             val nodes = height (!(#next g))
             val keys = height (Redblackmap.numItems (!(#keys state)))
             val types = height (Redblackmap.numItems (!(#types state)))
             val scopes = height (!(#next_scope g))
             (* Count the actual caller ancestry, not unrelated siblings.
                Pay each planning lookup before reading the parent. *)
             fun ancestry current =
               (debit (128 * (scopes + 1));
                case #parent (scope_frame g current) of NONE => 1
                  | SOME parent => 1 + ancestry parent)
             val path = ancestry scope
             fun children ty =
               (debit 16;ty :: (if Type.is_vartype ty then [] else
                 List.concat (List.map children (#2 (Type.dest_type ty)))))
             val needed = List.concat (List.map children annotations)
             (* Every future recent lookup/rebuild is within this prefix,
                plus <= seven newly cached fixed Types. Once the Boolean
                Types are warm, unrelated old Types are NOT rescanned. *)
             fun remove held [] = (debit 2;[])
               | remove held (ty::rest) =
                   (debit 4;if Portable.pointer_eq (held,ty) then
                      remove held rest else ty :: remove held rest)
             fun recent [] _ = (debit 2;0:IntInf.int)
               | recent _ [] = (debit 2;0)
               | recent ((ty,_)::rest) pending =
                   (debit 4;1 + recent rest (remove ty pending))
             val cached = recent (!(#recent state)) needed
             (* Covers lookups, persistent insert/rebalance, node/observer
                bookkeeping, fixed wrappers, and each recent scan/rebuild.
                Scope visibility walks at most path frames. Fixed Type keys
                compare at most two child IDs. This is a prospective upper
                bound, not a flat fee or credit for later native work. *)
           in debit (128 * (32 + nodes + keys + path * (scopes + 1) +
                7 * (types + cached + 7))) end)
      fun apply (left,right) =
        let
          (* The private left operands are ONLY the fixed implication head
             or its partial App. Pay its entry lookup before reading Type. *)
          val _ = debit (128 * (1 + height (!(#next g))))
          val (domain,range) = Type.dom_rng (type_of g left)
          val _ = prepay [domain,range]
        in application g scope (left,right) end
      val _ = prepay [Term.type_of boolSyntax.implication]
      val operator = constant g scope boolSyntax.implication
      fun build [] = (debit 2;target)
        | build (premise::rest) =
            let val _ = debit 4
                val result = build rest
                val partial = apply (operator,premise)
            in apply (partial,result) end
    in build premises end

  (* Hashes are bounded routing hints, never equality claims. Abstractions
     are opaque here; no dest_abs/body/free-variable query occurs. *)
  val physical_hint = SmtReplayImport.pointer_bucket 4 4093
  fun memo_peek (g : graph) scope term =
    case List.find (fn (saved,frame,_) => frame = scope_id scope andalso
          Portable.pointer_eq (saved,term))
        (Array.sub (#imports g, physical_hint term)) of
      SOME (_,_,result) => SOME result | NONE => NONE
  fun memo_save (g : graph) scope (source : source) =
    let val bucket = physical_hint (#original source) in
      validation_change g;
      Array.update (#imports g,bucket,
        (#original source,scope_id scope,source) ::
          Array.sub (#imports g,bucket))
    end
  fun source_for g original node theorem : source =
    let
      val (left,right) = Term.dest_eq (Thm.concl theorem)
      val _ = if List.null (Thm.hyp theorem) andalso
          Portable.pointer_eq (original,left) andalso
          Portable.pointer_eq (representative g node,right) then () else
        raise ERR "source_for" "source bridge lost its exact endpoints"
      val source = {node = node,original = original,bridge = theorem}
      val anchor = #source (entry g node)
      val _ = if Option.isSome (!anchor) then () else
        (validation_change g;anchor := SOME source)
    in source end
  (* The paid Type summary selects a checked proof, never an equality
     verdict or new admission limit. Small native comparisons stay native:
     they must not incur the cold full-GC cost of runtime sharing. *)
  fun atomic_equality g left right =
    if Portable.pointer_eq (left,right) then Thm.REFL left
    else if SmtReplayLeafProof.same_atom left right andalso
        (Thm.kernelid = "expknl" orelse not (Portable.pointer_eq
          (Term.type_of left, Term.type_of right))) andalso
        (if Thm.kernelid = "expknl" then
           SmtReplayLeafProof.large_type (semantic_entry_charge g)
             (Term.type_of left)
         else SmtReplayLeafProof.large_type_pair (semantic_entry_charge g)
           (Term.type_of left) (Term.type_of right)) then
      ((if Thm.kernelid = "expknl" andalso Term.is_var left andalso
           Portable.pointer_eq (Term.type_of left, Term.type_of right) then
          SmtReplayLeafProof.shared_variable left right
        else SmtReplayLeafProof.redex_equality left right)
       handle Feedback.HOL_ERR _ => raise Feedback.mk_HOL_ERR
         "Thm" "ALPHA" "Terms not alpha-convertible")
    else Thm.ALPHA left right

  fun import_atom g scope term =
    let
      val node = if Term.is_var term then
          case lookup_binding g scope term of SOME node => node
            | NONE => variable g (root_scope g) RigidSource term
        else constant g scope term
      (* Environments may denote different terms. Parser elaboration is not
         permission to invent a source bridge; the kernel still checks it. *)
    in (node,atomic_equality g term (representative g node)) end

  fun align_application original left right canonical =
    let
      val theorem = Thm.MK_COMB (left,right)
      val (rebuilt,rebuilt_right) = Term.dest_eq (Thm.concl theorem)
    in Thm.TRANS (Thm.ALPHA original rebuilt)
      (Thm.TRANS theorem (Thm.ALPHA rebuilt_right canonical)) end

  datatype import_plan = ImportPlan of
    {graph : graph,scope : scope,maximum : int,original : Term.term,
     types : Type.hol_type list}
  (* Public applications only; abstractions remain opaque and unopened.
     Count the same exposed DAG misses as import, before any alpha bridge. *)
  fun plan_imports g scope maximum originals =
    let
      val _ = check_scope g scope
      val _ = if maximum >= 1 then () else
        raise ERR "import" "nonpositive application import budget"
      val buckets = 4093
      val seen = Array.array (buckets,[] : Term.term list)
      val observations = ref 0
      val types = ref ([] : Type.hol_type list)
      fun visit term = case memo_peek g scope term of SOME _ => ()
        | NONE =>
          let val bucket = SmtReplayImport.pointer_bucket 4 buckets term
              val held = Array.sub (seen,bucket)
          in if List.exists (fn old => Portable.pointer_eq (old,term)) held
             then () else
             let
               val _ = observations := !observations+1
               val _ = if !observations <= maximum then () else
                 raise ERR "import"
                   "application import DAG budget exhausted"
               val _ = Array.update (seen,bucket,term :: held)
               val _ = types := Term.type_of term :: !types
             in if Term.is_comb term then
                  let val (f,x) = Term.dest_comb term in visit f;visit x end
                else if Term.is_var term orelse Term.is_const term orelse
                    Term.is_abs term then () else
                  raise ERR "import" "unexpected public term constructor"
             end
          end
      fun plan original =
        let val _ = observations := 0
            val _ = types := []
            val _ = visit original
        in ImportPlan {graph = g,scope = scope,maximum = maximum,
          original = original,types = List.rev (!types)} end
    in List.map plan originals end
  fun plan_import g scope maximum original =
    List.hd (plan_imports g scope maximum [original])
  fun import_types (ImportPlan {graph,scope,types,...}) =
    (check_scope graph scope;types)
  fun execute_import
      (ImportPlan {graph = g,scope,maximum,original,...}) =

    let
      val _ = check_scope g scope
      val _ = if maximum >= 1 then () else
        raise ERR "import" "nonpositive application import budget"
      val observations = ref 0
      fun visit term = case memo_peek g scope term of
          SOME source => source
        | NONE =>
          let
            val _ = observations := !observations + 1
            val _ = if !observations <= maximum then () else
              raise ERR "import" "application import DAG budget exhausted"
            val (node,theorem) =
              if Term.is_comb term then
                let
                  val (left,right) = Term.dest_comb term
                  val l = visit left and r = visit right
                  val node = application g scope (#node l,#node r)
                in (node,align_application term (#bridge l) (#bridge r)
                      (representative g node)) end
              else if Term.is_var term orelse Term.is_const term then
                import_atom g scope term
              else if Term.is_abs term then
                let
                  val ty = Term.type_of term
                  val node = fresh g
                    {scope = scope, ty = ty, type_id = intern_type g ty,
                     term = term, view = OpaqueRetained,
                     raw = NONE, inclusive = NONE, source = ref NONE}
                in (node,Thm.REFL term) end
              else raise ERR "import" "unexpected public term constructor"
            val source = source_for g term node theorem
            val _ = memo_save g scope source
          in source end
    in visit original end

  fun import g scope maximum original =
    execute_import (plan_import g scope maximum original)

  fun retain_source g scope original =
    (check_scope g scope;
     case memo_peek g scope original of SOME source => source
     | NONE =>
       let
         val ty = Term.type_of original
         val node = fresh g
           {scope=scope,ty=ty,type_id=intern_type g ty,term=original,
            view=OpaqueRetained,raw=NONE,inclusive=NONE,source=ref NONE}
         val source = source_for g original node (Thm.REFL original)
         val _ = memo_save g scope source
       in source end)

  fun reachable_using descend_binders g roots =
    let
      fun children node = case view g node of
          Application (left,right) => [left,right]
        | AdmittedBinder {binder,body,...} =>
            if descend_binders then [binder,body] else []
        | _ => []
      fun loop [] _ result = List.rev result
        | loop (node::rest) visited result =
          if Redblackset.member (visited,node_id node) then
            (ignore (entry g node); loop rest visited result)
          else loop (children node @ rest)
            (Redblackset.add (visited,node_id node)) (node::result)
    in loop roots (Redblackset.empty Int.compare) [] end
  val reachable = reachable_using true
  val block_reachable = reachable_using false
  fun dag_nodes g roots = List.length (reachable g roots)
  fun partial_scope_live g scope =
    let val {parent,active,...} = scope_frame g scope
    in !active andalso (case parent of NONE => true
      | SOME outer => partial_scope_live g outer) end
  fun partial_record_live (g : graph)
      (ClosureRecord {owner,node_frame,creation,backing,...}) =
    owner = #owner g andalso partial_scope_live g node_frame andalso
    partial_scope_live g (#declaring_scope creation) andalso
    partial_scope_live g (#binder_frame creation) andalso
    partial_scope_live g (#body_frame creation) andalso
    (case backing of NONE => true | SOME older => partial_record_live g older)
  fun opaque_profile_data (g : graph) scope
      (OpaqueProfile {owner,scope = held,node,original,raw,inc,ann,ty,
                      type_bytes,types,guard,...}) =
    if owner = #owner g then
      (check_scope g scope;usable g scope node;check_scope g held;
       if scope_visible g scope held andalso
           Portable.pointer_eq (original,representative g node) then () else
         raise ERR "opaque_profile_data" "different retained frame/term";
       guard ();
       {node = node,raw = raw,inc = inc,ann = ann,ty = ty,
        type_bytes = type_bytes,types = types})
    else raise ERR "opaque_profile_data" "foreign graph profile"
  fun opaque_profile_for (g : graph) scope node =
    let val _ = check_scope g scope val _ = usable g scope node
        val rows = Option.getOpt
          (Redblackmap.peek (!(#partial_profiles g),node_id node),[])
        fun choose [] answer = answer
          | choose ((profile as OpaqueProfile {scope = held,ready,...})::rest)
              answer =
              if ready () andalso scope_visible g scope held then
                (ignore (opaque_profile_data g scope profile);
                 choose rest (case answer of NONE => SOME profile
                   | SOME _ => answer))
              else choose rest answer
    in choose rows NONE end

  fun opaque_type_projection_data (g : graph) scope receipt depth =
    let val (node,original,path,guard) = case receipt of
          OpaqueTypeProjection {profile,path} =>
            let val data = opaque_profile_data g scope profile
                val OpaqueProfile {original,...} = profile
            in (#node data,original,path,
              fn () => ignore (opaque_profile_data g scope profile)) end
        | OpenedTypeProjection
            {owner,scope = held,node,original,path,guard,...} =>
            (if owner = #owner g andalso held = scope then () else
               raise ERR "opaque_type_projection" "foreign opened projection";
             check_scope g scope;usable g scope node;guard ();
             if Portable.pointer_eq (original,representative g node) then ()
             else raise ERR "opaque_type_projection" "raw root changed";
             (node,original,path,guard))
        val _ = if depth >= (0 : IntInf.int) then () else
          raise ERR "opaque_type_projection" "negative binder depth"
        fun first (ProjectionAtom {term,...}) = term
          | first (ProjectionApplication (term,_)) = term
          | first (ProjectionBinder (term,_,_)) = term
        val _ = if Portable.pointer_eq (first path,original) then () else
          raise ERR "opaque_type_projection" "different actual raw root"
        fun walk depth (ProjectionAtom {variable,...}) =
              {work = if variable then 1+depth else 1,
               visits = 1,binder_types = []}
          | walk depth (ProjectionApplication (_,child)) =
              let val data = walk depth child
              in {work = 2 + #work data,visits = plus 1 (#visits data),
                  binder_types = #binder_types data} end
          | walk depth (ProjectionBinder (_,domain,child)) =
              let val data = walk (depth+1) child
              in {work = 2 + #work data,visits = plus 1 (#visits data),
                  binder_types = domain :: #binder_types data} end
        val answer = walk depth path val _ = guard ()
    in {node = node,work = #work answer,visits = #visits answer,
        binder_types = #binder_types answer} end
  fun opaque_type_projection_for (g : graph) scope node =
    let val _ = check_scope g scope val _ = usable g scope node
        val rows = Option.getOpt
          (Redblackmap.peek (!(#partial_projections g),node_id node),[])
        fun available (OpaqueTypeProjection
              {profile = OpaqueProfile {scope = held,ready,...},...}) =
              ready () andalso scope_visible g scope held
          | available (OpenedTypeProjection {scope = held,ready,...}) =
              held = scope andalso ready ()
        fun choose [] answer = answer
          | choose (receipt :: rest) answer =
              if available receipt then
                (ignore (opaque_type_projection_data g scope receipt 0);
                 choose rest (case answer of NONE => SOME receipt
                   | SOME _ => answer))
              else choose rest answer
    in choose rows NONE end

  (* Count availability is authenticated by actual no-op scans, not a
     caller number. Ordinary unknown metrics stay unknown. Cached first
     raw/opened provenance and free-variable summaries remain unchanged. *)
  fun partial_metric_program observe (g : graph) metric root =
    let val _ = observe ()
        val caller = node_scope g root
        fun compare pair = (observe ();Int.compare pair)
        val _ = observe ()
        val memo = ref (Redblackmap.mkDict compare)
        fun retained current =
          let val _ = observe ()
              val rows = Option.getOpt
                (Redblackmap.peek (!(#partial_profiles g),node_id current),[])
              fun choose [] answer = (observe ();answer)
                | choose ((profile as OpaqueProfile {scope,ready,...})::rest)
                    answer =
                    (observe ();
                     if not (ready ()) orelse
                        not (scope_visible g caller scope) then
                      choose rest answer
                    else let val _ = observe ()
                        val data = opaque_profile_data g caller profile
                        val _ = observe ()
                        val value = case metric of RawNodes => #raw data
                          | BinderInclusiveNodes => #inc data
                    in choose rest (case answer of NONE => SOME value
                      | SOME old => if old = value then answer else
                          raise ERR "partial_metric" "profile count differs")
                    end)
          in choose rows NONE end
        fun visit current =
          let val _ = observe ()
              val fields = entry g current val key = node_id current
              val _ = observe ()
          in case Redblackmap.peek (!memo,key) of SOME value => value
            | NONE =>
              let val _ = observe ()
                  val saved = case metric of RawNodes => #raw fields
                    | BinderInclusiveNodes => #inclusive fields
                  val value = case saved of SOME _ => saved
                    | NONE => (case #view fields of
                        OpaqueRetained => retained current
                      | Application (left,right) =>
                          sum (visit left) (visit right)
                      | _ => NONE)
                  val _ = observe ()
                  val _ = memo := Redblackmap.insert (!memo,key,value)
              in value end
          end
    in visit root end
  fun partial_metric g metric root =
    partial_metric_program (fn () => ()) g metric root

  fun unfolded_nodes_program observe g metric limit node =
    let
      val _ = observe ()
      val _ = if limit >= 0 andalso limit < cap then () else
        raise ERR "unfolded_nodes" "invalid size limit"
      val _ = observe ()
      val fields = entry g node
      val cached = case metric of RawNodes => #raw fields
                                | BinderInclusiveNodes => #inclusive fields
      val _ = observe ()
      val size = case cached of SOME _ => cached
        | NONE => partial_metric_program observe g metric node
    in Option.map (fn n => (observe ();Int.min (limit+1,n))) size end
  fun unfolded_nodes g metric limit node =
    unfolded_nodes_program (fn () => ()) g metric limit node
  (* Metadata only. The observer pays actual traversal and registry work;
     no native syntax is opened and no metric/profile is created. *)
  fun unfolded_nodes_observed observe g metric limit node =
    unfolded_nodes_program observe g metric limit node
  exception UnknownFreeVariables
  datatype dependency_event = DependencyVisit | DependencyCompare
    | DependencyExcluded of int list | DependencyVisited of int list
    | DependencyVariable of int | DependencyType of int
  (* Keep event construction and instrumented comparators off the ordinary
     path. Only the explicitly observed entry points install those actions. *)
  fun free_variable_nodes_using
      {compare,visit,excluded_items,visited_key,variable} g root =
    let
      val initial = Redblackset.empty compare
      fun loop [] _ variables =
            SOME (List.map #2 (Redblackmap.listItems variables))
        | loop ((node,excluded)::rest) visited variables =
          let
            val _ = visit ()
            val fields = entry g node
            val exclusions = Redblackset.listItems excluded
            val _ = excluded_items exclusions
            val key = (node_id node,exclusions)
          in if Redblackset.member (visited,key) then
              loop rest visited variables
            else
              let
                val visited = Redblackset.add (visited,key)
                val _ = visited_key exclusions
                fun next pending vars = loop pending visited vars
              in case #view fields of
                  OpaqueRetained => raise UnknownFreeVariables
                | Variable _ =>
                    next rest
                      (if Redblackset.member (excluded,node_id node) then
                         variables else
                           (variable (node_id node);
                            Redblackmap.insert
                              (variables,node_id node,node)))
                | Application (left,right) =>
                    next ((left,excluded)::(right,excluded)::rest) variables
                | AdmittedBinder {binder,body,...} =>
                    next ((body,Redblackset.add
                      (excluded,node_id binder))::rest) variables
                | Constant _ => next rest variables
              end
          end
    in loop [(root,initial)]
      (Redblackset.empty
        (pair_compare compare (list_compare compare)))
      (Redblackmap.mkDict compare)
    end handle UnknownFreeVariables => NONE
  val free_variable_nodes = free_variable_nodes_using
    {compare = Int.compare,visit = fn () => (),excluded_items = fn _ => (),
     visited_key = fn _ => (),variable = fn _ => ()}
  fun free_variable_nodes_observed observe = free_variable_nodes_using
    {compare = fn pair => (observe DependencyCompare; Int.compare pair),
     visit = fn () => observe DependencyVisit,
     excluded_items = fn ids => observe (DependencyExcluded ids),
     visited_key = fn ids => observe (DependencyVisited ids),
     variable = fn id => observe (DependencyVariable id)}
  fun free_variables_using {query,read_type,compare_name,compare_type} g root =
    case query g root of NONE => Unknown
    | SOME nodes =>
      let
        fun collect (node,variables) =
          let val term = representative g node
              val ty = read_type g node
          in Redblackmap.insert (variables,
            (#1 (Term.dest_var term),ty),term) end
      in Known (List.map #2 (Redblackmap.listItems
        (List.foldl collect (Redblackmap.mkDict
          (pair_compare compare_name compare_type)) nodes))) end
  val free_variables = free_variables_using
    {query = free_variable_nodes,read_type = type_id,
     compare_name = String.compare,compare_type = Int.compare}
  fun free_variables_observed observe = free_variables_using
    {query = free_variable_nodes_observed observe,
     read_type = fn g => fn node =>
       let val ty = type_id g node
       in observe (DependencyType ty); ty end,
     compare_name = fn pair => (observe DependencyCompare;
       String.compare pair),
     compare_type = fn pair => (observe DependencyCompare; Int.compare pair)}

  fun placeholder (g : graph) node =
    let val fields = entry g node
        val _ = check_scope g (#scope fields)
    in
      case R.peek_int (!(#placeholders g),node_id node) of
        SOME term => term
      | NONE =>
        let
          fun choose () =
            let
              val id = !(#next_name g)
              val _ = #next_name g := id + 1
              val name = "__smt_replay_" ^ Int.toString id
            in if semantic_member_name g name then choose ()
               else name end
          val name = choose ()
          val term = Term.mk_var (name,#ty fields)
          val _ = validation_change g
          val _ = #reserved g := R.add_string (!(#reserved g),name)
          val _ = validation_change g
          val _ = #placeholders g := R.put_int
            (!(#placeholders g),node_id node,term)
        in term end
    end

  fun reserve_schema_holes (g : graph) pairs =
    let
      fun reserve (term,node) =
        let val fields = entry g node
            val _ = check_scope g (#scope fields)
        in case R.peek_int (!(#placeholders g),node_id node) of
            SOME owned =>
              if Portable.pointer_eq (term,owned) then ()
              else reserve_names g [term]
          | NONE => reserve_names g [term]
        end
    in List.app reserve pairs end

  fun abstraction g scope maximum (binder,body) =
    let
      val _ = check_scope g scope
      val binder_fields = entry g binder
      val _ = if scope_visible g (#scope binder_fields) scope then () else
        raise ERR "abstraction" "binder frame is outside the enclosing scope"
      val _ = case #view binder_fields of Variable (Bound,_) => ()
        | _ => raise ERR "abstraction" "binder is not a scoped bound variable"
      val body_scope = node_scope g body
      val _ = if scope_visible g (#scope binder_fields) body_scope orelse
          scope_visible g body_scope (#scope binder_fields) then () else
        raise ERR "abstraction" "body is outside the declaring binder frame"
      val body_fields = entry g body
      val raw = Option.map (plus 1) (#raw body_fields)
      val inclusive = sum (#inclusive binder_fields) (#inclusive body_fields)
      val _ = case raw of SOME size =>
          if size <= maximum then () else
            raise ERR "abstraction" "bounded binder budget exhausted"
        | NONE => raise ERR "abstraction" "opaque binder body is unadmitted"
      val binder_name = #1 (Term.dest_var (#term binder_fields))
      val _ = case free_variable_nodes g body of NONE =>
          raise ERR "abstraction" "unknown free-variable binder body"
        | SOME variables => List.app (fn node =>
            (if node = binder then () else usable g scope node;
            if node <> binder andalso
               type_id g node = #type_id binder_fields andalso
               #1 (Term.dest_var (representative g node)) = binder_name then
              raise ERR "abstraction"
                "binder captures a different graph variable"
            else ())) variables
      val term = Term.mk_abs (#term binder_fields,#term body_fields)
      val ty = Type.mk_type ("fun",[#ty binder_fields,#ty body_fields])
    in fresh g
      {scope = scope, ty = ty, type_id = intern_type g ty, term = term,
       view = AdmittedBinder {binder = binder,body = body,
                             frame = #scope binder_fields},
       raw = raw, inclusive = inclusive, source = ref NONE}
    end

  (* An old abstraction has no body-frame argument; never infer that frame
     from an ancestor constant/body node. This additive constructor records
     the explicit actual lexical frame at this NEW construction only. *)
  fun recorded_abstraction (g : graph) scope maximum
      {binder,body,body_frame} =
    let
      val _ = check_scope g scope
      val _ = check_scope g body_frame
      val binder_frame = node_scope g binder
      val _ = check_scope g binder_frame
      val _ = if scope_visible g body_frame binder_frame then () else
        raise ERR "recorded_abstraction" "body frame outside binder frame"
      val _ = usable g body_frame binder
      val _ = usable g body_frame body
      val node = abstraction g scope maximum (binder,body)
      val creation : binder_closure_creation =
        {identity = ref (),node = node,declaring_scope = scope,
         binder = binder,binder_term = representative g binder,
         binder_frame = binder_frame,body = body,body_frame = body_frame}
      val record = ClosureRecord {identity = ref (),owner = #owner g,
        node = node,node_frame = scope,creation = creation,backing = NONE}
      val next = Redblackmap.insert (!(#binder_closures g),node_id node,record)
      val _ = validation_change g
      val _ = #binder_closures g := next
    in node end

  (* Copy ONLY an already recorded creation; no lookup by Term/raw spelling.
     New node scope and original creation/backing scopes remain distinct.
     A retired backing still cannot pass the read-only closure guards. *)
  fun carry_binder_closure (g : graph) scope original target =
    if original = target then () else
    case Redblackmap.peek (!(#binder_closures g),node_id original) of
        NONE => ()
      | SOME (record as ClosureRecord {creation,...}) =>
          let val copied = ClosureRecord {identity = ref (),owner = #owner g,
                node = target,node_frame = scope,creation = creation,
                backing = SOME record}
              val next = Redblackmap.insert
                (!(#binder_closures g),node_id target,copied)
          in validation_change g;#binder_closures g := next end

  fun rehome g scope original =
    let
      val _ = check_scope g scope
      val memo = ref (Redblackmap.mkDict Int.compare)
      fun visit node = case Redblackmap.peek (!memo,node_id node) of
          SOME source => source
        | NONE =>
            let
              val fields = entry g node
              val term = #term fields
              val (result,bridge) =
                if scope_visible g scope (#scope fields) then
                  (node,Thm.REFL term)
                else case #view fields of
                    Application (operator,operand) =>
                      let val left = visit operator val right = visit operand
                          val result = application g scope
                            (#node left,#node right)
                      in (result,align_application term (#bridge left)
                        (#bridge right) (representative g result)) end
                  | AdmittedBinder _ =>
                      let
                        val variables = case free_variable_nodes g node of
                            SOME variables => variables
                          | NONE => raise ERR "rehome"
                              "unknown admitted binder dependencies"
                        val _ = List.app (usable g scope) variables
                        val result = fresh g
                          {scope = scope,ty = #ty fields,
                           type_id = #type_id fields,term = term,
                           view = #view fields,raw = #raw fields,
                           inclusive = #inclusive fields,source = ref NONE}
                      in (result,Thm.REFL term) end
                  | _ => raise ERR "rehome"
                      "retained node cannot escape its declaring frame"
              val source = source_for g term result bridge
              val _ = carry_binder_closure g scope node result
              val _ = memo := Redblackmap.insert (!memo,node_id node,source)
            in source end
    in visit original end

  (* Every index entry is the SAME immutable first successful admission.
     Lookup is integer-keyed and checks actual graph/node metadata. It never
     searches a raw term table, creates a view or decodes a theorem. *)
  fun indexed_binder_origin (g : graph) node =
    let
      val _ = ignore (entry g node)
      val admission = case Redblackmap.peek
          (!(#binder_origins g),node_id node) of SOME value => value
        | NONE => raise ERR "binder_origin" "missing admission node index"
      val _ = if #owner admission = #owner g andalso
          #node admission = node andalso
          #scope admission = node_scope g node andalso
          #node (#first_whole admission) = node andalso
          Portable.pointer_eq (#first_input admission,
            #original (#first_whole admission)) then () else
        raise ERR "binder_origin" "inconsistent admission node index"
    in admission end

  fun admit_binder_record (g : graph) scope maximum original =
    let
      val _ = check_scope g scope
      val _ = if Term.is_abs original then () else
        raise ERR "admit_binder" "not an abstraction"
      val _ = case SmtReplayImport.bounded_raw_size maximum original of
          SOME _ => ()
        | NONE => raise ERR "admit_binder" "bounded binder budget exhausted"
      val table = Option.getOpt
        (Redblackmap.peek (!(#binders g),scope_id scope),
         Redblackmap.mkDict Term.compare)
    in case Redblackmap.peek (table,original) of
        SOME (admission : admitted_binder_origin) =>
          let val node = #node admission
              val indexed = indexed_binder_origin g node
              val _ = if #identity indexed = #identity admission then () else
                raise ERR "admit_binder" "cached first origin differs"
          in (source_for g original node
            (Thm.ALPHA original (representative g node)),admission) end
      | NONE =>
        let
          val (binder_term,body_term) = Term.dest_abs original
          val frame = new_scope g scope []
          val binder = variable g frame Bound binder_term
          val body_frame = new_scope g frame [(binder_term,binder)]
          fun bounded term = case memo_peek g body_frame term of
              SOME source =>
                (case view g (#node source) of OpaqueRetained => compute term
                 | _ => source)
            | NONE => compute term
          and compute term =
            let val source =
              if Term.is_abs term then
                #1 (admit_binder_record g body_frame maximum term)
              else if Term.is_comb term then
              let
                val (left,right) = Term.dest_comb term
                val l = bounded left and r = bounded right
                val node = application g body_frame (#node l,#node r)
              in source_for g term node
                (align_application term (#bridge l) (#bridge r)
                  (representative g node)) end
              else import g body_frame maximum term
              val _ = memo_save g body_frame source
            in source end
          val body = bounded body_term
          val node = recorded_abstraction g scope maximum
            {binder = binder,body = #node body,body_frame = body_frame}
          val theorem = Thm.TRANS
            (Thm.ALPHA original
              (Term.mk_abs (binder_term,#original body)))
            (Thm.TRANS (Thm.ABS binder_term (#bridge body))
              (Thm.ALPHA
                (Term.mk_abs (binder_term,representative g (#node body)))
                (representative g node)))
          val source = source_for g original node theorem
          (* All these are the actual held values used above. Publish only
             AFTER the whole source bridge passes its endpoint checks. *)
          val admission : admitted_binder_origin =
            {identity = ref (),owner = #owner g,scope = scope,
             first_input = original,
             binder_term = binder_term,binder = binder,frame = frame,
             body_frame = body_frame,body = body,node = node,
             first_whole = source}
          val _ = case Redblackmap.peek (!(#binder_origins g),node_id node) of
              NONE => ()
            | SOME _ => raise ERR "admit_binder"
                "admission node already indexed"
          (* Stage both immutable dictionaries before publishing references.
             Missing/partial metadata always fails closed in new getters. *)
          val next_binders = Redblackmap.insert (!(#binders g),scope_id scope,
            Redblackmap.insert (table,original,admission))
          val next_origins = Redblackmap.insert
            (!(#binder_origins g),node_id node,admission)
          val _ = validation_change g
          val _ = #binders g := next_binders
          val _ = validation_change g
          val _ = #binder_origins g := next_origins
        in (source,admission) end
    end

  (* Existing public proof/admission behavior is retained. *)
  fun admit_binder g scope maximum original =
    #1 (admit_binder_record g scope maximum original)

  (* The private table records the actual construction, not a caller's
     assertion that a closed semantic equality is an alpha syntax view.
     Each application retains the two ORIGINAL child IDs. Binder discovery
     uses the old bounded admit_binder callback envelope, separately from
     the later normalization planner's cached-metric admission. *)
  fun record_opened_view (g : graph) scope maximum original =
    let
      val _ = check_scope g scope
      val _ = usable g scope original
      val _ = if maximum > 0 then () else
        raise ERR "record_opened_view" "nonpositive discovery budget"
      val remaining = ref maximum
      fun key node = (scope_id scope,node_id node)
      fun visit node =
        (usable g scope node;
         case Redblackmap.peek (!(#opened_views g),key node) of
           SOME record => #source record
         | NONE =>
           let
             val _ = if !remaining > 0 then remaining := !remaining-1
               else raise ERR "record_opened_view"
                 "opened recipe discovery budget exhausted"
             val term = representative g node
             val (source,recipe) = case view g node of
                 OpaqueRetained =>
                   let val (source,admission) =
                     admit_binder_record g scope maximum term
                   in (source,OpenedBinder admission) end
               | Application (operator,operand) =>
                   let val left = visit operator val right = visit operand
                       val rich = application g scope
                         (#node left,#node right)
                       val bridge = align_application term (#bridge left)
                         (#bridge right) (representative g rich)
                   in (source_for g term rich bridge,
                       OpenedApplication (operator,operand)) end
               | _ => (source_for g term node (Thm.REFL term),OpenedAtom)
             val _ = validation_change g
             val _ = #opened_views g := Redblackmap.insert
               (!(#opened_views g),key node,{source = source,recipe = recipe})
           in source end)
    in visit original end

  fun validate_discovered_view (g : graph) scope original
      (candidate : source) =
    let
      val _ = check_scope g scope
      val _ = usable g scope original
      val _ = usable g scope (#node candidate)
      fun key node = (scope_id scope,node_id node)
      val {source,recipe} = case Redblackmap.peek
          (!(#opened_views g),key original) of SOME record => record
        | NONE => raise ERR "validate_opened_view"
            "unrecorded opened Source view"
      val _ = if #node source = #node candidate andalso
          Portable.pointer_eq (#original source,#original candidate) andalso
          Portable.pointer_eq (#bridge source,#bridge candidate) then ()
        else raise ERR "validate_opened_view" "opened Source recipe differs"
      fun child node = case Redblackmap.peek
          (!(#opened_views g),key node) of SOME record => #node (#source
            record)
        | NONE => raise ERR "validate_opened_view" "missing recorded child"
      val ok = case (recipe,view g original,view g (#node source)) of
          (OpenedApplication (f,x),Application (ofn,ox),
           Application (rf,rx)) =>
             f = ofn andalso x = ox andalso child f = rf andalso child x = rx
        | (OpenedBinder _,OpaqueRetained,AdmittedBinder _) => true
        | (OpenedAtom,Application _,_) => false
        | (OpenedAtom,OpaqueRetained,_) => false
        | (OpenedAtom,_,_) => original = #node source
        | _ => false
    in if ok then () else
      raise ERR "validate_opened_view" "opened recipe constructors differ"
    end

  (* A separate private identity recipe cannot replace the first import,
     ordinary opened recipe or raw binder origin. Its proof comes only from
     the closure executor or private partial discovery; path guards survive. *)
  fun same_source (a : source) (b : source) =
    #node a = #node b andalso
    Portable.pointer_eq (#original a,#original b) andalso
    Portable.pointer_eq (#bridge a,#bridge b)
  fun validate_opened_view (g : graph) scope original (candidate : source) =
    let val _ = check_scope g scope val _ = usable g scope original
        val _ = usable g scope (#node candidate)
        val rows = case Redblackmap.peek (!(#identity_views g),
          (scope_id scope,node_id original)) of SOME rows => rows | NONE => []
        (* All matches guard, even if a kernel shares identical REFL data.
           A copied field record cannot drop one of the held lifetimes. *)
        fun matches [] seen = seen
          | matches ((row : identity_opened_record)::rest) seen =
              if same_source (#source row) candidate then
                ((#guard row) ();matches rest true) else matches rest seen
    in if matches rows false then () else
      validate_discovered_view g scope original candidate
    end

  (* Recover only the actual private import and opened-view records.
     This getter creates no view and never changes the first source anchor. *)
  (* Old discovery table only: identity/partial rows cannot acquire this
     receipt by matching a semantic node or presenting another theorem. *)
  fun cached_opened_view (g : graph) scope original =
    let
      val _ = check_scope g scope
      val _ = usable g scope original
      val source = case Redblackmap.peek (!(#opened_views g),
          (scope_id scope,node_id original)) of SOME record => #source record
        | NONE => raise ERR "cached_opened_view" "missing discovered record"
      val _ = validate_discovered_view g scope original source
    in source end

  fun imported_opened_source (g : graph) scope original target =
    let
      val _ = check_scope g scope
      val _ = usable g scope target
      val imported = case memo_peek g scope original of SOME source => source
        | NONE => raise ERR "imported_opened_source" "missing exact import"
      val raw = #node imported
      val _ = usable g scope raw
      val opened = case Redblackmap.peek (!(#opened_views g),
          (scope_id scope,node_id raw)) of SOME record => #source record
        | NONE => raise ERR "imported_opened_source" "missing opened import"
      val _ = validate_opened_view g scope raw opened
      val _ = if #node opened = target andalso
          Portable.pointer_eq (#original imported,original) then () else
        raise ERR "imported_opened_source" "exact import target differs"
    in (imported,opened) end

  (* Metadata-only guarded handle. No destructor, proof decoding, import
     or kernel operation occurs on this path. In particular, body_frame
     is never inferred from the possibly ancestor-owned body node. *)
  fun checked_binder_origin (g : graph) scope
      (BinderOrigin {owner,scope = held,original,whole,admission}) =
    let
      val _ = if owner = #owner g andalso scope = held then () else
        raise ERR "binder_origin" "different graph or opened owner scope"
      val _ = validate_opened_view g scope original whole
      val {recipe,...} = case Redblackmap.peek (!(#opened_views g),
          (scope_id scope,node_id original)) of SOME value => value
        | NONE => raise ERR "binder_origin" "missing opened origin"
      val saved = case recipe of OpenedBinder value => value
        | _ => raise ERR "binder_origin" "not a genuine admitted origin"
      val _ = if #identity saved = #identity admission andalso
          #owner admission = #owner g andalso #scope admission = scope andalso
          #node admission = #node whole then () else
        raise ERR "binder_origin" "stored admission identity differs"
      val indexed = indexed_binder_origin g (#node admission)
      val _ = if #identity indexed = #identity admission then () else
        raise ERR "binder_origin" "opened first origin index differs"
      val _ = case view g (#node admission) of
          AdmittedBinder {binder,body,frame} =>
            if binder = #binder admission andalso
                body = #node (#body admission) andalso
                frame = #frame admission then () else
              raise ERR "binder_origin" "stored binder identities differ"
        | _ => raise ERR "binder_origin" "stored node is not an abstraction"
      val _ = check_scope g (#frame admission)
      val _ = check_scope g (#body_frame admission)
      val _ = if #parent (scope_frame g (#frame admission)) = SOME scope
          andalso #parent (scope_frame g (#body_frame admission)) =
            SOME (#frame admission) then () else
        raise ERR "binder_origin" "stored admission frames differ"
      val _ = usable g (#frame admission) (#binder admission)
      val _ = usable g (#body_frame admission) (#node (#body admission))
      val _ = if Portable.pointer_eq (#binder_term admission,
          representative g (#binder admission)) then () else
        raise ERR "binder_origin" "stored binder term identity differs"
    in (admission,original,whole) end

  fun opened_binder_origin (g : graph) scope original candidate =
    let
      val _ = validate_opened_view g scope original candidate
      val {source,recipe} = case Redblackmap.peek (!(#opened_views g),
          (scope_id scope,node_id original)) of SOME value => value
        | NONE => raise ERR "opened_binder_origin" "missing opened origin"
      val admission = case recipe of OpenedBinder value => value
        | _ => raise ERR "opened_binder_origin"
            "no first genuine admission origin for this opened root"
      val handle_value = BinderOrigin
        {owner = #owner g,scope = scope,original = original,whole = source,
         admission = admission}
      val _ = checked_binder_origin g scope handle_value
    in handle_value end

  fun binder_origin_data g scope origin =
    let val (admission,original,whole) = checked_binder_origin g scope origin
    in {first_input = #first_input admission,
        binder_term = #binder_term admission,binder = #binder admission,
        frame = #frame admission,body_frame = #body_frame admission,
        body = #body admission,node = #node admission,
        original_node = original,whole = whole} end

  (* The caller scope is the original root owner, even at nested depth.
     This private validator instead uses each captured declaring scope for
     its actual node/frame visibility. No permission follows from a fresh
     ancestor/rehome node: only a genuine indexed admission can pass. *)
  fun checked_nested_admission g effective node
      (admission : admitted_binder_origin) =
    let
      val indexed = indexed_binder_origin g node
      val _ = if #identity indexed = #identity admission andalso
          #scope admission = effective then () else
        raise ERR "canonical_child" "different nested declaring scope"
      val _ = check_scope g effective
      val _ = check_scope g (#frame admission)
      val _ = check_scope g (#body_frame admission)
      val _ = case view g node of
          AdmittedBinder {binder,body,frame} =>
            if binder = #binder admission andalso
                body = #node (#body admission) andalso
                frame = #frame admission then () else
              raise ERR "canonical_child" "nested binder metadata differs"
        | _ => raise ERR "canonical_child" "not an admitted nested binder"
      val _ = if #parent (scope_frame g (#frame admission)) = SOME effective
          andalso #parent (scope_frame g (#body_frame admission)) =
            SOME (#frame admission) then () else
        raise ERR "canonical_child" "nested admission frames differ"
      val _ = usable g (#frame admission) (#binder admission)
      val _ = usable g (#body_frame admission) (#node (#body admission))
      val _ = if Portable.pointer_eq (#binder_term admission,
          representative g (#binder admission)) then () else
        raise ERR "canonical_child" "nested binder term differs"
    in admission end

  fun checked_canonical_child g caller_scope child =
    let
      val (effective,node) = case child of
          CanonicalBody root =>
            let val (admission,_,_) = checked_binder_origin g caller_scope root
            in (#body_frame admission,#node (#body admission)) end
        | CanonicalApplicationChild {parent,operator,node} =>
            let
              val (effective,parent_node) =
                checked_canonical_child g caller_scope parent
              val actual = case view g parent_node of
                  Application (left,right) => if operator then left else right
                | _ => raise ERR "canonical_child" "parent is not application"
              val _ = if actual = node then () else
                raise ERR "canonical_child" "stored application child differs"
            in (effective,node) end
        | CanonicalNestedBody {parent,admission} =>
            let
              val (effective,parent_node) =
                checked_canonical_child g caller_scope parent
              val held = checked_nested_admission g effective
                parent_node admission
            in (#body_frame held,#node (#body held)) end
      val _ = check_scope g effective
      val _ = usable g effective node
      val _ = case view g node of AdmittedBinder _ =>
          ignore (checked_nested_admission g effective node
            (indexed_binder_origin g node))
        | _ => ()
    in (effective,node) end

  fun binder_origin_body g caller_scope origin =
    let val child = CanonicalBody origin
        val _ = checked_canonical_child g caller_scope child
    in child end

  fun canonical_child_node g caller_scope child =
    #2 (checked_canonical_child g caller_scope child)

  fun canonical_application_children g caller_scope parent =
    let
      val (_,node) = checked_canonical_child g caller_scope parent
      val (left,right) = case view g node of Application pair => pair
        | _ => raise ERR "canonical_application_children" "not an application"
      val l = CanonicalApplicationChild
        {parent = parent,operator = true,node = left}
      val r = CanonicalApplicationChild
        {parent = parent,operator = false,node = right}
      val _ = checked_canonical_child g caller_scope l
      val _ = checked_canonical_child g caller_scope r
    in (l,r) end

  fun canonical_child_binder_origin g caller_scope child =
    let
      val (effective,node) = checked_canonical_child g caller_scope child
      val admission = checked_nested_admission g effective node
        (indexed_binder_origin g node)
    in NestedBinderOrigin {child = child,admission = admission} end

  fun checked_nested_origin g caller_scope
      (NestedBinderOrigin {child,admission}) =
    let val (effective,node) = checked_canonical_child g caller_scope child
    in checked_nested_admission g effective node admission end

  fun nested_binder_origin_data g caller_scope origin =
    let val admission = checked_nested_origin g caller_scope origin
    in {declaring_scope = #scope admission,
        first_input = #first_input admission,
        binder_term = #binder_term admission,binder = #binder admission,
        frame = #frame admission,body_frame = #body_frame admission,
        body = #body admission,node = #node admission,
        first_whole = #first_whole admission} end

  fun nested_binder_origin_body g caller_scope
      (origin as NestedBinderOrigin {child,admission}) =
    let val _ = checked_nested_origin g caller_scope origin
        val result = CanonicalNestedBody {parent = child,admission = admission}
        val _ = checked_canonical_child g caller_scope result
    in result end

  (* These paths inspect stored entries/frames only, never a Term/theorem.
     The original caller scope is carried through structural descendants. *)
  fun indexed_closure (g : graph) node =
    (ignore (entry g node);
     case Redblackmap.peek (!(#binder_closures g),node_id node) of
       SOME record => record
     | NONE => raise ERR "binder_closure" "actual body frame not recorded")

  fun checked_closure_record (g : graph)
      (record as ClosureRecord
        {identity,owner,node,node_frame,creation,backing}) =
    let
      val ClosureRecord {identity = indexed_identity,...} =
        indexed_closure g node
      val _ = if owner = #owner g andalso identity = indexed_identity andalso
          node_scope g node = node_frame then () else
        raise ERR "binder_closure" "closure owner/index/node frame differs"
      val _ = check_scope g node_frame
      val {node = first,declaring_scope,binder,binder_term,binder_frame,
           body,body_frame,...} = creation
      val _ = check_scope g declaring_scope
      val _ = check_scope g binder_frame
      val _ = check_scope g body_frame
      val _ = if node_scope g first = declaring_scope andalso
          node_scope g binder = binder_frame andalso
          scope_visible g binder_frame declaring_scope andalso
          scope_visible g body_frame binder_frame then () else
        raise ERR "binder_closure" "original creation frames differ"
      val _ = usable g body_frame binder
      val _ = usable g body_frame body
      val _ = if Portable.pointer_eq (binder_term,representative g binder)
          then () else
        raise ERR "binder_closure" "retained binder term differs"
      fun exact current = case view g current of
          AdmittedBinder {binder = b,body = t,frame} =>
            if b = binder andalso t = body andalso frame = binder_frame
              then () else
              raise ERR "binder_closure" "actual binder children differ"
        | _ => raise ERR "binder_closure" "not an admitted binder"
      val _ = exact first
      val _ = exact node
      val _ = case backing of NONE =>
          if node = first andalso node_frame = declaring_scope then () else
            raise ERR "binder_closure" "new closure is not its creation"
        | SOME parent =>
            let val _ = checked_closure_record g parent
                val ClosureRecord {creation = previous,...} = parent
            in if #identity previous = #identity creation then () else
              raise ERR "binder_closure" "rehome changed creation identity"
            end
    in record end

  fun checked_closure_child g caller child =
    let
      val (effective,node) = case child of
          ClosureRoot {owner,caller = held,node} =>
            (if owner = #owner g andalso caller = held then () else
               raise ERR "closure_child" "different graph or caller scope";
             check_scope g caller;usable g caller node;(caller,node))
        | ClosureApplicationChild {parent,operator,node} =>
            let val (effective,root) = checked_closure_child g caller parent
                val actual = case view g root of Application (f,x) =>
                    if operator then f else x
                  | _ => raise ERR "closure_child" "parent not application"
                val _ = if actual = node then () else
                  raise ERR "closure_child" "application child changed"
            in (effective,node) end
        | ClosureBodyChild {parent,record} =>
            let val (_,parent_node) = checked_closure_child g caller parent
                val ClosureRecord {node = captured,creation,...} =
                  checked_closure_record g record
                val _ = if parent_node = captured then () else
                  raise ERR "closure_child" "binder parent changed"
            in (#body_frame creation,#body creation) end
      val _ = check_scope g effective
      val _ = usable g effective node
      val _ = case view g node of AdmittedBinder _ =>
          ignore (checked_closure_record g (indexed_closure g node))
        | _ => ()
    in (effective,node) end

  fun closure_root g caller node =
    let val root = ClosureRoot {owner = #owner g,caller = caller,node = node}
        val _ = checked_closure_child g caller root
    in root end

  fun closure_child_node g caller child =
    #2 (checked_closure_child g caller child)

  fun closure_application_children g caller parent =
    let
      val (_,node) = checked_closure_child g caller parent
      val (f,x) = case view g node of Application pair => pair
        | _ => raise ERR "closure_application_children" "not application"
      val left = ClosureApplicationChild
        {parent = parent,operator = true,node = f}
      val right = ClosureApplicationChild
        {parent = parent,operator = false,node = x}
      val _ = checked_closure_child g caller left
      val _ = checked_closure_child g caller right
    in (left,right) end

  fun closure_child_binder g caller child =
    let val (_,node) = checked_closure_child g caller child
        val record = checked_closure_record g (indexed_closure g node)
    in BinderClosure {child = child,record = record} end

  fun binder_closure g caller node =
    closure_child_binder g caller (closure_root g caller node)

  fun recorded_binder_closure (g : graph) caller node =
    (check_scope g caller;usable g caller node;
     case Redblackmap.peek (!(#binder_closures g),node_id node) of
       NONE => NONE
     | SOME _ => SOME (binder_closure g caller node))

  fun checked_binder_closure g caller (BinderClosure {child,record}) =
    let val (_,node) = checked_closure_child g caller child
        val (held as ClosureRecord {node = captured,...}) =
          checked_closure_record g record
        val _ = if node = captured then () else
          raise ERR "binder_closure" "closure child changed"
    in held end

  fun binder_closure_data g caller closure =
    let val ClosureRecord {node,node_frame,creation,backing,...} =
          checked_binder_closure g caller closure
        val {node = first,declaring_scope,binder,binder_term,binder_frame,
             body,body_frame,...} = creation
    in {node = node,node_frame = node_frame,creation_node = first,
        declaring_scope = declaring_scope,binder = binder,
        binder_term = binder_term,binder_frame = binder_frame,body = body,
        body_frame = body_frame,rehomed = Option.isSome backing} end

  fun binder_closure_body g caller
      (closure as BinderClosure {child,record}) =
    let val _ = checked_binder_closure g caller closure
        val result = ClosureBodyChild {parent = child,record = record}
        val _ = checked_closure_child g caller result
    in result end

  fun same_opened_recipe (OpenedAtom,OpenedAtom) = true
    | same_opened_recipe (OpenedApplication (f,x),OpenedApplication (g,y)) =
        f = g andalso x = y
    | same_opened_recipe (OpenedBinder a,OpenedBinder b) =
        #identity a = #identity b
    | same_opened_recipe _ = false

  fun check_alpha_row (g : graph) scope (original,held : opened_record) =
    let
      val _ = validate_discovered_view g scope original (#source held)
      val actual = case Redblackmap.peek (!(#opened_views g),
          (scope_id scope,node_id original)) of SOME record => record
        | NONE => raise ERR "discovered_alpha" "missing discovered record"
      val _ = if same_source (#source actual) (#source held) andalso
          same_opened_recipe (#recipe actual,#recipe held) andalso
          type_id g original = type_id g (#node (#source held)) then () else
        raise ERR "discovered_alpha" "retained Alpha recipe differs"
      val _ = case #recipe held of OpenedBinder admission =>
          ignore (checked_binder_origin g scope
            (BinderOrigin {owner = #owner g,scope = scope,original = original,
              whole = #source held,admission = admission}))
        | _ => ()
    in () end

  fun checked_discovered_alpha (g : graph) scope
      (receipt as DiscoveredAlpha
        {owner,scope = caller,original,source,rows,roots,annotation,
         epoch,symbols,visits}) =
    let
      val _ = if owner = #owner g andalso caller = scope then () else
        raise ERR "discovered_alpha" "different graph or caller Scope"
      fun guard () =
        (check_scope g scope;
         if Type.type_epoch () = epoch andalso Term.term_epoch () = symbols
           then () else
           raise ERR "discovered_alpha" "kernel declaration epoch changed")
      val _ = guard ()
      val _ = usable g scope original
      val _ = List.app (check_alpha_row g scope) rows
      (* Every incoming handle is retained before semantic-node memoization.
         Its parent path is guarded even when descendants were visited once.
         Indexed binder records recursively guard creation/rehome backings. *)
      val _ = List.app (fn child =>
        ignore (checked_closure_child g scope child)) roots
      val _ = if #2 (checked_closure_child g scope annotation) = #node source
          andalso same_source (cached_opened_view g scope original) source
          andalso visits > 0 then () else
        raise ERR "discovered_alpha" "retained annotation root differs"
      val _ = guard ()
    in receipt end

  fun discovered_alpha_program (g : graph) scope spend visits original =
    let
      val epoch = Type.type_epoch () val symbols = Term.term_epoch ()
      val rows = ref ([] : (node * opened_record) list)
      val roots = ref ([] : closure_child list)
      val raw_seen = ref (Redblackmap.mkDict Int.compare)
      val rich_seen = ref (Redblackmap.mkDict Int.compare)
      fun raw node =
        let val _ = spend ()
            val _ = usable g scope node
            val record = case Redblackmap.peek (!(#opened_views g),
                (scope_id scope,node_id node)) of SOME record => record
              | NONE => raise ERR "discovered_alpha"
                  "missing discovered child recipe"
            val _ = check_alpha_row g scope (node,record)
        in case Redblackmap.peek (!raw_seen,node_id node) of SOME () => ()
          | NONE =>
            (raw_seen := Redblackmap.insert (!raw_seen,node_id node,());
             rows := (node,record) :: !rows;
             case #recipe record of OpenedApplication (f,x) => (raw f;raw x)
               | _ => ())
        end
      fun rich child =
        let val _ = spend ()
            val (_,node) = checked_closure_child g scope child
            val _ = roots := child :: !roots
        in case Redblackmap.peek (!rich_seen,node_id node) of SOME () => ()
          | NONE =>
            (rich_seen := Redblackmap.insert (!rich_seen,node_id node,());
             case view g node of Application _ =>
                 let val (f,x) = closure_application_children g scope child
                 in rich f;rich x end
               | AdmittedBinder _ => rich (binder_closure_body g scope
                   (closure_child_binder g scope child))
               | OpaqueRetained => raise ERR "discovered_alpha"
                   "incomplete canonical annotation recipe"
               | _ => ())
        end
      val _ = raw original
      val source = cached_opened_view g scope original
      val annotation = closure_root g scope (#node source)
      val _ = rich annotation
      val receipt = DiscoveredAlpha {owner = #owner g,scope = scope,
        original = original,source = source,rows = !rows,roots = !roots,
        annotation = annotation,epoch = epoch,symbols = symbols,
        visits = visits ()}
      val _ = checked_discovered_alpha g scope receipt
    in receipt end

  fun discovered_alpha (g : graph) scope maximum original =
    let
      val _ = check_scope g scope
      val _ = if maximum > 0 then () else
        raise ERR "discovered_alpha" "nonpositive metadata visit allowance"
      val remaining = ref maximum
      fun spend () =
        if !remaining > 0 then remaining := !remaining-1 else
          raise ERR "discovered_alpha" "metadata visit allowance exhausted"
    in discovered_alpha_program g scope spend
      (fn () => maximum - !remaining) original end

  fun validate_discovered_alpha g scope receipt =
    ignore (checked_discovered_alpha g scope receipt)

  fun discovered_alpha_data g scope receipt =
    let val DiscoveredAlpha {original,source,annotation,visits,...} =
          checked_discovered_alpha g scope receipt
    in {original = original,source = source,annotation = annotation,
        visits = visits} end

  fun partial_source (PartialAtom (_,source)) = source
    | partial_source (PartialRetained (_,source)) = source
    | partial_source (PartialFull (_,source)) = source
    | partial_source (PartialApplication (_,source,_,_)) = source
  fun partial_original (PartialAtom (node,_)) = node
    | partial_original (PartialRetained (node,_)) = node
    | partial_original (PartialFull (node,_)) = node
    | partial_original (PartialApplication (node,_,_,_)) = node
  (* The partial record is private. No caller boolean, theorem or Source
     triple can manufacture PartialRetained or replace its captured guard. *)
  fun validate_partial_recipe g scope recipe =
    let val completed = ref ([] : partial_recipe list)
        (* Every incoming row is checked before exact-object memoization.
           The scope is this one call's actual original discovery scope. *)
        fun visit current =
          let val original = partial_original current
              val source = partial_source current
              val _ = check_scope g scope val _ = usable g scope original
              val _ = usable g scope (#node source)
              val _ = if Portable.pointer_eq
                  (#original source,representative g original) then () else
                raise ERR "partial_view" "original recipe term changed"
              fun child_owner child =
                let val raw = partial_original child
                    val canonical = partial_source child
                    val _ = usable g scope raw
                    val _ = usable g scope (#node canonical)
                in if Portable.pointer_eq (#original canonical,
                    representative g raw) then () else
                  raise ERR "partial_view" "incoming child term changed" end
              val valid = case current of
                  PartialAtom _ => original = #node source andalso
                    (case view g original of Application _ => false
                       | OpaqueRetained => false | AdmittedBinder _ => false
                       | _ => true)
                | PartialRetained _ => original = #node source andalso
                    (case view g original of OpaqueRetained => true
                       | AdmittedBinder _ => true | _ => false)
                | PartialFull _ =>
                    (validate_discovered_view g scope original source;true)
                | PartialApplication (_,_,left,right) =>
                    (child_owner left;child_owner right;
                     case (view g original,view g (#node source)) of
                       (Application (f,x),Application (rf,rx)) =>
                         f = partial_original left andalso
                         x = partial_original right andalso
                         rf = #node (partial_source left) andalso
                         rx = #node (partial_source right)
                     | _ => false)
              val _ = if valid then () else raise ERR "partial_view"
                "partial recipe constructors changed"
          in if List.exists (fn old => Portable.pointer_eq (current,old))
              (!completed) then () else
            ((case current of PartialApplication (_,_,left,right) =>
                (visit left;visit right) | _ => ());
             completed := current :: !completed)
          end
    in visit recipe end
  fun validate_partial (g : graph) scope
      (PartialDiscovery {owner,scope = held,original,recipe,guard}) =
    if owner = #owner g andalso scope = held then
      (check_scope g scope;usable g scope original;guard ();
       case recipe of NONE => ()
         | SOME value => validate_partial_recipe g scope value)
    else raise ERR "validate_partial" "different graph/source caller"
  fun partial_view g scope
      (plan as PartialDiscovery {recipe,...}) =
    (validate_partial g scope plan;
     Option.map partial_source recipe)

  (* Source discovery only: no Work entitlement is conferred by step.
     The caller's hook must debit its SAME invocation before each primitive.
     Private map/frame and primitive kernel/type costs remain unquoted. *)
  (* Shared actual annotation traversal. The existing discovery callers
     retain their precise count_body/debit protocol. A separately bounded
     native producer may inspect the ordinary abstraction body instead. *)
  fun native_annotation_profile {size,bucket} capture_projection
      debit valid body original =
    let
      fun invoke action =
        (debit ();let val value = action () val _ = valid () in value end)
      val memo = Array.array (size,[])
      val types = ref ([] : Type.hol_type list)
      fun add (a : IntInf.int) (b : IntInf.int) = a+b
      fun text_bytes text : IntInf.int =
        let val size = String.size text
            fun walk index = if index = size then () else
              (debit ();ignore (String.sub (text,index));
               walk (index+1))
            val _ = walk 0
        in IntInf.fromInt size end
      fun weight ty : IntInf.int * IntInf.int =
        let val _ = debit ()
        in if invoke (fn () => Type.is_vartype ty) then
            (1,text_bytes (invoke
              (fn () => Type.dest_vartype ty)))
          else
            let val {Thy,Tyop,Args} = invoke
                  (fn () => Type.dest_thy_typeid ty)
                val name = invoke (fn () => KernelSig.name_of Tyop)
                val own = add (text_bytes Thy) (text_bytes name)
            in List.foldl (fn (child,(nodes,bytes)) =>
                 let val (n,b) = weight child
                 in (add nodes n,add bytes b) end) (1,own) Args end
        end
      fun annotation ty =
        let val counts = weight ty val _ = debit ()
            val _ = types := ty :: !types
        in counts end
      fun lookup term [] = NONE
        | lookup term ((held,value)::rest) =
            (debit ();if Portable.pointer_eq (term,held) then
              SOME value else lookup term rest)
      fun visit term =
        let val bucket = invoke (fn () => bucket term)
            val _ = debit ()
        in case lookup term (Array.sub (memo,bucket)) of
            SOME value => value
          | NONE =>
            let val ty = invoke (fn () => Term.type_of term)
                val (own,own_bytes) = annotation ty
                val value = if invoke (fn () => Term.is_comb term)
                  then
                    let val (f,x) = invoke
                          (fn () => Term.dest_comb term)
                        val a = visit f val b = visit x
                    in {raw = plus 1 (plus (#raw a) (#raw b)),
                        inc = plus 1 (plus (#inc a) (#inc b)),
                        ann = add own (add (#ann a) (#ann b)),
                        type_bytes = add own_bytes
                          (add (#type_bytes a) (#type_bytes b)),
                        ty = own,projection = Option.map
                          (fn path => ProjectionApplication (term,path))
                          (#projection a)} end
                  else if invoke
                      (fn () => Term.is_abs term) then
                    let val domain = invoke
                          (fn () => #1 (Type.dom_rng ty))
                        val (binder,binder_bytes) = annotation domain
                        val body = visit (invoke
                          (fn () => body term))
                    in {raw = plus 1 (#raw body),
                        inc = plus 2 (#inc body),
                        ann = add own (add binder (#ann body)),
                        type_bytes = add own_bytes
                          (add binder_bytes (#type_bytes body)),ty = own,
                        projection = Option.map
                          (fn path => ProjectionBinder
                            (term,domain,path))
                          (#projection body)}
                    end
                  else {raw = 1,inc = 1,ann = own,
                        type_bytes = own_bytes,ty = own,
                        projection = if capture_projection then
                          SOME (ProjectionAtom {term = term,
                            variable = invoke
                              (fn () => Term.is_var term)}) else NONE}
                val _ = debit ()
                val _ = Array.update (memo,bucket,
                  (term,value) :: Array.sub (memo,bucket))
            in value end
        end
      val original = invoke original
      val value = visit original
    in (original,value,!types) end

  (* A bounded native theorem operand may need metrics without opening or
     changing any graph syntax. The actual annotation scanner above measures
     it; this entry accepts no caller counts, bridge or proof permission. *)
  fun profile_bounded_native_observed (g:graph) caller
      {node,bound,maximum,observe} =
    let
      (* Authenticate graph ownership before activating a held child. *)
      val _ = check_scope g caller
      val _ = usable g caller node
      val _ = case view g node of OpaqueRetained => ()
        | _ => raise ERR "bounded_native_profile" "not retained opaque syntax"
      val _ = if maximum > 0 andalso maximum < cap then () else
        raise ERR "bounded_native_profile" "invalid native profile bound"
      val declared = node_scope g node
      val child = closure_root g caller node
      val original = representative g node
      val admitted = SmtReplayImport.raw_bound_data bound original
      val _ = if #raw_upper admitted <= IntInf.fromInt maximum andalso
          #inc_upper admitted <= IntInf.fromInt maximum then () else
        raise ERR "bounded_native_profile"
          "authentic native bound exceeds caller maximum"
      val epoch = Type.type_epoch () and symbols = Term.term_epoch ()
      (* New lease allocation/publication and eventual two-write cleanup
         are prepaid; cleanup itself must preserve a retired Primary. *)
      val _ = observe () val _ = observe ()
      val _ = observe () val _ = observe ()
      val _ = check_scope g caller
      val _ = usable g caller node
      val _ = case !(#partial_running g) of NONE => ()
        | SOME active =>
            (active := false;raise ERR "bounded_native_profile"
              "annotation producer reentry")
      val running = ref true
      val _ = #partial_running g := SOME running
      fun guard_program note () =
        (note ();check_scope g caller;
         note ();check_scope g declared;
         note ();if closure_child_node g caller child=node then () else
           raise ERR "bounded_native_profile" "retained child changed";
         note ();if Type.type_epoch ()=epoch andalso
             Term.term_epoch ()=symbols then () else
           raise ERR "bounded_native_profile" "Type or Term epoch changed";
         note ();if Portable.pointer_eq
             (original,representative g node) then () else
           raise ERR "bounded_native_profile" "retained native pointer changed")
      fun guard () = guard_program (fn () => ()) ()
      fun building note =
        (note ();if !running then () else
           raise ERR "bounded_native_profile" "annotation producer retired";
         guard_program note ())
      fun debit () = (building observe;observe ();building (fn () => ()))
      fun ready () = partial_scope_live g caller andalso
        partial_scope_live g declared andalso Type.type_epoch ()=epoch
        andalso Term.term_epoch ()=symbols
      fun measure () =
        let
        val size = Int.max (1,Int.min
          (4093,IntInf.toInt (#raw_upper admitted)))
        (* Actual local table initialization, separate from each observed
           pointer collision and native/type annotation operation below. *)
        fun setup 0 = debit ()
          | setup count = (debit ();debit ();setup (count-1))
        val _ = setup size
        fun bucket term =
          let val value = physical_hint term val _ = debit ()
          in value mod size end
        val (held,value,types) = native_annotation_profile
          {size=size,bucket=bucket} false debit guard
          (fn term => #2 (Term.dest_abs term)) (fn () => original)
        val _ = debit ()
        val _ = if #raw value <= maximum andalso #inc value <= maximum then ()
          else raise ERR "bounded_native_profile"
            "actual native profile exceeds caller bound"
        val _ = if Portable.pointer_eq (held,original) then () else
          raise ERR "bounded_native_profile" "measured native pointer changed"
        val _ = debit ()
        val profile = OpaqueProfile
          {owner= #owner g,scope=caller,node=node,original=original,
           raw= #raw value,inc= #inc value,ann= #ann value,ty= #ty value,
           type_bytes= #type_bytes value,types=types,ready=ready,guard=guard}
        (* These are the existing registry's public map operations, not a
           claimed private comparator/rotation envelope. No Work callback is
           retained in its comparator or in the profile's lifetime guard. *)
        val _ = debit ()
        val registry = !(#partial_profiles g)
        val _ = debit ()
        val rows = Option.getOpt (Redblackmap.peek (registry,node_id node),[])
        val _ = debit ()
        val updated = profile::rows
        val _ = debit ()
        val next = Redblackmap.insert (registry,node_id node,updated)
        val _ = debit ()
        val _ = validation_change g
        val _ = debit ()
        val _ = #partial_profiles g := next
        val _ = guard ()
        in profile end
      fun finish () = (running := false;#partial_running g := NONE)
    in (let val result = measure () val _ = finish () in result end)
       handle primary => (finish ();raise primary) end

  fun discover_partial_internal capture_projection (g : graph) scope
      {original,maximum,scan_limit,step} =
    let
      val _ = check_scope g scope val _ = usable g scope original
      val _ = if maximum > 0 andalso scan_limit > 0 then () else
        raise ERR "discover_partial" "nonpositive discovery bound"
      val _ = case !(#partial_running g) of NONE => ()
        | SOME active =>
            (active := false;
             raise ERR "discover_partial" "partial discovery reentry")
      val running = ref true
      val _ = #partial_running g := SOME running
      val epoch = Type.type_epoch () val symbols = Term.term_epoch ()
      val remaining = ref scan_limit
      val guards = ref ([] : (unit -> unit) list)
      val closures = ref ([] : binder_closure list)
      fun valid frame =
        (check_scope g scope;check_scope g frame;
         if !running andalso Type.type_epoch () = epoch andalso
             Term.term_epoch () = symbols then () else
           raise ERR "discover_partial" "scope/epoch/action retired";
         List.app (fn guard => guard ()) (!guards))
      fun debit frame =
        (valid frame;
         if !remaining > 0 then remaining := !remaining-1 else
           raise ERR "discover_partial" "discovery scan budget exhausted";
         step ();valid frame)
      fun invoke frame action =
        (debit frame;
         let val value = action () val _ = valid frame in value end)
      fun domain_needed frame ty =
        if invoke frame (fn () => Type.compare (ty,numSyntax.num) = EQUAL)
          then true
        else case invoke frame (fn () => Lib.total Type.dom_rng ty) of
            NONE => false
          | SOME (_,range) => invoke frame
              (fn () => Type.compare (range,numSyntax.num) = EQUAL)
      fun quantified frame operator abstraction get_type =
        if abstraction andalso
            invoke frame (fn () => Term.is_const operator) andalso
            invoke frame (fn () =>
              Term.same_const operator boolSyntax.universal orelse
              Term.same_const operator boolSyntax.existential) then
          let val ty = invoke frame get_type
          in case invoke frame (fn () => Lib.total Type.dom_rng ty) of
                SOME (domain,_) => domain_needed frame domain
              | NONE => false
          end
        else false
      (* Count-body substitutes only an ATOMIC marker. Recognition uses
         constructors, fixed declaration IDs and types, never variable names,
         equality of free variables, matching or semantic proof search. *)
      fun term_needed frame term =
        if invoke frame (fn () => Term.is_comb term) then
          let val (operator,operand) = invoke frame
                (fn () => Term.dest_comb term)
          in if invoke frame (fn () => Term.is_abs operator) orelse
              quantified frame operator
                (invoke frame (fn () => Term.is_abs operand))
                (fn () => Term.type_of operand) then true
            else term_needed frame operator orelse term_needed frame operand
          end
        else if invoke frame (fn () => Term.is_abs term) then
          term_needed frame (invoke frame
            (fn () => SmtReplayImport.count_body term))
        else false
      val seen = ref
        (Redblackmap.mkDict (pair_compare Int.compare Int.compare))
      val captured = ref
        (Redblackmap.mkDict (pair_compare Int.compare Int.compare))
      (* Private callback-free setup holds all genuinely recorded frames
         BEFORE a step can retire one. No node_scope(body) inference.
         Setup map/frame work remains a separate unquoted prerequisite. *)
      fun capture_paths frame node =
        let val _ = valid frame val _ = usable g frame node
            val key = (scope_id frame,node_id node)
        in case Redblackmap.peek (!captured,key) of SOME _ => ()
          | NONE =>
            let val _ = if !remaining > 0 then remaining := !remaining-1 else
                  raise ERR "discover_partial" "frame scan budget exhausted"
                val _ = captured := Redblackmap.insert (!captured,key,())
            in case view g node of
                Application (left,right) =>
                  (capture_paths frame left;capture_paths frame right)
              | AdmittedBinder _ =>
                  let val closure = binder_closure g frame node
                      val data = binder_closure_data g frame closure
                      fun guard () = ignore
                        (binder_closure_data g frame closure)
                      val _ = guards := guard :: !guards
                      val _ = closures := closure :: !closures
                  in capture_paths (#body_frame data) (#body data) end
              | _ => ()
            end
        end
      fun graph_needed frame node =
        let val _ = valid frame val _ = usable g frame node
            val _ = debit frame val key = (scope_id frame,node_id node)
        in case Redblackmap.peek (!seen,key) of SOME value => value
          | NONE =>
            let val answer = case invoke frame (fn () => view g node) of
                  Application (operator,operand) =>
                    let val operator_view = invoke frame
                          (fn () => view g operator)
                        val beta = case operator_view of
                            AdmittedBinder _ => true | OpaqueRetained => true
                          | _ => false
                        val operand_view = invoke frame
                          (fn () => view g operand)
                        val abstraction = case operand_view of
                            AdmittedBinder _ => true | OpaqueRetained => true
                          | _ => false
                        val carrier = quantified frame
                          (invoke frame (fn () => representative g operator))
                          abstraction (fn () => type_of g operand)
                    in beta orelse carrier orelse
                      graph_needed frame operator orelse
                      graph_needed frame operand end
                | OpaqueRetained => term_needed frame
                    (invoke frame (fn () => representative g node))
                | AdmittedBinder _ =>
                    let val closure = invoke frame
                          (fn () => binder_closure g frame node)
                        val data = invoke frame
                          (fn () => binder_closure_data g frame closure)
                        fun guard () = ignore
                          (binder_closure_data g frame closure)
                        val _ = guard ()
                    in graph_needed (#body_frame data) (#body data) end
                | _ => false
                val _ = valid frame
                val _ = seen := Redblackmap.insert (!seen,key,answer)
            in answer end
        end
      fun retained_guard () =
        (check_scope g scope;usable g scope original;
         if Type.type_epoch () = epoch andalso Term.term_epoch () = symbols
           then () else raise ERR "partial_view" "discovery epoch changed";
         List.app (fn guard => guard ()) (!guards))
      (* Only a child whose complete rule scan was false reaches this
         collector. It quotes full repeated annotations for mixed proof
         assembly; a whole unchanged NONE root needs no new type envelope. *)
      fun retained_ready () =
        partial_scope_live g scope andalso
        Type.type_epoch () = epoch andalso Term.term_epoch () = symbols
        andalso List.all (fn BinderClosure {record,...} =>
          partial_record_live g record) (!closures)
      fun retain_opaque node =
        let val _ = if graph_needed scope node then
              raise ERR "retain_opaque" "relevant binder is not a no-op"
            else ()
            val (original,value,types) = native_annotation_profile
              {size=4093,bucket=physical_hint} capture_projection
              (fn () => debit scope)
              (fn () => valid scope) SmtReplayImport.count_body
              (fn () => representative g node)
            val profile = OpaqueProfile
              {owner = #owner g,scope = scope,node = node,
               original = original,raw = #raw value,inc = #inc value,
               ann = #ann value,ty = #ty value,
               type_bytes = #type_bytes value,types = types,
               ready = retained_ready,guard = retained_guard}
            val _ = valid scope
            val rows = Option.getOpt
              (Redblackmap.peek (!(#partial_profiles g),node_id node),[])
            val _ = validation_change g
            val _ = #partial_profiles g := Redblackmap.insert
              (!(#partial_profiles g),node_id node,profile :: rows)
            val _ = case #projection value of NONE => () | SOME path =>
              let val receipt = OpaqueTypeProjection
                    {profile = profile,path = path}
                  val old = Option.getOpt (Redblackmap.peek
                    (!(#partial_projections g),node_id node),[])
              in validation_change g;
                 #partial_projections g := Redblackmap.insert
                (!(#partial_projections g),node_id node,receipt :: old) end
        in () end
      fun atom node retained =
        let val _ = if retained then (case view g node of
                  OpaqueRetained => retain_opaque node | _ => ()) else ()
            val term = invoke scope (fn () => representative g node)
            val proof = invoke scope (fn () => Thm.REFL term)
            val source = source_for g term node proof
        in if retained then PartialRetained (node,source)
           else PartialAtom (node,source) end
      fun opened node =
        let val source = invoke scope
              (fn () => record_opened_view g scope maximum node)
            val _ = capture_paths scope (#node source)
        in PartialFull (node,source) end
      fun visit force node =
        (valid scope;usable g scope node;
         case invoke scope (fn () => view g node) of
           OpaqueRetained =>
             if force orelse graph_needed scope node then
               opened node
             else atom node true
         | AdmittedBinder _ =>
             if force orelse graph_needed scope node then
               opened node
             else atom node true
         | Application (operator,operand) =>
             let val ov = invoke scope (fn () => view g operator)
                 val beta = case ov of AdmittedBinder _ => true
                   | OpaqueRetained => true | _ => false
                 val operand_view = invoke scope (fn () => view g operand)
                 val abstraction = case operand_view of
                     AdmittedBinder _ => true | OpaqueRetained => true
                   | _ => false
                 val carrier = quantified scope
                   (invoke scope (fn () => representative g operator))
                   abstraction (fn () => type_of g operand)
                 val left = visit beta operator
                 val right = visit carrier operand
                 val l = partial_source left val r = partial_source right
                 val term = invoke scope (fn () => representative g node)
                 val target = invoke scope
                   (fn () => application g scope (#node l,#node r))
                 val bridge = invoke scope (fn () =>
                   align_application term (#bridge l) (#bridge r)
                     (representative g target))
                 val source = source_for g term target bridge
             in PartialApplication (node,source,left,right) end
         | _ => atom node false)
      fun build () =
        let val _ = capture_paths scope original
            val changed = graph_needed scope original
            val recipe = if changed then SOME (visit false original) else NONE
            val result = PartialDiscovery
              {owner = #owner g,scope = scope,original = original,
               recipe = recipe,guard = retained_guard}
            val _ = valid scope
            val _ = case recipe of NONE => () | SOME value =>
              let val source = partial_source value
                  val row = {source = source,roots =
                    [closure_root g scope original],guard = fn () =>
                      (retained_guard ();
                       validate_partial_recipe g scope value)}
                  val key = (scope_id scope,node_id original)
                  val rows = Option.getOpt
                    (Redblackmap.peek (!(#identity_views g),key),[])
                  val old = Option.getOpt
                    (Redblackmap.peek (!(#partial_sources g),key),[])
                  val _ = validation_change g
                  val _ = #partial_sources g := Redblackmap.insert
                    (!(#partial_sources g),key,result :: old)
              in validation_change g;
                 #identity_views g := Redblackmap.insert
                (!(#identity_views g),key,row :: rows) end
        in result end
      val result = build () handle primary =>
        (running := false;#partial_running g := NONE;raise primary)
      val _ = running := false val _ = #partial_running g := NONE
    in result end

  fun validate_discovery_heads (g : graph) caller
      (DiscoveryHeads {owner,scope,epoch,symbols,rows,...}) =
    let val _ = if owner = #owner g then () else
          raise ERR "validate_discovery_heads" "foreign graph selection"
        val _ = check_scope g caller val _ = check_scope g scope
        val _ = if scope_visible g caller scope andalso
            Type.type_epoch () = epoch andalso Term.term_epoch () = symbols
          then () else raise ERR "validate_discovery_heads"
            "selection scope or declaration epoch retired"
        fun held (node,id,ty) =
          (usable g scope node;
           case view g node of Constant actual =>
             if KernelSig.id_compare (id,actual) = EQUAL andalso
                 type_id g node = ty then () else
               raise ERR "validate_discovery_heads" "held head changed"
           | _ => raise ERR "validate_discovery_heads" "head is not constant")
    in List.app held rows end

  fun record_discovery_heads (g : graph) scope {heads,maximum,step} =
    let
      val _ = check_scope g scope
      val _ = if maximum > 0 then () else
        raise ERR "record_discovery_heads" "nonpositive head allowance"
      val remaining = ref maximum
      val _ = case !(#partial_running g) of NONE => ()
        | SOME active =>
            (active := false;
             raise ERR "record_discovery_heads" "discovery reentry")
      val running = ref true
      val _ = #partial_running g := SOME running
      val epoch = Type.type_epoch () val symbols = Term.term_epoch ()
      val identity = ref ()
      val rows = ref ([] : (node * KernelSig.kernelid * int) list)
      fun valid () =
        (check_scope g scope;
         if !running andalso Type.type_epoch () = epoch andalso
             Term.term_epoch () = symbols then () else
           raise ERR "record_discovery_heads" "scope/epoch/action retired";
         validate_discovery_heads g scope (DiscoveryHeads
           {owner= #owner g,identity=identity,scope=scope,epoch=epoch,
            symbols=symbols,rows= !rows}))
      fun visit node =
        let val _ = valid () val _ = usable g scope node
            val _ = if !remaining > 0 then remaining := !remaining-1 else
              raise ERR "record_discovery_heads" "head allowance exhausted"
            val _ = step () val _ = valid ()
            val id = case view g node of Constant id => id
              | _ => raise ERR "record_discovery_heads"
                  "selection contains a nonconstant"
            val row = (node,id,type_id g node)
            val _ = rows := row :: !rows
        in valid () end
      fun build () =
        let val _ = List.app visit heads val _ = valid ()
        in DiscoveryHeads {owner= #owner g,identity=identity,scope=scope,
          epoch=epoch,symbols=symbols,rows=List.rev (!rows)} end
      val answer = build () handle primary =>
        (running := false;#partial_running g := NONE;raise primary)
      val _ = running := false val _ = #partial_running g := NONE
    in answer end

  fun discover_compact_recipe_dag_internal capture_projection selection
      (g : graph) scope
      {original,maximum,scan_limit,step} =
    let
      val _ = check_scope g scope val _ = usable g scope original
      val _ = if maximum > 0 andalso scan_limit > 0 then () else
        raise ERR "discover_partial" "nonpositive discovery bound"
      val _ = case !(#partial_running g) of NONE => ()
        | SOME active =>
            (active := false;
             raise ERR "discover_partial" "partial discovery reentry")
      val running = ref true
      val _ = #partial_running g := SOME running
      val epoch = Type.type_epoch () val symbols = Term.term_epoch ()
      val remaining = ref scan_limit
      val guards = ref ([] : (unit -> unit) list)
      val closures = ref ([] : binder_closure list)
      fun valid frame =
        (check_scope g scope;check_scope g frame;
         if !running andalso Type.type_epoch () = epoch andalso
             Term.term_epoch () = symbols then () else
           raise ERR "discover_partial" "scope/epoch/action retired";
         (case selection of NONE => () | SOME heads =>
           validate_discovery_heads g frame heads);
         List.app (fn guard => guard ()) (!guards))
      fun debit frame =
        (valid frame;
         if !remaining > 0 then remaining := !remaining-1 else
           raise ERR "discover_partial" "discovery scan budget exhausted";
         step ();valid frame)
      fun invoke frame action =
        (debit frame;
         let val value = action () val _ = valid frame in value end)
      (* Declaration-only potential recognition: no variable spelling,
         schematic matching or semantic equality influences absence. *)
      fun selected_id frame id = case selection of NONE => false
        | SOME (DiscoveryHeads {rows,...}) =>
            let fun walk [] = false
                  | walk ((_,held,_)::rest) =
                      invoke frame (fn () =>
                        KernelSig.id_compare (id,held) = EQUAL) orelse
                      walk rest
            in walk rows end
      fun selected_term frame term = case selection of NONE => false
        | SOME _ =>
            if invoke frame (fn () => Term.is_const term) then
              selected_id frame (invoke frame
                (fn () => #Name (Term.dest_thy_constid term)))
            else false
      fun domain_needed frame ty =
        if invoke frame (fn () => Type.compare (ty,numSyntax.num) = EQUAL)
          then true
        else case invoke frame (fn () => Lib.total Type.dom_rng ty) of
            NONE => false
          | SOME (_,range) => invoke frame
              (fn () => Type.compare (range,numSyntax.num) = EQUAL)
      fun quantified frame operator abstraction get_type =
        if abstraction andalso
            invoke frame (fn () => Term.is_const operator) andalso
            invoke frame (fn () =>
              Term.same_const operator boolSyntax.universal orelse
              Term.same_const operator boolSyntax.existential) then
          let val ty = invoke frame get_type
          in case invoke frame (fn () => Lib.total Type.dom_rng ty) of
                SOME (domain,_) => domain_needed frame domain
              | NONE => false
          end
        else false
      (* Count-body substitutes only an ATOMIC marker. Recognition uses
         constructors, fixed declaration IDs and types, never variable names,
         equality of free variables, matching or semantic proof search. *)
      val recognized_terms = ref ([] : (scope * Term.term * bool) list)
      fun term_needed frame term = case selection of NONE =>
          term_needed_fresh frame term
        | SOME _ =>
          let fun find [] = NONE
                | find ((held_scope,held,answer)::rest) =
                    if invoke frame (fn () => held_scope=frame andalso
                        Portable.pointer_eq (term,held)) then SOME answer
                    else find rest
          in case find (!recognized_terms) of SOME answer =>
               (valid frame;answer)
            | NONE =>
              let val answer=term_needed_fresh frame term
                  val _ = debit frame
                  val _ = recognized_terms :=
                    (frame,term,answer):: !recognized_terms
              in valid frame;answer end
          end
      and term_needed_fresh frame term =
        if invoke frame (fn () => Term.is_comb term) then
          let val (operator,operand) = invoke frame
                (fn () => Term.dest_comb term)
          in if invoke frame (fn () => Term.is_abs operator) orelse
              quantified frame operator
                (invoke frame (fn () => Term.is_abs operand))
                (fn () => Term.type_of operand) then true
            else term_needed frame operator orelse term_needed frame operand
          end
        else if invoke frame (fn () => Term.is_abs term) then
          term_needed frame (invoke frame
            (fn () => SmtReplayImport.count_body term))
        else selected_term frame term
      val seen = ref
        (Redblackmap.mkDict (pair_compare Int.compare Int.compare))
      val captured = ref
        (Redblackmap.mkDict (pair_compare Int.compare Int.compare))
      (* Private callback-free setup holds all genuinely recorded frames
         BEFORE a step can retire one. No node_scope(body) inference.
         Setup map/frame work remains a separate unquoted prerequisite. *)
      fun capture_paths frame node =
        let val _ = valid frame val _ = usable g frame node
            val key = (scope_id frame,node_id node)
        in case Redblackmap.peek (!captured,key) of SOME _ => ()
          | NONE =>
            let val _ = if !remaining > 0 then remaining := !remaining-1 else
                  raise ERR "discover_partial" "frame scan budget exhausted"
                val _ = captured := Redblackmap.insert (!captured,key,())
            in case view g node of
                Application (left,right) =>
                  (capture_paths frame left;capture_paths frame right)
              | AdmittedBinder _ =>
                  let val closure = binder_closure g frame node
                      val data = binder_closure_data g frame closure
                      fun guard () = ignore
                        (binder_closure_data g frame closure)
                      val _ = guards := guard :: !guards
                      val _ = closures := closure :: !closures
                  in capture_paths (#body_frame data) (#body data) end
              | _ => ()
            end
        end
      fun graph_needed frame node =
        let val _ = valid frame val _ = usable g frame node
            val _ = debit frame val key = (scope_id frame,node_id node)
        in case Redblackmap.peek (!seen,key) of SOME value => value
          | NONE =>
            let val answer = case invoke frame (fn () => view g node) of
                  Application (operator,operand) =>
                    let val operator_view = invoke frame
                          (fn () => view g operator)
                        val beta = case operator_view of
                            AdmittedBinder _ => true | OpaqueRetained => true
                          | _ => false
                        val operand_view = invoke frame
                          (fn () => view g operand)
                        val abstraction = case operand_view of
                            AdmittedBinder _ => true | OpaqueRetained => true
                          | _ => false
                        val carrier = quantified frame
                          (invoke frame (fn () => representative g operator))
                          abstraction (fn () => type_of g operand)
                    in beta orelse carrier orelse
                      graph_needed frame operator orelse
                      graph_needed frame operand end
                | OpaqueRetained => term_needed frame
                    (invoke frame (fn () => representative g node))
                | AdmittedBinder _ =>
                    let val closure = invoke frame
                          (fn () => binder_closure g frame node)
                        val data = invoke frame
                          (fn () => binder_closure_data g frame closure)
                        fun guard () = ignore
                          (binder_closure_data g frame closure)
                        val _ = guard ()
                    in graph_needed (#body_frame data) (#body data) end
                | Constant id => selected_id frame id
                | _ => false
                val _ = valid frame
                val _ = seen := Redblackmap.insert (!seen,key,answer)
            in answer end
        end
      fun retained_guard () =
        (check_scope g scope;usable g scope original;
         if Type.type_epoch () = epoch andalso Term.term_epoch () = symbols
           then () else raise ERR "partial_view" "discovery epoch changed";
         List.app (fn guard => guard ()) (!guards))
      (* Only a child whose complete rule scan was false reaches this
         collector. It quotes full repeated annotations for mixed proof
         assembly; a whole unchanged NONE root needs no new type envelope. *)
      fun retained_ready () =
        partial_scope_live g scope andalso
        Type.type_epoch () = epoch andalso Term.term_epoch () = symbols
        andalso List.all (fn BinderClosure {record,...} =>
          partial_record_live g record) (!closures)
      fun retain_opaque node =
        let val _ = if graph_needed scope node then
              raise ERR "retain_opaque" "relevant binder is not a no-op"
            else ()
            val (original,value,types) = native_annotation_profile
              {size=4093,bucket=physical_hint} capture_projection
              (fn () => debit scope)
              (fn () => valid scope) SmtReplayImport.count_body
              (fn () => representative g node)
            val profile = OpaqueProfile
              {owner = #owner g,scope = scope,node = node,
               original = original,raw = #raw value,inc = #inc value,
               ann = #ann value,ty = #ty value,
               type_bytes = #type_bytes value,types = types,
               ready = retained_ready,guard = retained_guard}
            val _ = valid scope
            val rows = Option.getOpt
              (Redblackmap.peek (!(#partial_profiles g),node_id node),[])
            val _ = validation_change g
            val _ = #partial_profiles g := Redblackmap.insert
              (!(#partial_profiles g),node_id node,profile :: rows)
            val _ = case #projection value of NONE => () | SOME path =>
              let val receipt = OpaqueTypeProjection
                    {profile = profile,path = path}
                  val old = Option.getOpt (Redblackmap.peek
                    (!(#partial_projections g),node_id node),[])
              in validation_change g;
                 #partial_projections g := Redblackmap.insert
                (!(#partial_projections g),node_id node,receipt :: old) end
        in () end
      fun atom node retained =
        let val _ = if retained then (case view g node of
                  OpaqueRetained => retain_opaque node | _ => ()) else ()
            val term = invoke scope (fn () => representative g node)
            val proof = invoke scope (fn () => Thm.REFL term)
            val source = source_for g term node proof
        in if retained then PartialRetained (node,source)
           else PartialAtom (node,source) end
      fun opened node =
        let val source = invoke scope
              (fn () => record_opened_view g scope maximum node)
            val _ = capture_paths scope (#node source)
        in PartialFull (node,source) end
      val recipe_memo = ref ([] : (node * bool * partial_recipe) list)
      fun cached_recipe force node [] = NONE
        | cached_recipe force node ((saved,mode,recipe)::rest) =
            (debit scope;
             if saved = node andalso mode = force then SOME recipe
             else cached_recipe force node rest)
      (* Whole original and opened backing paths were captured before this
         point. All incoming owners/epochs/scopes are rechecked before a
         hit, including after the caller's charged discovery hook. The key
         is actual original node AND force mode in this one fixed scope. *)
      fun visit force node =
        (valid scope;usable g scope node;
         case cached_recipe force node (!recipe_memo) of SOME recipe =>
           (valid scope;usable g scope node;recipe)
         | NONE =>
           let val recipe = visit_fresh force node
               val _ = debit scope
               val _ = recipe_memo := (node,force,recipe) :: !recipe_memo
               val _ = valid scope
           in recipe end)
      and visit_fresh force node =
        (valid scope;usable g scope node;
         case invoke scope (fn () => view g node) of
           OpaqueRetained =>
             if force orelse graph_needed scope node then
               opened node
             else atom node true
         | AdmittedBinder _ =>
             if force orelse graph_needed scope node then
               opened node
             else atom node true
         | Application (operator,operand) =>
             let val ov = invoke scope (fn () => view g operator)
                 val beta = case ov of AdmittedBinder _ => true
                   | OpaqueRetained => true | _ => false
                 val operand_view = invoke scope (fn () => view g operand)
                 val abstraction = case operand_view of
                     AdmittedBinder _ => true | OpaqueRetained => true
                   | _ => false
                 val carrier = quantified scope
                   (invoke scope (fn () => representative g operator))
                   abstraction (fn () => type_of g operand)
                 val left = visit beta operator
                 val right = visit carrier operand
                 val l = partial_source left val r = partial_source right
                 val term = invoke scope (fn () => representative g node)
                 val target = invoke scope
                   (fn () => application g scope (#node l,#node r))
                 val bridge = invoke scope (fn () =>
                   align_application term (#bridge l) (#bridge r)
                     (representative g target))
                 val source = source_for g term target bridge
             in PartialApplication (node,source,left,right) end
         | _ => atom node false)
      fun build () =
        let val _ = capture_paths scope original
            val changed = graph_needed scope original
            val _ = if changed then () else case selection of NONE => ()
              | SOME _ => (case view g original of
                  OpaqueRetained => retain_opaque original | _ => ())
            val recipe = if changed then SOME (visit false original) else NONE
            val result = PartialDiscovery
              {owner = #owner g,scope = scope,original = original,
               recipe = recipe,guard = retained_guard}
            val _ = valid scope
            val _ = case recipe of NONE => () | SOME value =>
              let val source = partial_source value
                  val row = {source = source,roots =
                    [closure_root g scope original],guard = fn () =>
                      (retained_guard ();
                       validate_partial_recipe g scope value)}
                  val key = (scope_id scope,node_id original)
                  val rows = Option.getOpt
                    (Redblackmap.peek (!(#identity_views g),key),[])
                  val old = Option.getOpt
                    (Redblackmap.peek (!(#partial_sources g),key),[])
                  val _ = validation_change g
                  val _ = #partial_sources g := Redblackmap.insert
                    (!(#partial_sources g),key,result :: old)
              in validation_change g;
                 #identity_views g := Redblackmap.insert
                (!(#identity_views g),key,row :: rows) end
        in result end
      val result = build () handle primary =>
        (running := false;#partial_running g := NONE;raise primary)
      val _ = running := false val _ = #partial_running g := NONE
    in result end

  (* Old callbacks/Work debits are unchanged. Only the additive compact
     route selects the extra charged actual type_of projection primitive. *)
  fun discover_partial g scope request =
    discover_partial_internal false g scope request
  fun discover_compact_partial g scope request =
    discover_partial_internal true g scope request

  (* Shared recipe construction has its own charged memo operations.
     The original compact entry retains its projection-only hook sequence. *)
  fun discover_compact_shared_partial g scope request =
    discover_compact_recipe_dag_internal true NONE g scope request

  fun discover_compact_selected_partial g scope
      {original,heads,maximum,scan_limit,step} =
    let val _ = validate_discovery_heads g scope heads
        val plan = discover_compact_recipe_dag_internal true (SOME heads)
          g scope {original=original,maximum=maximum,
            scan_limit=scan_limit,step=step}
    in SelectedPartialDiscovery {heads=heads,plan=plan} end

  fun selected_partial_data g scope
      (expected as DiscoveryHeads {owner,identity,...})
      (SelectedPartialDiscovery
        {heads=held as DiscoveryHeads {identity=captured,...},
         plan=plan as PartialDiscovery {original,...}}) =
    let val _ = if owner = #owner (g : graph) andalso identity = captured
          then () else raise ERR "selected_partial_data"
            "foreign graph or recognition selection"
        val _ = validate_discovery_heads g scope expected
        val _ = validate_discovery_heads g scope held
        val _ = validate_partial g scope plan
    in {original=original,view=partial_view g scope plan} end

  fun carrier_alpha_data (g : graph) scope receipt =
    case receipt of CarrierFull held => discovered_alpha_data g scope held
    | CarrierPartial {plan,recipe,annotation} =>
        let val _ = validate_partial g scope plan
            val _ = validate_partial_recipe g scope recipe
            val source = partial_source recipe
            val _ = if closure_child_node g scope annotation = #node source
                then () else raise ERR "carrier_alpha" "different rich path"
        in {original = partial_original recipe,source = source,
            annotation = annotation,visits = 1} end
    | CarrierIdentity {owner,scope = held,original,source,annotation,
                       epoch,symbols} =>
        let val _ = if owner = #owner g andalso scope = held andalso
              Type.type_epoch () = epoch andalso Term.term_epoch () = symbols
              then () else raise ERR "carrier_alpha" "different owner/epoch"
            val _ = validate_opened_view g scope original source
            val _ = if original = #node source andalso
              closure_child_node g scope annotation = original then () else
              raise ERR "carrier_alpha" "different identity source"
        in {original = original,source = source,annotation = annotation,
            visits = 1} end
  fun validate_carrier_alpha g scope receipt =
    ignore (carrier_alpha_data g scope receipt)
  (* Publish ONLY the exact existing source from a private partial receipt.
     No Source construction, proof, opening or caller fields occur here. The
     old validator remains strict; incoming paths and the whole discovery
     lifetime are retained by this row even at a projected child. *)
  fun carrier_alpha_source_for (g : graph) scope receipt =
    let val data = carrier_alpha_data g scope receipt
        val source = #source data
        val _ = case receipt of CarrierPartial _ =>
              let fun guard () = validate_carrier_alpha g scope receipt
                  val roots = [closure_root g scope (#original data),
                               #annotation data]
                  val key = (scope_id scope,node_id (#original data))
                  val rows = Option.getOpt
                    (Redblackmap.peek (!(#identity_views g),key),[])
                  val row = {source = source,roots = roots,guard = guard}
                  val _ = guard ()
              in validation_change g;
                 #identity_views g := Redblackmap.insert
                (!(#identity_views g),key,row :: rows) end
          | _ => ()
        val _ = validate_opened_view g scope (#original data) source
    in source end

  fun carrier_alpha_program (g : graph) scope check discover
      {original,source : source} =
    let val _ = validate_opened_view g scope original source
        val _ = check ()
        val plans = Option.getOpt (Redblackmap.peek
          (!(#partial_sources g),(scope_id scope,node_id original)),[])
        fun choose [] = NONE
          | choose ((plan as PartialDiscovery {recipe,...})::rest) =
              (case recipe of SOME recipe =>
                 if same_source (partial_source recipe) source then
                   (validate_partial g scope plan;
                    SOME (CarrierPartial {plan = plan,recipe = recipe,
                      annotation = closure_root g scope (#node source)}))
                 else choose rest
               | NONE => choose rest)
        val result = case choose plans of SOME receipt => receipt
          | NONE => if original = #node source then CarrierIdentity
              {owner = #owner g,scope = scope,original = original,
               source = source,annotation = closure_root g scope original,
               epoch = Type.type_epoch (),symbols = Term.term_epoch ()}
            else CarrierFull (discover original)
        val data = carrier_alpha_data g scope result
        val _ = if same_source (#source data) source then () else
          raise ERR "carrier_alpha" "different registered source"
    in result end
  fun carrier_alpha_for g scope maximum request =
    carrier_alpha_program g scope
      (fn () => if maximum > 0 then () else
        raise ERR "carrier_alpha" "nonpositive metadata allowance")
      (discovered_alpha g scope maximum) request

  (* The same exact metadata path, accounted by the caller's actual policy
     step. No int projection, separate allowance or semantic cutoff. *)
  fun carrier_alpha_for_with_policy g scope {original,source,step} =
    let
      val _ = step ()
      val visits = ref 0
      fun spend () = (step ();visits := !visits+1)
      fun discover node =
        (check_scope g scope;
         discovered_alpha_program g scope spend (fn () => !visits) node)
    in carrier_alpha_program g scope (fn () => ()) discover
      {original=original,source=source} end

  fun carrier_alpha_application_children g scope maximum receipt =
    let val data = carrier_alpha_data g scope receipt
        val (left,right) = closure_application_children g scope
          (#annotation data)
        fun full original child =
          let val source = cached_opened_view g scope original
              val result = carrier_alpha_for g scope maximum
                {original = original,source = source}
              val _ = if closure_child_node g scope child = #node source then
                  () else raise ERR "carrier_alpha" "different full child"
          in result end
        val result = case receipt of
            CarrierPartial {plan,recipe = PartialApplication
                (_,_,a,b),...} =>
              (CarrierPartial {plan = plan,recipe = a,annotation = left},
               CarrierPartial {plan = plan,recipe = b,annotation = right})
          | CarrierPartial {recipe = PartialFull (original,_),...} =>
              (case view g original of Application (f,x) =>
                 (full f left,full x right)
               | _ => raise ERR "carrier_alpha"
                 "raw source is not application")
          | CarrierFull _ => (case view g (#original data) of
              Application (f,x) => (full f left,full x right)
            | _ => raise ERR "carrier_alpha" "raw source is not application")
          | _ => raise ERR "carrier_alpha" "identity has no changed child"
        val _ = validate_carrier_alpha g scope (#1 result)
        val _ = validate_carrier_alpha g scope (#2 result)
    in result end

  fun equality (g : graph) (left,right) =
    let
      val l = entry g left and r = entry g right
      val _ = check_scope g (#scope l)
      val _ = check_scope g (#scope r)
      val key = (node_id left,node_id right)
      val _ = if #type_id l = #type_id r then () else
        raise ERR "equality" "node types differ"
    in case Redblackmap.peek (!(#equalities g),key) of
        SOME theorem => theorem
      | NONE =>
        let
          val theorem = if left = right then Thm.REFL (#term l) else
            case (#view l,#view r) of
              (Application (lf,lx), Application (rf,rx)) =>
                align_application (#term l) (equality g (lf,rf))
                  (equality g (lx,rx)) (#term r)
            | (Variable (lk,lv),Variable (rk,rv)) =>
                if lk = rk andalso #scope l = #scope r then
                  atomic_equality g lv rv else
                  raise ERR "equality" "variable ownership differs"
            | (Constant lc,Constant rc) =>
                if KernelSig.id_compare (lc,rc) = EQUAL then
                  atomic_equality g (#term l) (#term r) else
                  raise ERR "equality" "constant declarations differ"
            | (AdmittedBinder _,AdmittedBinder _) =>
                Thm.ALPHA (#term l) (#term r)
            | (OpaqueRetained,OpaqueRetained) =>
                if Portable.pointer_eq (#term l,#term r) then
                  Thm.REFL (#term l) else
                  raise ERR "equality" "independent opaque binders unadmitted"
            | _ => raise ERR "equality" "constructors differ"
          val _ = #equalities g := Redblackmap.insert
            (!(#equalities g),key,theorem)
        in theorem end
    end

  (* Occurrences are syntax, not semantic-node traversal. In particular a
     LET contributes its body, never its RHSs; proof boundaries are opaque. *)
  fun occurrence_leaves (occurrence as Occurrence {role,children,...}) =
    case role of
        Atom => [occurrence]
      | ProofBoundary => [occurrence]
      | Let => (case List.rev children of body::_ => occurrence_leaves body
          | [] => raise ERR "occurrence_leaves" "let has no recorded body")
      | _ => List.concat (List.map occurrence_leaves children)
  fun validate_occurrence g =
    let
      fun invalid message = raise ERR "validate_occurrence" message
      fun root (Occurrence {node,...}) = node
      fun binary constant node children = case children of
          [left,right] =>
            (case view g node of Application (operator,operand) =>
              (case view g operator of Application (head,argument) =>
                (case view g head of Constant _ =>
                  if Term.same_const (representative g head) constant andalso
                      argument = root left andalso operand = root right then ()
                  else invalid "recorded connective children differ"
                | _ => invalid "recorded connective head is not constant")
              | _ => invalid "recorded connective is not binary")
            | _ => invalid "recorded connective is not an application")
        | _ => invalid "recorded connective needs two children"
      fun validate (Occurrence {node,scope,role,children}) =
        let
          val _ = check_scope g scope
          val _ = usable g scope node
          val _ = case role of
              Atom => if null children then () else
                invalid "atom has recorded children"
            | Conjunction => binary boolSyntax.conjunction node children
            | Disjunction => binary boolSyntax.disjunction node children
            | Let => (case List.rev children of body::_ =>
                if node = root body then () else
                  invalid "let body has another semantic node"
              | [] => invalid "let has no recorded body")
            | _ => ()
          fun child (item as Occurrence {scope=inner,...}) =
            (if inner = scope orelse
                ((role = Let orelse role = ProofBoundary) andalso
                 scope_visible g inner scope) then () else
               invalid "child escapes recorded scope";
             validate item)
        in List.app child children end
    in validate end

  (* Private closure-issued identity view: metadata planning, then exactly
     one REFL on execution. No import, source anchor, opening or rehome. *)
  datatype identity_closure_view_plan = IdentityViewPlan of
    {graph : graph,caller : scope,node : node,term : Term.term,
     roots : closure_child list,guard : unit -> unit,
     snapshot : identity_opened_record list,used : bool ref}
  fun identity_rows (g : graph) caller node =
    case Redblackmap.peek (!(#identity_views g),
        (scope_id caller,node_id node)) of SOME rows => rows | NONE => []
  fun same_identity_rows [] [] = true
    | same_identity_rows ((a : identity_opened_record)::xs)
        ((b : identity_opened_record)::ys) =
        same_source (#source a) (#source b) andalso same_identity_rows xs ys
    | same_identity_rows _ _ = false
  fun same_identity_roots [] [] = true
    | same_identity_roots (x::xs) (y::ys) =
        Portable.pointer_eq (x,y) andalso same_identity_roots xs ys
    | same_identity_roots _ _ = false
  fun plan_identity_closure_view (g : graph) caller maximum
      {target,retain} =
    let
      val epoch = Type.type_epoch ()
      val node = closure_child_node g caller target
      val _ = if maximum > 0 then () else
        raise ERR "identity_view" "nonpositive original metadata contract"
      val held = ref ([] : closure_child list)
      val profiles = ref ([] : opaque_profile list)
      val visited = ref (Redblackset.empty Int.compare)
      val remaining = ref maximum
      fun visit child =
        let val current = closure_child_node g caller child
            val _ = if !remaining > 0 then remaining := !remaining-1 else
              raise ERR "identity_view" "closure portfolio exceeds contract"
            val _ = held := child :: !held
        in if Redblackset.member (!visited,node_id current) then () else
          (visited := Redblackset.add (!visited,node_id current);
           case view g current of
             Application _ =>
               let val (a,b) = closure_application_children g caller child
               in visit a;visit b end
           | AdmittedBinder _ => visit (binder_closure_body g caller
               (closure_child_binder g caller child))
           | OpaqueRetained =>
               (case opaque_profile_for g caller current of NONE =>
                  raise ERR "identity_view"
                    "opaque syntax has no complete closure recipe"
                | SOME profile =>
                  (ignore (opaque_profile_data g caller profile);
                   profiles := profile :: !profiles))
           | _ => ()) end
      val _ = List.app (fn metric =>
        case unfolded_nodes g metric maximum node of SOME count =>
          if count <= maximum then () else
            raise ERR "identity_view" "cached target exceeds contract"
        | NONE => raise ERR "identity_view" "unknown cached target syntax")
        [RawNodes,BinderInclusiveNodes]
      val roots = target::retain
      val _ = List.app visit roots
      val term = representative g node
      val snapshot = identity_rows g caller node
      fun guard () =
        (check_scope g caller;
         if Type.type_epoch () = epoch then () else
           raise ERR "identity_view" "Type retirement epoch changed";
         List.app (fn child =>
           ignore (closure_child_node g caller child)) (!held);
         List.app (fn profile =>
           ignore (opaque_profile_data g caller profile)) (!profiles);
         if Portable.pointer_eq (term,representative g node) then () else
           raise ERR "identity_view" "canonical target term changed")
      val _ = guard ()
    in IdentityViewPlan {graph = g,caller = caller,node = node,term = term,
      roots = roots,guard = guard,snapshot = snapshot,used = ref false} end
  fun identity_closure_view_node
      (IdentityViewPlan {graph,caller,node,guard,snapshot,used,...}) =
    (if !used then raise ERR "identity_view" "plan already used" else ();
     guard ();
     if same_identity_rows snapshot (identity_rows graph caller node) then
       node else raise ERR "identity_view" "identity cache changed")
  fun execute_identity_closure_view
      (plan as IdentityViewPlan
        {graph,caller,node,term,roots,guard,snapshot,used}) =
    let val _ = ignore (identity_closure_view_node plan)
        val _ = used := true
        fun cached [] = NONE
          | cached ((row : identity_opened_record)::rest) =
              if same_identity_roots roots (#roots row) then
                ((#guard row) ();SOME (#source row)) else cached rest
    in case cached snapshot of SOME source => (guard ();source)
      | NONE =>
        let val theorem = Thm.REFL term val _ = guard ()
            val (left,right) = Term.dest_eq (Thm.concl theorem)
            val _ = if null (Thm.hyp theorem) andalso
                Portable.pointer_eq (left,term) andalso
                Portable.pointer_eq (right,term) then () else
              raise ERR "identity_view" "REFL exact endpoints changed"
            val source : source =
              {node = node,original = term,bridge = theorem}
            val _ = guard ()
            val _ = if same_identity_rows snapshot
                (identity_rows graph caller node) then () else
              raise ERR "identity_view" "cache changed before publication"
            val row = {source = source,roots = roots,guard = guard}
            val _ = validation_change graph
            val _ = #identity_views graph := Redblackmap.insert
              (!(#identity_views graph),(scope_id caller,node_id node),
               row::snapshot)
        in guard ();source end
    end
  fun record_identity_closure_view g caller maximum request =
    execute_identity_closure_view
      (plan_identity_closure_view g caller maximum request)
  (* Source-only additive fragment. Fixed R tables are a prerequisite.
     The local ceiling is borrowed from SAME W by the future P owner;
     this opaque metadata plan itself does not issue a Work/Root grant. *)
  datatype placeholder_row = CachedName of node * Term.term
    | NewName of node * string * Type.hol_type
  datatype placeholder_phase = NamesPrepared
    | NamesMinted of Term.term R.int_map | NamesDead
  datatype placeholder_snapshot = PlaceholderSnapshot of
    {owner : unit ref,caller : scope,nodes : entry R.int_map,
     scopes : frame R.int_map,reserved : R.string_set,
     placeholders : Term.term R.int_map,first_name : int,first_node :
       int,first_scope : int,
     epoch : int,symbols : int,
     frames : (scope * bool ref) list,next_reserved : R.string_set,
     next_name : int}
  datatype placeholder_plan = PlaceholderPlan of
    {snapshot : placeholder_snapshot,rows : placeholder_row list,
     names : (node * string) list,
     bindings : (node * string * Type.hol_type) list,
     batch : Term.term R.int_batch,
     work : IntInf.int,guard_work : IntInf.int,
     phase : placeholder_phase ref,revision : IntInf.int ref}
  (* The phase belongs to the captured plan, including foreign-call refusal.
     Update its ACTUAL graph witness, never the supplied foreign graph. *)
  fun change_placeholder_revision (revision : IntInf.int ref) =
    revision := !revision+1
  (* Private source-event interpreter. PaidGuard is not an external callback
     or allowance: the future owned P caller must pay the genuine plan cost
     to SAME W before this path. Arithmetic/meter and primitive internals are
     explicit exclusions, as in the selected fixed-table prerequisite. *)
  datatype placeholder_meter = CountGuard of
      {ceiling : IntInf.int,used : IntInf.int ref} | PaidGuard
    | PolicyCountGuard of
      {ceiling:SmtReplayResourcePolicy.limit,used:IntInf.int ref}
    | SameMeterGuard of R.scope_meter
  datatype placeholder_requirement = EitherState | PreparedState
  fun placeholder_event PaidGuard = ()
    | placeholder_event (SameMeterGuard meter) =
        (R.scope_meter_charge meter 1 handle R.Limit =>
          raise ERR "plan_placeholders" "original remaining Work exhausted")
    | placeholder_event (CountGuard {ceiling,used}) =
        if !used >= ceiling then
          raise ERR "plan_placeholders" "original remaining Work exhausted"
        else used := !used+1

    | placeholder_event (PolicyCountGuard {ceiling,used}) =
        if SmtReplayResourcePolicy.allows ceiling (!used+1) then
          used := !used+1
        else raise ERR "plan_placeholders" "original remaining Work exhausted"

  (* This ONE private program is run during planning and again before every
     validation/mint. The successful prepared/minted paths have the same
     event grammar. Every refusal is a prefix plus one retirement write. *)
  fun placeholder_guard requirement meter (g : graph) caller
      (PlaceholderSnapshot
        {owner,caller =
    held,nodes,scopes,reserved,placeholders,first_name,first_node,first_scope,
         epoch,symbols,frames,next_reserved,next_name}) phase =
    let
      val _ = placeholder_event meter
      val _ = if owner = #owner g then () else
        raise ERR "placeholder_guard" "different graph owner"
      val _ = placeholder_event meter
      val _ = if caller = held then () else
        raise ERR "placeholder_guard" "different caller scope"
      val _ = placeholder_event meter
      val state = !phase
      val _ = placeholder_event meter
      val _ = case (requirement,state) of
          (_,NamesDead) => raise ERR "placeholder_guard" "retired plan"
        | (PreparedState,NamesMinted _) =>
            raise ERR "placeholder_guard" "one-shot mint"
        | _ => ()
      val _ = placeholder_event meter
      val (names,used,counter) = case state of
          NamesPrepared => (placeholders,reserved,first_name)
        | NamesMinted table => (table,next_reserved,next_name)
        | NamesDead => raise ERR "placeholder_guard" "retired plan"
      (* The private writers are append-only: fresh node/scope IDs, absent
         placeholder keys, and growing reserved names. Prepared still binds
         the whole state; Minted retains its exact immutable entries/terms
         while allowing later authentic extensions of the same graph. *)
      fun table_matches compare held current = case state of
          NamesPrepared => compare (held,current)
        | NamesMinted _ => true
        | NamesDead => false
      fun counter_matches held current = case state of
          NamesPrepared => held = current
        | NamesMinted _ => held <= current
        | NamesDead => false
      val _ = placeholder_event meter
      val current_nodes = !(#nodes g)
      val _ = placeholder_event meter
      val _ = if table_matches R.same_int nodes current_nodes then () else
        raise ERR "placeholder_guard" "node table changed"
      val _ = placeholder_event meter
      val current_scopes = !(#scopes g)
      val _ = placeholder_event meter
      val _ = if table_matches R.same_int scopes current_scopes then () else
        raise ERR "placeholder_guard" "scope table changed"
      val _ = placeholder_event meter
      val current_reserved = !(#reserved g)
      val _ = placeholder_event meter
      val _ = if table_matches R.same_string used current_reserved then () else
        raise ERR "placeholder_guard" "reserved table changed"
      val _ = placeholder_event meter
      val current_names = !(#placeholders g)
      val _ = placeholder_event meter
      val _ = if table_matches R.same_int names current_names then () else
        raise ERR "placeholder_guard" "placeholder table changed"
      val _ = placeholder_event meter
      val current_counter = !(#next_name g)
      val _ = placeholder_event meter
      val _ = if counter_matches counter current_counter then () else
        raise ERR "placeholder_guard" "name counter changed"
      val _ = placeholder_event meter
      val current_node = !(#next g)
      val _ = placeholder_event meter
      val _ = if counter_matches first_node current_node then () else
        raise ERR "placeholder_guard" "node high-water mark changed"
      val _ = placeholder_event meter
      val current_scope = !(#next_scope g)
      val _ = placeholder_event meter
      val _ = if counter_matches first_scope current_scope then () else
        raise ERR "placeholder_guard" "scope high-water mark changed"
      val _ = placeholder_event meter
      val current_epoch = Type.type_epoch ()
      val _ = placeholder_event meter
      val _ = if epoch = current_epoch then () else
        raise ERR "placeholder_guard" "Type epoch changed"
      val _ = placeholder_event meter
      val current_symbols = Term.term_epoch ()
      val _ = placeholder_event meter
      val _ = if symbols = current_symbols then () else
        raise ERR "placeholder_guard" "Term epoch changed"
      fun check pending =
        (placeholder_event meter;case pending of [] => ()
         | (_,active)::rest =>
             let val _ = placeholder_event meter val current = !active
                 val _ = placeholder_event meter
             in if current then check rest else
               raise ERR "placeholder_guard" "captured frame retired" end)
    in check frames end

  fun placeholder_plan_cost (PlaceholderPlan {work,...}) = work
  fun placeholder_plan_guard_cost (PlaceholderPlan {guard_work,...}) =
    guard_work
  fun placeholder_plan_names (PlaceholderPlan {names,...}) = names
  fun placeholder_plan_bindings (PlaceholderPlan {bindings,...}) = bindings

  fun plan_placeholders (g : graph) caller {nodes,remaining_work} =
    let
      (* Exactly the initial conversion/ref source events are admitted before
         either exists. This is not a new semantic input/output cutoff. *)
      val _ = if remaining_work >= 2 then () else
        raise ERR "plan_placeholders" "remaining Work cannot create meter"
      val ceiling = IntInf.fromInt remaining_work
      val used = ref (2 : IntInf.int)
      fun spend amount =
        if amount < 0 orelse amount > ceiling - !used then
          raise ERR "plan_placeholders" "original remaining Work exhausted"
        else used := !used+amount
      fun tick () = spend 1
      val _ = tick ()
      val original_nodes = !(#nodes g)
      val _ = tick ()
      val original_scopes = !(#scopes g)
      val _ = tick ()
      val original_reserved = !(#reserved g)
      val _ = tick ()
      val original_placeholders = !(#placeholders g)
      val _ = tick ()
      val first_name = !(#next_name g)
      val _ = tick ()
      val first_node = !(#next g)
      val _ = tick ()
      val first_scope = !(#next_scope g)
      val _ = tick ()
      val epoch = Type.type_epoch ()
      val _ = tick ()
      val symbols = Term.term_epoch ()
      val _ = tick ()
      val frames = ref ([] : (scope * bool ref) list)
      val _ = tick ()
      val scope_values = ref ([] : (scope * frame) list)
      fun int_value table key =
        let val _ = tick ()
            val plan = R.lookup_int (table,key,ceiling - !used)
            val _ = spend (#work (R.int_lookup_cost plan))
            val _ = tick ()
        in R.int_lookup_value (table,plan) end
      fun previous scope pending =
        (tick ();case pending of [] => NONE
         | (old,value)::rest =>
             (tick ();if scope = old then (tick ();SOME value)
              else previous scope rest))
      fun scope_value (scope as Scope {owner,id}) =
        (tick ();
         if owner <> #owner g then
           raise ERR "plan_placeholders" "foreign caller/frame"
         else (tick ();case previous scope (!scope_values) of
           SOME value => value
         | NONE =>
             let val value = case int_value original_scopes id of
                     SOME value => value
                   | NONE => raise ERR "plan_placeholders" "unknown frame"
                 val _ = tick () val _ = tick () val _ = tick ()
                 val _ = scope_values := (scope,value) :: !scope_values
                 val _ = tick () val _ = tick () val _ = tick ()
                 val _ = frames := (scope,#active value) :: !frames
             in value end))
      fun alive scope =
        let val frame = scope_value scope val _ = tick ()
            val _ = if !(#active frame) then () else
              raise ERR "plan_placeholders" "retired frame"
        in tick ();case #parent frame of NONE => () | SOME p => alive p end
      fun visible scope required =
        (tick ();if scope = required then true else
         case #parent (scope_value scope) of NONE => false
         | SOME parent => visible parent required)
      val _ = alive caller
      val _ = tick () val staged_reserved = ref original_reserved
      val _ = tick () val next_name = ref first_name
      val _ = tick () val rows = ref ([] : placeholder_row list)
      val _ = tick () val names = ref ([] : (node * string) list)
      val _ = tick ()
      val bindings = ref ([] : (node * string * Type.hol_type) list)
      val _ = tick () val keys = ref ([] : int list)
      (* Local to this genuine regular plan and its original meter. Numeric
         IDs select buckets; only complete graph-owned nodes establish
         membership. There is no cross-plan cache or Work permission. *)
      val _ = spend 2
      val visited = ref (R.empty_int () : node list R.int_map)
      fun visited_entry node =
        let val _ = spend 3
            val table = !visited
            val key = node_id node
            val query = R.lookup_int (table,key,ceiling - !used)
            val _ = spend (#work (R.int_lookup_cost query))
            val _ = tick ()
            val values = case R.int_lookup_value (table,query) of
                NONE => [] | SOME values => values
        in (table,key,values) end
      fun visited_member node pending =
        (tick ();case pending of [] => false | old::rest =>
          (tick ();node = old orelse visited_member node rest))
      fun remember entry node =
        let val _ = spend 3
            val (table,key,values) = entry
            val insertion = R.insert_int (table,key,ceiling - !used)
            val _ = spend (#work (R.int_insertion_cost insertion))
            (* Actual bucket cons and publication of the finished map;
               R's quote already retains its one-shot finish programme. *)
            val _ = spend 2
            val next = R.finish_int (table,insertion,node::values)
        in visited := next end
      (* Decimal formatting has a fixed machine-int input. Borrowed source
         events reserve each digit/cons plus concatenation bytes BEFORE the
         primitive formatter/concatenator; internal primitive costs remain
         outside this event model. No arbitrary name-length cutoff exists. *)
      fun candidate id =
        let
          fun digits n = (tick ();if n < 10 then 1 else 1+digits (n div 10))
          val _ = if id < 0 then
            raise ERR "plan_placeholders" "negative name counter" else ()
          val _ = case Int.maxInt of NONE => () | SOME maximum =>
            if id < maximum then () else
              raise ERR "plan_placeholders" "name counter cannot advance"
          val n = digits id
          val _ = spend (IntInf.fromInt n)
          val decimal = Int.toString id
          val _ = spend (IntInf.fromInt (String.size "__smt_replay_"))
          val _ = spend (IntInf.fromInt n)
        in "__smt_replay_" ^ decimal end
      fun choose () =
        let val _ = tick () val id = !next_name
            val name = candidate id
            val _ = tick () val _ = tick () val _ = next_name := id+1
            val _ = tick () val staged = !staged_reserved
            val _ = tick ()
            val plan = R.lookup_string (staged,name,ceiling - !used)
            val _ = spend (#work (R.string_lookup_cost plan))
            val _ = tick ()
        in if R.string_lookup_value (staged,plan) then choose ()
           else name end
      fun one (node as Node {owner,id}) =
        let
          val _ = tick ()
          val _ = if owner = #owner g then () else
            raise ERR "plan_placeholders" "foreign node"
          val fields = case int_value original_nodes id of SOME v => v
            | NONE => raise ERR "plan_placeholders" "unknown node"
          val _ = alive (#scope fields)
          val _ = if visible caller (#scope fields) then () else
            raise ERR "plan_placeholders" "node outside original caller"
        in case int_value original_placeholders id of
            SOME term =>
              let val _ = tick () val name = #1 (Term.dest_var term)
                  val _ = tick () val _ = tick ()
                  val _ = tick () val _ = tick ()
                  val _ = rows := CachedName (node,term) :: !rows
                  val _ = tick () val _ = tick () val _ = tick ()
                  val _ = names := (node,name) :: !names
                  (* Type read, tuple, cons, write before allocation. *)
                  val _ = spend 4
                  val _ = bindings := (node,name,#ty fields) :: !bindings
              in () end
          | NONE =>
              let
                val name = choose ()
                val _ = tick () val staged = !staged_reserved
                val _ = tick ()
                val insertion = R.insert_string
                  (staged,name,ceiling - !used)
                val _ = spend (#work (R.string_insertion_cost insertion))
                val _ = tick ()
                val next = R.finish_string (staged,insertion)
                val _ = tick () val _ = staged_reserved := next
                val _ = tick () val _ = tick ()
                val _ = tick () val _ = tick ()
                val _ = rows := NewName (node,name,#ty fields) :: !rows
                val _ = tick () val _ = tick () val _ = tick ()
                val _ = names := (node,name) :: !names
                val _ = spend 4
                val _ = bindings := (node,name,#ty fields) :: !bindings
                val _ = tick () val _ = tick () val _ = keys := id :: !keys
              in () end
        end
      fun walk pending =
        (tick ();case pending of [] => () | node::rest =>
          let val entry = visited_entry node
              val _ = spend 3
              val (_,_,values) = entry
          in if visited_member node values then
               raise ERR "plan_placeholders" "duplicate naming node"
             else (one node;remember entry node;tick ();walk rest)
          end)
      val _ = walk nodes
      (* Actual private row grammar, including cached skip and empty tail.
         One event precedes each planning inspection; separate events retain
         the future branch, variable constructor and output-list cons. *)
      fun reserve_payloads pending =
        (tick ();tick ();case pending of [] => spend 4
         | CachedName _::rest =>
             (spend 5;reserve_payloads rest)
         | NewName _::rest =>
             (spend 8;reserve_payloads rest))
      val _ = reserve_payloads (!rows)
      (* Exact output reversal: tail visit, cons and branch for each row. *)
      fun reserve_reverse [] = tick ()
        | reserve_reverse (_::rest) = (spend 4;reserve_reverse rest)
      val _ = reserve_reverse (!rows)
      val batch = R.insert_int_batch
        (original_placeholders,!keys,ceiling - !used)
      val _ = spend (#work (R.int_batch_cost batch))
      (* The two immutable snapshot constructors and the phase reference
         are charged BEFORE construction. Both positive guard invocations
         share placeholder_guard; failure retirement is separately reserved. *)
      val _ = tick () val _ = tick () val _ = tick ()
      val snapshot = PlaceholderSnapshot
        {owner = #owner g,caller = caller,nodes = original_nodes,
         scopes = original_scopes,reserved = original_reserved,
         placeholders = original_placeholders,first_name = first_name,
         first_node = first_node,first_scope = first_scope,
         epoch = epoch,symbols = symbols,frames = !frames,next_reserved =
           !staged_reserved,
         next_name = !next_name}
      val phase = ref NamesPrepared
      val _ = tick () val _ = tick ()
      val meter = CountGuard {ceiling = ceiling,used = used}
      val before_guard = !used
      val _ = placeholder_guard EitherState meter g caller snapshot phase
      val positive_guard = !used-before_guard
      (* Mint's same prepared guard plus a possible refusal-retirement write.
         Future independent validation pays guard_work from SAME W. *)
      val guard_work = positive_guard+1
      val _ = spend guard_work
      (* Future phase retirement, three graph writes, minted wrapper/write;
         final immutable plan record and wrapper. No future source search. *)
      val _ = tick () val _ = tick () val _ = tick () val _ = tick ()
      val _ = tick () val _ = tick () val _ = tick () val _ = tick ()
      (* Additional retained field and its read. *)
      val _ = spend 2
    in PlaceholderPlan
      {snapshot = snapshot,rows = !rows,names = !names,
       bindings = !bindings,batch = batch,
       work = !used,guard_work = guard_work,phase = phase,
       revision = #validation_changes g} end

  fun validate_placeholder_plan g caller
      (PlaceholderPlan {snapshot,phase,revision,...}) =
    placeholder_guard EitherState PaidGuard g caller snapshot phase
    handle primary =>
      (change_placeholder_revision revision;phase := NamesDead;raise primary)

  fun mint_placeholder_terms (g : graph) caller (PlaceholderPlan
      {snapshot = snapshot as PlaceholderSnapshot
  {placeholders,next_reserved,next_name,...},rows,batch,phase,revision,...}) =
    ((placeholder_guard PreparedState PaidGuard g caller snapshot phase;
      change_placeholder_revision revision;phase := NamesDead;
      let
        fun payloads [] = ([],[])
          | payloads (CachedName (node,term)::rest) =
              let val (pairs,values) = payloads rest
              in ((node,term)::pairs,values) end
          | payloads (NewName (node,name,ty)::rest) =
              let val term = Term.mk_var (name,ty)
                  val (pairs,values) = payloads rest
              in ((node,term)::pairs,term::values) end
        val (pairs,values) = payloads rows
        val table = R.finish_int_batch (placeholders,batch,values)
        fun reverse [] result = result
          | reverse (pair::rest) result = reverse rest (pair::result)
        val ordered = reverse pairs []
        (* No callback/search/Term remains after protected preparation.
           SAME Context exclusive writer remains an explicit prerequisite. *)
        val _ = validation_change g
        val _ = #placeholders g := table
        val _ = validation_change g
        val _ = #reserved g := next_reserved
        val _ = #next_name g := next_name
        val _ = change_placeholder_revision revision
        val _ = phase := NamesMinted table
      in ordered end)
     handle primary => (change_placeholder_revision revision;phase :=
       NamesDead;raise primary))
  fun mint_placeholders g caller plan =
    ignore (mint_placeholder_terms g caller plan)

  (* Only a genuine registered carrier Alpha recipe can produce this path.
     Canonical shape authenticates traversal; raw operators/body/domain are
     inspected and retained themselves. Hidden Clos/Subst forcing remains
     outside the logical type_of envelope returned by the existing getter. *)
  fun record_opened_type_projection (g : graph) scope maximum alpha =
    let val incoming = carrier_alpha_data g scope alpha
        val node = #original incoming
        val _ = if maximum > 0 andalso
            (case view g node of OpaqueRetained => true | _ => false) then ()
          else raise ERR "record_opened_type_projection"
            "expected opaque raw endpoint and positive metadata allowance"
        val remaining = ref maximum
        val epoch = Type.type_epoch () val symbols = Term.term_epoch ()
        fun guard () = validate_carrier_alpha g scope alpha
        fun spend () =
          if !remaining > 0 then remaining := !remaining-1 else
            raise ERR "record_opened_type_projection"
              "metadata visit allowance exhausted"
        fun inspect action = (guard ();spend ();action ())
        val original = inspect (fn () => representative g node)
        val _ = if Portable.pointer_eq (original,#original (#source incoming))
          then () else raise ERR "record_opened_type_projection"
            "different actual registered raw source"
        fun walk term child =
          let val _ = guard () val _ = spend ()
              val current = closure_child_node g scope child
          in if inspect (fn () => Term.is_comb term) then
              let val (operator,_) = inspect (fn () => Term.dest_comb term)
                  val (left,_) = closure_application_children g scope child
              in ProjectionApplication (term,walk operator left) end
            else if inspect (fn () => Term.is_abs term) then
              let val binder = closure_child_binder g scope child
                  val data = binder_closure_data g scope binder
                  val (variable,_) = inspect (fn () => Term.dest_abs term)
                  val domain = inspect (fn () => Term.type_of variable)
                  val expected = type_of g (#binder data)
                  val _ = if domain = expected then () else
                    raise ERR "record_opened_type_projection"
                      "different actual binder domain"
                  val body = inspect
                    (fn () => SmtReplayImport.count_body term)
                  val child = binder_closure_body g scope binder
              in ProjectionBinder (term,domain,walk body child) end
            else
              let val variable = inspect (fn () => Term.is_var term)
                  val constant = inspect (fn () => Term.is_const term)
                  val _ = if (variable orelse constant) andalso
                    (case view g current of Application _ => false
                      | AdmittedBinder _ => false | OpaqueRetained => false
                      | _ => true) then () else
                    raise ERR "record_opened_type_projection"
                      "unrecorded actual projection atom"
              in ProjectionAtom {term = term,variable = variable} end
          end
        val path = walk original (#annotation incoming)
        (* Readiness is callback-free backing metadata, not exception
           recovery from a stale semantic getter. A projected partial child
           retains its WHOLE discovery's canonical backing paths as well. *)
        val ready_root = case alpha of CarrierPartial
              {plan = PartialDiscovery {recipe = SOME whole,...},...} =>
                closure_root g scope (#node (partial_source whole))
          | _ => #annotation incoming
        val paths = ref ([] : closure_child list)
        val seen = ref ([] : node list)
        fun collect child =
          let val _ = guard () val _ = spend ()
              val node = closure_child_node g scope child
              val _ = paths := child :: !paths
          in if List.exists (fn old => old = node) (!seen) then () else
            (seen := node :: !seen;
             case view g node of Application _ =>
                 let val (a,b) = closure_application_children g scope child
                 in collect a;collect b end
               | AdmittedBinder _ => collect (binder_closure_body g scope
                   (closure_child_binder g scope child))
               | _ => ())
          end
        val _ = collect ready_root
        val _ = collect (#annotation incoming)
        val _ = case alpha of CarrierPartial
              {plan = PartialDiscovery {original,...},...} =>
                collect (closure_root g scope original)
          | _ => ()
        fun live (ClosureRoot {owner,caller,node}) =
              owner = #owner g andalso partial_scope_live g caller andalso
              partial_scope_live g (node_scope g node)
          | live (ClosureApplicationChild {parent,node,...}) =
              live parent andalso partial_scope_live g (node_scope g node)
          | live (ClosureBodyChild {parent,record}) =
              live parent andalso partial_record_live g record
        fun ready () = partial_scope_live g scope andalso
          Type.type_epoch () = epoch andalso Term.term_epoch () = symbols
          andalso List.all live (!paths)
        val receipt = OpenedTypeProjection
          {owner = #owner g,scope = scope,node = node,original = original,
           path = path,guard = guard,ready = ready,
           visits = maximum - !remaining}
        val _ = ignore (opaque_type_projection_data g scope receipt 0)
        val rows = Option.getOpt (Redblackmap.peek
          (!(#partial_projections g),node_id node),[])
        val _ = validation_change g
        val _ = #partial_projections g := Redblackmap.insert
          (!(#partial_projections g),node_id node,receipt :: rows)
        val _ = guard ()
    in receipt end
  fun opened_type_projection_visits g scope
      (receipt as OpenedTypeProjection {visits,...}) =
        (ignore (opaque_type_projection_data g scope receipt 0);visits)
    | opened_type_projection_visits _ _ _ =
        raise ERR "opened_type_projection_visits" "not an opened path receipt"

  (* Additive import policy. Old int APIs above remain literal.
     Representable finite requests use the original exact import programs.
     Uncapped and large finite requests retain exact IntInf miss counts. *)
  datatype policy_import_plan =
      FinitePolicyImportPlan of import_plan
    | ExactPolicyImportPlan of
        {graph : graph,scope : scope,
         maximum : SmtReplayResourcePolicy.limit,original : Term.term,
         types : Type.hol_type list}
  fun policy_import_int_limit SmtReplayResourcePolicy.Uncapped = NONE
    | policy_import_int_limit (SmtReplayResourcePolicy.AtMost maximum) =
        (SOME (IntInf.toInt maximum) handle Overflow => NONE)
  fun plan_exact_policy_imports g scope maximum originals =
    let
      val _ = check_scope g scope
      val _ = if SmtReplayResourcePolicy.positive maximum then () else
        raise ERR "import" "nonpositive application import budget"
      val buckets = 4093
      val seen = Array.array (buckets,[] : Term.term list)
      val observations = ref (0 : IntInf.int)
      val types = ref ([] : Type.hol_type list)
      fun visit term = case memo_peek g scope term of SOME _ => ()
        | NONE =>
          let val bucket = SmtReplayImport.pointer_bucket 4 buckets term
              val held = Array.sub (seen,bucket)
          in if List.exists (fn old => Portable.pointer_eq (old,term)) held
             then () else
             let
               val _ = observations := !observations+1
               val _ = if SmtReplayResourcePolicy.allows maximum
                   (!observations) then () else
                 raise ERR "import"
                   "application import DAG budget exhausted"
               val _ = Array.update (seen,bucket,term :: held)
               val _ = types := Term.type_of term :: !types
             in if Term.is_comb term then
                  let val (f,x) = Term.dest_comb term in visit f;visit x end
                else if Term.is_var term orelse Term.is_const term orelse
                    Term.is_abs term then () else
                  raise ERR "import" "unexpected public term constructor"
             end
          end
      fun plan original =
        let val _ = observations := 0
            val _ = types := []
            val _ = visit original
        in ExactPolicyImportPlan {graph = g,scope = scope,maximum = maximum,
          original = original,types = List.rev (!types)} end
    in List.map plan originals end
  fun plan_imports_with_policy g scope maximum originals =
    case policy_import_int_limit maximum of
        SOME finite => List.map FinitePolicyImportPlan
          (plan_imports g scope finite originals)
      | NONE => plan_exact_policy_imports g scope maximum originals
  fun plan_import_with_policy g scope maximum original =
    List.hd (plan_imports_with_policy g scope maximum [original])
  fun import_types_with_policy (FinitePolicyImportPlan plan) =
        import_types plan
    | import_types_with_policy
        (ExactPolicyImportPlan {graph,scope,types,...}) =
        (check_scope graph scope;types)
  fun execute_import_with_policy (FinitePolicyImportPlan plan) =
        execute_import plan
    | execute_import_with_policy
        (ExactPolicyImportPlan
          {graph = g,scope,maximum,original,...}) =

    let
      val _ = check_scope g scope
      val _ = if SmtReplayResourcePolicy.positive maximum then () else
        raise ERR "import" "nonpositive application import budget"
      val observations = ref (0 : IntInf.int)
      fun visit term = case memo_peek g scope term of
          SOME source => source
        | NONE =>
          let
            val _ = observations := !observations + 1
            val _ = if SmtReplayResourcePolicy.allows maximum
                (!observations) then () else
              raise ERR "import" "application import DAG budget exhausted"
            val (node,theorem) =
              if Term.is_comb term then
                let
                  val (left,right) = Term.dest_comb term
                  val l = visit left and r = visit right
                  val node = application g scope (#node l,#node r)
                in (node,align_application term (#bridge l) (#bridge r)
                      (representative g node)) end
              else if Term.is_var term orelse Term.is_const term then
                import_atom g scope term
              else if Term.is_abs term then
                let
                  val ty = Term.type_of term
                  val node = fresh g
                    {scope = scope, ty = ty, type_id = intern_type g ty,
                     term = term, view = OpaqueRetained,
                     raw = NONE, inclusive = NONE, source = ref NONE}
                in (node,Thm.REFL term) end
              else raise ERR "import" "unexpected public term constructor"
            val source = source_for g term node theorem
            val _ = memo_save g scope source
          in source end
    in visit original end

  fun import_with_policy g scope maximum original =
    execute_import_with_policy
      (plan_import_with_policy g scope maximum original)

  fun prepare_exact_scope_path (g:graph) caller {remaining_work} =
    let
      val _ = if SmtReplayResourcePolicy.allows remaining_work 2 then () else
        raise ERR "prepare_scope_path" "remaining Work cannot create meter"
      val ceiling = remaining_work
      val used = ref (2:IntInf.int)
      fun spend amount =
        if SmtReplayResourcePolicy.allows
            (SmtReplayResourcePolicy.remaining ceiling (!used)) amount then
          used := !used+amount else
          raise ERR "prepare_scope_path" "original remaining Work exhausted"
      fun tick () = spend 1
      val _ = tick ()
      val table = !(#scopes g)
      fun capture (current as Scope {owner,id}) =
        let val _ = spend 4
            val _ = if owner = #owner g then () else
              raise ERR "prepare_scope_path" "different graph scope"
            val _ = tick ()
            val lookup = R.lookup_int_with_policy
              (table,id,SmtReplayResourcePolicy.remaining ceiling
                (!used))
            val _ = tick ()
            val _ = spend (#work (R.int_lookup_cost lookup))
            val _ = spend 2
            val frame = case R.int_lookup_value (table,lookup) of
                SOME value => value | NONE =>
                  raise ERR "prepare_scope_path" "unknown scope"
            val _ = tick ()
            val parent = #parent frame
            val _ = tick ()
            val (tail,future) = case parent of NONE =>
                (tick ();([],1:IntInf.int))
              | SOME outer => capture outer
            (* Ref selection, private cons, return pair; every future
               retained frame has list-pattern/ref-read/branch events. *)
            val _ = spend 4
        in (#active frame::tail,future+3) end
      val (frames,validation) = capture caller
      (* Owner and caller comparisons/branches precede every held frame. *)
      val _ = spend 1
      val validation = validation+5
      val _ = spend 3
    in ScopePath {owner= #owner g,scope=caller,frames=frames,
      setup= !used,validation=validation} end
  fun prepare_scope_path_with_policy g caller
      {remaining_work} =
    case policy_import_int_limit remaining_work of
        SOME finite => prepare_scope_path g caller {remaining_work=finite}
      | NONE => prepare_exact_scope_path g caller
          {remaining_work=remaining_work}
  fun prepare_shared_scope_path_policy (g:graph) caller meter =
    let
      val initial = R.scope_meter_charged_policy meter
      val _ = R.scope_meter_charge meter 2
      val table = !(#scopes g)
      fun capture (current as Scope {owner,id}) =
        let
          val _ = R.scope_meter_charge meter 4
          val _ = if owner = #owner g then () else
            raise ERR "prepare_shared_scope_path" "different graph scope"
          val _ = R.scope_meter_charge meter 2
          val frame = case R.scope_lookup_int meter (table,id) of
              SOME value => value | NONE =>
                raise ERR "prepare_shared_scope_path" "unknown scope"
          val _ = R.scope_meter_charge meter 2
          val (tail,chain,future) = case #parent frame of NONE =>
              (R.scope_meter_charge meter 2;([],[],1:IntInf.int))
            | SOME parent => capture parent
          val _ = R.scope_meter_charge meter 6
        in (#active frame::tail,current::chain,future+3) end
      val (frames,chain,validation) = capture caller
      val _ = R.scope_meter_charge meter 6
      val path = ScopePath {owner= #owner g,scope=caller,frames=frames,
        setup=R.scope_meter_charged_policy meter-initial,
        validation=validation+5}
    in (path,chain) end

  fun prepare_binding_scope_path_policy (g:graph) active required meter =
    let
      val (active_path,chain) = prepare_shared_scope_path_policy g active meter
      val (required_path,_) = prepare_shared_scope_path_policy g required meter
      fun contains [] = (R.scope_meter_charge meter 1;false)
        | contains (current::rest) =
            (R.scope_meter_charge meter 3;
             current = required orelse contains rest)
      val visible = contains chain
      val _ = R.scope_meter_charge meter 8
      val validation = scope_path_validation_work active_path +
        scope_path_validation_work required_path + 8
    in BindingScopePath {owner= #owner g,active=active,required=required,
      active_path=active_path,required_path=required_path,visible=visible,
      validation=validation} end

  (* Exact policy-route metrics are retained by this completed result.
     They are never projected into legacy int opaque-profile caches. *)
  datatype policy_opaque_profile = PolicyOpaqueProfile of
    {owner:unit ref,scope:scope,node:node,original:Term.term,
     raw:IntInf.int,inc:IntInf.int,ann:IntInf.int,ty:IntInf.int,
     type_bytes:IntInf.int,types:Type.hol_type list,
     heads:Term.term list,ready:unit->bool,guard:unit->unit}
  datatype policy_partial_discovery = PolicyPartialDiscovery of
    {owner:unit ref,scope:scope,plan:partial_discovery,
     maximum:SmtReplayResourcePolicy.limit,
     scan_limit:SmtReplayResourcePolicy.limit,scans:IntInf.int,
     profiles:policy_opaque_profile list}
  fun policy_discovery_plus (a:IntInf.int) (b:IntInf.int) = a+b

  datatype policy_metric_task = PolicyMetricVisit of node
    | PolicyMetricJoin of node * int * node list
  (* Memoize real owned constructors, then sum each child incidence. No
     cached saturated int is an exact metric or a caller-supplied bound. *)
  fun policy_node_metrics g root =
    let
      val memo=ref (Redblackmap.mkDict Int.compare)
      val pending=ref (Redblackset.empty Int.compare)
      fun save current result =
        (memo := Redblackmap.insert (!memo,node_id current,result);
         pending := Redblackset.delete (!pending,node_id current))
      fun get current=case Redblackmap.peek (!memo,node_id current) of
          SOME value=>value
        | NONE=>raise ERR "policy_node_metrics" "unfinished actual child"
      fun add children (raw:IntInf.int) (inc:IntInf.int) =
        case children of []=>SOME(raw,inc)
        | child::rest=>case get child of NONE=>NONE
          | SOME(r,i)=>add rest (raw+r) (inc+i)
      fun loop []=get root
        | loop (PolicyMetricVisit current::rest)=
          (case Redblackmap.peek (!memo,node_id current) of
            SOME _=>loop rest
          | NONE=>
            let
              val fields=entry g current
              val key=node_id current
              val _=if Redblackset.member (!pending,key) then
                  raise ERR "policy_node_metrics" "cyclic actual graph"
                else pending := Redblackset.add (!pending,key)
              fun children own nodes = loop
                (List.map PolicyMetricVisit nodes @
                 PolicyMetricJoin(current,own,nodes)::rest)
            in case #view fields of
                Variable _ => (save current (SOME(1,1));loop rest)
              | Constant _ => (save current (SOME(1,1));loop rest)
              | OpaqueRetained => (save current NONE;loop rest)
              | Application(left,right)=>children 1 [left,right]
              | AdmittedBinder {body,...}=>children 2 [body]
            end)
        | loop (PolicyMetricJoin(current,own,children)::rest)=
            let val result=add children (1:IntInf.int) (IntInf.fromInt own)
                val _=save current result
            in loop rest end
    in loop [PolicyMetricVisit root] end
  fun policy_metric_int value = SOME (IntInf.toInt value)
    handle Overflow=>NONE

  fun abstraction_with_policy g scope maximum (binder,body) =
    let
      val _ = check_scope g scope
      val binder_fields = entry g binder
      val _ = if scope_visible g (#scope binder_fields) scope then () else
        raise ERR "abstraction" "binder frame is outside the enclosing scope"
      val _ = case #view binder_fields of Variable (Bound,_) => ()
        | _ => raise ERR "abstraction" "binder is not a scoped bound variable"
      val body_scope = node_scope g body
      val _ = if scope_visible g (#scope binder_fields) body_scope orelse
          scope_visible g body_scope (#scope binder_fields) then () else
        raise ERR "abstraction" "body is outside the declaring binder frame"
      val body_fields = entry g body
      val exact = policy_node_metrics g body
      val (raw,inclusive) = case exact of NONE =>
          raise ERR "abstraction" "opaque binder body is unadmitted"
        | SOME(r,i) =>
          if SmtReplayResourcePolicy.allows maximum (r+1) then
            (policy_metric_int (r+1),policy_metric_int (i+2))
          else raise ERR "abstraction" "bounded binder budget exhausted"
      val binder_name = #1 (Term.dest_var (#term binder_fields))
      val _ = case free_variable_nodes g body of NONE =>
          raise ERR "abstraction" "unknown free-variable binder body"
        | SOME variables => List.app (fn node =>
            (if node = binder then () else usable g scope node;
            if node <> binder andalso
               type_id g node = #type_id binder_fields andalso
               #1 (Term.dest_var (representative g node)) = binder_name then
              raise ERR "abstraction"
                "binder captures a different graph variable"
            else ())) variables
      val term = Term.mk_abs (#term binder_fields,#term body_fields)
      val ty = Type.mk_type ("fun",[#ty binder_fields,#ty body_fields])
    in fresh g
      {scope = scope, ty = ty, type_id = intern_type g ty, term = term,
       view = AdmittedBinder {binder = binder,body = body,
                             frame = #scope binder_fields},
       raw = raw, inclusive = inclusive, source = ref NONE}
    end

  fun recorded_abstraction_with_policy (g : graph) scope maximum
      {binder,body,body_frame} =
    let
      val _ = check_scope g scope
      val _ = check_scope g body_frame
      val binder_frame = node_scope g binder
      val _ = check_scope g binder_frame
      val _ = if scope_visible g body_frame binder_frame then () else
        raise ERR "recorded_abstraction" "body frame outside binder frame"
      val _ = usable g body_frame binder
      val _ = usable g body_frame body
      val node = abstraction_with_policy g scope maximum (binder,body)
      val creation : binder_closure_creation =
        {identity = ref (),node = node,declaring_scope = scope,
         binder = binder,binder_term = representative g binder,
         binder_frame = binder_frame,body = body,body_frame = body_frame}
      val record = ClosureRecord {identity = ref (),owner = #owner g,
        node = node,node_frame = scope,creation = creation,backing = NONE}
      val next = Redblackmap.insert (!(#binder_closures g),node_id node,record)
      val _ = validation_change g
      val _ = #binder_closures g := next
    in node end

  fun admit_binder_record_with_policy (g : graph) scope maximum original =
    let
      val _ = check_scope g scope
      val _ = if Term.is_abs original then () else
        raise ERR "admit_binder" "not an abstraction"
      val _ = case SmtReplayImport.raw_size_with_policy maximum original of
          SOME _ => ()
        | NONE => raise ERR "admit_binder" "bounded binder budget exhausted"
      val table = Option.getOpt
        (Redblackmap.peek (!(#binders g),scope_id scope),
         Redblackmap.mkDict Term.compare)
    in case Redblackmap.peek (table,original) of
        SOME (admission : admitted_binder_origin) =>
          let val node = #node admission
              val indexed = indexed_binder_origin g node
              val _ = if #identity indexed = #identity admission then () else
                raise ERR "admit_binder" "cached first origin differs"
          in (source_for g original node
            (Thm.ALPHA original (representative g node)),admission) end
      | NONE =>
        let
          val (binder_term,body_term) = Term.dest_abs original
          val frame = new_scope g scope []
          val binder = variable g frame Bound binder_term
          val body_frame = new_scope g frame [(binder_term,binder)]
          fun bounded term = case memo_peek g body_frame term of
              SOME source =>
                (case view g (#node source) of OpaqueRetained => compute term
                 | _ => source)
            | NONE => compute term
          and compute term =
            let val source =
              if Term.is_abs term then
                #1 (admit_binder_record_with_policy g body_frame maximum term)
              else if Term.is_comb term then
              let
                val (left,right) = Term.dest_comb term
                val l = bounded left and r = bounded right
                val node = application g body_frame (#node l,#node r)
              in source_for g term node
                (align_application term (#bridge l) (#bridge r)
                  (representative g node)) end
              else import_with_policy g body_frame maximum term
              val _ = memo_save g body_frame source
            in source end
          val body = bounded body_term
          val node = recorded_abstraction_with_policy g scope maximum
            {binder = binder,body = #node body,body_frame = body_frame}
          val theorem = Thm.TRANS
            (Thm.ALPHA original
              (Term.mk_abs (binder_term,#original body)))
            (Thm.TRANS (Thm.ABS binder_term (#bridge body))
              (Thm.ALPHA
                (Term.mk_abs (binder_term,representative g (#node body)))
                (representative g node)))
          val source = source_for g original node theorem
          (* All these are the actual held values used above. Publish only
             AFTER the whole source bridge passes its endpoint checks. *)
          val admission : admitted_binder_origin =
            {identity = ref (),owner = #owner g,scope = scope,
             first_input = original,
             binder_term = binder_term,binder = binder,frame = frame,
             body_frame = body_frame,body = body,node = node,
             first_whole = source}
          val _ = case Redblackmap.peek (!(#binder_origins g),node_id node) of
              NONE => ()
            | SOME _ => raise ERR "admit_binder"
                "admission node already indexed"
          (* Stage both immutable dictionaries before publishing references.
             Missing/partial metadata always fails closed in new getters. *)
          val next_binders = Redblackmap.insert (!(#binders g),scope_id scope,
            Redblackmap.insert (table,original,admission))
          val next_origins = Redblackmap.insert
            (!(#binder_origins g),node_id node,admission)
          val _ = validation_change g
          val _ = #binders g := next_binders
          val _ = validation_change g
          val _ = #binder_origins g := next_origins
        in (source,admission) end
    end

  fun admit_binder_with_policy g scope maximum original =
    #1 (admit_binder_record_with_policy g scope maximum original)

  fun record_opened_view_with_policy (g : graph) scope maximum original =
    let
      val _ = check_scope g scope
      val _ = usable g scope original
      val _ = if SmtReplayResourcePolicy.positive maximum then () else
        raise ERR "record_opened_view" "nonpositive discovery budget"
      val observations = ref (0:IntInf.int)
      fun key node = (scope_id scope,node_id node)
      fun visit node =
        (usable g scope node;
         case Redblackmap.peek (!(#opened_views g),key node) of
           SOME record => #source record
         | NONE =>
           let
             val _ = if SmtReplayResourcePolicy.allows maximum
                 (!observations+1) then observations := !observations+1
               else raise ERR "record_opened_view"
                 "opened recipe discovery budget exhausted"
             val term = representative g node
             val (source,recipe) = case view g node of
                 OpaqueRetained =>
                   let val (source,admission) =
                     admit_binder_record_with_policy g scope maximum term
                   in (source,OpenedBinder admission) end
               | Application (operator,operand) =>
                   let val left = visit operator val right = visit operand
                       val rich = application g scope
                         (#node left,#node right)
                       val bridge = align_application term (#bridge left)
                         (#bridge right) (representative g rich)
                   in (source_for g term rich bridge,
                       OpenedApplication (operator,operand)) end
               | _ => (source_for g term node (Thm.REFL term),OpenedAtom)
             val _ = validation_change g
             val _ = #opened_views g := Redblackmap.insert
               (!(#opened_views g),key node,{source = source,recipe = recipe})
           in source end)
    in visit original end

  fun discover_partial_with_policy (g : graph) scope
      {original,maximum,scan_limit,step} =
    let
      val _ = check_scope g scope val _ = usable g scope original
      val _ = if SmtReplayResourcePolicy.positive maximum andalso
          SmtReplayResourcePolicy.positive scan_limit then () else
        raise ERR "discover_partial" "nonpositive discovery bound"
      val _ = case !(#partial_running g) of NONE => ()
        | SOME active =>
            (active := false;
             raise ERR "discover_partial" "partial discovery reentry")
      val running = ref true
      val _ = #partial_running g := SOME running
      val epoch = Type.type_epoch () val symbols = Term.term_epoch ()
      val scans = ref (0:IntInf.int)
      val profiles = ref ([]:policy_opaque_profile list)
      fun consume_scan message =
        if SmtReplayResourcePolicy.allows scan_limit (!scans+1) then
          scans := !scans+1 else raise ERR "discover_partial" message
      val guards = ref ([] : (unit -> unit) list)
      val closures = ref ([] : binder_closure list)
      fun valid frame =
        (check_scope g scope;check_scope g frame;
         if !running andalso Type.type_epoch () = epoch andalso
             Term.term_epoch () = symbols then () else
           raise ERR "discover_partial" "scope/epoch/action retired";
         List.app (fn guard => guard ()) (!guards))
      fun debit frame =
        (valid frame;
         consume_scan "discovery scan budget exhausted";
         step ();valid frame)
      fun invoke frame action =
        (debit frame;
         let val value = action () val _ = valid frame in value end)
      fun domain_needed frame ty =
        if invoke frame (fn () => Type.compare (ty,numSyntax.num) = EQUAL)
          then true
        else case invoke frame (fn () => Lib.total Type.dom_rng ty) of
            NONE => false
          | SOME (_,range) => invoke frame
              (fn () => Type.compare (range,numSyntax.num) = EQUAL)
      fun quantified frame operator abstraction get_type =
        if abstraction andalso
            invoke frame (fn () => Term.is_const operator) andalso
            invoke frame (fn () =>
              Term.same_const operator boolSyntax.universal orelse
              Term.same_const operator boolSyntax.existential) then
          let val ty = invoke frame get_type
          in case invoke frame (fn () => Lib.total Type.dom_rng ty) of
                SOME (domain,_) => domain_needed frame domain
              | NONE => false
          end
        else false
      (* Count-body substitutes only an ATOMIC marker. Recognition uses
         constructors, fixed declaration IDs and types, never variable names,
         equality of free variables, matching or semantic proof search. *)
      fun term_needed frame term =
        if invoke frame (fn () => Term.is_comb term) then
          let val (operator,operand) = invoke frame
                (fn () => Term.dest_comb term)
          in if invoke frame (fn () => Term.is_abs operator) orelse
              quantified frame operator
                (invoke frame (fn () => Term.is_abs operand))
                (fn () => Term.type_of operand) then true
            else term_needed frame operator orelse term_needed frame operand
          end
        else if invoke frame (fn () => Term.is_abs term) then
          term_needed frame (invoke frame
            (fn () => SmtReplayImport.count_body term))
        else false
      val seen = ref
        (Redblackmap.mkDict (pair_compare Int.compare Int.compare))
      val captured = ref
        (Redblackmap.mkDict (pair_compare Int.compare Int.compare))
      (* Private callback-free setup holds all genuinely recorded frames
         BEFORE a step can retire one. No node_scope(body) inference.
         Setup map/frame work remains a separate unquoted prerequisite. *)
      fun capture_paths frame node =
        let val _ = valid frame val _ = usable g frame node
            val key = (scope_id frame,node_id node)
        in case Redblackmap.peek (!captured,key) of SOME _ => ()
          | NONE =>
            let val _ = consume_scan "frame scan budget exhausted"
                val _ = captured := Redblackmap.insert (!captured,key,())
            in case view g node of
                Application (left,right) =>
                  (capture_paths frame left;capture_paths frame right)
              | AdmittedBinder _ =>
                  let val closure = binder_closure g frame node
                      val data = binder_closure_data g frame closure
                      fun guard () = ignore
                        (binder_closure_data g frame closure)
                      val _ = guards := guard :: !guards
                      val _ = closures := closure :: !closures
                  in capture_paths (#body_frame data) (#body data) end
              | _ => ()
            end
        end
      fun graph_needed frame node =
        let val _ = valid frame val _ = usable g frame node
            val _ = debit frame val key = (scope_id frame,node_id node)
        in case Redblackmap.peek (!seen,key) of SOME value => value
          | NONE =>
            let val answer = case invoke frame (fn () => view g node) of
                  Application (operator,operand) =>
                    let val operator_view = invoke frame
                          (fn () => view g operator)
                        val beta = case operator_view of
                            AdmittedBinder _ => true | OpaqueRetained => true
                          | _ => false
                        val operand_view = invoke frame
                          (fn () => view g operand)
                        val abstraction = case operand_view of
                            AdmittedBinder _ => true | OpaqueRetained => true
                          | _ => false
                        val carrier = quantified frame
                          (invoke frame (fn () => representative g operator))
                          abstraction (fn () => type_of g operand)
                    in beta orelse carrier orelse
                      graph_needed frame operator orelse
                      graph_needed frame operand end
                | OpaqueRetained => term_needed frame
                    (invoke frame (fn () => representative g node))
                | AdmittedBinder _ =>
                    let val closure = invoke frame
                          (fn () => binder_closure g frame node)
                        val data = invoke frame
                          (fn () => binder_closure_data g frame closure)
                        fun guard () = ignore
                          (binder_closure_data g frame closure)
                        val _ = guard ()
                    in graph_needed (#body_frame data) (#body data) end
                | _ => false
                val _ = valid frame
                val _ = seen := Redblackmap.insert (!seen,key,answer)
            in answer end
        end
      fun retained_guard () =
        (check_scope g scope;usable g scope original;
         if Type.type_epoch () = epoch andalso Term.term_epoch () = symbols
           then () else raise ERR "partial_view" "discovery epoch changed";
         List.app (fn guard => guard ()) (!guards))
      (* Only a child whose complete rule scan was false reaches this
         collector. It quotes full repeated annotations for mixed proof
         assembly; a whole unchanged NONE root needs no new type envelope. *)
      fun retained_ready () =
        partial_scope_live g scope andalso
        Type.type_epoch () = epoch andalso Term.term_epoch () = symbols
        andalso List.all (fn BinderClosure {record,...} =>
          partial_record_live g record) (!closures)
      fun retain_opaque node =
        let val _ = if graph_needed scope node then
              raise ERR "retain_opaque" "relevant binder is not a no-op"
            else ()
            val memo = Array.array (4093,[])
            val types = ref ([] : Type.hol_type list)
            val heads = ref ([] : Term.term list)
            fun add (a : IntInf.int) (b : IntInf.int) = a+b
            fun text_bytes text : IntInf.int =
              let val size = String.size text
                  fun walk index = if index = size then () else
                    (debit scope;ignore (String.sub (text,index));
                     walk (index+1))
                  val _ = walk 0
              in IntInf.fromInt size end
            fun weight ty : IntInf.int * IntInf.int =
              let val _ = debit scope
              in if invoke scope (fn () => Type.is_vartype ty) then
                  (1,text_bytes (invoke scope
                    (fn () => Type.dest_vartype ty)))
                else
                  let val {Thy,Tyop,Args} = invoke scope
                        (fn () => Type.dest_thy_typeid ty)
                      val name = invoke scope (fn () => KernelSig.name_of Tyop)
                      val own = add (text_bytes Thy) (text_bytes name)
                  in List.foldl (fn (child,(nodes,bytes)) =>
                       let val (n,b) = weight child
                       in (add nodes n,add bytes b) end) (1,own) Args end
              end
            fun annotation ty =
              let val counts = weight ty val _ = debit scope
                  val _ = types := ty :: !types
              in counts end
            fun lookup term [] = NONE
              | lookup term ((held,value)::rest) =
                  (debit scope;if Portable.pointer_eq (term,held) then
                    SOME value else lookup term rest)
            fun visit term =
              let val bucket = invoke scope (fn () => physical_hint term)
                  val _ = debit scope
              in case lookup term (Array.sub (memo,bucket)) of
                  SOME value => value
                | NONE =>
                  let val ty = invoke scope (fn () => Term.type_of term)
                      val (own,own_bytes) = annotation ty
                      val value = if invoke scope (fn () => Term.is_comb term)
                        then
                          let val (f,x) = invoke scope
                                (fn () => Term.dest_comb term)
                              val a = visit f val b = visit x
                          in {raw = policy_discovery_plus 1
                                (policy_discovery_plus (#raw a) (#raw b)),
                              inc = policy_discovery_plus 1
                                (policy_discovery_plus (#inc a) (#inc b)),
                              ann = add own (add (#ann a) (#ann b)),
                              type_bytes = add own_bytes
                                (add (#type_bytes a) (#type_bytes b)),
                              ty = own,projection = Option.map
                                (fn path => ProjectionApplication (term,path))
                                (#projection a)} end
                        else if invoke scope
                            (fn () => Term.is_abs term) then
                          let val domain = invoke scope
                                (fn () => #1 (Type.dom_rng ty))
                              val (binder,binder_bytes) = annotation domain
                              val body = visit (invoke scope
                                (fn () => SmtReplayImport.count_body term))
                          in {raw = policy_discovery_plus 1 (#raw body),
                              inc = policy_discovery_plus 2 (#inc body),
                              ann = add own (add binder (#ann body)),
                              type_bytes = add own_bytes
                                (add binder_bytes (#type_bytes body)),ty = own,
                              projection = Option.map
                                (fn path =>
                                  ProjectionBinder (term,domain,path))
                                (#projection body)}
                          end
                        else
                          let val _ = if invoke scope
                                  (fn () => Term.is_const term) then
                                heads := term :: !heads else ()
                          in {raw = 1,inc = 1,ann = own,
                              type_bytes = own_bytes,ty = own,
                              projection = if false then
                                SOME (ProjectionAtom {term = term,
                                  variable = invoke scope
                                    (fn () => Term.is_var term)}) else NONE}
                          end
                      val _ = debit scope
                      val _ = Array.update (memo,bucket,
                        (term,value) :: Array.sub (memo,bucket))
                  in value end
              end
            val original = invoke scope (fn () => representative g node)
            val value = visit original
            val profile = PolicyOpaqueProfile
              {owner = #owner g,scope = scope,node = node,
               original = original,raw = #raw value,inc = #inc value,
               ann = #ann value,ty = #ty value,
               type_bytes = #type_bytes value,types = !types,
               heads = !heads,
               ready = retained_ready,guard = retained_guard}
            val _ = valid scope
            val _ = validation_change g
            val _ = profiles := profile :: !profiles
        in () end
      fun atom node retained =
        let val _ = if retained then (case view g node of
                  OpaqueRetained => retain_opaque node | _ => ()) else ()
            val term = invoke scope (fn () => representative g node)
            val proof = invoke scope (fn () => Thm.REFL term)
            val source = source_for g term node proof
        in if retained then PartialRetained (node,source)
           else PartialAtom (node,source) end
      fun opened node =
        let val source = invoke scope
              (fn () => record_opened_view_with_policy g scope maximum node)
            val _ = capture_paths scope (#node source)
        in PartialFull (node,source) end
      val recipe_memo = ref ([] : (node * bool * partial_recipe) list)
      fun cached_recipe force node [] = NONE
        | cached_recipe force node ((saved,mode,recipe)::rest) =
            (debit scope;
             if saved = node andalso mode = force then SOME recipe
             else cached_recipe force node rest)
      (* Whole original and opened backing paths were captured before this
         point. All incoming owners/epochs/scopes are rechecked before a
         hit, including after the caller's charged discovery hook. The key
         is actual original node AND force mode in this one fixed scope. *)
      fun visit force node =
        (valid scope;usable g scope node;
         case cached_recipe force node (!recipe_memo) of SOME recipe =>
           (valid scope;usable g scope node;recipe)
         | NONE =>
           let val recipe = visit_fresh force node
               val _ = debit scope
               val _ = recipe_memo := (node,force,recipe) :: !recipe_memo
               val _ = valid scope
           in recipe end)
      and visit_fresh force node =
        (valid scope;usable g scope node;
         case invoke scope (fn () => view g node) of
           OpaqueRetained =>
             if force orelse graph_needed scope node then
               opened node
             else atom node true
         | AdmittedBinder _ =>
             if force orelse graph_needed scope node then
               opened node
             else atom node true
         | Application (operator,operand) =>
             let val ov = invoke scope (fn () => view g operator)
                 val beta = case ov of AdmittedBinder _ => true
                   | OpaqueRetained => true | _ => false
                 val operand_view = invoke scope (fn () => view g operand)
                 val abstraction = case operand_view of
                     AdmittedBinder _ => true | OpaqueRetained => true
                   | _ => false
                 val carrier = quantified scope
                   (invoke scope (fn () => representative g operator))
                   abstraction (fn () => type_of g operand)
                 val left = visit beta operator
                 val right = visit carrier operand
                 val l = partial_source left val r = partial_source right
                 val term = invoke scope (fn () => representative g node)
                 val target = invoke scope
                   (fn () => application g scope (#node l,#node r))
                 val bridge = invoke scope (fn () =>
                   align_application term (#bridge l) (#bridge r)
                     (representative g target))
                 val source = source_for g term target bridge
             in PartialApplication (node,source,left,right) end
         | _ => atom node false)
      fun build () =
        let val _ = capture_paths scope original
            val changed = graph_needed scope original
            val recipe = if changed then SOME (visit false original) else NONE
            val result = PartialDiscovery
              {owner = #owner g,scope = scope,original = original,
               recipe = recipe,guard = retained_guard}
            val _ = valid scope
            val _ = case recipe of NONE => () | SOME value =>
              let val source = partial_source value
                  val row = {source = source,roots =
                    [closure_root g scope original],guard = fn () =>
                      (retained_guard ();
                       validate_partial_recipe g scope value)}
                  val key = (scope_id scope,node_id original)
                  val rows = Option.getOpt
                    (Redblackmap.peek (!(#identity_views g),key),[])
                  val old = Option.getOpt
                    (Redblackmap.peek (!(#partial_sources g),key),[])
                  val _ = validation_change g
                  val _ = #partial_sources g := Redblackmap.insert
                    (!(#partial_sources g),key,result :: old)
              in validation_change g;
                 #identity_views g := Redblackmap.insert
                (!(#identity_views g),key,row :: rows) end
        in result end
      val result = build () handle primary =>
        (running := false;#partial_running g := NONE;raise primary)
      val _ = running := false val _ = #partial_running g := NONE
    in PolicyPartialDiscovery {owner= #owner g,scope=scope,plan=result,
      maximum=maximum,scan_limit=scan_limit,scans= !scans,
      profiles=List.rev (!profiles)} end

  fun validate_partial_with_policy (g:graph) scope
      (result as PolicyPartialDiscovery {owner,scope=held,...}) =
    if owner= #owner g andalso scope=held then
      let val PolicyPartialDiscovery {plan,...}=result
      in validate_partial g scope plan end
    else raise ERR "validate_partial" "different graph/source caller"
  fun partial_view_with_policy g scope result =
    let val _=validate_partial_with_policy g scope result
        val PolicyPartialDiscovery
          {plan=PartialDiscovery {recipe,...},...}=result
    in Option.map partial_source recipe end
  fun partial_discovery_policy_data g scope result =
    let val _=validate_partial_with_policy g scope result
        val PolicyPartialDiscovery {maximum,scan_limit,scans,...}=result
    in {maximum=maximum,scan_limit=scan_limit,scans=scans} end
  fun partial_profiles_with_policy g scope result =
    let val _=validate_partial_with_policy g scope result
        val PolicyPartialDiscovery {profiles,...}=result
    in profiles end
  fun opaque_profile_data_with_policy (g:graph) scope
      (profile as PolicyOpaqueProfile {owner,...}) =
    if owner= #owner g then
      let val PolicyOpaqueProfile
            {scope=held,node,original,raw,inc,ann,ty,type_bytes,types,
             guard,...}
              =profile
          val _=check_scope g scope
          val _=usable g scope node
          val _=check_scope g held
          val _=if scope_visible g scope held andalso
           Portable.pointer_eq (original,representative g node) then () else
            raise ERR "opaque_profile_data" "different retained frame/term"
          val _=guard ()
      in {node=node,raw=raw,inc=inc,ann=ann,ty=ty,type_bytes=type_bytes,
        types=types} end
    else raise ERR "opaque_profile_data" "foreign graph profile"

  (* Preserve old representable finite metric/profile lookup. The exact
     route counts genuine constructors and never opens opaque binders. *)
  fun exact_unfolded_nodes_with_policy g metric maximum node =
    let
      val _=if SmtReplayResourcePolicy.allows maximum 0 then () else
        raise ERR "unfolded_nodes" "invalid size limit"
      val _=entry g node
      fun bounded (raw,inc) =
        let val amount=case metric of RawNodes=>raw
              | BinderInclusiveNodes=>inc
        in case maximum of SmtReplayResourcePolicy.Uncapped=>amount
          | SmtReplayResourcePolicy.AtMost bound=>
              if amount<=bound then amount else bound+1 end
    in Option.map bounded (policy_node_metrics g node) end
  fun unfolded_nodes_with_policy g metric maximum node =
    case policy_import_int_limit maximum of
        SOME finite =>
          if finite<cap then Option.map IntInf.fromInt
            (unfolded_nodes g metric finite node)
          else exact_unfolded_nodes_with_policy g metric maximum node
      | NONE => exact_unfolded_nodes_with_policy g metric maximum node

  fun plan_placeholders_with_policy (g : graph) caller {nodes,remaining_work} =
    let
      (* Exactly the initial conversion/ref source events are admitted before
         either exists. This is not a new semantic input/output cutoff. *)
      val _ = if SmtReplayResourcePolicy.allows remaining_work 2 then () else
        raise ERR "plan_placeholders" "remaining Work cannot create meter"
      val ceiling = remaining_work
      val used = ref (2 : IntInf.int)
      fun spend amount =
        if not (SmtReplayResourcePolicy.allows ceiling (!used+amount)) orelse
            amount < 0 then
          raise ERR "plan_placeholders" "original remaining Work exhausted"
        else used := !used+amount
      fun tick () = spend 1
      val _ = tick ()
      val original_nodes = !(#nodes g)
      val _ = tick ()
      val original_scopes = !(#scopes g)
      val _ = tick ()
      val original_reserved = !(#reserved g)
      val _ = tick ()
      val original_placeholders = !(#placeholders g)
      val _ = tick ()
      val first_name = !(#next_name g)
      val _ = tick ()
      val first_node = !(#next g)
      val _ = tick ()
      val first_scope = !(#next_scope g)
      val _ = tick ()
      val epoch = Type.type_epoch ()
      val _ = tick ()
      val symbols = Term.term_epoch ()
      val _ = tick ()
      val frames = ref ([] : (scope * bool ref) list)
      val _ = tick ()
      val scope_values = ref ([] : (scope * frame) list)
      fun int_value table key =
        let val _ = tick ()
            val plan = R.lookup_int_with_policy
              (table,key,SmtReplayResourcePolicy.remaining ceiling (!used))
            val _ = spend (#work (R.int_lookup_cost plan))
            val _ = tick ()
        in R.int_lookup_value (table,plan) end
      fun previous scope pending =
        (tick ();case pending of [] => NONE
         | (old,value)::rest =>
             (tick ();if scope = old then (tick ();SOME value)
              else previous scope rest))
      fun scope_value (scope as Scope {owner,id}) =
        (tick ();
         if owner <> #owner g then
           raise ERR "plan_placeholders" "foreign caller/frame"
         else (tick ();case previous scope (!scope_values) of
           SOME value => value
         | NONE =>
             let val value = case int_value original_scopes id of
                     SOME value => value
                   | NONE => raise ERR "plan_placeholders" "unknown frame"
                 val _ = tick () val _ = tick () val _ = tick ()
                 val _ = scope_values := (scope,value) :: !scope_values
                 val _ = tick () val _ = tick () val _ = tick ()
                 val _ = frames := (scope,#active value) :: !frames
             in value end))
      fun alive scope =
        let val frame = scope_value scope val _ = tick ()
            val _ = if !(#active frame) then () else
              raise ERR "plan_placeholders" "retired frame"
        in tick ();case #parent frame of NONE => () | SOME p => alive p end
      fun visible scope required =
        (tick ();if scope = required then true else
         case #parent (scope_value scope) of NONE => false
         | SOME parent => visible parent required)
      val _ = alive caller
      val _ = tick () val staged_reserved = ref original_reserved
      val _ = tick () val next_name = ref first_name
      val _ = tick () val rows = ref ([] : placeholder_row list)
      val _ = tick () val names = ref ([] : (node * string) list)
      val _ = tick ()
      val bindings = ref ([] : (node * string * Type.hol_type) list)
      val _ = tick () val keys = ref ([] : int list)
      (* Local to this genuine policy plan and its original meter. Numeric
         IDs select buckets; only complete graph-owned nodes establish
         membership. There is no cross-plan cache or Work permission. *)
      val _ = spend 2
      val visited = ref (R.empty_int () : node list R.int_map)
      fun visited_entry node =
        let val _ = spend 3
            val table = !visited
            val key = node_id node
            val query = R.lookup_int_with_policy
              (table,key,SmtReplayResourcePolicy.remaining ceiling (!used))
            val _ = spend (#work (R.int_lookup_cost query))
            val _ = tick ()
            val values = case R.int_lookup_value (table,query) of
                NONE => [] | SOME values => values
        in (table,key,values) end
      fun visited_member node pending =
        (tick ();case pending of [] => false | old::rest =>
          (tick ();node = old orelse visited_member node rest))
      fun remember entry node =
        let val _ = spend 3
            val (table,key,values) = entry
            val insertion = R.insert_int_with_policy
              (table,key,SmtReplayResourcePolicy.remaining ceiling (!used))
            val _ = spend (#work (R.int_insertion_cost insertion))
            (* Actual bucket cons and publication of the finished map;
               R's quote already retains its one-shot finish programme. *)
            val _ = spend 2
            val next = R.finish_int (table,insertion,node::values)
        in visited := next end
      (* Decimal formatting has a fixed machine-int input. Borrowed source
         events reserve each digit/cons plus concatenation bytes BEFORE the
         primitive formatter/concatenator; internal primitive costs remain
         outside this event model. No arbitrary name-length cutoff exists. *)
      fun candidate id =
        let
          fun digits n = (tick ();if n < 10 then 1 else 1+digits (n div 10))
          val _ = if id < 0 then
            raise ERR "plan_placeholders" "negative name counter" else ()
          val _ = case Int.maxInt of NONE => () | SOME maximum =>
            if id < maximum then () else
              raise ERR "plan_placeholders" "name counter cannot advance"
          val n = digits id
          val _ = spend (IntInf.fromInt n)
          val decimal = Int.toString id
          val _ = spend (IntInf.fromInt (String.size "__smt_replay_"))
          val _ = spend (IntInf.fromInt n)
        in "__smt_replay_" ^ decimal end
      fun choose () =
        let val _ = tick () val id = !next_name
            val name = candidate id
            val _ = tick () val _ = tick () val _ = next_name := id+1
            val _ = tick () val staged = !staged_reserved
            val _ = tick ()
            val plan = R.lookup_string_with_policy
              (staged,name,
                   SmtReplayResourcePolicy.remaining ceiling (!used))
            val _ = spend (#work (R.string_lookup_cost plan))
            val _ = tick ()
        in if R.string_lookup_value (staged,plan) then choose ()
           else name end
      fun one (node as Node {owner,id}) =
        let
          val _ = tick ()
          val _ = if owner = #owner g then () else
            raise ERR "plan_placeholders" "foreign node"
          val fields = case int_value original_nodes id of SOME v => v
            | NONE => raise ERR "plan_placeholders" "unknown node"
          val _ = alive (#scope fields)
          val _ = if visible caller (#scope fields) then () else
            raise ERR "plan_placeholders" "node outside original caller"
        in case int_value original_placeholders id of
            SOME term =>
              let val _ = tick () val name = #1 (Term.dest_var term)
                  val _ = tick () val _ = tick ()
                  val _ = tick () val _ = tick ()
                  val _ = rows := CachedName (node,term) :: !rows
                  val _ = tick () val _ = tick () val _ = tick ()
                  val _ = names := (node,name) :: !names
                  (* Type read, tuple, cons, write before allocation. *)
                  val _ = spend 4
                  val _ = bindings := (node,name,#ty fields) :: !bindings
              in () end
          | NONE =>
              let
                val name = choose ()
                val _ = tick () val staged = !staged_reserved
                val _ = tick ()
                val insertion = R.insert_string_with_policy
                  (staged,name,
                   SmtReplayResourcePolicy.remaining ceiling (!used))
                val _ = spend (#work (R.string_insertion_cost insertion))
                val _ = tick ()
                val next = R.finish_string (staged,insertion)
                val _ = tick () val _ = staged_reserved := next
                val _ = tick () val _ = tick ()
                val _ = tick () val _ = tick ()
                val _ = rows := NewName (node,name,#ty fields) :: !rows
                val _ = tick () val _ = tick () val _ = tick ()
                val _ = names := (node,name) :: !names
                val _ = spend 4
                val _ = bindings := (node,name,#ty fields) :: !bindings
                val _ = tick () val _ = tick () val _ = keys := id :: !keys
              in () end
        end
      fun walk pending =
        (tick ();case pending of [] => () | node::rest =>
          let val entry = visited_entry node
              val _ = spend 3
              val (_,_,values) = entry
          in if visited_member node values then
               raise ERR "plan_placeholders" "duplicate naming node"
             else (one node;remember entry node;tick ();walk rest)
          end)
      val _ = walk nodes
      (* Actual private row grammar, including cached skip and empty tail.
         One event precedes each planning inspection; separate events retain
         the future branch, variable constructor and output-list cons. *)
      fun reserve_payloads pending =
        (tick ();tick ();case pending of [] => spend 4
         | CachedName _::rest =>
             (spend 5;reserve_payloads rest)
         | NewName _::rest =>
             (spend 8;reserve_payloads rest))
      val _ = reserve_payloads (!rows)
      (* Exact output reversal: tail visit, cons and branch for each row. *)
      fun reserve_reverse [] = tick ()
        | reserve_reverse (_::rest) = (spend 4;reserve_reverse rest)
      val _ = reserve_reverse (!rows)
      val batch = R.insert_int_batch_with_policy
        (original_placeholders,!keys,
         SmtReplayResourcePolicy.remaining ceiling (!used))
      val _ = spend (#work (R.int_batch_cost batch))
      (* The two immutable snapshot constructors and the phase reference
         are charged BEFORE construction. Both positive guard invocations
         share placeholder_guard; failure retirement is separately reserved. *)
      val _ = tick () val _ = tick () val _ = tick ()
      val snapshot = PlaceholderSnapshot
        {owner = #owner g,caller = caller,nodes = original_nodes,
         scopes = original_scopes,reserved = original_reserved,
         placeholders = original_placeholders,first_name = first_name,
         first_node = first_node,first_scope = first_scope,
         epoch = epoch,symbols = symbols,frames = !frames,
         next_reserved = !staged_reserved,
         next_name = !next_name}
      val phase = ref NamesPrepared
      val _ = tick () val _ = tick ()
      val meter = PolicyCountGuard {ceiling = ceiling,used = used}
      val before_guard = !used
      val _ = placeholder_guard EitherState meter g caller snapshot phase
      val positive_guard = !used-before_guard
      (* Mint's same prepared guard plus a possible refusal-retirement write.
         Future independent validation pays guard_work from SAME W. *)
      val guard_work = positive_guard+1
      val _ = spend guard_work
      (* Future phase retirement, three graph writes, minted wrapper/write;
         final immutable plan record and wrapper. No future source search. *)
      val _ = tick () val _ = tick () val _ = tick () val _ = tick ()
      val _ = tick () val _ = tick () val _ = tick () val _ = tick ()
      (* Additional retained field and its read. *)
      val _ = spend 2
    in PlaceholderPlan
      {snapshot = snapshot,rows = !rows,names = !names,
       bindings = !bindings,batch = batch,
       work = !used,guard_work = guard_work,phase = phase,
       revision = #validation_changes g} end

  (* SAME-meter counterpart of the genuine placeholder programme. The
     ordinary planners above retain their exact standalone accounting and
     diagnostics. Only this route uses already-paid R plans; their costs
     must NOT be charged a second time. All partial debits survive refusal.
     Meter snapshots report cost DATA, never create a new allowance. *)
  fun plan_placeholders_with_meter (g : graph) caller meter {nodes} =
    let
      val initial = R.scope_meter_charged_policy meter
      val _ = R.scope_meter_charge meter 2 handle R.Limit =>
        raise ERR "plan_placeholders" "remaining Work cannot create meter"
      fun spend amount = R.scope_meter_charge meter amount handle R.Limit =>
        raise ERR "plan_placeholders" "original remaining Work exhausted"
      fun tick () = spend 1
      val _ = tick ()
      val original_nodes = !(#nodes g)
      val _ = tick ()
      val original_scopes = !(#scopes g)
      val _ = tick ()
      val original_reserved = !(#reserved g)
      val _ = tick ()
      val original_placeholders = !(#placeholders g)
      val _ = tick ()
      val first_name = !(#next_name g)
      val _ = tick ()
      val first_node = !(#next g)
      val _ = tick ()
      val first_scope = !(#next_scope g)
      val _ = tick ()
      val epoch = Type.type_epoch ()
      val _ = tick ()
      val symbols = Term.term_epoch ()
      val _ = tick ()
      val frames = ref ([] : (scope * bool ref) list)
      val _ = tick ()
      val scope_values = ref ([] : (scope * frame) list)
      fun int_value table key =
        let val _ = tick ()
            val plan = R.scope_plan_lookup_int meter (table,key)
            val _ = tick ()
        in R.int_lookup_value (table,plan) end
      fun previous scope pending =
        (tick ();case pending of [] => NONE
         | (old,value)::rest =>
             (tick ();if scope = old then (tick ();SOME value)
              else previous scope rest))
      fun scope_value (scope as Scope {owner,id}) =
        (tick ();
         if owner <> #owner g then
           raise ERR "plan_placeholders" "foreign caller/frame"
         else (tick ();case previous scope (!scope_values) of
           SOME value => value
         | NONE =>
             let val value = case int_value original_scopes id of
                     SOME value => value
                   | NONE => raise ERR "plan_placeholders" "unknown frame"
                 val _ = tick () val _ = tick () val _ = tick ()
                 val _ = scope_values := (scope,value) :: !scope_values
                 val _ = tick () val _ = tick () val _ = tick ()
                 val _ = frames := (scope,#active value) :: !frames
             in value end))
      fun alive scope =
        let val frame = scope_value scope val _ = tick ()
            val _ = if !(#active frame) then () else
              raise ERR "plan_placeholders" "retired frame"
        in tick ();case #parent frame of NONE => () | SOME p => alive p end
      fun visible scope required =
        (tick ();if scope = required then true else
         case #parent (scope_value scope) of NONE => false
         | SOME parent => visible parent required)
      val _ = alive caller
      val _ = tick () val staged_reserved = ref original_reserved
      val _ = tick () val next_name = ref first_name
      val _ = tick () val rows = ref ([] : placeholder_row list)
      val _ = tick () val names = ref ([] : (node * string) list)
      val _ = tick ()
      val bindings = ref ([] : (node * string * Type.hol_type) list)
      val _ = tick () val keys = ref ([] : int list)
      val _ = spend 2
      val visited = ref (R.empty_int () : node list R.int_map)
      fun visited_entry node =
        let val _ = spend 3
            val table = !visited
            val key = node_id node
            val query = R.scope_plan_lookup_int meter (table,key)
            val _ = tick ()
            val values = case R.int_lookup_value (table,query) of
                NONE => [] | SOME values => values
        in (table,key,values) end
      fun visited_member node pending =
        (tick ();case pending of [] => false | old::rest =>
          (tick ();node = old orelse visited_member node rest))
      fun remember entry node =
        let val _ = spend 3
            val (table,key,values) = entry
            val insertion = R.scope_plan_insert_int meter (table,key)
            val _ = spend 2
            val next = R.finish_int (table,insertion,node::values)
        in visited := next end
      fun candidate id =
        let
          fun digits n = (tick ();if n < 10 then 1 else 1+digits (n div 10))
          val _ = if id < 0 then
            raise ERR "plan_placeholders" "negative name counter" else ()
          val _ = case Int.maxInt of NONE => () | SOME maximum =>
            if id < maximum then () else
              raise ERR "plan_placeholders" "name counter cannot advance"
          val n = digits id
          val _ = spend (IntInf.fromInt n)
          val decimal = Int.toString id
          val _ = spend (IntInf.fromInt (String.size "__smt_replay_"))
          val _ = spend (IntInf.fromInt n)
        in "__smt_replay_" ^ decimal end
      fun choose () =
        let val _ = tick () val id = !next_name
            val name = candidate id
            val _ = tick () val _ = tick () val _ = next_name := id+1
            val _ = tick () val staged = !staged_reserved
            val _ = tick ()
            val plan = R.scope_plan_lookup_string meter (staged,name)
            val _ = tick ()
        in if R.string_lookup_value (staged,plan) then choose ()
           else name end
      fun one (node as Node {owner,id}) =
        let
          val _ = tick ()
          val _ = if owner = #owner g then () else
            raise ERR "plan_placeholders" "foreign node"
          val fields = case int_value original_nodes id of SOME v => v
            | NONE => raise ERR "plan_placeholders" "unknown node"
          val _ = alive (#scope fields)
          val _ = if visible caller (#scope fields) then () else
            raise ERR "plan_placeholders" "node outside original caller"
        in case int_value original_placeholders id of
            SOME term =>
              let val _ = tick () val name = #1 (Term.dest_var term)
                  val _ = tick () val _ = tick ()
                  val _ = tick () val _ = tick ()
                  val _ = rows := CachedName (node,term) :: !rows
                  val _ = tick () val _ = tick () val _ = tick ()
                  val _ = names := (node,name) :: !names
                  val _ = spend 4
                  val _ = bindings := (node,name,#ty fields) :: !bindings
              in () end
          | NONE =>
              let
                val name = choose ()
                val _ = tick () val staged = !staged_reserved
                val _ = tick ()
                val insertion = R.scope_plan_insert_string meter
                  (staged,name)
                val _ = tick ()
                val next = R.finish_string (staged,insertion)
                val _ = tick () val _ = staged_reserved := next
                val _ = tick () val _ = tick ()
                val _ = tick () val _ = tick ()
                val _ = rows := NewName (node,name,#ty fields) :: !rows
                val _ = tick () val _ = tick () val _ = tick ()
                val _ = names := (node,name) :: !names
                val _ = spend 4
                val _ = bindings := (node,name,#ty fields) :: !bindings
                val _ = tick () val _ = tick () val _ = keys := id :: !keys
              in () end
        end
      fun walk pending =
        (tick ();case pending of [] => () | node::rest =>
          let val entry = visited_entry node
              val _ = spend 3
              val (_,_,values) = entry
          in if visited_member node values then
               raise ERR "plan_placeholders" "duplicate naming node"
             else (one node;remember entry node;tick ();walk rest)
          end)
      val _ = walk nodes
      fun reserve_payloads pending =
        (tick ();tick ();case pending of [] => spend 4
         | CachedName _::rest =>
             (spend 5;reserve_payloads rest)
         | NewName _::rest =>
             (spend 8;reserve_payloads rest))
      val _ = reserve_payloads (!rows)
      fun reserve_reverse [] = tick ()
        | reserve_reverse (_::rest) = (spend 4;reserve_reverse rest)
      val _ = reserve_reverse (!rows)
      val batch = R.scope_plan_insert_int_batch meter
        (original_placeholders,!keys)
      val _ = tick () val _ = tick () val _ = tick ()
      val snapshot = PlaceholderSnapshot
        {owner = #owner g,caller = caller,nodes = original_nodes,
         scopes = original_scopes,reserved = original_reserved,
         placeholders = original_placeholders,first_name = first_name,
         first_node = first_node,first_scope = first_scope,
         epoch = epoch,symbols = symbols,frames = !frames,
         next_reserved = !staged_reserved,
         next_name = !next_name}
      val phase = ref NamesPrepared
      val _ = tick () val _ = tick ()
      val guard_meter = SameMeterGuard meter
      val before_guard = R.scope_meter_charged_policy meter
      val _ = placeholder_guard EitherState guard_meter g caller
        snapshot phase
      val positive_guard = R.scope_meter_charged_policy meter-before_guard
      val guard_work = positive_guard+1
      val _ = spend guard_work
      val _ = tick () val _ = tick () val _ = tick () val _ = tick ()
      val _ = tick () val _ = tick () val _ = tick () val _ = tick ()
      val _ = spend 2
    in PlaceholderPlan
      {snapshot = snapshot,rows = !rows,names = !names,
       bindings = !bindings,batch = batch,
       work = R.scope_meter_charged_policy meter-initial,
       guard_work = guard_work,phase = phase,
       revision = #validation_changes g} end

  (* Only authentic policy discovery profiles can fill an opaque leaf.
     The private selection closure never accepts a caller scalar/guard. *)
  fun policy_identity_profiles (g:graph) caller available =
    let
      val chosen=ref (Redblackmap.mkDict Int.compare :
        (int,policy_opaque_profile) Redblackmap.dict)
      fun select node=
        case Redblackmap.peek (!chosen,node_id node) of
          SOME profile=>opaque_profile_data_with_policy g caller profile
        | NONE=>
            let
              fun seek []=raise ERR "identity_view"
                    "opaque syntax has no complete policy closure recipe"
                | seek ((profile as PolicyOpaqueProfile {owner,...})::rest)=
                    if owner<> #owner g then
                      raise ERR "identity_view" "foreign policy profile"
                    else let val PolicyOpaqueProfile {node=held,...}=profile
                      in if node=held then
                        let val data=opaque_profile_data_with_policy
                              g caller profile
                            val PolicyOpaqueProfile {ready,...}=profile
                            val _=if ready () then () else
                              raise ERR "identity_view"
                                "incomplete policy closure recipe"
                        in chosen := Redblackmap.insert
                            (!chosen,node_id node,profile);data end
                      else seek rest end
            in seek available end
      fun guard ()=Redblackmap.app
        (fn (_,profile)=>ignore
          (opaque_profile_data_with_policy g caller profile)) (!chosen)
    in (select,guard) end
  fun policy_identity_metrics g select root =
    let
      val memo=ref (Redblackmap.mkDict Int.compare)
      val pending=ref (Redblackset.empty Int.compare)
      fun save current result =
        (memo := Redblackmap.insert (!memo,node_id current,result);
         pending := Redblackset.delete (!pending,node_id current))
      fun get current=case Redblackmap.peek (!memo,node_id current) of
          SOME value=>value
        | NONE=>raise ERR "policy_node_metrics" "unfinished actual child"
      fun add children (raw:IntInf.int) (inc:IntInf.int) =
        case children of []=>SOME(raw,inc)
        | child::rest=>case get child of NONE=>NONE
          | SOME(r,i)=>add rest (raw+r) (inc+i)
      fun loop []=get root
        | loop (PolicyMetricVisit current::rest)=
          (case Redblackmap.peek (!memo,node_id current) of
            SOME _=>loop rest
          | NONE=>
            let
              val fields=entry g current
              val key=node_id current
              val _=if Redblackset.member (!pending,key) then
                  raise ERR "policy_node_metrics" "cyclic actual graph"
                else pending := Redblackset.add (!pending,key)
              fun children own nodes = loop
                (List.map PolicyMetricVisit nodes @
                 PolicyMetricJoin(current,own,nodes)::rest)
            in case #view fields of
                Variable _ => (save current (SOME(1,1));loop rest)
              | Constant _ => (save current (SOME(1,1));loop rest)
              | OpaqueRetained =>
                  let val (raw,inc)=select current
                  in save current (SOME(raw,inc));loop rest end
              | Application(left,right)=>children 1 [left,right]
              | AdmittedBinder {body,...}=>children 2 [body]
            end)
        | loop (PolicyMetricJoin(current,own,children)::rest)=
            let val result=add children (1:IntInf.int) (IntInf.fromInt own)
                val _=save current result
            in loop rest end
    in loop [PolicyMetricVisit root] end
  fun plan_identity_closure_view_with_policy (g : graph) caller maximum
      {target,retain,profiles=available} =
    let
      val epoch = Type.type_epoch ()
      val node = closure_child_node g caller target
      val _ = if SmtReplayResourcePolicy.positive maximum then () else
        raise ERR "identity_view" "nonpositive original metadata contract"
      val held = ref ([] : closure_child list)
      val (select_profile,profile_guard)=
        policy_identity_profiles g caller available
      val visited = ref (Redblackset.empty Int.compare)
      val remaining = ref maximum
      fun visit child =
        let val current = closure_child_node g caller child
            val _ = if SmtReplayResourcePolicy.allows (!remaining) 1 then
              remaining := SmtReplayResourcePolicy.remaining (!remaining) 1
            else
              raise ERR "identity_view" "closure portfolio exceeds contract"
            val _ = held := child :: !held
        in if Redblackset.member (!visited,node_id current) then () else
          (visited := Redblackset.add (!visited,node_id current);
           case view g current of
             Application _ =>
               let val (a,b) = closure_application_children g caller child
               in visit a;visit b end
           | AdmittedBinder _ => visit (binder_closure_body g caller
               (closure_child_binder g caller child))
           | OpaqueRetained => ignore (select_profile current)
           | _ => ()) end
      fun opaque_metric current=
        let val data=select_profile current in (#raw data,#inc data) end
      val (raw,inc)=case policy_identity_metrics g opaque_metric node of
          SOME pair=>pair
        | NONE=>raise ERR "identity_view" "unknown cached target syntax"
      val _=if SmtReplayResourcePolicy.allows maximum raw andalso
          SmtReplayResourcePolicy.allows maximum inc then () else
        raise ERR "identity_view" "cached target exceeds contract"
      val roots = target::retain
      val _ = List.app visit roots
      val term = representative g node
      val snapshot = identity_rows g caller node
      fun guard () =
        (check_scope g caller;
         if Type.type_epoch () = epoch then () else
           raise ERR "identity_view" "Type retirement epoch changed";
         List.app (fn child =>
           ignore (closure_child_node g caller child)) (!held);
         profile_guard ();
         if Portable.pointer_eq (term,representative g node) then () else
           raise ERR "identity_view" "canonical target term changed")
      val _ = guard ()
    in IdentityViewPlan {graph = g,caller = caller,node = node,term = term,
      roots = roots,guard = guard,snapshot = snapshot,used = ref false} end

  (* Exact DATA rooted in owned immutable graph constructors and genuine
     retained profiles. No semantic limit, Work credit or freshness lease. *)
  datatype profiled_metric = ProfiledMetric of
    {owner:unit ref,scope:scope,node:node,term:Term.term,
     raw:IntInf.int,inc:IntInf.int,types:Type.hol_type list,
     epoch:int,symbols:int,guard:unit->unit}
  fun prepare_profiled_metric (g:graph) caller {node,profiles} =
    let
      val _=check_scope g caller
      val _=usable g caller node
      val epoch=Type.type_epoch () val symbols=Term.term_epoch ()
      val term=representative g node
      val (select,profile_guard)=policy_identity_profiles g caller profiles
      val type_vectors=ref ([]:Type.hol_type list list)
      fun opaque current=
        let val data=select current
            val _=type_vectors := #types data :: !type_vectors
        in (#raw data,#inc data) end
      val (raw,inc)=case policy_identity_metrics g opaque node of
          SOME counts=>counts
        | NONE=>raise ERR "profiled_metric" "unknown actual syntax"
      fun guard ()=
        (check_scope g caller;usable g caller node;
         if Type.type_epoch ()=epoch andalso Term.term_epoch ()=symbols
           then () else raise ERR "profiled_metric" "retirement epoch changed";
         if Portable.pointer_eq (term,representative g node) then () else
           raise ERR "profiled_metric" "actual root term changed";
         profile_guard ())
      val _=guard ()
      val types=List.concat (List.rev (!type_vectors))
    in ProfiledMetric {owner= #owner g,scope=caller,node=node,term=term,
      raw=raw,inc=inc,types=types,
      epoch=epoch,symbols=symbols,guard=guard} end
  fun profiled_metric_data (g:graph) caller
      (saved as ProfiledMetric {owner,...}) =
    if owner= #owner g then
      let val ProfiledMetric {scope,...}=saved
          val _=if caller=scope then () else
            raise ERR "profiled_metric" "different actual caller"
          val ProfiledMetric {node,raw,inc,types,guard,...}=saved
          val _=guard ()
      in {node=node,raw=raw,inc=inc,types=types} end
    else raise ERR "profiled_metric" "different graph owner"

  (* The original caller authenticates the complete genuine child chain.
     The effective frame is the existing checked result, never a new root. *)
  fun closure_child_scope g caller child =
    #1 (checked_closure_child g caller child)

  (* This checks retained profile liveness at its actual producer frame.
     It grants no permission to use that profile from another requester. *)
  fun validate_policy_opaque_profile (g:graph)
      (profile as PolicyOpaqueProfile {owner,...}) =
    if owner= #owner g then
      let val PolicyOpaqueProfile {scope,...}=profile
      in ignore (opaque_profile_data_with_policy g scope profile) end
    else raise ERR "validate_policy_profile" "foreign graph profile"

  (* Header comparison does not turn a different profile into a matching
     operand. A matching token still checks the actual caller visibility. *)
  fun opaque_profile_for_node_with_policy (g:graph) caller node
      (profile as PolicyOpaqueProfile {owner,...}) =
    if owner= #owner g then
      let val _=check_scope g caller
          val _=usable g caller node
          val PolicyOpaqueProfile {node=held,...}=profile
      in if node=held then
          SOME (opaque_profile_data_with_policy g caller profile)
        else NONE end
    else raise ERR "opaque_profile_for_node" "foreign graph profile"

  (* This native constructor requires a separate actual finite caller gate.
     Metadata maximum and genuine metric profiles never supply that gate. *)
  fun recorded_abstraction_with_profile_policy (g:graph) scope
      {maximum,native_limit,type_work_limit,binder,body,body_frame,
       profiles,step} =
    let
      val _=check_scope g scope
      val binder_fields=entry g binder
      val _=check_scope g body_frame
      val _=if native_limit>0 andalso type_work_limit>0 andalso
          SmtReplayResourcePolicy.positive maximum then () else
        raise ERR "profiled_abstraction" "nonpositive native caller gate"
      val ceiling=IntInf.fromInt type_work_limit
      val used=ref (0:IntInf.int)
      val epoch=Type.type_epoch () val symbols=Term.term_epoch ()
      val held=ref ([]:(scope*binder_closure) list)
      val chosen=ref ([]:(node*scope*policy_opaque_profile) list)
      fun guard ()=
        (check_scope g scope;check_scope g body_frame;
         ignore(entry g binder);ignore(entry g body);
         if Type.type_epoch ()=epoch andalso Term.term_epoch ()=symbols
           then () else raise ERR "profiled_abstraction"
             "native epoch changed";
         List.app (validate_policy_opaque_profile g) profiles;
         List.app (fn(caller,closure)=>ignore
           (binder_closure_data g caller closure)) (!held);
         List.app (fn(n,caller,p)=>case
             opaque_profile_for_node_with_policy g caller n p of
               SOME _=>() | NONE=>raise ERR "profiled_abstraction"
                 "selected actual profile changed") (!chosen))
      fun tick ()=
        (guard();if !used<ceiling then used:= !used+1 else
           raise ERR "profiled_abstraction" "native Type/model gate exhausted";
         step();guard())
      fun invoke action=(tick();let val value=action() in guard();value end)
      fun same ((a,s),(b,t))=a=b andalso s=t
      fun lookup _ []=NONE
        | lookup key ((old,value)::rest)=
            (tick();if same(key,old) then SOME value else lookup key rest)
      fun plus (a:IntInf.int) b=
        if a>=0 andalso b>=0 andalso a+b<=ceiling then a+b else
          raise ERR "profiled_abstraction"
            "native repeated Type gate exhausted"
      val type_memo=ref ([]:(Type.hol_type*IntInf.int) list)
      fun type_find _ []=NONE
        | type_find ty ((old,n)::rest)=
            (tick();if Portable.pointer_eq(ty,old) then SOME n
             else type_find ty rest)
      fun weight ty=case type_find ty (!type_memo) of SOME n=>n
        | NONE=>
            let val _=tick()
                val n=if invoke(fn()=>Type.is_vartype ty) then 1 else
                  List.foldl (fn(child,total)=>plus total (weight child)) 1
                    (invoke(fn()=> #2(Type.dest_type ty)))
                val _=if invoke(fn()=>Type.uptodate_type ty) then () else
                  raise ERR "profiled_abstraction" "retired annotation"
                val _=type_memo:=(ty,n):: !type_memo
            in n end
      fun select caller n=
        let fun find []=raise ERR "profiled_abstraction"
                  "opaque body lacks genuine policy profile"
              | find(p::rest)=
                  (tick();case opaque_profile_for_node_with_policy g caller n p
                    of NONE=>find rest | SOME data=>
                      (chosen:=(n,caller,p):: !chosen;data))
        in find profiles end
      type metric={raw:IntInf.int,inc:IntInf.int,ann:IntInf.int,ty:IntInf.int}
      val metrics=ref ([]:((node*scope)*metric) list)
      fun measure caller n=
        let val _=tick() val _=usable g caller n
        in case lookup(n,caller)(!metrics) of SOME value=>value | NONE=>
          let val fields=entry g n val ty=weight(#ty fields)
              val value:metric=case #view fields of
                  OpaqueRetained=>
                    let val data=select caller n
                        val _=if #ty data=ty then () else
                          raise ERR "profiled_abstraction"
                            "profile Type differs"
                    in {raw= #raw data,inc= #inc data,ann= #ann data,ty=ty} end
                | Application(f,x)=>
                    let val a=measure caller f val b=measure caller x
                    in {raw=1+ #raw a+ #raw b,inc=1+ #inc a+ #inc b,
                        ann=plus ty (plus(#ann a)(#ann b)),ty=ty} end
                | AdmittedBinder _=>
                    let val closure=binder_closure g caller n
                        val d=binder_closure_data g caller closure
                        val _=held:=(caller,closure):: !held
                        val a=measure (#body_frame d) (#body d)
                        val bt=weight(type_of g (#binder d))
                    in {raw=1+ #raw a,inc=2+ #inc a,
                        ann=plus ty (plus bt (#ann a)),ty=ty} end
                | _=>{raw=1,inc=1,ann=ty,ty=ty}
              val _=metrics:=((n,caller),value):: !metrics
          in value end
        end
      val _=guard()
      val _=if scope_visible g (#scope binder_fields) scope then () else
        raise ERR "profiled_abstraction" "binder outside enclosing scope"
      val _=case #view binder_fields of Variable(Bound,_)=>() | _=>
        raise ERR "profiled_abstraction" "binder is not scoped bound variable"
      val _=check_scope g (#scope binder_fields)
      val _=if scope_visible g body_frame (#scope binder_fields) then () else
        raise ERR "profiled_abstraction" "body frame outside binder frame"
      val _=usable g body_frame binder val _=usable g body_frame body
      val body_fields=entry g body
      val actual=measure body_frame body
      val raw= #raw actual+1 val inc= #inc actual+2
      val bt=weight(#ty binder_fields)
      val outer=plus 1 (plus bt (#ty actual))
      val ann=plus outer (plus bt (#ann actual))
      (* Whole realized input/output and repeated Type admission precede
         EVERY native FV call. The actual native input term is unchanged. *)
      val _=if raw<=IntInf.fromInt native_limit andalso
          inc<=IntInf.fromInt native_limit andalso ann<=ceiling andalso
          SmtReplayResourcePolicy.allows maximum raw andalso
          SmtReplayResourcePolicy.allows maximum inc then () else
        raise ERR "profiled_abstraction" "native or metadata binder geometry"
      val variables=ref ([]:((node*scope)*node list) list)
      fun insert n []=[n]
        | insert n (old::rest)=
            (tick();if n=old then old::rest else old::insert n rest)
      fun union left right=List.foldl(fn(n,out)=>insert n out) right left
      fun remove n []=[]
        | remove n (old::rest)=
            (tick();if n=old then remove n rest else old::remove n rest)
      fun free caller n=
        let val _=tick() val _=usable g caller n
        in case lookup(n,caller)(!variables) of SOME out=>out | NONE=>
          let val fields=entry g n
              val out=case #view fields of
                  Variable _=>[n] | Constant _=>[]
                | Application(f,x)=>union(free caller f)(free caller x)
                | AdmittedBinder _=>
                    let val closure=binder_closure g caller n
                        val d=binder_closure_data g caller closure
                        val _=held:=(caller,closure):: !held
                    in remove (#binder d) (free (#body_frame d) (#body d)) end
                | OpaqueRetained=>
                    let val _=ignore(select caller n)
                        val terms=invoke(fn()=>Term.free_vars (#term fields))
                        fun resolve(term,out)=
                          let val _=tick()
                              val _=if invoke(fn()=>Term.is_var term) then ()
                                else raise ERR "profiled_abstraction"
                                  "native FV result is not a variable"
                              val _=ignore(weight(invoke(fn()=>Term.type_of
                                term)))
                              (* Resolve at the OPAQUE NODE'S original frame,
                                 never the new binder/body requester. A rigid
                                 same-name leaf must not become that binder. *)
                              val variable=invoke(fn()=>resolve_variable g
                                (#scope fields) term)
                          in insert variable out end
                    in List.foldl resolve [] terms end
              val _=variables:=((n,caller),out):: !variables
          in out end
        end
      val free_nodes=free body_frame body
      val binder_name= #1(Term.dest_var(#term binder_fields))
      val _=List.app (fn n=>
        (tick();if n=binder then () else usable g scope n;
         if n<>binder andalso type_id g n= #type_id binder_fields andalso
             #1(Term.dest_var(representative g n))=binder_name then
           raise ERR "profiled_abstraction"
             "binder captures another graph variable"
         else ())) free_nodes
      val term=invoke(fn()=>Term.mk_abs(#term binder_fields,#term body_fields))
      val ty=invoke(fn()=>Type.mk_type("fun",[#ty binder_fields,#ty
        body_fields]))
      val _=guard()
      val node=fresh g
        {scope=scope,ty=ty,type_id=intern_type g ty,term=term,
         view=AdmittedBinder{binder=binder,body=body,frame= #scope
           binder_fields},
         raw=policy_metric_int raw,inclusive=policy_metric_int inc,
         source=ref NONE}
      val creation:binder_closure_creation=
        {identity=ref(),node=node,declaring_scope=scope,binder=binder,
         binder_term=representative g binder,binder_frame= #scope
           binder_fields,
         body=body,body_frame=body_frame}
      val record=ClosureRecord{identity=ref(),owner= #owner g,node=node,
        node_frame=scope,creation=creation,backing=NONE}
      val next=Redblackmap.insert(!(#binder_closures g),node_id node,record)
      val _=validation_change g val _= #binder_closures g:=next
      val _=guard()
    in node end

  (* Companion, UNSELECTED. The effective requester comes only from the
     actual checked binder creation; a profile issuer cannot choose it. *)
  fun prepare_scoped_profiled_metric_program observe (g:graph) caller
      {node,profiles} =
    let
      val _=observe ()
      val _=check_scope g caller val _=usable g caller node
      val epoch=Type.type_epoch () val symbols=Term.term_epoch ()
      val term=representative g node
      val held=ref ([]:(scope*binder_closure) list)
      val chosen=ref ([]:(node*scope*policy_opaque_profile) list)
      val vectors=ref ([]:Type.hol_type list list)
      fun compare pair=(observe ();Int.compare pair)
      val memo=ref (Redblackmap.mkDict
        (pair_compare compare compare):
        (int*int,IntInf.int*IntInf.int) Redblackmap.dict)
      fun opaque frame current=
        let fun seek []=(observe ();raise ERR "scoped_profiled_metric"
                  "opaque syntax lacks genuine scoped profile")
              | seek(p::rest)=(observe ();case
                  opaque_profile_for_node_with_policy g frame current p of
                    NONE=>seek rest | SOME data=>
                      (observe ();chosen:=(current,frame,p):: !chosen;
                       observe ();vectors:= #types data:: !vectors;
                       (#raw data,#inc data)))
        in seek profiles end
      fun visit frame current=
        let val _=observe ()
            val _=usable g frame current
            val key=(scope_id frame,node_id current)
            val _=observe ()
        in case Redblackmap.peek(!memo,key) of SOME result=>result | NONE=>
          let val _=observe ()
              val value=case view g current of
                  Variable _=>(1,1) | Constant _=>(1,1)
                | OpaqueRetained=>opaque frame current
                | Application(f,x)=>
                    let val(a,b)=visit frame f val(c,d)=visit frame x
                    in (1+a+c,1+b+d) end
                | AdmittedBinder _=>
                    let val _=observe ()
                        val closure=binder_closure g frame current
                        val _=observe ()
                        val data=binder_closure_data g frame closure
                        val _=observe ()
                        val _=held:=(frame,closure):: !held
                        val(a,b)=visit (#body_frame data) (#body data)
                    in (1+a,2+b) end
              val _=observe ()
              val _=memo:=Redblackmap.insert(!memo,key,value)
          in value end
        end
      val(raw,inc)=visit caller node
      fun guard ()=
        (observe ();check_scope g caller;usable g caller node;
         observe ();
         if Type.type_epoch ()=epoch andalso Term.term_epoch ()=symbols
           then () else raise ERR "scoped_profiled_metric" "retirement epoch";
         observe ();
         if Portable.pointer_eq(term,representative g node) then () else
           raise ERR "scoped_profiled_metric" "actual root changed";
         List.app(fn(frame,closure)=>(observe ();ignore
           (binder_closure_data g frame closure)))(!held);
         List.app(fn(current,frame,p)=>(observe ();case
             opaque_profile_for_node_with_policy g frame current p of
               SOME _=>() | NONE=>raise ERR "scoped_profiled_metric"
                 "actual profile changed"))(!chosen))
      val _=guard()
      (* Same memoized annotation-root vector meaning as the old API.
         Repeated effective-frame acquisitions are retained in first order;
         these roots are not a flattened Type traversal or a fee invoice. *)
      fun reverse [] answer=(observe ();answer)
        | reverse (items::rest) answer=
            (observe ();reverse rest (items::answer))
      fun append [] rest=(observe ();rest)
        | append (ty::more) rest=(observe ();ty::append more rest)
      fun flatten []=(observe ();[])
        | flatten (items::rest)=(observe ();append items (flatten rest))
      val types=flatten(reverse (!vectors) [])
    in ProfiledMetric{owner= #owner g,scope=caller,node=node,term=term,
      raw=raw,inc=inc,types=types,epoch=epoch,symbols=symbols,guard=guard} end

  fun prepare_scoped_profiled_metric graph caller request =
    prepare_scoped_profiled_metric_program (fn () => ()) graph caller request
  (* The same observer is retained by the metric's lifetime guard. An owned
     caller must therefore keep observation valid on every later getter. *)
  fun prepare_scoped_profiled_metric_observed graph caller
      {node,profiles,observe} =
    prepare_scoped_profiled_metric_program observe graph caller
      {node=node,profiles=profiles}

  (* Borrowed actual constant leaves from the SAME completed policy profile
     walk. Reverse first-visit order is DATA; it confers no native opening,
     matching, name freshness, or alternative requester Scope permission. *)
  fun opaque_profile_heads_with_policy g caller profile=
    let val _=ignore(opaque_profile_data_with_policy g caller profile)
        val PolicyOpaqueProfile{node,heads,...}=profile
    in {node=node,heads=heads}end
  (* The checked child chain supplies each effective requester. No profile
     issuer is substituted for that requester, including on a memo hit. *)
  fun plan_scoped_identity_closure_view_with_policy (g:graph) caller maximum
      {target,retain,profiles} =
    let
      val _=check_scope g caller
      val (effective,node)=checked_closure_child g caller target
      (* The published source view belongs to caller. A body-only target
         needs its actual body caller, not an unusable ancestor cache row. *)
      val _=usable g caller node
      val _=if SmtReplayResourcePolicy.positive maximum then () else
        raise ERR "scoped_identity_view" "nonpositive metadata contract"
      val epoch=Type.type_epoch() val symbols=Term.term_epoch()
      val term=representative g node
      val metric=prepare_scoped_profiled_metric g effective
        {node=node,profiles=profiles}
      val data=profiled_metric_data g effective metric
      val _=if SmtReplayResourcePolicy.allows maximum (#raw data) andalso
          SmtReplayResourcePolicy.allows maximum (#inc data) then () else
        raise ERR "scoped_identity_view" "cached target exceeds contract"
      val held=ref ([]:closure_child list)
      val chosen=ref ([]:(node*scope*policy_opaque_profile) list)
      val seen=ref (Redblackset.empty
        (pair_compare Int.compare Int.compare))
      val remaining=ref maximum
      fun select frame current=
        let fun seek []=raise ERR "scoped_identity_view"
                  "opaque syntax lacks genuine scoped profile"
              | seek(p::rest)=case
                  opaque_profile_for_node_with_policy g frame current p of
                    NONE=>seek rest
                  | SOME _=>chosen:=(current,frame,p):: !chosen
        in seek profiles end
      fun visit child=
        let val (frame,current)=checked_closure_child g caller child
            val _=if SmtReplayResourcePolicy.allows (!remaining) 1 then
                remaining:=SmtReplayResourcePolicy.remaining (!remaining) 1
              else raise ERR "scoped_identity_view"
                "closure portfolio exceeds contract"
            val _=held:=child:: !held
            val key=(scope_id frame,node_id current)
        in if Redblackset.member(!seen,key) then () else
          (seen:=Redblackset.add(!seen,key);
           case view g current of
             Application _=>
               let val(a,b)=closure_application_children g caller child
               in visit a;visit b end
           | AdmittedBinder _=>visit(binder_closure_body g caller
               (closure_child_binder g caller child))
           | OpaqueRetained=>select frame current
           | _=>())
        end
      val roots=target::retain
      val _=List.app visit roots
      val snapshot=identity_rows g caller node
      fun guard ()=
        (check_scope g caller;
         if Type.type_epoch()=epoch andalso Term.term_epoch()=symbols
           then () else raise ERR "scoped_identity_view" "retirement epoch";
         List.app(fn child=>ignore
           (checked_closure_child g caller child))(!held);
         ignore(profiled_metric_data g effective metric);
         List.app(fn(current,frame,p)=>case
             opaque_profile_for_node_with_policy g frame current p of
               SOME _=>() | NONE=>raise ERR "scoped_identity_view"
                 "actual profile changed")(!chosen);
         if Portable.pointer_eq(term,representative g node) then () else
           raise ERR "scoped_identity_view" "canonical target changed")
      val _=guard()
    in IdentityViewPlan{graph=g,caller=caller,node=node,term=term,
      roots=roots,guard=guard,snapshot=snapshot,used=ref false} end

  (* Actual selected programme, with the old declaration-only predicates
     and recipe/recognition memo. No finite API is changed. Metadata RP
     limits do not authorize native opening: consumers must independently
     admit the actual native programme before a positive call. *)
  datatype policy_selected_partial_discovery = PolicySelectedPartialDiscovery
    of {heads:discovery_heads,plan:policy_partial_discovery}
  fun discover_selected_partial_with_policy (g : graph) scope
      {original,heads,maximum,scan_limit,step} =
    let
      val selection=SOME heads
      val _ = validate_discovery_heads g scope heads
      val _ = check_scope g scope val _ = usable g scope original
      val _ = if SmtReplayResourcePolicy.positive maximum andalso
          SmtReplayResourcePolicy.positive scan_limit then () else
        raise ERR "discover_partial" "nonpositive discovery bound"
      val _ = case !(#partial_running g) of NONE => ()
        | SOME active =>
            (active := false;
             raise ERR "discover_partial" "partial discovery reentry")
      val running = ref true
      val _ = #partial_running g := SOME running
      val epoch = Type.type_epoch () val symbols = Term.term_epoch ()
      val scans=ref(0:IntInf.int)
      val profiles=ref([]:policy_opaque_profile list)
      fun consume_scan message=
        if SmtReplayResourcePolicy.allows scan_limit (!scans+1)then
          scans:= !scans+1 else raise ERR "discover_partial" message
      val guards = ref ([] : (unit -> unit) list)
      val closures = ref ([] : binder_closure list)
      fun valid frame =
        (check_scope g scope;check_scope g frame;
         if !running andalso Type.type_epoch () = epoch andalso
             Term.term_epoch () = symbols then () else
           raise ERR "discover_partial" "scope/epoch/action retired";
         (case selection of NONE => () | SOME heads =>
           validate_discovery_heads g frame heads);
         List.app (fn guard => guard ()) (!guards))
      fun debit frame =
        (valid frame;
         consume_scan "discovery scan budget exhausted";
         step ();valid frame)
      fun invoke frame action =
        (debit frame;
         let val value = action () val _ = valid frame in value end)
      (* Declaration-only potential recognition: no variable spelling,
         schematic matching or semantic equality influences absence. *)
      fun selected_id frame id = case selection of NONE => false
        | SOME (DiscoveryHeads {rows,...}) =>
            let fun walk [] = false
                  | walk ((_,held,_)::rest) =
                      invoke frame (fn () =>
                        KernelSig.id_compare (id,held) = EQUAL) orelse
                      walk rest
            in walk rows end
      fun selected_term frame term = case selection of NONE => false
        | SOME _ =>
            if invoke frame (fn () => Term.is_const term) then
              selected_id frame (invoke frame
                (fn () => #Name (Term.dest_thy_constid term)))
            else false
      fun domain_needed frame ty =
        if invoke frame (fn () => Type.compare (ty,numSyntax.num) = EQUAL)
          then true
        else case invoke frame (fn () => Lib.total Type.dom_rng ty) of
            NONE => false
          | SOME (_,range) => invoke frame
              (fn () => Type.compare (range,numSyntax.num) = EQUAL)
      fun quantified frame operator abstraction get_type =
        if abstraction andalso
            invoke frame (fn () => Term.is_const operator) andalso
            invoke frame (fn () =>
              Term.same_const operator boolSyntax.universal orelse
              Term.same_const operator boolSyntax.existential) then
          let val ty = invoke frame get_type
          in case invoke frame (fn () => Lib.total Type.dom_rng ty) of
                SOME (domain,_) => domain_needed frame domain
              | NONE => false
          end
        else false
      (* Count-body substitutes only an ATOMIC marker. Recognition uses
         constructors, fixed declaration IDs and types, never variable names,
         equality of free variables, matching or semantic proof search. *)
      val recognized_terms = ref ([] : (scope * Term.term * bool) list)
      fun term_needed frame term = case selection of NONE =>
          term_needed_fresh frame term
        | SOME _ =>
          let fun find [] = NONE
                | find ((held_scope,held,answer)::rest) =
                    if invoke frame (fn () => held_scope=frame andalso
                        Portable.pointer_eq (term,held)) then SOME answer
                    else find rest
          in case find (!recognized_terms) of SOME answer =>
               (valid frame;answer)
            | NONE =>
              let val answer=term_needed_fresh frame term
                  val _ = debit frame
                  val _ = recognized_terms :=
                    (frame,term,answer):: !recognized_terms
              in valid frame;answer end
          end
      and term_needed_fresh frame term =
        if invoke frame (fn () => Term.is_comb term) then
          let val (operator,operand) = invoke frame
                (fn () => Term.dest_comb term)
          in if invoke frame (fn () => Term.is_abs operator) orelse
              quantified frame operator
                (invoke frame (fn () => Term.is_abs operand))
                (fn () => Term.type_of operand) then true
            else term_needed frame operator orelse term_needed frame operand
          end
        else if invoke frame (fn () => Term.is_abs term) then
          term_needed frame (invoke frame
            (fn () => SmtReplayImport.count_body term))
        else selected_term frame term
      val seen = ref
        (Redblackmap.mkDict (pair_compare Int.compare Int.compare))
      val captured = ref
        (Redblackmap.mkDict (pair_compare Int.compare Int.compare))
      (* Private callback-free setup holds all genuinely recorded frames
         BEFORE a step can retire one. No node_scope(body) inference.
         Setup map/frame work remains a separate unquoted prerequisite. *)
      fun capture_paths frame node =
        let val _ = valid frame val _ = usable g frame node
            val key = (scope_id frame,node_id node)
        in case Redblackmap.peek (!captured,key) of SOME _ => ()
          | NONE =>
            let val _ = consume_scan "frame scan budget exhausted"
                val _ = captured := Redblackmap.insert (!captured,key,())
            in case view g node of
                Application (left,right) =>
                  (capture_paths frame left;capture_paths frame right)
              | AdmittedBinder _ =>
                  let val closure = binder_closure g frame node
                      val data = binder_closure_data g frame closure
                      fun guard () = ignore
                        (binder_closure_data g frame closure)
                      val _ = guards := guard :: !guards
                      val _ = closures := closure :: !closures
                  in capture_paths (#body_frame data) (#body data) end
              | _ => ()
            end
        end
      fun graph_needed frame node =
        let val _ = valid frame val _ = usable g frame node
            val _ = debit frame val key = (scope_id frame,node_id node)
        in case Redblackmap.peek (!seen,key) of SOME value => value
          | NONE =>
            let val answer = case invoke frame (fn () => view g node) of
                  Application (operator,operand) =>
                    let val operator_view = invoke frame
                          (fn () => view g operator)
                        val beta = case operator_view of
                            AdmittedBinder _ => true | OpaqueRetained => true
                          | _ => false
                        val operand_view = invoke frame
                          (fn () => view g operand)
                        val abstraction = case operand_view of
                            AdmittedBinder _ => true | OpaqueRetained => true
                          | _ => false
                        val carrier = quantified frame
                          (invoke frame (fn () => representative g operator))
                          abstraction (fn () => type_of g operand)
                    in beta orelse carrier orelse
                      graph_needed frame operator orelse
                      graph_needed frame operand end
                | OpaqueRetained => term_needed frame
                    (invoke frame (fn () => representative g node))
                | AdmittedBinder _ =>
                    let val closure = invoke frame
                          (fn () => binder_closure g frame node)
                        val data = invoke frame
                          (fn () => binder_closure_data g frame closure)
                        fun guard () = ignore
                          (binder_closure_data g frame closure)
                        val _ = guard ()
                    in graph_needed (#body_frame data) (#body data) end
                | Constant id => selected_id frame id
                | _ => false
                val _ = valid frame
                val _ = seen := Redblackmap.insert (!seen,key,answer)
            in answer end
        end
      fun retained_guard () =
        (check_scope g scope;usable g scope original;
         if Type.type_epoch () = epoch andalso Term.term_epoch () = symbols
           then () else raise ERR "partial_view" "discovery epoch changed";
         List.app (fn guard => guard ()) (!guards))
      (* Only a child whose complete rule scan was false reaches this
         collector. It quotes full repeated annotations for mixed proof
         assembly; a whole unchanged NONE root needs no new type envelope. *)
      fun retained_ready () =
        partial_scope_live g scope andalso
        Type.type_epoch () = epoch andalso Term.term_epoch () = symbols
        andalso List.all (fn BinderClosure {record,...} =>
          partial_record_live g record) (!closures)
      fun retain_opaque node =
        let val _ = if graph_needed scope node then
              raise ERR "retain_opaque" "relevant binder is not a no-op"
            else ()
            val memo = Array.array (4093,[])
            val types = ref ([] : Type.hol_type list)
            val heads = ref ([] : Term.term list)
            fun add (a : IntInf.int) (b : IntInf.int) = a+b
            fun text_bytes text : IntInf.int =
              let val size = String.size text
                  fun walk index = if index = size then () else
                    (debit scope;ignore (String.sub (text,index));
                     walk (index+1))
                  val _ = walk 0
              in IntInf.fromInt size end
            fun weight ty : IntInf.int * IntInf.int =
              let val _ = debit scope
              in if invoke scope (fn () => Type.is_vartype ty) then
                  (1,text_bytes (invoke scope
                    (fn () => Type.dest_vartype ty)))
                else
                  let val {Thy,Tyop,Args} = invoke scope
                        (fn () => Type.dest_thy_typeid ty)
                      val name = invoke scope (fn () => KernelSig.name_of Tyop)
                      val own = add (text_bytes Thy) (text_bytes name)
                  in List.foldl (fn (child,(nodes,bytes)) =>
                       let val (n,b) = weight child
                       in (add nodes n,add bytes b) end) (1,own) Args end
              end
            fun annotation ty =
              let val counts = weight ty val _ = debit scope
                  val _ = types := ty :: !types
              in counts end
            fun lookup term [] = NONE
              | lookup term ((held,value)::rest) =
                  (debit scope;if Portable.pointer_eq (term,held) then
                    SOME value else lookup term rest)
            fun visit term =
              let val bucket = invoke scope (fn () => physical_hint term)
                  val _ = debit scope
              in case lookup term (Array.sub (memo,bucket)) of
                  SOME value => value
                | NONE =>
                  let val ty = invoke scope (fn () => Term.type_of term)
                      val (own,own_bytes) = annotation ty
                      val value = if invoke scope (fn () => Term.is_comb term)
                        then
                          let val (f,x) = invoke scope
                                (fn () => Term.dest_comb term)
                              val a = visit f val b = visit x
                          in {raw = policy_discovery_plus 1
                                (policy_discovery_plus (#raw a) (#raw b)),
                              inc = policy_discovery_plus 1
                                (policy_discovery_plus (#inc a) (#inc b)),
                              ann = add own (add (#ann a) (#ann b)),
                              type_bytes = add own_bytes
                                (add (#type_bytes a) (#type_bytes b)),
                              ty = own,projection = Option.map
                                (fn path => ProjectionApplication (term,path))
                                (#projection a)} end
                        else if invoke scope
                            (fn () => Term.is_abs term) then
                          let val domain = invoke scope
                                (fn () => #1 (Type.dom_rng ty))
                              val (binder,binder_bytes) = annotation domain
                              val body = visit (invoke scope
                                (fn () => SmtReplayImport.count_body term))
                          in {raw = policy_discovery_plus 1 (#raw body),
                              inc = policy_discovery_plus 2 (#inc body),
                              ann = add own (add binder (#ann body)),
                              type_bytes = add own_bytes
                                (add binder_bytes (#type_bytes body)),ty = own,
                              projection = Option.map
                                (fn path =>
                                  ProjectionBinder (term,domain,path))
                                (#projection body)}
                          end
                        else
                          let val _ = if invoke scope
                                  (fn () => Term.is_const term) then
                                heads := term :: !heads else ()
                          in {raw = 1,inc = 1,ann = own,
                              type_bytes = own_bytes,ty = own,
                              projection = if false then
                                SOME (ProjectionAtom {term = term,
                                  variable = invoke scope
                                    (fn () => Term.is_var term)}) else NONE}
                          end
                      val _ = debit scope
                      val _ = Array.update (memo,bucket,
                        (term,value) :: Array.sub (memo,bucket))
                  in value end
              end
            val original = invoke scope (fn () => representative g node)
            val value = visit original
            val profile = PolicyOpaqueProfile
              {owner = #owner g,scope = scope,node = node,
               original = original,raw = #raw value,inc = #inc value,
               ann = #ann value,ty = #ty value,
               type_bytes = #type_bytes value,types = !types,
               heads = !heads,
               ready = retained_ready,guard = retained_guard}
            val _ = valid scope
            val _ = validation_change g
            val _ = profiles := profile :: !profiles
        in () end
      fun atom node retained =
        let val _ = if retained then (case view g node of
                  OpaqueRetained => retain_opaque node | _ => ()) else ()
            val term = invoke scope (fn () => representative g node)
            val proof = invoke scope (fn () => Thm.REFL term)
            val source = source_for g term node proof
        in if retained then PartialRetained (node,source)
           else PartialAtom (node,source) end
      fun opened node =
        let val source = invoke scope
              (fn () => record_opened_view_with_policy g scope maximum node)
            val _ = capture_paths scope (#node source)
        in PartialFull (node,source) end
      val recipe_memo = ref ([] : (node * bool * partial_recipe) list)
      fun cached_recipe force node [] = NONE
        | cached_recipe force node ((saved,mode,recipe)::rest) =
            (debit scope;
             if saved = node andalso mode = force then SOME recipe
             else cached_recipe force node rest)
      (* Whole original and opened backing paths were captured before this
         point. All incoming owners/epochs/scopes are rechecked before a
         hit, including after the caller's charged discovery hook. The key
         is actual original node AND force mode in this one fixed scope. *)
      fun visit force node =
        (valid scope;usable g scope node;
         case cached_recipe force node (!recipe_memo) of SOME recipe =>
           (valid scope;usable g scope node;recipe)
         | NONE =>
           let val recipe = visit_fresh force node
               val _ = debit scope
               val _ = recipe_memo := (node,force,recipe) :: !recipe_memo
               val _ = valid scope
           in recipe end)
      and visit_fresh force node =
        (valid scope;usable g scope node;
         case invoke scope (fn () => view g node) of
           OpaqueRetained =>
             if force orelse graph_needed scope node then
               opened node
             else atom node true
         | AdmittedBinder _ =>
             if force orelse graph_needed scope node then
               opened node
             else atom node true
         | Application (operator,operand) =>
             let val ov = invoke scope (fn () => view g operator)
                 val beta = case ov of AdmittedBinder _ => true
                   | OpaqueRetained => true | _ => false
                 val operand_view = invoke scope (fn () => view g operand)
                 val abstraction = case operand_view of
                     AdmittedBinder _ => true | OpaqueRetained => true
                   | _ => false
                 val carrier = quantified scope
                   (invoke scope (fn () => representative g operator))
                   abstraction (fn () => type_of g operand)
                 val left = visit beta operator
                 val right = visit carrier operand
                 val l = partial_source left val r = partial_source right
                 val term = invoke scope (fn () => representative g node)
                 val target = invoke scope
                   (fn () => application g scope (#node l,#node r))
                 val bridge = invoke scope (fn () =>
                   align_application term (#bridge l) (#bridge r)
                     (representative g target))
                 val source = source_for g term target bridge
             in PartialApplication (node,source,left,right) end
         | _ => atom node false)
      fun build () =
        let val _ = capture_paths scope original
            val changed = graph_needed scope original
            val _ = if changed then () else case selection of NONE => ()
              | SOME _ => (case view g original of
                  OpaqueRetained => retain_opaque original | _ => ())
            val recipe = if changed then SOME (visit false original) else NONE
            val result = PartialDiscovery
              {owner = #owner g,scope = scope,original = original,
               recipe = recipe,guard = retained_guard}
            val _ = valid scope
            val _ = case recipe of NONE => () | SOME value =>
              let val source = partial_source value
                  val row = {source = source,roots =
                    [closure_root g scope original],guard = fn () =>
                      (retained_guard ();
                       validate_partial_recipe g scope value)}
                  val key = (scope_id scope,node_id original)
                  val rows = Option.getOpt
                    (Redblackmap.peek (!(#identity_views g),key),[])
                  val old = Option.getOpt
                    (Redblackmap.peek (!(#partial_sources g),key),[])
                  val _ = validation_change g
                  val _ = #partial_sources g := Redblackmap.insert
                    (!(#partial_sources g),key,result :: old)
              in validation_change g;
                 #identity_views g := Redblackmap.insert
                (!(#identity_views g),key,row :: rows) end
        in result end
      val result = build () handle primary =>
        (running := false;#partial_running g := NONE;raise primary)
      val _ = running := false val _ = #partial_running g := NONE
    in PolicySelectedPartialDiscovery {heads=heads,
      plan=PolicyPartialDiscovery {owner= #owner g,scope=scope,plan=result,
        maximum=maximum,scan_limit=scan_limit,scans= !scans,
        profiles=List.rev(!profiles)}}end

  fun selected_partial_data_with_policy (g:graph) scope
      (expected as DiscoveryHeads {owner,identity,...})
      (PolicySelectedPartialDiscovery
        {heads=held as DiscoveryHeads {identity=captured,...},plan}) =
    let val _=if owner= #owner g andalso identity=captured then ()else
          raise ERR "selected_partial_data" "foreign graph or selection"
        val _=validate_discovery_heads g scope expected
        val _=validate_discovery_heads g scope held
        val _=validate_partial_with_policy g scope plan
        val PolicyPartialDiscovery
          {plan=PartialDiscovery {original,...},profiles,...}=plan
    in {original=original,view=partial_view_with_policy g scope plan,
      profiles=profiles}end

  (* A completed retained profile proves generic carrier/beta absence.
     Its actual constant-leaf vector may additionally prove selected-head
     absence, without reopening a binder or constructing a theorem.
     Relevant heads still use the existing positive programme; its caller
     must independently admit every native opening from its real contract.
     Missing profiles are unknown, never an unchanged result. *)
  fun discover_selected_profiled_partial_with_policy (g:graph) scope
      {original,heads,profiles,maximum,scan_limit,step} =
    let
      val _=validate_discovery_heads g scope heads
      val _=check_scope g scope
      val _=usable g scope original
      val _=if SmtReplayResourcePolicy.positive maximum andalso
          SmtReplayResourcePolicy.positive scan_limit then ()else
        raise ERR "selected_profile" "nonpositive discovery bound"
      (* Check foreign headers before activating any profile backing. *)
      val _=List.app(fn PolicyOpaqueProfile{owner,...}=>
        if owner= #owner g then ()else
          raise ERR "selected_profile" "foreign graph profile")profiles
      fun seek []=raise ERR "selected_profile"
            "missing genuine original no-op profile"
        | seek(p::rest)=case opaque_profile_for_node_with_policy
            g scope original p of SOME _=>p | NONE=>seek rest
      val profile=seek profiles
      val _=case !(#partial_running g)of NONE=>() | SOME active=>
        (active:=false;
         raise ERR "selected_profile" "partial discovery reentry")
      val running=ref true
      val _= #partial_running g:=SOME running
      val epoch=Type.type_epoch()val symbols=Term.term_epoch()
      val scans=ref(0:IntInf.int)
      fun guard()=
        (validate_discovery_heads g scope heads;
         check_scope g scope;usable g scope original;
         if Type.type_epoch()=epoch andalso Term.term_epoch()=symbols then
           ()else raise ERR "selected_profile" "declaration epoch changed";
         case opaque_profile_for_node_with_policy g scope original profile of
           SOME _=>() | NONE=>raise ERR "selected_profile"
             "different original no-op profile")
      fun valid()=(guard();if !running then ()else
        raise ERR "selected_profile" "discovery action retired")
      fun debit()=
        (valid();if SmtReplayResourcePolicy.allows scan_limit(!scans+1)then
            scans:= !scans+1 else
          raise ERR "selected_profile" "discovery scan budget exhausted";
         step();valid())
      fun invoke action=
        (debit();let val result=action()val _=valid()in result end)
      fun selected id=
        let val DiscoveryHeads{rows,...}=heads
            fun walk []=false
              | walk((_,held,_)::rest)=
                  invoke(fn()=>KernelSig.id_compare(id,held)=EQUAL)orelse
                  walk rest
        in walk rows end
      fun relevant term=
        let val id=invoke(fn()=> #Name(Term.dest_thy_constid term))
        in selected id end
      fun run()=
        let val data=invoke(fn()=>
                  opaque_profile_heads_with_policy g scope profile)
            val _=if #node data=original then ()else
              raise ERR "selected_profile" "different retained head root"
            val changed=List.exists relevant(#heads data)
            val _=valid()
        in changed end
      fun finish()=(running:=false;#partial_running g:=NONE)
      val changed=run()handle primary=>(finish();raise primary)
      val _=finish()
    in
      if changed then
        let val result=discover_selected_partial_with_policy g scope
              {original=original,heads=heads,maximum=maximum,
               scan_limit=SmtReplayResourcePolicy.remaining
                 scan_limit(!scans),step=step}
            val PolicySelectedPartialDiscovery
              {plan=PolicyPartialDiscovery{plan,scans=used,profiles,...},...}
                =result
            val _=guard()
        in PolicySelectedPartialDiscovery{heads=heads,
          plan=PolicyPartialDiscovery{owner= #owner g,scope=scope,plan=plan,
            maximum=maximum,scan_limit=scan_limit,scans= !scans+used,
            profiles=profiles}}end
      else
        let val _=guard()
            val plan=PartialDiscovery{owner= #owner g,scope=scope,
              original=original,recipe=NONE,guard=guard}
        in PolicySelectedPartialDiscovery{heads=heads,
          plan=PolicyPartialDiscovery{owner= #owner g,scope=scope,plan=plan,
            maximum=maximum,scan_limit=scan_limit,scans= !scans,
            profiles=[profile]}}end
    end

  (* Only the actual saved policy plan can supply this constructor. No raw
     Source/node pair, fallback discovery or finite sentinel is accepted. *)
  fun carrier_alpha_from_partial_with_policy (g:graph) scope held=
    let val _=validate_partial_with_policy g scope held
        val PolicyPartialDiscovery{plan,...}=held
        val PartialDiscovery{recipe,...}=plan
    in case recipe of NONE=>NONE|SOME actual=>
      let val source=partial_source actual
          val result=CarrierPartial{plan=plan,recipe=actual,
            annotation=closure_root g scope(#node source)}
          val _=validate_carrier_alpha g scope result
      in SOME result end
    end

  (* Authenticate the actual selected authority before projecting its saved
     policy plan. This does not equate generic no-op and numeric no-op. *)
  fun carrier_alpha_from_selected_with_policy g scope expected
      (held as PolicySelectedPartialDiscovery{plan,...})=
    (ignore(selected_partial_data_with_policy g scope expected held);
     carrier_alpha_from_partial_with_policy g scope plan)

  (* Every child retains the SAME whole-plan guard. A full opened child is
     projected from its genuine cached opened source, never opened again. *)
  fun carrier_alpha_application_children_with_policy (g:graph) scope alpha=
    let val incoming=carrier_alpha_data g scope alpha
        val _=usable g scope(#original incoming)
        val(left,right)=closure_application_children g scope
          (#annotation incoming)
        fun child plan annotation actual=
          let val result=CarrierPartial
                {plan=plan,recipe=actual,annotation=annotation}
              val _=validate_carrier_alpha g scope result
          in result end
        fun opened plan original annotation=
          let val source=cached_opened_view g scope original
              val _=validate_discovered_view g scope original source
          in child plan annotation(PartialFull(original,source))end
    in case alpha of
        CarrierPartial{plan,recipe=PartialApplication(_,_,a,b),...}=>
          (child plan left a,child plan right b)
      | CarrierPartial{plan,recipe=PartialFull(original,_),...}=>
          (case view g original of Application(f,x)=>
             (opened plan f left,opened plan x right)
           | _=>raise ERR "carrier_alpha_children_with_policy"
               "raw source is not application")
      | _=>raise ERR "carrier_alpha_children_with_policy"
          "expected genuine partial-policy application recipe"
    end

  (* Borrow only the actual original and optional view from a genuine
     completed policy discovery. NONE is generic carrier/beta absence,
     never selected numeric absence, geometry, or native permission. *)
  fun partial_source_header_with_policy (g:graph) scope
      (held as PolicyPartialDiscovery{owner,scope=caller,...}) =
    let val _=if owner= #owner g andalso caller=scope then ()else
          raise ERR "partial_source_header" "different graph/source caller"
        val _=validate_partial_with_policy g scope held
        val PolicyPartialDiscovery{plan=PartialDiscovery
          {original,recipe,...},...}=held
    in {original=original,view=Option.map partial_source recipe}end

  (* Compare BOTH immutable owners before either retained backing. This
     query borrows an existing alpha recipe and an existing rich capture;
     it does not acquire a profile, open a term or mint an identity view. *)
  fun alpha_metric_data_with_policy (g:graph) caller alpha metric =
    let
      val (owner,scope)=case alpha of
          CarrierPartial {plan=PartialDiscovery {owner,scope,...},...}=>
            (owner,scope)
        | CarrierFull (DiscoveredAlpha {owner,scope,...})=>(owner,scope)
        | CarrierIdentity {owner,scope,...}=>(owner,scope)
      val ProfiledMetric {owner=metric_owner,scope=metric_scope,...}=metric
      val _=if owner= #owner g andalso metric_owner= #owner g andalso
          scope=caller andalso metric_scope=caller then () else
        raise ERR "alpha_metric" "different graph or actual requester"
      val data=carrier_alpha_data g caller alpha
      val counts=profiled_metric_data g caller metric
      val source= #source data
      val _=if #node source= #node counts andalso
          closure_child_node g caller (#annotation data)= #node counts
        then () else raise ERR "alpha_metric" "different rich capture"
    in {original= #original data,source=source,
      annotation= #annotation data,raw= #raw counts,inc= #inc counts,
      types= #types counts} end

(* Isolated Source implementation of the reviewed local guard ports.
   Not installed, compiled or selected. Four public ports share the supplied
   genuine opaque R.scope_meter; this does not connect an A/Ready payer.
   The finer root/scope logical-event model is explicit. The two inherited
   node13 programmes remain qualified, including parameter reception and
   observer/private CPU administration. No aggregate Ready invoice, finite
   acquired acceptance or whole CPU pricing is claimed. *)

  fun root_scope_with_meter (g:graph) meter =
    (R.scope_meter_charge meter 3;
     Scope {owner= #owner g,id=0})

  fun scope_frame_with_meter (g:graph) held meter =
    let
      (* Existing owner tariff4 retained, plus5 for formerly implicit
         wrapper payload/field extraction and local holding in this model. *)
      val _=R.scope_meter_charge meter 5
      val _=R.scope_meter_charge meter 4
    in
      case held of Scope {owner,id} =>
        if owner <> #owner g then
          (R.scope_meter_charge meter 15;
           raise ERR "scope" "scope belongs to a different graph")
        else
          let
            (* Old field/ref2 retained; the added explicit table hold is1. *)
            val _=R.scope_meter_charge meter 1
            val _=R.scope_meter_charge meter 2
            val table= !(#scopes g)
            (* Tuple1, two curried applications2, result hold1, case1. *)
            val _=R.scope_meter_charge meter 5
            val found=R.scope_lookup_int meter (table,id)
          in
            case found of
                SOME _ =>
                  let
                    (* Second immutable tag match1, payload1, holding1.
                       Outer SOME_ extracts no payload before this charge. *)
                    val _=R.scope_meter_charge meter 3
                    val SOME frame=found
                  in frame end
              | NONE =>
                  (R.scope_meter_charge meter 15;
                   raise ERR "scope" "unknown scope")
          end
    end

  fun check_scope_with_meter (g:graph) scope meter =
    let
      (* Three actual argument applications and returned-frame hold. *)
      val _=R.scope_meter_charge meter 4
      val frame=scope_frame_with_meter g scope meter
      (* Two field projections+two holds, active ref read, not, branch. *)
      val _=R.scope_meter_charge meter 7
      val parent= #parent frame
      val active= #active frame
    in
      if not (!active) then
        (R.scope_meter_charge meter 15;
         raise ERR "scope" "scope is closed")
      else
        (R.scope_meter_charge meter 1;
         case parent of
             NONE => (R.scope_meter_charge meter 1;())
           | SOME _ =>
               let
                 (* Immutable tag/payload/hold3 plus recursive apps3. *)
                 val _=R.scope_meter_charge meter 6
                 val SOME outer=parent
               in check_scope_with_meter g outer meter end)
    end

  val validate_scope_with_meter=check_scope_with_meter

  (* Closed Source-event revision query. No revision field is touched
     until genuine same-graph Scope/ancestor validation has succeeded.
     The caller supplies its authentic retained original-A meter. *)
  fun validation_revision_with_meter (g:graph) caller meter =
    let
      (* Three curried validation applications and sequencing: 4. *)
      val _ = R.scope_meter_charge meter 4
      val _ = check_scope_with_meter g caller meter
      (* Private field projection and local reference holding: 2. *)
      val _ = R.scope_meter_charge meter 2
      val revision = #validation_changes g
      (* The final dereference: 1. No new result reference is allocated. *)
      val _ = R.scope_meter_charge meter 1
    in !revision end

  (* The two node ports remain EXACT design1 twins after this point.
     Their inherited13 is not silently upgraded to this finer local model.
     Their datatype parameter matching/observer/primitive CPU qualifications
     remain explicit; they are not selected into A or a Graph provider here. *)
  (* DESIGN ONLY. Closed specialization of observe_node g #accesses.
     No selector/callback is received. Billing primitive transport and its
     own debit administration are the explicit nonrecursive base. *)
  fun observe_node_accesses_with_meter (g:graph) meter =
    let
      val _ = R.scope_meter_charge meter 4
      val observation = !(#node_observation g)
    in
      case observation of
          NONE => (R.scope_meter_charge meter 1;())
        | SOME _ =>
            let
              val _ = R.scope_meter_charge meter 6
              val SOME tagged = observation
              val NodeObservation fields = tagged
              val _ = R.scope_meter_charge meter 2
              val cell = #accesses fields
              val _ = R.scope_meter_charge meter 3
            in cell := !cell+1 end
    end

  fun node_scope_with_meter (g:graph) held meter =
    let
      val _ = R.scope_meter_charge meter 9
    in
      case held of Node {owner,id} =>
        if owner = #owner g then
          let
            val _ = R.scope_meter_charge meter 3
            val table = !(#nodes g)
            val _ = R.scope_meter_charge meter 5
            val found = R.scope_lookup_int meter (table,id)
          in
            case found of
                NONE =>
                  (R.scope_meter_charge meter 15;
                   raise ERR "node" "unknown node")
              | SOME _ =>
                  let
                    val _ = R.scope_meter_charge meter 3
                    val SOME fields = found
                  in
                    R.scope_meter_charge meter 2;
                    observe_node_accesses_with_meter g meter;
                    R.scope_meter_charge meter 1;
                    #scope fields
                  end
          end
        else
          (R.scope_meter_charge meter 15;
           raise ERR "node" "node belongs to a different graph")
    end

  fun representative_with_meter (g:graph) held meter =
    let
      val _ = R.scope_meter_charge meter 9
    in
      case held of Node {owner,id} =>
        if owner = #owner g then
          let
            val _ = R.scope_meter_charge meter 3
            val table = !(#nodes g)
            val _ = R.scope_meter_charge meter 5
            val found = R.scope_lookup_int meter (table,id)
          in
            case found of
                NONE =>
                  (R.scope_meter_charge meter 15;
                   raise ERR "node" "unknown node")
              | SOME _ =>
                  let
                    val _ = R.scope_meter_charge meter 3
                    val SOME fields = found
                  in
                    R.scope_meter_charge meter 2;
                    observe_node_accesses_with_meter g meter;
                    R.scope_meter_charge meter 1;
                    #term fields
                  end
          end
        else
          (R.scope_meter_charge meter 15;
           raise ERR "node" "node belongs to a different graph")
    end


  (* Isolated closed initializer. The supplied genuine policy meter owns
     every debit. No A, Work, Seed, Type/Hyp or native grant is constructed.
     Control transport and pre-charge metadata retain design qualifications. *)
  fun new_with_bootstrap_meter meter : graph =
    let
      val _=R.scope_meter_charge meter 4
      val policy_sample=R.scope_meter_remaining_with_policy meter
      val local_admin=case policy_sample of
          SmtReplayResourcePolicy.Uncapped => 4238
        | SmtReplayResourcePolicy.AtMost _ => 4245
      (* Retain the accepted conservative constructor administration.
         Additional paid-index/root capture has its own local128; no
         removed quote work is relabelled as a prospective payment. *)
      val _=R.scope_meter_charge meter local_admin
      val _=R.scope_meter_charge meter 128
      val owner=ref ()
      val empty_scopes : frame R.int_map=R.empty_int ()
      val frame={parent=NONE,active=ref true,
        bindings=Redblackmap.mkDict
          (pair_compare String.compare Int.compare)}
      val scopes=R.scope_int_singleton_from_empty meter
        (empty_scopes,0,frame)
      val semantic_types : int R.graph_key_map=
        R.scope_empty_graph_key meter
      val semantic_keys : node R.graph_key_map=
        R.scope_empty_graph_key meter
      val empty_placeholders : Term.term R.int_map=R.empty_int ()
    in
      {owner = owner, next = ref 0, next_scope = ref 1,
       node_observation = ref NONE,
       scope_retirements = ref 0,
       validation_changes = ref 0,
       nodes = ref (R.empty_int ()),
       scopes = ref scopes,
       indices = PaidIndices
         {owner=owner,root=Scope {owner=owner,id=0},meter=meter,
          epoch=Type.type_epoch (),symbols=Term.term_epoch (),
          types=ref semantic_types,keys=ref semantic_keys,recent=ref [],
          empty_placeholders=empty_placeholders},
       imports = Array.array (4093, []),
       binders = ref (Redblackmap.mkDict Int.compare),
       binder_origins = ref (Redblackmap.mkDict Int.compare),
       binder_closures = ref (Redblackmap.mkDict Int.compare),
       opened_views = ref (Redblackmap.mkDict
         (pair_compare Int.compare Int.compare)),
       identity_views = ref (Redblackmap.mkDict
         (pair_compare Int.compare Int.compare)),
       partial_sources = ref (Redblackmap.mkDict
         (pair_compare Int.compare Int.compare)),
       partial_projections = ref (Redblackmap.mkDict Int.compare),
       partial_running = ref NONE,
       partial_profiles = ref (Redblackmap.mkDict Int.compare),
       reserved = ref (R.empty_string ()),
       placeholders = ref empty_placeholders,
       next_name = ref 0, next_bound_name = ref 0,
       next_flexible_name = ref 0,
       equalities = ref (Redblackmap.mkDict
         (pair_compare Int.compare Int.compare))}
    end


  (* Closed structural storage only. No Term/Type object or G.node is
     admitted by these ports; returned integers are metadata table IDs.
     The backing fresh graph never escapes and no existing graph can be
     converted. The opaque handle captures the one original payer. *)
  datatype fixed_type_id = FixedTypeId of {owner:unit ref,id:int}
  datatype fixed_node_id = FixedNodeId of {owner:unit ref,id:int}
  datatype fixed_type_key = FixedTypeVariable of string
    | FixedTypeOperator of KernelSig.kernelid * fixed_type_id list
  datatype fixed_node_key =
      FixedVariable of variable_kind * string * fixed_type_id
    | FixedConstant of KernelSig.kernelid * fixed_type_id
    | FixedApplication of fixed_node_id * fixed_node_id
  datatype fixed_storage = FixedStorage of
    {graph:graph,owner:unit ref,root:scope,meter:R.scope_meter,
     epoch:int,symbols:int,types:int R.graph_key_map ref,
     keys:int R.graph_key_map ref,original_context_claimed:bool ref}

  fun fixed_storage_context (FixedStorage held) caller =
    let
      val meter = #meter held
      val _ = R.scope_meter_charge meter 32
      (* Reject the immutable caller before touching retained backing. *)
      val _ = if caller = #root held then () else
        raise ERR "fixed_storage" "different original root"
      val graph = #graph held
      val _ = if #owner held = #owner graph then () else
        raise ERR "fixed_storage" "different graph owner"
      val _ = if Type.type_epoch () = #epoch held andalso
          Term.term_epoch () = #symbols held then () else
        raise ERR "fixed_storage" "Type or Term epoch changed"
      val _ = R.scope_meter_charge meter 4
      val _ = check_scope_with_meter graph caller meter
    in held end

  fun fixed_storage_counts storage caller =
    let
      val held = fixed_storage_context storage caller
      val meter = #meter held
      val _ = R.scope_meter_charge meter 16
      val types = R.scope_graph_key_count meter (!(#types held))
      val keys = R.scope_graph_key_count meter (!(#keys held))
    in {types=types,keys=keys} end

  fun fixed_storage_revision storage caller =
    let
      val held = fixed_storage_context storage caller
      val meter = #meter held
      val _ = R.scope_meter_charge meter 4
    in validation_revision_with_meter (#graph held) caller meter end

  fun fixed_type_key_to_r (FixedStorage held) key =
    let
      val meter = #meter held
      val _ = R.scope_meter_charge meter 24
      fun child (FixedTypeId {owner,id}) =
        let
          val _ = R.scope_meter_charge meter 12
          val _ = if owner = #owner held then () else
            raise ERR "fixed_type_key" "foreign metadata type id"
          val bound = R.scope_graph_key_count meter (!(#types held))
        in if 0 <= id andalso id < bound then id else
          raise ERR "fixed_type_key" "unknown metadata type id" end
      fun children ids =
        (R.scope_meter_charge meter 12;
         case ids of [] => []
           | item::rest =>
               let val id = child item
                   val tail = children rest
               in id::tail end)
    in case key of
        FixedTypeVariable name => R.GraphTypeVariable name
      | FixedTypeOperator(name,ids) =>
          R.GraphTypeOperator(name,children ids)
    end

  fun fixed_type_key_id storage caller key =
    let
      val held = fixed_storage_context storage caller
      val meter = #meter held
      val _ = R.scope_meter_charge meter 4
      val key = fixed_type_key_to_r storage key
      val _ = R.scope_meter_charge meter 16
      val table = !(#types held)
    in case R.scope_lookup_graph_key meter (table,key) of
        SOME id =>
          (R.scope_meter_charge meter 8;
           FixedTypeId {owner= #owner held,id=id})
      | NONE =>
          let
            val _ = R.scope_meter_charge meter 32
            val id = R.scope_graph_key_count meter table
            val next = R.scope_put_graph_key meter (table,key,id)
            (* The fixed local commit reservation is paid before put.
               A refused persistent put leaves both retained refs intact. *)
            val _ = #types held := next
            val _ = validation_change (#graph held)
          in FixedTypeId {owner= #owner held,id=id} end
    end

  fun fixed_node_key_to_r (FixedStorage held) key =
    let
      val meter = #meter held
      val _ = R.scope_meter_charge meter 24
      fun tid (FixedTypeId {owner,id}) =
        let
          val _ = R.scope_meter_charge meter 12
          val _ = if owner = #owner held then () else
            raise ERR "fixed_node_key" "foreign metadata type id"
          val bound = R.scope_graph_key_count meter (!(#types held))
        in if 0 <= id andalso id < bound then id else
          raise ERR "fixed_node_key" "unknown metadata type id" end
      fun child (FixedNodeId {owner,id}) =
        let
          val _ = R.scope_meter_charge meter 12
          val _ = if owner = #owner held then () else
            raise ERR "fixed_node_key" "foreign metadata node id"
          val bound = R.scope_graph_key_count meter (!(#keys held))
        in if 0 <= id andalso id < bound then id else
          raise ERR "fixed_node_key" "unknown metadata node id" end
    in case key of
        FixedVariable(kind,name,ty) =>
          R.GraphVariable(scope_id (#root held),kind_id kind,name,tid ty)
      | FixedConstant(name,ty) => R.GraphConstant(name,tid ty)
      | FixedApplication(left,right) =>
          let val l = child left
              val r = child right
          in R.GraphApplication(scope_id (#root held),l,r) end
    end

  fun fixed_node_key_id storage caller key =
    let
      val held = fixed_storage_context storage caller
      val meter = #meter held
      val _ = R.scope_meter_charge meter 4
      val key = fixed_node_key_to_r storage key
      val _ = R.scope_meter_charge meter 16
      val table = !(#keys held)
    in case R.scope_lookup_graph_key meter (table,key) of
        SOME id =>
          (R.scope_meter_charge meter 8;
           FixedNodeId {owner= #owner held,id=id})
      | NONE =>
          let
            val _ = R.scope_meter_charge meter 32
            val id = R.scope_graph_key_count meter table
            val next = R.scope_put_graph_key meter (table,key,id)
            val _ = #keys held := next
            val _ = validation_change (#graph held)
          in FixedNodeId {owner= #owner held,id=id} end
    end

  fun new_fixed_storage_with_bootstrap_meter meter =
    let
      (* Scoped defined administration tariff, paid before the backing
         constructor call. Not a complete Source-event/CPU upper bound. *)
      val _ = R.scope_meter_charge meter 128
      val graph = new_with_bootstrap_meter meter
      val root = root_scope_with_meter graph meter
      val types = R.scope_empty_graph_key meter
      val keys = R.scope_empty_graph_key meter
      val _ = R.scope_meter_charge meter 4
      val held = FixedStorage
        {graph=graph,owner= #owner graph,root=root,meter=meter,
         epoch=Type.type_epoch (),symbols=Term.term_epoch (),
         types=ref types,keys=ref keys,original_context_claimed=ref false}
    in (held,root) end

  (* Additive ORIGINAL birth bundle, not an extractor accepting an existing
     fixed_storage handle. The ONE newly born graph is deliberately
     returned alongside storage; old fixed-only factory handles retain
     their original privacy. No ID becomes a semantic G node/Ready receipt. *)
  fun new_original_with_fixed_storage_bootstrap_meter meter =
    let
      (* Defined local reservation; not a whole Source-event/CPU upper. *)
      val _ = R.scope_meter_charge meter 16
      val (storage as FixedStorage held,root) =
        new_fixed_storage_with_bootstrap_meter meter
    in {graph= #graph held,root=root,storage=storage} end

  (* ONE FIRST canonical Bool variable, on this same fresh original graph.
     No raw theorem, callback, metadata ID or arbitrary existing graph is
     accepted. Returned source has a genuine registry node and private REFL.
     A must additionally authenticate its original request/native history. *)
  type first_boolean_variable_limits =
    {construction_limits:SmtReplayResourcePolicy.graph_policy,
     semantic_limits:SmtReplayResourcePolicy.semantic_policy,
     native_limits:
       {semantic_limits:SmtReplayResourcePolicy.semantic_policy,
        import_limit:SmtReplayResourcePolicy.limit,
        type_work_limit:SmtReplayResourcePolicy.limit}}

  fun import_first_boolean_variable storage caller
      ({original,limits}:{original:Term.term,
        limits:first_boolean_variable_limits}) =
    let
      val held = fixed_storage_context storage caller
      val graph = #graph held
      val meter = #meter held
      val paid = paid_first_indices graph meter
      val first = paid_index_snapshot graph paid
      (* Defined local validation/capture tariff, not whole CPU pricing. *)
      val _ = R.scope_meter_charge meter 128
      val allows = SmtReplayResourcePolicy.allows
      val construction = #construction_limits limits
      val semantic = #semantic_limits limits
      val native = #native_limits limits
      val ns = #semantic_limits native
      (* Exact single-original programme bounds. Existing A reflection
         cannot be counted as fresh credit; its caller admits history. *)
      val _ = if allows (#import_limit construction) 1 andalso
          allows (#literal_limit construction) 1 andalso
          allows (#input_limit semantic) 1 andalso
          allows (#output_limit semantic) 11 andalso
          allows (#template_limit semantic) 11 andalso
          allows (#input_limit ns) 1 andalso
          allows (#output_limit ns) 11 andalso
          allows (#template_limit ns) 11 andalso
          allows (#import_limit native) 5 andalso
          allows (#type_work_limit native) 1562 then () else
        raise ERR "first_boolean_variable" "original policy exhausted"
      val _ = R.scope_meter_charge meter 128
      val old_types = #types first
      val old_keys = #keys first
      val old_nodes = #nodes first
      val old_reserved = #reserved first
      fun fresh () =
        !(#validation_changes graph)=0 andalso !(#next graph)=0 andalso
        !(#next_scope graph)=1 andalso !(#scope_retirements graph)=0 andalso
        R.scope_graph_key_count meter (!(#types paid))=0 andalso
        R.scope_graph_key_count meter (!(#keys paid))=0 andalso
        List.null (!(#recent paid)) andalso
        not (Option.isSome (!(#node_observation graph))) andalso
        not (Option.isSome (!(#partial_running graph)))
      val _ = if fresh () then () else
        raise ERR "first_boolean_variable" "semantic registry is not fresh"
      val _ = if R.scope_graph_key_count meter (!(#types held))=0 andalso
          R.scope_graph_key_count meter (!(#keys held))=0 then () else
        raise ERR "first_boolean_variable" "metadata registry is not fresh"
      (* Positive Var before type_of; no arbitrary App/Abs/Clos descent. *)
      val _ = R.scope_meter_charge meter 74
    in if not (Term.is_var original) then NONE
      else if not (Portable.pointer_eq (Term.type_of original,Type.bool))
        then NONE
      else
        let
          (* Additional fixed Bool-ID observation allowance64; reflected
             proof bound1424 is the independently reviewed closed REFL. *)
          val _ = R.scope_meter_charge meter 64
          val (name,ty) = Term.dest_var original
          val bool_name = #Tyop (Type.dest_thy_typeid Type.bool)
          val _ = R.scope_meter_charge meter 32
          val length = String.size name
          (* EXACT pointer_bucket4 Var route, with each byte/spine paid.
             Hashes route only; all initial semantic imports are absent. *)
          fun name_hash i hash =
            (R.scope_meter_charge meter 8;
             if i=length then hash else
               (R.scope_meter_charge meter 16;
                name_hash (i+1)
                  (Word.+ (Word.* (hash,0w33),
                    Word.fromInt (Char.ord (String.sub(name,i)))))))
          val hash = name_hash 0 0w17
          val _ = R.scope_meter_charge meter 32
          val bucket = Word.toInt (Word.mod
            (Word.+ (Word.* (0w37,hash),hash),Word.fromInt 4093))
          val _ = if List.null (Array.sub (#imports graph,bucket)) then ()
            else raise ERR "first_boolean_variable"
              "import bucket is not fresh"
          (* Fixed empty-map construction only: no raw comparator descent.
             All symbolic/local payloads and later commit fields funded. *)
          val _ = R.scope_meter_charge meter 512
          val recent = [(ty,0)]
          val node = Node {owner= #owner graph,id=0}
          val anchor : source option ref = ref NONE
          val fields : entry =
            {scope=caller,ty=ty,type_id=0,term=original,
             view=Variable(RigidSource,original),raw=SOME 1,
             inclusive=SOME 1,source=anchor}
          val types = R.scope_put_graph_key meter
            (old_types,R.GraphTypeOperator(bool_name,[]),0)
          val keys = R.scope_put_graph_key meter
            (old_keys,R.GraphVariable
              (scope_id caller,kind_id RigidSource,name,0),node)
          (* FIRST-only empty roots: R admits the captured SAME meter
             before inspecting either opaque root, then constructs the
             genuine singleton pair directly. Nonempty roots refuse;
             no private quote ledger or fresh allowance is involved. *)
          val (nodes,reserved) = R.scope_singletons_from_empty meter
            (old_nodes,old_reserved,0,fields,name)
          val next_revision = !(#validation_changes graph)+1
          (* All future retained-state commit administration already paid;
             the last dynamic scope validation is BEFORE native effect. *)
          val _ = ignore (fixed_storage_context storage caller)
          val _ = if fresh () andalso
              R.scope_same_graph_key meter (old_types,!(#types paid)) andalso
              R.scope_same_graph_key meter (old_keys,!(#keys paid)) andalso
              R.same_int (old_nodes,!(#nodes graph)) andalso
              R.same_string (old_reserved,!(#reserved graph)) andalso
              List.null (Array.sub (#imports graph,bucket)) then () else
            raise ERR "first_boolean_variable" "original registry changed"
          val _ = paid_index_close graph paid first
          val _ = R.scope_meter_charge meter 1424
          val theorem = Thm.REFL original
          (* The node's representative is this exact original and private
             REFL has exactly its reflexive endpoints and empty hypothesis.
             No arbitrary supplied proof is inspected or trusted. *)
          val source : source = {node=node,original=original,bridge=theorem}
          val _ = anchor := SOME source
          val _ = #types paid := types
          val _ = #recent paid := recent
          val _ = #keys paid := keys
          val _ = #nodes graph := nodes
          val _ = #next graph := 1
          val _ = #reserved graph := reserved
          val _ = Array.update (#imports graph,bucket,[(original,scope_id
            caller,source)])
          val _ = #validation_changes graph := next_revision
        in SOME source end
    end

  (* Additive FIRST-only canonical Bool Const. Variable programme above
     stays literal. Both routes use the captured original graph and
     payer; A owns one-attempt/request/native-history authentication. *)
  fun import_first_boolean_constant storage caller
      ({original,limits}:{original:Term.term,
        limits:first_boolean_variable_limits}) =
    let
      val held = fixed_storage_context storage caller
      val graph = #graph held
      val meter = #meter held
      val paid = paid_first_indices graph meter
      val first = paid_index_snapshot graph paid
      (* Defined local validation/capture tariff, not whole CPU pricing. *)
      val _ = R.scope_meter_charge meter 128
      val allows = SmtReplayResourcePolicy.allows
      val construction = #construction_limits limits
      val semantic = #semantic_limits limits
      val native = #native_limits limits
      val ns = #semantic_limits native
      (* Exact single-original programme bounds. Existing A reflection
         cannot be counted as fresh credit; its caller admits history. *)
      val _ = if allows (#import_limit construction) 1 andalso
          allows (#literal_limit construction) 1 andalso
          allows (#input_limit semantic) 1 andalso
          allows (#output_limit semantic) 11 andalso
          allows (#template_limit semantic) 11 andalso
          allows (#input_limit ns) 1 andalso
          allows (#output_limit ns) 11 andalso
          allows (#template_limit ns) 11 andalso
          allows (#import_limit native) 5 andalso
          allows (#type_work_limit native) 1626 then () else
        raise ERR "first_boolean_constant" "original policy exhausted"
      val _ = R.scope_meter_charge meter 128
      val old_types = #types first
      val old_keys = #keys first
      val old_nodes = #nodes first
      val old_reserved = #reserved first
      fun fresh () =
        !(#validation_changes graph)=0 andalso !(#next graph)=0 andalso
        !(#next_scope graph)=1 andalso !(#scope_retirements graph)=0 andalso
        R.scope_graph_key_count meter (!(#types paid))=0 andalso
        R.scope_graph_key_count meter (!(#keys paid))=0 andalso
        List.null (!(#recent paid)) andalso
        not (Option.isSome (!(#node_observation graph))) andalso
        not (Option.isSome (!(#partial_running graph)))
      val _ = if fresh () then () else
        raise ERR "first_boolean_constant" "semantic registry is not fresh"
      val _ = if R.scope_graph_key_count meter (!(#types held))=0 andalso
          R.scope_graph_key_count meter (!(#keys held))=0 then () else
        raise ERR "first_boolean_constant" "metadata registry is not fresh"
      (* Positive Const before type_of; no arbitrary App/Abs/Clos descent. *)
      val _ = R.scope_meter_charge meter 74
    in if not (Term.is_const original) then NONE
      else if not (Portable.pointer_eq (Term.type_of original,Type.bool))
        then NONE
      else
        let
          (* Paid closed Const metadata programme: actual immutable ID,
             canonical Bool ID, epoch and exact pointer_bucket4 Const
             route. No display/name lookup or arbitrary string scan. *)
          val _ = R.scope_meter_charge meter 128
          val {Name,Ty=ty,...} = Term.dest_thy_constid original
          val bool_name = #Tyop (Type.dest_thy_typeid Type.bool)
          val hash = Word.fromInt (KernelSig.epoch_of Name)
          val bucket = Word.toInt (Word.mod
            (Word.+ (Word.* (0w37,hash),hash),Word.fromInt 4093))
          val _ = if List.null (Array.sub (#imports graph,bucket)) then ()
            else raise ERR "first_boolean_constant"
              "import bucket is not fresh"
          (* Fixed empty-map construction only: no raw comparator descent.
             All symbolic/local payloads and later commit fields funded. *)
          val _ = R.scope_meter_charge meter 512
          val recent = [(ty,0)]
          val node = Node {owner= #owner graph,id=0}
          val anchor : source option ref = ref NONE
          val fields : entry =
            {scope=caller,ty=ty,type_id=0,term=original,
             view=Constant Name,raw=SOME 1,
             inclusive=SOME 1,source=anchor}
          val types = R.scope_put_graph_key meter
            (old_types,R.GraphTypeOperator(bool_name,[]),0)
          val keys = R.scope_put_graph_key meter
            (old_keys,R.GraphConstant(Name,0),node)
          (* Only the actual empty int root is changed. R admits the
             SAME original meter before root inspection. The reserved
             string root is retained unchanged, never given a fake name. *)
          val nodes = R.scope_int_singleton_from_empty meter
            (old_nodes,0,fields)
          val next_revision = !(#validation_changes graph)+1
          (* All future retained-state commit administration already paid;
             the last dynamic scope validation is BEFORE native effect. *)
          val _ = ignore (fixed_storage_context storage caller)
          val _ = if fresh () andalso
              R.scope_same_graph_key meter (old_types,!(#types paid)) andalso
              R.scope_same_graph_key meter (old_keys,!(#keys paid)) andalso
              R.same_int (old_nodes,!(#nodes graph)) andalso
              R.same_string (old_reserved,!(#reserved graph)) andalso
              List.null (Array.sub (#imports graph,bucket)) then () else
            raise ERR "first_boolean_constant" "original registry changed"
          val _ = paid_index_close graph paid first
          val _ = R.scope_meter_charge meter 1424
          val theorem = Thm.REFL original
          (* The node's representative is this exact original and private
             REFL has exactly its reflexive endpoints and empty hypothesis.
             No arbitrary supplied proof is inspected or trusted. *)
          val source : source = {node=node,original=original,bridge=theorem}
          val _ = anchor := SOME source
          val _ = #types paid := types
          val _ = #recent paid := recent
          val _ = #keys paid := keys
          val _ = #nodes graph := nodes
          val _ = #next graph := 1
          val _ = Array.update (#imports graph,bucket,[(original,scope_id
            caller,source)])
          val _ = #validation_changes graph := next_revision
        in SOME source end
    end

  (* Owned ordered-original acquisition PREFIX only. No executor, native
     admission, Source, denial, Ready or policy credit is issued here. *)
  type original_import_usage =
    {construction_import:IntInf.int,construction_literal:IntInf.int,
     construction_binder:IntInf.int,recipe_template:IntInf.int,
     recipe_index:IntInf.int,recipe_operand:IntInf.int,
     recipe_token:IntInf.int,semantic_input:IntInf.int,
     semantic_output:IntInf.int,semantic_template:IntInf.int,
     native_input:IntInf.int,native_output:IntInf.int,
     native_template:IntInf.int,native_import:IntInf.int,
     type_work:IntInf.int}
  (* Only this executor can issue an alias receipt. Public Source keeps
     its original three fields; the receipt authenticates its actual proof. *)
  datatype ordered_alias_receipt = OrderedAliasReceipt of
    {source:source,canonical:Term.term,anchor:source}
  datatype ordered_function_child = OrderedFunctionChild of
    {source:source,canonical:Term.term,anchor:source,type_id:int}
  datatype original_import_context = OriginalImportContext of
    {storage:fixed_storage,paid:paid_index_state,
     expected:paid_index_snapshot ref,limits:first_boolean_variable_limits,
     originals:Term.term list,usage:original_import_usage ref,
     completed:IntInf.int ref,denial_complete:bool ref,
     remaining:Term.term list ref,sources:source list ref,stopped:bool ref,
     goal_witness:(source * Word.word) option ref,denial_source:source option
       ref,
     source_rows:(source * int) list ref,denial_bucket:int option ref,
     aliases:ordered_alias_receipt list ref,
     function_children:ordered_function_child list ref,
     replay_workspace:unit ref option ref}

  fun original_import_context_for storage caller
      (OriginalImportContext saved) =
    let
      val FixedStorage expected = storage
      val FixedStorage held = #storage saved
      (* Immutable EXPECTED owner/root precedes retained graph/root reads. *)
      val _ = if #owner expected= #owner held andalso
          caller= #root expected andalso caller= #root held then () else
        raise ERR "original_import_context" "different original owner"
      val current = fixed_storage_context storage caller
      val meter = #meter current
      val _ = R.scope_meter_charge meter 64
      val _ = if R.same_scope_meter (meter,#meter held) then () else
        raise ERR "original_import_context" "different original meter"
      val _ = paid_index_close (#graph current) (#paid saved)
        (!(#expected saved))
    in saved end

  fun begin_original_import_context storage caller
      ({limits,originals}:{limits:first_boolean_variable_limits,
        originals:Term.term list}) =
    let
      val held = fixed_storage_context storage caller
      val graph = #graph held
      val meter = #meter held
      val _ = R.scope_meter_charge meter 256
      val _ = if !(#original_context_claimed held) then
        raise ERR "original_import_context" "context already claimed"
        else ()
      val paid = paid_first_indices graph meter
      val first = paid_index_snapshot graph paid
      val _ = if #revision first=0 andalso #next first=0 andalso
          #next_scope first=1 andalso #retirements first=0 andalso
          R.scope_graph_key_count meter (#types first)=0 andalso
          R.scope_graph_key_count meter (#keys first)=0 andalso
          List.null (#recent first) andalso
          R.scope_graph_key_count meter (!(#types held))=0 andalso
          R.scope_graph_key_count meter (!(#keys held))=0 andalso
          not (Option.isSome (!(#node_observation graph))) andalso
          not (Option.isSome (!(#partial_running graph))) then () else
        raise ERR "original_import_context" "original registry is not fresh"
      val _ = paid_index_close graph paid first
      val _ = R.scope_meter_charge meter 64
      val usage : original_import_usage =
        {construction_import=0,construction_literal=0,
         construction_binder=0,recipe_template=0,recipe_index=0,
         recipe_operand=0,recipe_token=0,semantic_input=0,
         semantic_output=0,semantic_template=0,native_input=0,
         native_output=0,native_template=0,native_import=0,type_work=0}
      val _ = R.scope_meter_charge meter 4
      val _ = R.scope_meter_charge meter 12
      val _ = R.scope_meter_charge meter 8
      val _ = R.scope_meter_charge meter 8
      val _ = R.scope_meter_charge meter 4
      val _ = R.scope_meter_charge meter 4
      val _ = R.scope_meter_charge meter 4
      val result = OriginalImportContext
        {storage=storage,paid=paid,expected=ref first,limits=limits,
         originals=originals,usage=ref usage,completed=ref 0,
         denial_complete=ref false,remaining=ref originals,
         sources=ref [],stopped=ref false,
         goal_witness=ref NONE,denial_source=ref NONE,
         source_rows=ref [],denial_bucket=ref NONE,aliases=ref [],
         function_children=ref [],replay_workspace=ref NONE}
      (* No public setter/reset/claimant revision or quota callback exists.
         Future commits must update witnesses inside a closed executor. *)
      val _ = #original_context_claimed held := true
    in result end

  fun original_import_progress storage caller context =
    let
      val saved = original_import_context_for storage caller context
      val FixedStorage held = storage
      val _ = R.scope_meter_charge (#meter held) 32
    in {completed= !(#completed saved),usage= !(#usage saved),
      revision= #revision (!(#expected saved)),
      denial_complete= !(#denial_complete saved)} end

  datatype original_import_step = OriginalImported
    | OriginalUnsupported | OriginalInputsComplete

  (* Cumulative ADMITTED UPPER reservations, not observed event counters.
     Admit actual common classifier/descriptor202 and occurrence geometry
     first. A fresh key later admits REFL1424; a memo admits no REFL, and
     a distinct assumption alias admits its own metadata+ALPHA programme. *)
  fun reserve_ordered_boolean meter
      (limits:first_boolean_variable_limits) (used:original_import_usage) =
    let
      val _ = R.scope_meter_charge meter 256
      val next : original_import_usage =
        {construction_import= #construction_import used+1,
         construction_literal= #construction_literal used+1,
         construction_binder= #construction_binder used,
         recipe_template= #recipe_template used,
         recipe_index= #recipe_index used,recipe_operand= #recipe_operand used,
         recipe_token= #recipe_token used,
         semantic_input= #semantic_input used+1,
         semantic_output= #semantic_output used+11,
         semantic_template= #semantic_template used+11,
         native_input= #native_input used+1,
         native_output= #native_output used+11,
         native_template= #native_template used+11,
         native_import= #native_import used+5,type_work= #type_work used+202}
      val construction = #construction_limits limits
      val recipes = #recipe_limits construction
      val semantic = #semantic_limits limits
      val native = #native_limits limits
      val ns = #semantic_limits native
      val allows = SmtReplayResourcePolicy.allows
      val admitted =
        allows (#import_limit construction) (#construction_import next)
        andalso allows (#literal_limit construction)
          (#construction_literal next)
        andalso allows (#binder_limit construction)
          (#construction_binder next)
        andalso allows (#template_limit recipes) (#recipe_template next)
        andalso allows (#index_limit recipes) (#recipe_index next)
        andalso allows (#operand_limit recipes) (#recipe_operand next)
        andalso allows (#token_limit recipes) (#recipe_token next)
        andalso allows (#input_limit semantic) (#semantic_input next)
        andalso allows (#output_limit semantic) (#semantic_output next)
        andalso allows (#template_limit semantic) (#semantic_template next)
        andalso allows (#input_limit ns) (#native_input next)
        andalso allows (#output_limit ns) (#native_output next)
        andalso allows (#template_limit ns) (#native_template next)
        andalso allows (#import_limit native) (#native_import next)
        andalso allows (#type_work_limit native) (#type_work next)
    in if admitted then next else
      raise ERR "ordered_boolean_original"
        "cumulative original policy exhausted"
    end

  (* Add only actual branch-native work after the common occurrence
     geometry/metadata reservation. The other fourteen counters/limits
     are immutable and unchanged since their complete admission above.
     No caller quote, refund or old REFLEXIVITY credit is consulted. *)
  fun reserve_ordered_extra_native meter
      (limits:first_boolean_variable_limits) (used:original_import_usage)
      amount =
    let
      val _ = R.scope_meter_charge meter 96
      val native = #native_limits limits
      val next_type = #type_work used+amount
      val _ = if amount>=0 andalso
          SmtReplayResourcePolicy.allows (#type_work_limit native) next_type
        then () else raise ERR "ordered_boolean_original"
          "cumulative original policy exhausted"
    in {construction_import= #construction_import used,
        construction_literal= #construction_literal used,
        construction_binder= #construction_binder used,
        recipe_template= #recipe_template used,
        recipe_index= #recipe_index used,recipe_operand= #recipe_operand used,
        recipe_token= #recipe_token used,
        semantic_input= #semantic_input used,
        semantic_output= #semantic_output used,
        semantic_template= #semantic_template used,
        native_input= #native_input used,native_output= #native_output used,
        native_template= #native_template used,
        native_import= #native_import used,type_work=next_type}
      : original_import_usage end

  (* Private immediate-Type observer. This is structural metadata, not
     authority to run native equality over an arbitrary Type forest. Only
     the separately checked sealed nullary Bool root becomes a Source.
     Every new pointer cell pays native128 before its public observation;
     all native-free pointer/key/list/cache programmes use this SAME meter. *)
  fun observe_ordered_native_type storage caller context actual_type =
    let
      val saved = original_import_context_for storage caller context
      val FixedStorage held = storage
      val graph = #graph held
      val meter = #meter held
      val paid = #paid saved
      val _ = R.scope_meter_charge meter 128
      fun cached ty rows =
        (R.scope_meter_charge meter 32;
         case rows of [] => NONE
         | (prior,id)::rest =>
             if Portable.pointer_eq(ty,prior) then SOME id
             else cached ty rest)
      fun reverse ids acc =
        (R.scope_meter_charge meter 16;
         case ids of [] => acc
         | id::rest => (R.scope_meter_charge meter 16;
             reverse rest (id::acc)))
      fun walk ty =
        let
          val _ = R.scope_meter_charge meter 64
          val current = !(#expected saved)
        in case cached ty (#recent current) of
            SOME id => id
          | NONE =>
            let
              val admitted = reserve_ordered_extra_native meter
                (#limits saved) (!(#usage saved)) 128
              val _ = R.scope_meter_charge meter 16
              val _ = #usage saved := admitted
              val _ = R.scope_meter_charge meter 128
              (* No recursive native observer: these public destructors
                 return immediate payloads only. Native child visits below
                 are individually admitted before their own observations. *)
              val key = if Type.is_vartype ty then
                  R.GraphTypeVariable(Type.dest_vartype ty)
                else
                  let
                    val {Tyop,Args,...} = Type.dest_thy_typeid ty
                    fun children pending ids =
                      (R.scope_meter_charge meter 32;
                       case pending of [] => reverse ids []
                       | child::rest =>
                           (R.scope_meter_charge meter 32;
                            children rest (walk child::ids)))
                    val ids = children Args []
                  in R.GraphTypeOperator(Tyop,ids) end
              (* A child may legitimately have published its OWN completed
                 Type/cache prefix. Use its authentic current witness;
                 never reinstate/adopt the pre-child revision or roots. *)
              val first = !(#expected saved)
              val (types,id) =
                case R.scope_lookup_graph_key meter (#types first,key) of
                    SOME id => (#types first,id)
                  | NONE =>
                      let val id = R.scope_graph_key_count meter (#types first)
                      in (R.scope_put_graph_key meter (#types first,key,id),id)
                      end
              val _ = R.scope_meter_charge meter 192
              val recent = (ty,id):: #recent first
              val revision = #revision first+1
              val next_snapshot : paid_index_snapshot =
                {types=types,keys= #keys first,recent=recent,
                 nodes= #nodes first,scopes= #scopes first,
                 reserved= #reserved first,next= #next first,
                 next_scope= #next_scope first,retirements= #retirements first,
                 revision=revision}
              val _ = paid_index_close graph paid first
              (* No callback/native operation/debit between these own
                 persistent cache/root stores and the expected witness. *)
              val _ = #types paid := types
              val _ = #recent paid := recent
              val _ = #validation_changes graph := revision
              val _ = #expected saved := next_snapshot
            in id end
        end
    in walk actual_type end

  fun ordered_semantic_Bool_type storage caller context actual_type bool_name =
    let
      val id = observe_ordered_native_type storage caller context actual_type
      val saved = original_import_context_for storage caller context
      val FixedStorage held = storage
      val meter = #meter held
      val _ = R.scope_meter_charge meter 32
      val first = !(#expected saved)
    in case R.scope_lookup_graph_key meter
          (#types first,R.GraphTypeOperator(bool_name,[])) of
          SOME 0 => id=0
        | _ => false
    end

  fun advance_original_boolean_leaf storage caller context =
    let
      val saved = original_import_context_for storage caller context
      val FixedStorage held = storage
      val graph = #graph held
      val meter = #meter held
      val paid = #paid saved
      val _ = R.scope_meter_charge meter 128
      val _ = if !(#stopped saved) then
        raise ERR "ordered_boolean_original"
          "unsupported original already encountered"
        else ()
      fun unsupported () =
        (R.scope_meter_charge meter 16;
         #stopped saved := true;OriginalUnsupported)
      fun owned (candidate:source) rows =
        (R.scope_meter_charge meter 32;
         case rows of [] => false
         | (item:source)::rest =>
             (#node item= #node candidate andalso
              Portable.pointer_eq (#original item,#original candidate)
              andalso Portable.pointer_eq (#bridge item,#bridge candidate))
             orelse owned candidate rest)
      fun memo original rows =
        (R.scope_meter_charge meter 32;
         case rows of [] => NONE
         | (term,scope,source)::rest =>
             if scope=scope_id caller andalso
                 Portable.pointer_eq(term,original) then SOME source
             else memo original rest)
      fun finish source tail head_hash bucket =
        (if !(#completed saved)=0 then
           #goal_witness saved := SOME(source,head_hash) else ();
         #source_rows saved := (source,bucket):: !(#source_rows saved);
         #sources saved := source :: !(#sources saved);
         #remaining saved := tail;
         #completed saved := !(#completed saved)+1;
         OriginalImported)
      val _ = R.scope_meter_charge meter 4
      (* A key hit is not a pointer-memo hit. Only a later captured
         assumption may acquire its own paid raw-to-canonical bridge. *)
      fun alias node original tail key view name bucket head_hash
          (first:paid_index_snapshot)
          old_bucket =
        let
          val _ = R.scope_meter_charge meter 256
          val Node {owner,id} = node
          val _ = if owner= #owner graph then () else
            raise ERR "ordered_boolean_alias" "different semantic node owner"
          val fields = case R.scope_lookup_int meter (#nodes first,id) of
              SOME fields => fields
            | NONE => raise ERR "ordered_boolean_alias" "missing semantic node"
          val canonical = #term fields
          val _ = if #scope fields=caller andalso #type_id fields=0 then ()
            else
            raise ERR "ordered_boolean_alias" "different semantic Bool node"
          val _ = if Portable.pointer_eq(original,canonical) then
            raise ERR "ordered_boolean_alias" "missing canonical pointer memo"
            else ()
          val anchor = case !(#source fields) of SOME source => source
            | NONE => raise ERR "ordered_boolean_alias"
              "missing first Source anchor"
          val _ = if #node anchor=node andalso
              Portable.pointer_eq(#original anchor,canonical) andalso
              owned anchor (!(#sources saved)) then () else
            raise ERR "ordered_boolean_alias" "foreign first Source anchor"
          fun admit amount =
            let
              val admitted = reserve_ordered_extra_native meter
                (#limits saved) (!(#usage saved)) amount
              val _ = R.scope_meter_charge meter 16
              val _ = #usage saved := admitted
            in R.scope_meter_charge meter amount end
          (* Canonical atom observations and authentic D extraction are
             independently admitted BEFORE their native effects. Raw atom
             descriptors below are the immutable, already paid tuple. *)
          val _ = admit 256
          fun bytes text = IntInf.fromInt(String.size text)
          val (byte_mass,canonical_key,stored_key) =
            case (view,#view fields,name) of
              (Variable(RigidSource,_),Variable(RigidSource,held),SOME raw) =>
                if Term.is_var canonical andalso
                    Portable.pointer_eq(Term.type_of canonical,#ty fields)
                    andalso Portable.pointer_eq(held,canonical) then
                  let val (text,_) = Term.dest_var canonical
                      val held_key = R.GraphVariable
                        (scope_id caller,kind_id RigidSource,text,0)
                  in (bytes raw+bytes text,held_key,held_key) end
                else raise ERR "ordered_boolean_alias"
                  "different canonical variable"
            | (Constant raw_id,Constant stored_id,NONE) =>
                if Term.is_const canonical andalso
                    Portable.pointer_eq(Term.type_of canonical,#ty fields) then
                  let
                    val {Name=canonical_id,...} = Term.dest_thy_constid
                      canonical
                    val {Thy=raw_thy,Name=raw_name} = KernelSig.name_of_id
                      raw_id
                    val {Thy=held_thy,Name=held_name} =
                      KernelSig.name_of_id canonical_id
                  in (bytes raw_thy+bytes raw_name+
                        bytes held_thy+bytes held_name,
                      R.GraphConstant(canonical_id,0),
                      R.GraphConstant(stored_id,0)) end
                else raise ERR "ordered_boolean_alias"
                  "different canonical constant"
            | _ => raise ERR "ordered_boolean_alias"
              "different canonical atom kind"
          (* The fixed R programme pays each actual name/UID comparison;
             no unpriced SML string/UID equality establishes this key. *)
          val _ = if R.scope_compare_graph_key meter (key,canonical_key)=EQUAL
              andalso R.scope_compare_graph_key meter (key,stored_key)=EQUAL
            then () else raise ERR "ordered_boolean_alias"
              "different semantic atom key"
          val alpha_upper : IntInf.int = 2437+32*(byte_mass+1)
          (* Includes the separately proved fixed bridge endpoint/tag/Hyp
             check256. Neither old1424 nor an unused reservation is credit. *)
          val _ = admit (alpha_upper+256)
          val _ = R.scope_meter_charge meter 384
          val next_revision = #revision first+1
          val next_snapshot : paid_index_snapshot =
            {types= #types first,keys= #keys first,recent= #recent first,
             nodes= #nodes first,scopes= #scopes first,
             reserved= #reserved first,next= #next first,
             next_scope= #next_scope first,retirements= #retirements first,
             revision=next_revision}
          (* Retained finish tariff pays the actual occurrence/list stores.
             All paid lookup, policy, closing and staging precedes ALPHA. *)
          val _ = R.scope_meter_charge meter 144
          val _ = paid_index_close graph paid first
          val _ = if Portable.pointer_eq
              (old_bucket,Array.sub(#imports graph,bucket)) then () else
            raise ERR "ordered_boolean_alias" "import bucket changed"
          val theorem = Thm.ALPHA original canonical
          val (left,right) = Term.dest_eq(Thm.concl theorem)
          val tag = Thm.tag theorem
          val _ = if Portable.pointer_eq(left,original) andalso
              Portable.pointer_eq(right,canonical) andalso
              HOLset.numItems(Thm.hypset theorem)=0 andalso
              Tag.isEmpty tag then () else
            raise ERR "ordered_boolean_alias"
              "different native bridge endpoints"
          val source : source =
            {node=node,original=original,bridge=theorem}
          val receipt = OrderedAliasReceipt
            {source=source,canonical=canonical,anchor=anchor}
          (* No debit/callback/recursive traversal after ALPHA. Only prepaid
             fixed observations above, then these OWN immutable stores.
             First anchor and all semantic node/key/type roots stay put. *)
          val _ = #aliases saved := receipt :: !(#aliases saved)
          val _ = Array.update(#imports graph,bucket,
            (original,scope_id caller,source)::old_bucket)
          val _ = #validation_changes graph := next_revision
          val _ = #expected saved := next_snapshot
        in finish source tail head_hash bucket end
    in case !(#remaining saved) of
        [] => OriginalInputsComplete
      | original::tail =>
        let
          (* No Term discriminator/type/native operation precedes admission.
             Quota reservations are monotone even on later refusal. *)
          val admitted = reserve_ordered_boolean meter (#limits saved)
            (!(#usage saved))
          val _ = R.scope_meter_charge meter 16
          val _ = #usage saved := admitted
          val _ = R.scope_meter_charge meter 74
          val is_variable = Term.is_var original
          val is_constant = if is_variable then false
            else Term.is_const original
        in if not (is_variable orelse is_constant) then unsupported ()
          else
            let
              val actual_type = Term.type_of original
              (* Preserve the actual pointer-Bool shortcut. The raw
                 descriptor invoice is moved before its ONE shared Bool
                 UID getter, not charged twice or treated as old credit. *)
              val _ = R.scope_meter_charge meter
                (if is_variable then 64 else 128)
              val bool_name = #Tyop(Type.dest_thy_typeid Type.bool)
              val boolean = Portable.pointer_eq(actual_type,Type.bool)
                orelse ordered_semantic_Bool_type storage caller context
                  actual_type bool_name
            in if not boolean then unsupported () else
            let
              (* Actual closed raw descriptor/hash route. The same Bool
                 UID above is reused; no generic native Type comparison. *)
              val (ty,bool_name,key,view,name,bucket,head_hash) =
                if is_variable then
                  let
                    val (name,ty) = Term.dest_var original
                    val _ = R.scope_meter_charge meter 32
                    val length = String.size name
                    fun hash i value =
                      (R.scope_meter_charge meter 8;
                       if i=length then value else
                         (R.scope_meter_charge meter 16;
                          hash (i+1) (Word.+ (Word.*(value,0w33),
                            Word.fromInt(Char.ord(String.sub(name,i)))))))
                    val value = hash 0 0w17
                    val _ = R.scope_meter_charge meter 32
                    val bucket = Word.toInt(Word.mod
                      (Word.+(Word.*(0w37,value),value),Word.fromInt 4093))
                  in (ty,bool_name,R.GraphVariable
                    (scope_id caller,kind_id RigidSource,name,0),
                    Variable(RigidSource,original),SOME name,bucket,value) end
                else
                  let
                    val {Name,Ty=ty,...} = Term.dest_thy_constid original
                    val value = Word.fromInt(KernelSig.epoch_of Name)
                    val bucket = Word.toInt(Word.mod
                      (Word.+(Word.*(0w37,value),value),Word.fromInt 4093))
                  in (ty,bool_name,R.GraphConstant(Name,0),
                    Constant Name,NONE,bucket,value) end
              val _ = R.scope_meter_charge meter 128
              val _ = if Portable.pointer_eq(ty,actual_type) then () else
                raise ERR "ordered_boolean_original"
                  "different observed native Type"
              val first = !(#expected saved)
              val old_bucket = Array.sub(#imports graph,bucket)
              val cached = memo original old_bucket
            in case cached of
                SOME source =>
                  if owned source (!(#sources saved)) then
                    (paid_index_close graph paid first;
                     R.scope_meter_charge meter 144;finish source tail
                       head_hash bucket)
                  else raise ERR "ordered_boolean_original"
                    "foreign cached Source"
              | NONE =>
                (case R.scope_lookup_graph_key meter (#keys first,key) of
                    SOME node =>
                      if !(#completed saved)=0 then unsupported () else
                        alias node original tail key view name bucket
                          head_hash first old_bucket
                  | NONE =>
                    let
                      (* Prospective branch admission, never a refund of
                         previously billed or unexecuted native work. *)
                      val branch = reserve_ordered_extra_native meter
                        (#limits saved) (!(#usage saved)) 1424
                      val _ = R.scope_meter_charge meter 16
                      val _ = #usage saved := branch
                      val _ = R.scope_meter_charge meter 512
                      val (types,recent) =
                        case R.scope_lookup_graph_key meter
                            (#types first,R.GraphTypeOperator(bool_name,[])) of
                            SOME 0 => (#types first,#recent first)
                          | SOME _ => raise ERR "ordered_boolean_original"
                              "different semantic Bool type id"
                          | NONE =>
                              if R.scope_graph_key_count meter (#types first)=0
                                then (R.scope_put_graph_key meter
                                  (#types
                                    first,R.GraphTypeOperator(bool_name,[]),0),
                                  [(ty,0)])
                              else raise ERR "ordered_boolean_original"
                                "unexpected semantic type registry"
                      val id = #next first
                      val node = Node {owner= #owner graph,id=id}
                      val anchor : source option ref = ref NONE
                      val fields : entry =
                        {scope=caller,ty=ty,type_id=0,term=original,
                         view=view,raw=SOME 1,inclusive=SOME 1,source=anchor}
                      val keys = R.scope_put_graph_key meter
                        (#keys first,key,node)
                      val nodes = R.scope_put_int meter
                        (#nodes first,id,fields)
                      val reserved = case name of NONE => #reserved first
                        | SOME text => R.scope_add_string meter
                            (#reserved first,text)
                      val next_revision = #revision first+1
                      val next_snapshot : paid_index_snapshot =
                        {types=types,keys=keys,recent=recent,nodes=nodes,
                         scopes= #scopes first,reserved=reserved,next=id+1,
                         next_scope= #next_scope first,
                         retirements= #retirements first,
                         revision=next_revision}
                      (* Stage all persistent roots and fund commit BEFORE
                         native effect. Refusal preserves real Work prefix;
                         no semantic root or Source has been published. *)
                      val _ = R.scope_meter_charge meter 128
                      val _ = paid_index_close graph paid first
                      val _ = if Portable.pointer_eq
                          (old_bucket,Array.sub(#imports graph,bucket))
                        then () else raise ERR "ordered_boolean_original"
                          "import bucket changed"
                      val _ = R.scope_meter_charge meter 144
                      val _ = R.scope_meter_charge meter 1424
                      val theorem = Thm.REFL original
                      val source : source =
                        {node=node,original=original,bridge=theorem}
                      (* No callback/native observation between these
                         funded stores. Witness changes only with OWN
                         authentic semantic commit, never caller revision. *)
                      val _ = anchor := SOME source
                      val _ = #types paid := types
                      val _ = #recent paid := recent
                      val _ = #keys paid := keys
                      val _ = #nodes graph := nodes
                      val _ = #next graph := id+1
                      val _ = #reserved graph := reserved
                      val _ = Array.update(#imports graph,bucket,
                        (original,scope_id caller,source)::old_bucket)
                      val _ = #validation_changes graph := next_revision
                      val _ = #expected saved := next_snapshot
                    in finish source tail head_hash bucket end)
            end
            end
        end
    end

  (* A typed child is not an admitted Boolean original occurrence. These
     receipts remain private until a genuine owning App programme uses
     them. In particular this port never pops remaining or increments
     completed, and cannot publish a hypothesis/Ready payload. *)
  fun prepare_original_function_child storage caller context =
    let
      val saved = original_import_context_for storage caller context
      val FixedStorage held = storage
      val graph = #graph held
      val paid = #paid saved
      val meter = #meter held
      val _ = R.scope_meter_charge meter 192
      val _ = if !(#stopped saved) orelse !(#denial_complete saved) then
        raise ERR "ordered_function_child" "original programme is closed"
        else ()
      val original = case !(#remaining saved) of item::_ => item
        | [] => raise ERR "ordered_function_child" "no current original"
      fun issued (candidate:source) rows =
        (R.scope_meter_charge meter 32;
         case rows of [] => false
         | OrderedFunctionChild {source,...}::rest =>
             (#node source= #node candidate andalso
              Portable.pointer_eq(#original source,#original candidate)
              andalso Portable.pointer_eq(#bridge source,#bridge candidate))
             orelse issued candidate rest)
      fun already rows =
        (R.scope_meter_charge meter 32;
         case rows of [] => false
         | OrderedFunctionChild {source,...}::rest =>
             Portable.pointer_eq(#original source,original)
             orelse already rest)
      fun memo rows =
        (R.scope_meter_charge meter 32;
         case rows of [] => NONE
         | (term,frame,source)::rest =>
             if frame=scope_id caller andalso
                 Portable.pointer_eq(term,original) then SOME source
             else memo rest)
      fun admit amount =
        let val usage = reserve_ordered_extra_native meter
              (#limits saved) (!(#usage saved)) amount
            val _ = R.scope_meter_charge meter 16
            val _ = #usage saved := usage
        in R.scope_meter_charge meter amount end
    in if already (!(#function_children saved)) then () else
      let
        (* The same authentic fifteen counters are monotone. A failed
           classifier/type observation retains its actual paid prefix. *)
        val usage = reserve_ordered_boolean meter (#limits saved)
          (!(#usage saved))
        val _ = R.scope_meter_charge meter 16
        val _ = #usage saved := usage
        val _ = R.scope_meter_charge meter 74
        val is_variable = Term.is_var original
        val is_constant = if is_variable then false
          else Term.is_const original
        val _ = if is_variable orelse is_constant then () else
          raise ERR "ordered_function_child" "current original is not an atom"
        val actual_type = Term.type_of original
        val observed = observe_ordered_native_type storage caller context
          actual_type
        (* Fixed metadata512 is admitted independently of both the Type
           forest's actual per-cell128 and the later proof programme.
           The trusted builtin supplies the complete function UID; its
           two actual leaves are verified semantically, never by pointer. *)
        val _ = admit 512
        val {Ty=negation_type,...} =
          Term.dest_thy_constid boolSyntax.negation
        val bool_name = #Tyop(Type.dest_thy_typeid Type.bool)
        val {Tyop=fun_name,Args,...} =
          Type.dest_thy_typeid negation_type
        fun boolean_leaf ty =
          if Type.is_vartype ty then false else
            let val {Tyop,Args,...} = Type.dest_thy_typeid ty
                val {Thy,Name} = KernelSig.name_of_id Tyop
            in case Args of [] =>
                String.size Thy=3 andalso String.size Name=4 andalso
                Tyop=bool_name
              | _ => false end
        val _ = case Args of [domain,range] =>
            if boolean_leaf domain andalso boolean_leaf range then () else
              raise ERR "ordered_function_child" "different builtin function"
          | _ => raise ERR "ordered_function_child"
            "different builtin function"
        val _ = R.scope_meter_charge meter 96
        val typed_snapshot = !(#expected saved)
        val bool_id = case R.scope_lookup_graph_key meter
            (#types typed_snapshot,R.GraphTypeOperator(bool_name,[])) of
            SOME id => id
          | NONE => raise ERR "ordered_function_child" "missing observed Bool"
        val type_id = case R.scope_lookup_graph_key meter
            (#types typed_snapshot,
             R.GraphTypeOperator(fun_name,[bool_id,bool_id])) of
            SOME id => if id=observed then id else
              raise ERR "ordered_function_child" "different observed function"
          | NONE => raise ERR "ordered_function_child"
            "different observed function"
        (* Actual raw descriptor and name hashing are distinct from the
           separately priced native equality/REFL/ALPHA calls below. *)
        val _ = R.scope_meter_charge meter
          (if is_variable then 64 else 128)
        val (ty,key,view,name,bucket) = if is_variable then
            let
              val (text,ty) = Term.dest_var original
              val _ = R.scope_meter_charge meter 32
              val length = String.size text
              fun hash i value =
                (R.scope_meter_charge meter 8;
                 if i=length then value else
                   (R.scope_meter_charge meter 16;
                    hash (i+1) (Word.+(Word.*(value,0w33),
                      Word.fromInt(Char.ord(String.sub(text,i)))))))
              val value = hash 0 0w17
              val _ = R.scope_meter_charge meter 32
              val bucket = Word.toInt(Word.mod
                (Word.+(Word.*(0w37,value),value),Word.fromInt 4093))
            in (ty,R.GraphVariable
                (scope_id caller,kind_id RigidSource,text,type_id),
                Variable(RigidSource,original),SOME text,bucket) end
          else
            let val {Name,Ty=ty,...} = Term.dest_thy_constid original
                val value = Word.fromInt(KernelSig.epoch_of Name)
                val bucket = Word.toInt(Word.mod
                  (Word.+(Word.*(0w37,value),value),Word.fromInt 4093))
            in (ty,R.GraphConstant(Name,type_id),Constant Name,NONE,bucket) end
        val _ = R.scope_meter_charge meter 128
        val _ = if Portable.pointer_eq(ty,actual_type) then () else
          raise ERR "ordered_function_child" "different observed native Type"
        val first = !(#expected saved)
        val old_bucket = Array.sub(#imports graph,bucket)
      in case memo old_bucket of SOME source =>
          if issued source (!(#function_children saved)) then () else
            raise ERR "ordered_function_child" "foreign cached child Source"
        | NONE =>
          (case R.scope_lookup_graph_key meter (#keys first,key) of
              NONE =>
                let
                  (* Fresh typed atom REFL1668: the equality template
                     still has five input nodes; instantiated polymorphic
                     scan now has nine nodes and seventeen list cases. *)
                  val branch = reserve_ordered_extra_native meter
                    (#limits saved) (!(#usage saved)) 1668
                  val _ = R.scope_meter_charge meter 16
                  val _ = #usage saved := branch
                  val _ = R.scope_meter_charge meter 640
                  val id = #next first
                  val node = Node {owner= #owner graph,id=id}
                  val anchor : source option ref = ref NONE
                  val fields : entry =
                    {scope=caller,ty=ty,type_id=type_id,term=original,
                     view=view,raw=SOME 1,inclusive=SOME 1,source=anchor}
                  val keys = R.scope_put_graph_key meter (#keys first,key,node)
                  val nodes = R.scope_put_int meter (#nodes first,id,fields)
                  val reserved = case name of NONE => #reserved first
                    | SOME text => R.scope_add_string meter (#reserved
                      first,text)
                  val revision = #revision first+1
                  val next : paid_index_snapshot =
                    {types= #types first,keys=keys,recent= #recent first,
                     nodes=nodes,scopes= #scopes first,reserved=reserved,
                     next=id+1,next_scope= #next_scope first,
                     retirements= #retirements first,revision=revision}
                  val _ = R.scope_meter_charge meter 256
                  val _ = paid_index_close graph paid first
                  val _ = if Portable.pointer_eq
                      (old_bucket,Array.sub(#imports graph,bucket)) then ()
                        else
                    raise ERR "ordered_function_child" "import bucket changed"
                  val _ = R.scope_meter_charge meter 1668
                  val theorem = Thm.REFL original
                  val source : source =
                    {node=node,original=original,bridge=theorem}
                  val receipt = OrderedFunctionChild
                    {source=source,canonical=original,anchor=source,
                     type_id=type_id}
                  (* All root/list/receipt stores were funded before REFL.
                     No native/debit/callback occurs inside own publication. *)
                  val _ = anchor := SOME source
                  val _ = #keys paid := keys
                  val _ = #nodes graph := nodes
                  val _ = #next graph := id+1
                  val _ = #reserved graph := reserved
                  val _ = Array.update(#imports graph,bucket,
                    (original,scope_id caller,source)::old_bucket)
                  val _ = #validation_changes graph := revision
                  val _ = #expected saved := next
                  val _ = #function_children saved :=
                    receipt :: !(#function_children saved)
                in () end
            | SOME node =>
                let
                  val _ = R.scope_meter_charge meter 256
                  val Node {owner,id} = node
                  val _ = if owner= #owner graph then () else
                    raise ERR "ordered_function_child" "different node owner"
                  val fields = case R.scope_lookup_int meter (#nodes first,id)
                    of
                      SOME fields => fields
                    | NONE => raise ERR "ordered_function_child" "missing node"
                  val canonical = #term fields
                  val _ = if #scope fields=caller andalso
                      #type_id fields=type_id then () else
                    raise ERR "ordered_function_child" "different typed node"
                  val anchor = case !(#source fields) of SOME source => source
                    | NONE => raise ERR "ordered_function_child"
                      "missing anchor"
                  val _ = if #node anchor=node andalso
                      Portable.pointer_eq(#original anchor,canonical) andalso
                      issued anchor (!(#function_children saved)) then () else
                    raise ERR "ordered_function_child" "foreign typed anchor"
                  val _ = admit 256
                  fun bytes text = IntInf.fromInt(String.size text)
                  val (mass,canonical_key,stored_key) =
                    case (view,#view fields,name) of
                      (Variable(RigidSource,_),
                       Variable(RigidSource,retained),SOME raw) =>
                        if Term.is_var canonical andalso
                            Portable.pointer_eq(retained,canonical) andalso
                            Portable.pointer_eq
                              (Term.type_of canonical,#ty fields) then
                          let val (text,_) = Term.dest_var canonical
                              val k = R.GraphVariable
                                (scope_id caller,kind_id
                                  RigidSource,text,type_id)
                          in (bytes raw+bytes text,k,k) end
                        else raise ERR "ordered_function_child"
                          "different variable"
                    | (Constant raw_id,Constant stored_id,NONE) =>
                        if Term.is_const canonical andalso
                            Portable.pointer_eq
                              (Term.type_of canonical,#ty fields) then
                          let val {Name=canonical_id,...} =
                                Term.dest_thy_constid canonical
                              val {Thy=a,Name=b} = KernelSig.name_of_id raw_id
                              val {Thy=c,Name=d} =
                                KernelSig.name_of_id canonical_id
                          in (bytes a+bytes b+bytes c+bytes d,
                              R.GraphConstant(canonical_id,type_id),
                              R.GraphConstant(stored_id,type_id)) end
                        else raise ERR "ordered_function_child"
                          "different constant"
                    | _ => raise ERR "ordered_function_child"
                      "different atom kind"
                  val _ = if R.scope_compare_graph_key meter
                        (key,canonical_key)=EQUAL andalso
                      R.scope_compare_graph_key meter (key,stored_key)=EQUAL
                    then () else
                      raise ERR "ordered_function_child"
                        "different semantic key"
                  val alpha : IntInf.int = 3801+32*(mass+1)
                  val _ = admit (alpha+256)
                  val _ = R.scope_meter_charge meter 640
                  val revision = #revision first+1
                  val next : paid_index_snapshot =
                    {types= #types first,keys= #keys first,recent= #recent
                      first,
                     nodes= #nodes first,scopes= #scopes first,
                     reserved= #reserved first,next= #next first,
                     next_scope= #next_scope first,
                     retirements= #retirements first,revision=revision}
                  val _ = paid_index_close graph paid first
                  val _ = if Portable.pointer_eq
                      (old_bucket,Array.sub(#imports graph,bucket)) then ()
                        else
                    raise ERR "ordered_function_child" "import bucket changed"
                  val theorem = Thm.ALPHA original canonical
                  val (left,right) = Term.dest_eq(Thm.concl theorem)
                  val _ = if Portable.pointer_eq(left,original) andalso
                      Portable.pointer_eq(right,canonical) andalso
                      HOLset.numItems(Thm.hypset theorem)=0 andalso
                      Tag.isEmpty(Thm.tag theorem) then () else
                    raise ERR "ordered_function_child"
                      "different bridge endpoints"
                  val source : source =
                    {node=node,original=original,bridge=theorem}
                  val receipt = OrderedFunctionChild
                    {source=source,canonical=canonical,anchor=anchor,
                     type_id=type_id}
                  val _ = Array.update(#imports graph,bucket,
                    (original,scope_id caller,source)::old_bucket)
                  val _ = #validation_changes graph := revision
                  val _ = #expected saved := next
                  val _ = #function_children saved :=
                    receipt :: !(#function_children saved)
                in () end)
      end
    end

  fun reserve_ordered_boolean_denial meter
      (limits:first_boolean_variable_limits) (used:original_import_usage) =
    let
      val _ = R.scope_meter_charge meter 256
      val next : original_import_usage =
        {construction_import= #construction_import used+3,
         construction_literal= #construction_literal used+2,
         construction_binder= #construction_binder used,
         recipe_template= #recipe_template used,
         recipe_index= #recipe_index used,recipe_operand= #recipe_operand used,
         recipe_token= #recipe_token used,
         semantic_input= #semantic_input used+3,
         semantic_output= #semantic_output used+19,
         semantic_template= #semantic_template used+19,
         native_input= #native_input used+3,
         native_output= #native_output used+19,
         native_template= #native_template used+19,
         native_import= #native_import used+9,type_work= #type_work used+2400}
      val construction = #construction_limits limits
      val recipes = #recipe_limits construction
      val semantic = #semantic_limits limits
      val native = #native_limits limits
      val ns = #semantic_limits native
      val allows = SmtReplayResourcePolicy.allows
      val admitted =
        allows (#import_limit construction) (#construction_import next)
        andalso allows (#literal_limit construction)
          (#construction_literal next)
        andalso allows (#binder_limit construction)
          (#construction_binder next)
        andalso allows (#template_limit recipes) (#recipe_template next)
        andalso allows (#index_limit recipes) (#recipe_index next)
        andalso allows (#operand_limit recipes) (#recipe_operand next)
        andalso allows (#token_limit recipes) (#recipe_token next)
        andalso allows (#input_limit semantic) (#semantic_input next)
        andalso allows (#output_limit semantic) (#semantic_output next)
        andalso allows (#template_limit semantic) (#semantic_template next)
        andalso allows (#input_limit ns) (#native_input next)
        andalso allows (#output_limit ns) (#native_output next)
        andalso allows (#template_limit ns) (#native_template next)
        andalso allows (#import_limit native) (#native_import next)
        andalso allows (#type_work_limit native) (#type_work next)
    in if admitted then next else
      raise ERR "ordered_boolean_denial" "cumulative original policy exhausted"
    end

  (* Constructor-owned denial of the exact previously issued atomic goal.
     No raw goal/proof/hash/profile argument or arbitrary App admission. *)
  fun complete_original_boolean_denial storage caller context =
    let
      val saved = original_import_context_for storage caller context
      val FixedStorage held = storage
      val graph = #graph held
      val meter = #meter held
      val paid = #paid saved
      val _ = R.scope_meter_charge meter 256
      val _ = if !(#stopped saved) then
        raise ERR "ordered_boolean_denial" "unsupported original encountered"
        else ()
      val _ = case !(#remaining saved) of [] => () | _ =>
        raise ERR "ordered_boolean_denial" "original occurrences remain"
      val _ = if !(#denial_complete saved) then
        raise ERR "ordered_boolean_denial" "denial already completed"
        else ()
      val (goal,goal_hash) = case !(#goal_witness saved) of
          SOME witness => witness
        | NONE => raise ERR "ordered_boolean_denial" "missing original goal"
      fun issued rows =
        (R.scope_meter_charge meter 32;
         case rows of [] => false
         | (source:source)::rest =>
             (#node source= #node goal andalso
              Portable.pointer_eq(#original source,#original goal) andalso
              Portable.pointer_eq(#bridge source,#bridge goal))
             orelse issued rest)
      val _ = if issued (!(#sources saved)) then () else
        raise ERR "ordered_boolean_denial" "goal Source was not issued here"
      val admitted = reserve_ordered_boolean_denial meter (#limits saved)
        (!(#usage saved))
      val _ = R.scope_meter_charge meter 16
      val _ = #usage saved := admitted
      (* Fixed native programme2400 = metadata476 + constructor396 +
         private application REFL1528. All is admitted before FIRST native
         metadata/constructor effect, never borrowed from later quota. *)
      val _ = R.scope_meter_charge meter 2400
      val negation = boolSyntax.negation
      val {Name=neg_id,Ty=neg_ty,...} = Term.dest_thy_constid negation
      val bool_name = #Tyop(Type.dest_thy_typeid Type.bool)
      val {Tyop=fun_name,Args,...} = Type.dest_thy_typeid neg_ty
      (* Physical Type sharing is not semantic Bool evidence. Only this
         fixed, constructor-owned three-node function shape is admitted:
         two actual nullary leaves with the COMPLETE canonical Bool UID.
         Fixed name lengths bound equality of immutable KernelSig fields;
         epoch identity is still checked, never textual name alone. *)
      fun boolean_leaf ty =
        if Type.is_vartype ty then false else
          let
            val {Tyop,Args,...} = Type.dest_thy_typeid ty
            val {Thy,Name} = KernelSig.name_of_id Tyop
          in case Args of [] =>
              String.size Thy=3 andalso String.size Name=4 andalso
              Tyop=bool_name
            | _ => false end
      val _ = case Args of [domain,range] =>
          if boolean_leaf domain andalso boolean_leaf range then () else
            raise ERR "ordered_boolean_denial" "different negation type"
        | _ => raise ERR "ordered_boolean_denial" "different negation type"
      val denial_term = Term.mk_comb(negation,#original goal)
      val not_hash = Word.fromInt(KernelSig.epoch_of neg_id)
      val prefix = Word.+(Word.*(not_hash,0w37),0w29)
      val code = Word.+(prefix,Word.*(0w17,goal_hash))
      val bucket = Word.toInt(Word.mod
        (Word.+(Word.*(0w37,code),code),Word.fromInt 4093))
      (* The constructor result now exists locally but is unescaped. All
         R staging and closing below is paid separately. A later Limit
         preserves that real prefix and retires A; no rollback is claimed. *)
      val _ = R.scope_meter_charge meter 768
      val first = !(#expected saved)
      val old_bucket = Array.sub(#imports graph,bucket)
      val bool_id = case R.scope_lookup_graph_key meter
          (#types first,R.GraphTypeOperator(bool_name,[])) of
          SOME 0 => 0
        | _ => raise ERR "ordered_boolean_denial" "different semantic Bool id"
      val fun_id = R.scope_graph_key_count meter (#types first)
      val _ = if fun_id=1 then () else
        raise ERR "ordered_boolean_denial" "unexpected semantic type registry"
      val fun_key = R.GraphTypeOperator(fun_name,[bool_id,bool_id])
      val _ = case R.scope_lookup_graph_key meter (#types first,fun_key) of
          NONE => ()
        | SOME _ => raise ERR "ordered_boolean_denial"
          "function type already present"
      val not_key = R.GraphConstant(neg_id,fun_id)
      val _ = case R.scope_lookup_graph_key meter (#keys first,not_key) of
          NONE => ()
        | SOME _ => raise ERR "ordered_boolean_denial"
          "negation node already present"
      val types = R.scope_put_graph_key meter (#types first,fun_key,fun_id)
      val recent = (neg_ty,fun_id):: #recent first
      val not_id = #next first
      val not_node = Node {owner= #owner graph,id=not_id}
      val not_fields : entry =
        {scope=caller,ty=neg_ty,type_id=fun_id,term=negation,
         view=Constant neg_id,raw=SOME 1,inclusive=SOME 1,source=ref NONE}
      val app_id = not_id+1
      val app_node = Node {owner= #owner graph,id=app_id}
      val app_key = R.GraphApplication(scope_id caller,not_id,node_id(#node
        goal))
      val _ = case R.scope_lookup_graph_key meter (#keys first,app_key) of
          NONE => ()
        | SOME _ => raise ERR "ordered_boolean_denial"
          "denial node already present"
      val anchor : source option ref = ref NONE
      val app_fields : entry =
        {scope=caller,ty=Type.bool,type_id=bool_id,term=denial_term,
         view=Application(not_node,#node goal),raw=SOME 3,
         inclusive=SOME 3,source=anchor}
      val keys = R.scope_put_graph_key meter
        (R.scope_put_graph_key meter (#keys first,not_key,not_node),
         app_key,app_node)
      val nodes = R.scope_put_int meter
        (R.scope_put_int meter (#nodes first,not_id,not_fields),
         app_id,app_fields)
      val next_revision = #revision first+1
      val next_snapshot : paid_index_snapshot =
        {types=types,keys=keys,recent=recent,nodes=nodes,
         scopes= #scopes first,reserved= #reserved first,next=app_id+1,
         next_scope= #next_scope first,retirements= #retirements first,
         revision=next_revision}
      val _ = R.scope_meter_charge meter 272
      val _ = paid_index_close graph paid first
      val _ = if Portable.pointer_eq
          (old_bucket,Array.sub(#imports graph,bucket)) then () else
        raise ERR "ordered_boolean_denial" "import bucket changed"
      (* Native REFL was fully paid2400 above. No charged primitive/callback
         is needed after this theorem effect and before OWN publication. *)
      val theorem = Thm.REFL denial_term
      val source : source =
        {node=app_node,original=denial_term,bridge=theorem}
      val _ = anchor := SOME source
      val _ = #types paid := types
      val _ = #recent paid := recent
      val _ = #keys paid := keys
      val _ = #nodes graph := nodes
      val _ = #next graph := app_id+1
      val _ = Array.update(#imports graph,bucket,
        (denial_term,scope_id caller,source)::old_bucket)
      val _ = #validation_changes graph := next_revision
      val _ = #expected saved := next_snapshot
      val _ = #denial_bucket saved := SOME bucket
      val _ = #denial_source saved := SOME source
      val _ = #denial_complete saved := true
    in () end

  (* Fixed authenticated G-to-A completion port. A keeps both handles
     private. No caller Source/hash/proof, native operation or Ready grant. *)
  fun original_source_preparation_data storage caller context =
    let
      val saved = original_import_context_for storage caller context
      val FixedStorage held = storage
      val graph = #graph held
      val meter = #meter held
      val _ = R.scope_meter_charge meter 128
      val _ = if !(#stopped saved) then
        raise ERR "original_source_preparation"
          "unsupported original encountered"
        else ()
      val _ = case !(#remaining saved) of [] => () | _ =>
        raise ERR "original_source_preparation" "original occurrences remain"
      val _ = if !(#denial_complete saved) then () else
        raise ERR "original_source_preparation" "denial is not complete"
      val first = !(#expected saved)
      val _ = R.scope_meter_charge meter 8
      fun same_source (left:source,right:source) =
        #node left= #node right andalso
        Portable.pointer_eq(#original left,#original right) andalso
        Portable.pointer_eq(#bridge left,#bridge right)
      fun issued_alias (candidate:source) canonical anchor receipts =
        (R.scope_meter_charge meter 32;
         case receipts of [] => false
         | OrderedAliasReceipt
             {source=issued,canonical=held,anchor=first}::rest =>
             (R.scope_meter_charge meter 96;
              if same_source(candidate,issued) andalso
                  Portable.pointer_eq(canonical,held) andalso
                  same_source(anchor,first) then true
              else issued_alias candidate canonical anchor rest))
      fun validate (source:source,bucket) =
        let
          val _ = R.scope_meter_charge meter 128
          val Node {owner,id} = #node source
          val _ = if owner= #owner graph andalso bucket>=0 andalso
              bucket<4093 then () else
            raise ERR "original_source_preparation"
              "different Source owner or bucket"
          val fields = case R.scope_lookup_int meter (#nodes first,id) of
              SOME fields => fields
            | NONE => raise ERR "original_source_preparation"
              "missing issued node"
          val canonical = #term fields
          val _ = if #scope fields=caller andalso #type_id fields=0 then ()
            else
            raise ERR "original_source_preparation"
              "different issued representative"
          val anchor = case !(#source fields) of SOME first => first
            | NONE => raise ERR "original_source_preparation"
              "missing Source anchor"
          val _ = R.scope_meter_charge meter 64
          val _ = if #node anchor= #node source andalso
              Portable.pointer_eq(#original anchor,canonical) then () else
            raise ERR "original_source_preparation"
              "different canonical Source anchor"
          val _ = if Portable.pointer_eq(#original source,canonical) then
              if same_source(anchor,source) then () else
                raise ERR "original_source_preparation"
                  "different issued Source anchor"
            else if issued_alias source canonical anchor (!(#aliases saved))
              then () else raise ERR "original_source_preparation"
                "unissued alias Source bridge"
        in () end
      fun restore rows acc =
        (R.scope_meter_charge meter 16;
         case rows of [] => acc
         | row::rest => (R.scope_meter_charge meter 16;
             restore rest (row::acc)))
      val rows = restore (!(#source_rows saved)) []
      fun ordered originals rows count =
        (R.scope_meter_charge meter 32;
         case (originals,rows) of
             ([],[]) => count
           | (term::terms,(row as (source:source,_))::rest) =>
               (R.scope_meter_charge meter 32;
                if Portable.pointer_eq(term,#original source) then () else
                  raise ERR "original_source_preparation"
                    "different original order";
                validate row;ordered terms rest (count+1))
           | _ => raise ERR "original_source_preparation"
             "different original count")
      val count = ordered (#originals saved) rows (0:IntInf.int)
      val _ = if count= !(#completed saved) andalso count>0 then () else
        raise ERR "original_source_preparation" "incomplete original inventory"
      val denied = case (!(#denial_source saved),!(#denial_bucket saved)) of
          (SOME source,SOME bucket) => (source,bucket)
        | _ => raise ERR "original_source_preparation" "missing issued denial"
      val _ = validate denied
      val _ = R.scope_meter_charge meter 32
      val _ = paid_index_close graph (#paid saved) first
    in {originals=rows,denied=denied,revision= #revision first} end

  (* Closed supported-atomic finalisation only. Raw F is DATA: immutable
     issued Sources, canonical representatives and captured limits below
     decide admission. These conservative prototype reservations do not
     assert tight unchanged-budget acceptance or any Ready publication. *)
  fun reserve_ordered_finaliser meter
      (limits:first_boolean_variable_limits) (used:original_import_usage)
      (count:IntInf.int) denied_present =
    let
      val _ = R.scope_meter_charge meter 256
      (* The authenticated membership scan supplies this presence bit.
         Occurrence telemetry below stays cumulative; it is NOT remaining
         per-operand capacity. Bool atoms have raw=inclusive1 and their
         owned negation raw=inclusive3; the empty-Hyp goal bridge is5. *)
      val _ = R.scope_meter_charge meter 32
      val denied_count : IntInf.int = if denied_present then 1 else 0
      val input_extent = IntInf.max(5,1+count+2*denied_count)
      val output_extent = IntInf.max(5,1+count-denied_count)
      val native_work = 7903+512*(count+1)
      val next : original_import_usage =
        {construction_import= #construction_import used,
         construction_literal= #construction_literal used,
         construction_binder= #construction_binder used,
         recipe_template= #recipe_template used,
         recipe_index= #recipe_index used,recipe_operand= #recipe_operand used,
         recipe_token= #recipe_token used,
         semantic_input= #semantic_input used+25+6*count,
         semantic_output= #semantic_output used+13+2*count,
         semantic_template= #semantic_template used+18+2*count,
         native_input= #native_input used+25+6*count,
         native_output= #native_output used+13+2*count,
         native_template= #native_template used+18+2*count,
         native_import= #native_import used+10+2*count,
         type_work= #type_work used+native_work}
      val construction = #construction_limits limits
      val recipes = #recipe_limits construction
      val semantic = #semantic_limits limits
      val native = #native_limits limits
      val ns = #semantic_limits native
      val allows = SmtReplayResourcePolicy.allows
      val admitted = count>=denied_count andalso
        allows (#import_limit construction) (#construction_import next)
        andalso allows (#literal_limit construction)
          (#construction_literal next)
        andalso allows (#binder_limit construction)
          (#construction_binder next)
        andalso allows (#template_limit recipes) (#recipe_template next)
        andalso allows (#index_limit recipes) (#recipe_index next)
        andalso allows (#operand_limit recipes) (#recipe_operand next)
        andalso allows (#token_limit recipes) (#recipe_token next)
        andalso allows (#input_limit semantic) input_extent
        andalso allows (#output_limit semantic) output_extent
        andalso allows (#template_limit semantic) (#semantic_template next)
        andalso allows (#input_limit ns) input_extent
        andalso allows (#output_limit ns) output_extent
        andalso allows (#template_limit ns) (#native_template next)
        andalso allows (#import_limit native) (#native_import next)
        andalso allows (#type_work_limit native) (#type_work next)
    in if admitted then (next,native_work) else
      raise ERR "ordered_boolean_finalise"
        "cumulative original policy exhausted"
    end

  fun finalise_original_boolean_goal storage caller context raw_false =
    let
      (* Expected storage/root owner precedes retained context validation.
         This port cannot adopt a Source, proof profile, meter or goal. *)
      val saved = original_import_context_for storage caller context
      val FixedStorage held = storage
      val graph = #graph held
      val meter = #meter held
      val _ = R.scope_meter_charge meter 256
      val _ = case !(#function_children saved) of [] => () | _::_ =>
        (R.scope_meter_charge meter 16;
         raise ERR "ordered_boolean_finalise"
           "owned application requires an application finaliser")
      val data = original_source_preparation_data storage caller context
      val first = !(#expected saved)
      val (goal,assumptions) = case #originals data of
          (source,_)::rest => (source,rest)
        | [] => raise ERR "ordered_boolean_finalise" "missing issued goal"
      val denied = #1 (#denied data)
      val canonical_goal = #original goal
      (* Goal is the fresh first occurrence. It is never an assumption
         alias: its actual private REFL has raw==canonical endpoints. *)
      val _ = R.scope_meter_charge meter 32
      val hypotheses = Thm.hypset raw_false
      val count = IntInf.fromInt(HOLset.numItems hypotheses)
      (* Real protected cached cardinality, not a caller size or maxInt
         conversion. listItems is prepaid before native set extraction. *)
      val _ = R.scope_meter_charge meter (256+256*count)
      val terms = HOLset.listItems hypotheses
      fun member term rows =
        (R.scope_meter_charge meter 32;
         case rows of [] => false
         | ((source:source,_)::rest) =>
             let
               val _ = R.scope_meter_charge meter 96
               val Node {owner,id} = #node source
               val _ = if owner= #owner graph then () else
                 raise ERR "ordered_boolean_finalise" "different Source owner"
               val fields = case R.scope_lookup_int meter (#nodes first,id) of
                   SOME fields => fields
                 | NONE => raise ERR "ordered_boolean_finalise"
                     "missing canonical hypothesis"
             in if Portable.pointer_eq(term,#term fields) then true
                else member term rest end)
      (* Return only the presence of the EXACT private denied pointer.
         No caller profile/hash/proof is authority. The extra8 per list
         case funds the threaded result/call metadata before its use. *)
      fun all rows denied_seen =
        (R.scope_meter_charge meter 40;
         case rows of [] => denied_seen
         | term::rest =>
             (R.scope_meter_charge meter 32;
              if Portable.pointer_eq(term,#original denied) then
                all rest true
              else if member term assumptions then all rest denied_seen
              else raise ERR "ordered_boolean_finalise"
                "hypothesis is not a canonical source"))
      val denied_present = all terms false
      (* Fixed literal gates precede full protected UID equality. No raw
         term/type recursion, arbitrary name hash or string comparison. *)
      fun fixed expected candidate =
        let
          val _ = R.scope_meter_charge meter 16
          val size = String.size expected
          val _ = if size<=8 then () else
            raise ERR "ordered_boolean_finalise" "nonfixed private literal"
          fun bytes index =
            (R.scope_meter_charge meter 8;
             if index=size then true else
               (R.scope_meter_charge meter 8;
                String.sub(candidate,index)=String.sub(expected,index)
                andalso bytes(index+1)))
        in String.size candidate=size andalso bytes 0 end
      val _ = R.scope_meter_charge meter 128
      val conclusion = Thm.concl raw_false
      val genuine_false = Portable.pointer_eq(conclusion,boolSyntax.F) orelse
        (Term.is_const conclusion andalso
         let
           val {Name=id,...} = Term.dest_thy_constid conclusion
           val {Thy,Name} = KernelSig.name_of_id id
         in fixed "bool" Thy andalso fixed "F" Name andalso
            Term.same_const conclusion boolSyntax.F end)
      val _ = if genuine_false then () else
        raise ERR "ordered_boolean_finalise" "replay did not prove F"
      val _ = R.scope_meter_charge meter 32
      val tag = Thm.tag raw_false
      (* Public dest_tag traverses axioms: only its genuinely empty case
         is permitted. Oracles use their actual paid head/byte stream. *)
      val _ = case Tag.axioms_of tag of [] => () | _::_ =>
        raise ERR "ordered_boolean_finalise" "unexpected replay tags"
      val _ = R.scope_meter_charge meter 32
      val (oracles,_) = Tag.dest_tag tag
      fun allowed names =
        (R.scope_meter_charge meter 16;
         case names of [] => true
         | name::rest =>
             (R.scope_meter_charge meter 16;
              fixed "DISK_THM" name andalso allowed rest))
      val _ = if allowed oracles then () else
        raise ERR "ordered_boolean_finalise" "unexpected replay tags"
      (* Semantic/F/tag validation precedes the exact per-payload guard,
         as in the retained Source-close adapter. Invalid metadata keeps
         its real paid Work prefix but consumes no fabricated finaliser
         occurrence reservation. No native proof effect occurred above. *)
      val (admitted,native_work) = reserve_ordered_finaliser meter
        (#limits saved) (!(#usage saved)) count denied_present
      val _ = R.scope_meter_charge meter 16
      val _ = #usage saved := admitted
      (* All later local native-call/result administration is paid now.
         The last dynamic owner/epoch/root/index closure precedes CCONTR;
         no G store, native-type declaration or callback follows it. *)
      val _ = R.scope_meter_charge meter (native_work+128)
      val _ = ignore(original_import_context_for storage caller context)
      val canonical = Thm.CCONTR canonical_goal raw_false
      val symmetric = Thm.SYM (#bridge goal)
      val final = Thm.EQ_MP symmetric canonical
    in final end
  (* Constructor-origin evidence is created only around THIS real mk_comb.
     It is not granted by a term view, semantic key, flag or caller quote. *)
  datatype owned_application_birth = OwnedApplicationBirth of
    {storage:fixed_storage,original:Term.term,function:Term.term,
     argument:Term.term,limits:first_boolean_variable_limits,
     usage:original_import_usage,
     context:original_import_context option ref,
     argument_type:(Type.hol_type * int) option ref,
     argument_source:(source * Word.word) option ref,
     application_source:(source * Word.word * int) option ref}

  fun owned_application_birth_for storage caller
      (birth as OwnedApplicationBirth retained) =
    let
      val FixedStorage expected = storage
      val FixedStorage held = #storage retained
      val _ = if #owner expected= #owner held andalso
          caller= #root expected andalso caller= #root held then () else
        raise ERR "owned_application" "different original owner"
      val _ = ignore(fixed_storage_context storage caller)
    in retained end

  fun new_owned_boolean_application_with_bootstrap_meter meter
      ({function,argument,limits}:{function:Term.term,argument:Term.term,
        limits:first_boolean_variable_limits}) =
    let
      val _ = R.scope_meter_charge meter 384
      (* A defined cumulative constructor component: raw output3 and two
         retained leaves; actual annotated input3/output5; no proof is claimed.
           *)
      val usage : original_import_usage =
        {construction_import=3,construction_literal=2,
         construction_binder=0,recipe_template=0,recipe_index=0,
         recipe_operand=0,recipe_token=0,semantic_input=3,
         semantic_output=5,semantic_template=5,native_input=3,
         native_output=5,native_template=5,native_import=3,type_work=1312}
      val construction = #construction_limits limits
      val recipes = #recipe_limits construction
      val semantic = #semantic_limits limits
      val native = #native_limits limits
      val ns = #semantic_limits native
      val allows = SmtReplayResourcePolicy.allows
      val _ = if allows (#import_limit construction) 3 andalso
          allows (#literal_limit construction) 2 andalso
          allows (#binder_limit construction) 0 andalso
          allows (#template_limit recipes) 0 andalso
          allows (#index_limit recipes) 0 andalso
          allows (#operand_limit recipes) 0 andalso
          allows (#token_limit recipes) 0 andalso
          allows (#input_limit semantic) 3 andalso
          allows (#output_limit semantic) 5 andalso
          allows (#template_limit semantic) 5 andalso
          allows (#input_limit ns) 3 andalso
          allows (#output_limit ns) 5 andalso
          allows (#template_limit ns) 5 andalso
          allows (#import_limit native) 3 andalso
          allows (#type_work_limit native) 1312 then () else
        raise ERR "owned_application" "constructor policy exhausted"
      (* Native programme1312 is wholly admitted before the first native
         predicate. It is not an observed cost or later proof credit. *)
      val _ = R.scope_meter_charge meter 1312
      val {graph,root,storage} =
        new_original_with_fixed_storage_bootstrap_meter meter
      fun atom term = Term.is_var term orelse Term.is_const term
      val _ = if atom function andalso atom argument then () else
        raise ERR "owned_application" "constructor children are not atoms"
      val function_type = Term.type_of function
      val argument_type = Term.type_of argument
      val bool_name = #Tyop(Type.dest_thy_typeid Type.bool)
      val {Ty=negation_type,...} =
        Term.dest_thy_constid boolSyntax.negation
      val {Tyop=fun_name,...} = Type.dest_thy_typeid negation_type
      fun boolean_leaf ty =
        if Type.is_vartype ty then false else
          let val {Tyop,Args,...} = Type.dest_thy_typeid ty
              val {Thy,Name} = KernelSig.name_of_id Tyop
          in case Args of [] =>
              String.size Thy=3 andalso String.size Name=4 andalso
              Tyop=bool_name
            | _ => false end
      val _ = if Type.is_vartype function_type then
          raise ERR "owned_application" "different function type"
        else ()
      val {Tyop,Args,...} = Type.dest_thy_typeid function_type
      val {Thy,Name} = KernelSig.name_of_id Tyop
      val {Thy=expected_thy,Name=expected_name} =
        KernelSig.name_of_id fun_name
      val _ = if String.size Thy=String.size expected_thy andalso
          String.size Name=String.size expected_name andalso
          String.size expected_thy<=4 andalso
          String.size expected_name<=4 andalso Tyop=fun_name then () else
        raise ERR "owned_application" "different function declaration"
      val _ = case Args of [domain,range] =>
          if boolean_leaf domain andalso boolean_leaf range andalso
              boolean_leaf argument_type then () else
            raise ERR "owned_application" "different Boolean child type"
        | _ => raise ERR "owned_application" "different function type"
      (* All local result/ref/record publication administration, native
         constructor work and same-root closure precede actual mk_comb. *)
      val _ = R.scope_meter_charge meter 152
      val _ = ignore(fixed_storage_context storage root)
      val original = Term.mk_comb(function,argument)
      val birth = OwnedApplicationBirth
        {storage=storage,original=original,function=function,
         argument=argument,limits=limits,usage=usage,
         context=ref NONE,argument_type=ref NONE,
         argument_source=ref NONE,application_source=ref NONE}
    in {graph=graph,root=root,storage=storage,original=original,birth=birth}
    end

  fun begin_owned_application_import_context storage caller birth =
    let
      val retained = owned_application_birth_for storage caller birth
      val FixedStorage held = storage
      val meter = #meter held
      val _ = R.scope_meter_charge meter 128
      val _ = case !(#context retained) of NONE => () | SOME _ =>
        raise ERR "owned_application" "context already claimed"
      val context as OriginalImportContext saved =
        begin_original_import_context storage caller
          {limits= #limits retained,originals=[#original retained]}
      (* This context is newly local and has never escaped. Carry the
         actual birth reservation; no published counter/context is reset. *)
      val _ = R.scope_meter_charge meter 32
      val _ = #usage saved := #usage retained
      val _ = #context retained := SOME context
    in context end

  fun prepare_owned_application_function storage caller context birth =
    let
      val saved = original_import_context_for storage caller context
      val FixedStorage held = storage
      val graph = #graph held
      val paid = #paid saved
      val meter = #meter held
      val _ = R.scope_meter_charge meter 192
      val _ = if !(#stopped saved) orelse !(#denial_complete saved) then
        raise ERR "ordered_function_child" "original programme is closed"
        else ()
      val retained = owned_application_birth_for storage caller birth
      val _ = R.scope_meter_charge meter 128
      val _ = case !(#context retained) of SOME expected =>
          if Portable.pointer_eq(expected,context) then () else
            raise ERR "owned_application" "different captured context"
        | NONE => raise ERR "owned_application" "context is not claimed"
      val _ = case !(#remaining saved) of item::_ =>
          if Portable.pointer_eq(item,#original retained) then () else
            raise ERR "owned_application" "different retained original"
        | [] => raise ERR "owned_application" "no current original"
      val original = #function retained
      fun issued (candidate:source) rows =
        (R.scope_meter_charge meter 32;
         case rows of [] => false
         | OrderedFunctionChild {source,...}::rest =>
             (#node source= #node candidate andalso
              Portable.pointer_eq(#original source,#original candidate)
              andalso Portable.pointer_eq(#bridge source,#bridge candidate))
             orelse issued candidate rest)
      fun already rows =
        (R.scope_meter_charge meter 32;
         case rows of [] => false
         | OrderedFunctionChild {source,...}::rest =>
             Portable.pointer_eq(#original source,original)
             orelse already rest)
      fun memo rows =
        (R.scope_meter_charge meter 32;
         case rows of [] => NONE
         | (term,frame,source)::rest =>
             if frame=scope_id caller andalso
                 Portable.pointer_eq(term,original) then SOME source
             else memo rest)
      fun admit amount =
        let val usage = reserve_ordered_extra_native meter
              (#limits saved) (!(#usage saved)) amount
            val _ = R.scope_meter_charge meter 16
            val _ = #usage saved := usage
        in R.scope_meter_charge meter amount end
    in if already (!(#function_children saved)) then () else
      let
        (* The same authentic fifteen counters are monotone. A failed
           classifier/type observation retains its actual paid prefix. *)
        val usage = reserve_ordered_boolean meter (#limits saved)
          (!(#usage saved))
        val _ = R.scope_meter_charge meter 16
        val _ = #usage saved := usage
        val _ = R.scope_meter_charge meter 74
        val is_variable = Term.is_var original
        val is_constant = if is_variable then false
          else Term.is_const original
        val _ = if is_variable orelse is_constant then () else
          raise ERR "ordered_function_child" "current original is not an atom"
        val actual_type = Term.type_of original
        val observed = observe_ordered_native_type storage caller context
          actual_type
        (* Fixed metadata512 is admitted independently of both the Type
           forest's actual per-cell128 and the later proof programme.
           The trusted builtin supplies the complete function UID; its
           two actual leaves are verified semantically, never by pointer. *)
        val _ = admit 512
        val {Ty=negation_type,...} =
          Term.dest_thy_constid boolSyntax.negation
        val bool_name = #Tyop(Type.dest_thy_typeid Type.bool)
        val {Tyop=fun_name,Args,...} =
          Type.dest_thy_typeid negation_type
        fun boolean_leaf ty =
          if Type.is_vartype ty then false else
            let val {Tyop,Args,...} = Type.dest_thy_typeid ty
                val {Thy,Name} = KernelSig.name_of_id Tyop
            in case Args of [] =>
                String.size Thy=3 andalso String.size Name=4 andalso
                Tyop=bool_name
              | _ => false end
        val _ = case Args of [domain,range] =>
            if boolean_leaf domain andalso boolean_leaf range then () else
              raise ERR "ordered_function_child" "different builtin function"
          | _ => raise ERR "ordered_function_child"
            "different builtin function"
        val _ = R.scope_meter_charge meter 96
        val typed_snapshot = !(#expected saved)
        val bool_id = case R.scope_lookup_graph_key meter
            (#types typed_snapshot,R.GraphTypeOperator(bool_name,[])) of
            SOME id => id
          | NONE => raise ERR "ordered_function_child" "missing observed Bool"
        val type_id = case R.scope_lookup_graph_key meter
            (#types typed_snapshot,
             R.GraphTypeOperator(fun_name,[bool_id,bool_id])) of
            SOME id => if id=observed then id else
              raise ERR "ordered_function_child" "different observed function"
          | NONE => raise ERR "ordered_function_child"
            "different observed function"
        (* Actual raw descriptor and name hashing are distinct from the
           separately priced native equality/REFL/ALPHA calls below. *)
        val _ = R.scope_meter_charge meter
          (if is_variable then 64 else 128)
        val (ty,key,view,name,bucket) = if is_variable then
            let
              val (text,ty) = Term.dest_var original
              val _ = R.scope_meter_charge meter 32
              val length = String.size text
              fun hash i value =
                (R.scope_meter_charge meter 8;
                 if i=length then value else
                   (R.scope_meter_charge meter 16;
                    hash (i+1) (Word.+(Word.*(value,0w33),
                      Word.fromInt(Char.ord(String.sub(text,i)))))))
              val value = hash 0 0w17
              val _ = R.scope_meter_charge meter 32
              val bucket = Word.toInt(Word.mod
                (Word.+(Word.*(0w37,value),value),Word.fromInt 4093))
            in (ty,R.GraphVariable
                (scope_id caller,kind_id RigidSource,text,type_id),
                Variable(RigidSource,original),SOME text,bucket) end
          else
            let val {Name,Ty=ty,...} = Term.dest_thy_constid original
                val value = Word.fromInt(KernelSig.epoch_of Name)
                val bucket = Word.toInt(Word.mod
                  (Word.+(Word.*(0w37,value),value),Word.fromInt 4093))
            in (ty,R.GraphConstant(Name,type_id),Constant Name,NONE,bucket) end
        val _ = R.scope_meter_charge meter 128
        val _ = if Portable.pointer_eq(ty,actual_type) then () else
          raise ERR "ordered_function_child" "different observed native Type"
        val first = !(#expected saved)
        val old_bucket = Array.sub(#imports graph,bucket)
      in case memo old_bucket of SOME source =>
          if issued source (!(#function_children saved)) then () else
            raise ERR "ordered_function_child" "foreign cached child Source"
        | NONE =>
          (case R.scope_lookup_graph_key meter (#keys first,key) of
              NONE =>
                let
                  (* Fresh typed atom REFL1668: the equality template
                     still has five input nodes; instantiated polymorphic
                     scan now has nine nodes and seventeen list cases. *)
                  val branch = reserve_ordered_extra_native meter
                    (#limits saved) (!(#usage saved)) 1668
                  val _ = R.scope_meter_charge meter 16
                  val _ = #usage saved := branch
                  val _ = R.scope_meter_charge meter 640
                  val id = #next first
                  val node = Node {owner= #owner graph,id=id}
                  val anchor : source option ref = ref NONE
                  val fields : entry =
                    {scope=caller,ty=ty,type_id=type_id,term=original,
                     view=view,raw=SOME 1,inclusive=SOME 1,source=anchor}
                  val keys = R.scope_put_graph_key meter (#keys first,key,node)
                  val nodes = R.scope_put_int meter (#nodes first,id,fields)
                  val reserved = case name of NONE => #reserved first
                    | SOME text => R.scope_add_string meter (#reserved
                      first,text)
                  val revision = #revision first+1
                  val next : paid_index_snapshot =
                    {types= #types first,keys=keys,recent= #recent first,
                     nodes=nodes,scopes= #scopes first,reserved=reserved,
                     next=id+1,next_scope= #next_scope first,
                     retirements= #retirements first,revision=revision}
                  val _ = R.scope_meter_charge meter 256
                  val _ = paid_index_close graph paid first
                  val _ = if Portable.pointer_eq
                      (old_bucket,Array.sub(#imports graph,bucket)) then ()
                        else
                    raise ERR "ordered_function_child" "import bucket changed"
                  val _ = R.scope_meter_charge meter 1668
                  val theorem = Thm.REFL original
                  val source : source =
                    {node=node,original=original,bridge=theorem}
                  val receipt = OrderedFunctionChild
                    {source=source,canonical=original,anchor=source,
                     type_id=type_id}
                  (* All root/list/receipt stores were funded before REFL.
                     No native/debit/callback occurs inside own publication. *)
                  val _ = anchor := SOME source
                  val _ = #keys paid := keys
                  val _ = #nodes graph := nodes
                  val _ = #next graph := id+1
                  val _ = #reserved graph := reserved
                  val _ = Array.update(#imports graph,bucket,
                    (original,scope_id caller,source)::old_bucket)
                  val _ = #validation_changes graph := revision
                  val _ = #expected saved := next
                  val _ = #function_children saved :=
                    receipt :: !(#function_children saved)
                in () end
            | SOME node =>
                let
                  val _ = R.scope_meter_charge meter 256
                  val Node {owner,id} = node
                  val _ = if owner= #owner graph then () else
                    raise ERR "ordered_function_child" "different node owner"
                  val fields = case R.scope_lookup_int meter (#nodes first,id)
                    of
                      SOME fields => fields
                    | NONE => raise ERR "ordered_function_child" "missing node"
                  val canonical = #term fields
                  val _ = if #scope fields=caller andalso
                      #type_id fields=type_id then () else
                    raise ERR "ordered_function_child" "different typed node"
                  val anchor = case !(#source fields) of SOME source => source
                    | NONE => raise ERR "ordered_function_child"
                      "missing anchor"
                  val _ = if #node anchor=node andalso
                      Portable.pointer_eq(#original anchor,canonical) andalso
                      issued anchor (!(#function_children saved)) then () else
                    raise ERR "ordered_function_child" "foreign typed anchor"
                  val _ = admit 256
                  fun bytes text = IntInf.fromInt(String.size text)
                  val (mass,canonical_key,stored_key) =
                    case (view,#view fields,name) of
                      (Variable(RigidSource,_),
                       Variable(RigidSource,retained),SOME raw) =>
                        if Term.is_var canonical andalso
                            Portable.pointer_eq(retained,canonical) andalso
                            Portable.pointer_eq
                              (Term.type_of canonical,#ty fields) then
                          let val (text,_) = Term.dest_var canonical
                              val k = R.GraphVariable
                                (scope_id caller,kind_id
                                  RigidSource,text,type_id)
                          in (bytes raw+bytes text,k,k) end
                        else raise ERR "ordered_function_child"
                          "different variable"
                    | (Constant raw_id,Constant stored_id,NONE) =>
                        if Term.is_const canonical andalso
                            Portable.pointer_eq
                              (Term.type_of canonical,#ty fields) then
                          let val {Name=canonical_id,...} =
                                Term.dest_thy_constid canonical
                              val {Thy=a,Name=b} = KernelSig.name_of_id raw_id
                              val {Thy=c,Name=d} =
                                KernelSig.name_of_id canonical_id
                          in (bytes a+bytes b+bytes c+bytes d,
                              R.GraphConstant(canonical_id,type_id),
                              R.GraphConstant(stored_id,type_id)) end
                        else raise ERR "ordered_function_child"
                          "different constant"
                    | _ => raise ERR "ordered_function_child"
                      "different atom kind"
                  val _ = if R.scope_compare_graph_key meter
                        (key,canonical_key)=EQUAL andalso
                      R.scope_compare_graph_key meter (key,stored_key)=EQUAL
                    then () else
                      raise ERR "ordered_function_child"
                        "different semantic key"
                  val alpha : IntInf.int = 3801+32*(mass+1)
                  val _ = admit (alpha+256)
                  val _ = R.scope_meter_charge meter 640
                  val revision = #revision first+1
                  val next : paid_index_snapshot =
                    {types= #types first,keys= #keys first,recent= #recent
                      first,
                     nodes= #nodes first,scopes= #scopes first,
                     reserved= #reserved first,next= #next first,
                     next_scope= #next_scope first,
                     retirements= #retirements first,revision=revision}
                  val _ = paid_index_close graph paid first
                  val _ = if Portable.pointer_eq
                      (old_bucket,Array.sub(#imports graph,bucket)) then ()
                        else
                    raise ERR "ordered_function_child" "import bucket changed"
                  val theorem = Thm.ALPHA original canonical
                  val (left,right) = Term.dest_eq(Thm.concl theorem)
                  val _ = if Portable.pointer_eq(left,original) andalso
                      Portable.pointer_eq(right,canonical) andalso
                      HOLset.numItems(Thm.hypset theorem)=0 andalso
                      Tag.isEmpty(Thm.tag theorem) then () else
                    raise ERR "ordered_function_child"
                      "different bridge endpoints"
                  val source : source =
                    {node=node,original=original,bridge=theorem}
                  val receipt = OrderedFunctionChild
                    {source=source,canonical=canonical,anchor=anchor,
                     type_id=type_id}
                  val _ = Array.update(#imports graph,bucket,
                    (original,scope_id caller,source)::old_bucket)
                  val _ = #validation_changes graph := revision
                  val _ = #expected saved := next
                  val _ = #function_children saved :=
                    receipt :: !(#function_children saved)
                in () end)
      end
    end


  (* Consume only the two genuine constructor-captured raw children.
     Functional child proof is private; argument preparation below is a
     real Type witness only, not an original Source or completed Hyp. *)
  fun prepare_owned_application_children storage caller context birth =
    let
      val retained = owned_application_birth_for storage caller birth
      val _ = prepare_owned_application_function storage caller context birth
      val saved = original_import_context_for storage caller context
      val FixedStorage held = storage
      val meter = #meter held
      val _ = R.scope_meter_charge meter 128
    in case !(#argument_type retained) of SOME _ => () | NONE =>
      let
        val usage = reserve_ordered_extra_native meter (#limits saved)
          (!(#usage saved)) 106
        val _ = R.scope_meter_charge meter 16
        val _ = #usage saved := usage
        val _ = R.scope_meter_charge meter 106
        val argument = #argument retained
        val _ = if Term.is_var argument orelse Term.is_const argument then ()
          else raise ERR "owned_application" "different argument atom"
        val ty = Term.type_of argument
        val id = observe_ordered_native_type storage caller context ty
        val first = !(#expected saved)
        val _ = R.scope_meter_charge meter 64
        val bool_name = #Tyop(Type.dest_thy_typeid Type.bool)
        val expected = case R.scope_lookup_graph_key meter
            (#types first,R.GraphTypeOperator(bool_name,[])) of
            SOME expected => expected
          | NONE => raise ERR "owned_application" "missing argument Bool"
        val _ = if id=expected then () else
          raise ERR "owned_application" "different argument Type"
        val _ = R.scope_meter_charge meter 16
        val _ = ignore(original_import_context_for storage caller context)
        val _ = #argument_type retained := SOME (ty,id)
      in () end
    end

  (* These private geometry updates describe actual issued equality payloads.
     Input/output policies constrain each operand/result; telemetry retains
     all occurrences. No used counter is reset to a capacity. *)
  fun reserve_owned_application_source meter
      (limits:first_boolean_variable_limits) (used:original_import_usage)
      application =
    let
      val _ = R.scope_meter_charge meter 256
      val next : original_import_usage =
        {construction_import= #construction_import used+
            (if application then 3 else 1),
         construction_literal= #construction_literal used+
            (if application then 0 else 1),
         construction_binder= #construction_binder used,
         recipe_template= #recipe_template used,
         recipe_index= #recipe_index used,recipe_operand= #recipe_operand used,
         recipe_token= #recipe_token used,
         semantic_input= #semantic_input used+(if application then 128 else 1),
         semantic_output= #semantic_output used+(if application then 95 else
           11),
         semantic_template= #semantic_template used+
            (if application then 95 else 11),
         native_input= #native_input used+(if application then 128 else 1),
         native_output= #native_output used+(if application then 95 else 11),
         native_template= #native_template used+(if application then 95 else
           11),
         native_import= #native_import used+(if application then 45 else 5),
         type_work= #type_work used+(if application then 16096 else 1424)}
      val construction = #construction_limits limits
      val recipes = #recipe_limits construction
      val semantic = #semantic_limits limits
      val native = #native_limits limits
      val ns = #semantic_limits native
      val allows = SmtReplayResourcePolicy.allows
      val input : IntInf.int = if application then 21 else 1
      val output : IntInf.int = if application then 19 else 11
      val _ = if
          allows (#import_limit construction) (#construction_import next)
          andalso allows (#literal_limit construction)
            (#construction_literal next)
          andalso allows (#binder_limit construction)
            (#construction_binder next)
          andalso allows (#template_limit recipes) (#recipe_template next)
          andalso allows (#index_limit recipes) (#recipe_index next)
          andalso allows (#operand_limit recipes) (#recipe_operand next)
          andalso allows (#token_limit recipes) (#recipe_token next)
          andalso allows (#input_limit semantic) input
          andalso allows (#output_limit semantic) output
          andalso allows (#template_limit semantic) (#semantic_template next)
          andalso allows (#input_limit ns) input
          andalso allows (#output_limit ns) output
          andalso allows (#template_limit ns) (#native_template next)
          andalso allows (#import_limit native) (#native_import next)
          andalso allows (#type_work_limit native) (#type_work next)
        then () else
          raise ERR "owned_application_source"
            "cumulative original policy exhausted"
    in next end

  fun owned_application_extra_native meter (OriginalImportContext saved) amount
    =
    let val next = reserve_ordered_extra_native meter (#limits saved)
          (!(#usage saved)) amount
        val _ = R.scope_meter_charge meter 16
        val _ = #usage saved := next
    in R.scope_meter_charge meter amount end

  fun prepare_owned_application_argument_source storage caller context birth =
    let
      val retained = owned_application_birth_for storage caller birth
      val saved = original_import_context_for storage caller context
      val FixedStorage held = storage
      val graph = #graph held
      val meter = #meter held
      val paid = #paid saved
      val _ = R.scope_meter_charge meter 192
    in case !(#argument_source retained) of SOME _ => () | NONE =>
      let
        val original = #argument retained
        val (ty,type_id) = case !(#argument_type retained) of SOME pair => pair
          | NONE => raise ERR "owned_application_source"
            "argument Type is not prepared"
        val next_usage = reserve_owned_application_source meter
          (#limits saved) (!(#usage saved)) false
        val _ = R.scope_meter_charge meter 16
        val _ = #usage saved := next_usage
        val _ = R.scope_meter_charge meter 1424
        val _ = owned_application_extra_native meter context 8
        val is_variable = Term.is_var original
        val _ = owned_application_extra_native meter context
          (if is_variable then 64 else 128)
        val (key,view,name,code) = if is_variable then
            let val (text,actual_type) = Term.dest_var original
                val _ = R.scope_meter_charge meter 32
                val _ = if Portable.pointer_eq(actual_type,ty) then () else
                  raise ERR "owned_application_source"
                    "different argument Type"
                val length = String.size text
                fun hash i value =
                  (R.scope_meter_charge meter 8;
                   if i=length then value else
                     (R.scope_meter_charge meter 16;
                      hash (i+1) (Word.+(Word.*(value,0w33),
                        Word.fromInt(Char.ord(String.sub(text,i)))))))
                val value = hash 0 0w17
            in (R.GraphVariable
                (scope_id caller,kind_id RigidSource,text,type_id),
                Variable(RigidSource,original),SOME text,value) end
          else
            let val {Name,Ty=actual_type,...} = Term.dest_thy_constid original
                val _ = R.scope_meter_charge meter 32
                val _ = if Portable.pointer_eq(actual_type,ty) then () else
                  raise ERR "owned_application_source"
                    "different argument Type"
            in (R.GraphConstant(Name,type_id),Constant Name,NONE,
                Word.fromInt(KernelSig.epoch_of Name)) end
        val _ = R.scope_meter_charge meter 640
        val first = !(#expected saved)
        val bucket = Word.toInt(Word.mod
          (Word.+(Word.*(0w37,code),code),Word.fromInt 4093))
        val old_bucket = Array.sub(#imports graph,bucket)
        val _ = case R.scope_lookup_graph_key meter (#keys first,key) of
            NONE => () | SOME _ =>
              raise ERR "owned_application_source" "argument node is not fresh"
        val id = #next first
        val node = Node {owner= #owner graph,id=id}
        val anchor : source option ref = ref NONE
        val fields : entry =
          {scope=caller,ty=ty,type_id=type_id,term=original,
           view=view,raw=SOME 1,inclusive=SOME 1,source=anchor}
        val keys = R.scope_put_graph_key meter (#keys first,key,node)
        val nodes = R.scope_put_int meter (#nodes first,id,fields)
        val reserved = case name of NONE => #reserved first
          | SOME text => R.scope_add_string meter (#reserved first,text)
        val revision = #revision first+1
        val next : paid_index_snapshot =
          {types= #types first,keys=keys,recent= #recent first,
           nodes=nodes,scopes= #scopes first,reserved=reserved,
           next=id+1,next_scope= #next_scope first,
           retirements= #retirements first,revision=revision}
        val _ = R.scope_meter_charge meter 272
        val _ = paid_index_close graph paid first
        val _ = if Portable.pointer_eq
            (old_bucket,Array.sub(#imports graph,bucket)) then () else
          raise ERR "owned_application_source" "argument import bucket changed"
        val theorem = Thm.REFL original
        val source : source = {node=node,original=original,bridge=theorem}
        val _ = anchor := SOME source
        val _ = #keys paid := keys
        val _ = #nodes graph := nodes
        val _ = #next graph := id+1
        val _ = #reserved graph := reserved
        val _ = Array.update(#imports graph,bucket,
          (original,scope_id caller,source)::old_bucket)
        val _ = #validation_changes graph := revision
        val _ = #expected saved := next
        val _ = #argument_source retained := SOME (source,code)
      in () end
    end

  (* Reachable on every accepted fresh constructor birth. MK_COMB is never
     replaced by an unreachable branch or a dummy REFL-only completion. *)
  fun complete_owned_application_source storage caller context birth =
    let
      val retained = owned_application_birth_for storage caller birth
      val saved_at_entry = original_import_context_for storage caller context
      val FixedStorage initial_held = storage
      val initial_meter = #meter initial_held
      val _ = R.scope_meter_charge initial_meter 128
      (* Actual functional-child equality annotations21 (not the old
         prototype11 telemetry), Bool-child11, and App equality19. The
         largest single native operand/result is21. Fund this full actual
         payload gate before invoking either child proof programme. *)
      val semantic = #semantic_limits (#limits saved_at_entry)
      val native_semantic = #semantic_limits
        (#native_limits (#limits saved_at_entry))
      val allows = SmtReplayResourcePolicy.allows
      val _ = if allows (#input_limit semantic) 21 andalso
          allows (#output_limit semantic) 21 andalso
          allows (#template_limit semantic) 21 andalso
          allows (#input_limit native_semantic) 21 andalso
          allows (#output_limit native_semantic) 21 andalso
          allows (#template_limit native_semantic) 21 then () else
        raise ERR "owned_application_source" "native payload policy exhausted"
      val _ = prepare_owned_application_children storage caller context birth
      val _ = prepare_owned_application_argument_source storage caller context
        birth
      val saved = original_import_context_for storage caller context
      val FixedStorage held = storage
      val graph = #graph held
      val meter = #meter held
      val paid = #paid saved
      val _ = R.scope_meter_charge meter 256
    in case !(#application_source retained) of SOME _ => () | NONE =>
      let
        fun function_source rows =
          (R.scope_meter_charge meter 32;
           case rows of [] =>
               raise ERR "owned_application_source"
                 "missing private function Source"
           | OrderedFunctionChild {source,canonical,anchor,type_id}::rest =>
               if Portable.pointer_eq(#original source,#function retained) then
                 (source,canonical,anchor,type_id)
               else function_source rest)
        val (function,canonical_function,function_anchor,function_type_id) =
          function_source (!(#function_children saved))
        val (argument,argument_code) = case !(#argument_source retained) of
            SOME pair => pair
          | NONE => raise ERR "owned_application_source"
            "missing private argument Source"
        val first = !(#expected saved)
        val _ = R.scope_meter_charge meter 256
        fun own_fields (source:source) =
          let val Node {owner,id} = #node source
              val _ = if owner= #owner graph then () else
                raise ERR "owned_application_source" "different child owner"
          in case R.scope_lookup_int meter (#nodes first,id) of SOME fields =>
            fields
            | NONE => raise ERR "owned_application_source" "missing child node"
              end
        val function_fields = own_fields function
        val argument_fields = own_fields argument
        val _ = if #scope function_fields=caller andalso
            #scope argument_fields=caller andalso
            #type_id function_fields=function_type_id andalso
            Portable.pointer_eq(canonical_function,#function retained) andalso
            Portable.pointer_eq(#term function_fields,#function retained)
              andalso
            Portable.pointer_eq(#original function_anchor,#function retained)
              andalso
            #node function_anchor= #node function andalso
            Portable.pointer_eq(#original argument,#argument retained) andalso
            Portable.pointer_eq(#term argument_fields,#argument retained) then
              () else
          raise ERR "owned_application_source"
            "different captured canonical children"
        val (argument_type,argument_type_id) =
          case !(#argument_type retained) of SOME pair => pair
          | NONE => raise ERR "owned_application_source"
            "missing argument Type receipt"
        val _ = if #type_id argument_fields=argument_type_id andalso
            Portable.pointer_eq(#ty argument_fields,argument_type) then () else
          raise ERR "owned_application_source"
            "different argument Type receipt"
        (* Hash ONLY the captured authenticated function leaf. Its actual
           byte stream is paid; no Term.hash/viewApplication is authority. *)
        val _ = R.scope_meter_charge meter 64
        val function_code = case #view function_fields of
            Variable(RigidSource,term) =>
              let val _ = owned_application_extra_native meter context 64
                  val (text,_) = Term.dest_var term
                  val length = String.size text
                  fun hash i value =
                    (R.scope_meter_charge meter 8;
                     if i=length then value else
                       (R.scope_meter_charge meter 16;
                        hash (i+1) (Word.+(Word.*(value,0w33),
                          Word.fromInt(Char.ord(String.sub(text,i)))))))
              in hash 0 0w17 end
          | Constant id =>
              (owned_application_extra_native meter context 8;
               Word.fromInt(KernelSig.epoch_of id))
          | _ => raise ERR "owned_application_source" "different function atom"
        val next_usage = reserve_owned_application_source meter
          (#limits saved) (!(#usage saved)) true
        val _ = R.scope_meter_charge meter 16
        val _ = #usage saved := next_usage
        (* All input/result native metadata and five actual theorem calls
           are prepaid NOW. No R debit/callback follows the first MK_COMB
           until the actual private node/key/source publication is closed. *)
        val _ = R.scope_meter_charge meter 16096
        val _ = R.scope_meter_charge meter 896
        val (fl,fr) = Term.dest_eq(Thm.concl(#bridge function))
        val (xl,xr) = Term.dest_eq(Thm.concl(#bridge argument))
        fun clean theorem = HOLset.numItems(Thm.hypset theorem)=0 andalso
          Tag.isEmpty(Thm.tag theorem)
        val _ = if Portable.pointer_eq(fl,#function retained) andalso
            Portable.pointer_eq(fr,#function retained) andalso
            Portable.pointer_eq(xl,#argument retained) andalso
            Portable.pointer_eq(xr,#argument retained) andalso
            clean(#bridge function) andalso clean(#bridge argument) then ()
              else
          raise ERR "owned_application_source"
            "different private child bridges"
        val {Tyop,Args,...} = Type.dest_thy_typeid(#ty function_fields)
        val range = case Args of [_,range] => range
          | _ => raise ERR "owned_application_source"
            "different sealed function Type"
        val _ = case R.scope_lookup_graph_key meter
            (#types first,R.GraphTypeOperator
              (Tyop,[argument_type_id,argument_type_id])) of
            SOME id => if id=function_type_id then () else
              raise ERR "owned_application_source"
                "different semantic function Type"
          | NONE => raise ERR "owned_application_source"
            "missing semantic function Type"
        (* Captured constructor result already has exactly these canonical
           children, hence is the preconstructed canonical root as well as
           the actual original. No second mk_comb or native fee credit. *)
        val original = #original retained
        val code = Word.+(Word.+(Word.*(function_code,0w37),0w29),
          Word.*(0w17,argument_code))
        val bucket = Word.toInt(Word.mod
          (Word.+(Word.*(0w37,code),code),Word.fromInt 4093))
        val old_bucket = Array.sub(#imports graph,bucket)
        val key = R.GraphApplication
          (scope_id caller,node_id(#node function),node_id(#node argument))
        val _ = case R.scope_lookup_graph_key meter (#keys first,key) of
            NONE => () | SOME _ =>
              raise ERR "owned_application_source"
                "application node is not fresh"
        val id = #next first
        val node = Node {owner= #owner graph,id=id}
        val anchor : source option ref = ref NONE
        val fields : entry =
          {scope=caller,ty=range,type_id=argument_type_id,term=original,
           view=Application(#node function,#node argument),
           raw=SOME 3,inclusive=SOME 3,source=anchor}
        val keys = R.scope_put_graph_key meter (#keys first,key,node)
        val nodes = R.scope_put_int meter (#nodes first,id,fields)
        val revision = #revision first+1
        val next : paid_index_snapshot =
          {types= #types first,keys=keys,recent= #recent first,
           nodes=nodes,scopes= #scopes first,reserved= #reserved first,
           next=id+1,next_scope= #next_scope first,
           retirements= #retirements first,revision=revision}
        val _ = R.scope_meter_charge meter 384
        (* Retained hash/bucket tuple is allocated only in this own store. *)
        val _ = R.scope_meter_charge meter 4
        val _ = paid_index_close graph paid first
        val _ = if Portable.pointer_eq
            (old_bucket,Array.sub(#imports graph,bucket)) then () else
          raise ERR "owned_application_source"
            "application import bucket changed"
        val combined = Thm.MK_COMB(#bridge function,#bridge argument)
        val (left,right) = Term.dest_eq(Thm.concl combined)
        val (lf,lx) = Term.dest_comb left
        val (rf,rx) = Term.dest_comb right
        val _ = if Portable.pointer_eq(lf,#function retained) andalso
            Portable.pointer_eq(lx,#argument retained) andalso
            Portable.pointer_eq(rf,#function retained) andalso
            Portable.pointer_eq(rx,#argument retained) andalso clean combined
              then () else
          raise ERR "owned_application_source" "different MK_COMB endpoints"
        val raw_alignment = Thm.ALPHA original left
        val raw_combined = Thm.TRANS raw_alignment combined
        val canonical_alignment = Thm.ALPHA right original
        val theorem = Thm.TRANS raw_combined canonical_alignment
        val (actual_left,actual_right) = Term.dest_eq(Thm.concl theorem)
        val _ = if Portable.pointer_eq(actual_left,original) andalso
            Portable.pointer_eq(actual_right,original) andalso clean theorem
              then () else
          raise ERR "owned_application_source" "different actual App bridge"
        val source : source = {node=node,original=original,bridge=theorem}
        val _ = anchor := SOME source
        val _ = #keys paid := keys
        val _ = #nodes graph := nodes
        val _ = #next graph := id+1
        val _ = Array.update(#imports graph,bucket,
          (original,scope_id caller,source)::old_bucket)
        val _ = #validation_changes graph := revision
        val _ = #expected saved := next
        val _ = #application_source retained := SOME(source,code,bucket)
      in () end
    end

  (* Only a constructor-owned, already issued App Source may enter this
     completion. Occurrence and denial publish together: the old atomic
     denial can never observe an intermediate App goal witness. *)
  fun reserve_owned_application_denial meter
      (limits:first_boolean_variable_limits) (used:original_import_usage) =
    let
      val _ = R.scope_meter_charge meter 256
      val next : original_import_usage =
        {construction_import= #construction_import used+5,
         construction_literal= #construction_literal used+1,
         construction_binder= #construction_binder used,
         recipe_template= #recipe_template used,
         recipe_index= #recipe_index used,recipe_operand= #recipe_operand used,
         recipe_token= #recipe_token used,
         semantic_input= #semantic_input used+17,
         semantic_output= #semantic_output used+36,
         semantic_template= #semantic_template used+36,
         native_input= #native_input used+17,
         native_output= #native_output used+36,
         native_template= #native_template used+36,
         native_import= #native_import used+18,
         type_work= #type_work used+2504}
      val construction = #construction_limits limits
      val recipes = #recipe_limits construction
      val semantic = #semantic_limits limits
      val native = #native_limits limits
      val ns = #semantic_limits native
      val allows = SmtReplayResourcePolicy.allows
      val _ = if
          allows (#import_limit construction) (#construction_import next)
          andalso allows (#literal_limit construction)
            (#construction_literal next)
          andalso allows (#binder_limit construction)
            (#construction_binder next)
          andalso allows (#template_limit recipes) (#recipe_template next)
          andalso allows (#index_limit recipes) (#recipe_index next)
          andalso allows (#operand_limit recipes) (#recipe_operand next)
          andalso allows (#token_limit recipes) (#recipe_token next)
          andalso allows (#input_limit semantic) 9
          andalso allows (#output_limit semantic) 27
          andalso allows (#template_limit semantic) (#semantic_template next)
          andalso allows (#input_limit ns) 9
          andalso allows (#output_limit ns) 27
          andalso allows (#template_limit ns) (#native_template next)
          andalso allows (#import_limit native) (#native_import next)
          andalso allows (#type_work_limit native) (#type_work next)
        then () else raise ERR "owned_application_denial"
          "cumulative original policy exhausted"
    in next end

  fun complete_owned_application_denial storage caller context birth =
    let
      val retained = owned_application_birth_for storage caller birth
      val saved = original_import_context_for storage caller context
      val FixedStorage held = storage
      val graph = #graph held
      val meter = #meter held
      val paid = #paid saved
      val _ = R.scope_meter_charge meter 384
      val _ = case !(#context retained) of SOME expected =>
          if Portable.pointer_eq(expected,context) then () else
            raise ERR "owned_application_denial" "different captured context"
        | NONE => raise ERR "owned_application_denial" "context is not claimed"
      val _ = if !(#stopped saved) then
        raise ERR "owned_application_denial" "unsupported original encountered"
        else ()
      val _ = if !(#denial_complete saved) then
        raise ERR "owned_application_denial" "denial already completed"
        else ()
      val _ = case (#originals saved,!(#remaining saved)) of
          ([original],[remaining]) =>
            if Portable.pointer_eq(original,#original retained) andalso
                Portable.pointer_eq(remaining,original) andalso
                !(#completed saved)=0 andalso
                List.null (!(#sources saved)) andalso
                List.null (!(#source_rows saved)) andalso
                not (Option.isSome (!(#goal_witness saved))) then () else
              raise ERR "owned_application_denial"
                "different original inventory"
        | _ => raise ERR "owned_application_denial"
          "different original inventory"
      (* Do not reserve any dummy child proof. The actual Source route is
         executed only if needed, with its own admitted native programmes. *)
      val _ = complete_owned_application_source storage caller context birth
      val _ = ignore(original_import_context_for storage caller context)
      val (goal,goal_hash,goal_bucket) =
        case !(#application_source retained) of SOME triple => triple
        | NONE => raise ERR "owned_application_denial"
          "missing issued App Source"
      val first = !(#expected saved)
      val _ = R.scope_meter_charge meter 192
      val goal_fields = case R.scope_lookup_int meter
          (#nodes first,node_id(#node goal)) of SOME fields => fields
        | NONE => raise ERR "owned_application_denial"
          "missing issued App node"
      val _ = if #scope goal_fields=caller andalso #type_id goal_fields=0
          andalso Portable.pointer_eq(#term goal_fields,#original retained)
          andalso Portable.pointer_eq(#original goal,#original retained)
          andalso (case !(#source goal_fields) of SOME anchor =>
            #node anchor= #node goal andalso
            Portable.pointer_eq(#original anchor,#original goal) andalso
            Portable.pointer_eq(#bridge anchor,#bridge goal) | NONE => false)
          andalso (case #view goal_fields of Application _ => true | _ =>
            false)
        then () else raise ERR "owned_application_denial"
          "different App anchor"
      val admitted = reserve_owned_application_denial meter (#limits saved)
        (!(#usage saved))
      val _ = R.scope_meter_charge meter 16
      val _ = #usage saved := admitted
      (* 476 fixed metadata +500 constructor +1528 private REFL. The extra
         constructor104 pays App type_of132 instead of leaf28.
         Negation REFL type_of still follows only the builtin not rator. *)
      val _ = R.scope_meter_charge meter 2504
      val negation = boolSyntax.negation
      val {Name=neg_id,Ty=neg_ty,...} = Term.dest_thy_constid negation
      val bool_name = #Tyop(Type.dest_thy_typeid Type.bool)
      val {Tyop=fun_name,Args,...} = Type.dest_thy_typeid neg_ty
      fun boolean_leaf ty =
        if Type.is_vartype ty then false else
          let val {Tyop,Args,...} = Type.dest_thy_typeid ty
              val {Thy,Name} = KernelSig.name_of_id Tyop
          in case Args of [] =>
              String.size Thy=3 andalso String.size Name=4 andalso
              Tyop=bool_name
            | _ => false end
      val _ = case Args of [domain,range] =>
          if boolean_leaf domain andalso boolean_leaf range then () else
            raise ERR "owned_application_denial" "different negation type"
        | _ => raise ERR "owned_application_denial" "different negation type"
      val _ = R.scope_meter_charge meter 1024
      val _ = case R.scope_lookup_graph_key meter
          (#types first,R.GraphTypeOperator(bool_name,[])) of SOME 0 => ()
        | _ => raise ERR "owned_application_denial"
          "different semantic Bool id"
      val fun_id = case R.scope_lookup_graph_key meter
          (#types first,R.GraphTypeOperator(fun_name,[0,0])) of SOME id => id
        | NONE => raise ERR "owned_application_denial"
          "missing sealed function id"
      val not_key = R.GraphConstant(neg_id,fun_id)
      (* f itself may be not. Reuse its genuine semantic entry instead of
         requiring an empty registry or inventing a duplicate constant. *)
      val (not_node,not_term,not_fields,not_is_new) =
        case R.scope_lookup_graph_key meter (#keys first,not_key) of
            SOME node =>
              let val fields = case R.scope_lookup_int meter
                      (#nodes first,node_id node) of SOME fields => fields
                    | NONE => raise ERR "owned_application_denial"
                        "missing existing negation node"
                  val _ = if #scope fields=caller andalso
                      #type_id fields=fun_id andalso
                      (case #view fields of Constant _ => true | _ => false)
                    then () else raise ERR "owned_application_denial"
                      "different existing negation node"
              in (node,#term fields,fields,false) end
          | NONE =>
              let val node = Node {owner= #owner graph,id= #next first}
                  val fields : entry =
                    {scope=caller,ty=neg_ty,type_id=fun_id,term=negation,
                     view=Constant neg_id,raw=SOME 1,inclusive=SOME 1,
                     source=ref NONE}
              in (node,negation,fields,true) end
      val denial_term = Term.mk_comb(not_term,#original retained)
      val not_hash = Word.fromInt(KernelSig.epoch_of neg_id)
      val code = Word.+(Word.+(Word.*(not_hash,0w37),0w29),
        Word.*(0w17,goal_hash))
      val bucket = Word.toInt(Word.mod
        (Word.+(Word.*(0w37,code),code),Word.fromInt 4093))
      val old_bucket = Array.sub(#imports graph,bucket)
      val goal_old_bucket = Array.sub(#imports graph,goal_bucket)
      val app_id = #next first+(if not_is_new then 1 else 0)
      val app_node = Node {owner= #owner graph,id=app_id}
      val app_key = R.GraphApplication
        (scope_id caller,node_id not_node,node_id(#node goal))
      val _ = case R.scope_lookup_graph_key meter (#keys first,app_key) of
          NONE => () | SOME _ =>
            raise ERR "owned_application_denial" "denial node already present"
      val anchor : source option ref = ref NONE
      val fields : entry =
        {scope=caller,ty= #ty goal_fields,type_id=0,term=denial_term,
         view=Application(not_node,#node goal),raw=SOME 5,
         inclusive=SOME 5,source=anchor}
      val keys = R.scope_put_graph_key meter
        ((if not_is_new then R.scope_put_graph_key meter
            (#keys first,not_key,not_node) else #keys first),app_key,app_node)
      val nodes = R.scope_put_int meter
        ((if not_is_new then R.scope_put_int meter
            (#nodes first,node_id not_node,not_fields) else #nodes first),
         app_id,fields)
      val revision = #revision first+1
      val next : paid_index_snapshot =
        {types= #types first,keys=keys,recent= #recent first,nodes=nodes,
         scopes= #scopes first,reserved= #reserved first,next=app_id+1,
         next_scope= #next_scope first,retirements= #retirements first,
         revision=revision}
      val _ = R.scope_meter_charge meter 512
      val _ = paid_index_close graph paid first
      val _ = if Portable.pointer_eq
          (old_bucket,Array.sub(#imports graph,bucket)) andalso
          Portable.pointer_eq
            (goal_old_bucket,Array.sub(#imports graph,goal_bucket)) then ()
              else
        raise ERR "owned_application_denial" "import bucket changed"
      (* Every native/metadata/R programme and own store is funded before
         REFL. No postproof debit/callback occurs before OWN publication. *)
      val theorem = Thm.REFL denial_term
      val source : source =
        {node=app_node,original=denial_term,bridge=theorem}
      val _ = anchor := SOME source
      val _ = #keys paid := keys
      val _ = #nodes graph := nodes
      val _ = #next graph := app_id+1
      val _ = Array.update(#imports graph,bucket,
        (denial_term,scope_id caller,source)::old_bucket)
      val _ = #validation_changes graph := revision
      val _ = #expected saved := next
      val _ = #goal_witness saved := SOME(goal,goal_hash)
      val _ = #source_rows saved := [(goal,goal_bucket)]
      val _ = #sources saved := [goal]
      val _ = #remaining saved := []
      val _ = #completed saved := 1
      val _ = #denial_bucket saved := SOME bucket
      val _ = #denial_source saved := SOME source
      val _ = #denial_complete saved := true
    in () end

  (* Issued only from a completed, private captured programme. A may retain
     this token, but no caller flag/Source/hash can construct or replace it. *)
  datatype owned_application_completion = OwnedApplicationCompletion of
    {context:original_import_context,goal:source,denied:source,
     revision:IntInf.int,function:Term.term,argument:Term.term}

  fun classified_original_source_preparation_data storage caller context =
    let
      val data = original_source_preparation_data storage caller context
      val OriginalImportContext saved = context
      val FixedStorage held = storage
      val graph = #graph held
      val meter = #meter held
      val first = !(#expected saved)
      val _ = R.scope_meter_charge meter 64
      val (goal,assumptions) = case #originals data of (source,_)::rest =>
          (source,rest)
        | [] => raise ERR "owned_application_completion" "missing issued goal"
      fun fields node =
        let val Node {owner,id} = node
            val _ = if owner= #owner graph then () else
              raise ERR "owned_application_completion"
                "different semantic owner"
        in case R.scope_lookup_int meter (#nodes first,id) of SOME fields =>
          fields
          | NONE => raise ERR "owned_application_completion"
            "missing issued node"
        end
      val goal_fields = fields (#node goal)
      fun same (left:source,right:source) =
        #node left= #node right andalso
        Portable.pointer_eq(#original left,#original right) andalso
        Portable.pointer_eq(#bridge left,#bridge right)
      val completion = case #view goal_fields of
          Variable _ => NONE
        | Constant _ => NONE
        | Application(function_node,argument_node) =>
          let
            val _ = R.scope_meter_charge meter 384
            val _ = if List.null assumptions andalso
                !(#completed saved)=1 andalso #type_id goal_fields=0 andalso
                #raw goal_fields=SOME 3 andalso #inclusive goal_fields=SOME 3
                andalso Portable.pointer_eq(#term goal_fields,#original goal)
              then () else raise ERR "owned_application_completion"
                "not the fixed owned application programme"
            val function_fields = fields function_node
            val argument_fields = fields argument_node
            fun atom fields = case #view (fields:entry) of
                Variable(RigidSource,_) => true | Constant _ => true | _ =>
                  false
            fun typed rows =
              (R.scope_meter_charge meter 32;
               case rows of [] => false
               | OrderedFunctionChild {source,canonical,anchor,type_id}::rest
                 =>
                 if #node source=function_node andalso
                     type_id= #type_id function_fields andalso
                     Portable.pointer_eq(canonical,#term function_fields)
                       andalso
                     Portable.pointer_eq(#original source,canonical) andalso
                     same(source,anchor) then true else typed rest)
            val _ = if atom function_fields andalso atom argument_fields
                andalso #scope function_fields=caller andalso
                #scope argument_fields=caller andalso
                #type_id argument_fields=0 andalso
                #type_id function_fields<>0 andalso
                typed (!(#function_children saved)) then () else
              raise ERR "owned_application_completion"
                "missing typed child issuance"
            val _ = case !(#source argument_fields) of SOME anchor =>
                if #node anchor=argument_node andalso
                    Portable.pointer_eq(#original anchor,#term argument_fields)
                then () else raise ERR "owned_application_completion"
                  "different argument anchor"
              | NONE => raise ERR "owned_application_completion"
                  "missing argument anchor"
            val denied = #1 (#denied data)
            val denied_fields = fields (#node denied)
            val _ = if #scope denied_fields=caller andalso
                #type_id denied_fields=0 andalso #raw denied_fields=SOME 5
                andalso #inclusive denied_fields=SOME 5 andalso
                (case #view denied_fields of Application(_,child) =>
                   child= #node goal | _ => false) then () else
              raise ERR "owned_application_completion" "different owned denial"
            (* Field views alone are not origin. Both Sources are members
               of this exact private captured context, validated by the
               original completion port; the function receipt was issued
               by the actual typed native child programme, not a caller. *)
            val _ = R.scope_meter_charge meter 16
            val _ = ignore(original_import_context_for storage caller context)
          in SOME (OwnedApplicationCompletion
            {context=context,goal=goal,denied=denied,revision= #revision data,
             function= #term function_fields,argument= #term argument_fields})
               end
        | _ => raise ERR "owned_application_completion"
          "unsupported issued programme"
    in {originals= #originals data,denied= #denied data,
      revision= #revision data,application=completion} end

  fun reserve_owned_application_finaliser meter
      (limits:first_boolean_variable_limits) (used:original_import_usage)
      denied_present =
    let
      val _ = R.scope_meter_charge meter 256
      val hypotheses : IntInf.int = if denied_present then 1 else 0
      val native_work : IntInf.int =
        5627+512*(hypotheses+1)+(if denied_present then 2560 else 0)
      val next : original_import_usage =
        {construction_import= #construction_import used,
         construction_literal= #construction_literal used,
         construction_binder= #construction_binder used,
         recipe_template= #recipe_template used,
         recipe_index= #recipe_index used,recipe_operand= #recipe_operand used,
         recipe_token= #recipe_token used,
         semantic_input= #semantic_input used+49+9*hypotheses,
         semantic_output= #semantic_output used+29,
         semantic_template= #semantic_template used+38,
         native_input= #native_input used+49+9*hypotheses,
         native_output= #native_output used+29,
         native_template= #native_template used+38,
         native_import= #native_import used+20,
         type_work= #type_work used+native_work}
      val construction = #construction_limits limits
      val recipes = #recipe_limits construction
      val semantic = #semantic_limits limits
      val native = #native_limits limits
      val ns = #semantic_limits native
      val allows = SmtReplayResourcePolicy.allows
      val admitted =
        allows (#import_limit construction) (#construction_import next)
        andalso allows (#literal_limit construction) (#construction_literal
          next)
        andalso allows (#binder_limit construction) (#construction_binder next)
        andalso allows (#template_limit recipes) (#recipe_template next)
        andalso allows (#index_limit recipes) (#recipe_index next)
        andalso allows (#operand_limit recipes) (#recipe_operand next)
        andalso allows (#token_limit recipes) (#recipe_token next)
        andalso allows (#input_limit semantic) 19
        andalso allows (#output_limit semantic) 19
        andalso allows (#template_limit semantic) (#semantic_template next)
        andalso allows (#input_limit ns) 19
        andalso allows (#output_limit ns) 19
        andalso allows (#template_limit ns) (#native_template next)
        andalso allows (#import_limit native) (#native_import next)
        andalso allows (#type_work_limit native) (#type_work next)
    in if admitted then (next,native_work) else
      raise ERR "owned_application_finalise"
        "cumulative original policy exhausted"
    end

  fun finalise_owned_application_goal storage caller context
      (OwnedApplicationCompletion retained) raw_false =
    let
      (* Identity of this opaque token's context precedes held theorem or
         graph reads. Full expected storage/root authentication follows. *)
      val _ = if Portable.pointer_eq(context,#context retained) then () else
        raise ERR "owned_application_finalise" "different completion context"
      val saved = original_import_context_for storage caller context
      val FixedStorage held = storage
      val meter = #meter held
      val _ = R.scope_meter_charge meter 256
      val data = original_source_preparation_data storage caller context
      fun same (left:source,right:source) =
        #node left= #node right andalso
        Portable.pointer_eq(#original left,#original right) andalso
        Portable.pointer_eq(#bridge left,#bridge right)
      val goal = #goal retained
      val denied = #denied retained
      val _ = case #originals data of [(current,_)] =>
          if same(current,goal) andalso same(#1(#denied data),denied) andalso
              #revision data= #revision retained then () else
            raise ERR "owned_application_finalise" "completion witness changed"
        | _ => raise ERR "owned_application_finalise"
          "different original inventory"
      val _ = R.scope_meter_charge meter 32
      val hypotheses = Thm.hypset raw_false
      val count = IntInf.fromInt(HOLset.numItems hypotheses)
      (* No ordinary assumptions exist on this constructor route. More
         than one distinct hypothesis cannot be a permitted private set. *)
      val _ = if count<=1 then () else raise ERR "owned_application_finalise"
        "hypothesis is not the owned denial"
      val _ = R.scope_meter_charge meter (256+256*count)
      val terms = HOLset.listItems hypotheses
      val _ = R.scope_meter_charge meter 32
      val denied_present = case terms of [] => false | [term] =>
          if Portable.pointer_eq(term,#original denied) then true else
            raise ERR "owned_application_finalise"
              "hypothesis is not the owned denial"
        | _ => raise ERR "owned_application_finalise"
          "hypothesis is not the owned denial"
      fun fixed expected candidate =
        let
          val _ = R.scope_meter_charge meter 16
          val size = String.size expected
          val _ = if size<=8 then () else
            raise ERR "owned_application_finalise" "nonfixed private literal"
          fun bytes index =
            (R.scope_meter_charge meter 8;
             if index=size then true else
               (R.scope_meter_charge meter 8;
                String.sub(candidate,index)=String.sub(expected,index)
                andalso bytes(index+1)))
        in String.size candidate=size andalso bytes 0 end
      val _ = R.scope_meter_charge meter 128
      val conclusion = Thm.concl raw_false
      val genuine_false = Portable.pointer_eq(conclusion,boolSyntax.F) orelse
        (Term.is_const conclusion andalso
         let
           val {Name=id,...} = Term.dest_thy_constid conclusion
           val {Thy,Name} = KernelSig.name_of_id id
         in fixed "bool" Thy andalso fixed "F" Name andalso
            Term.same_const conclusion boolSyntax.F end)
      val _ = if genuine_false then () else
        raise ERR "owned_application_finalise" "replay did not prove F"
      val _ = R.scope_meter_charge meter 32
      val tag = Thm.tag raw_false
      (* Public dest_tag traverses axioms: only its genuinely empty case
         is permitted. Oracles use their actual paid head/byte stream. *)
      val _ = case Tag.axioms_of tag of [] => () | _::_ =>
        raise ERR "owned_application_finalise" "unexpected replay tags"
      val _ = R.scope_meter_charge meter 32
      val (oracles,_) = Tag.dest_tag tag
      fun allowed names =
        (R.scope_meter_charge meter 16;
         case names of [] => true
         | name::rest =>
             (R.scope_meter_charge meter 16;
              fixed "DISK_THM" name andalso allowed rest))
      val _ = if allowed oracles then () else
        raise ERR "owned_application_finalise" "unexpected replay tags"
      val (admitted,native_work) = reserve_owned_application_finaliser meter
        (#limits saved) (!(#usage saved)) denied_present
      val _ = R.scope_meter_charge meter 16
      val _ = #usage saved := admitted
      val _ = R.scope_meter_charge meter (native_work+128)
      val _ = ignore(original_import_context_for storage caller context)
      (* Genuine App-specific native programme; old atomic entry remains
         independently fenced. No debit/callback between these rules. *)
      val canonical = Thm.CCONTR (#original goal) raw_false
      val symmetric = Thm.SYM (#bridge goal)
      val result = Thm.EQ_MP symmetric canonical
    in result end


  (* Closed EMPTY child only. Neither a caller snapshot nor a callback can
     nominate a delta. Staging funds this exact one-use commit before any
     graph store; A finishes its billed action tail before calling commit. *)
  datatype original_proof_scope = OriginalProofScope of
    {owner:unit ref,context:paid_index_snapshot ref,root:scope,
     child:scope,token:unit ref,active:bool ref,closed:bool ref}
  datatype original_proof_scope_plan = OriginalProofScopePlan of
    {owner:unit ref,context:paid_index_snapshot ref,root:scope,
     prior:paid_index_snapshot,predicted:paid_index_snapshot,
     root_active:bool ref,workspace:original_proof_scope,
     opening:bool,used:bool ref,completion_advanced:bool ref}

  fun original_proof_scope_owner storage caller
      (OriginalImportContext saved) (OriginalProofScope workspace) =
    let val FixedStorage expected=storage
    in if #owner expected= #owner workspace andalso
        caller= #root expected andalso caller= #root workspace andalso
        #context workspace= #expected saved then () else
      raise ERR "ordered_proof_scope" "different original workspace owner"
    end

  (* Only the fixed staged commit calls this prepaid constant-size check.
     Its root comparisons are exactly the private R pointer predicates;
     it traverses no tree/list and issues no generic validation credit. *)
  fun original_proof_roots_match (g:graph) (p:paid_index_state)
      (saved:paid_index_snapshot) =
    Portable.pointer_eq(#types saved,!(#types p)) andalso
    Portable.pointer_eq(#keys saved,!(#keys p)) andalso
    Portable.pointer_eq(#recent saved,!(#recent p)) andalso
    R.same_int(#nodes saved,!(#nodes g)) andalso
    R.same_int(#scopes saved,!(#scopes g)) andalso
    R.same_string(#reserved saved,!(#reserved g)) andalso
    #next saved= !(#next g) andalso
    #next_scope saved= !(#next_scope g) andalso
    #retirements saved= !(#scope_retirements g) andalso
    #revision saved= !(#validation_changes g)

  fun stage_original_proof_scope storage caller context =
    let
      val saved=original_import_context_for storage caller context
      val FixedStorage held=storage
      val graph= #graph held
      val meter= #meter held
      (* Local staging512 + fixed commit/pre/postclosure512. Dynamic
         authentic context/path/R insertion work is billed separately. *)
      val _=R.scope_meter_charge meter 1024
      val _=if !(#denial_complete saved) andalso
          not(!(#stopped saved)) then () else
        raise ERR "ordered_proof_scope" "original completion required"
      val _=case !(#remaining saved) of [] => () | _ =>
        raise ERR "ordered_proof_scope" "original occurrences remain"
      val _=case !(#replay_workspace saved) of NONE => () | SOME _ =>
        raise ERR "ordered_proof_scope" "workspace already open"
      val prior= !(#expected saved)
      val root_frame=scope_frame graph caller
      val _=case #parent root_frame of NONE => () | SOME _ =>
        raise ERR "ordered_proof_scope" "original root required"
      val id= #next_scope prior
      val _=if id>0 then () else
        raise ERR "ordered_proof_scope" "invalid next scope identifier"
      val _=case R.scope_lookup_int meter (#scopes prior,id) of NONE => ()
        | SOME _ => raise ERR "ordered_proof_scope"
          "scope identifier is not fresh"
      val child=Scope {owner= #owner held,id=id}
      val active=ref true
      (* The constructor-owned original root bindings are immutable empty.
         Reuse that genuine empty table: no arbitrary bindings/native walk. *)
      val frame={parent=SOME caller,active=active,
        bindings= #bindings root_frame}
      val scopes=R.scope_put_int meter (#scopes prior,id,frame)
      val predicted:paid_index_snapshot=
        {types= #types prior,keys= #keys prior,recent= #recent prior,
         nodes= #nodes prior,scopes=scopes,reserved= #reserved prior,
         next= #next prior,next_scope=id+1,
         retirements= #retirements prior,revision= #revision prior+1}
      val workspace=OriginalProofScope
        {owner= #owner held,context= #expected saved,root=caller,
         child=child,token=ref (),active=active,closed=ref false}
      val plan=OriginalProofScopePlan
        {owner= #owner held,context= #expected saved,root=caller,
         prior=prior,predicted=predicted,root_active= #active root_frame,
         workspace=workspace,opening=true,used=ref false,
         completion_advanced=ref false}
      val _=paid_index_close graph (#paid saved) prior
    in {plan=plan,workspace=workspace,revision= #revision predicted} end

  fun original_proof_scope_for storage caller context
      (workspace as OriginalProofScope fields) =
    let
      val _=original_proof_scope_owner storage caller context workspace
      val saved=original_import_context_for storage caller context
      val FixedStorage held=storage
      val _=R.scope_meter_charge (#meter held) 64
      val _=case !(#replay_workspace saved) of SOME token =>
          if token= #token fields andalso not(!(#closed fields)) andalso
              !(#active fields) then () else
            raise ERR "ordered_proof_scope" "workspace is not open"
        | NONE => raise ERR "ordered_proof_scope" "workspace is not open"
    in #child fields end

  fun stage_original_proof_scope_close storage caller context
      (workspace as OriginalProofScope fields) =
    let
      val _=original_proof_scope_owner storage caller context workspace
      val saved=original_import_context_for storage caller context
      val FixedStorage held=storage
      val graph= #graph held
      val meter= #meter held
      val _=R.scope_meter_charge meter 1024
      val _=case !(#replay_workspace saved) of SOME token =>
          if token= #token fields andalso not(!(#closed fields)) andalso
              !(#active fields) then () else
            raise ERR "ordered_proof_scope" "workspace is not open"
        | NONE => raise ERR "ordered_proof_scope" "workspace is not open"
      val prior= !(#expected saved)
      val root_frame=scope_frame graph caller
      val predicted:paid_index_snapshot=
        {types= #types prior,keys= #keys prior,recent= #recent prior,
         nodes= #nodes prior,scopes= #scopes prior,reserved= #reserved prior,
         next= #next prior,next_scope= #next_scope prior,
         retirements= #retirements prior+1,revision= #revision prior+1}
      val plan=OriginalProofScopePlan
        {owner= #owner held,context= #expected saved,root=caller,
         prior=prior,predicted=predicted,root_active= #active root_frame,
         workspace=workspace,opening=false,used=ref false,
         completion_advanced=ref false}
      val _=paid_index_close graph (#paid saved) prior
    in {plan=plan,revision= #revision predicted} end

  (* No debit, callback, root lookup/traversal, native action or current
     snapshot capture occurs in commit. The staged fixed programme alone
     prepaid these guards/stores. It cannot commit any caller delta. *)
  fun commit_original_proof_scope storage caller
      (context as OriginalImportContext saved)
      (OriginalProofScopePlan plan) =
    let
      val workspace as OriginalProofScope fields= #workspace plan
      val _=original_proof_scope_owner storage caller context workspace
      val FixedStorage held=storage
      val graph= #graph held
      val paid= #paid saved
      val prior= #prior plan
      val predicted= #predicted plan
      val _=if #owner plan= #owner held andalso #root plan=caller andalso
          #context plan= #expected saved andalso not(!(#used plan)) then ()
        else raise ERR "ordered_proof_scope" "stale workspace programme"
      val _=if Type.type_epoch ()= #epoch paid andalso
          Term.term_epoch ()= #symbols paid andalso !(#root_active plan)
          andalso Portable.pointer_eq(prior,!(#expected saved)) andalso
          original_proof_roots_match graph paid prior then () else
        raise ERR "ordered_proof_scope" "workspace programme roots changed"
      val _=if !(#active fields) andalso not(!(#closed fields)) then () else
        raise ERR "ordered_proof_scope" "workspace is not open"
      val _=case (!(#replay_workspace saved),#opening plan) of
          (NONE,true) => ()
        | (SOME token,false) => if token= #token fields then () else
            raise ERR "ordered_proof_scope" "different open workspace"
        | _ => raise ERR "ordered_proof_scope" "workspace phase changed"
      val _= #used plan := true
      val _=if #opening plan then
          (#scopes graph := #scopes predicted;
           #next_scope graph := #next_scope predicted;
           #replay_workspace saved := SOME (#token fields))
        else (#active fields := false;#closed fields := true;
          #scope_retirements graph := #retirements predicted;
          #replay_workspace saved := NONE)
      val _= #validation_changes graph := #revision predicted
      val _= #expected saved := predicted
      val _=if Type.type_epoch ()= #epoch paid andalso
          Term.term_epoch ()= #symbols paid andalso !(#root_active plan)
          andalso original_proof_roots_match graph paid predicted then ()
        else raise ERR "ordered_proof_scope" "closed scope prediction failed"
      val _=if #opening plan then
          (case !(#replay_workspace saved) of SOME token =>
             if token= #token fields andalso !(#active fields) andalso
                 not(!(#closed fields)) then () else
               raise ERR "ordered_proof_scope"
                 "open workspace prediction failed"
           | NONE => raise ERR "ordered_proof_scope"
             "open workspace prediction failed")
        else (case !(#replay_workspace saved) of NONE =>
             if !(#closed fields) andalso not(!(#active fields)) then () else
               raise ERR "ordered_proof_scope"
                 "closed workspace prediction failed"
           | SOME _ => raise ERR "ordered_proof_scope"
             "closed workspace prediction failed")
    in () end

  (* Public-view DATA only. These row IDs are private observation IDs,
     never semantic node IDs or native constructor-origin witnesses. *)
  datatype external_public_head =
      ExternalVariable of string * Type.hol_type
    | ExternalConstant of KernelSig.kernelid * Type.hol_type
    | ExternalApplication
    | ExternalAbstraction
    | ExternalOther
  datatype external_public_row = ExternalPublicRow of
    {original:Term.term,head:external_public_head,children:int list,
     native_type:(Type.hol_type * int) option,
     raw:IntInf.int option,inclusive:IntInf.int option}
  datatype external_public_task = ExternalEnter of Term.term
    | ExternalFinishApplication of Term.term * int
  datatype external_original_stage = ExternalOriginalStage of
    {owner:unit ref,root:scope,context:paid_index_snapshot ref,
     snapshot:paid_index_snapshot,remaining:Term.term list,
     completed:IntInf.int,original:Term.term,
     rows:external_public_row R.int_map,root_row:int,
     observations:IntInf.int,public_views:IntInf.int,
     opaque_binders:IntInf.int,unresolved:IntInf.int,
     raw:IntInf.int option,inclusive:IntInf.int option,
     root_type_known:bool,metric_ceiling:SmtReplayResourcePolicy.limit}
  type external_original_stage_summary =
    {observations:IntInf.int,public_views:IntInf.int,
     opaque_binders:IntInf.int,unresolved:IntInf.int,
     raw:IntInf.int option,inclusive:IntInf.int option,
     root_type_known:bool,revision:IntInf.int,
     semantic_nodes_published:IntInf.int,sources_issued:IntInf.int,
     originals_completed:IntInf.int}

  fun prepare_external_original_stage storage caller context =
    let
      val saved=original_import_context_for storage caller context
      val FixedStorage held=storage
      val meter= #meter held
      val _=R.scope_meter_charge meter 512
      val _=if !(#stopped saved) orelse !(#denial_complete saved) then
        raise ERR "external_original_stage" "original programme is closed"
        else ()
      val remaining= !(#remaining saved)
      val original=case remaining of term::_ => term | [] =>
        raise ERR "external_original_stage" "no current original"
      val completed= !(#completed saved)
      val limits= #limits saved
      val import_limit= #import_limit (#construction_limits limits)
      val semantic= #semantic_limits limits
      val native= #semantic_limits (#native_limits limits)
      fun maximum (SmtReplayResourcePolicy.Uncapped,_) =
            SmtReplayResourcePolicy.Uncapped
        | maximum (_,SmtReplayResourcePolicy.Uncapped) =
            SmtReplayResourcePolicy.Uncapped
        | maximum (SmtReplayResourcePolicy.AtMost a,
            SmtReplayResourcePolicy.AtMost b) =
            SmtReplayResourcePolicy.AtMost(IntInf.max(a,b))
      val ceiling=maximum (#input_limit semantic,
        maximum (#output_limit semantic,maximum (#template_limit semantic,
          maximum (#input_limit native,maximum (#output_limit native,
            #template_limit native)))))
      (* Defined public primitive-call tariff, not a claim to clone or
         bound hidden STD Subst CPU. Every actual exposed view is billed.
         The caller's existing physical import-DAG limit stays separate
         from raw/binder-inclusive summaries and native Type admission. *)
      val _=R.scope_meter_charge meter (32+4093)
      val memo=Array.array(4093,[]:(Term.term * int) list)
      val rows=ref(R.empty_int())
      val next=ref 0
      val observations=ref(0:IntInf.int)
      val public_views=ref(0:IntInf.int)
      val binders=ref(0:IntInf.int)
      val unresolved=ref(0:IntInf.int)
      val fun_name=ref(NONE:KernelSig.kernelid option)
      fun fund_native amount =
        let val admitted=reserve_ordered_extra_native meter limits
              (!(#usage saved)) amount
            val _=R.scope_meter_charge meter 16
            val _= #usage saved:=admitted
        in R.scope_meter_charge meter amount end
      fun public_call () =
        (R.scope_meter_charge meter 16;
         public_views:= !public_views+1)
      fun inspect term =
        (public_call();
         if Term.is_var term then
           (fund_native 64;
            let val (name,ty)=Term.dest_var term
            in ExternalVariable(name,ty) end)
         else (public_call();
           if Term.is_const term then
             (fund_native 128;
              let val {Name,Ty,...}=Term.dest_thy_constid term
              in ExternalConstant(Name,Ty) end)
           else (public_call();
             if Term.is_comb term then ExternalApplication
             else (public_call();if Term.is_abs term then
                 ExternalAbstraction else ExternalOther))))
      fun children term = (public_call();Term.dest_comb term)
      fun text_hash text =
        let val _=R.scope_meter_charge meter 16
            val length=String.size text
            fun loop i code =
              (R.scope_meter_charge meter 8;
               if i=length then code else
                 (R.scope_meter_charge meter 16;
                  loop(i+1)(Word.+(Word.*(code,0w33),
                    Word.fromInt(Char.ord(String.sub(text,i)))))))
        in loop 0 0w17 end
      fun head_code head = case head of
          ExternalVariable(name,_) => text_hash name
        | ExternalConstant(id,_) =>
            (fund_native 6;Word.fromInt(KernelSig.epoch_of id))
        | ExternalAbstraction => 0w19 | _ => 0w17
      (* Bounded public application-path hint only. Each hit is still an
         exact pointer check; no native origin or absence fact is inferred.
         Opaque abstractions never open in the hint. *)
      fun first_child operator operand =
        (R.scope_meter_charge meter 16;
         case inspect operator of ExternalApplication => #2(children operator)
           | _ => operand)
      fun sample depth first term =
        let val _=R.scope_meter_charge meter 64
            val head=inspect term
        in case (depth,head) of
            (0,_) => head_code head
          | (_,ExternalApplication) =>
              let val (f,x)=children term
                  val code=head_code(inspect f)
                  val child=if first then first_child f x else x
              in Word.+(Word.*(code,0w37),
                Word.+(Word.*(0w17,sample(depth-1)first child),0w29)) end
          | _ => head_code head
        end
      fun samples depth term =
        let val _=R.scope_meter_charge meter 64
            val head=inspect term
        in case (depth,head) of
            (0,_) => let val code=head_code head in (code,code) end
          | (_,ExternalApplication) =>
              let val (f,x)=children term
                  val first=first_child f x
                  val (left,right)=if Portable.pointer_eq(first,x) then
                      samples(depth-1)x
                    else (sample(depth-1)true first,sample(depth-1)false x)
                  val prefix=Word.+(Word.*(head_code(inspect f),0w37),0w29)
                  fun mix code=Word.+(prefix,Word.*(0w17,code))
              in (mix left,mix right) end
          | _ => let val code=head_code head in (code,code) end
        end
      fun hint term head =
        let
          val _=R.scope_meter_charge meter 64
          val opened=case head of ExternalApplication => SOME(children term)
            | _ => NONE
          val (left,right)=samples 4 term
          val bucket=Word.toInt(Word.mod
            (Word.+(Word.*(0w37,left),right),Word.fromInt 4093))
        in (opened,bucket) end
      fun lookup term pending =
        (R.scope_meter_charge meter 32;
         case pending of [] => NONE
         | (held,id)::rest => if Portable.pointer_eq(term,held) then SOME id
             else lookup term rest)
      fun row id = case R.scope_lookup_int meter (!rows,id) of
          SOME fields => fields | NONE =>
            raise ERR "external_original_stage" "missing private row"
      fun save term bucket fields =
        let val _=R.scope_meter_charge meter 96
            val id= !next
            val staged=R.scope_put_int meter (!rows,id,fields)
            val held=Array.sub(memo,bucket)
        in rows:=staged;next:=id+1;
          Array.update(memo,bucket,(term,id)::held);id end
      fun protected_function_name () =
        (R.scope_meter_charge meter 32;
         case !fun_name of SOME name => name
        | NONE =>
            (fund_native 80;
             let val {Ty,...}=Term.dest_thy_constid boolSyntax.negation
                 val {Tyop,...}=Type.dest_thy_typeid Ty
                 val _=R.scope_meter_charge meter 16
             in fun_name:=SOME Tyop;Tyop end))
      fun application_type f x =
        (R.scope_meter_charge meter 64;
         case (f,x) of
          (SOME(ty,_),SOME(_,argument_id)) =>
            let
              val expected=protected_function_name()
              val _=fund_native 128
              val _=if Type.is_vartype ty then
                raise ERR "external_original_stage" "nonfunction rator Type"
                else ()
              val {Tyop,Args,...}=Type.dest_thy_typeid ty
              val {Thy,Name}=KernelSig.name_of_id Tyop
              val _=if String.size Thy=3 andalso String.size Name=3
                  andalso Tyop=expected then () else
                raise ERR "external_original_stage" "nonfunction rator Type"
              val (domain,range)=case Args of [domain,range] => (domain,range)
                | _ => raise ERR "external_original_stage" "function arity"
              val domain_id=observe_ordered_native_type storage caller context
                domain
              val range_id=observe_ordered_native_type storage caller context
                range
              val _=R.scope_meter_charge meter 32
              val _=if domain_id=argument_id then () else
                raise ERR "external_original_stage" "public child Types differ"
            in SOME(range,range_id) end
        | _ => NONE)
      fun combine a b = case (a,b) of (SOME x,SOME y) =>
          SOME(SmtReplayResourcePolicy.add_up_to ceiling
            (1,SmtReplayResourcePolicy.add_up_to ceiling (x,y)))
        | _ => NONE
      fun walk pending values =
        (R.scope_meter_charge meter 32;
         case pending of [] => (case values of [root] => root | _ =>
             raise ERR "external_original_stage" "invalid result stack")
         | ExternalEnter term::rest =>
             let
               val head=inspect term
               val (opened,bucket)=hint term head
             in case lookup term (Array.sub(memo,bucket)) of
                 SOME id => walk rest (id::values)
               | NONE =>
                   let
                     val count= !observations+1
                     val _=if SmtReplayResourcePolicy.allows import_limit count
                       then () else raise ERR "import"
                         "application import DAG budget exhausted"
                     val _=R.scope_meter_charge meter 64
                     val _=observations:=count
                   in case opened of SOME(f,x) =>
                       walk (ExternalEnter f::ExternalEnter x::
                         ExternalFinishApplication(term,bucket)::rest) values
                     | NONE =>
                         let
                           val typed=case head of ExternalVariable(_,ty) =>
                               SOME(ty,observe_ordered_native_type storage
                                 caller context ty)
                             | ExternalConstant(_,ty) =>
                               SOME(ty,observe_ordered_native_type storage
                                 caller context ty)
                             | _ => NONE
                           val known=case typed of SOME _ => true | NONE =>
                             false
                           val _=R.scope_meter_charge meter 64
                           val _=case head of ExternalAbstraction =>
                               binders:= !binders+1 | _ => ()
                           val _=if known then () else unresolved:=
                             !unresolved+1
                           val id=save term bucket (ExternalPublicRow
                        {original=term,head=head,children=[],native_type=typed,
                              raw=if known then SOME 1 else NONE,
                              inclusive=if known then SOME 1 else NONE})
                         in walk rest (id::values) end
                   end
             end
         | ExternalFinishApplication(term,bucket)::rest =>
             (case values of x::f::tail =>
               let val ExternalPublicRow left=row f
                   val ExternalPublicRow right=row x
                   val typed=application_type (#native_type left) (#native_type
                     right)
                   val _=R.scope_meter_charge meter 96
                   val _=case typed of SOME _ => ()
                     | NONE => unresolved:= !unresolved+1
                   val id=save term bucket (ExternalPublicRow
                     {original=term,head=ExternalApplication,children=[f,x],
                      native_type=typed,raw=combine (#raw left)(#raw right),
                      inclusive=combine (#inclusive left)(#inclusive right)})
               in walk rest (id::tail) end
              | _ => raise ERR "external_original_stage"
                "missing child results"))
      val root_row=walk [ExternalEnter original] []
      val ExternalPublicRow result=row root_row
      val _=R.scope_meter_charge meter 256
      val current=original_import_context_for storage caller context
      val _=if Portable.pointer_eq(remaining,!(#remaining current)) andalso
          completed= !(#completed current) andalso not(!(#stopped current))
          andalso not(!(#denial_complete current)) then () else
        raise ERR "external_original_stage" "original occurrence changed"
    in ExternalOriginalStage
      {owner= #owner held,root=caller,context= #expected saved,
       snapshot= !(#expected saved),remaining=remaining,completed=completed,
       original=original,rows= !rows,root_row=root_row,
       observations= !observations,public_views= !public_views,
       opaque_binders= !binders,unresolved= !unresolved,
       raw= #raw result,inclusive= #inclusive result,
       root_type_known=Option.isSome(#native_type
         result),metric_ceiling=ceiling}
    end

  fun external_original_stage_summary storage caller context
      (ExternalOriginalStage held) : external_original_stage_summary =
    let
      val FixedStorage expected=storage
      val _=if #owner expected= #owner held andalso caller= #root held
          andalso caller= #root expected then () else
        raise ERR "external_original_stage" "different stage owner"
      val saved=original_import_context_for storage caller context
      val _=if #context held= #expected saved then () else
        raise ERR "external_original_stage" "different stage context"
      val _=R.scope_meter_charge (#meter expected) 128
      val _=if Portable.pointer_eq(#snapshot held,!(#expected saved)) andalso
          Portable.pointer_eq(#remaining held,!(#remaining saved)) andalso
          #completed held= !(#completed saved) andalso
          not(!(#stopped saved)) andalso not(!(#denial_complete saved)) then ()
            else
        raise ERR "external_original_stage" "stage witness changed"
    in {observations= #observations held,public_views= #public_views held,
      opaque_binders= #opaque_binders held,unresolved= #unresolved held,
      raw= #raw held,inclusive= #inclusive held,
      root_type_known= #root_type_known held,
      revision= #revision (#snapshot held),semantic_nodes_published=0,
      sources_issued=0,originals_completed=0}
    end

  (* One immutable App completion successor for ONE actual staged scope
     change. Its revision comes only from the opaque plan, never a caller
     integer/current snapshot/Source/permission callback. Stage1024 funds
     this optional single-use suffix together with the fixed commit. *)
  fun stage_owned_application_completion_for_scope storage caller
      (context as OriginalImportContext saved)
      (OwnedApplicationCompletion retained) (OriginalProofScopePlan plan) =
    let
      val FixedStorage held=storage
      val workspace= #workspace plan
      val _=original_proof_scope_owner storage caller context workspace
      val _=if Portable.pointer_eq(context,#context retained) andalso
          #owner plan= #owner held andalso #root plan=caller andalso
          #context plan= #expected saved andalso not(!(#used plan))
          andalso not(!(#completion_advanced plan)) then () else
        raise ERR "owned_application_scope" "different or consumed scope plan"
      val graph= #graph held
      val paid= #paid saved
      val prior= #prior plan
      val _=if Type.type_epoch ()= #epoch paid andalso
          Term.term_epoch ()= #symbols paid andalso !(#root_active plan)
          andalso #revision retained= #revision prior andalso
          Portable.pointer_eq(prior,!(#expected saved)) andalso
          original_proof_roots_match graph paid prior then () else
        raise ERR "owned_application_scope" "completion scope roots changed"
      (* Monotone even if subsequent allocation/commit/action-tail fails.
         The old completion is untouched. The predicted token remains
         unusable until actual G commit, whose revision/data check is in
         finalise_owned_application_goal before metadata/native admission. *)
      val _= #completion_advanced plan := true
    in OwnedApplicationCompletion
      {context=context,goal= #goal retained,denied= #denied retained,
       revision= #revision (#predicted plan),
       function= #function retained,argument= #argument retained}
    end

end
