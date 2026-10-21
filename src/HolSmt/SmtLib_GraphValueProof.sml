(* Typed syntax ownership and lifetime, separate from checked inference. *)
structure SmtLib_GraphValueProof :> SmtLib_GraphValueProof =
struct
  structure G = SmtReplayGraph
  structure W = SmtReplayInvocationWork
  structure S = SmtReplaySource
  structure GP = SmtLib_GraphPreprocess
  structure F = SmtLib_GraphFrontend
  structure B = SmtLib_GraphBackend
  structure PV = SmtLib_GraphParserValue
  structure M = SmtLib_GraphParserMapping
  structure MD = SmtLib_GraphDeclarationMetadata
  val ERR = Feedback.mk_HOL_ERR "SmtLib_GraphValueProof"
  type private_binding =
    {lexical_scope:G.scope,scope:G.scope,marker:PV.value,kind:string,
     source:PV.value option}
  type 'proof contents =
    {proof:'proof,context:PV.context,metadata:MD.metadata,
     graph:G.graph,scope:G.scope,solver:string,
     versions:{requested:string,resolved:string},
     variables:F.value_solver_variable list,
     private_bindings:private_binding list}
  type 'proof parsed =
    {proof:'proof,terms:F.value_term list,
     bindings:F.value_scoped_session list,close:unit -> unit}
  datatype 'proof packet = Packet of
    {work:W.portfolio,query:GP.graph_query,sources:S.sources,
     limits:SmtReplayResourcePolicy.semantic_policy,
     mapping:M.mapping,contents:'proof contents,
     backend:PV.value B.backend,
     owner:SmtReplayOwnedParserValue.owner,
     terms:F.value_term list,bindings:F.value_scoped_session list,
     assertions:PV.value list option,
     epoch:int,symbols:int,closed:bool ref,revision:IntInf.int ref,
     close:unit -> unit}

  fun validate expected input (Packet
      {work,query,sources,limits,mapping,contents,backend,terms,bindings,
       epoch,symbols,closed,revision,assertions,...}) =
    ((if Portable.pointer_eq (expected,work) andalso
          Portable.pointer_eq (input,query) then () else
        raise ERR "validate" "different original Work or exact query";
      if !closed then raise ERR "validate" "Value packet is closed" else ();
      let
        val graph = #graph contents val scope = #scope contents
        val context = #context contents
        val _ = W.validate_policy expected graph scope sources limits
        val _ = if Type.type_epoch ()=epoch andalso
            Term.term_epoch ()=symbols then () else
          raise ERR "validate" "packet declaration lifetime changed"
        val _ = PV.validate_for context graph scope
        val _ = PV.validate context
        val _ = ignore (M.types mapping)
        (* A cached packet revision cannot hide retirement of a Mapping
           assertion's owned parser child. NONE performs no new traversal. *)
        val _=case assertions of NONE=>()|SOME values=>
          let fun live []=PV.validate context
                | live(value::rest)=
                    (PV.spend context 1;PV.usable context scope value;
                     live rest)
          in live values end
        val current = G.validation_revision graph scope
        fun term ({scope,node,...}:F.value_term) =
          (PV.spend context 1;PV.usable context scope node)
        fun binding (saved as F.ScopedSession
            {session,variables,scope=child,...}) =
          let val _ = if Portable.pointer_eq
                  (#backend (#reader session),backend) then () else
                raise ERR "validate" "different parser binding backend"
              val origin = F.scoped_session_origin saved
              val owner = F.scoped_origin_owner origin
              val _ = if Portable.pointer_eq (#graph owner,graph) andalso
                  #scope owner=child andalso
                  G.scope_visible graph child scope then () else
                raise ERR "validate" "proof binding escaped query root"
              val _ = ignore ((#namespace session) ())
          in List.app (fn value =>
            (PV.spend context 1;PV.usable context child value)) variables end
        fun variable ({node,lexical,scope}:F.value_solver_variable) =
          (PV.spend context 1;
           if Term.is_var lexical andalso
               Type.compare (PV.type_of context node,
                 Term.type_of lexical)=EQUAL andalso
               PV.scope_of context node=scope then () else
             raise ERR "validate" "incompatible solver variable";
           case PV.view context node of
               PV.Variable (G.SolverFlexible,_) => ()
             | _ => raise ERR "validate" "rigid solver inventory value")
        fun private ({scope,marker,source,...}:private_binding) =
          (PV.spend context 1;
           if PV.scope_of context marker=scope then () else
             raise ERR "validate" "private construction scope changed";
           (case PV.view context marker of
                PV.Variable (G.SolverFlexible,_) => ()
              | _ => raise ERR "validate" "private marker is rigid");
           Option.app (PV.usable context scope) source)
      in if !revision=current then () else
        (GP.validate_query_with_policy expected input;
         List.app term terms;List.app binding bindings;
         List.app variable (#variables contents);
         List.app private (#private_bindings contents);
         PV.validate context;
         if G.validation_revision graph scope=current then revision:=current
           else raise ERR "validate" "graph publication during validation")
      end) handle primary => (W.close expected;raise primary))

  fun new expected query
      {factory:SmtLib_GraphValueTranslation.session,metadata,proof:'proof,
       terms,bindings,requested_version,close} =
    ((let
      val _ = GP.validate_query_with_policy expected query
      val sources = W.original_sources expected
      val {graph,scope} = S.owner_for_scope_guard sources
      val mapping = MD.mapping_for graph scope metadata
      val context = #context factory
      val _ = PV.validate_for context graph scope
      val reader = #reader (#session factory)
      val _ = if Portable.pointer_eq (#graph reader,graph) andalso
          #scope reader=scope then () else
        raise ERR "new" "different Value reader owner"
      val variables = (#solver_variables reader) ()
      (* Temporary lexical LET/abstraction frames may already be closed.
         Their labels are historical DATA. The retained construction scope
         and the actual flexible value carry all usable lifetime identity. *)
      fun private ({scope,marker,kind,source}:F.value_private_binding) =
        (PV.spend context 1;
         {lexical_scope=scope,scope=PV.scope_of context marker,
          marker=marker,kind=kind,source=source}:private_binding)
      val private_bindings = List.map private ((#private_bindings reader) ())
      val contents:'proof contents =
        {proof=proof,context=context,metadata=metadata,graph=graph,scope=scope,
         solver= #solver reader,
         versions={requested=requested_version,resolved= #version reader},
         variables=variables,private_bindings=private_bindings}
      val assertion_values= #assertions factory
      val _=case assertion_values of NONE=>()|SOME _=>PV.spend context 2
      val packet = Packet
        {work=expected,query=query,sources=sources,
         limits=W.semantic_policy expected,mapping=mapping,contents=contents,
         backend= #backend reader,owner= #owner factory,
         terms=terms,bindings=bindings,assertions=assertion_values,
         epoch=Type.type_epoch (),
         symbols=Term.term_epoch (),closed=ref false,
         revision=ref (~1:IntInf.int),close=close}
      val _ = validate expected query packet
    in packet end) handle primary => (W.close expected;raise primary))

  fun create expected query
      {options,metadata,description,requested_version,tokens} parse =
    ((let
      val factory = SmtLib_GraphValueTranslation.create_session_with_policy
        expected query options metadata description tokens
      val pending = ref NONE
      fun finish close =
        let val parsed = Exn.capture close ()
            val released = Exn.capture (#close factory) ()
        in case parsed of Exn.Exn primary => raise primary
          | Exn.Res () => Exn.release released end
      fun run () =
        let val {proof,terms,bindings,close} = parse factory
            val _ = pending:=SOME close
            val packet = new expected query
              {factory=factory,metadata=metadata,proof=proof,terms=terms,
               bindings=bindings,requested_version=requested_version,
               close=fn () => finish close}
            val _ = pending:=NONE
        in packet end
      val outcome = Exn.capture (fn () => W.with_step expected run) ()
    in case outcome of Exn.Res packet => packet
      | Exn.Exn primary =>
          (ignore (Exn.capture (fn () =>
             Option.app (fn close => close ()) (!pending)) ());
           ignore (Exn.capture (#close factory) ());raise primary)
    end) handle primary => (W.close expected;raise primary))

  fun contents_with_policy_for expected query
      (packet as Packet {contents,...}) =
    (validate expected query packet;contents)
  fun assertions_with_policy_for expected query
      (packet as Packet {assertions,...}) =
    (validate expected query packet;assertions)
  fun binding_scope_with_policy expected query
      (packet as Packet {owner,bindings,...}) parent binding =
    ((let
      val origin = W.with_step expected (fn () =>
        let
          val _ = validate expected query packet
          val actual = F.scoped_session_origin binding
          fun member [] = false
            | member (held::rest) =
                (W.spend_policy expected 1;
                 Portable.pointer_eq (actual,F.scoped_session_origin held)
                 orelse member rest)
          val _ = if member bindings then () else
            raise ERR "binding_scope" "binding is not part of actual packet"
        in F.scoped_session_binding_origin binding end)
    in SmtReplayOwnedScopeReceipt.binding_value_with_policy
      expected parent owner origin end)
     handle primary => (W.close expected;raise primary))
  structure BinderScope=SmtReplayOwnedScopeReceipt
  datatype binding_frame = BindingFrame of
    {work:W.portfolio,query:GP.graph_query,guard:unit -> unit,
     context:PV.context,parent:BinderScope.receipt,
     frame:BinderScope.receipt,
     binding:W.value_binding_guard}

  fun prepare_binding_frame_with_policy expected query
      (packet as Packet {owner,...}) parent saved =
    ((let
      (* The existing authentic member-origin port owns its actions. *)
      val frame=binding_scope_with_policy expected query packet parent saved
      val result=W.with_step expected (fn()=>
        let
          val contents=contents_with_policy_for expected query packet
          val parent_data=BinderScope.description_with_policy_for
            expected parent
          val origin=F.scoped_session_binding_origin saved
          val binding=SmtReplayOwnedParserValue.prepare_binding_for
            expected owner (#scope parent_data) origin
          val _=W.spend_policy expected 9
          fun guard ()=validate expected query packet
        in BindingFrame {work=expected,query=query,guard=guard,
          context= #context contents,parent=parent,frame=frame,
          binding=binding} end)
    in result end) handle primary=>(W.close expected;raise primary))

  fun binding_frame_data_for expected input
      (BindingFrame {work,query,guard,context,parent,frame,binding}) =
    ((let
      val _=if Portable.pointer_eq(expected,work) andalso
          Portable.pointer_eq(input,query) then () else
        raise ERR "binding_frame" "different original Work or exact query"
      val _=guard ()
      val parent_data=BinderScope.description_with_policy_for
        expected parent
      val data=BinderScope.description_with_policy_for
        expected frame
      val actual=W.value_backend_binding_data_for expected binding
      val _=W.spend_policy expected 18
      val _=if #scope data= #scope actual andalso
          Portable.pointer_eq(#graph data,#graph parent_data) andalso
          #root data= #root parent_data then () else
        raise ERR "binding_frame" "different authentic binder geometry"
      val _=guard ()
    in {context=context,graph= #graph data,root= #root data,
      scope= #scope data,parent=parent,frame=frame,
      variables= #variables actual,descriptors= #descriptors actual,
      binders= #binders actual} end)
     handle primary=>(W.close expected;raise primary))

  fun close (Packet {closed,close,...}) =
    if !closed then () else (closed:=true;close ())
end
