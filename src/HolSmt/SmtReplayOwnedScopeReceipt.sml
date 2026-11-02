structure SmtReplayOwnedScopeReceipt :> SmtReplayOwnedScopeReceipt =
struct
  structure G = SmtReplayGraph
  structure S = SmtReplaySource
  structure W = SmtReplayInvocationWork
  structure B = SmtLib_GraphBackend
  val ERR = Feedback.mk_HOL_ERR "SmtReplayOwnedScopeReceipt"
  datatype priced_kind = PricedRoot of G.scope_path
    | PricedBinding of G.scope * B.binding_guard
  datatype receipt = Receipt of
    {graph : G.graph,root : G.scope,scope : G.scope,sources : S.sources,
     work : W.portfolio,limits : W.limits,epoch : int,symbols : int,
     guard : unit -> unit,private_guard : unit -> unit}
    | PricedReceipt of
    {graph:G.graph,root:G.scope,scope:G.scope,sources:S.sources,
     work:W.portfolio,limits:W.limits,epoch:int,symbols:int,
     kind:priced_kind,parent:receipt option}
    | PolicyReceipt of
    {graph:G.graph,root:G.scope,scope:G.scope,sources:S.sources,
     work:W.portfolio,limits:SmtReplayResourcePolicy.semantic_policy,
     epoch:int,symbols:int,mode:policy_mode}
  and policy_mode = PolicyUnpriced of
    {guard:unit->unit,private_guard:unit->unit}
    | PolicyPriced of {kind:priced_kind,parent:receipt option}
  fun protected work action = action ()
    handle primary => (W.close work;raise primary)
  (* Every executed receipt visit debits the SAME original Work, including
     ordinary portfolios and recursive parent/lifetime validation. *)
  fun scope_guard_payment work = W.spend_guard_policy work 1
  (* These helpers accept only the private policy case. Callbacks below
     are the module's own recursive description/lifetime functions. *)
  fun describe_policy expected (saved as PolicyReceipt {work,...})
      describe_parent =
    protected expected (fn () =>
      (if Portable.pointer_eq (expected,work) then () else
         raise ERR "description_for" "different original Work";
       let
         val _=scope_guard_payment work
         val PolicyReceipt
           {graph,root,scope,sources,limits,epoch,symbols,mode,...}=saved
         val _=case mode of PolicyUnpriced {guard,...} =>
             (W.validate_policy work graph root sources limits;
              G.validate_scope graph scope;
              if Type.type_epoch ()=epoch andalso
                  Term.term_epoch ()=symbols then () else
                raise ERR "description_for" "retirement epoch changed";
              guard ())
           | PolicyPriced {kind,parent} =>
             ((case kind of PricedRoot path =>
                 W.validate_priced_scope_frame_policy work
                   {graph=graph,root=root,scope=scope,sources=sources,
                    limits=limits,epoch=epoch,symbols=symbols,path=path}
               | PricedBinding (caller,program) =>
                 (W.validate_policy work graph root sources limits;
                  W.validate_backend_binding_guard work caller program;
                  if Type.type_epoch ()=epoch andalso
                      Term.term_epoch ()=symbols then () else
                    raise ERR "description_for" "retirement epoch changed"));
              case parent of NONE=>()
                | SOME held=>ignore (describe_parent work held))
       in {graph=graph,root=root,scope=scope,sources=sources,
           limits=limits} end))
    | describe_policy expected _ _ = protected expected (fn () =>
        raise ERR "description_for" "not a policy receipt")
  fun lifetime_policy expected (saved as PolicyReceipt {work,...})
      validate_parent =
    protected expected (fn () =>
      (if Portable.pointer_eq (expected,work) then () else
         raise ERR "validate_lifetime_for" "different original Work";
       let
         val _=scope_guard_payment work
         val PolicyReceipt
           {graph,root,scope,sources,limits,epoch,symbols,mode,...}=saved
         fun ordinary () =
           (W.validate_policy work graph root sources limits;
            G.validate_scope graph scope;
            if Type.type_epoch ()=epoch andalso
                Term.term_epoch ()=symbols then () else
              raise ERR "validate_lifetime_for" "retirement epoch changed")
         fun priced kind = case kind of PricedRoot path =>
               W.validate_priced_scope_frame_policy work
                 {graph=graph,root=root,scope=scope,sources=sources,
                  limits=limits,epoch=epoch,symbols=symbols,path=path}
           | PricedBinding (caller,program) =>
               (W.validate_policy work graph root sources limits;
                W.validate_backend_binding_guard work caller program;
                if Type.type_epoch ()=epoch andalso
                    Term.term_epoch ()=symbols then () else
                  raise ERR "validate_lifetime_for" "retirement epoch changed")
         val _=case mode of PolicyUnpriced {private_guard,...} =>
             (ordinary ();private_guard ();ordinary ())
           | PolicyPriced {kind,parent} =>
             (priced kind;
              case kind of PricedRoot _=>()
                | PricedBinding _=>
                  ((case parent of NONE=>()
                      | SOME held=>validate_parent work held);
                   priced kind))
       in () end))
    | lifetime_policy expected _ _ = protected expected (fn () =>
        raise ERR "validate_lifetime_for" "not a policy receipt")

  fun description_for expected (Receipt
      {graph,root,scope,sources,work,limits,epoch,symbols,guard,...}) =
    protected expected (fn () =>
      (if Portable.pointer_eq (expected,work) then () else
         raise ERR "description_for" "different original Work";
       scope_guard_payment work;
       W.validate work graph root sources limits;G.validate_scope graph scope;
       if Type.type_epoch () = epoch andalso Term.term_epoch () = symbols
         then () else raise ERR "description_for" "retirement epoch changed";
       guard ();
       {graph = graph,root = root,scope = scope,sources = sources}))
    | description_for expected (PricedReceipt
        {graph,root,scope,sources,work,limits,epoch,symbols,kind,parent}) =
      protected expected (fn () =>
        (if Portable.pointer_eq (expected,work) then () else
           raise ERR "description_for" "different original Work";
         scope_guard_payment work;
         (case kind of PricedRoot path =>
             W.validate_priced_scope_frame work
               {graph=graph,root=root,scope=scope,sources=sources,
                limits=limits,epoch=epoch,symbols=symbols,path=path}
           | PricedBinding (caller,program) =>
               (W.validate work graph root sources limits;
                W.validate_backend_binding_guard work caller program;
                if Type.type_epoch ()=epoch andalso
                    Term.term_epoch ()=symbols then () else
                  raise ERR "description_for" "retirement epoch changed"));
         (case parent of NONE => ()
           | SOME held => ignore (description_for work held));
         {graph=graph,root=root,scope=scope,sources=sources}))
    | description_for expected (saved as PolicyReceipt _) =
      let val data=describe_policy expected saved description_for
      in {graph= #graph data,root= #root data,scope= #scope data,
        sources= #sources data} end
  fun validate_lifetime_for expected (Receipt
      {graph,root,scope,sources,work,limits,epoch,symbols,private_guard,...}) =
    protected expected (fn () =>
      (if Portable.pointer_eq (expected,work) then () else
         raise ERR "validate_lifetime_for" "different original Work";
       scope_guard_payment work;
       W.validate work graph root sources limits;
       G.validate_scope graph scope;
       if Type.type_epoch ()=epoch andalso Term.term_epoch ()=symbols then ()
         else raise ERR "validate_lifetime_for" "retirement epoch changed";
       private_guard ();
       W.validate work graph root sources limits;
       G.validate_scope graph scope;
       if Type.type_epoch ()=epoch andalso Term.term_epoch ()=symbols then ()
         else raise ERR "validate_lifetime_for" "retirement epoch changed"))
    | validate_lifetime_for expected (PricedReceipt
        {graph,root,scope,sources,work,limits,epoch,symbols,kind,parent}) =
      protected expected (fn () =>
        let
          val _ = if Portable.pointer_eq (expected,work) then () else
            raise ERR "validate_lifetime_for" "different original Work"
          val _ = scope_guard_payment work
          fun guard () = case kind of PricedRoot path =>
                W.validate_priced_scope_frame work
                  {graph=graph,root=root,scope=scope,sources=sources,
                   limits=limits,epoch=epoch,symbols=symbols,path=path}
            | PricedBinding (caller,program) =>
                (W.validate work graph root sources limits;
                 W.validate_backend_binding_guard work caller program;
                 if Type.type_epoch ()=epoch andalso
                     Term.term_epoch ()=symbols then () else
                   raise ERR "validate_lifetime_for"
                     "retirement epoch changed")
          (* The root has no parent or callback between its two former
             identical passes. Execute and pay its genuine frame program
             once on EVERY outer lifetime check. Binding still brackets
             the parent traversal with both original local passes. *)
          val _ = guard ()
          val _ = case kind of PricedRoot _ => ()
            | PricedBinding _ =>
                ((case parent of NONE => ()
                    | SOME held => validate_lifetime_for work held);
                 guard ())
        in () end)
    | validate_lifetime_for expected (saved as PolicyReceipt _) =
        lifetime_policy expected saved validate_lifetime_for
  fun root_legacy work = protected work (fn () => W.with_step work (fn () =>
    let val sources = W.original_sources work
        val graph = S.owning_graph sources val scope = S.owning_scope sources
        val limits = W.semantic_limits work
        val _ = W.validate work graph scope sources limits
        val _ = W.spend work 1
    in Receipt {graph = graph,root = scope,scope = scope,sources = sources,
      work = work,limits = limits,epoch = Type.type_epoch (),
      symbols = Term.term_epoch (),guard = fn () => (),
      private_guard = fn () => ()} end))
  fun root work = case W.priced_root_scope_path work of
      NONE => root_legacy work
    | SOME path => protected work (fn () => W.with_step work (fn () =>
        let
          val sources = W.original_sources work
          val _ = W.spend work 6
          val owner = S.owner_for_scope_guard sources
          val graph = #graph owner val scope = #scope owner
          val limits = W.semantic_limits work
          val _ = W.validate work graph scope sources limits
          val _ = W.spend work 16
        in PricedReceipt {graph=graph,root=scope,scope=scope,sources=sources,
          work=work,limits=limits,epoch=Type.type_epoch (),
          symbols=Term.term_epoch (),kind=PricedRoot path,parent=NONE} end))
  fun body work parent child = protected work (fn () =>
    let val incoming = description_for work parent
    in W.with_step work (fn () =>
      let val graph = #graph incoming val caller = #scope incoming
          val _ = W.spend work 1
          val node = G.closure_child_node graph caller child
          val closure = G.closure_child_binder graph caller child
          val data = G.binder_closure_data graph caller closure
          val _ = if #node data = node then () else
            raise ERR "body" "different authentic binder closure"
          val frame = #body_frame data
          fun guard () =
            (ignore (description_for work parent);
             if G.closure_child_node graph caller child = node andalso
                 #body_frame (G.binder_closure_data graph caller closure) = frame
               then () else raise ERR "body" "held binder path changed")
          val result = Receipt {graph = graph,root = #root incoming,
            scope = frame,sources = #sources incoming,work = work,
            limits = W.semantic_limits work,epoch = Type.type_epoch (),
            symbols = Term.term_epoch (),guard = guard,
          private_guard = fn () => validate_lifetime_for work parent}
          val _ = guard ()
      in result end)
    end)
  (* The expected Work and genuine parent are authenticated before any
     potentially retired foreign parser/backend frame is activated. *)
  fun binding_legacy work parent origin = protected work (fn () =>
    let val incoming = description_for work parent
        val owner = SmtLib_GraphBackend.binding_origin_owner origin
        val graph = #graph incoming val caller = #scope incoming
        val _ = if Portable.pointer_eq (#graph owner,graph) andalso
            #parent_scope owner = caller then () else
          raise ERR "binding" "different genuine frontend parent"
        val data = SmtLib_GraphBackend.binding_origin_data graph caller origin
        val frame = #scope data
    in W.with_step work (fn () =>
      let
        fun guard () =
          (ignore (description_for work parent);
           if #scope (SmtLib_GraphBackend.binding_origin_data
               graph caller origin) = frame then () else
             raise ERR "binding" "held frontend child changed")
        val _ = W.spend work 1
        val result = Receipt {graph = graph,root = #root incoming,
          scope = frame,sources = #sources incoming,work = work,
          limits = W.semantic_limits work,epoch = Type.type_epoch (),
          symbols = Term.term_epoch (),guard = guard,
          private_guard = fn () =>
            (validate_lifetime_for work parent;
             if #scope (SmtLib_GraphBackend.binding_origin_data
                 graph caller origin)=frame then () else
               raise ERR "binding" "held private lexical child changed")}
        val _ = guard ()
      in result end)
    end)
  fun binding work parent origin = case W.priced_root_scope_path work of
      NONE => binding_legacy work parent origin
    | SOME _ => protected work (fn () =>
        let val incoming = description_for work parent
        in W.with_step work (fn () =>
          let
            val caller = #scope incoming
            val program = case W.prepare_backend_binding_guard work caller
                origin of SOME value => value | NONE =>
                  raise ERR "binding" "priced Work lost its private mode"
            val data = B.binding_guard_data program
            val _ = W.spend work 16
            val result = PricedReceipt {graph= #graph incoming,
              root= #root incoming,scope= #scope data,
              sources= #sources incoming,work=work,
              limits=W.semantic_limits work,epoch=Type.type_epoch (),
              symbols=Term.term_epoch (),kind=PricedBinding (caller,program),
              parent=SOME parent}
            val _ = ignore (description_for work result)
          in result end)
        end)

  fun description_with_policy_for expected
      (saved as PolicyReceipt _) =
        describe_policy expected saved description_with_policy_for
    | description_with_policy_for expected saved =
      protected expected (fn () =>
        let val data=description_for expected saved
            val limits=W.semantic_policy expected
        in {graph= #graph data,root= #root data,scope= #scope data,
          sources= #sources data,limits=limits} end)
  val validate_lifetime_with_policy_for=validate_lifetime_for

  fun policy_root_legacy work = protected work (fn () =>
    W.with_step work (fn () =>
    let val sources = W.original_sources work
        val graph = S.owning_graph sources val scope = S.owning_scope sources
        val limits = W.semantic_policy work
        val _ = W.validate_policy work graph scope sources limits
        val _ = W.spend_policy work 1
    in PolicyReceipt {graph = graph,root = scope,scope = scope,
      sources = sources,
      work = work,limits = limits,epoch = Type.type_epoch (),
      symbols = Term.term_epoch (),mode=PolicyUnpriced {guard = fn () => (),
      private_guard = fn () => ()}} end))
  fun root_with_policy work = case W.priced_root_scope_path work of
      NONE => policy_root_legacy work
    | SOME path => protected work (fn () => W.with_step work (fn () =>
        let
          val sources = W.original_sources work
          val _ = W.spend_policy work 6
          val owner = S.owner_for_scope_guard sources
          val graph = #graph owner val scope = #scope owner
          val limits = W.semantic_policy work
          val _ = W.validate_policy work graph scope sources limits
          val _ = W.spend_policy work 16
        in PolicyReceipt {graph=graph,root=scope,scope=scope,sources=sources,
          work=work,limits=limits,epoch=Type.type_epoch (),
          symbols=Term.term_epoch (),
          mode=PolicyPriced {kind=PricedRoot path,parent=NONE}} end))
  fun body_with_policy work parent child = protected work (fn () =>
    let val incoming = description_with_policy_for work parent
    in W.with_step work (fn () =>
      let val graph = #graph incoming val caller = #scope incoming
          val _ = W.spend_policy work 1
          val node = G.closure_child_node graph caller child
          val closure = G.closure_child_binder graph caller child
          val data = G.binder_closure_data graph caller closure
          val _ = if #node data = node then () else
            raise ERR "body" "different authentic binder closure"
          val frame = #body_frame data
          fun guard () =
            (ignore (description_with_policy_for work parent);
             if G.closure_child_node graph caller child = node andalso
                 #body_frame (G.binder_closure_data
                   graph caller closure) = frame
               then () else raise ERR "body" "held binder path changed")
          val result = PolicyReceipt {graph = graph,root = #root incoming,
            scope = frame,sources = #sources incoming,work = work,
            limits = W.semantic_policy work,epoch = Type.type_epoch (),
            symbols = Term.term_epoch (),mode=PolicyUnpriced {guard = guard,
          private_guard = fn () =>
            validate_lifetime_with_policy_for work parent}}
          val _ = guard ()
      in result end)
    end)
  (* The expected Work and genuine parent are authenticated before any
     potentially retired foreign parser/backend frame is activated. *)
  fun policy_binding_legacy work parent origin = protected work (fn () =>
    let val incoming = description_with_policy_for work parent
        val owner = SmtLib_GraphBackend.binding_origin_owner origin
        val graph = #graph incoming val caller = #scope incoming
        val _ = if Portable.pointer_eq (#graph owner,graph) andalso
            #parent_scope owner = caller then () else
          raise ERR "binding" "different genuine frontend parent"
        val data = SmtLib_GraphBackend.binding_origin_data graph caller origin
        val frame = #scope data
    in W.with_step work (fn () =>
      let
        fun guard () =
          (ignore (description_with_policy_for work parent);
           if #scope (SmtLib_GraphBackend.binding_origin_data
               graph caller origin) = frame then () else
             raise ERR "binding" "held frontend child changed")
        val _ = W.spend_policy work 1
        val result = PolicyReceipt {graph = graph,root = #root incoming,
          scope = frame,sources = #sources incoming,work = work,
          limits = W.semantic_policy work,epoch = Type.type_epoch (),
          symbols = Term.term_epoch (),mode=PolicyUnpriced {guard = guard,
          private_guard = fn () =>
            (validate_lifetime_with_policy_for work parent;
             if #scope (SmtLib_GraphBackend.binding_origin_data
                 graph caller origin)=frame then () else
               raise ERR "binding" "held private lexical child changed")}}
        val _ = guard ()
      in result end)
    end)
  fun binding_with_policy work parent origin =
    case W.priced_root_scope_path work of
      NONE => policy_binding_legacy work parent origin
    | SOME _ => protected work (fn () =>
        let val incoming = description_with_policy_for work parent
        in W.with_step work (fn () =>
          let
            val caller = #scope incoming
            val program = case W.prepare_backend_binding_guard work caller
                origin of SOME value => value | NONE =>
                  raise ERR "binding" "priced Work lost its private mode"
            val data = B.binding_guard_data program
            val _ = W.spend_policy work 16
            val result = PolicyReceipt {graph= #graph incoming,
              root= #root incoming,scope= #scope data,
              sources= #sources incoming,work=work,
              limits=W.semantic_policy work,epoch=Type.type_epoch (),
              symbols=Term.term_epoch (),
              mode=PolicyPriced {kind=PricedBinding (caller,program),
              parent=SOME parent}}
            val _ = ignore (description_with_policy_for work result)
          in result end)
        end)

  fun binding_value_with_policy work parent owner origin =
    protected work (fn () =>
    let
      val incoming = description_with_policy_for work parent
      val _ = SmtReplayOwnedParserValue.validate_for work owner
      val caller = #scope incoming
      val saved = W.with_step work (fn () =>
        SmtReplayOwnedParserValue.prepare_binding_for work owner caller origin)
      fun guard () =
        (ignore (description_with_policy_for work parent);
         SmtReplayOwnedParserValue.validate_for work owner;
         W.validate_value_backend_binding_guard work saved)
      val data = W.value_backend_binding_data_for work saved
      val result = PolicyReceipt
        {graph= #graph incoming,root= #root incoming,scope= #scope data,
         sources= #sources incoming,work=work,
         limits=W.semantic_policy work,epoch=Type.type_epoch (),
         symbols=Term.term_epoch (),
         mode=PolicyUnpriced {guard=guard,private_guard=guard}}
      val _ = guard ()
    in result end)
end
