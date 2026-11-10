(* Structural decline BEFORE one-attempt Carrier/Beta preparation. *)
structure SmtLib_TraversalRootRecognition :>
    SmtLib_TraversalRootRecognition =
struct
  structure G = SmtReplayGraph
  structure S = SmtReplaySource
  structure W = SmtReplayInvocationWork
  structure F = SmtReplayFocusAdmission
  val _ = SmtReplayFocusAdmission.describe_for
  (* Qualified loader hints retain functions, never invoke providers. *)
  val _ = SmtReplayGraph.closure_child_node
  val _ = SmtReplaySource.owning_scope
  val _ = SmtReplayInvocationWork.validate
  val ERR = Feedback.mk_HOL_ERR "SmtLib_TraversalRootRecognition"
  datatype carrier = NumForall | NumExists | BagForall | BagExists
  type request =
    {graph : G.graph,scope : G.scope,sources : S.sources,
     work : W.portfolio,focus : G.closure_child}
  type admitted_request =
    {graph : G.graph,scope : G.scope,sources : S.sources,
     work : W.portfolio,admission : F.focus}
  type held = {request : request,root : G.scope,limits : W.limits,
               node : G.node,admission : F.focus option,source_limit : int}
  datatype probe = Probe of
    {held : held,carrier : carrier option,beta : bool}

  (* Only fixed public constructors; never destruct an input Term. *)
  val all_id = #Name (Term.dest_thy_constid boolSyntax.universal)
  val exists_id = #Name (Term.dest_thy_constid boolSyntax.existential)
  val num_id = #Tyop (Type.dest_thy_typeid numSyntax.num)
  val fun_id = #Tyop
    (Type.dest_thy_typeid (Term.type_of boolSyntax.negation))

  fun active ({request={graph,scope,sources,work,focus},root,limits,
               node,admission,source_limit} : held) =
    (W.validate work graph root sources limits;
     G.validate_scope graph scope;
     (case admission of NONE => () | SOME held =>
       let val d = F.describe_for
             {graph = graph,scope = scope,sources = sources,work = work} held
       in if #node d = node andalso #source_limit d = source_limit then ()
          else raise ERR "active" "different admitted source profile" end);
     if G.closure_child_node graph scope focus = node then () else
       raise ERR "active" "different retained root";
     if Term.uptodate_term boolSyntax.universal andalso
         Term.uptodate_term boolSyntax.existential andalso
         Term.uptodate_term boolSyntax.negation andalso
         Type.uptodate_type numSyntax.num then () else
       raise ERR "active" "retired fixed root constructors")
    handle primary => (W.close work;raise primary)

  fun invoke held operation =
    (active held;let val result=operation () in active held;result end)
  fun spend (h as {request={work,...},...} : held) amount =
    (active h;W.spend work amount;active h)

  (* Actual KernelSig compares text then epoch. Precharge BOTH name texts
     before comparison, against the SAME remaining invocation allowance.
     This is a Source primitive envelope, not a machine/allocator proof. *)
  fun same_id (held as {request={work,...},...} : held) (a,b) =
    let
      val _ = spend held 1
      val na = KernelSig.name_of_id a
      val nb = KernelSig.name_of_id b
      fun bytes {Thy,Name} =
        IntInf.fromInt (String.size Thy) + IntInf.fromInt (String.size Name)
      val amount = 1 + bytes na + bytes nb
      val limit = IntInf.fromInt (W.work_limit work)
      val _ = if amount <= limit then () else
        raise ERR "same_id" "original comparison allowance exhausted"
      val _ = spend held (IntInf.toInt amount)
    in KernelSig.id_compare (a,b) = EQUAL end

  fun inspect_internal admission
      (request as {graph,scope,sources,work,focus} : request) =
    let
      val root = S.owning_scope sources
      val limits = W.semantic_limits work
      val _ = W.validate work graph root sources limits
      val _ = G.validate_scope graph scope
      val original = G.closure_child_node graph scope focus
      val source_limit = case admission of NONE => #input_limit limits
        | SOME held => #source_limit (F.describe_for
            {graph = graph,scope = scope,sources = sources,work = work} held)
      val held : held =
        {request = request,root = root,limits = limits,node = original,
         admission = admission,source_limit = source_limit}
      fun view child =
        let val _ = spend held 1
            val n = invoke held
              (fn()=>G.closure_child_node graph scope child)
        in (n,invoke held (fn()=>G.view graph n)) end
      fun missing () = raise ERR "inspect"
        "applicable opaque binder requires genuine recorded discovery"
      fun applicable_input () =
        List.app (fn metric =>
          (spend held 1;
           case invoke held (fn()=>G.unfolded_nodes graph metric
               source_limit original) of
               SOME count => if count <= source_limit then () else
                 raise ERR "inspect" "applicable root exceeds original cap"
             | NONE => raise ERR "inspect"
                 "applicable root lacks complete recorded input metrics"))
          [G.RawNodes,G.BinderInclusiveNodes]
      fun number ty =
        (spend held 1;
         if invoke held (fn()=>Type.is_vartype ty) then false else
         let val {Tyop,Args,...} = invoke held
               (fn()=>Type.dest_thy_typeid ty)
         in same_id held (Tyop,num_id) andalso null Args end)
      fun carrier_type ty =
        if number ty then SOME true else
        (spend held 1;
         if invoke held (fn()=>Type.is_vartype ty) then NONE else
         let val {Tyop,Args,...} = invoke held
               (fn()=>Type.dest_thy_typeid ty)
         in if same_id held (Tyop,fun_id) then
              (case Args of [_,range] =>
                 if number range then SOME false else NONE
               | _ => raise ERR "inspect" "malformed function type metadata")
            else NONE
         end)
      (* The cached predicate function domain decides eligibility before
         opening a body or applying an operation's semantic input cap. *)
      fun predicate_domain predicate =
        let val (node,_) = view predicate
            val ty = invoke held (fn()=>G.type_of graph node)
            val _ = spend held 1
            val _ = if invoke held (fn()=>Type.is_vartype ty) then
              raise ERR "inspect" "quantifier predicate lacks function type"
              else ()
            val {Tyop,Args,...} = invoke held
              (fn()=>Type.dest_thy_typeid ty)
        in if same_id held (Tyop,fun_id) then
             (case Args of [domain,_] => domain
              | _ => raise ERR "inspect" "malformed predicate function type")
           else raise ERR "inspect" "quantifier predicate is not a function"
        end
      (* Bound both complete compared types and name bytes under the SAME
         existing template/Work envelope before Type.compare. This is
         nominal source-event admission, not private/machine cost closure. *)
      fun equal_domain left right =
        let val remaining = ref (#template_limit limits)
            val future = ref (0 : IntInf.int)
            fun add amount = future := !future + IntInf.fromInt amount
            fun quote pending =
              (spend held 1;case pending of [] => () | spine::more =>
                (spend held 1;case spine of [] => quote more
                 | ty::rest =>
                   let val _ = if !remaining > 0 then
                         remaining := !remaining-1 else
                         raise ERR "inspect" "binder type portfolio exceeds cap"
                       val _ = spend held 1 val _ = add 2
                   in if invoke held (fn()=>Type.is_vartype ty) then
                        let val name = invoke held (fn()=>Type.dest_vartype ty)
                            val _ = add (String.size name)
                            val _ = spend held 1
                        in quote (rest::more) end
                      else let val {Tyop,Args,...} = invoke held
                                 (fn()=>Type.dest_thy_typeid ty)
                               val {Thy,Name} = KernelSig.name_of_id Tyop
                               val _ = add (String.size Thy + String.size Name)
                               val _ = spend held 2
                           in quote (Args::rest::more) end end))
            val _ = quote [[left,right]]
            val _ = if !future <= IntInf.fromInt (W.work_limit work) then
                spend held (IntInf.toInt (!future)) else
              raise ERR "inspect" "binder type comparison exceeds Work"
        in invoke held (fn()=>Type.compare (left,right)) = EQUAL end
      fun quantify universal predicate =
        let val domain = predicate_domain predicate
        in case carrier_type domain of NONE => NONE
          | SOME natural =>
            (case #2 (view predicate) of
               G.OpaqueRetained => missing ()
             | G.AdmittedBinder _ =>
                 let val _ = applicable_input ()
                     val closure = invoke held
                       (fn()=>G.closure_child_binder graph scope predicate)
                     val data = invoke held
                       (fn()=>G.binder_closure_data graph scope closure)
                     val ty = invoke held
                       (fn()=>G.type_of graph (#binder data))
                     val _ = if equal_domain ty domain then () else
                       raise ERR "inspect" "binder differs from cached domain"
                 in SOME (if natural then
                      (if universal then NumForall else NumExists)
                    else (if universal then BagForall else BagExists)) end
             | _ => NONE)
        end
      fun attempt () =
        let
          val _ = active held
          val result = case #2 (view focus) of
              G.Application _ =>
                let val (rator,rand) = invoke held
                      (fn()=>G.closure_application_children graph scope focus)
                    val (_,operator) = view rator
                    val carrier = case operator of
                        G.Constant id =>
                          if same_id held (id,all_id) then quantify true rand
                          else if same_id held (id,exists_id) then
                            quantify false rand else NONE
                      | _ => NONE
                    val beta = case operator of
                        G.OpaqueRetained => missing ()
                      | G.AdmittedBinder _ =>
                          let val _ = applicable_input ()
                              val c = invoke held
                                (fn()=>G.closure_child_binder
                                  graph scope rator)
                              val d = invoke held
                                (fn()=>G.binder_closure_data graph scope c)
                              val argument = #1 (view rand)
                              val _ = spend held 1
                          in if G.type_id graph argument =
                                G.type_id graph (#binder d) then true else
                               raise ERR "inspect" "invalid beta argument type"
                          end
                      | _ => false
                in (carrier,beta) end
            | _ => (NONE,false)
          val _ = active held
        in Probe {held=held,carrier= #1 result,beta= #2 result} end
    in W.with_step work attempt end
    handle primary => (W.close work;raise primary)

  fun inspect request = inspect_internal NONE request
  fun inspect_admitted
      ({graph,scope,sources,work,admission} : admitted_request) =
    let val d = F.describe_for
          {graph = graph,scope = scope,sources = sources,work = work} admission
    in inspect_internal (SOME admission)
      {graph = graph,scope = scope,sources = sources,work = work,
       focus = #child d} end
    handle primary => (W.close work;raise primary)

  fun carrier (Probe {held,carrier,...}) = (active held;carrier)
  fun beta (Probe {held,beta,...}) = (active held;beta)
  fun node (Probe {held as {node,...},...}) = (active held;node)
  fun validate_for
      {graph,scope,sources,work,focus} (Probe {held,...}) =
    let val original = #request held
        val _ = W.validate work graph (S.owning_scope sources) sources
          (W.semantic_limits work)
        val _ = G.validate_scope graph scope
        val _ = if Portable.pointer_eq (graph,#graph original) andalso
            scope = #scope original andalso
            Portable.pointer_eq (sources,#sources original) andalso
            Portable.pointer_eq (work,#work original) andalso
            Portable.pointer_eq (focus,#focus original) then () else
          raise ERR "validate_for" "different expected root owner"
    in active held end
    handle primary => (W.close work;raise primary)
end
