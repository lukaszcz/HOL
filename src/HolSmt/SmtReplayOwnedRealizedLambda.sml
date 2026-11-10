(* Actual binder operands are fully inventoried: no comparison-hole ABS. *)
structure SmtReplayOwnedRealizedLambda :> SmtReplayOwnedRealizedLambda =
struct
  structure G = SmtReplayGraph
  structure S = SmtReplaySource
  structure W = SmtReplayInvocationWork
  structure Scope = SmtReplayOwnedScopeReceipt
  structure Q = SmtReplayFocusAdmission
  structure Core = SmtReplayOwnedLargeProofCore
  val ERR = Feedback.mk_HOL_ERR "SmtReplayOwnedRealizedLambda"
  type owner = {graph : G.graph,root : G.scope,scope : G.scope,
    sources : S.sources,work : W.portfolio,limits : W.limits,
    epoch : int,symbols : int,frame : Scope.receipt,admission : Q.focus,
    body : Core.result,closure : G.binder_closure,
    child : G.closure_child,source : G.node,binder : G.node,
    left : G.node,right : G.node,body_frame : G.scope,
    declaring : G.scope,node_frame : G.scope}
  datatype held = Child of G.scope * G.closure_child
                | Profile of G.scope * G.opaque_profile
  datatype phase = Ready | Running | Complete
  datatype plan = Plan of {owner : owner,held : held list,
    types : Type.hol_type list,policy : Type.hol_type -> unit,
    state : phase ref}
  datatype result = Result of
    {plan : plan,target : G.node,child : G.closure_child,theorem : Thm.thm}
  type size = {raw : IntInf.int,inc : IntInf.int,ann : IntInf.int,
    ty : IntInf.int,type_bytes : IntInf.int,bytes : IntInf.int}
  fun protected work action = action ()
    handle primary => (W.close work;raise primary)
  fun active (own : owner) =
    let val frame = Scope.description_for (#work own) (#frame own)
        val expected = {graph = #graph own,scope = #scope own,
          sources = #sources own,work = #work own}
        val parent = Q.describe_for expected (#admission own)
        val lambda = G.binder_closure_data
          (#graph own) (#scope own) (#closure own)
        val body = Core.conversion_description_for (#work own) (#body own)
        val _ = W.validate (#work own) (#graph own) (#root own) (#sources own)
          (#limits own)
    in if Portable.pointer_eq (#graph frame,#graph own) andalso
        #root frame = #root own andalso #scope frame = #scope own andalso
        Portable.pointer_eq (#sources frame,#sources own) andalso
        #node parent = #source own andalso #node lambda = #source own andalso
        #binder lambda = #binder own andalso #body lambda = #left own andalso
        #body_frame lambda = #body_frame own andalso
        #declaring_scope lambda = #declaring own andalso
        #node_frame lambda = #node_frame own andalso
        Portable.pointer_eq (#graph body,#graph own) andalso
        Portable.pointer_eq (#sources body,#sources own) andalso
        #root body = #root own andalso #scope body = #body_frame own andalso
        #source body = #left own andalso #target body = #right own andalso
        Type.type_epoch () = #epoch own andalso
        Term.term_epoch () = #symbols own
      then () else raise ERR "active" "actual source/body/frame changed"
    end
  fun validate expected (Plan {owner,held,...}) = protected expected (fn () =>
    (if Portable.pointer_eq (expected,#work owner) then () else
       raise ERR "validate" "different original Work";
     active owner;
     (* No callback intervenes in this paid retained-witness walk. *)
     List.app (fn retained =>
       (W.spend_guard_policy expected 1;
        case retained of Child (caller,child) => ignore
          (G.closure_child_node (#graph owner) caller child)
        | Profile (caller,profile) => ignore
            (G.opaque_profile_data (#graph owner) caller profile))) held))
  fun prepare_admitted work {frame,admission,body,ordinal,check_type} =
    protected work (fn () => W.with_step work (fn () =>
    let
      val location = Scope.description_for work frame
      val graph = #graph location val scope = #scope location
      val sources = #sources location val limits = W.semantic_limits work
      val expected =
        {graph = graph,scope = scope,sources = sources,work = work}
      val parent = Q.describe_for expected admission
      val closure = G.closure_child_binder graph scope (#child parent)
      val lambda = G.binder_closure_data graph scope closure
      (* Core expected-Work validation precedes every body endpoint getter. *)
      val proof = Core.conversion_description_for work body
      val owner : owner = {graph = graph,root = #root location,scope = scope,
        sources = sources,work = work,limits = limits,
        epoch = Type.type_epoch (),symbols = Term.term_epoch (),frame = frame,
        admission = admission,body = body,closure = closure,
        child = #child parent,source = #node lambda,binder = #binder lambda,
        left = #body lambda,right = #target proof,
        body_frame = #body_frame lambda,declaring = #declaring_scope lambda,
        node_frame = #node_frame lambda}
      val _ = if ordinal >= 0 then () else
        raise ERR "prepare" "negative lambda ordinal"
      val _ = active owner
      val ceiling = IntInf.fromInt (W.work_limit work)
      fun plus a b = IntInf.min (ceiling+1,a+b)
      fun times a b = IntInf.min (ceiling+1,a*b)
      (* Entry and final fences enclose this callback-free inventory.
         Rewalking the entire Core backing at every type/node/probe would
         multiply its cost by the actual operand inventory. *)
      fun tick () = W.spend work 1
      val held = ref ([] : held list)
      val types = ref ([] : Type.hol_type list)
      val memo = ref ([] : (G.node * size) list)
      fun type_weight ty =
        let fun walk [] n bytes = (n,bytes)
              | walk (pending::more) n bytes =
                  (tick ();case pending of [] => walk more n bytes
                   | current::rest =>
                     let val n = plus n 1
                         val _ = if n <= ceiling then () else
                           raise ERR "prepare" "type inventory exceeds Work"
                     in if Type.is_vartype current then
                          walk (rest::more) n
                            (plus bytes (IntInf.fromInt
                              (String.size (Type.dest_vartype current))))
                        else walk (#2 (Type.dest_type current)::rest::more)
                          n bytes end)
        in walk [[ty]] 0 0 end
      fun annotation node =
        let val _ = tick () val ty = G.type_of graph node
            val _ = types := ty :: !types
        in type_weight ty end
      fun cached node [] = NONE
        | cached node ((old,value)::rest) =
            (tick ();if old = node then SOME value else cached node rest)
      fun visit caller child : size =
        let val _ = tick ()
            val node = G.closure_child_node graph caller child
            (* Incoming closure is retained before a semantic-node hit. *)
            val _ = held := Child (caller,child) :: !held
        in case cached node (!memo) of SOME value => value | NONE =>
          let val (ty,bytes) = annotation node
              val value : size = case G.view graph node of
                  G.Application _ =>
                    let val (f,x) = G.closure_application_children
                          graph caller child
                        val a = visit caller f val b = visit caller x
                    in {raw = plus 1 (plus (#raw a) (#raw b)),
                      inc = plus 1 (plus (#inc a) (#inc b)),
                      ann = plus ty (plus (#ann a) (#ann b)),ty = ty,
                      type_bytes = bytes,
                      bytes = plus bytes (plus (#bytes a) (#bytes b))} end
                | G.AdmittedBinder _ =>
                    let val closure = G.closure_child_binder graph caller child
                        val lambda = G.binder_closure_data graph caller closure
                        val (bt,bb) = annotation (#binder lambda)
                        val b = visit caller
                          (G.binder_closure_body graph caller closure)
                    in {raw = plus 1 (#raw b),inc = plus 2 (#inc b),
                      ann = plus ty (plus bt (#ann b)),ty = ty,
                      type_bytes = bytes,
                      bytes = plus bytes (plus bb (#bytes b))} end
                | G.OpaqueRetained =>
                    let val profile = case G.opaque_profile_for
                          graph caller node of
                            SOME result => result | NONE => raise ERR "prepare"
                              "opaque actual body has no complete inventory"
                        val data = G.opaque_profile_data graph caller profile
                        val _ = held := Profile (caller,profile) :: !held
                        val _ = types := #types data @ !types
                    in {raw = IntInf.fromInt (#raw data),
                      inc = IntInf.fromInt (#inc data),ann = #ann data,
                      ty = #ty data,type_bytes = bytes,
                      bytes = #type_bytes data} end
                | _ => {raw = 1,inc = 1,ann = ty,ty = ty,
                        type_bytes = bytes,bytes = bytes}
              val _ = tick () val _ = memo := (node,value) :: !memo
          in value end
        end
      val old = visit scope (#child parent)
      val left = visit (#body_frame owner)
        (G.closure_root graph (#body_frame owner) (#left owner))
      val right = visit (#body_frame owner)
        (G.closure_root graph (#body_frame owner) (#right owner))
      val binder = visit (#body_frame owner)
        (G.closure_root graph (#body_frame owner) (#binder owner))
      val new : size = {raw = plus 1 (#raw right),inc = plus 2 (#inc right),
        ann = plus (#ty old) (plus (#ann binder) (#ann right)),ty = #ty old,
        type_bytes = #type_bytes old,
        bytes = plus (#type_bytes old) (plus (#bytes binder) (#bytes right))}
      fun bound label cap (value : size) =
        if #raw value <= IntInf.fromInt cap andalso
            #inc value <= IntInf.fromInt cap then () else
          raise ERR "prepare" (label ^ " exceeds original actual contract")
      val _ = bound "source lambda" (#source_limit parent) old
      val _ = bound "left body operand" (#source_limit parent) left
      val _ = bound "right body operand" (#output_limit limits) right
      val _ = bound "result lambda" (#output_limit limits) new
      fun equal (a : size) (b : size) : size =
        {raw = plus 3 (plus (#raw a) (#raw b)),
         inc = plus 3 (plus (#inc a) (#inc b)),
         ann = plus 6 (plus (times 3 (#ty a)) (plus (#ann a) (#ann b))),
         ty = 1,type_bytes = 0,
         bytes = plus (times 3 (#type_bytes a)) (plus (#bytes a) (#bytes b))}
      val body_eq = equal left right
      val old_alpha = equal old old val new_alpha = equal new new
      val final = equal old new
      val equations = [body_eq,old_alpha,new_alpha,final,final,final]
      (* Surviving Hyp is exactly empty by Core.execute's checked contract.
         Every actual operand/result is admitted before the first callback,
         graph constructor, ABS, ALPHA or TRANS. No body is a named atom. *)
      val _ = List.app (bound "actual public lambda result"
        (#template_limit limits)) equations
      fun weight (value : size) = plus 1
        (plus (#raw value) (plus (#inc value)
          (plus (#ann value) (#bytes value))))
      (* Equality declaration/partial types are rendered only after reserve;
         forecast BOTH actual body and lambda equality policy families. *)
      fun equality_types ty =
        let val partial = plus 2 ty val head = plus 3 (times 2 ty)
        in plus (times 2 partial) (times 2 head) end
      val rendering = plus 2 (plus (equality_types (#ty old))
        (equality_types (#ty left)))
      val actual_quote = List.foldl (fn (value,total) =>
        plus total (weight value)) 0
        (new :: binder :: left :: right :: equations @
          (if #node_frame owner = #declaring owner then [] else [new_alpha]))
      val quotation = plus actual_quote rendering
      val _ = if quotation <= ceiling then () else
        raise ERR "prepare" "actual lambda quote exceeds original Work"
      val token = W.reserve work {role = W.ClosedRecord,ordinal = ordinal,
        amount = IntInf.toInt quotation}
      val _ = W.consume work token (IntInf.toInt quotation)
      val plan = Plan {owner = owner,held = !held,types = !types,
        policy = check_type,state = ref Ready}
      val _ = validate work plan
    in plan end))
  fun execute work (plan as Plan {owner,types,policy,state,...}) =
    protected work (fn () =>
      (validate work plan;W.with_step work (fn () =>
       let val _ = if !state = Ready then state := Running else
             raise ERR "execute" "lambda plan already used"
           fun guard () = validate work plan
           (* All run operations below are callback-free. Entry/the last
              policy return and the final fence enclose their real work;
              every genuine backing witness is still checked at fences. *)
           fun run action = action ()
           val graph = #graph owner
           fun equality_types node =
             let val operand = run (fn () => G.type_of graph node)
                 val partial = run (fn () =>
                   Type.mk_type ("fun",[operand,Type.bool]))
                 val head = run (fn () => Type.mk_type ("fun",[operand,partial]))
             in [partial,head] end
           val generated = Type.bool ::
             (equality_types (#source owner) @ equality_types (#left owner))
           val _ = List.app (fn ty =>
             (policy ty;guard ())) (generated @ types)
           val lambda = run (fn () => G.binder_closure_data graph
             (#scope owner) (#closure owner))
           val first = run (fn () => G.recorded_abstraction graph
             (#declaring owner) (#output_limit (#limits owner))
             {binder = #binder owner,body = #right owner,
              body_frame = #body_frame owner})
           val target = if #node_frame owner = #declaring owner then first
             else #node (run (fn () =>
               G.rehome graph (#node_frame owner) first))
           val child = run (fn () =>
             G.closure_root graph (#scope owner) target)
           val body = run (fn () => Core.theorem_for work (#body owner))
           val _ = if null (Thm.hyp body) andalso
               null (Tag.axioms_of (Thm.tag body)) andalso
               List.all (fn tag => tag = "DISK_THM")
                 (#1 (Tag.dest_tag (Thm.tag body))) then () else
             raise ERR "execute" "body result is not clean Source-free proof"
           val (left,right) = boolSyntax.dest_eq (Thm.concl body)
           val _ = if Portable.pointer_eq
                 (left,G.representative graph (#left owner)) andalso
               Portable.pointer_eq
                 (right,G.representative graph (#right owner)) then () else
             raise ERR "execute" "actual body result endpoints changed"
           val abstracted = run (fn () => Thm.ABS (#binder_term lambda) body)
           val (left,right) = boolSyntax.dest_eq (Thm.concl abstracted)
           val prefix = run (fn () => Thm.ALPHA
             (G.representative graph (#source owner)) left)
           val after = run (fn () => Thm.ALPHA right
             (G.representative graph target))
           val tail = run (fn () => Thm.TRANS abstracted after)
           val theorem = run (fn () => Thm.TRANS prefix tail)
           val _ = state := Complete val _ = guard ()
       in Result {plan = plan,target = target,child = child,theorem = theorem}
       end)))
  fun conversion_description_for work
      (Result {plan = plan as Plan {owner,state,...},target,child,theorem}) =
    (validate work plan;
     let val (left,right) = boolSyntax.dest_eq (Thm.concl theorem)
     in if !state = Complete andalso null (Thm.hyp theorem) andalso
         null (Tag.axioms_of (Thm.tag theorem)) andalso
         List.all (fn tag => tag = "DISK_THM")
           (#1 (Tag.dest_tag (Thm.tag theorem))) andalso
         Portable.pointer_eq (left,G.representative
           (#graph owner) (#source owner)) andalso
         Portable.pointer_eq (right,G.representative (#graph owner) target)
         andalso
         G.closure_child_node (#graph owner) (#scope owner) child = target then
       {graph = #graph owner,root = #root owner,scope = #scope owner,
        sources = #sources owner,source = #source owner,target = target}
     else raise ERR "description_for" "held lambda result changed" end)
  fun theorem_for work (result as Result {theorem,...}) =
    (ignore (conversion_description_for work result);theorem)
  (* The body comes only from a genuine closed Core result. The existing
     canonical Lambda producer owns its actual finite native programme. *)
  structure PolicyRealizedLambda =
  struct
    structure P=SmtReplayProof
    structure L=SmtReplayOwnedLambda
    val _=SmtReplayOwnedLambda.prepare_canonical_admitted_with_policy
    val _=SmtReplayOwnedLargeProofCore.realization_with_policy_for
    val _=SmtReplayProof.policy_source_realization_closed_fact_for
    structure NC=SmtReplayNativeContract
    structure RP=SmtReplayResourcePolicy
    type owner={work:W.portfolio,graph:G.graph,root:G.scope,scope:G.scope,
      sources:S.sources,frame:Scope.receipt,admission:Q.policy_focus,
      body:Core.policy_result,native_contract:NC.contract,
      closure:G.binder_closure,source:G.node,left:G.node,right:G.node,
      body_frame:G.scope,epoch:int,symbols:int}
    datatype plan=Plan of {owner:owner,lambda:L.canonical_policy_plan,
      used:bool ref}
    datatype result=Result of {plan:plan,
      converted:L.canonical_policy_conversion}
    fun protect work action=action() handle primary=>
      (W.close work;raise primary)
    fun expected (own:owner)=
      {graph= #graph own,caller= #scope own,scope= #scope own,
       sources= #sources own,work= #work own}
    fun active (own:owner)=
      let val work= #work own
          val _=NC.validate_for work (#native_contract own)
          val contract=Core.native_contract_with_policy_for work (#body own)
          val _=if Portable.pointer_eq(contract,#native_contract own)
            then () else raise ERR "policy_lambda" "different native owner"
          val frame=Scope.description_with_policy_for work (#frame own)
          val parent=Q.describe_with_policy_for
            {graph= #graph own,scope= #scope own,sources= #sources own,
             work=work} (#admission own)
          val lambda=G.binder_closure_data (#graph own) (#scope own)
            (#closure own)
          val body=Core.conversion_description_with_policy_for work
            (#body own)
      in if Portable.pointer_eq(#graph frame,#graph own) andalso
          #root frame= #root own andalso #scope frame= #scope own andalso
          Portable.pointer_eq(#sources frame,#sources own) andalso
          #node parent= #source own andalso
          #node lambda= #source own andalso #body lambda= #left own andalso
          #body_frame lambda= #body_frame own andalso
          Portable.pointer_eq(#graph body,#graph own) andalso
          #root body= #root own andalso #scope body= #body_frame own andalso
          Portable.pointer_eq(#sources body,#sources own) andalso
          #source body= #left own andalso #target body= #right own andalso
          Type.type_epoch()= #epoch own andalso
          Term.term_epoch()= #symbols own then () else
        raise ERR "policy_lambda" "actual original frame or body changed"
      end
    fun validate work (Plan{owner,...})=protect work (fn()=>
      (if Portable.pointer_eq(work,#work owner) then () else
         raise ERR "policy_lambda" "different original Work";
       active owner))
    fun prepare work
        {frame,admission,body,ordinal,native_contract,profiles,check_type}=
      protect work (fn()=>
      let
        val _=NC.validate_for work native_contract
        val contract=Core.native_contract_with_policy_for work body
        val _=if Portable.pointer_eq(contract,native_contract) then () else
          raise ERR "policy_lambda" "different native owner"
        val _=if ordinal>=0 then () else
          raise ERR "policy_lambda" "negative lambda ordinal"
        val (owner,fact)=W.with_step work (fn()=>
          let
            val location=Scope.description_with_policy_for work frame
            val graph= #graph location val scope= #scope location
            val sources= #sources location
            val parent=Q.describe_with_policy_for
              {graph=graph,scope=scope,sources=sources,work=work} admission
            val closure=G.closure_child_binder graph scope (#child parent)
            val lambda=G.binder_closure_data graph scope closure
            val header=Core.conversion_description_with_policy_for work body
            val own:owner={work=work,graph=graph,root= #root location,
              scope=scope,sources=sources,frame=frame,admission=admission,
              body=body,native_contract=native_contract,closure=closure,
              source= #node lambda,left= #body lambda,right= #target header,
              body_frame= #body_frame lambda,epoch=Type.type_epoch(),
              symbols=Term.term_epoch()}
            val _=active own
            val receipt=Core.realization_with_policy_for work body
            (* This pure bridge retains the SAME closed proof. An ordinary
               recorder would execute REFL/EQ_MP before L's native gate. *)
            val fact=P.policy_source_realization_closed_fact_for work receipt
            val _=W.spend_policy work 1
            val _=active own
          in (own,fact) end)
        val lambda=L.prepare_canonical_admitted_with_policy
          {graph= #graph owner,scope= #scope owner,sources= #sources owner,
           work=work,ordinal=ordinal,admission=admission,body_fact=fact,
           native_contract=native_contract,profiles=profiles,
           check_type=fn ty=>(active owner;check_type ty;active owner)}
        val plan=Plan{owner=owner,lambda=lambda,used=ref false}
        val _=validate work plan
      in plan end)
    fun execute work (plan as Plan{owner,lambda,used})=protect work (fn()=>
      let val _=validate work plan
          val _=if !used then raise ERR "policy_lambda" "plan already used"
            else used:=true
          val converted=L.execute_canonical_with_policy lambda
          val _=validate work plan
          val _=L.validate_canonical_with_policy_for (expected owner)
            converted
      in Result{plan=plan,converted=converted} end)
    fun endpoints work (Result{plan=plan as Plan{owner,...},converted})=
      protect work (fn()=>
      (validate work plan;
       L.endpoints_canonical_with_policy_for (expected owner) converted))
    fun description work
        (result as Result{plan=Plan{owner,...},...})=
      let val data=endpoints work result
      in {graph= #graph owner,root= #root owner,scope= #scope owner,
          sources= #sources owner,source= #source data,target= #target data}
      end
    fun theorem work result= #theorem(endpoints work result)
    fun contract work (result as Result{plan=Plan{owner,...},...})=
      (ignore(endpoints work result);#native_contract owner)
  end
  type policy_plan=PolicyRealizedLambda.plan
  type policy_result=PolicyRealizedLambda.result
  val prepare_admitted_with_policy=PolicyRealizedLambda.prepare
  val execute_with_policy=PolicyRealizedLambda.execute
  val conversion_description_with_policy_for=PolicyRealizedLambda.description
  val theorem_with_policy_for=PolicyRealizedLambda.theorem
  val native_contract_with_policy_for=PolicyRealizedLambda.contract

end
