(* Canonical closure and complete local proof portfolio proposal. *)
structure SmtLib_GraphCarrierRoot :> SmtLib_GraphCarrierRoot =
struct
  structure G = SmtReplayGraph
  structure S = SmtReplaySource
  structure P = SmtReplayProof
  structure H = SmtLib_GraphLawTypeInstance
  val prepare_instance = SmtLib_GraphLawTypeInstance.prepare
  val prepare_identity = SmtLib_GraphLawTypeInstance.prepare_identity
  structure W = SmtReplayInvocationWork
  structure F = SmtReplayFocusAdmission
  val _ = SmtReplayFocusAdmission.describe_for
  val ERR = Feedback.mk_HOL_ERR "SmtLib_GraphCarrierRoot"
  type request =
    {graph : G.graph,scope : G.scope,sources : S.sources,
     work : W.portfolio,ordinal : int,original : G.node,view : G.source,
     predicate_view : G.source,law : P.closed_fact,
     check_type : Type.hol_type -> unit,scope_opened : G.scope -> unit}
  type closure_request =
    {graph : G.graph,scope : G.scope,sources : S.sources,
     work : W.portfolio,ordinal : int,original : G.closure_child,
     law : P.closed_fact,check_type : Type.hol_type -> unit,
     scope_opened : G.scope -> unit}
  type admitted_request =
    {graph : G.graph,scope : G.scope,sources : S.sources,
     work : W.portfolio,ordinal : int,admission : F.focus,
     law : P.closed_fact,check_type : Type.hol_type -> unit,
     scope_opened : G.scope -> unit}
  type owner =
    {graph : G.graph,scope : G.scope,sources : S.sources,
     work : W.portfolio,ordinal : int,original : G.node,
     law : P.closed_fact,check_type : Type.hol_type -> unit,
     scope_opened : G.scope -> unit}
  datatype surface = Views of {view : G.source,predicate_view : G.source}
    | Canonical of G.closure_child
  datatype shape = Actual of Type.hol_type | Arrow of shape * shape
  datatype expr = Existing of G.node | Variable of int * shape
    | Constant of Term.term * shape | Apply of expr * expr * shape
    | Lambda of int * shape * expr
  type size = {raw : IntInf.int,binder : IntInf.int,ann : IntInf.int}
  datatype plan = Plan of
    {request : owner,surface : surface,active : unit -> unit,
     limits : W.limits,
     hplan : H.plan,predicate : G.node,target : expr,
     token : W.entitlement,amount : int,used : bool ref,
     fresh : G.scope list ref}
  datatype conversion = Conversion of
    {request : owner,active : unit -> unit,source : G.node,
     target : G.node,theorem : Thm.thm}

  (* Expression and proof operations below the int and policy interfaces.
     They touch neither a native contract, a policy focus nor the kind of
     Work. A caller passes the effects it owns (its charge, its guard, the
     lists it retains, its abstraction) and keeps its own lifecycle checks,
     scope cleanup and Work retirement. [origin] names the caller in the
     errors raised on its behalf. *)

  fun refuse origin message = raise ERR origin message

  (* The stock constants a preparation retains and revalidates. *)
  fun stock_constants () =
    [boolSyntax.universal,boolSyntax.existential,boolSyntax.implication,
     boolSyntax.conjunction,intSyntax.zero_tm,intSyntax.leq_tm,
     intSyntax.Num_tm,intSyntax.int_injection,numSyntax.zero_tm]

  (* The part of a guard that concerns what a preparation retained. *)
  fun retained_live graph {epoch,constants,fresh,held} =
    (if Type.type_epoch () = epoch then () else
       raise ERR "active" "Type retirement epoch changed";
     List.app (fn term => if Term.uptodate_term term then () else
       raise ERR "active" "retired retained constant") (!constants);
     List.app (G.validate_scope graph) (!fresh);
     List.app (fn (caller,closure) => ignore
       (G.binder_closure_data graph caller closure)) (!held))

  (* Syntax weights of types and shapes; every step is [charge]d. *)
  fun weights {charge,origin} =
    let fun weight ty : IntInf.int =
          let val _ = charge 1
              val n = if Type.is_vartype ty then 1 else
                List.foldl (fn (a,n) => n + weight a) 1
                  (#2 (Type.dest_type ty))
          in if Type.uptodate_type ty then n
             else refuse origin "retired type" end
        fun shape_weight (Actual ty) = weight ty
          | shape_weight (Arrow (a,b)) =
              (charge 1;1 + shape_weight a + shape_weight b)
    in {weight = weight,shape_weight = shape_weight} end

  fun bound origin cap n = if n >= 0 andalso n <= IntInf.fromInt cap
    then () else refuse origin "prospective carrier syntax exceeds cap"

  (* Which carrier law the quantifier needs. *)
  fun classify {graph,operator,predicate,weight,origin} =
    let
      fun reject message = refuse origin message
      val universal = case G.view graph operator of G.Constant id =>
          KernelSig.id_compare (id,#Name
            (Term.dest_thy_constid boolSyntax.universal)) = EQUAL
        | _ => reject "not a constant quantifier"
      val existential = case G.view graph operator of G.Constant id =>
          KernelSig.id_compare (id,#Name
            (Term.dest_thy_constid boolSyntax.existential)) = EQUAL
        | _ => false
      val _ = if universal orelse existential then () else
        reject "not forall or exists"
      val predicate_type = G.type_of graph predicate
      val _ = ignore (weight predicate_type)
      val (carrier,result) = Type.dom_rng predicate_type
      val _ = if Type.compare (result,Type.bool) = EQUAL then () else
        reject "non-Boolean predicate"
      val natural = Type.compare (carrier,numSyntax.num) = EQUAL
      val domain = if natural then NONE else
        let val (a,count) = Type.dom_rng carrier in
          if Type.compare (count,numSyntax.num) = EQUAL then SOME a
          else reject "carrier is neither num nor arbitrary bag"
        end
      val fixed = case (natural,universal) of
          (true,true) => HolSmtTheory.NUM_FORALL_TO_INT
        | (true,false) => HolSmtTheory.NUM_EXISTS_TO_INT
        | (false,true) => HolSmtTheory.BAG_FORALL_TO_INT
        | (false,false) => HolSmtTheory.BAG_EXISTS_TO_INT
    in {universal = universal,carrier = carrier,domain = domain,
        fixed = fixed} end

  (* The predicate child must be the predicate; its binder closure is
     retained for revalidation. *)
  fun predicate_closure {graph,scope,predicate_child,predicate,held,origin} =
    let val _ = if G.closure_child_node graph scope predicate_child =
          predicate then () else refuse origin "different predicate child"
        val closure = G.closure_child_binder graph scope predicate_child
        val _ = G.binder_closure_data graph scope closure
        val _ = held := (scope,closure) :: !held
    in closure end

  (* Sizes the nodes below a closure child once each. A node is keyed by
     its [locate]d locus, so a policy prover can tell frames apart; a
     retained opaque node is sized by [opaque]. *)
  fun size_walk {graph,charge,weight,held,constants,types,locate,opaque} =
    let
      val memo = ref []
      fun visit caller child =
        let val _ = charge 1
            val node = G.closure_child_node graph caller child
            val locus = locate caller child node
            fun find [] = NONE
              | find ((n,saved)::rest) =
                  (charge 1;if n = locus then SOME (n,saved)
                   else find rest)
        in case find (!memo) of
            SOME (_,saved) => saved
          | NONE =>
            let val ty = G.type_of graph node val w = weight ty
                val _ = charge 1 val _ = types := ty :: !types
                val value = case G.view graph node of
                    G.Application _ =>
                      let val (a,b) =
                            G.closure_application_children graph caller
                              child
                          val l = visit caller a val r = visit caller b
                      in {raw = 1 + #raw l + #raw r,
                        binder = 1 + #binder l + #binder r,
                        ann = w + #ann l + #ann r} : size end
                  | G.AdmittedBinder _ =>
                      let val c = G.closure_child_binder graph caller child
                          val cd = G.binder_closure_data graph caller c
                          val _ = held := (caller,c) :: !held
                          val bt = G.type_of graph (#binder cd)
                          val bw = weight bt
                          val _ = types := bt :: !types
                          val b = visit caller
                            (G.binder_closure_body graph caller c)
                      in {raw = 1 + #raw b,binder = 2 + #binder b,
                          ann = w + bw + #ann b} : size end
                  | G.Constant _ =>
                      (charge 1;
                       constants := G.representative graph node ::
                         !constants;
                       {raw = 1,binder = 1,ann = w} : size)
                  | G.OpaqueRetained => opaque locus
                      {weight = w,charge = charge,weigh = weight,
                       types = types}
                  | _ => {raw = 1,binder = 1,ann = w} : size
                val _ = charge 1 val _ = memo := (locus,value) :: !memo
            in value end
        end
    in visit end

  (* The sizes of the predicate and of its body. *)
  fun predicate_sizes graph visit scope predicate_child closure =
    let val ps = visit scope predicate_child
        val body_size = visit scope (G.binder_closure_body graph scope closure)
    in (ps,body_size) end

  (* The type-variable bindings the stock law is instantiated at. *)
  fun law_bindings origin domain variables =
    case domain of
      NONE => if null variables then []
              else refuse origin "unexpected num law types"
    | SOME domain => (case variables of [_] => [(0,domain)]
        | _ => refuse origin "BAG law must have one original type variable")

  val bool_shape = Actual Type.bool

  (* The generated carrier [target] and the quantifier [left] it replaces. *)
  fun carrier_exprs {universal,domain,carrier,predicate} =
    let
      val bool = bool_shape val integer = Actual intSyntax.int_ty
      val natural = Actual numSyntax.num
      fun constant term ty = Constant (term,ty)
      fun app f x ty = Apply (f,x,ty)
      fun binary term a b = app
        (app (constant term (Arrow (bool,Arrow (bool,bool)))) a
          (Arrow (bool,bool))) b bool
      fun forall domain body = app
        (constant boolSyntax.universal
          (Arrow (Arrow (domain,bool),bool))) body bool
      fun quantify domain body = app
        (constant (if universal then boolSyntax.universal
                   else boolSyntax.existential)
          (Arrow (Arrow (domain,bool),bool))) body bool
      fun num_of node = app
        (constant intSyntax.Num_tm (Arrow (integer,natural))) node natural
      fun guard node = app
        (app (constant intSyntax.leq_tm
            (Arrow (integer,Arrow (integer,bool))))
          (app (constant intSyntax.int_injection
              (Arrow (natural,integer)))
            (constant numSyntax.zero_tm natural) integer)
          (Arrow (integer,bool)))
        node bool
      val predicate = Existing predicate
      val (new_carrier,guarded,payload) = case domain of NONE =>
          (integer,guard (Variable (0,integer)),
           num_of (Variable (0,integer)))
        | SOME ty =>
          let val domain = Actual ty
              val count = Arrow (domain,integer)
              val cx = app (Variable (0,count))
                (Variable (1,domain)) integer
              val cx2 = app (Variable (0,count))
                (Variable (2,domain)) integer
          in (count,forall domain (Lambda (1,domain,guard cx)),
              Lambda (2,domain,num_of cx2)) end
      val connective = if universal then boolSyntax.implication
        else boolSyntax.conjunction
      val target = quantify new_carrier (Lambda (0,new_carrier,
        binary connective guarded (app predicate payload bool)))
      val old_carrier = Actual carrier
      val left = quantify old_carrier (Lambda (3,old_carrier,
        app predicate (Variable (3,old_carrier)) bool))
    in {target = target,left = left,old_carrier = old_carrier} end

  (* The sizes of an expression; the shapes it needs are recorded. *)
  fun expr_size {graph,predicate,existing,charge,shape_weight,shapes} =
    let
      fun expr_type (Existing _) = Actual (G.type_of graph predicate)
        | expr_type (Variable (_,ty)) = ty
        | expr_type (Constant (_,ty)) = ty
        | expr_type (Apply (_,_,ty)) = ty
        | expr_type (Lambda (_,ty,b)) = Arrow (ty,expr_type b)
      fun size expression =
        let val ty = expr_type expression val w = shape_weight ty
            val _ = charge 1 val _ = shapes := ty :: !shapes
        in case expression of Existing _ => existing
          | Apply (f,x,_) =>
              let val a = size f val b = size x in
                {raw = 1 + #raw a + #raw b,
                 binder = 1 + #binder a + #binder b,
                 ann = w + #ann a + #ann b} : size end
          | Lambda (_,ty,body) =>
              let val b = size body val v = shape_weight ty
                  val _ = shapes := ty :: !shapes
              in {raw = 1 + #raw b,binder = 2 + #binder b,
                  ann = w + v + #ann b} : size end
          | _ => {raw = 1,binder = 1,ann = w} : size
        end
    in size end

  (* Whether the sizes of the stock law's instance agree with the one
     predicate per side of the fixed law schema. [weight] is charged for
     the law's annotations. *)
  fun schema_agrees weight {raw,binder,typed_annotations}
      {ps : size,pweight,lhs : size,rhs : size} =
    let
      val law_annotations = List.foldl
        (fn (ty,n) => n + weight ty) 0 typed_annotations
      val spec_raw = IntInf.fromInt raw - 5 + 2 * #raw ps
      val spec_binder = IntInf.fromInt binder - 6 + 2 * #binder ps
      val spec_annotations = law_annotations - (5*pweight + 7) +
        2 * #ann ps
    in spec_raw = 3 + #raw lhs + #raw rhs andalso
       spec_binder = 3 + #binder lhs + #binder rhs andalso
       spec_annotations = 9 + #ann lhs + #ann rhs end

  (* Every public local theorem result, including the operand laws supplied
     to TRANS, is quoted before external policies. BETA substitutes one
     same-typed variable into the retained predicate body: capture renaming
     changes no syntax counts. [proof] is SYM(AP_TERM) and three inner TRANS
     results. *)
  fun proof_sizes {lhs,rhs,ps : size,body_size : size,pweight,cw,qw} =
    let
      val source_size : size =
        {raw = 2 + #raw ps,binder = 2 + #binder ps,
         ann = 1 + qw + #ann ps}
      val application : size =
        {raw = 2 + #raw ps,binder = 2 + #binder ps,
         ann = 1 + cw + #ann ps}
      val uncontracted : size =
        {raw = 1 + #raw application,
         binder = 2 + #binder application,
         ann = pweight + cw + #ann application}
      fun equality w (a : size) (b : size) : size =
        {raw = 3 + #raw a + #raw b,
         binder = 3 + #binder a + #binder b,
         ann = 6 + 3*w + #ann a + #ann b}
      val beta = equality 1 application body_size
      val abs = equality pweight uncontracted ps
      val ap_term = equality 1 lhs source_size
      val alignment = equality 1 source_size source_size
      val finish = equality 1 rhs rhs
      val specialized = equality 1 lhs rhs
      val final = equality 1 source_size rhs
    in {source_size = source_size,application = application,
        uncontracted = uncontracted,alignment = alignment,final = final,
        proof = [specialized,beta,abs,ap_term,alignment,finish,
                 ap_term,specialized,final,final]} end

  (* Annotation work is charged independently to SAME Work, not invented as
     an annotation <= semantic syntax cap rule. Each produced theorem's full
     repeated annotations are retained. *)
  fun carrier_amount {lhs,rhs,source_size,application,uncontracted,proof} =
    List.foldl (fn (z : size,n) => n + #raw z + #binder z + #ann z) 0
      (lhs :: rhs :: source_size :: application :: uncontracted :: proof)

  (* The shapes the proof builds besides those of the expressions. *)
  fun proof_shapes old_carrier =
    [Arrow (old_carrier,bool_shape),
     Arrow (Arrow (old_carrier,bool_shape),
       Arrow (Arrow (old_carrier,bool_shape),bool_shape)),
     Arrow (bool_shape,Arrow (bool_shape,bool_shape))]

  fun render_shape active (Actual ty) = ty
    | render_shape active (Arrow (a,b)) =
        let val l = render_shape active a val r = render_shape active b
            val _ = active ()
            val ty = Type.mk_type ("fun",[l,r])
            val _ = active () in ty end

  (* Every type the plan needs goes through the caller's type policy. *)
  fun issue_types {active,check_type,queued,types,shapes} =
    let fun policy ty = (active ();check_type ty;active ())
        val generated = List.map (render_shape active) (!shapes)
    in List.app policy (!queued @ types @ generated) end

  fun guarded guard f = (guard ();let val x = f () in guard ();x end)

  (* Builds the generated carrier [target] in the graph, opening its fresh
     frames below [scope]. [abstract] records a generated binder. *)
  fun build_target {graph,guard,scope_opened,fresh,abstract,origin}
      scope target =
    let
      fun invoke f = guarded guard f
      fun render (Actual ty) = ty
        | render (Arrow (a,b)) = invoke
            (fn () => Type.mk_type ("fun",[render a,render b]))
      fun opened child =
        (guard ();G.validate_scope graph child;scope_opened child;
         G.validate_scope graph child;guard ())
      fun new_frame parent bindings =
        let val child = G.new_scope graph parent bindings
            val _ = fresh := child :: !fresh
            val _ = opened child
        in child end
      fun build caller environment expression =
        (guard ();case expression of Existing node => node
         | Variable (slot,_) =>
             (case List.find (fn (i,_) => i = slot) environment of
                SOME (_,node) => node
              | NONE => refuse origin "missing generated binder")
         | Constant (term,ty) =>
             let val {Thy,Name,...} = Term.dest_thy_const term
                 val actual = invoke (fn () => Term.mk_thy_const
                   {Thy = Thy,Name = Name,Ty = render ty})
             in G.constant graph caller actual end
         | Apply (f,x,_) => G.application graph caller
             (build caller environment f,build caller environment x)
         | Lambda (slot,ty,body) =>
             let val frame = new_frame caller []
                 val term = invoke (fn () => Term.genvar (render ty))
                 val variable = G.variable graph frame G.Bound term
                 val body_frame = new_frame frame [(term,variable)]
                 val child = build body_frame
                   ((slot,variable)::environment) body
             in abstract caller {binder = variable,body = child,
                  body_frame = body_frame} end)
    in build scope [] target end

  (* The proof chain from the instantiated stock law [typed] to the
     equation between the node [alignment_source] and the generated
     [candidate]. *)
  fun carrier_proof {graph,guard,typed,predicate,alignment_source,candidate} =
    let
      fun invoke f = guarded guard f
      val specialized = invoke (fn () =>
        Thm.SPEC (G.representative graph predicate) typed)
      val (left,right) = boolSyntax.dest_eq (Thm.concl specialized)
      val (q,abstraction) = Term.dest_comb left
      val (variable,application) = Term.dest_abs abstraction
      (* ONLY this introduced LEFT predicate redex is contracted. The
         old predicate body and generated RHS guards remain untouched. *)
      val beta = invoke (fn () => Thm.BETA_CONV application)
      val abs_bridge = invoke (fn () => Thm.ABS variable beta)
      val left_bridge = invoke (fn () => Thm.AP_TERM q abs_bridge)
      val (_,contracted) = boolSyntax.dest_eq (Thm.concl left_bridge)
      val alignment = invoke (fn () => Thm.ALPHA
        (G.representative graph alignment_source) contracted)
      val finish = invoke (fn () => Thm.ALPHA right
        (G.representative graph candidate))
      val reversed = invoke (fn () => Thm.SYM left_bridge)
      val finished = invoke (fn () => Thm.TRANS specialized finish)
      val contracted_result = invoke (fn () =>
        Thm.TRANS reversed finished)
    in invoke (fn () => Thm.TRANS alignment contracted_result) end

  (* The final theorem must be the exact closed conversion. *)
  fun check_boundary {graph,original,candidate,theorem,origin,message} =
    let val (a,b) = boolSyntax.dest_eq (Thm.concl theorem)
        val (oracles,_) = Tag.dest_tag (Thm.tag theorem)
    in if Portable.pointer_eq (a,G.representative graph original) andalso
          Portable.pointer_eq (b,G.representative graph candidate)
          andalso null (Thm.hyp theorem) andalso
          null (Tag.axioms_of (Thm.tag theorem)) andalso
          List.all (fn s => s = "DISK_THM") oracles then ()
       else raise ERR origin message end

  fun validate (Conversion {active,...}) = active ()
  fun validate_for {graph,scope,sources,work}
      (Conversion {request=held,active,...}) =
    let
      val root=S.owning_scope sources
      val limits=W.semantic_limits work
      val _=W.validate work graph root sources limits
      val _=G.validate_scope graph scope
      val _=if Portable.pointer_eq (graph,#graph held) andalso
               scope= #scope held andalso
               Portable.pointer_eq (sources,#sources held) andalso
               Portable.pointer_eq (work,#work held) then ()
            else raise ERR "validate_for" "foreign carrier work receipt"
    in active () end
    handle primary=>(W.close work;raise primary)

  fun endpoints (conversion as Conversion {source,target,theorem,...}) =
    (validate conversion;{source = source,target = target,theorem = theorem})

  fun prepare_internal admission surface (request as
      {graph,scope,sources,work,ordinal,original,law,
       check_type,scope_opened} : owner) =
    let
      val limits = W.semantic_limits work
      val root = S.owning_scope sources
      val source_limit = case admission of NONE => #input_limit limits
        | SOME held => #source_limit (F.describe_for
            {graph = graph,scope = scope,sources = sources,work = work} held)
      val epoch = Type.type_epoch ()
      val fresh = ref ([] : G.scope list)
      val held = ref ([] : (G.scope * G.binder_closure) list)
      val constants = ref (stock_constants ())
      fun active () =
        (W.validate work graph root sources limits;
         G.validate_scope graph scope;
         (case admission of NONE => () | SOME held =>
           let val d = F.describe_for
                 {graph = graph,scope = scope,sources = sources,work = work}
                 held
           in if #node d = original andalso
               #source_limit d = source_limit then () else
             raise ERR "active" "different admitted carrier profile" end);
         (case surface of Views {view,...} =>
            G.validate_opened_view graph scope original view
          | Canonical child =>
            if G.closure_child_node graph scope child = original then ()
            else raise ERR "active" "different canonical root handle");
         retained_live graph
           {epoch = epoch,constants = constants,fresh = fresh,held = held})
      fun charge n = (active ();W.spend work n)
      fun reject message = raise ERR "prepare" message
      val {weight,shape_weight} = weights {charge = charge,origin = "prepare"}
      fun cached cap node metric =
        (charge 1;case G.unfolded_nodes graph metric cap node of
           SOME n => if n <= cap then () else reject "cached metric cap"
         | NONE => reject "missing recorded metric")
      fun admit cap node =
        (cached cap node G.RawNodes;cached cap node G.BinderInclusiveNodes)
      val queued = ref ([] : Type.hol_type list)
      fun queue ty = (active ();W.spend work 1;queued := ty :: !queued)
      (* Callback-free original/canonical/type inventory FIRST. Genuine
         import and recorded opening are separate existing prerequisites. *)
      val initial = W.with_step work (fn () =>
        let
          val _ = active ()
          val _ = if ordinal >= 0 then () else reject "negative ordinal"
          val source = case surface of Views {view,...} => #node view
            | Canonical child => G.closure_child_node graph scope child
          val _ = admit source_limit source
          val (operator,predicate) = case G.view graph source of
              G.Application pair => pair
            | _ => reject "not a quantifier application"
          val predicate_child = case surface of Canonical child =>
              #2 (G.closure_application_children graph scope child)
            | Views {predicate_view,...} =>
              let val raw_predicate = case G.view graph original of
                      G.Application (_,p) => p
                    | _ => reject "original root is not a quantifier"
                  val _ = G.validate_opened_view graph scope raw_predicate
                    predicate_view
                  val _ = if #node predicate_view = predicate then () else
                    reject "different original predicate occurrence/view"
                  val closure = G.binder_closure graph scope predicate
                  val d = G.binder_closure_data graph scope closure
                  val _ = case G.view graph raw_predicate of
                      G.OpaqueRetained =>
                        let val origin = G.opened_binder_origin graph scope
                              raw_predicate predicate_view
                            val admission =
                              G.binder_origin_data graph scope origin
                        in if #node admission = predicate andalso
                            #body_frame d = #body_frame admission andalso
                            #body d = #node (#body admission) then () else
                          reject "different genuine predicate body frame"
                        end
                    | G.AdmittedBinder _ =>
                        if raw_predicate = predicate then () else
                          reject "constructed predicate was not exact"
                    | _ => reject "not a recorded predicate abstraction"
              in G.closure_root graph scope predicate end
          val closure = predicate_closure {graph = graph,scope = scope,
            predicate_child = predicate_child,predicate = predicate,
            held = held,origin = "prepare"}
          (* Constructed/rehome closures retain their genuine creation
             frames. They do NOT acquire a fabricated raw Source origin.
             This branch permits a later step on a generated BAG guard. *)
          val {universal,carrier,domain,fixed} = classify {graph = graph,
            operator = operator,predicate = predicate,weight = weight,
            origin = "prepare"}
          val _ = admit (#template_limit limits) (P.closed_node law)
          val _ = P.validate_closed_fact graph root
            (#template_limit limits) law
          val _ = if Portable.pointer_eq (P.closed_original law,fixed)
            then () else reject "not the exact selected original stock law"
          val types = ref ([] : Type.hol_type list)
          val visit = size_walk {graph = graph,charge = charge,
            weight = weight,held = held,constants = constants,types = types,
            locate = fn _ => fn _ => fn node => node,
            opaque = fn _ => fn _ =>
              reject "nested original binder needs genuine opening"}
          val (ps,body_size) = predicate_sizes graph visit scope
            predicate_child closure
          val _ = active ()
        in {source = source,predicate = predicate,carrier = carrier,
            domain = domain,universal = universal,size = ps,
            body_size = body_size,types = !types} end)
      (* H preparation hooks SAME Work. Its supplied policy only queues
         admitted types: no external callback precedes carrier reservation. *)
      val producer = H.begin_original_with_work graph root
        {original = law,template_limit = #template_limit limits,
         check_type = queue,work = work}
      val variables = H.type_variables producer
      val bindings = law_bindings "prepare" (#domain initial) variables
      val hplan = case #domain initial of
          NONE => prepare_identity producer
        | SOME _ => prepare_instance producer {bindings = bindings}
      val result = W.with_step work (fn () =>
        let
          val metadata = H.planned_syntax hplan
          val {target,left,old_carrier} = carrier_exprs
            {universal = #universal initial,domain = #domain initial,
             carrier = #carrier initial,predicate = #predicate initial}
          val shapes = ref ([] : shape list)
          val size = expr_size {graph = graph,predicate = #predicate initial,
            existing = #size initial,charge = charge,
            shape_weight = shape_weight,shapes = shapes}
          val rhs = size target val lhs = size left
          val ps = #size initial
          val pweight = weight (G.type_of graph (#predicate initial))
          val _ = if schema_agrees weight
              {raw = #raw metadata,binder = #binder metadata,
               typed_annotations = #typed_annotations metadata}
              {ps = ps,pweight = pweight,lhs = lhs,rhs = rhs} then () else
            reject "fixed one-P-per-side law schema differs"
          val cw = shape_weight old_carrier
          val qw = shape_weight (Arrow (Arrow (old_carrier,bool_shape),
            bool_shape))
          val {source_size,application,uncontracted,alignment,final,
               proof = base_proof} = proof_sizes
            {lhs = lhs,rhs = rhs,ps = ps,body_size = #body_size initial,
             pweight = pweight,cw = cw,qw = qw}
          (* The Views mode additionally quotes its existing ALPHA-only
             bridge and the outer TRANS. Canonical mode never requests a
             raw view. *)
          val proof = base_proof @
            (case surface of Canonical _ => []
             | Views _ => [alignment,final])
          val _ = List.app (fn (z : size) =>
            (bound "prepare" (#output_limit limits) (#raw z);
             bound "prepare" (#output_limit limits) (#binder z)))
            (rhs :: proof)
          (* This lhs is constructed by SPEC, not an original input. *)
          val _ = List.app (bound "prepare" (#output_limit limits))
            [#raw lhs,#binder lhs]
          val _ = List.app (fn (metric,n) =>
            case G.unfolded_nodes graph metric source_limit
                (#source initial) of
              SOME actual => if IntInf.fromInt actual = n then () else
                reject "canonical source forecast differs"
            | NONE => reject "missing canonical source forecast")
            [(G.RawNodes,#raw source_size),
             (G.BinderInclusiveNodes,#binder source_size)]
          val amount = carrier_amount {lhs = lhs,rhs = rhs,
            source_size = source_size,application = application,
            uncontracted = uncontracted,proof = proof}
          val _ = shapes := proof_shapes old_carrier @ !shapes
          val _ = bound "prepare" (W.work_limit work) amount
          val token = W.reserve work {role = W.LocalCarrier,ordinal = ordinal,
            amount = IntInf.toInt amount}
          val _ = issue_types {active = active,check_type = check_type,
            queued = queued,types = #types initial,shapes = shapes}
        in Plan {request = request,surface = surface,active = active,
          limits = limits,
          hplan = hplan,predicate = #predicate initial,target = target,
          token = token,amount = IntInf.toInt amount,used = ref false,
          fresh = fresh} end)
    in result end
    handle primary => (W.close work;raise primary)

  fun prepare ({graph,scope,sources,work,ordinal,original,view,
      predicate_view,law,check_type,scope_opened} : request) =
    prepare_internal NONE (Views {view = view,predicate_view = predicate_view})
      {graph = graph,scope = scope,sources = sources,work = work,
       ordinal = ordinal,original = original,law = law,
       check_type = check_type,scope_opened = scope_opened}

  fun prepare_closure ({graph,scope,sources,work,ordinal,original,law,
      check_type,scope_opened} : closure_request) =
    let val node = G.closure_child_node graph scope original
    in prepare_internal NONE (Canonical original)
      {graph = graph,scope = scope,sources = sources,work = work,
       ordinal = ordinal,original = node,law = law,
       check_type = check_type,scope_opened = scope_opened} end
    handle primary => (W.close work;raise primary)

  fun prepare_closure_admitted
      ({graph,scope,sources,work,ordinal,admission,law,check_type,scope_opened}
       : admitted_request) =
    let val d = F.describe_for
          {graph = graph,scope = scope,sources = sources,work = work} admission
    in prepare_internal (SOME admission) (Canonical (#child d))
      {graph = graph,scope = scope,sources = sources,work = work,
       ordinal = ordinal,original = #node d,law = law,
       check_type = check_type,scope_opened = scope_opened} end
    handle primary => (W.close work;raise primary)

  fun execute (Plan {request as {graph,scope,sources,work,original,
      scope_opened,...},surface,active,limits,hplan,predicate,target,token,
      amount,
      used,fresh}) =
    let
      val root = S.owning_scope sources
      val _ = W.with_step work (fn () =>
        (active ();if !used then raise ERR "execute" "plan already consumed"
         else used := true))
      val instance = H.execute hplan
      val result = W.with_step work (fn () =>
        let
          fun guard () =
            (active ();H.validate_instance_with_work graph root
              (#template_limit limits) work instance)
          val _ = guard ()
          val _ = W.consume work token amount
          fun abstract caller {binder,body,body_frame} =
            G.recorded_abstraction graph caller (#output_limit limits)
              {binder = binder,body = body,body_frame = body_frame}
          val candidate = build_target {graph = graph,guard = guard,
            scope_opened = scope_opened,fresh = fresh,abstract = abstract,
            origin = "execute"} scope target
          val typed = H.typed_theorem instance
          val joined = carrier_proof {graph = graph,guard = guard,
            typed = typed,predicate = predicate,
            alignment_source = (case surface of
              Views {view,...} => #node view | Canonical _ => original),
            candidate = candidate}
          val theorem = case surface of Canonical _ => joined
            | Views {view,...} => guarded guard (fn () =>
                Thm.TRANS (#bridge view) joined)
          val _ = check_boundary {graph = graph,original = original,
            candidate = candidate,theorem = theorem,origin = "execute",
            message = "exact closed conversion boundary differs"}
          val _ = guard ()
        in Conversion {request = request,active = guard,source = original,
          target = candidate,
          theorem = theorem} end)
    in result end
    handle primary =>
      (W.close work;List.app (fn frame =>
         (G.close_scope graph frame handle _ => ())) (!fresh);raise primary)
  structure RP=SmtReplayResourcePolicy
  structure NC=SmtReplayNativeContract
  type policy_admitted_request=
    {graph:G.graph,scope:G.scope,sources:S.sources,work:W.portfolio,
     ordinal:int,admission:F.policy_focus,law:P.closed_fact,
     native_contract:NC.contract,profiles:G.policy_opaque_profile list,
     check_type:Type.hol_type->unit,scope_opened:G.scope->unit}
  local
    type policy_owner =
      {graph : G.graph,scope : G.scope,sources : S.sources,
       work : W.portfolio,ordinal : int,original : G.node,
       law : P.closed_fact,check_type : Type.hol_type -> unit,
       scope_opened : G.scope -> unit,native_contract:NC.contract,
       profiles:G.policy_opaque_profile list}
    datatype surface = Canonical of G.closure_child
    type abstract =
      {graph : G.graph,work : W.portfolio,request : policy_owner,
       limits : W.limits,guard : unit -> unit} ->
      G.scope -> {binder : G.node,body : G.node,body_frame : G.scope} -> G.node
    datatype policy_plan = PolicyPlan of
      {request : policy_owner,surface : surface,active : unit -> unit,
       limits : W.limits,
       hplan : H.policy_plan,predicate : G.node,target : expr,
       token : W.entitlement,amount : IntInf.int,used : bool ref,
       fresh : G.scope list ref,abstract : abstract}
    datatype policy_conversion = PolicyConversion of
      {request : policy_owner,active : unit -> unit,source : G.node,
       target : G.node,theorem : Thm.thm}

    (* The operations in which the two policy provers differ. A metric is
       made afresh by each preparation: [locate] keys the size memo and
       locates an opaque node; [measure] sizes a node for the syntax caps and
       [measure_source] the canonical source for the forecast, each retaining
       the evidence that [revalidate] rechecks at every guard; [opaque] sizes
       a retained opaque node. An abstractor, given the preparation's native
       step counter, builds a generated binder while executing; a plan keeps
       it as its [abstract] operation. *)
    type counts =
      {node : G.node,raw : IntInf.int,inc : IntInf.int,
       types : Type.hol_type list}
    type ''locus metric =
      {revalidate : unit -> unit,
       locate : G.scope -> G.closure_child -> G.node -> ''locus,
       measure : G.node -> counts,measure_source : G.node -> counts,
       opaque : ''locus ->
         {weight : IntInf.int,charge : int -> unit,
          weigh : Type.hol_type -> IntInf.int,
          types : Type.hol_type list ref} -> size}
    type ''locus metrics =
      {graph : G.graph,scope : G.scope,
       profiles : G.policy_opaque_profile list} -> ''locus metric
    type abstractor = IntInf.int ref -> abstract
    type ''locus prover = {metrics : ''locus metrics,abstractor : abstractor}

    fun validate_with_policy_for {graph,scope,sources,work}
        (PolicyConversion {request=held,active,...}) =
      ((if Portable.pointer_eq (work,#work held) andalso
            Portable.pointer_eq (graph,#graph held) andalso scope= #scope held
            andalso Portable.pointer_eq (sources,#sources held) then () else
          raise ERR "validate_policy" "foreign carrier Work receipt";
        NC.validate_for work (#native_contract held);
        let val root=S.owning_scope sources
        in W.validate_policy work graph root sources (W.semantic_policy work);
           G.validate_scope graph scope;active () end)
       handle primary=>(W.close work;raise primary))
    fun endpoints_with_policy_for expected (held as PolicyConversion _) =
      (validate_with_policy_for expected held;
       let val PolicyConversion {source,target,theorem,...}=held
       in {source=source,target=target,theorem=theorem} end)

    fun reject message = raise ERR "prepare_with_policy" message

    fun pc_prepare_internal ({metrics,abstractor} : ''locus prover) admission
        surface
        (request as {graph,scope,sources,work,ordinal,original,law,
         check_type,scope_opened,native_contract,profiles} : policy_owner) =
      let
        val native=NC.for_work work native_contract
        val limits= #semantic_limits native
        val policy_limits=W.semantic_policy work
        val native_used=ref (0:IntInf.int)
        val native_work=IntInf.fromInt (#type_work_limit native)
        val root = S.owning_scope sources
        val selected=Option.map (F.describe_with_policy_for
          {graph=graph,scope=scope,sources=sources,work=work}) admission
        val source_limit=case selected of NONE=> #input_limit limits
          | SOME d=> (case #category d of F.Original=> #input_limit limits
              | F.Generated=> #output_limit limits
              | F.Auxiliary=> #template_limit limits)
        val source_policy=case selected of NONE=> #input_limit policy_limits
          | SOME d=> #source_limit d
        val epoch = Type.type_epoch ()
        val fresh = ref ([] : G.scope list)
        val held = ref ([] : (G.scope * G.binder_closure) list)
        val hooks = metrics {graph=graph,scope=scope,profiles=profiles}
        val constants = ref (stock_constants ())
        fun active () =
          (NC.validate_for work native_contract;
           W.validate_policy work graph root sources policy_limits;
           G.validate_scope graph scope;
           (case admission of NONE => () | SOME held =>
             let val d = F.describe_with_policy_for
                   {graph = graph,scope = scope,sources = sources,work = work}
                   held
             in if #node d = original andalso
                 #source_limit d = source_policy then () else
               raise ERR "active" "different admitted carrier profile" end);
           (case surface of Canonical child =>
              if G.closure_child_node graph scope child = original then ()
              else raise ERR "active" "different canonical root handle");
           retained_live graph
             {epoch = epoch,constants = constants,fresh = fresh,held = held};
           #revalidate hooks ())
        fun charge n =
          (active ();
           if n>=0 andalso !native_used+IntInf.fromInt n<=native_work then ()
             else raise ERR "prepare_policy"
               "native planning allowance exhausted";
           W.spend_policy work (IntInf.fromInt n);
           native_used:= !native_used+IntInf.fromInt n)
        val {weight,shape_weight} = weights
          {charge = charge,origin = "prepare_with_policy"}
        fun cached metadata cap node metric =
          let val _=charge 1
              val d= #measure hooks node
              val count=case metric of G.RawNodes=> #raw d
                | G.BinderInclusiveNodes=> #inc d
          in if count<=IntInf.fromInt cap andalso RP.allows metadata count then
              () else reject "native or metadata syntax cap" end
        fun admit metadata cap node =
          (cached metadata cap node G.RawNodes;
           cached metadata cap node G.BinderInclusiveNodes)
        val queued = ref ([] : Type.hol_type list)
        fun queue ty = (charge 1;queued := ty :: !queued)
        (* Callback-free original/canonical/type inventory FIRST. Genuine
           import and recorded opening are separate existing prerequisites. *)
        val initial = W.with_step work (fn () =>
          let
            val _ = active ()
            val _ = if ordinal >= 0 then () else reject "negative ordinal"
            val source = case surface of Canonical child =>
              G.closure_child_node graph scope child
            val _ = admit source_policy source_limit source
            val (operator,predicate) = case G.view graph source of
                G.Application pair => pair
              | _ => reject "not a quantifier application"
            val predicate_child = case surface of Canonical child =>
                #2 (G.closure_application_children graph scope child)
            val closure = predicate_closure {graph = graph,scope = scope,
              predicate_child = predicate_child,predicate = predicate,
              held = held,origin = "prepare_with_policy"}
            (* Constructed/rehome closures retain their genuine creation
               frames. They do NOT acquire a fabricated raw Source origin.
               This branch permits a later step on a generated BAG guard. *)
            val {universal,carrier,domain,fixed} = classify {graph = graph,
              operator = operator,predicate = predicate,weight = weight,
              origin = "prepare_with_policy"}
            val _ = P.validate_closed_fact_with_policy graph root
              (#template_limit policy_limits) law
            val _ = admit (#template_limit policy_limits)
              (#template_limit limits) (P.closed_node law)
            val _ = if Portable.pointer_eq (P.closed_original law,fixed)
              then () else reject "not the exact selected original stock law"
            val types = ref ([] : Type.hol_type list)
            val visit = size_walk {graph = graph,charge = charge,
              weight = weight,held = held,constants = constants,
              types = types,locate = #locate hooks,opaque = #opaque hooks}
            val (ps,body_size) = predicate_sizes graph visit scope
              predicate_child closure
            val _ = active ()
          in {source = source,predicate = predicate,carrier = carrier,
              domain = domain,universal = universal,size = ps,
              body_size = body_size,types = !types} end)
        (* H preparation hooks SAME Work. Its supplied policy only queues
           admitted types: no external callback precedes carrier
           reservation. *)
        val producer = H.begin_original_with_policy graph root
          {original=law,native_contract=native_contract,
           check_type=queue,work=work}
        val variables = H.type_variables_with_policy producer
        val bindings = law_bindings "prepare_with_policy" (#domain initial)
          variables
        val hplan = case #domain initial of
            NONE => H.prepare_identity_with_policy producer
          | SOME _ => H.prepare_with_policy producer {bindings = bindings}
        val result = W.with_step work (fn () =>
          let
            val metadata = H.planned_syntax_with_policy hplan
            val {target,left,old_carrier} = carrier_exprs
              {universal = #universal initial,domain = #domain initial,
               carrier = #carrier initial,predicate = #predicate initial}
            val shapes = ref ([] : shape list)
            val size = expr_size {graph = graph,
              predicate = #predicate initial,existing = #size initial,
              charge = charge,shape_weight = shape_weight,shapes = shapes}
            val rhs = size target val lhs = size left
            val ps = #size initial
            val pweight = weight (G.type_of graph (#predicate initial))
            val _ = if schema_agrees weight
                {raw = #raw metadata,binder = #binder metadata,
                 typed_annotations = #typed_annotations metadata}
                {ps = ps,pweight = pweight,lhs = lhs,rhs = rhs} then () else
              reject "fixed one-P-per-side law schema differs"
            val cw = shape_weight old_carrier
            val qw = shape_weight (Arrow (Arrow (old_carrier,bool_shape),
              bool_shape))
            val {source_size,application,uncontracted,proof,...} =
              proof_sizes {lhs = lhs,rhs = rhs,ps = ps,
                body_size = #body_size initial,pweight = pweight,cw = cw,
                qw = qw}
            val bound = bound "prepare_with_policy"
            fun output n=(bound (#output_limit limits) n;
              if RP.allows (#output_limit policy_limits) n then () else
                reject "prospective output exceeds metadata policy")
            val _ = List.app (fn (z : size) =>
              (output (#raw z);output (#binder z))) (rhs :: proof)
            (* This lhs is constructed by SPEC, not an original input. *)
            val _ = List.app output
              [#raw lhs,#binder lhs]
            val actual= #measure_source hooks (#source initial)
            val _=if #raw actual= #raw source_size andalso
                #inc actual= #binder source_size then () else
              reject "canonical source forecast differs"
            (* Annotation work is charged independently to SAME Work, not
               invented as an annotation <= semantic syntax cap rule. Each
               produced theorem's full repeated annotations are retained. *)
            val amount = carrier_amount {lhs = lhs,rhs = rhs,
              source_size = source_size,application = application,
              uncontracted = uncontracted,proof = proof}
            val _ = shapes := proof_shapes old_carrier @ !shapes
            val _=if amount>0 andalso !native_used+amount<=native_work andalso
                RP.allows (W.remaining_policy work) amount then () else
              reject "carrier portfolio exceeds native or Work allowance"
            val token=W.reserve_policy work
              {role=W.LocalCarrier,ordinal=ordinal,amount=amount}
            val _=native_used:= !native_used+amount
            val _ = issue_types {active = active,check_type = check_type,
              queued = queued,types = #types initial,shapes = shapes}
          in PolicyPlan {request = request,surface = surface,active = active,
            limits = limits,
            hplan = hplan,predicate = #predicate initial,target = target,
            token = token,amount = amount,used = ref false,
            fresh = fresh,abstract = abstractor native_used} end)
      in result end
      handle primary => (W.close work;raise primary)

    fun prepare_admitted prover
        ({graph,scope,sources,work,ordinal,admission,law,native_contract,
          profiles,check_type,scope_opened}:policy_admitted_request) =
      ((NC.validate_for work native_contract;
        let val actual=W.original_sources work
            val _=if Portable.pointer_eq (actual,sources) andalso
                Portable.pointer_eq (graph,S.owning_graph actual) then () else
              raise ERR "prepare_policy" "different original Source owner"
            val d=F.describe_with_policy_for
              {graph=graph,scope=scope,sources=sources,work=work} admission
        in pc_prepare_internal prover (SOME admission) (Canonical (#child d))
          {graph=graph,scope=scope,sources=sources,work=work,
           ordinal=ordinal,original= #node d,law=law,
           native_contract=native_contract,profiles=profiles,
           check_type=check_type,scope_opened=scope_opened} end)
       handle primary=>(W.close work;raise primary))

    fun execute
        (PolicyPlan {request as {graph,scope,sources,work,original,
        scope_opened,...},surface,active,limits,hplan,predicate,target,token,
        amount,
        used,fresh,abstract}) =
      let
        val root = S.owning_scope sources
        val _ = W.with_step work (fn () =>
          (active ();
           if !used then raise ERR "execute_with_policy"
             "policy_plan already consumed"
           else used := true))
        val instance = H.execute_with_policy hplan
        val result = W.with_step work (fn () =>
          let
            fun guard () =
              (active ();H.validate_instance_with_policy_for
                {graph=graph,scope=root,work=work} instance)
            val _ = guard ()
            val _ = W.consume_policy work token amount
            val abstract = abstract
              {graph=graph,work=work,request=request,limits=limits,
               guard=guard}
            val candidate = build_target {graph = graph,guard = guard,
              scope_opened = scope_opened,fresh = fresh,abstract = abstract,
              origin = "execute_with_policy"} scope target
            val typed = H.typed_theorem_with_policy instance
            val theorem = carrier_proof {graph = graph,guard = guard,
              typed = typed,predicate = predicate,alignment_source = original,
              candidate = candidate}
            val _ = check_boundary {graph = graph,original = original,
              candidate = candidate,theorem = theorem,
              origin = "execute_with_policy",
              message = "exact closed policy_conversion boundary differs"}
            val _ = guard ()
          in PolicyConversion {request = request,active = guard,
            source = original,target = candidate,theorem = theorem} end)
      in result end
      handle primary =>
        (W.close work;List.app (fn frame =>
           (G.close_scope graph frame handle _ => ())) (!fresh);raise primary)

    (* The ordinary prover sizes a node at its own frame, keys its memo by
       node and rejects an opaque node. *)
    val ordinary_metric : G.node metrics =
      fn {graph,scope,profiles} =>
        {revalidate = fn () => (),
         locate = fn _ => fn _ => fn node => node,
         measure = fn node =>
           let val fixed = G.node_scope graph node
               val plan = G.prepare_profiled_metric graph fixed
                 {node = node,profiles = profiles}
           in G.profiled_metric_data graph fixed plan end,
         measure_source = fn node =>
           let val plan = G.prepare_profiled_metric graph scope
                 {node = node,profiles = profiles}
           in G.profiled_metric_data graph scope plan end,
         opaque = fn _ => fn _ =>
           reject "nested original binder needs genuine opening"}
    val ordinary_abstractor : abstractor =
      fn _ => fn {graph,limits,...} => fn caller =>
        fn {binder,body,body_frame} =>
          G.recorded_abstraction_with_policy graph caller
            (RP.AtMost (IntInf.fromInt (#output_limit limits)))
            {binder = binder,body = body,body_frame = body_frame}

    (* The profiled prover sizes at the actual scope, keys its memo by node
       and effective scope, selects a genuine profile for an opaque node and
       revalidates every metric and profile it retained. Its abstractor
       charges native steps. *)
    val profiled_metric : (G.node * G.scope) metrics =
      fn {graph,scope,profiles} =>
        let
          val metrics = ref ([] : (G.scope * G.profiled_metric) list)
          val opaque =
            ref ([] : (G.scope * G.node * G.policy_opaque_profile) list)
          fun measure node =
            let val plan = G.prepare_scoped_profiled_metric graph scope
                  {node = node,profiles = profiles}
                val d = G.profiled_metric_data graph scope plan
                val _ = metrics := (scope,plan) :: !metrics
            in d end
          fun revalidate () =
            (List.app (fn (frame,metric) => ignore
               (G.profiled_metric_data graph frame metric)) (!metrics);
             List.app (fn (frame,node,profile) => case
                 G.opaque_profile_for_node_with_policy graph frame node
                   profile of
                   SOME _ => () | NONE => raise ERR "profiled_carrier"
                     "actual selected opaque profile changed") (!opaque))
          fun select (node,effective) w charge weigh types =
            let fun go [] = reject "opaque predicate lacks genuine profile"
                  | go (p :: rest) =
                      (charge 1;case G.opaque_profile_for_node_with_policy
                         graph effective node p of
                         NONE => go rest
                       | SOME data =>
                           (opaque := (effective,node,p) :: !opaque;data))
                val data = go profiles
                val _ = if #ty data = w then () else
                  reject "actual opaque Type size differs"
                val _ = List.app (fn ty =>
                  (ignore (weigh ty);types := ty :: !types)) (#types data)
            in {raw = #raw data,binder = #inc data,ann = #ann data} : size end
        in
          {revalidate = revalidate,
           locate = fn caller => fn child => fn node =>
             (node,G.closure_child_scope graph caller child),
           measure = measure,measure_source = measure,
           opaque = fn locus => fn {weight = w,charge,weigh,types} =>
             select locus w charge weigh types}
        end
    val profiled_abstractor : abstractor =
      fn native_used => fn {graph,work,request,limits,guard} =>
        let
          val native = NC.for_work work (#native_contract request)
          val native_ceiling = IntInf.fromInt (#type_work_limit native)
          fun native_step () =
            (guard ();
             if !native_used < native_ceiling then () else
               raise ERR "execute_profiled" "native model gate exhausted";
             W.spend_policy work 1;native_used := !native_used + 1;guard ())
        in
          fn caller => fn {binder,body,body_frame} =>
            G.recorded_abstraction_with_profile_policy graph caller
              {maximum = #output_limit (W.semantic_policy work),
               native_limit = #output_limit limits,
               type_work_limit = #type_work_limit native,
               binder = binder,body = body,body_frame = body_frame,
               profiles = #profiles request,step = native_step}
        end
    val ordinary_prover : G.node prover =
      {metrics = ordinary_metric,abstractor = ordinary_abstractor}
    val profiled_prover : (G.node * G.scope) prover =
      {metrics = profiled_metric,abstractor = profiled_abstractor}
  in
    type policy_plan = policy_plan
    type policy_conversion = policy_conversion
    val validate_with_policy_for = validate_with_policy_for
    val endpoints_with_policy_for = endpoints_with_policy_for
    fun prepare_closure_admitted_with_policy request =
      prepare_admitted ordinary_prover request
    val execute_with_policy = execute
    type profiled_policy_plan = policy_plan
    type profiled_policy_conversion = policy_conversion
    fun prepare_closure_profiled_admitted_with_policy request =
      prepare_admitted profiled_prover request
    val execute_profiled_with_policy = execute
    val validate_profiled_with_policy_for = validate_with_policy_for
    val endpoints_profiled_with_policy_for = endpoints_with_policy_for
  end

end
