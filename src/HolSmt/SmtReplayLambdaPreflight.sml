(* Canonical syntax only; no raw body provenance or proof authority issuance. *)
structure SmtReplayLambdaPreflight :> SmtReplayLambdaPreflight =
struct
  structure G = SmtReplayGraph
  structure P = SmtReplayProof
  structure S = SmtReplaySource
  structure W = SmtReplayInvocationWork
  structure A = SmtReplayFocusAdmission
  val _ = SmtReplayFocusAdmission.describe_for
  val ERR = Feedback.mk_HOL_ERR "SmtReplayLambdaPreflight"
  type request =
    {graph : G.graph,scope : G.scope,sources : S.sources,
     work : W.portfolio,ordinal : int,body_scope : G.scope,
     declaring_scope : G.scope,old_lambda : G.node,binder : G.node,
     equality : G.node,left : G.node,right : G.node,
     body_fact : P.closed_fact}
  type admitted_request =
    {request : request,source_scope : G.scope,admission : A.focus}
  type size = {raw : IntInf.int,inclusive : IntInf.int,
               annotations : IntInf.int,ty : IntInf.int}
  datatype held = Child of G.scope * G.closure_child
    | Binder of G.scope * G.binder_closure
  datatype shape = Actual of Type.hol_type | Boolean | Arrow of shape * shape
  type summary =
    {compact_context : IntInf.int * IntInf.int,
     compact_law : IntInf.int * IntInf.int,
     actual_context : IntInf.int * IntInf.int * IntInf.int,
     actual_law : IntInf.int * IntInf.int * IntInf.int,
     body : IntInf.int * IntInf.int * IntInf.int,
     lambda_result : IntInf.int * IntInf.int * IntInf.int,
     reserved_annotations : IntInf.int,reserved_render_work : IntInf.int,
     surviving_hypotheses : int}
  datatype plan = Plan of
    {request : request,limits : W.limits,epoch : int,held : held list,
     types : Type.hol_type list,generated : shape list,summary : summary,
     rendered : bool ref,admission : (G.scope * A.focus) option}

  fun same (a : request) (b : request) =
    Portable.pointer_eq (#graph a,#graph b) andalso #scope a = #scope b andalso
    Portable.pointer_eq (#sources a,#sources b) andalso
    Portable.pointer_eq (#work a,#work b) andalso #ordinal a = #ordinal b
    andalso #body_scope a = #body_scope b andalso
    #declaring_scope a = #declaring_scope b andalso
    #old_lambda a = #old_lambda b andalso #binder a = #binder b andalso
    #equality a = #equality b andalso #left a = #left b andalso
    #right a = #right b andalso
    Portable.pointer_eq (#body_fact a,#body_fact b)
  (* Expected receipt ownership precedes foreign activation. Keep the
     original Work root distinct from the actual traversal source frame. *)
  fun source_limit (request : request) admission limits =
    case admission of NONE => #input_limit (limits : W.limits)
    | SOME (source_scope,focus) =>
      let val {graph,sources,work,old_lambda,binder,left,body_scope,
               declaring_scope,...} = request
          val d = A.describe_for
            {graph = graph,scope = source_scope,sources = sources,work = work}
            focus
          val closure = G.closure_child_binder graph source_scope (#child d)
          val captured = G.binder_closure_data graph source_scope closure
          val _ = if #node d = old_lambda andalso
              #node captured = old_lambda andalso #binder captured = binder
              andalso #body captured = left andalso
              #body_frame captured = body_scope andalso
              #node_frame captured = declaring_scope then () else
            raise ERR "admission" "different lambda or actual binder frame"
      in #source_limit d end
  fun validate request (Plan {request = original,limits,epoch,held,
                              admission,...}) =
    let
      val {graph,scope,sources,work,...} = request
      val _ = W.validate work graph scope sources limits
      val _ = source_limit request admission limits
      val _ = if same request original andalso Type.type_epoch () = epoch
        then () else raise ERR "validate" "owner, endpoints or epoch changed"
      val _ = if P.closed_node (#body_fact request) = #equality request
        then () else raise ERR "validate" "different opaque closed evidence"
      fun check (Child (caller,child)) =
            ignore (G.closure_child_node graph caller child)
        | check (Binder (caller,closure)) =
            ignore (G.binder_closure_data graph caller closure)
    in List.app check held end
    handle primary => (W.close (#work request);raise primary)
  fun report (Plan {summary,...}) = summary

  fun prepare_internal admission (request as
      {graph,scope,sources,work,ordinal,body_scope,declaring_scope,
       old_lambda,binder,equality,left,right,body_fact}) =
    let
      val limits = W.semantic_limits work
      val _ = W.validate work graph scope sources limits
      val source_cap = source_limit request admission limits
      val epoch = Type.type_epoch ()
      val _ = if ordinal >= 0 then () else
        raise ERR "prepare" "negative original closure ordinal"
      val ceiling = IntInf.fromInt (W.work_limit work)
      val node_ceiling = IntInf.fromInt (Int.max (#template_limit limits,
        Int.max (#input_limit limits,#output_limit limits)))
      (* Saturation is limit+1 in IntInf, never machine-int wraparound. *)
      fun sum cap a b = IntInf.min (cap+1,a+b)
      fun plus a b = sum ceiling a b
      fun times a b = IntInf.min (ceiling+1,a*b)
      fun raw_plus a b = sum node_ceiling a b
      fun active () =
        (W.validate work graph scope sources limits;
         ignore (source_limit request admission limits);
         if Type.type_epoch () = epoch then () else
           raise ERR "prepare" "Type epoch changed")
      fun charge n = (active ();W.spend work n)
      (* Cached original graph admission precedes even the annotation walk.
         A saturated SOME(limit+1) is a refusal, not successful metadata. *)
      fun cached label cap node metric =
        (charge 1;case G.unfolded_nodes graph metric cap node of
           SOME count => if count <= cap then () else
             raise ERR "prepare" (label ^ " exceeds original metric cap")
         | NONE => raise ERR "prepare" (label ^ " has unknown metadata"))
      fun admit label cap node =
        (cached label cap node G.RawNodes;
         cached label cap node G.BinderInclusiveNodes)
      val _ = admit "source lambda" source_cap old_lambda
      val _ = admit "closed body equality" (#template_limit limits) equality
      val _ = admit "body left" source_cap left
      val _ = admit "body right" (#output_limit limits) right
      val held = ref ([] : held list)
      val types = ref ([] : Type.hol_type list)
      val type_memo = ref ([] : (Type.hol_type * IntInf.int) list)
      fun type_lookup ty [] = NONE
        | type_lookup ty ((old,count)::rest) =
            (charge 1;if Portable.pointer_eq (ty,old) then SOME count
             else type_lookup ty rest)
      fun type_size ty = case type_lookup ty (!type_memo) of
          SOME count => count
        | NONE =>
          let
            (* Borrow each argument spine, charging BEFORE its inspection.
               No Args@rest, whole list length or type constructor here. *)
            fun walk [] total = total
              | walk (pending::more) total =
                (charge 1;case pending of [] => walk more total
                 | current::rest =>
                   let val _ = charge 1
                       val total = plus total 1
                       val _ = if total <= ceiling then () else
                         raise ERR "prepare" "type shape exceeds Work"
                   in if Type.is_vartype current then walk (rest::more) total
                      else walk (#2 (Type.dest_type current)::rest::more)
                        total end)
            val count = walk [[ty]] 0
            val _ = charge 1
            val _ = type_memo := (ty,count) :: !type_memo
          in count end
      fun annotate node =
        let val _ = charge 1
            val ty = G.type_of graph node
            val count = type_size ty
            val _ = charge 1
            val _ = types := ty :: !types
        in count end
      val memo = ref ([] : (G.node * size) list)
      fun lookup node [] = NONE
        | lookup node ((old,value)::rest) =
            (charge 1;if old = node then SOME value else lookup node rest)
      fun hold_child caller child =
        (charge 1;held := Child (caller,child) :: !held;
         G.closure_child_node graph caller child)
      fun visit caller child =
        let val node = hold_child caller child in
          case lookup node (!memo) of SOME value => value
          | NONE =>
            let
              val ty = annotate node
              val value = case G.view graph node of
                  G.Application _ =>
                    let val _ = charge 1
                        val (a,b) =
                          G.closure_application_children graph caller child
                        val l = visit caller a val r = visit caller b
                    in {raw = raw_plus 1 (raw_plus (#raw l) (#raw r)),
                        inclusive = raw_plus 1
                          (raw_plus (#inclusive l) (#inclusive r)),
                        annotations = plus ty
                          (plus (#annotations l) (#annotations r)),ty = ty}
                        : size end
                | G.AdmittedBinder _ =>
                    let
                      val _ = charge 1
                      val origin = G.closure_child_binder graph caller child
                      val _ = charge 1
                      val _ = held := Binder (caller,origin) :: !held
                      val d = G.binder_closure_data graph caller origin
                      val variable_ty = annotate (#binder d)
                      val _ = charge 1
                      val body = visit caller
                        (G.binder_closure_body graph caller origin)
                    in {raw = raw_plus 1 (#raw body),
                        inclusive = raw_plus 2 (#inclusive body),
                        annotations = plus ty
                          (plus variable_ty (#annotations body)),ty = ty}
                        : size end
                | G.OpaqueRetained => raise ERR "prepare"
                    "unknown body closure/type annotations"
                | _ => {raw = 1,inclusive = 1,annotations = ty,ty = ty}
                    : size
              val _ = charge 1
              val _ = memo := (node,value) :: !memo
            in value end
        end
      fun root caller node =
        (charge 1;visit caller (G.closure_root graph caller node))
      val old = root declaring_scope old_lambda
      val body = root body_scope equality
      val _ = charge 1
      val old_closure = G.binder_closure graph declaring_scope old_lambda
      val _ = charge 1
      val _ = held := Binder (declaring_scope,old_closure) :: !held
      val captured = G.binder_closure_data graph declaring_scope old_closure
      val _ = if #binder captured = binder andalso #body captured = left
          andalso #body_frame captured = body_scope then () else
        raise ERR "prepare" "different captured binder or exact body frame"
      (* The consumer supplies a CLOSED equality fact. Check this node's
         exact graph constructor shape before forecasting P's syntax. *)
      val _ = charge 1
      val (partial,actual_right) = case G.view graph equality of
          G.Application pair => pair
        | _ => raise ERR "prepare" "body evidence is not equality syntax"
      val _ = charge 1
      val (operator,actual_left) = case G.view graph partial of
          G.Application pair => pair
        | _ => raise ERR "prepare" "body evidence lacks equality operator"
      val _ = charge 1
      val _ = case G.view graph operator of G.Constant id =>
          if KernelSig.id_compare (id,
              #Name (Term.dest_thy_constid boolSyntax.equality)) = EQUAL
          then () else
            raise ERR "prepare" "different equality declaration"
        | _ => raise ERR "prepare" "body equality operator not constant"
      val _ = if actual_left = left andalso actual_right = right then () else
        raise ERR "prepare" "different equality endpoints"
      fun saved node = case lookup node (!memo) of SOME value => value
        | NONE => raise ERR "prepare" "endpoint outside exact equality DAG"
      val lhs = saved left and rhs = saved right
      val binder_ty = annotate binder
      val lambda_ty = #ty old
      val _ = if lambda_ty = plus 1 (plus binder_ty (#ty rhs)) andalso
          G.type_id graph left = G.type_id graph right then () else
        raise ERR "prepare" "lambda/body type shape differs"
      fun require label cap count =
        if count <= IntInf.fromInt cap then () else
          raise ERR "prepare" (label ^ " exceeds original contract")
      val _ = require "source raw" source_cap (#raw old)
      val _ = require "source binder" source_cap (#inclusive old)
      (* Exact P reachable grammar: applications recurse; binders are atoms.
         Each actual walk/spine/seen comparison is billed before inspection. *)
      fun seen node [] = false
        | seen node (old::rest) =
            (charge 1;old = node orelse seen node rest)
      val definitions = ref ([] : G.node list)
      fun walk [] _ = ()
        | walk (pending::more) visited =
          (charge 1;case pending of [] => walk more visited
           | node::rest =>
             (charge 1;
              if seen node visited then walk (rest::more) visited
              else case G.view graph node of
                  G.Application (a,b) =>
                    (charge 3;definitions := node :: !definitions;
                     walk ([a,b]::rest::more) (node::visited))
                | G.Constant _ =>
                    (charge 1;definitions := node :: !definitions;
                     walk (rest::more) (node::visited))
                | _ => walk (rest::more) (node::visited)))
      val _ = walk [[equality]] []
      (* One ClosedWitness name is the first leaf. Each new definition
         adds one conjunction join: raw3, exact type annotations9. *)
      val c_raw = ref (1 : IntInf.int) and c_ann = ref (1 : IntInf.int)
      val a_raw = ref (#raw body) and a_inc = ref (#inclusive body)
      val a_ann = ref (#annotations body)
      val generated = ref ([] : shape list)
      fun equality_types ty =
        [Arrow (Actual ty,Arrow (Actual ty,Boolean)),
         Arrow (Actual ty,Boolean)]
      fun definition node =
        let
          val _ = charge 1 val n = saved node
          val ty = G.type_of graph node val t = #ty n
          val (r,ann) = case G.view graph node of G.Constant _ =>
              (5,plus 6 (times 5 t))
            | G.Application (f,x) =>
                (7,plus 6 (plus (times 5 t)
                  (plus (#ty (saved f)) (#ty (saved x)))))
            | _ => raise ERR "prepare" "different P definition grammar"
          val _ = charge 2
          val _ = generated := equality_types ty @ !generated
          val _ = c_raw := raw_plus (!c_raw) (raw_plus r 3)
          val _ = c_ann := plus (!c_ann) (plus ann 9)
          val _ = a_raw := raw_plus (!a_raw)
            (raw_plus 6 (raw_plus (#raw n) (#raw n)))
          val _ = a_inc := raw_plus (!a_inc)
            (raw_plus 6 (raw_plus (#inclusive n) (#inclusive n)))
          (* Equality shell: (3+2t)+(2+t)+1 = 6+3t.
             Both actual definition endpoints have annotation A(n). *)
          val _ = a_ann := plus (!a_ann)
            (plus 15 (plus (times 3 t) (times 2 (#annotations n))))
        in () end
      val _ = List.app definition (!definitions)
      val compact_law_raw = raw_plus 4 (!c_raw)
      val compact_law_ann = plus 10 (!c_ann)
      val actual_law_raw = raw_plus 3 (raw_plus (!a_raw) (#raw body))
      val actual_law_inc = raw_plus 3
        (raw_plus (!a_inc) (#inclusive body))
      val actual_law_ann = plus 9 (plus (!a_ann) (#annotations body))
      val new_raw = raw_plus 1 (#raw rhs)
      val new_inc = raw_plus 2 (#inclusive rhs)
      val new_ann = plus lambda_ty
        (plus binder_ty (#annotations rhs))
      val result_raw = raw_plus 3 (raw_plus (#raw old) new_raw)
      val result_inc = raw_plus 3 (raw_plus (#inclusive old) new_inc)
      val result_ann = plus 6
        (plus (times 3 lambda_ty) (plus (#annotations old) new_ann))
      val _ = List.app (require "compact context/law"
        (#template_limit limits)) [!c_raw,compact_law_raw]
      (* P context, discharged law, body evidence and final equality are
         operational proof syntax, not the converted lambda result. *)
      val _ = List.app (require "realized proof raw/binder portfolio"
        (#template_limit limits))
        [!a_raw,!a_inc,actual_law_raw,actual_law_inc,
         #raw body,#inclusive body,result_raw,result_inc]
      val _ = List.app (require "converted lambda raw/binder result"
        (#output_limit limits)) [new_raw,new_inc]
      (* This exact sum is annotation inventory, NOT an estimated bound on
         private kernel/graph operations or a new symbol-byte allowance. *)
      val annotations = List.foldl (fn (n,total) => plus total n) 0
        [!c_ann,compact_law_ann,!a_ann,actual_law_ann,
         #annotations body,#annotations old,new_ann,result_ann]
      val _ = if annotations <= ceiling then () else
        raise ERR "prepare" "annotation inventory exceeds original Work"
      (* These exact Boolean operators occur in P's context/implication and
         final lambda equality; no types are constructed before reservation. *)
      val _ = charge 8
      val generated = equality_types (G.type_of graph old_lambda) @
        [Arrow (Boolean,Arrow (Boolean,Boolean)),Arrow (Boolean,Boolean),
         Boolean] @ !generated
      (* Reserve the actual future renderer/list work separately from term
         annotation multiplicity. Each Arrow visits two children, constructs
         an exact two-element argument spine, and one fun Type. Internal
         declaration lookup/symbol work is not certified by this inventory. *)
      fun render_work (Actual _) = (charge 1;1)
        | render_work Boolean = (charge 1;1)
        | render_work (Arrow (a,b)) =
            (charge 1;plus 4 (plus (render_work a) (render_work b)))
      fun pending_work [] total = total
        | pending_work (item::rest) total =
            (charge 1;pending_work rest (plus total
              (plus 2 (render_work item))))
      fun original_list_work [] total = total
        | original_list_work (_::rest) total =
            (charge 1;original_list_work rest (plus total 1))
      val render_cost = original_list_work (!types)
        (pending_work generated 0)
      val total = plus annotations render_cost
      val _ = if total <= ceiling then () else
        raise ERR "prepare" "syntax and renderer exceed original Work"
      val token = W.reserve work
        {role = W.LocalCarrier,ordinal = ordinal,amount = IntInf.toInt total}
      val _ = W.consume work token (IntInf.toInt total)
      (* This is retained opaque P evidence, not a supplied theorem or
         source/body pair. Only AFTER the complete syntax portfolio is
         charged inspect its clean, empty-Hyp, exact canonical boundary. *)
      val _ = active ()
      val _ = P.validate_closed_fact graph body_scope
        (#template_limit limits) body_fact
      val _ = active ()
      val _ = if P.closed_node body_fact = equality then () else
        raise ERR "prepare" "different closed body equality node"
      val summary =
        {compact_context = (!c_raw,!c_ann),
         compact_law = (compact_law_raw,compact_law_ann),
         actual_context = (!a_raw,!a_inc,!a_ann),
         actual_law = (actual_law_raw,actual_law_inc,actual_law_ann),
         body = (#raw body,#inclusive body,#annotations body),
         lambda_result = (result_raw,result_inc,result_ann),
         reserved_annotations = annotations,reserved_render_work = render_cost,
         surviving_hypotheses = 0}
      val result = Plan {request = request,limits = limits,epoch = epoch,
        held = !held,types = !types,generated = generated,
        summary = summary,rendered = ref false,admission = admission}
      val _ = validate request result
    in result end
    handle primary => (W.close work;raise primary)

  fun prepare request = prepare_internal NONE request
  fun prepare_admitted {request,source_scope,admission} =
    prepare_internal (SOME (source_scope,admission)) request

  fun policy_types request (plan as Plan {types,generated,rendered,...}) =
    let
      val _ = validate request plan
      val _ = W.spend (#work request) 0 (* SAME caller's active owned action *)
      val _ = if not (!rendered) then rendered := true else
        raise ERR "policy_types" "generated types already rendered"
      fun render (Actual ty) = ty
        | render Boolean = Type.bool
        | render (Arrow (a,b)) =
          let val left = render a val right = render b
              val _ = validate request plan
              val result = Type.mk_type ("fun",[left,right])
              val _ = validate request plan
          in result end
    in List.map render generated @ types end
    handle primary => (W.close (#work request);raise primary)
end
