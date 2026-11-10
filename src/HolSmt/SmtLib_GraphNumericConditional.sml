(* SAME Work primitive quotient of a genuine fixed numeric instance. *)
structure SmtLib_GraphNumericConditional :> SmtLib_GraphNumericConditional =
struct
  structure G = SmtReplayGraph
  structure S = SmtReplaySource
  structure W = SmtReplayInvocationWork
  structure P = SmtReplayProof
  structure K = SmtLib_GraphNumericCanonical
  structure M = SmtLib_GraphNumericRuleMatch
  structure F = SmtReplayOwnedScopeReceipt
  structure Core = SmtReplayOwnedLargeProofCore
  structure Lambda = SmtReplayOwnedRealizedLambda
  val _ = SmtLib_GraphNumericRuleMatch.instance_fact_for
  val _ = SmtReplayProof.record_closed_from_import
  val _ = SmtReplayOwnedLargeProofCore.realization_for
  val _ = SmtReplayOwnedRealizedLambda.theorem_for
  val ERR = Feedback.mk_HOL_ERR "SmtLib_GraphNumericConditional"
  type profile = {raw:IntInf.int,inc:IntInf.int,ann:IntInf.int}
  datatype owner = Owner of
    {work:W.portfolio,graph:G.graph,root:G.scope,sources:S.sources,
     catalogue:K.catalogue,check_type:Type.hol_type -> unit,
     symbols:int,dead:bool ref}
  datatype evidence = Recorded of P.closed_fact | Owned of Core.result
  datatype plan = Plan of
    {owner:owner,frame:F.receipt,scope:G.scope,instance:M.instance,
     seed:P.closed_fact,conditions:evidence list,
     pairs:(G.node * G.node) list,
     retained:G.closure_child list,used:bool ref}
  datatype result = Result of
    {owner:owner,frame:F.receipt,instance:M.instance,
     retained:G.closure_child list,fact:P.closed_fact}
  fun retire (Owner {work,dead,...}) = (dead := true;W.close work)
  fun protect owner action = action () handle primary =>
    (retire owner;raise primary)
  fun active (owner as Owner
      {work,graph,root,sources,catalogue,symbols,dead,...}) =
    protect owner (fn () =>
      (if !dead then raise ERR "active" "conditional owner retired" else ();
       W.validate work graph root sources (W.semantic_limits work);
       if Term.term_epoch () = symbols then () else
         raise ERR "active" "constant retirement epoch changed";
       K.validate_for work catalogue))
  fun begin work catalogue {check_type} =
    let val _ = K.validate_for work catalogue
        val sources = W.original_sources work
        val graph = S.owning_graph sources val root = S.owning_scope sources
    in Owner {work=work,graph=graph,root=root,sources=sources,
      catalogue=catalogue,check_type=check_type,symbols=Term.term_epoch (),
      dead=ref false} end handle primary => (W.close work;raise primary)
  fun guard owner action =
    (active owner;let val answer = action () in active owner;answer end)
  fun tick (owner as Owner {work,...}) =
    guard owner (fn () => W.spend work 1)
  fun add (p:profile) (q:profile) : profile =
    {raw= #raw p + #raw q,inc= #inc p + #inc q,ann= #ann p + #ann q}
  val zero : profile = {raw=0,inc=0,ann=0}
  fun equality (p:profile) : profile =
    {raw=3+2 * #raw p,inc=3+2 * #inc p,ann=9+2 * #ann p}
  fun evidence_node work graph scope cap value =
    case value of Recorded fact =>
      (P.validate_closed_fact graph scope cap fact;P.closed_node fact)
    | Owned receipt =>
      let val data = Core.conversion_description_for work receipt
          val _ = if Portable.pointer_eq (graph,#graph data) andalso
              scope = #scope data then () else
            raise ERR "evidence_node" "condition has a different actual frame"
          val realized = Core.realization_for work receipt
      in #equality (P.realization_data_for work realized) end
  fun evidence_theorem work value = case value of
      Recorded fact => P.closed_original fact
    | Owned receipt => Core.theorem_for work receipt
  fun prepare_internal (owner as Owner {work,graph,root,...})
      {frame,instance,conditions} = protect owner (fn () =>
    W.with_step work (fn () =>
    let val _ = active owner
        val where_ = F.description_for work frame
        val scope = #scope where_
        val _ = if Portable.pointer_eq (graph,#graph where_) andalso
            root = #root where_ then () else
          raise ERR "prepare" "foreign authentic frame"
        val seed = M.instance_fact_for work instance
        val _ = if #traversal (M.instance_target_for work instance)=scope
          then () else raise ERR "prepare" "instance has another body frame"
        val cap = #template_limit (W.semantic_limits work)
        val ceiling = IntInf.fromInt (W.work_limit work)
        val output = IntInf.fromInt (#output_limit (W.semantic_limits work))
        val retained = ref ([] : G.closure_child list)
        val types = ref ([] : Type.hol_type list)
        val quotes = ref ([] : profile list)
        fun live () =
          (active owner;ignore (F.description_for work frame);
           ignore (M.instance_fact_for work instance);
           List.app (fn item => ignore
             (evidence_node work graph scope cap item)) conditions;
           List.app (fn child => ignore
             (G.closure_child_node graph scope child)) (!retained))
        fun inspect action =
          (live ();let val answer = action () in live ();answer end)
        fun step () = (live ();W.spend work 1;live ())
        fun weight ty =
          (step ();if Type.is_vartype ty then
             (W.spend work (String.size (Type.dest_vartype ty));1)
           else let val {Thy,Tyop,Args} = Type.dest_thy_type ty
                    val _ = W.spend work (String.size Thy+String.size Tyop)
                in List.foldl (fn (t,n) => n+weight t)
                  (1:IntInf.int) Args end)
        fun bound (p:profile) =
          if #raw p <= output andalso #inc p <= output andalso
              #ann p <= ceiling then () else
            raise ERR "prepare" "primitive conditional result exceeds quota"
        fun quote p = (bound p;quotes := p:: !quotes)
        (* Full actual annotation occurrences, including each binder VAR.
           Cached complete syntax admission precedes the first type getter. *)
        fun profile node =
          let val _ = List.app (fn metric =>
                case G.unfolded_nodes graph metric
                    (#output_limit (W.semantic_limits work)) node of
                  SOME n => if IntInf.fromInt n <= output then () else
                    raise ERR "profile" "leaf exceeds original output"
                | NONE => raise ERR "profile" "missing complete leaf syntax")
                [G.RawNodes,G.BinderInclusiveNodes]
              fun walk traversal child =
                let val _ = step ()
                    val n = inspect (fn () =>
                      G.closure_child_node graph scope child)
                    val _ = G.validate_scope graph traversal
                    val ty = inspect (fn () => G.type_of graph n)
                    val ann = weight ty
                    val _ = types := ty:: !types
                    val _ = retained := child:: !retained
                    val actual = inspect (fn () => G.view graph n)
                in case actual of
                    G.Application _ =>
                      let val (f,x) = inspect (fn () =>
                            G.closure_application_children graph scope child)
                      in add {raw=1,inc=1,ann=ann}
                        (add (walk traversal f) (walk traversal x)) end
                  | G.AdmittedBinder _ =>
                      let val closure = inspect (fn () =>
                            G.closure_child_binder graph scope child)
                          val info = inspect (fn () =>
                            G.binder_closure_data graph scope closure)
                          val bt = inspect (fn () =>
                            G.type_of graph (#binder info))
                          val bw = weight bt val _ = types := bt:: !types
                          val body = inspect (fn () =>
                            G.binder_closure_body graph scope closure)
                      in add {raw=1,inc=2,ann=ann+bw}
                        (walk (#body_frame info) body) end
                  | G.OpaqueRetained => raise ERR "profile"
                      "closed conditional leaf needs genuine complete view"
                  | _ => {raw=1,inc=1,ann=ann}
                end
              val p = walk scope (G.closure_root graph scope node)
              val _ = bound p
          in p end
        fun binary thy name node =
          let fun view n = (step ();inspect (fn () => G.view graph n))
          in case view node of G.Application (partial,right) =>
             (case view partial of G.Application (head,left) =>
                (case view head of G.Constant id =>
                   let val {Thy,Name} = KernelSig.name_of_id id
                   in if Thy=thy andalso Name=name then SOME (left,right)
                      else NONE end
                 | _ => NONE)
              | _ => NONE)
           | _ => NONE end
        fun is_truth node =
          let val _ = step () val view = inspect (fn () => G.view graph node)
          in case view of G.Constant id =>
               let val expected = #Name (Term.dest_thy_constid boolSyntax.T)
               in KernelSig.id_compare (id,expected)=EQUAL end
           | _ => false end
        val _ = P.validate_closed_fact graph scope cap seed
        val start = P.closed_node seed val _ = quote (profile start)
        fun arrange current [] = (current,[])
          | arrange current (fact::rest) =
              let val (condition,next) = case binary "min" "==>" current of
                    SOME pair => pair
                  | NONE => raise ERR "prepare" "extra condition evidence"
                  val evidence = evidence_node work graph scope cap fact
                  val (left,right) = case binary "min" "=" evidence of
                    SOME pair => pair
                  | NONE => raise ERR "prepare" "condition is not equality"
                  val _ = if is_truth right then () else
                    raise ERR "prepare" "condition did not normalize to T"
                  val _ = quote (profile evidence) (* input and SYM *)
                  val _ = quote (profile evidence)
                  val _ = quote (profile left) (* EQ_MP with fixed TRUTH *)
                  val _ = quote (profile next) (* MP result *)
                  val (final,more) = arrange next rest
              in (final,(condition,left)::more) end
        val (final,pairs) = arrange start conditions
        val _ = if Option.isSome (binary "min" "==>" final) then
          raise ERR "prepare" "missing condition evidence" else ()
        val final_profile = profile final
        val _ = if #raw final_profile <= IntInf.fromInt cap andalso
            #inc final_profile <= IntInf.fromInt cap then () else
          raise ERR "prepare" "closed result exceeds original template"
        val _ = List.app quote [equality final_profile,
          equality final_profile,equality final_profile,final_profile]
        val _ = types := Type.bool:: !types
        val _ = quote {raw=1,inc=1,ann=1} (* fixed TRUTH *)
        val total = List.foldl (fn (p,n) =>
          n+ #raw p + #inc p + #ann p) (0:IntInf.int) (!quotes)
        val _ = if total <= ceiling then W.spend work (IntInf.toInt total)
          else raise ERR "prepare" "conditional portfolio exceeds Work"
        val Owner {check_type,...} = owner
        val _ = List.app (fn ty => inspect (fn () => check_type ty))
          (List.rev (!types))
        (* Semantic alpha check follows full syntax/type admission. These
           P facts grant neither original Source incidence nor past work. *)
        val _ = List.app (fn (wanted,actual) =>
          if inspect (fn () => Term.aconv (G.representative graph wanted)
              (G.representative graph actual)) then () else
            raise ERR "prepare" "condition belongs to a different premise")
          pairs
        val _ = live ()
    in Plan {owner=owner,frame=frame,scope=scope,instance=instance,seed=seed,
      conditions=conditions,pairs=pairs,retained= !retained,used=ref false}
    end))
  fun prepare owner {frame,instance,conditions} =
    prepare_internal owner
      {frame=frame,instance=instance,conditions=List.map Recorded conditions}
  (* Only opaque SAME-Work completed proofs; no theorem/target pair or
     externally supplied normalizer. The recursive producer fixes context. *)
  fun prepare_owned owner {frame,instance,conditions} =
    prepare_internal owner
      {frame=frame,instance=instance,conditions=List.map Owned conditions}
  fun execute (Plan {owner=owner as Owner {work,graph,check_type,...},
      frame,scope,instance,seed,conditions,pairs,retained,used}) =
    protect owner (fn () => W.with_step work (fn () =>
    let val _ = active owner
        val _ = if !used then raise ERR "execute" "conditional plan consumed"
          else used := true
        val cap = #template_limit (W.semantic_limits work)
        val paths = ref retained
        fun live () =
          (active owner;ignore (F.description_for work frame);
           ignore (M.instance_fact_for work instance);
           List.app (fn item => ignore
             (evidence_node work graph scope cap item)) conditions;
           List.app (fn child => ignore
             (G.closure_child_node graph scope child)) (!paths))
        fun invoke action =
          (live ();let val answer = action () in live ();answer end)
        fun discharge (fact,theorem) =
          let val equality = invoke (fn () => evidence_theorem work fact)
              val sym = invoke (fn () => Thm.SYM equality)
              val condition = invoke (fn () =>
                Thm.EQ_MP sym boolTheory.TRUTH)
          in invoke (fn () => Thm.MP theorem condition) end
        val theorem = List.foldl discharge (P.closed_original seed) conditions
        val _ = if null (Thm.hyp theorem) then () else
          raise ERR "execute" "conditional proof acquired Source hypotheses"
        val imported = invoke (fn () => G.import graph scope cap
          (Thm.concl theorem))
        val opened = invoke (fn () => G.record_opened_view graph scope cap
          (#node imported))
        (* Retain actual NEW output backing paths before the recording
           policy and afterward. These guarded graph operations are charged
           to the same remaining Work; private map/path costs remain open. *)
        fun retain child =
          let val _ = live () val _ = W.spend work 1
              val node = invoke (fn () =>
                G.closure_child_node graph scope child)
              val _ = paths := child:: !paths
          in case invoke (fn () => G.view graph node) of
               G.Application _ =>
                 let val (f,x) = invoke (fn () =>
                       G.closure_application_children graph scope child)
                 in retain f;retain x end
             | G.AdmittedBinder _ =>
                 let val closure = invoke (fn () =>
                       G.closure_child_binder graph scope child)
                 in retain (invoke (fn () =>
                   G.binder_closure_body graph scope closure)) end
             | G.OpaqueRetained => raise ERR "execute"
                 "quoted output lost its complete opened syntax"
             | _ => ()
          end
        val _ = retain (invoke (fn () =>
          G.closure_root graph scope (#node opened)))
        val fact = invoke (fn () => P.record_closed_from_import graph scope
          {node= #node opened,theorem=theorem,template_limit=cap,
           check_type=fn ty => invoke (fn () => check_type ty)})
    in Result {owner=owner,frame=frame,instance=instance,
      retained= !paths,fact=fact} end))
  fun fact_for expected (Result {owner=owner as Owner
      {work,graph,...},frame,instance,retained,fact}) =
    ((if Portable.pointer_eq (expected,work) then () else
        raise ERR "fact_for" "foreign expected Work";
      active owner;
      let val scope = #scope (F.description_for expected frame)
      in ignore (M.instance_fact_for expected instance);
         List.app (fn child => ignore
           (G.closure_child_node graph scope child)) retained;
         P.validate_closed_fact graph scope
           (#template_limit (W.semantic_limits expected)) fact;fact end)
     handle primary => (W.close expected;raise primary))
  fun aligned_conversion (owner as Owner
      {work,graph,check_type,...}) frame source right retained
      evidence theorem_of = protect owner (fn () => W.with_step work (fn () =>
      let val where_ = F.description_for work frame val scope = #scope where_
          val _ = evidence ()
          val cap = #template_limit (W.semantic_limits work)
          val output = #output_limit (W.semantic_limits work)
          val ceiling = IntInf.fromInt (W.work_limit work)
          val types = ref ([] : Type.hol_type list)
          val amount = ref (0:IntInf.int)
          val paths = ref retained
          fun live () =
            (active owner;ignore (F.description_for work frame);
             evidence ();
             List.app (fn child => ignore
               (G.closure_child_node graph scope child)) (!paths))
          fun inspect action =
            (live ();let val answer = action () in live ();answer end)
          fun step () = (live ();W.spend work 1;live ())
          fun weight ty =
            (step ();if Type.is_vartype ty then
               (W.spend work (String.size (Type.dest_vartype ty));1)
             else let val {Thy,Tyop,Args} = Type.dest_thy_type ty
                      val _ = W.spend work (String.size Thy+String.size Tyop)
                  in List.foldl (fn (t,n) => n+weight t)
                    (1:IntInf.int) Args end)
          (* Genuine admitted graph profiles bound the raw ALPHA-corresponding
             terms BEFORE any original destructor/reconstruction. *)
          val _ = List.app (fn n => List.app (fn metric =>
            case G.unfolded_nodes graph metric output n of SOME count =>
              if count<=output then () else
                raise ERR "conversion_for" "local endpoint exceeds output"
            | NONE => raise ERR "conversion_for" "missing endpoint profile")
            [G.RawNodes,G.BinderInclusiveNodes]) [source,right]
          fun measure term =
            let val _ = step () val ty = inspect (fn () => Term.type_of term)
                val annotation = weight ty val _ = types := ty:: !types
            in if Term.is_comb term then
                 let val (f,x) = inspect (fn () => Term.dest_comb term)
                 in add {raw=1,inc=1,ann=annotation}
                   (add (measure f) (measure x)) end
               else if Term.is_abs term then
                 let val (v,b) = inspect (fn () => Term.dest_abs term)
                     val bt = inspect (fn () => Term.type_of v)
                     val bw = weight bt val _ = types := bt:: !types
                 in add {raw=1,inc=2,ann=annotation+bw} (measure b) end
               else {raw=1,inc=1,ann=annotation}
            end
          val theorem = inspect theorem_of
          val (old_left,old_right) = inspect (fn () =>
            boolSyntax.dest_eq (Thm.concl theorem))
          val source_term = inspect (fn () => G.representative graph source)
          val right_term = inspect (fn () => G.representative graph right)
          val actual_eq = measure (inspect (fn () => Thm.concl theorem))
          val l = measure source_term val a = measure old_left
          val b = measure old_right val r = measure right_term
          val t = inspect (fn () => Term.type_of source_term)
          val tw = weight t
          val header : profile = {raw=3,inc=3,ann=6+3*tw}
          fun eq p q = add header (add p q)
          fun quote (p:profile) =
            if #raw p <= IntInf.fromInt output andalso
                #inc p <= IntInf.fromInt output andalso #ann p <= ceiling
              then amount := !amount + #raw p + #inc p + #ann p
            else raise ERR "conversion_for" "local ALPHA portfolio exceeds quota"
          val _ = List.app quote [actual_eq,eq l a,eq b r,eq l b,eq l r,
            eq l l,eq r r] (* two ALPHA, two TRANS, two genuine identities *)
          val _ = if #raw (eq l r) <= IntInf.fromInt cap andalso
              #inc (eq l r) <= IntInf.fromInt cap then () else
            raise ERR "conversion_for" "closed conversion exceeds template"
          val _ = if !amount <= ceiling then
              W.spend work (IntInf.toInt (!amount)) else
            raise ERR "conversion_for" "ALPHA portfolio exceeds original Work"
          (* Header annotation types already exist on the admitted actual
             equality. Queue them for EVERY prospective equality occurrence. *)
          val (eq_partial,_) = inspect (fn () =>
            Term.dest_comb (Thm.concl theorem))
          val (eq_head,_) = inspect (fn () => Term.dest_comb eq_partial)
          val header_types = List.map (fn term => inspect
            (fn () => Term.type_of term))
            [Thm.concl theorem,eq_partial,eq_head]
          val _ = List.app (fn _ => types := header_types @ !types)
            [1,2,3,4,5,6]
          val _ = List.app (fn ty => inspect (fn () => check_type ty))
            (List.rev (!types))
          val source_child = inspect (fn () => G.closure_root graph scope source)
          val right_child = inspect (fn () => G.closure_root graph scope right)
          val _ = paths := source_child::right_child:: !paths
          val source_plan = inspect (fn () => G.plan_identity_closure_view
            graph scope cap {target=source_child,retain=[right_child]})
          val right_plan = inspect (fn () => G.plan_identity_closure_view
            graph scope cap {target=right_child,retain=[source_child]})
          val source_view = inspect (fn () =>
            G.execute_identity_closure_view source_plan)
          val right_view = inspect (fn () =>
            G.execute_identity_closure_view right_plan)
          val first = inspect (fn () => Thm.ALPHA source_term old_left)
          val last = inspect (fn () => Thm.ALPHA old_right right_term)
          val middle = inspect (fn () => Thm.TRANS first theorem)
          val aligned = inspect (fn () => Thm.TRANS middle last)
          val conversion = inspect (fn () => P.record_typed_conversion
            graph scope {source=source,source_view=source_view,
              target=right,target_view=right_view,theorem=aligned,
              template_limit=cap,check_type=fn ty =>
                inspect (fn () => check_type ty)})
      in conversion end))

  fun conversion_for expected (value as Result
      {owner=owner as Owner {work,graph,...},frame,instance,
       retained,...}) =
    let val fact = fact_for expected value
        val scope = #scope (F.description_for expected frame)
        val data = M.instance_target_for expected instance
        val _ = if #traversal data=scope then () else
          raise ERR "conversion_for" "instance has a different body frame"
        val equality_node = P.closed_node fact
        val right = case G.view graph equality_node of
            G.Application (partial,right) =>
              (case G.view graph partial of G.Application (head,left) =>
                (case G.view graph head of G.Constant id =>
                  if KernelSig.id_compare
                    (id,#Name (Term.dest_thy_constid boolSyntax.equality))=EQUAL
                  then right else raise ERR "conversion_for" "not equality"
                | _ => raise ERR "conversion_for" "not equality")
              | _ => raise ERR "conversion_for" "not equality")
          | _ => raise ERR "conversion_for" "not equality"
        fun evidence () = ignore (fact_for expected value)
    in aligned_conversion owner frame (#node data) right retained evidence
      (fn () => P.closed_original fact) end
    handle primary => (W.close expected;raise primary)
  fun lambda_conversion_for expected
      (owner as Owner {work,graph,sources,root,...}) {frame,result} =
    ((if Portable.pointer_eq (expected,work) then () else
        raise ERR "lambda_conversion_for" "foreign expected Work";
      let val data = Lambda.conversion_description_for expected result
          val scope = #scope (F.description_for expected frame)
          fun evidence () =
            let val current = Lambda.conversion_description_for expected result
            in if Portable.pointer_eq (#graph current,graph) andalso
                Portable.pointer_eq (#sources current,sources) andalso
                #root current=root andalso #scope current=scope andalso
                #source current= #source data andalso
                #target current= #target data then () else
              raise ERR "lambda_conversion_for" "foreign lambda proof frame"
            end
          val _ = evidence ()
      in aligned_conversion owner frame (#source data) (#target data) []
        evidence (fn () => Lambda.theorem_for expected result) end)
     handle primary => (W.close expected;raise primary))

  (* The policy route uses genuine closed Core results as conditions and
     performs the fixed discharge on compact names. Borrowed residues are
     never re-admitted by an invented finite whole-term ceiling. *)
  structure ConditionalPolicy =
  struct
    structure RP=SmtReplayResourcePolicy
    structure NC=SmtReplayNativeContract
    datatype owner=Owner of
      {work:W.portfolio,graph:G.graph,root:G.scope,sources:S.sources,
       catalogue:K.policy_catalogue,native_contract:NC.contract,
       profiles:G.policy_opaque_profile list,
       check_type:Type.hol_type->unit,symbols:int,epoch:int,dead:bool ref}
    datatype condition=Condition of
      {proof:Core.policy_result,conversion:P.closed_conversion,
       wanted:G.node,truth:G.node}
    datatype plan=Plan of
      {owner:owner,frame:F.receipt,scope:G.scope,instance:M.policy_instance,
       seed:P.closed_fact,conditions:condition list,final:G.node,
       freeze:P.policy_native_freeze_plan,used:bool ref}
    datatype result=Result of
      {owner:owner,frame:F.receipt,scope:G.scope,instance:M.policy_instance,
       conditions:condition list,receipt:P.policy_source_realization}
    fun retire(Owner{work,dead,...})=(dead:=true;W.close work)
    fun protect owner action=action() handle primary=>
      (retire owner;raise primary)
    fun active(owner as Owner
        {work,graph,root,sources,catalogue,native_contract,symbols,epoch,
         dead,...})=protect owner (fn()=>
      (if !dead then raise ERR "conditional_policy" "owner retired" else ();
       NC.validate_for work native_contract;
       W.validate_policy work graph root sources (W.semantic_policy work);
       if Term.term_epoch()=symbols andalso Type.type_epoch()=epoch then ()
       else raise ERR "conditional_policy" "native epoch changed";
       K.validate_with_policy_for work catalogue))
    fun begin work catalogue {profiles,check_type}=W.with_step work (fn()=>
      let val _=K.validate_with_policy_for work catalogue
          val native_contract=K.native_contract_for work catalogue
          val _=NC.validate_for work native_contract
          val sources=W.original_sources work
          val graph=S.owning_graph sources
          val root=S.owning_scope sources
          val value=Owner{work=work,graph=graph,root=root,sources=sources,
            catalogue=catalogue,native_contract=native_contract,
            profiles=profiles,check_type=check_type,
            symbols=Term.term_epoch(),epoch=Type.type_epoch(),dead=ref false}
          val _=active value
      in value end) handle primary=>(W.close work;raise primary)
    fun same_contract(owner as Owner{work,native_contract,...}) held=
      (active owner;
       if Portable.pointer_eq(native_contract,held) then () else
         raise ERR "conditional_policy" "different native caller contract")
    fun frame_data(owner as Owner{work,graph,root,sources,...}) frame=
      let val _=active owner
          val data=F.description_with_policy_for work frame
          val _=if Portable.pointer_eq(graph,#graph data) andalso
              root= #root data andalso
              Portable.pointer_eq(sources,#sources data) then () else
            raise ERR "conditional_policy" "different authentic frame owner"
      in data end
    fun view(owner as Owner{work,graph,...}) node=
      (active owner;W.spend_policy work 1;G.view graph node)
    fun binary owner thy name node=
      case view owner node of G.Application(partial,right)=>
        (case view owner partial of G.Application(head,left)=>
          (case view owner head of G.Constant id=>
            let val actual=KernelSig.name_of_id id
            in if #Thy actual=thy andalso #Name actual=name
                 then SOME(left,right) else NONE end
           | _=>NONE)
         | _=>NONE)
      | _=>NONE
    fun truth owner node=case view owner node of G.Constant id=>
        KernelSig.id_compare(id,
          #Name(Term.dest_thy_constid boolSyntax.T))=EQUAL
      | _=>false
    (* These are actual owner-bearing results, never theorem/node tuples.
       The result's original NC is compared before using its receipt. *)
    fun condition_data(owner as Owner
        {work,graph,root,sources,...}) scope proof=
      let val _=active owner
          val contract=Core.native_contract_with_policy_for work proof
          val _=same_contract owner contract
          val header=Core.conversion_description_with_policy_for work proof
          val _=if Portable.pointer_eq(graph,#graph header) andalso
              root= #root header andalso scope= #scope header andalso
              Portable.pointer_eq(sources,#sources header) then () else
            raise ERR "conditional_policy" "different condition owner/frame"
          val receipt=Core.realization_with_policy_for work proof
          val actual=P.policy_source_realization_data_for work receipt
          val _=if #source actual= #source header andalso
              #target actual= #target header andalso scope= #scope actual
              andalso Portable.pointer_eq(graph,#graph actual)
              andalso Portable.pointer_eq(sources,#sources actual)
              andalso root= #root actual
              andalso Portable.pointer_eq(contract,#native_contract actual)
              then ()
            else raise ERR "conditional_policy"
              "condition receipt changed its actual endpoints"
          val conversion=
            P.conversion_from_policy_source_realization_for work receipt
      in (header,conversion) end
    fun live(owner as Owner{work,graph,...}) frame scope instance conditions=
      let val _=active owner
          val actual=frame_data owner frame
          val _=if #scope actual=scope then () else
            raise ERR "conditional_policy" "original Scope changed"
          val _=same_contract owner
            (M.instance_native_contract_for work instance)
          val target=M.instance_target_with_policy_for work instance
          val _=if #traversal target=scope then () else
            raise ERR "conditional_policy" "instance has another body frame"
          val _=ignore(M.instance_fact_with_policy_for work instance)
          fun check(Condition{proof,conversion,wanted,truth,...})=
            let val(header,_)=condition_data owner scope proof
                val _=P.validate_conversion_for work conversion
            in if #source header=wanted andalso #target header=truth
                andalso G.scope_visible graph scope
                  (G.node_scope graph wanted) then () else
              raise ERR "conditional_policy" "condition endpoint changed" end
      in List.app check conditions end
    fun prepare(owner as Owner
        {work,graph,native_contract,profiles,check_type,...})
        {frame,instance,conditions,ordinal}=protect owner (fn()=>
      W.with_step work (fn()=>
      let val data=frame_data owner frame val scope= #scope data
          val _=if ordinal>=0 then () else
            raise ERR "conditional_policy" "negative caller ordinal"
          val _=same_contract owner
            (M.instance_native_contract_for work instance)
          val target=M.instance_target_with_policy_for work instance
          val _=if #traversal target=scope then () else
            raise ERR "conditional_policy" "instance has another body frame"
          val seed=M.instance_fact_with_policy_for work instance
          val start=P.closed_node seed
          fun arrange current []=(current,[],[current])
            | arrange current(proof::rest)=
                let val(wanted,next)=case binary owner "min" "==>" current of
                      SOME pair=>pair | NONE=>
                        raise ERR "conditional_policy" "extra conditions"
                    val(header,conversion)=condition_data owner scope proof
                    val _=if #source header=wanted andalso
                        truth owner (#target header) then () else
                      raise ERR "conditional_policy"
                        "condition is not this actual antecedent to T"
                    val(final,more,roots)=arrange next rest
                    val condition=Condition{proof=proof,conversion=conversion,
                      wanted=wanted,truth= #target header}
                in (final,condition::more,
                    current:: #target header::roots) end
          val(final,held,roots)=arrange start conditions
          val _=if Option.isSome(binary owner "min" "==>" final) then
              raise ERR "conditional_policy" "missing conditions" else ()
          (* Numeric canonical clauses end in an actual equality. This is
             checked from the genuine instance, not a caller terminal tag. *)
          val _=case binary owner "min" "=" final of SOME(left,_)=>
                if left= #node target then () else
                  raise ERR "conditional_policy"
                    "instance equality has a different canonical source"
            | NONE=>raise ERR "conditional_policy"
                "canonical instance did not finish as equality"
          val conversions=List.map
            (fn Condition{conversion,...}=>conversion) held
          val _=live owner frame scope instance held
          val frontier=P.prepare_realization_frontier_with_policy work
            {frame=frame,roots=roots,closed_facts=[seed],
             conversions=conversions}
          val tables=P.prepare_owned_realization_tables_with_policy
            work frontier
          val freeze=P.prepare_native_realization_freeze_with_policy work
            {tables=tables,contract=native_contract,profiles=profiles,
             ordinal=ordinal,check_type=fn ty=>
               (live owner frame scope instance held;check_type ty;
                live owner frame scope instance held)}
          val _=live owner frame scope instance held
      in Plan{owner=owner,frame=frame,scope=scope,instance=instance,seed=seed,
        conditions=held,final=final,freeze=freeze,used=ref false} end))
    fun execute(Plan{owner=owner as Owner{work,...},frame,scope,instance,
        seed,conditions,final,freeze,used})=protect owner (fn()=>
      W.with_step work (fn()=>
      let val _=live owner frame scope instance conditions
          val _=if !used then raise ERR "conditional_policy" "plan consumed"
            else used:=true
          val block=P.freeze_owned_realization_tables_with_policy work freeze
          fun guard()=live owner frame scope instance conditions
          fun primitive opcode operands=
            (guard();P.execute_primitive_with_policy work
              (P.prepare_primitive_with_policy work block opcode operands))
          fun boolean opcode operands=
            (guard();P.execute_boolean_primitive_with_policy work
              (P.prepare_boolean_primitive_with_policy work block
                opcode operands))
          fun named_truth node=
            let val original=P.execute_closed_named_inst_with_policy work
                  (P.prepare_closed_named_inst_with_policy work block
                    {substitution=[],theorem=boolTheory.TRUTH})
                val definition=P.definition block node
            in primitive P.EqualityMP
              [primitive P.Symmetry [definition],original] end
          fun discharge(Condition{conversion,truth,...},(current,edge))=
            let val(_,next)=case binary owner "min" "==>" current of
                      SOME pair=>pair | NONE=>raise ERR "conditional_policy"
                        "retained implication spine changed"
                val equality=P.conversion block conversion
                val condition=primitive P.EqualityMP
                  [primitive P.Symmetry [equality],named_truth truth]
                val implication=primitive P.EqualityMP
                  [P.constructor_with_policy work block current,edge]
                val result=boolean P.PolicyImplicationMP
                  [implication,condition]
            in (next,result) end
          val(actual,edge)=List.foldl discharge
            (P.closed_node seed,P.closed block seed) conditions
          val _=if actual=final then () else
            raise ERR "conditional_policy" "actual MP tail changed"
          val receipt=P.execute_realization_with_policy work
            (P.prepare_realization_with_policy work block final edge)
          val actual=P.policy_source_realization_data_for work receipt
          val target=M.instance_target_with_policy_for work instance
          val _=if #source actual= #node target then () else
            raise ERR "conditional_policy" "realized instance source changed"
          val _=guard()
      in Result{owner=owner,frame=frame,scope=scope,instance=instance,
        conditions=conditions,receipt=receipt} end))
    fun conversion_for expected
        (Result{owner=owner as Owner{work,...},frame,scope,instance,
          conditions,receipt})=
      ((if Portable.pointer_eq(expected,work) then () else
          raise ERR "conditional_policy" "foreign expected Work";
        protect owner (fn()=>
          (live owner frame scope instance conditions;
           P.conversion_from_policy_source_realization_for expected receipt)))
       handle primary=>(W.close expected;raise primary))
  end
  type policy_owner=ConditionalPolicy.owner
  type policy_plan=ConditionalPolicy.plan
  type policy_result=ConditionalPolicy.result
  val begin_with_policy=ConditionalPolicy.begin
  val prepare_owned_with_policy=ConditionalPolicy.prepare
  val execute_with_policy=ConditionalPolicy.execute
  val conversion_with_policy_for=ConditionalPolicy.conversion_for

  (* Implementation anchors, not calls. Alias RHSs alone are insufficient
     implementation dependencies for Holmake's source scanner. *)
  val _=SmtReplayOwnedRealizedLambda.theorem_with_policy_for
  val _=SmtReplayProof.record_typed_conversion_with_policy_scoped_profiles
  val _=SmtReplayGraph.plan_scoped_identity_closure_view_with_policy
  val _=SmtReplayNativeContract.for_work
  structure ConditionalLambdaPolicy =
  struct
    structure RP=SmtReplayResourcePolicy
    structure NC=SmtReplayNativeContract
    fun convert expected
        (owner as ConditionalPolicy.Owner
          {work,graph,root,sources,native_contract,profiles,check_type,...})
        {frame,result}=
      ((if Portable.pointer_eq(expected,work)then ()else
          raise ERR "policy_lambda_conversion" "foreign expected Work";
        NC.validate_for expected native_contract;
        if Portable.pointer_eq
            (Lambda.native_contract_with_policy_for expected result,
             native_contract)then ()else
          raise ERR "policy_lambda_conversion" "different native owner";
        W.with_step expected(fn()=>
        let
          val location=ConditionalPolicy.frame_data owner frame
          val scope= #scope location
          val original=Lambda.conversion_description_with_policy_for
            expected result
          fun evidence()=
            let val _=ConditionalPolicy.active owner
                val _=ignore(ConditionalPolicy.frame_data owner frame)
                val current=Lambda.conversion_description_with_policy_for
                  expected result
                val contract=Lambda.native_contract_with_policy_for
                  expected result
            in if Portable.pointer_eq(graph,#graph current)andalso
                root= #root current andalso scope= #scope current andalso
                Portable.pointer_eq(sources,#sources current)andalso
                #source current= #source original andalso
                #target current= #target original andalso
                Portable.pointer_eq(contract,native_contract)then ()else
              raise ERR "policy_lambda_conversion"
                "different authentic Lambda frame or endpoints"end
          val _=evidence()
          val native=NC.for_work expected native_contract
          val finite= #semantic_limits native
          val maximum= #template_limit(W.semantic_policy expected)
          val ceiling=IntInf.fromInt(#type_work_limit native)
          val used=ref(0:IntInf.int)
          fun debit amount=
            (evidence();if amount>=0 andalso amount<=ceiling- !used then
               (used:= !used+amount;W.spend_policy expected amount)
             else raise ERR "policy_lambda_conversion"
               "native identity planning allowance exhausted";
             evidence())
          fun tick()=debit 1
          fun inspect operation=
            (tick();let val answer=operation()val _=evidence()
                   in answer end)
          fun capture node=
            inspect(fn()=>G.prepare_scoped_profiled_metric graph scope
              {node=node,profiles=profiles})
          val source= #source original val target= #target original
          val left_capture=capture source
          val right_capture=if source=target then left_capture
            else capture target
          fun geometry node capture=
            let val d=inspect(fn()=>
                  G.profiled_metric_data graph scope capture)
                val output=IntInf.fromInt(#output_limit finite)
            in if #node d=node andalso #raw d<=output andalso
                #inc d<=output then d else
              raise ERR "policy_lambda_conversion"
                "actual identity operand exceeds native output"end
          val left=geometry source left_capture
          val right=geometry target right_capture
          fun captures_live()=
            (ignore(geometry source left_capture);
             ignore(geometry target right_capture))
          val theorem=inspect(fn()=>Lambda.theorem_with_policy_for
            expected result)
          val _=if inspect(fn()=>HOLset.numItems(Thm.hypset theorem))=0
            then ()else raise ERR "policy_lambda_conversion"
              "actual Lambda theorem has surviving hypotheses"
          val(l,r)=inspect(fn()=>boolSyntax.dest_eq(Thm.concl theorem))
          val _=if Portable.pointer_eq(l,
                inspect(fn()=>G.representative graph source))andalso
              Portable.pointer_eq(r,
                inspect(fn()=>G.representative graph target))andalso
              inspect(fn()=>G.type_id graph source)=
                inspect(fn()=>G.type_id graph target)then ()else
            raise ERR "policy_lambda_conversion"
              "noncanonical actual Lambda endpoints"
          val type_memo=ref([]:(Type.hol_type*IntInf.int)list)
          fun weight ty=
            let fun seek []=NONE
                  | seek((held,n)::rest)=
                      (tick();if Portable.pointer_eq(held,ty)then SOME n
                       else seek rest)
            in case seek(!type_memo)of SOME n=>n | NONE=>
              let val _=tick()
                  val n=if inspect(fn()=>Type.is_vartype ty)then
                    (debit(IntInf.fromInt(String.size
                       (inspect(fn()=>Type.dest_vartype ty))));1:IntInf.int)
                    else let val{Thy,Tyop,Args}=inspect
                               (fn()=>Type.dest_thy_type ty)
                         in debit(IntInf.fromInt(String.size Thy)+
                              IntInf.fromInt(String.size Tyop));
                            List.foldl(fn(t,n)=>n+weight t)1 Args end
                  val _=if n<=ceiling then ()else
                    raise ERR "policy_lambda_conversion"
                      "native Type incidence exceeds caller"
                  val _=type_memo:=(ty,n):: !type_memo
              in n end
            end
          val native_types=ref([]:Type.hol_type list)
          fun measure term:profile=
            let val ty=inspect(fn()=>Term.type_of term)
                val own=weight ty
                val _=native_types:=ty:: !native_types
            in case inspect(fn()=>Term.dest_term term)of
                Term.COMB(f,x)=>
                  let val a=measure f val b=measure x
                  in {raw=1+ #raw a+ #raw b,inc=1+ #inc a+ #inc b,
                    ann=own+ #ann a+ #ann b}:profile end
              | Term.LAMB(v,b)=>
                  let val bt=inspect(fn()=>Term.type_of v)
                      val binder=weight bt
                      val _=native_types:=bt:: !native_types
                      val a=measure b
                  in {raw=1+ #raw a,inc=2+ #inc a,
                    ann=own+binder+ #ann a}:profile end
              | _=>{raw=1,inc=1,ann=own}:profile
            end
          (* Only this actual binder-sensitive native route is measured.
             It does not impose a whole-source cap on a Core cut getter. *)
          val a=measure l
          val left_types=List.rev(!native_types)
          val _=native_types:=[]
          val b=measure r
          val right_types=List.rev(!native_types)
          val _=if #raw a= #raw left andalso #inc a= #inc left andalso
              #raw b= #raw right andalso #inc b= #inc right then ()else
            raise ERR "policy_lambda_conversion" "actual geometry changed"
          val equation=inspect(fn()=>Thm.concl theorem)
          val(partial,_)=inspect(fn()=>Term.dest_comb equation)
          val(head,_)=inspect(fn()=>Term.dest_comb partial)
          val header_types=List.map(fn t=>inspect(fn()=>Term.type_of t))
            [equation,partial,head]
          val header=List.foldl(fn(ty,n)=>n+weight ty)0 header_types
          fun reflexive(value:profile):profile=
            {raw=3+2* #raw value,inc=3+2* #inc value,
             ann=header+2* #ann value}
          val lhs=reflexive a val rhs=reflexive b
          fun quote(value:profile)=
            if #raw value<=IntInf.fromInt(#output_limit finite)andalso
                #inc value<=IntInf.fromInt(#output_limit finite)andalso
                #raw value<=IntInf.fromInt(#template_limit finite)andalso
                #inc value<=IntInf.fromInt(#template_limit finite)andalso
                #ann value<=ceiling then
              #raw value+ #inc value+ #ann value else
              raise ERR "policy_lambda_conversion"
                "future native REFL exceeds actual caller envelope"
          val recorder_types=List.map(fn node=>inspect
              (fn()=>G.type_of graph node))
            (inspect(fn()=>G.reachable graph[source,target]))@
            #types left@(if source=target then []else #types right)
          val recorder_amount=List.foldl(fn(ty,n)=>n+weight ty)0
            recorder_types
          val _=debit(quote lhs+quote rhs+recorder_amount)
          val _=if RP.allows maximum(3+ #raw a+ #raw b)andalso
              RP.allows maximum(3+ #inc a+ #inc b)then ()else
            raise ERR "policy_lambda_conversion" "metadata template cap"
          (* All prospective native/recorder Type roots are admitted before
             the first external policy. The recorder repeats its own real
             callbacks later; no earlier call grants future permission. *)
          val callbacks=header_types@left_types@left_types@
            header_types@right_types@right_types
          val _=List.app(fn ty=>
            (evidence();captures_live();check_type ty;
             evidence();captures_live()))callbacks
          val left_child=inspect(fn()=>G.closure_root graph scope source)
          val right_child=inspect(fn()=>G.closure_root graph scope target)
          fun plan child other=inspect(fn()=>
            G.plan_scoped_identity_closure_view_with_policy graph scope
              maximum {target=child,retain=[other],profiles=profiles})
          val first=plan left_child right_child
          val second=plan right_child left_child
          val source_view=inspect(fn()=>G.execute_identity_closure_view first)
          val target_view=inspect(fn()=>G.execute_identity_closure_view second)
          val converted=inspect(fn()=>
            P.record_typed_conversion_with_policy_scoped_profiles graph scope
              {source=source,source_view=source_view,target=target,
               target_view=target_view,theorem=theorem,template_limit=maximum,
               profiles=profiles,check_type=fn ty=>
                 (evidence();captures_live();check_type ty;
                  evidence();captures_live())})
          val _=evidence()
        in converted end))
       handle primary=>(W.close expected;raise primary))
  end
  val lambda_conversion_with_policy_for=ConditionalLambdaPolicy.convert

end
