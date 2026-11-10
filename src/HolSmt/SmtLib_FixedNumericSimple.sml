(* Fixed numeric PURE context: no Source or antecedent assumptions. *)
structure SmtLib_FixedNumericSimple :> SmtLib_FixedNumericSimple =
struct
  structure G = SmtReplayGraph
  structure S = SmtReplaySource
  structure W = SmtReplayInvocationWork
  structure P = SmtReplayProof
  structure A = SmtReplayFocusAdmission
  structure F = SmtReplayOwnedScopeReceipt
  structure K = SmtLib_GraphNumericCanonical
  structure M = SmtLib_GraphNumericRuleMatch
  structure Conditional = SmtLib_GraphNumericConditional
  structure T = SmtLib_CompactCarrierScheduler
  structure C = SmtReplayCanonGraph
  structure D = SmtReplayOwnedTransport
  structure Core = SmtReplayOwnedLargeProofCore
  structure Lambda = SmtReplayOwnedRealizedLambda
  val _ = SmtLib_GraphNumericRuleMatch.begin_canonical
  val _ = SmtLib_GraphNumericConditional.conversion_for
  val _ = SmtReplayFocusAdmission.initial_condition
  val _ = SmtLib_CompactCarrierScheduler.aux_target_for
  val _ = SmtLib_CompactCarrierScheduler.revalidate_for
  val _ = SmtLib_CompactCarrierScheduler.normalization_ordinal
  val _ = SmtReplayGraph.discover_compact_selected_partial
  val _ = SmtReplayGraph.record_opened_type_projection
  val ERR = Feedback.mk_HOL_ERR "SmtLib_FixedNumericSimple"
  datatype owner = Owner of
    {work:W.portfolio,graph:G.graph,root:G.scope,sources:S.sources,
     catalogue:K.catalogue,traversal:T.owner,matcher:M.owner,
     net:(M.schema * bool) Ho_Net.net,heads:(string * string) list,
     discovery_heads:G.discovery_heads,
     conditional:Conditional.owner,
     check_type:Type.hol_type -> unit,symbols:int,stack_limit:int,
     running:bool ref,
     dead:bool ref,backing:(unit -> unit) list ref,
     frames:F.receipt list ref,
     validated:(IntInf.int * (unit -> unit) list) option ref,
     fence:IntInf.int ref}
  type description = {node:G.node,child:G.closure_child,scope:G.scope,
    frame:F.receipt,admission:A.focus,source_limit:int,category:A.category}
  datatype focus = Focus of
    {admission:A.focus,frame:F.receipt,scope:G.scope,
     described:(IntInf.int * IntInf.int * description) option ref,
     backing_guard:unit -> unit}
  datatype plan = Plan of {owner:owner,source:focus,used:bool ref}
  datatype result = Result of {owner:owner,source:focus,proof:Core.result}
  type outcome = {target:focus,recipe:C.graph_conversion,proof:Core.result}
  type memo_entry = {node:G.node,scope:G.scope,category:A.category,limit:int,
    stack:(G.node * G.scope) list,result:outcome option}
  exception Inapplicable
  fun close (Owner {work,dead,...}) = (dead := true;W.close work)
  fun protect owner action = action () handle primary =>
    (close owner;raise primary)
  fun guard_app work action rows = case rows of
      [] => W.spend_guard_policy work 1
    | row::rest =>
        (W.spend_guard_policy work 1;action row;guard_app work action rest)
  fun active (Owner {work,graph,root,sources,catalogue,traversal,
                    symbols,stack_limit,dead,backing,discovery_heads,
                    validated,frames,...}) =
    let
      val _ = if !dead then raise ERR "active" "numeric owner retired" else ()
      val _ = W.validate work graph root sources (W.semantic_limits work)
      val _ = if Term.term_epoch () = symbols then () else
        raise ERR "active" "constant retirement epoch changed"
      val _ = if !Cond_rewr.stack_limit=stack_limit then () else
        raise ERR "active" "fixed conditional stack policy changed"
      (* A lexical zero-binder frame may retire without any G mutation.
         Its authentic private lifetime is checked on EVERY cache hit. *)
      val _ = guard_app work (F.validate_lifetime_for work) (!frames)
      val revision = G.validation_revision graph root
      val rows = !backing
      val hit = case !validated of SOME (old,held) =>
          old=revision andalso Portable.pointer_eq (held,rows)
        | NONE => false
    in if hit then () else
      (T.revalidate_for work traversal;K.validate_for work catalogue;
       G.validate_discovery_heads graph root discovery_heads;
       guard_app work (fn guard => guard ()) rows;
       W.validate work graph root sources (W.semantic_limits work);
       if Term.term_epoch () = symbols andalso
           !Cond_rewr.stack_limit=stack_limit andalso
           G.validation_revision graph root=revision andalso
           Portable.pointer_eq (rows,!backing) then
         validated := SOME (revision,rows) else
         raise ERR "active" "validation state changed during backing pass")
    end
  fun revalidate (owner as Owner {validated,fence,...}) =
    (fence := !fence+1;validated := NONE;active owner)
  fun expected (Owner {graph,sources,work,...}) scope =
    {graph=graph,scope=scope,sources=sources,work=work}
  fun describe (owner as Owner {work,graph,root,fence,...})
      (Focus {admission,frame,scope,described,...}) : description =
    let val _ = active owner val _ = G.validate_scope graph scope
        val revision=G.validation_revision graph root val generation= !fence
        fun full () =
          let val data = F.description_for work frame
              val _ = if Portable.pointer_eq (#graph data,graph) andalso
                  #root data=root andalso #scope data=scope then () else
                raise ERR "describe" "foreign actual frame"
              val lower = A.describe_for (expected owner scope) admission
              val answer = {node= #node lower,child= #child lower,
                scope=scope,frame=frame,admission=admission,
                source_limit= #source_limit lower,category= #category lower}
                : description
              val _ = active owner
              val _ = if G.validation_revision graph root=revision andalso
                  !fence=generation then () else
                raise ERR "describe" "validation state changed"
              val _ = described := SOME (revision,generation,answer)
          in answer end
    in case !described of SOME (old,held,answer) =>
         if old=revision andalso held=generation then answer else full ()
       | NONE => full () end
  fun capture (owner as Owner {work,backing,frames,...}) frame admission =
    let val scope = #scope (F.description_for
          (case owner of Owner {work,...} => work) frame)
        fun present [] = (W.spend_guard_policy work 1;false)
          | present (held::rest) =
              (W.spend_guard_policy work 1;
               Portable.pointer_eq (held,frame) orelse present rest)
        val _ = if present (!frames) then () else
          frames := frame :: !frames
        fun guard () = A.validate_for (expected owner scope) admission
        val focus = Focus {admission=admission,frame=frame,scope=scope,
          described=ref NONE,backing_guard=guard}
        val _ = ignore (describe owner focus)
        val _ = backing := guard :: !backing
    in focus end
  (* A.generated_compact retains and validates its exact parent focus.
     Once that child is registered, its parent's separate owner-list entry
     is redundant, not a new dependency. Prune only that private closure;
     no node equality or cached validation result authorizes this step. *)
  fun covered_parent (Owner {work,backing,...})
      (Focus {backing_guard,...}) =
    let fun retain [] = (W.spend_guard_policy work 1;[])
          | retain (guard::rest) =
              (W.spend_guard_policy work 1;
               if Portable.pointer_eq (guard,backing_guard) then retain rest
               else guard :: retain rest)
    in backing := retain (!backing) end
  fun action (owner as Owner {work,...}) focus operation =
    W.with_step work (fn () =>
      let fun observe () =
            (ignore (describe owner focus);W.spend work 1)
          val answer = operation observe
          val _ = ignore (describe owner focus)
      in answer end)
  fun ordinal (owner as Owner {work,traversal,...}) =
    (active owner;T.validate_for work traversal;
     T.normalization_ordinal traversal)
  fun policy (owner as Owner {check_type,...}) focus ty =
    (* active checks original owner/epochs/stack/private Scope lifetimes on
       every call, and forces backing geometry on a genuine G revision or
       retained-list change. Every policy is still invoked in order. *)
    (active owner;ignore (describe owner focus);check_type ty;
     active owner;ignore (describe owner focus))
  fun identity (owner as Owner {graph,...}) focus =
    let val d = describe owner focus
    in action owner focus (fn observe => C.graph_identity graph (#scope d)
      {observe=observe} (#node d)) end
  fun seal (owner as Owner {work,graph,...}) focus recipe =
    let val d = describe owner focus
        val plan = Core.prepare_in_scope work
          {frame= #frame d,conversion=recipe,ordinal=ordinal owner,
           check_type=policy owner focus}
        val proof = Core.execute work plan
        (* capture retains the generated admission, whose guard owns this
           EXACT Core receipt and its parent. Do not retain a second guard
           for the same proof beside that authentic dependency chain. *)
        val target = capture owner (#frame d)
          (A.generated_compact (expected owner (#scope d))
            (#admission d) proof)
        val _ = covered_parent owner focus
        val closed = action owner focus (fn observe =>
          C.graph_realized_leaf work
            {realization=Core.realization_for work proof,observe=observe})
    in {target=target,recipe=closed,proof=proof} : outcome end
  fun joined (owner as Owner {work,...}) source
      (left:outcome) (right:outcome) =
    let val d = describe owner source
        val recipe = action owner source (fn observe =>
          C.graph_realized_sequence work
            {first= #recipe left,second= #recipe right,observe=observe})
    in seal owner source recipe end
  fun after source NONE = source
    | after _ (SOME (value:outcome)) = #target value
  fun join owner source NONE right = right
    | join _ _ left NONE = left
    | join owner source (SOME left) (SOME right) =
        SOME (joined owner source left right)
  (* Exact public PURE_ss discrimination net: foldr insertion and its
     lookup order, never a reordered head bucket or a caller rule table. *)
  fun candidates (owner as Owner {graph,net,heads,...}) focus =
    let val d = describe owner focus
        fun head observe child =
          let val _ = observe ()
              val n = G.closure_child_node graph (#scope d) child
          in case G.view graph n of G.Application _ =>
                head observe (#1 (G.closure_application_children
                  graph (#scope d) child))
             | G.Constant id =>
                 let val {Thy,Name} = KernelSig.name_of_id id
                 in SOME (Thy,Name) end
             | _ => NONE end
    in action owner focus (fn observe =>
      case head observe (#child d) of NONE => []
      | SOME name => if not (List.exists (fn key => key=name) heads)
          then [] else
        let val _ = List.app (fn metric =>
              case G.unfolded_nodes graph metric (#source_limit d)
                  (#node d) of SOME n => if n<= #source_limit d then () else
                    raise ERR "candidates" "relevant source exceeds its role"
              | NONE => raise ERR "candidates" "missing numeric source syntax")
              [G.RawNodes,G.BinderInclusiveNodes]
            (* Actual lookup is constructor-only, with no callbacks. Debit
               the full admitted source visits before that public net walk.
               Internal balanced-map/kernel costs remain a separate gate. *)
            val _ = case G.unfolded_nodes graph G.RawNodes
                (#source_limit d) (#node d) of SOME n =>
                  (case owner of Owner {work,...} => W.spend work n)
              | NONE => raise ERR "candidates" "missing admitted source"
            val term = G.representative graph (#node d)
            val answer = Ho_Net.lookup term net
            val _ = observe ()
        in answer end)
    end
  fun same owner first second =
    let val Owner {graph,work,...} = owner
        val l = describe owner first val r = describe owner second
    in action owner first (fn observe =>
      if #scope l<> #scope r then
        (* Only condition stack comparison crosses actual frames; every
           condition was fully admitted by its opaque numeric instance. *)
        (observe ();List.app (fn (data:description) => List.app (fn metric =>
           case G.unfolded_nodes graph metric (#source_limit data) (#node data) of
             SOME n => if n<= #source_limit data then () else
               raise ERR "same" "condition comparison exceeds its output role"
           | NONE => raise ERR "same" "missing complete condition syntax")
           [G.RawNodes,G.BinderInclusiveNodes]) [l,r];
         Term.aconv (G.representative graph (#node l))
           (G.representative graph (#node r)))
      else let val scope = #scope l
               val memo = ref ([] : (G.node * G.node * bool) list)
               val paths = ref ([] : G.closure_child list)
               fun lookup x y [] = NONE
                 | lookup x y ((a,b,v)::rest) =
                     (observe ();if x=a andalso y=b then SOME v
                       else lookup x y rest)
               (* A raw opaque child can already have a genuine retained
                  alpha opening. Compare that annotation, never an invented
                  no-op metric or a newly opened comparison operand. The
                  raw incoming path and exact registered receipt stay live. *)
               fun comparison_child child =
                 let val _ = observe ()
                     val original = G.closure_child_node graph scope child
                     fun known metric = Option.isSome
                       (G.unfolded_nodes graph metric
                         (#output_limit (W.semantic_limits work)) original)
                 in case G.view graph original of G.OpaqueRetained =>
                      if known G.RawNodes andalso
                          known G.BinderInclusiveNodes then child else
                        let val _ = observe ()
                            val source = G.cached_opened_view
                              graph scope original
                            val _ = observe ()
                            val receipt = G.carrier_alpha_for graph scope
                              (W.work_limit work)
                              {original=original,source=source}
                            fun guard () =
                              let val _ = ignore (G.closure_child_node
                                    graph scope child)
                                  val _ = G.validate_opened_view
                                    graph scope original source
                                  val data = G.carrier_alpha_data
                                    graph scope receipt
                              in if #original data=original andalso
                                  #node (#source data)= #node source andalso
                                  Portable.pointer_eq
                                    (#bridge (#source data),#bridge source)
                                  then () else raise ERR "same"
                                    "different retained alpha operand"
                              end
                            val _ = guard ()
                            val _ = (case owner of Owner {backing,...} =>
                              backing := guard :: !backing)
                            val _ = observe ()
                            val data = G.carrier_alpha_data
                              graph scope receipt
                            val annotation = #annotation data
                            val _ = W.spend work (#visits data)
                            val _ = paths := annotation :: !paths
                            val _ = guard ()
                        in annotation end
                    | _ => child
                 end
               fun compare left right =
                 let val _ = observe ()
                     val a = G.closure_child_node graph scope left
                     val b = G.closure_child_node graph scope right
                     val _ = paths := left::right:: !paths
                 in if a=b then true else
                   case lookup a b (!memo) of SOME value => value
                   | NONE =>
                     let val result = if G.type_id graph a<>G.type_id graph b
                           then false else case (G.view graph a,G.view graph b) of
                             (G.Application _,G.Application _) =>
                               let val (f,x) = G.closure_application_children
                                     graph scope left
                                   val (g,y) = G.closure_application_children
                                     graph scope right
                               in compare f g andalso compare x y end
                           | (G.Application _,_) => false
                           | (_,G.Application _) => false
                           | _ => SmtReplayOwnedAlpha.same_inside work
                               {caller=scope,traversal=scope,
                                left=comparison_child left,
                                right=comparison_child right}
                         val _ = observe ()
                         val _ = memo := (a,b,result):: !memo
                     in result end
                 end
               val result = compare (#child l) (#child r)
               val _ = List.app (fn child =>
                 (observe ();ignore (G.closure_child_node graph scope child)))
                 (!paths)
               val _ = ignore (describe owner second)
           in result end)
    end
  (* Cond_rewr's exact AC order, with nominal visits/name/type work
     debited at the actual comparison sites. No policy or proof callback. *)
  fun ac_order owner focus pair = action owner focus (fn observe =>
    let val Owner {work,...} = owner
        fun text value = W.spend work (String.size value)
        fun weight ty =
          (observe ();if Type.is_vartype ty then
             (text (Type.dest_vartype ty);()) else
           let val {Thy,Tyop,Args} = Type.dest_thy_type ty
           in text Thy;text Tyop;List.app weight Args end)
        fun type_order (a,b) = (weight a;weight b;Type.compare (a,b))
        fun size term = (observe ();case Term.dest_term term of
            Term.LAMB (_,body) => 1+size body
          | Term.COMB (f,x) => size f+size x | _ => 1)
        fun env_find env term = case env of [] => NONE
          | (key,value)::rest =>
              (observe ();if Term.aconv key term then SOME value
                else env_find rest term)
        fun dest_head env term = (observe ();case Term.dest_term term of
            Term.VAR (name,ty) =>
              (case env_find env term of NONE => (((name,""),0),ty)
              | SOME n => ((("",""),~n),Type.alpha))
          | Term.CONST {Name,Thy,Ty} => (((Name,Thy),1),Ty)
          | Term.LAMB (v,_) => ((("",""),2),Term.type_of v)
          | Term.COMB _ => raise ERR "ac_order" "unstripped application head")
        fun name_order (a,b) = (observe ();text a;text b;String.compare (a,b))
        fun heads (e1,e2) (a,b) =
          let val (((an,at),ak),ay) = dest_head e1 a
              val (((bn,bt),bk),by) = dest_head e2 b
          in case name_order (an,bn) of EQUAL =>
               (case name_order (at,bt) of EQUAL =>
                  (case Int.compare (ak,bk) of EQUAL => type_order (ay,by)
                    | other => other) | other => other)
             | other => other end
        fun compare n (e1,e2) (a,b) =
          (observe ();case Int.compare (size a,size b) of EQUAL =>
             if Term.is_abs a then
               if Term.is_abs b then
                 let val (av,ab) = Term.dest_abs a
                     val (bv,bb) = Term.dest_abs b
                 in case type_order (Term.type_of av,Term.type_of bv) of
                     EQUAL => compare (n+1) ((av,n)::e1,(bv,n)::e2) (ab,bb)
                   | other => other end else GREATER
             else if Term.is_abs b then LESS else
               let val (ah,aa) = HolKernel.strip_comb a
                   val (bh,ba) = HolKernel.strip_comb b
                   fun args ([],[]) = EQUAL
                     | args ([],_) = LESS | args (_,[]) = GREATER
                     | args (x::xs,y::ys) =
                         (case compare n (e1,e2) (x,y) of EQUAL =>
                           args (xs,ys) | other => other)
               in case heads (e1,e2) (ah,bh) of EQUAL =>
                    (case Int.compare (length aa,length ba) of EQUAL =>
                      args (aa,ba) | other => other) | other => other end
           | other => other)
    in compare 0 ([],[]) pair end)
  (* root, condition and descendant routines are mutually recursive so the
     fixed PURE context never receives an enclosing antecedent or Source. *)
  fun simplify owner memo stack focus =
    let val d = describe owner focus
        val stack_key = action owner focus (fn observe =>
          List.map (fn held =>
            let val _ = observe () val data = describe owner held
            in (#node data,#scope data) end) stack)
        fun stack_equal observe ([],[]) = true
          | stack_equal observe ((a,s)::xs,(b,t)::ys) =
              (observe ();a=b andalso s=t andalso
                stack_equal observe (xs,ys))
          | stack_equal _ _ = false
        val cached = action owner focus (fn observe =>
          let fun find [] = NONE
                | find ((row:memo_entry)::rest) =
                    (observe ();if #node row= #node d andalso
                       #scope row= #scope d andalso #category row= #category d
                       andalso #limit row= #source_limit d andalso
                       stack_equal observe (#stack row,stack_key)
                     then SOME (#result row) else find rest)
          in find (!memo) end)
        fun reuse (old:outcome) =
          let val Owner {work,...} = owner
              val _ = ignore (Core.conversion_description_for work (#proof old))
              (* Preserve THIS occurrence/path even when the semantic node
                 and already-paid closed proof have a genuine DAG alias. *)
              val target = capture owner (#frame d)
                (A.generated_compact (expected owner (#scope d))
                  (#admission d) (#proof old))
              val _ = covered_parent owner focus
          in {target=target,recipe= #recipe old,proof= #proof old}:outcome end
    in case cached of SOME NONE => NONE | SOME (SOME old) => SOME (reuse old)
      | NONE =>
        let val result = fresh owner memo stack focus
            val _ = action owner focus (fn observe =>
              (observe ();memo := {node= #node d,scope= #scope d,
                category= #category d,limit= #source_limit d,stack=stack_key,
                result=result}:: !memo))
        in result end
    end
  and fresh owner memo stack focus =
    let val (middle,roots) = repeat owner memo stack focus
        val children = descend owner memo stack middle
    in case children of NONE => roots | SOME child_result =>
      let val prefix = join owner focus roots (SOME child_result)
          val retry = if same owner middle (#target child_result) then NONE
            else rewrite owner memo stack (#target child_result)
      in case retry of NONE => prefix | SOME changed =>
        join owner focus (join owner focus prefix (SOME changed))
          (simplify owner memo stack (#target changed)) end
    end
  and repeat owner memo stack source =
    let fun loop current accumulated =
          case rewrite owner memo stack current of NONE => (current,accumulated)
          | SOME result => loop (#target result)
              (join owner source accumulated (SOME result))
    in loop source NONE end
  and rewrite (owner as Owner
      {work,matcher,conditional,stack_limit,...}) memo stack focus =
    let val d = describe owner focus
        fun attempt [] = NONE
          | attempt ((schema,isperm)::rest) =
            (case M.prepare matcher
                {schema=schema,caller= #scope d,traversal= #scope d,
                 target= #child d} of M.NoMatch => attempt rest
             | M.NeedsHigherOrder => raise ERR "rewrite"
                 "fixed scalar clause unexpectedly needs higher-order matching"
             | M.Matched matched =>
               let val metadata = M.describe_for work matched
                   val count = length (#conditions metadata)
               in if length stack+count>stack_limit then attempt rest else
                 let val instance = M.instantiate matched
                       {check_type=policy owner focus}
                     val applicable = action owner focus (fn observe =>
                       let val _ = observe ()
                           val seed = M.instance_fact_for work instance
                           val (_,body) = boolSyntax.strip_imp
                             (Thm.concl (P.closed_original seed))
                           val (l,r) = boolSyntax.dest_eq body
                       in not (Term.aconv l r) end)
                     val applicable = applicable andalso (not isperm orelse
                       let val pair = action owner focus (fn observe =>
                             (observe ();boolSyntax.dest_eq (#2
                               (boolSyntax.strip_imp (Thm.concl
                                 (P.closed_original
                                   (M.instance_fact_for work instance)))))))
                       in ac_order owner focus pair=GREATER end)

                 in if not applicable then attempt rest else
                   let val conditions = List.tabulate (count,fn index =>
                         capture owner (#frame d)
                           (A.initial_condition work
                             {instance=instance,index=index}))
                       val looping = List.exists (fn ant =>
                         List.exists (same owner ant) stack) conditions
                   in if looping then attempt rest else
                     let val stack' = conditions @ stack
                         fun prove condition =
                           let val normalized = case simplify owner memo stack'
                                 condition of NONE =>
                                   seal owner condition
                                     (identity owner condition)
                               | SOME result => result
                           in if is_true owner (#target normalized) then
                                #proof normalized else raise Inapplicable end
                         val evidence = List.map prove conditions
                         val prepared = Conditional.prepare_owned conditional
                           {frame= #frame d,instance=instance,
                            conditions=evidence}
                         val result = Conditional.execute prepared
                         val conversion =
                           Conditional.conversion_for work result
                         val leaf = action owner focus (fn observe =>
                           C.graph_leaf
                             (case owner of Owner {graph,...} => graph)
                             (#scope d) {conversion=conversion,
                               template_limit= #template_limit
                                 (W.semantic_limits work),observe=observe})
                     in SOME (seal owner focus leaf) end
                     handle Inapplicable =>
                       (ignore (describe owner focus);attempt rest)
                   end
                 end
               end)
    in attempt (candidates owner focus) end
  and descend (owner as Owner {graph,work,...}) memo stack focus =
    let val d = describe owner focus val scope = #scope d
    in case G.view graph (#node d) of
        G.Application _ =>
          let val (a,b) = A.application_children (expected owner scope)
                (#admission d)
              val left = capture owner (#frame d) a
              val right = capture owner (#frame d) b
              val l = simplify owner memo stack left
              val r = simplify owner memo stack right
          in case (l,r) of (NONE,NONE) => NONE | _ =>
             let val lp = case l of NONE => identity owner left
                   | SOME x => #recipe x
                 val rp = case r of NONE => identity owner right
                   | SOME x => #recipe x
                 val composed = action owner focus (fn observe =>
                   C.graph_application_fused graph scope
                     {source= #node d,left=lp,right=rp,observe=observe})
             in SOME (seal owner focus composed) end
          end
      | G.AdmittedBinder _ =>
          let val frame = F.body work (#frame d) (#child d)
              val body = capture owner frame
                (A.binder_body (expected owner scope) (#admission d))
          in case simplify owner memo stack body of NONE => NONE
            | SOME result => SOME (lift owner focus result) end
      | G.OpaqueRetained => discover owner memo stack focus
      | _ => NONE
    end
  (* Selection is derived from ALL authenticated fixed canonical rows in
     begin, not supplied by a caller. A complete negative scan needs no
     opening. A positive scan retains the exact private alpha recipe. *)
  and discover (owner as Owner {work,graph,discovery_heads,...})
      memo stack focus =
    let val d = describe owner focus val scope = #scope d
        val cap = #template_limit (W.semantic_limits work)
        val output = #output_limit (W.semantic_limits work)
        val ceiling = IntInf.fromInt (W.work_limit work)
        val converted = action owner focus (fn observe =>
          let val receipt = G.discover_compact_selected_partial graph scope
                {original= #node d,heads=discovery_heads,
                 maximum= #source_limit d,scan_limit=W.work_limit work,
                 step=observe}
              fun data () =
                let val value = G.selected_partial_data graph scope
                      discovery_heads receipt
                in if #original value= #node d then value else
                  raise ERR "discover" "selected original changed" end
              val _ = (case owner of Owner {backing,...} =>
                backing := (fn () => ignore (data ())) :: !backing)
          in case #view (data ()) of NONE => NONE
            | SOME view =>
              let val target = #node view
                  val _ = G.validate_opened_view graph scope (#node d) view
                  (* The genuine private alpha recipe preserves every raw,
                     binder-variable and type incidence. Its cached rich
                     profile bounds the old raw term before inspection. *)
                  fun count metric =
                    case G.unfolded_nodes graph metric output target of
                      SOME n => if n<=output then IntInf.fromInt n else
                        raise ERR "discover" "opened target exceeds output"
                    | NONE => raise ERR "discover" "missing opened profile"
                  val raw = count G.RawNodes
                  val inc = count G.BinderInclusiveNodes
                  val _ = if 3+2*raw<=IntInf.fromInt output andalso
                      3+2*inc<=IntInf.fromInt output andalso
                      3+2*raw<=IntInf.fromInt cap andalso
                      3+2*inc<=IntInf.fromInt cap then () else
                    raise ERR "discover" "alpha equality exceeds quota"
                  val types = ref ([] : Type.hol_type list)
                  fun live () =
                    (ignore (describe owner focus);ignore (data ());
                     G.validate_opened_view graph scope (#node d) view)
                  fun inspect operation =
                    (live ();let val value=operation () in live ();value end)
                  fun step () = (live ();W.spend work 1;live ())
                  fun weight ty : IntInf.int =
                    (step ();if Type.is_vartype ty then
                       (W.spend work (String.size (Type.dest_vartype ty));1)
                     else let val {Thy,Tyop,Args}=Type.dest_thy_type ty
                              val _ = W.spend work
                                (String.size Thy+String.size Tyop)
                          in List.foldl (fn (t,n) => n+weight t) 1 Args end)
                  (* Primitive projection provenance belongs to the exact
                     original opaque object, not a fake no-op profile. Its
                     future capture is planned from the genuine rich path.
                     Cached type incidences precede all raw Term getters. *)
                  val rich=inspect
                    (fn () => G.closure_root graph scope target)
                  fun cached_types child =
                    let val _ = step ()
                        val n=inspect (fn () =>
                          G.closure_child_node graph scope child)
                        val ty=inspect (fn () => G.type_of graph n)
                        val own=weight ty val _ = types := ty:: !types
                    in case G.view graph n of G.Application _ =>
                         let val (f,x)=inspect (fn () =>
                               G.closure_application_children
                                 graph scope child)
                         in own+cached_types f+cached_types x end
                       | G.AdmittedBinder _ =>
                         let val held=inspect (fn () =>
                               G.closure_child_binder graph scope child)
                             val data=inspect (fn () =>
                               G.binder_closure_data graph scope held)
                             val bt=inspect (fn () =>
                               G.type_of graph (#binder data))
                             val bw=weight bt val _ = types := bt:: !types
                             val body=inspect (fn () =>
                               G.binder_closure_body graph scope held)
                         in own+bw+cached_types body end
                       | G.OpaqueRetained => raise ERR "discover"
                           "rich projection has no complete type portfolio"
                       | _ => own
                    end
                  val cached_ann=cached_types rich
                  val _ = if cached_ann<=ceiling then
                      W.spend work (IntInf.toInt cached_ann)
                    else raise ERR "discover"
                      "projected annotation portfolio exceeds original Work"
                  (* EXACT record_opened_type_projection spend grammar:
                     initial representative=1; App=3+operator;
                     Binder=6+body; Atom=5. collect pays one per actual
                     incoming incidence, skipping descendants on an ID hit. *)
                  fun path_visits child : IntInf.int =
                    let val _ = step ()
                        val n=inspect (fn () =>
                          G.closure_child_node graph scope child)
                    in case G.view graph n of G.Application _ =>
                         3+path_visits (#1 (inspect (fn () =>
                           G.closure_application_children graph scope child)))
                       | G.AdmittedBinder _ =>
                         6+path_visits (inspect (fn () =>
                           G.binder_closure_body graph scope
                             (G.closure_child_binder graph scope child)))
                       | G.OpaqueRetained => raise ERR "discover"
                           "projection path cannot use an opaque rich node"
                       | _ => 5
                    end
                  val seen=ref ([] : G.node list)
                  fun collected child : IntInf.int =
                    let val _ = step ()
                        val n=inspect (fn () =>
                          G.closure_child_node graph scope child)
                        fun present [] = false
                          | present (held::rest) =
                              (step ();n=held orelse present rest)
                    in if present (!seen) then 1 else
                      (seen := n:: !seen;
                       case G.view graph n of G.Application _ =>
                         let val (f,x)=inspect (fn () =>
                               G.closure_application_children
                                 graph scope child)
                         in 1+collected f+collected x end
                       | G.AdmittedBinder _ =>
                         1+collected (inspect (fn () =>
                           G.binder_closure_body graph scope
                             (G.closure_child_binder graph scope child)))
                       | _ => 1)
                    end
                  (* This scan is rooted at this exact opaque original, so
                     PartialFull's whole ready_root IS its rich annotation.
                     The second rich collect is one hit; old opaque is one. *)
                  val projection_visits=1+path_visits rich+collected rich+2
                  val _ = if projection_visits<=ceiling then
                      W.spend work (IntInf.toInt projection_visits)
                    else raise ERR "discover"
                      "primitive projection capture exceeds original Work"
                  val alpha=inspect (fn () => G.carrier_alpha_for
                    graph scope cap {original= #node d,source=view})
                  val projection=inspect (fn () =>
                    G.record_opened_type_projection graph scope
                      (IntInf.toInt projection_visits) alpha)
                  val actual_visits=inspect (fn () =>
                    G.opened_type_projection_visits graph scope projection)
                  val _ = if IntInf.fromInt actual_visits=projection_visits
                    then () else raise ERR "discover"
                      "actual primitive projection grammar changed"
                  fun projected () =
                    let val data=G.opaque_type_projection_data
                          graph scope projection 0
                    in if #node data= #node d then () else
                      raise ERR "discover" "projected original changed" end
                  val _ = projected ()
                  val _ = (case owner of Owner {backing,...} =>
                    backing := projected :: !backing)
                  fun measure term :
                      IntInf.int * IntInf.int * IntInf.int =
                    let val _ = step ()
                        val ty=inspect (fn () => Term.type_of term)
                        val ann=weight ty val _ = types := ty:: !types
                    in if Term.is_comb term then
                         let val (f,x)=inspect (fn () => Term.dest_comb term)
                             val (a,b,c)=measure f val (e,h,j)=measure x
                         in (1+a+e,1+b+h,ann+c+j) end
                       else if Term.is_abs term then
                         let val (v,b)=inspect (fn () => Term.dest_abs term)
                             val bt=inspect (fn () => Term.type_of v)
                             val bw=weight bt val _ = types := bt:: !types
                             val (a,c,e)=measure b
                         in (1+a,2+c,ann+bw+e) end
                       else (1,1,ann)
                    end
                  val proof= #bridge view
                  val (er,ei,ea)=measure (inspect (fn () => Thm.concl proof))
                  val term=inspect (fn () => G.representative graph target)
                  val (tr,ti,ta)=measure term
                  val (tr2,ti2,ta2)=measure term
                  val (eq_partial,_)=inspect
                    (fn () => Term.dest_comb (Thm.concl proof))
                  val (eq_head,_)=inspect (fn () => Term.dest_comb eq_partial)
                  val header_types=List.map (fn t => inspect
                    (fn () => Term.type_of t))
                    [Thm.concl proof,eq_partial,eq_head]
                  val header=List.foldl (fn (ty,n) => n+weight ty) 0
                    header_types
                  val rr=3+tr+tr2 val ri=3+ti+ti2
                  val ra=header+ta+ta2
                  val amount=er+ei+ea+rr+ri+ra
                  val _ = if er=3+2*raw andalso ei=3+2*inc andalso
                      tr=raw andalso ti=inc andalso tr=tr2 andalso
                      ti=ti2 andalso ta=ta2 andalso ea<=ceiling andalso
                      ra<=ceiling andalso amount<=ceiling then () else
                    raise ERR "discover" "alpha metadata/Work mismatch"
                  val _ = W.spend work (IntInf.toInt amount)
                  val _ = types := header_types @ !types
                  val target_child=inspect
                    (fn () => G.closure_root graph scope target)
                  val identity=inspect (fn () =>
                    G.plan_identity_closure_view graph scope cap
                      (* Original/partial guards remain in data/live,
                         owner.backing and P.source_view validation. The
                         raw opaque original is not an identity recipe. *)
                      {target=target_child,retain=[]})
                  val _ = List.app (fn ty => inspect
                    (fn () => policy owner focus ty)) (List.rev (!types))
                  val target_view=inspect
                    (fn () => G.execute_identity_closure_view identity)
                  val conversion=inspect (fn () => P.record_typed_conversion
                    graph scope {source= #node d,source_view=view,
                      target=target,target_view=target_view,theorem=proof,
                      template_limit=cap,check_type=fn ty => inspect
                        (fn () => policy owner focus ty)})
              in SOME conversion end
          end)
    in case converted of NONE => NONE | SOME conversion =>
      let val leaf=action owner focus (fn observe =>
            C.graph_leaf graph scope {conversion=conversion,
              template_limit=cap,observe=observe})
          val prefix=seal owner focus leaf
          val rest=simplify owner memo stack (#target prefix)
      in join owner focus (SOME prefix) rest end
    end
  (* Concrete proof adapters below retain their SAME-owned receipts. *)
  and is_true owner focus =
    let val Owner {graph,...} = owner val d = describe owner focus
    in action owner focus (fn observe =>
      (observe ();case G.view graph (#node d) of G.Constant id =>
        KernelSig.id_compare
          (id,#Name (Term.dest_thy_constid boolSyntax.T))=EQUAL
       | _ => false)) end
  and lift owner focus (result:outcome) =
    let val Owner {work,conditional,graph,...} = owner
        val d = describe owner focus
        val plan = Lambda.prepare_admitted work
          {frame= #frame d,admission= #admission d,body= #proof result,
           ordinal=ordinal owner,check_type=policy owner focus}
        val value = Lambda.execute work plan
        val converted = Conditional.lambda_conversion_for work conditional
          {frame= #frame d,result=value}
        val leaf = action owner focus (fn observe =>
          C.graph_leaf graph (#scope d)
            {conversion=converted,template_limit= #template_limit
              (W.semantic_limits work),observe=observe})
    in seal owner focus leaf end
  fun begin work {catalogue,traversal,check_type} =
    let val _ = T.validate_for work traversal
        val _ = K.validate_for work catalogue
        val sources = W.original_sources work
        val graph = S.owning_graph sources val root = S.owning_scope sources
        val matcher = M.begin_canonical work catalogue
        val schemas = M.compile matcher
        (* The COMPLETE actual fixed catalogue is checked, not a whitelist.
           Scalar domains and no pattern lambda make HO_PART_MATCH's literal
           match_terml branch exact. Native all-row comparison is separate. *)
        val (net,heads,discovery_heads) = W.with_step work (fn () =>
          let fun step () =
                    (W.validate work graph root sources
                       (W.semantic_limits work);
                     K.validate_for work catalogue;W.spend work 1)
              fun scan term =
                (step ();if Term.is_comb term then
                   let val (f,x) = Term.dest_comb term in scan f;scan x end
                 else if Term.is_abs term then
                   raise ERR "begin" "fixed left pattern contains a lambda"
                 else if Term.is_var term then
                   let val ty = Term.type_of term
                   in if Type.is_vartype ty orelse
                       (case Type.dest_thy_type ty of
                       {Thy="min",Tyop="fun",...} => true | _ => false) then
                     raise ERR "begin"
                       "fixed catalogue has a non-scalar schematic"
                     else () end else ())
              fun vperm (l,r) =
                (step ();case (Term.dest_term l,Term.dest_term r) of
                   (Term.VAR (_,a),Term.VAR (_,b)) => Type.compare (a,b)=EQUAL
                 | (Term.LAMB (_,a),Term.LAMB (_,b)) => vperm (a,b)
                 | (Term.COMB (a,b),Term.COMB (c,d)) =>
                     vperm (a,c) andalso vperm (b,d)
                 | _ => Term.aconv l r)
              fun row schema =
                let val {left,right} = M.pattern_for work schema
                    val _ = scan left
                    val _ = List.app (fn variable =>
                      let val _ = step () val ty = Term.type_of variable
                      in if Type.is_vartype ty orelse
                       (case Type.dest_thy_type ty of
                       {Thy="min",Tyop="fun",...} => true | _ => false) then
                        raise ERR "begin"
                          "fixed rule contains non-scalar free var"
                        else () end)
                      (Term.free_vars (Thm.concl (M.original schema)))
                    val perm = vperm (left,right) andalso
                      HOLset.equal (Term.FVL [left] Term.empty_tmset,
                        Term.FVL [right] Term.empty_tmset)
                    val (head,_) = HolKernel.strip_comb left
                    val {Thy,Name,...} = Term.dest_thy_const head
                    val _ = step ()
                    val constant = G.constant graph root head
                in (schema,left,perm,(Thy,Name),constant) end
              val rows = List.map row schemas
              val net = List.foldr (fn ((schema,left,perm,_,_),net) =>
                (step ();Ho_Net.enter ([],left,(schema,perm)) net))
                Ho_Net.empty rows
              val selected = G.record_discovery_heads graph root
                {heads=List.map (fn (_,_,_,_,node) => node) rows,
                 maximum=W.work_limit work,step=step}
              val _ = step ()
          in (net,List.map (fn (_,_,_,head,_) => head) rows,selected) end)
        val conditional = Conditional.begin work catalogue
          {check_type=check_type}
    in Owner {work=work,graph=graph,root=root,sources=sources,
      catalogue=catalogue,traversal=traversal,matcher=matcher,net=net,
      heads=heads,discovery_heads=discovery_heads,
      conditional=conditional,check_type=check_type,symbols=Term.term_epoch (),
      stack_limit= !Cond_rewr.stack_limit,
      running=ref false,dead=ref false,backing=ref [],frames=ref [],
      validated=ref NONE,fence=ref 0} end
    handle primary => (W.close work;raise primary)
  fun prepare (owner as Owner {running,...}) {frame,admission} =
    protect owner (fn () =>
    (active owner;
     if !running then raise ERR "prepare" "reentrant SIMPLE preparation"
       else ();
     Plan {owner=owner,source=capture owner frame admission,used=ref false}))
  fun execute_internal require_proof
      (Plan {owner=owner as Owner {running,...},source,used}) =
    protect owner (fn () =>
    let val _ = active owner
        val _ = if !running orelse !used then
          raise ERR "execute" "consumed or reentrant SIMPLE plan"
          else (used := true;running := true)
        fun restore () = running := false
        val answer = (let val converted = simplify owner
            (ref ([] : memo_entry list)) [] source
          in case converted of SOME result =>
               SOME (Result {owner=owner,source=source,proof= #proof result})
             | NONE => if require_proof then
                 SOME (Result {owner=owner,source=source,
                   proof= #proof (seal owner source (identity owner source))})
               else NONE end)
          handle primary => (restore ();raise primary)
        val _ = restore () val _ = active owner
    in answer end)
  fun execute plan = valOf (execute_internal true plan)
  fun execute_changed plan = execute_internal false plan
  fun core_for expected
      (Result {owner=owner as Owner {work,...},source,proof}) =
    ((if Portable.pointer_eq (work,expected) then () else
        raise ERR "core_for" "foreign expected Work";
      ignore (describe owner source);
      ignore (Core.conversion_description_for expected proof);proof)
     handle primary => (W.close expected;raise primary))
  fun validate_for expected (owner as Owner {work,...}) =
    ((if Portable.pointer_eq (work,expected) then revalidate owner else
        raise ERR "validate_for" "foreign expected Work")
     handle primary => (W.close expected;raise primary))
  fun validate_cached_for expected (owner as Owner {work,...}) =
    ((if Portable.pointer_eq (work,expected) then active owner else
        raise ERR "validate_cached_for" "foreign expected Work")
     handle primary => (W.close expected;raise primary))
  fun normalize_aux (owner as Owner {work,traversal,...}) target =
    protect owner (fn () =>
      let val held = T.aux_target_for work traversal target
          val plan = prepare owner
            {frame= #frame held,admission= #admission held}
          val result = execute_changed plan
      in case result of NONE =>
           (ignore (T.aux_target_for work traversal target);#conversion held)
       | SOME result =>
         let val proof = core_for work result
             val local_result = D.adopt_compact (#dynamic held) proof
         in D.compose {first= #conversion held,second=local_result,
           ordinal=ordinal owner,check_type=fn ty =>
             (active owner;
              ignore (T.aux_target_for work traversal target);
              let val Owner {check_type,...} = owner in check_type ty end;
              active owner;
              ignore (T.aux_target_for work traversal target))}
         end end)

  (* Actual implementation dependency anchors. Structure aliases alone do
     not force Holmake to load these implementation objects. No call runs. *)
  val _=SmtReplayGraph.discover_selected_partial_with_policy
  val _=SmtReplaySource.goal_source
  val _=SmtReplayInvocationWork.begin_with_policy
  val _=SmtReplayProof.policy_source_realization_generated_equality_for
  val _=SmtReplayProof.record_typed_conversion_with_policy_scoped_profiles
  val _=SmtReplayFocusAdmission.generated_scoped_with_policy
  val _=SmtReplayOwnedScopeReceipt.description_with_policy_for
  val _=SmtLib_GraphNumericCanonical.checked_rules_with_policy
  val _=SmtLib_GraphNumericRuleMatch.begin_canonical_with_policy
  val _=SmtLib_GraphNumericConditional.prepare_owned_with_policy
  val _=SmtLib_GraphNumericConditional.lambda_conversion_with_policy_for
  val _=SmtLib_CompactCarrierScheduler.native_contract_carrier_with_policy_for
  val _=SmtReplayCanonGraph.graph_leaf_with_policy
  val _=SmtReplayOwnedTransport.adopt_core_with_policy_for
  val _=SmtReplayOwnedLargeProofCore.prepare_in_scope_with_policy
  val _=SmtReplayOwnedRealizedLambda.prepare_admitted_with_policy
  val _=SmtReplayNativeContract.validate_for
  val _=SmtReplayResourcePolicy.allows

  (* Private base for the complete fixed-context policy programme. Its
     constructors are not public entry points or caller rule authorities. *)
  structure PolicySimpleBase =
  struct
    structure RP=SmtReplayResourcePolicy
    structure NC=SmtReplayNativeContract
    datatype owner=Owner of
      {work:W.portfolio,graph:G.graph,root:G.scope,sources:S.sources,
       catalogue:K.policy_catalogue,traversal:T.policy_carrier_owner,
       native_contract:NC.contract,profiles:G.policy_opaque_profile list,
       matcher:M.policy_owner,
       net:(M.policy_schema * bool) Ho_Net.net,heads:(string * string) list,
       discovery_heads:G.discovery_heads,
       conditional:Conditional.policy_owner,
       check_type:Type.hol_type -> unit,symbols:int,epoch:int,stack_limit:int,
       running:bool ref,dead:bool ref,backing:(unit -> unit) list ref,
       frames:F.receipt list ref,
       validated:(IntInf.int * (unit -> unit) list) option ref,
       fence:IntInf.int ref}
    type description={node:G.node,child:G.closure_child,scope:G.scope,
      frame:F.receipt,admission:A.policy_focus,source_limit:RP.limit,
      category:A.category}
    datatype focus=Focus of
      {admission:A.policy_focus,frame:F.receipt,scope:G.scope,
       described:(IntInf.int * IntInf.int * description) option ref}
    datatype plan=Plan of {owner:owner,source:focus,used:bool ref}
    datatype result=Result of
      {owner:owner,source:focus,proof:Core.policy_result}
    type outcome={target:focus,recipe:C.graph_conversion,
      proof:Core.policy_result}
    type memo_entry={node:G.node,scope:G.scope,category:A.category,
      limit:RP.limit,stack:(G.node * G.scope) list,result:outcome option}
    exception Inapplicable
    fun close(Owner{work,dead,...})=(dead:=true;W.close work)
    fun protect owner action=action()handle primary=>
      (close owner;raise primary)
    fun active(Owner{work,graph,root,sources,catalogue,traversal,
        native_contract,symbols,epoch,stack_limit,dead,backing,
        discovery_heads,validated,frames,...})=
      let
        val _=if !dead then raise ERR "policy_simple" "numeric owner retired"
          else ()
        val _=NC.validate_for work native_contract
        val _=W.validate_policy work graph root sources(W.semantic_policy work)
        val _=if Term.term_epoch()=symbols andalso Type.type_epoch()=epoch
          then ()else raise ERR "policy_simple" "native epoch changed"
        val _=if !Cond_rewr.stack_limit=stack_limit then ()else
          raise ERR "policy_simple" "fixed conditional stack policy changed"
        val _=guard_app work(F.validate_lifetime_with_policy_for work)(!frames)
        val revision=G.validation_revision graph root
        val rows= !backing
        val hit=case !validated of SOME(old,held)=>
            old=revision andalso Portable.pointer_eq(held,rows)
          | NONE=>false
      in if hit then ()else
        (T.validate_carrier_with_policy_for work traversal;
         K.validate_with_policy_for work catalogue;
         if Portable.pointer_eq(K.native_contract_for work catalogue,
             native_contract)andalso
             Portable.pointer_eq(T.native_contract_carrier_with_policy_for
               work traversal,native_contract)then ()else
           raise ERR "policy_simple" "different actual catalogue contract";
         G.validate_discovery_heads graph root discovery_heads;
         guard_app work(fn guard=>guard())rows;
         W.validate_policy work graph root sources(W.semantic_policy work);
         if Term.term_epoch()=symbols andalso Type.type_epoch()=epoch andalso
             !Cond_rewr.stack_limit=stack_limit andalso
             G.validation_revision graph root=revision andalso
             Portable.pointer_eq(rows,!backing)then
           validated:=SOME(revision,rows)else
           raise ERR "policy_simple" "validation state changed during backing")
      end
    fun revalidate(owner as Owner{validated,fence,...})=
      (fence:= !fence+1;validated:=NONE;active owner)
    fun expected(Owner{graph,sources,work,...})scope=
      {graph=graph,scope=scope,sources=sources,work=work}
    fun describe(owner as Owner{work,graph,root,fence,...})
        (Focus{admission,frame,scope,described}):description=
      let val _=active owner val _=G.validate_scope graph scope
          val revision=G.validation_revision graph root
          val generation= !fence
          fun full()=
            let val data=F.description_with_policy_for work frame
                val _=if Portable.pointer_eq(#graph data,graph)andalso
                    #root data=root andalso #scope data=scope then ()else
                  raise ERR "policy_simple" "foreign actual frame"
                val lower=A.describe_with_policy_for
                  (expected owner scope)admission
                val answer={node= #node lower,child= #child lower,scope=scope,
                  frame=frame,admission=admission,
                  source_limit= #source_limit lower,category= #category lower}
                  :description
                val _=active owner
                val _=if G.validation_revision graph root=revision andalso
                    !fence=generation then ()else
                  raise ERR "policy_simple" "validation state changed"
                val _=described:=SOME(revision,generation,answer)
            in answer end
      in case !described of SOME(old,held,answer)=>
           if old=revision andalso held=generation then answer else full()
         | NONE=>full()end
    fun capture(owner as Owner{work,backing,frames,...})frame admission=
      let val scope= #scope(F.description_with_policy_for work frame)
          fun present []=(W.spend_guard_policy work 1;false)
            | present(held::rest)=
                (W.spend_guard_policy work 1;
                 Portable.pointer_eq(held,frame)orelse present rest)
          val _=if present(!frames)then ()else frames:=frame:: !frames
          val focus=Focus{admission=admission,frame=frame,scope=scope,
            described=ref NONE}
          val _=ignore(describe owner focus)
          val _=backing:=(fn()=>A.validate_with_policy_for
            (expected owner scope)admission):: !backing
      in focus end
    fun action(owner as Owner{work,...})focus operation=
      W.with_step work(fn()=>
        let fun observe()=(ignore(describe owner focus);W.spend_policy work 1)
            val answer=operation observe
            val _=ignore(describe owner focus)
        in answer end)
    fun ordinal(owner as Owner{work,traversal,...})=
      (active owner;T.validate_carrier_with_policy_for work traversal;
       T.carrier_normalization_ordinal_with_policy_for work traversal)
    fun policy(owner as Owner{check_type,...})focus ty=
      (active owner;ignore(describe owner focus);check_type ty;
       active owner;ignore(describe owner focus))
    fun identity(owner as Owner{graph,...})focus=
      let val d=describe owner focus
      in action owner focus(fn observe=>C.graph_identity graph(#scope d)
        {observe=observe}(#node d))end
    fun metric(owner as Owner{graph,profiles,backing,...})focus=
      let val d=describe owner focus
          val capture=G.prepare_scoped_profiled_metric graph(#scope d)
            {node= #node d,profiles=profiles}
          fun backing_guard()=
            let val data=G.profiled_metric_data graph(#scope d)capture
            in if #node data= #node d then ()else
              raise ERR "policy_simple" "different retained metric node"end
          fun guarded()=
            (ignore(describe owner focus);
             G.profiled_metric_data graph(#scope d)capture)
          val data=guarded()
          val _=if #node data= #node d andalso
              RP.allows(#source_limit d)(#raw data)andalso
              RP.allows(#source_limit d)(#inc data)then ()else
            raise ERR "policy_simple" "actual source exceeds its role"
          val _=backing:=backing_guard:: !backing
      in data end
  end

  (* Publication always starts with an actual closed Core result. The
     generated wrapper producer derives its own fact/frame/RHS metric. *)
  structure PolicySimpleProof =
  struct
    open PolicySimpleBase
    fun seal(owner as Owner{work,graph,native_contract,profiles,backing,...})
        focus recipe=
      let val d=describe owner focus
          val plan=Core.prepare_in_scope_with_policy work
            {frame= #frame d,conversion=recipe,ordinal=ordinal owner,
             native_contract=native_contract,profiles=profiles,
             check_type=policy owner focus}
          val proof=Core.execute_with_policy work plan
          val _=backing:=(fn()=>ignore
            (Core.conversion_description_with_policy_for work proof))::
              !backing
          val wrapper=action owner focus(fn observe=>
            let val _=observe()
                val receipt=Core.realization_with_policy_for work proof
            in P.policy_source_realization_generated_equality_for work receipt
              {profiles=profiles}end)
          val target=capture owner(#frame d)
            (A.generated_scoped_with_policy(expected owner(#scope d))
              (#admission d)wrapper)
          val closed=action owner focus(fn observe=>
            C.graph_realized_leaf_with_policy work
              {realization=Core.realization_with_policy_for work proof,
               observe=observe})
      in {target=target,recipe=closed,proof=proof}:outcome end
    fun joined(owner as Owner{work,...})source(left:outcome)(right:outcome)=
      let val recipe=action owner source(fn observe=>
            C.graph_realized_sequence_with_policy work
              {first= #recipe left,second= #recipe right,observe=observe})
      in seal owner source recipe end
    fun after source NONE=source
      | after _ (SOME(value:outcome))= #target value
    fun join owner source NONE right=right
      | join _ _ left NONE=left
      | join owner source(SOME left)(SOME right)=
          SOME(joined owner source left right)
    fun core_for expected
        (Result{owner=owner as Owner{work,...},source,proof})=
      ((if Portable.pointer_eq(work,expected)then ()else
          raise ERR "policy_simple" "foreign expected Work";
        ignore(describe owner source);
        ignore(Core.conversion_description_with_policy_for expected proof);
        proof)
       handle primary=>(W.close expected;raise primary))
    fun validate_for expected(owner as Owner{work,...})=
      ((if Portable.pointer_eq(work,expected)then revalidate owner else
          raise ERR "policy_simple" "foreign expected Work")
       handle primary=>(W.close expected;raise primary))
    fun validate_cached_for expected(owner as Owner{work,...})=
      ((if Portable.pointer_eq(work,expected)then active owner else
          raise ERR "policy_simple" "foreign expected Work")
       handle primary=>(W.close expected;raise primary))
  end

  (* Exact fixed PURE_ss rule order. All native syntax/type inspection here
     concerns genuine fixed catalogue clauses, never a borrowed goal term. *)
  structure PolicySimpleFixedNet =
  struct
    structure RP=SmtReplayResourcePolicy
    structure NC=SmtReplayNativeContract
    fun build work catalogue native_contract profiles=
      (NC.validate_for work native_contract;
       K.validate_with_policy_for work catalogue;
       if Portable.pointer_eq(K.native_contract_for work catalogue,
           native_contract)then ()else
         raise ERR "policy_simple_net" "different actual catalogue contract";
       let val sources=W.original_sources work
           val graph=S.owning_graph sources val root=S.owning_scope sources
           val native=NC.for_work work native_contract
           val matcher=M.begin_canonical_with_policy work catalogue
           val schemas=M.compile_with_policy matcher
           val facts=K.checked_rules_with_policy catalogue
       in W.with_step work(fn()=>
         let
           val ceiling=IntInf.fromInt(#type_work_limit native)
           val used=ref(0:IntInf.int)
           fun valid()=
             (NC.validate_for work native_contract;
              W.validate_policy work graph root sources
                (W.semantic_policy work);
              K.validate_with_policy_for work catalogue)
           fun charge amount=
             (valid();if amount>=0 andalso amount<=ceiling- !used then
                (used:= !used+amount;W.spend_policy work amount)
              else raise ERR "policy_simple_net" "fixed native scan limit";
              valid())
           fun step()=charge 1
           val type_memo=ref([]:(Type.hol_type*IntInf.int)list)
           fun type_weight ty=
             let val _=step()
             in case List.find(fn(held,_)=>Portable.pointer_eq(held,ty))
                 (!type_memo)of SOME(_,amount)=>amount
               | NONE=>
                 let val amount=if Type.is_vartype ty then
                       (charge(IntInf.fromInt
                          (String.size(Type.dest_vartype ty)));
                        1:IntInf.int)
                       else let val{Thy,Tyop,Args}=Type.dest_thy_type ty
                            in charge(IntInf.fromInt(String.size Thy)+
                                 IntInf.fromInt(String.size Tyop));
                               List.foldl(fn(arg,n)=>n+type_weight arg)1 Args
                            end
                     val _=if amount<=ceiling then ()else
                       raise ERR "policy_simple_net" "fixed native Type size"
                     val _=type_memo:=(ty,amount):: !type_memo
                 in amount end
             end
           fun annotation term=
             let val _=step()val own=type_weight(Term.type_of term)
             in if Term.is_comb term then
                  let val(f,x)=Term.dest_comb term
                  in own+annotation f+annotation x end
                else if Term.is_abs term then
                  let val(v,b)=Term.dest_abs term
                  in own+type_weight(Term.type_of v)+annotation b end
                else own end
           fun preflight(schema,fact)=
             let val _=step()
                 val _=P.validate_closed_fact_with_policy graph root
                   (#template_limit(W.semantic_policy work))fact
                 val theorem=M.original_with_policy schema
                 val _=if Portable.pointer_eq(P.closed_original fact,theorem)
                   then ()else raise ERR "policy_simple_net"
                     "different actual canonical clause proof"
                 val capture=G.prepare_scoped_profiled_metric graph root
                   {node=P.closed_node fact,profiles=profiles}
                 val data=G.profiled_metric_data graph root capture
                 val limit=IntInf.fromInt
                   (#template_limit(#semantic_limits native))
                 val _=if #raw data<=limit andalso #inc data<=limit then ()else
                   raise ERR "policy_simple_net" "fixed native schema size"
                 val amount=annotation(Thm.concl theorem)
                 val _=charge amount
                 val _=ignore(G.profiled_metric_data graph root capture)
             in ()end
           val _=if length schemas=length facts then ()else
             raise ERR "policy_simple_net" "canonical clause count changed"
           (* Complete geometry/Type discovery precedes the public FVL/net
              operations. It invokes no external policy and no native rule. *)
           val _=List.app preflight(ListPair.zip(schemas,facts))
           fun scan term=
             (step();if Term.is_comb term then
                let val(f,x)=Term.dest_comb term in scan f;scan x end
              else if Term.is_abs term then raise ERR "policy_simple_net"
                "fixed left pattern contains a lambda"
              else if Term.is_var term then
                let val ty=Term.type_of term
                in if Type.is_vartype ty orelse
                    (case Type.dest_thy_type ty of
                     {Thy="min",Tyop="fun",...}=>true|_=>false)then
                  raise ERR "policy_simple_net" "non-scalar schematic"
                  else ()end else ())
           fun vperm(l,r)=
             (step();case(Term.dest_term l,Term.dest_term r)of
                (Term.VAR(_,a),Term.VAR(_,b))=>Type.compare(a,b)=EQUAL
              | (Term.LAMB(_,a),Term.LAMB(_,b))=>vperm(a,b)
              | (Term.COMB(a,b),Term.COMB(c,d))=>vperm(a,c)andalso vperm(b,d)
              | _=>Term.aconv l r)
           fun row schema=
             let val{left,right}=M.pattern_with_policy_for work schema
                 val _=scan left
                 val _=List.app(fn variable=>
                   let val _=step()val ty=Term.type_of variable
                   in if Type.is_vartype ty orelse
                       (case Type.dest_thy_type ty of
                        {Thy="min",Tyop="fun",...}=>true|_=>false)then
                     raise ERR "policy_simple_net" "non-scalar free variable"
                     else ()end)
                   (Term.free_vars(Thm.concl(M.original_with_policy schema)))
                 val perm=vperm(left,right)andalso
                   HOLset.equal(Term.FVL[left]Term.empty_tmset,
                     Term.FVL[right]Term.empty_tmset)
                 val(head,_)=HolKernel.strip_comb left
                 val{Thy,Name,...}=Term.dest_thy_const head
                 val _=step()val constant=G.constant graph root head
             in(schema,left,perm,(Thy,Name),constant)end
           val rows=List.map row schemas
           val net=List.foldr(fn((schema,left,perm,_,_),net)=>
             (step();Ho_Net.enter([],left,(schema,perm))net))Ho_Net.empty rows
           (* This is a finite bound for this fixed native catalogue scan,
              taken from its actual caller, not a projection of Work policy. *)
           val heads=G.record_discovery_heads graph root
             {heads=List.map(fn(_,_,_,_,node)=>node)rows,
              maximum= #type_work_limit native,step=step}
           val _=valid()
         in{matcher=matcher,net=net,
            heads=List.map(fn(_,_,_,head,_)=>head)rows,
            discovery_heads=heads}end)
       end)handle primary=>(W.close work;raise primary)
  end

  (* A finite native operation has a separate caller contract. Metadata
     limits never supply this allowance. The bounded discovery below is
     itself charged and may refuse; it is not a pre-admitted native walk. *)
  structure PolicySimpleInspection =
  struct
    open PolicySimpleBase
    fun native_nodes
        (owner as Owner{work,graph,native_contract,profiles,backing,...})
        focus operands =
      let
        val native=NC.for_work work native_contract
        val ceiling=IntInf.fromInt(#type_work_limit native)
        val used=ref(0:IntInf.int)
        val held=ref([]:(G.scope*G.node*G.profiled_metric)list)
        fun guard()=
          (NC.validate_for work native_contract;
           guard_app work(fn(scope,node,capture)=>
             let val d=G.profiled_metric_data graph scope capture
             in if #node d=node then ()else raise ERR "policy_native"
               "different actual native operand"end)(!held))
        fun charge amount=
          (guard();if amount>=0 andalso amount<=ceiling- !used then
             (used:= !used+amount;W.spend_policy work amount)
           else raise ERR "policy_native" "native inspection allowance";
           guard())
        fun tick()=charge 1
        val type_memo=ref([]:(Type.hol_type*IntInf.int)list)
        fun type_size ty=
          let val _=tick()
              fun find []=NONE
                | find((old,n)::rest)=
                    (tick();if Portable.pointer_eq(old,ty)then SOME n
                     else find rest)
          in case find(!type_memo)of SOME n=>n | NONE=>
            let val n=if Type.is_vartype ty then
                  (charge(IntInf.fromInt
                     (String.size(Type.dest_vartype ty)));1:IntInf.int)
                  else let val{Thy,Tyop,Args}=Type.dest_thy_type ty
                       in charge(IntInf.fromInt(String.size Thy)+
                            IntInf.fromInt(String.size Tyop));
                         List.foldl(fn(arg,n)=>n+type_size arg)1 Args end
                val _=if n<=ceiling then ()else raise ERR "policy_native"
                  "native Type incidence limit"
                val _=type_memo:=(ty,n):: !type_memo
            in n end
          end
        val term_memo=ref([]:(Term.term*(IntInf.int*IntInf.int*
          IntInf.int))list)
        fun annotation term=
          let val _=tick()
              fun find []=NONE
                | find((old,data)::rest)=
                    (tick();if Portable.pointer_eq(old,term)then SOME data
                     else find rest)
          in case find(!term_memo)of SOME data=>data | NONE=>
            let val own=type_size(Term.type_of term)
                val data=case Term.dest_term term of
                    Term.COMB(f,x)=>
                      let val(a,b,c)=annotation f
                          val(d,e,h)=annotation x
                      in(1+a+d,1+b+e,own+c+h)end
                  | Term.LAMB(v,b)=>
                      let val(a,c,d)=annotation b
                          val binder=type_size(Term.type_of v)
                      in(1+a,2+c,own+binder+d)end
                  | _=>(1,1,own)
                val(_,_,amount)=data
                val _=if amount<=ceiling then ()else
                  raise ERR "policy_native" "repeated annotation limit"
                val _=term_memo:=(term,data):: !term_memo
            in data end
          end
        fun operand(scope,node,maximum,cap)=
          let val capture=G.prepare_scoped_profiled_metric graph scope
                {node=node,profiles=profiles}
              val _=held:=(scope,node,capture):: !held
              val data=G.profiled_metric_data graph scope capture
              val finite=IntInf.fromInt cap
              val _=if cap>0 andalso #raw data<=finite andalso
                  #inc data<=finite andalso
                  RP.allows maximum(#raw data)andalso
                  RP.allows maximum(#inc data)then ()else
                raise ERR "policy_native" "actual native operand role cap"
              val term=G.representative graph node
              val(raw,inc,types)=annotation term
              val _=if raw= #raw data andalso inc= #inc data then ()else
                raise ERR "policy_native" "native/profile geometry changed"
              val _=charge types
          in ()end
        val _=ignore(describe owner focus)
        val _=List.app operand operands
        val _=guard()
        val _=backing:=guard:: !backing
      in ()end
    fun native_preflight owner focus operands=
      native_nodes owner focus(List.map(fn(other,cap)=>
        let val d=describe owner other
        in(#scope d,#node d,#source_limit d,cap)end)operands)
    (* The only non-focus operand here is the genuine instance fact. It
       never accepts an independent theorem or an arbitrary caller node. *)
    fun native_instance(owner as Owner{work,graph,native_contract,...})
        focus instance=
      let val d=describe owner focus
          val fact=M.instance_fact_with_policy_for work instance
          val maximum= #template_limit(W.semantic_policy work)
          val _=P.validate_closed_fact_with_policy graph(#scope d)
            maximum fact
          val _=if Portable.pointer_eq
              (M.instance_native_contract_for work instance,native_contract)
            then ()else raise ERR "policy_native"
              "different actual instance contract"
          val cap= #template_limit
            (#semantic_limits(NC.for_work work native_contract))
          val _=native_nodes owner focus
            [(#scope d,P.closed_node fact,maximum,cap)]
      in P.closed_original fact end
    fun native_source_cap(owner as Owner{work,native_contract,...})focus=
      let val limits= #semantic_limits(NC.for_work work native_contract)
      in case #category(describe owner focus)of
          A.Original=> #input_limit limits
        | A.Generated=> #output_limit limits
        | A.Auxiliary=> #template_limit limits
      end
    fun native_output_cap(Owner{work,native_contract,...})=
      #output_limit(#semantic_limits(NC.for_work work native_contract))
    (* Reject only a constructor mismatch in the actual fixed head Type.
       Pattern Type variables remain unknown here, including repetitions.
       This avoids demanding an opaque argument tree for a schema which
       cannot have that head instance. It grants no native admission. *)
    fun head_types_compatible(owner as Owner{work,graph,...})focus schema=
      let val d=describe owner focus
          val {left,...}=M.pattern_with_policy_for work schema
      in action owner focus(fn observe=>
        let
          fun pattern_head term=
            (observe();if Term.is_comb term then
               pattern_head(#1(Term.dest_comb term))else term)
          fun actual_head child=
            let val _=observe()
                val node=G.closure_child_node graph(#scope d)child
            in case G.view graph node of G.Application _=>
                actual_head(#1(G.closure_application_children
                  graph(#scope d)child))
              | G.Constant _=>SOME(G.type_of graph node)
              | _=>NONE
            end
          val memo=ref([]:(Type.hol_type*Type.hol_type*bool)list)
          fun compatible pattern actual=
            let val _=observe()
                fun find []=NONE
                  | find((p,a,result)::rest)=
                      (observe();if Portable.pointer_eq(p,pattern)andalso
                          Portable.pointer_eq(a,actual)then SOME result
                       else find rest)
            in case find(!memo)of SOME result=>result | NONE=>
              let val answer=if Type.is_vartype pattern then true
                    else if Type.is_vartype actual then false else
                      let val p=Type.dest_thy_typeid pattern
                          val a=Type.dest_thy_typeid actual
                          fun children [] []=true
                            | children(x::xs)(y::ys)=
                                compatible x y andalso children xs ys
                            | children _ _=false
                      in KernelSig.id_compare(#Tyop p,#Tyop a)=EQUAL andalso
                        children(#Args p)(#Args a)end
                  val _=observe()
                  val _=memo:=(pattern,actual,answer):: !memo
              in answer end
            end
          val head=pattern_head left
          val answer=if Term.is_const head then
              case actual_head(#child d)of NONE=>true
                | SOME actual=>compatible(Term.type_of head)actual
            else true
          val _=observe()
        in answer end)
      end
    (* Exact public PURE_ss lookup order. The whole metadata geometry is
       charged IntInf work; it is not projected onto a finite sentinel. *)
    fun candidates(owner as Owner{graph,work,net,heads,...})focus=
      let val d=describe owner focus
          fun head observe child=
            let val _=observe()
                val node=G.closure_child_node graph(#scope d)child
            in case G.view graph node of G.Application _=>
                 head observe(#1(G.closure_application_children
                   graph(#scope d)child))
              | G.Constant id=>
                  let val{Thy,Name}=KernelSig.name_of_id id
                  in SOME(Thy,Name)end
              | _=>NONE
            end
      in action owner focus(fn observe=>case head observe(#child d)of
          NONE=>[]
        | SOME name=>if not(List.exists(fn key=>key=name)heads)then []else
            let val data=metric owner focus
                val _=W.spend_policy work(#raw data)
                val answer=Ho_Net.lookup
                  (G.representative graph(#node d))net
                val _=observe()
            in answer end)
      end
    (* Native equality is reached only after both actual role envelopes
       and repeated annotation incidences have passed the finite contract. *)
    fun same owner first second=
      let val Owner{graph,work,native_contract,profiles,...}=owner
          val left=describe owner first val right=describe owner second
      in action owner first(fn observe=>
        if #scope left<> #scope right then
          (observe();native_preflight owner first
             [(first,native_source_cap owner first),
              (second,native_output_cap owner)];
           observe();let val answer=Term.aconv
             (G.representative graph(#node left))
             (G.representative graph(#node right))
           in observe();ignore(describe owner second);answer end)
        else
          let val scope= #scope left
              val memo=ref([]:(G.node*G.node*bool)list)
              val held=ref([]:G.closure_child list)
              fun lookup a b []=NONE
                | lookup a b((x,y,value)::rest)=
                    (observe();if a=x andalso b=y then SOME value
                     else lookup a b rest)
              fun compare l r=
                let val _=observe()
                    val a=G.closure_child_node graph scope l
                    val b=G.closure_child_node graph scope r
                    val _=held:=l::r:: !held
                in if a=b then true else case lookup a b(!memo)of
                    SOME answer=>answer
                  | NONE=>
                    let val answer=if G.type_id graph a<>
                          G.type_id graph b then false else
                          case(G.view graph a,G.view graph b)of
                            (G.Application _,G.Application _)=>
                              let val(f,x)=G.closure_application_children
                                    graph scope l
                                  val(g,y)=G.closure_application_children
                                    graph scope r
                              in compare f g andalso compare x y end
                          | (G.Application _,_)=>false
                          | (_,G.Application _)=>false
                          | _=>
                              SmtReplayOwnedAlpha.same_inside_with_policy
                                work {caller=scope,traversal=scope,
                                  left=l,right=r,
                                  native_contract=native_contract,
                                  profiles=profiles}
                        val _=observe()
                        val _=memo:=(a,b,answer):: !memo
                    in answer end
                end
              val answer=compare(#child left)(#child right)
              val _=List.app(fn child=>
                (observe();ignore(G.closure_child_node
                  graph scope child)))(!held)
              val _=ignore(describe owner second)
          in answer end)
      end
  end

  (* Same Cond_rewr order after a fresh finite native instance gate.
     IntInf removes only the accumulator representation barrier. *)
  structure PolicySimpleOrder =
  struct
    open PolicySimpleInspection
    fun ac_order owner focus instance = action owner focus (fn observe =>
    let val Owner {work,...} = owner
        val proof=native_instance owner focus instance
        val pair=boolSyntax.dest_eq(#2(boolSyntax.strip_imp(Thm.concl proof)))
        fun text value =
          W.spend_policy work (IntInf.fromInt(String.size value))
        fun weight ty =
          (observe ();if Type.is_vartype ty then
             (text (Type.dest_vartype ty);()) else
           let val {Thy,Tyop,Args} = Type.dest_thy_type ty
           in text Thy;text Tyop;List.app weight Args end)
        fun type_order (a,b) = (weight a;weight b;Type.compare (a,b))
        fun size term : IntInf.int = (observe ();case Term.dest_term term of
            Term.LAMB (_,body) => 1+size body
          | Term.COMB (f,x) => size f+size x | _ => 1)
        fun env_find env term = case env of [] => NONE
          | (key,value)::rest =>
              (observe ();if Term.aconv key term then SOME value
                else env_find rest term)
        fun dest_head env term = (observe ();case Term.dest_term term of
            Term.VAR (name,ty) =>
              (case env_find env term of NONE => (((name,""),0),ty)
              | SOME n => ((("",""),~n),Type.alpha))
          | Term.CONST {Name,Thy,Ty} => (((Name,Thy),1),Ty)
          | Term.LAMB (v,_) => ((("",""),2),Term.type_of v)
          | Term.COMB _ => raise ERR "ac_order" "unstripped application head")
        fun name_order (a,b) = (observe ();text a;text b;String.compare (a,b))
        fun heads (e1,e2) (a,b) =
          let val (((an,at),ak),ay) = dest_head e1 a
              val (((bn,bt),bk),by) = dest_head e2 b
          in case name_order (an,bn) of EQUAL =>
               (case name_order (at,bt) of EQUAL =>
                  (case Int.compare (ak,bk) of EQUAL => type_order (ay,by)
                    | other => other) | other => other)
             | other => other end
        fun compare n (e1,e2) (a,b) =
          (observe ();case IntInf.compare (size a,size b) of EQUAL =>
             if Term.is_abs a then
               if Term.is_abs b then
                 let val (av,ab) = Term.dest_abs a
                     val (bv,bb) = Term.dest_abs b
                 in case type_order (Term.type_of av,Term.type_of bv) of
                     EQUAL => compare (n+1) ((av,n)::e1,(bv,n)::e2) (ab,bb)
                   | other => other end else GREATER
             else if Term.is_abs b then LESS else
               let val (ah,aa) = HolKernel.strip_comb a
                   val (bh,ba) = HolKernel.strip_comb b
                   fun args ([],[]) = EQUAL
                     | args ([],_) = LESS | args (_,[]) = GREATER
                     | args (x::xs,y::ys) =
                         (case compare n (e1,e2) (x,y) of EQUAL =>
                           args (xs,ys) | other => other)
               in case heads (e1,e2) (ah,bh) of EQUAL =>
                    (case Int.compare (length aa,length ba) of EQUAL =>
                      args (aa,ba) | other => other) | other => other end
           | other => other)
    in compare 0 ([],[]) pair end)
  end

  (* The complete fixed net rejects nonconstant/wildcard heads before
     this screen. Generic no-op plus actual absence of ALL those heads is
     the only negative shortcut. Missing genuine profile means unknown. *)
  structure PolicySimpleSelected =
  struct
    open PolicySimpleInspection
    open PolicySimpleProof
    fun selected(owner as Owner{graph,work,profiles,heads,backing,...})focus=
      let val d=describe owner focus
          fun seek []=raise ERR "policy_discover"
                "missing actual selected-source no-op profile"
            | seek(p::rest)=case G.opaque_profile_for_node_with_policy
                graph(#scope d)(#node d)p of NONE=>seek rest
              | SOME _=>p
          val held=seek profiles
          fun guard()=
            case G.opaque_profile_for_node_with_policy
                graph(#scope d)(#node d)held of SOME _=>()
              | NONE=>raise ERR "policy_discover" "different no-op profile"
          val _=guard()
          val data=G.opaque_profile_heads_with_policy graph(#scope d)held
          val _=if #node data= #node d then ()else
            raise ERR "policy_discover" "different actual no-op head root"
          val _=backing:=guard:: !backing
          fun member term=
            let val _=guard()val _=W.spend_policy work 1
                val{Thy,Name,...}=Term.dest_thy_const term
                fun walk []=false
                  | walk(key::rest)=
                      (W.spend_policy work 1;
                       key=(Thy,Name)orelse walk rest)
                val answer=walk heads
                val _=guard()
            in answer end
      in List.exists member(#heads data)end
    fun discover(owner as Owner
        {work,graph,discovery_heads,native_contract,profiles,...})focus=
    let val d = describe owner focus val scope = #scope d
        val native=NC.for_work work native_contract
        val cap= #template_limit(#semantic_limits native)
        val output= #output_limit(#semantic_limits native)
        val ceiling=IntInf.fromInt(#type_work_limit native)
        val interested=selected owner focus
        val converted=if not interested then NONE else
          action owner focus(fn observe=>
          let val _=native_preflight owner focus
                [(focus,native_source_cap owner focus)]
              val source_metric=metric owner focus
              val raw= #raw source_metric val inc= #inc source_metric
              val _=if 3+2*raw<=IntInf.fromInt output andalso
                  3+2*inc<=IntInf.fromInt output andalso
                  3+2*raw<=IntInf.fromInt cap andalso
                  3+2*inc<=IntInf.fromInt cap andalso
                  raw<=IntInf.fromInt(#import_limit native)andalso
                  inc<=IntInf.fromInt(#import_limit native)then ()else
                raise ERR "policy_discover" "native alpha equality envelope"
              val actual_cap=Int.min(#import_limit native,
                Int.min(cap,Int.min(output,native_source_cap owner focus)))
              val receipt=G.discover_selected_partial_with_policy graph scope
                {original= #node d,heads=discovery_heads,
                 maximum=RP.AtMost(IntInf.fromInt actual_cap),
                 scan_limit=RP.AtMost ceiling,step=observe}
              fun data () =
                let val value = G.selected_partial_data_with_policy graph scope
                      discovery_heads receipt
                in if #original value= #node d then value else
                  raise ERR "discover" "selected original changed" end
              val _ = (case owner of Owner {backing,...} =>
                backing := (fn () => ignore (data ())) :: !backing)
          in case #view (data ()) of NONE => NONE
            | SOME view =>
              let val target = #node view
                  val _ = G.validate_opened_view graph scope (#node d) view
                  (* The genuine private alpha recipe preserves every raw,
                     binder-variable and type incidence. Its cached rich
                     profile bounds the old raw term before inspection. *)
                  val opened_metric=G.prepare_scoped_profiled_metric
                    graph scope {node=target,profiles=profiles}
                  fun count metric=
                    let val data=G.profiled_metric_data
                          graph scope opened_metric
                        val n=case metric of G.RawNodes=> #raw data
                          | G.BinderInclusiveNodes=> #inc data
                    in if n<=IntInf.fromInt output then n else
                      raise ERR "policy_discover" "native opened output cap"
                    end
                  val raw = count G.RawNodes
                  val inc = count G.BinderInclusiveNodes
                  val _ = if 3+2*raw<=IntInf.fromInt output andalso
                      3+2*inc<=IntInf.fromInt output andalso
                      3+2*raw<=IntInf.fromInt cap andalso
                      3+2*inc<=IntInf.fromInt cap then () else
                    raise ERR "discover" "alpha equality exceeds quota"
                  val types = ref ([] : Type.hol_type list)
                  fun live () =
                    (ignore (describe owner focus);ignore (data ());
                     G.validate_opened_view graph scope (#node d) view)
                  fun inspect operation =
                    (live ();let val value=operation () in live ();value end)
                  fun step () = (live ();W.spend_policy work 1;live ())
                  fun weight ty : IntInf.int =
                    (step ();if Type.is_vartype ty then
                       (W.spend_policy work
                          (IntInf.fromInt
                            (String.size(Type.dest_vartype ty)));1)
                     else let val {Thy,Tyop,Args}=Type.dest_thy_type ty
                              val _ = W.spend_policy work
                                (IntInf.fromInt(String.size Thy)+
                                 IntInf.fromInt(String.size Tyop))
                          in List.foldl (fn (t,n) => n+weight t) 1 Args end)
                  (* Primitive projection provenance belongs to the exact
                     original opaque object, not a fake no-op profile. Its
                     future capture is planned from the genuine rich path.
                     Cached type incidences precede all raw Term getters. *)
                  val rich=inspect
                    (fn () => G.closure_root graph scope target)
                  fun cached_types child =
                    let val _ = step ()
                        val n=inspect (fn () =>
                          G.closure_child_node graph scope child)
                        val ty=inspect (fn () => G.type_of graph n)
                        val own=weight ty val _ = types := ty:: !types
                    in case G.view graph n of G.Application _ =>
                         let val (f,x)=inspect (fn () =>
                               G.closure_application_children
                                 graph scope child)
                         in own+cached_types f+cached_types x end
                       | G.AdmittedBinder _ =>
                         let val held=inspect (fn () =>
                               G.closure_child_binder graph scope child)
                             val data=inspect (fn () =>
                               G.binder_closure_data graph scope held)
                             val bt=inspect (fn () =>
                               G.type_of graph (#binder data))
                             val bw=weight bt val _ = types := bt:: !types
                             val body=inspect (fn () =>
                               G.binder_closure_body graph scope held)
                         in own+bw+cached_types body end
                       | G.OpaqueRetained => raise ERR "discover"
                           "rich projection has no complete type portfolio"
                       | _ => own
                    end
                  val cached_ann=cached_types rich
                  val _ = if cached_ann<=ceiling then
                      W.spend_policy work cached_ann
                    else raise ERR "discover"
                      "projected annotation portfolio exceeds original Work"
                  (* EXACT record_opened_type_projection spend grammar:
                     initial representative=1; App=3+operator;
                     Binder=6+body; Atom=5. collect pays one per actual
                     incoming incidence, skipping descendants on an ID hit. *)
                  fun path_visits child : IntInf.int =
                    let val _ = step ()
                        val n=inspect (fn () =>
                          G.closure_child_node graph scope child)
                    in case G.view graph n of G.Application _ =>
                         3+path_visits (#1 (inspect (fn () =>
                           G.closure_application_children graph scope child)))
                       | G.AdmittedBinder _ =>
                         6+path_visits (inspect (fn () =>
                           G.binder_closure_body graph scope
                             (G.closure_child_binder graph scope child)))
                       | G.OpaqueRetained => raise ERR "discover"
                           "projection path cannot use an opaque rich node"
                       | _ => 5
                    end
                  val seen=ref ([] : G.node list)
                  fun collected child : IntInf.int =
                    let val _ = step ()
                        val n=inspect (fn () =>
                          G.closure_child_node graph scope child)
                        fun present [] = false
                          | present (held::rest) =
                              (step ();n=held orelse present rest)
                    in if present (!seen) then 1 else
                      (seen := n:: !seen;
                       case G.view graph n of G.Application _ =>
                         let val (f,x)=inspect (fn () =>
                               G.closure_application_children
                                 graph scope child)
                         in 1+collected f+collected x end
                       | G.AdmittedBinder _ =>
                         1+collected (inspect (fn () =>
                           G.binder_closure_body graph scope
                             (G.closure_child_binder graph scope child)))
                       | _ => 1)
                    end
                  (* This scan is rooted at this exact opaque original, so
                     PartialFull's whole ready_root IS its rich annotation.
                     The second rich collect is one hit; old opaque is one. *)
                  val projection_visits=1+path_visits rich+collected rich+2
                  val _ = if projection_visits<=ceiling then
                      W.spend_policy work projection_visits
                    else raise ERR "discover"
                      "primitive projection capture exceeds original Work"
                  val alpha=inspect (fn () => G.carrier_alpha_for
                    graph scope cap {original= #node d,source=view})
                  val projection=inspect (fn () =>
                    G.record_opened_type_projection graph scope
                      (IntInf.toInt projection_visits) alpha)
                  val actual_visits=inspect (fn () =>
                    G.opened_type_projection_visits graph scope projection)
                  val _ = if IntInf.fromInt actual_visits=projection_visits
                    then () else raise ERR "discover"
                      "actual primitive projection grammar changed"
                  fun projected () =
                    let val data=G.opaque_type_projection_data
                          graph scope projection 0
                    in if #node data= #node d then () else
                      raise ERR "discover" "projected original changed" end
                  val _ = projected ()
                  val _ = (case owner of Owner {backing,...} =>
                    backing := projected :: !backing)
                  fun measure term :
                      IntInf.int * IntInf.int * IntInf.int =
                    let val _ = step ()
                        val ty=inspect (fn () => Term.type_of term)
                        val ann=weight ty val _ = types := ty:: !types
                    in if Term.is_comb term then
                         let val (f,x)=inspect (fn () => Term.dest_comb term)
                             val (a,b,c)=measure f val (e,h,j)=measure x
                         in (1+a+e,1+b+h,ann+c+j) end
                       else if Term.is_abs term then
                         let val (v,b)=inspect (fn () => Term.dest_abs term)
                             val bt=inspect (fn () => Term.type_of v)
                             val bw=weight bt val _ = types := bt:: !types
                             val (a,c,e)=measure b
                         in (1+a,2+c,ann+bw+e) end
                       else (1,1,ann)
                    end
                  val proof= #bridge view
                  val (er,ei,ea)=measure (inspect (fn () => Thm.concl proof))
                  val term=inspect (fn () => G.representative graph target)
                  val (tr,ti,ta)=measure term
                  val (tr2,ti2,ta2)=measure term
                  val (eq_partial,_)=inspect
                    (fn () => Term.dest_comb (Thm.concl proof))
                  val (eq_head,_)=inspect (fn () => Term.dest_comb eq_partial)
                  val header_types=List.map (fn t => inspect
                    (fn () => Term.type_of t))
                    [Thm.concl proof,eq_partial,eq_head]
                  val header=List.foldl (fn (ty,n) => n+weight ty) 0
                    header_types
                  val rr=3+tr+tr2 val ri=3+ti+ti2
                  val ra=header+ta+ta2
                  val amount=er+ei+ea+rr+ri+ra
                  val _ = if er=3+2*raw andalso ei=3+2*inc andalso
                      tr=raw andalso ti=inc andalso tr=tr2 andalso
                      ti=ti2 andalso ta=ta2 andalso ea<=ceiling andalso
                      ra<=ceiling andalso amount<=ceiling then () else
                    raise ERR "discover" "alpha metadata/Work mismatch"
                  val _ = W.spend_policy work amount
                  val _ = types := header_types @ !types
                  val target_child=inspect
                    (fn () => G.closure_root graph scope target)
                  val identity=inspect (fn () =>
                    G.plan_scoped_identity_closure_view_with_policy graph scope
                      (#template_limit(W.semantic_policy work))
                      (* Original/partial guards remain in data/live,
                         owner.backing and P.source_view validation. The
                         raw opaque original is not an identity recipe. *)
                      {target=target_child,retain=[],profiles=profiles})
                  val _ = List.app (fn ty => inspect
                    (fn () => policy owner focus ty)) (List.rev (!types))
                  val target_view=inspect
                    (fn () => G.execute_identity_closure_view identity)
                  val conversion=inspect(fn()=>
                    P.record_typed_conversion_with_policy_scoped_profiles
                    graph scope {source= #node d,source_view=view,
                      target=target,target_view=target_view,theorem=proof,
                      template_limit= #template_limit(W.semantic_policy work),
                      profiles=profiles,check_type=fn ty=>inspect
                        (fn()=>policy owner focus ty)})
              in SOME conversion end
          end)
    in case converted of NONE=>NONE | SOME conversion=>
      let val leaf=action owner focus(fn observe=>
            C.graph_leaf_with_policy work
              {frame= #frame d,conversion=conversion,observe=observe})
      in SOME(seal owner focus leaf)end
    end
  end

  (* Closed internal recursion. The two function arguments are wired only
     to the genuine selected-discovery and owned-Lambda adapters; they are
     not part of a public rule, callback or proof-input interface. *)
  structure PolicySimpleNormalize =
  struct
    open PolicySimpleOrder
    open PolicySimpleProof
    fun normalize (discover:owner->focus->outcome option)
        (lift:owner->focus->outcome->outcome) owner source =
      let
        fun simplify memo stack focus=
          let val d=describe owner focus
              val stack_key=action owner focus(fn observe=>
                List.map(fn held=>
                  let val _=observe()val data=describe owner held
                  in(#node data,#scope data)end)stack)
              fun stack_equal observe([],[])=true
                | stack_equal observe((a,s)::xs,(b,t)::ys)=
                    (observe();a=b andalso s=t andalso
                      stack_equal observe(xs,ys))
                | stack_equal _ _=false
              val cached=action owner focus(fn observe=>
                let fun find []=NONE
                      | find((row:memo_entry)::rest)=
                          (observe();if #node row= #node d andalso
                             #scope row= #scope d andalso
                             #category row= #category d andalso
                             #limit row= #source_limit d andalso
                             stack_equal observe(#stack row,stack_key)
                           then SOME(#result row)else find rest)
                in find(!memo)end)
              fun reuse(old:outcome)=
                let val Owner{work,profiles,...}=owner
                    val _=ignore(Core.conversion_description_with_policy_for
                      work(#proof old))
                    val wrapper=action owner focus(fn observe=>
                      (observe();
                       P.policy_source_realization_generated_equality_for
                         work(Core.realization_with_policy_for
                           work(#proof old)){profiles=profiles}))
                    val target=capture owner(#frame d)
                      (A.generated_scoped_with_policy
                        (expected owner(#scope d))(#admission d)wrapper)
                in {target=target,recipe= #recipe old,proof= #proof old}
                  :outcome end
          in case cached of SOME NONE=>NONE
            | SOME(SOME old)=>SOME(reuse old)
            | NONE=>
                let val result=fresh memo stack focus
                    val _=action owner focus(fn observe=>
                      (observe();memo:={node= #node d,scope= #scope d,
                        category= #category d,limit= #source_limit d,
                        stack=stack_key,result=result}:: !memo))
                in result end
          end
        and fresh memo stack focus=
          let val(middle,roots)=repeat memo stack focus
              val children=descend memo stack middle
          in case children of NONE=>roots | SOME child_result=>
            let val prefix=join owner focus roots(SOME child_result)
                val retry=if same owner middle(#target child_result)
                  then NONE else rewrite memo stack(#target child_result)
            in case retry of NONE=>prefix | SOME changed=>
              join owner focus(join owner focus prefix(SOME changed))
                (simplify memo stack(#target changed))end
          end
        and repeat memo stack first=
          let fun loop current accumulated=
                case rewrite memo stack current of NONE=>(current,accumulated)
                | SOME result=>loop(#target result)
                    (join owner first accumulated(SOME result))
          in loop first NONE end
        and rewrite memo stack focus=
          let val Owner{work,matcher,conditional,stack_limit,...}=owner
              val d=describe owner focus
              fun attempt []=NONE
                | attempt((schema,isperm)::rest)=
                  if not(head_types_compatible owner focus schema)then
                    attempt rest else
                  (case M.prepare_with_policy matcher
                      {policy_schema=schema,caller= #scope d,
                       traversal= #scope d,target= #child d}of
                      M.PolicyNoMatch=>attempt rest
                    | M.PolicyNeedsHigherOrder=>raise ERR "policy_simple"
                        "fixed scalar clause needs higher-order matching"
                    | M.PolicyMatched matched=>
                      let val metadata=M.describe_with_policy_for work matched
                          val count=length(#conditions metadata)
                      in if length stack+count>stack_limit then attempt rest
                        else
                        let val instance=M.instantiate_with_policy matched
                              {check_type=policy owner focus}
                            val applicable=action owner focus(fn observe=>
                              let val _=observe()
                                  val proof=native_instance
                                    owner focus instance
                                  val(_,body)=boolSyntax.strip_imp
                                    (Thm.concl proof)
                                  val(l,r)=boolSyntax.dest_eq body
                                  val answer=not(Term.aconv l r)
                              in observe();answer end)
                            val applicable=applicable andalso
                              (not isperm orelse
                               ac_order owner focus instance=GREATER)
                        in if not applicable then attempt rest else
                          let val conditions=List.tabulate(count,fn index=>
                                capture owner(#frame d)
                                  (A.initial_condition_with_policy work
                                    {instance=instance,index=index}))
                              val looping=List.exists(fn ant=>
                                List.exists(same owner ant)stack)conditions
                          in if looping then attempt rest else
                            let val next_stack=conditions@stack
                                fun prove condition=
                                  let val normalized=case
                                        simplify memo next_stack condition of
                                          NONE=>seal owner condition
                                            (identity owner condition)
                                        | SOME result=>result
                                  in if is_true(#target normalized)then
                                      #proof normalized
                                    else raise Inapplicable end
                                val evidence=List.map prove conditions
                                val prepared=
                                  Conditional.prepare_owned_with_policy
                                    conditional {frame= #frame d,
                                      instance=instance,conditions=evidence,
                                      ordinal=ordinal owner}
                                val result=Conditional.execute_with_policy
                                  prepared
                                val converted=
                                  Conditional.conversion_with_policy_for
                                    work result
                                val leaf=action owner focus(fn observe=>
                                  C.graph_leaf_with_policy work
                                    {frame= #frame d,conversion=converted,
                                     observe=observe})
                            in SOME(seal owner focus leaf)end
                            handle Inapplicable=>
                              (ignore(describe owner focus);attempt rest)
                          end
                        end
                      end)
          in attempt(candidates owner focus)end
        and descend memo stack focus=
          let val Owner{graph,work,...}=owner
              val d=describe owner focus val scope= #scope d
          in case G.view graph(#node d)of
              G.Application _=>
                let val(a,b)=A.application_children_with_policy
                      (expected owner scope)(#admission d)
                    val left=capture owner(#frame d)a
                    val right=capture owner(#frame d)b
                    val l=simplify memo stack left
                    val r=simplify memo stack right
                in case(l,r)of(NONE,NONE)=>NONE | _=>
                  let val lp=case l of NONE=>identity owner left
                        | SOME x=> #recipe x
                      val rp=case r of NONE=>identity owner right
                        | SOME x=> #recipe x
                      val composed=action owner focus(fn observe=>
                        C.graph_application_fused graph scope
                          {source= #node d,left=lp,right=rp,observe=observe})
                  in SOME(seal owner focus composed)end
                end
            | G.AdmittedBinder _=>
                let val frame=F.body_with_policy work(#frame d)(#child d)
                    val body=capture owner frame
                      (A.binder_body_with_policy(expected owner scope)
                        (#admission d))
                in case simplify memo stack body of NONE=>NONE
                  | SOME result=>SOME(lift owner focus result)end
            | G.OpaqueRetained=>
                (case discover owner focus of NONE=>NONE | SOME prefix=>
                  join owner focus(SOME prefix)
                    (simplify memo stack(#target prefix)))
            | _=>NONE
          end
        and is_true focus=
          let val Owner{graph,...}=owner val d=describe owner focus
          in action owner focus(fn observe=>
            (observe();case G.view graph(#node d)of G.Constant id=>
               KernelSig.id_compare
                 (id,#Name(Term.dest_thy_constid boolSyntax.T))=EQUAL
             | _=>false))end
      in simplify(ref([]:memo_entry list))[] source end
  end

  structure PolicySimpleLifecycle =
  struct
    open PolicySimpleBase
    fun begin_policy work
        {catalogue,traversal,native_contract,profiles,check_type} =
      ((let
          val _=NC.validate_for work native_contract
          val _=T.validate_carrier_with_policy_for work traversal
          val _=K.validate_with_policy_for work catalogue
          val _=if Portable.pointer_eq
              (T.native_contract_carrier_with_policy_for work traversal,
               native_contract)andalso Portable.pointer_eq
              (K.native_contract_for work catalogue,native_contract)
            then ()else raise ERR "policy_simple"
              "different actual native caller contract"
          val sources=W.original_sources work
          val graph=S.owning_graph sources
          val root=S.owning_scope sources
          val net=PolicySimpleFixedNet.build work catalogue
            native_contract profiles
          val held=ref(NONE:owner option)
          fun conditional_type ty=case !held of NONE=>
                raise ERR "policy_simple" "premature conditional callback"
            | SOME owner=>(active owner;check_type ty;active owner)
          val conditional=Conditional.begin_with_policy work catalogue
            {profiles=profiles,check_type=conditional_type}
          val owner=Owner{work=work,graph=graph,root=root,sources=sources,
            catalogue=catalogue,traversal=traversal,
            native_contract=native_contract,profiles=profiles,
            matcher= #matcher net,net= #net net,heads= #heads net,
            discovery_heads= #discovery_heads net,conditional=conditional,
            check_type=check_type,symbols=Term.term_epoch(),
            epoch=Type.type_epoch(),stack_limit= !Cond_rewr.stack_limit,
            running=ref false,dead=ref false,backing=ref[],frames=ref[],
            validated=ref NONE,fence=ref 0}
          val _=held:=SOME owner
          val _=active owner
        in owner end)
       handle primary=>(W.close work;raise primary))
    fun prepare_policy(owner as Owner{running,...}){frame,admission}=
      protect owner(fn()=>
        (active owner;if !running then raise ERR "policy_simple"
           "reentrant SIMPLE preparation"else();
         Plan{owner=owner,source=capture owner frame admission,
           used=ref false}))
    (* These internal adapter arguments are fixed in the eventual module
       exports, never supplied by a user of the policy API. *)
    fun execute_internal require_proof discover lift
        (Plan{owner=owner as Owner{running,...},source,used})=
      protect owner(fn()=>
        let val _=active owner
            val _=if !running orelse !used then raise ERR "policy_simple"
                "consumed or reentrant SIMPLE plan"
              else(used:=true;running:=true)
            fun restore()=running:=false
            val answer=(let
                val converted=PolicySimpleNormalize.normalize
                  discover lift owner source
              in case converted of SOME result=>
                   SOME(Result{owner=owner,source=source,proof= #proof result})
                | NONE=>if require_proof then
                    SOME(Result{owner=owner,source=source,
                      proof= #proof(PolicySimpleProof.seal owner source
                        (identity owner source))})else NONE end)
              handle primary=>(restore();raise primary)
            val _=restore()val _=active owner
        in answer end)
  end

  structure PolicySimpleLambda =
  struct
    open PolicySimpleBase
    open PolicySimpleProof
    fun lift(owner as Owner
        {work,conditional,native_contract,profiles,...})focus(result:outcome)=
      let val d=describe owner focus
          val plan=Lambda.prepare_admitted_with_policy work
            {frame= #frame d,admission= #admission d,body= #proof result,
             ordinal=ordinal owner,native_contract=native_contract,
             profiles=profiles,check_type=policy owner focus}
          val value=Lambda.execute_with_policy work plan
          val converted=Conditional.lambda_conversion_with_policy_for
            work conditional {frame= #frame d,result=value}
          val leaf=action owner focus(fn observe=>
            C.graph_leaf_with_policy work
              {frame= #frame d,conversion=converted,observe=observe})
      in seal owner focus leaf end
  end

  type policy_owner=PolicySimpleBase.owner
  type policy_plan=PolicySimpleBase.plan
  type policy_result=PolicySimpleBase.result
  val begin_with_policy=PolicySimpleLifecycle.begin_policy
  val prepare_with_policy=PolicySimpleLifecycle.prepare_policy
  val validate_with_policy_for=PolicySimpleProof.validate_for
  val validate_cached_with_policy_for=PolicySimpleProof.validate_cached_for
  val core_with_policy_for=PolicySimpleProof.core_for
  fun execute_changed_with_policy plan=
    PolicySimpleLifecycle.execute_internal false
      PolicySimpleSelected.discover PolicySimpleLambda.lift plan
  fun execute_with_policy plan=valOf
    (PolicySimpleLifecycle.execute_internal true
      PolicySimpleSelected.discover PolicySimpleLambda.lift plan)
  fun normalize_aux_with_policy
      (owner as PolicySimpleBase.Owner{work,traversal,check_type,...})target=
    PolicySimpleBase.protect owner(fn()=>
      let val held=T.carrier_aux_target_with_policy_for work traversal target
          val plan=prepare_with_policy owner
            {frame= #frame held,admission= #admission held}
          val result=execute_changed_with_policy plan
      in case result of NONE=>
          (ignore(T.carrier_aux_target_with_policy_for work traversal target);
           #conversion held)
        | SOME result=>
          let val proof=core_with_policy_for work result
              val scope= #scope(F.description_with_policy_for
                work(#frame held))
              val local_result=D.adopt_core_with_policy_for
                (PolicySimpleBase.expected owner scope)(#dynamic held)proof
          in D.compose_with_policy
            {first= #conversion held,second=local_result,
             ordinal=PolicySimpleBase.ordinal owner,check_type=fn ty=>
               (PolicySimpleBase.active owner;
                ignore(T.carrier_aux_target_with_policy_for
                  work traversal target);
                check_type ty;PolicySimpleBase.active owner;
                ignore(T.carrier_aux_target_with_policy_for
                  work traversal target))}end
      end)

end
