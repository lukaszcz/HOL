(* Root-frame compact scheduling. Private/kernel/full PLAN costs stay open. *)
structure SmtLib_CompactCarrierScheduler :> SmtLib_CompactCarrierScheduler =
struct
  structure G = SmtReplayGraph
  structure S = SmtReplaySource
  structure W = SmtReplayInvocationWork
  structure D = SmtReplayOwnedTransport
  structure Q = SmtReplayFocusAdmission
  structure R = SmtLib_TraversalRootRecognition
  structure B = SmtReplayRecordedBeta
  structure Carrier = SmtLib_GraphCarrierRoot
  structure Laws = SmtLib_CarrierLaws
  structure C = SmtReplayCanonGraph
  structure P = SmtReplayProof
  structure Core = SmtReplayOwnedLargeProofCore
  structure Scope = SmtReplayOwnedScopeReceipt
  structure Lambda = SmtReplayOwnedRealizedLambda
  structure Aux = SmtLib_GraphSelectedAuxiliary
  val _ = SmtLib_GraphSelectedAuxiliary.describe_for
  val _ = SmtReplayOwnedTransport.start_auxiliary
  val _ = SmtReplayFocusAdmission.initial_auxiliary
  val _ = SmtReplayGraph.record_opened_type_projection
  val _ = SmtReplayCanonGraph.graph_realized_leaf
  val _ = SmtReplayCanonGraph.graph_realized_sequence
  val _ = SmtReplayOwnedLargeProofCore.realization_for
  val _ = SmtReplayGraph.carrier_alpha_source_for
  val _ = SmtReplayOwnedTransport.start_assumption
  val _ = SmtLib_TraversalRootRecognition.inspect_admitted
  val _ = SmtReplayRecordedBeta.prepare_admitted
  val _ = SmtLib_GraphCarrierRoot.prepare_closure_admitted
  val _ = SmtLib_CarrierLaws.begin
  val _ = SmtReplayOwnedRealizedLambda.prepare_admitted
  val ERR = Feedback.mk_HOL_ERR "SmtLib_CompactCarrierScheduler"
  (* Retained guard portfolios are separate from native syntax quotes.
     This payer uses the original counter in either Idle or Busy. *)
  fun guard_app work action rows =
    let fun visit [] = W.spend_guard_policy work 1
          | visit (row::rest) =
              (W.spend_guard_policy work 1;action row;visit rest)
    in visit rows end
  fun guard_member work wanted rows =
    let fun visit [] = (W.spend_guard_policy work 1;false)
          | visit (row::rest) =
              (W.spend_guard_policy work 1;
               Portable.pointer_eq (row,wanted) orelse visit rest)
    in visit rows end
  datatype owner = Owner of
    {marker : unit ref,graph : G.graph,scope : G.scope,sources : S.sources,
     work : W.portfolio,limits : W.limits,epoch : int,symbols : int,
     laws : Laws.owner,next : int ref,running : bool ref,
     backing : (unit -> unit) list ref,
     validated : (IntInf.int * (unit -> unit) list) option ref,
     fence : IntInf.int ref,
     root_receipt : Scope.receipt,frames : Scope.receipt list ref,
     local_receipts : (P.closed_fact * D.conversion) list ref,
     check_type : Type.hol_type -> unit,scope_opened : G.scope -> unit}
  type description =
    {node:G.node,child:G.closure_child,dynamic:D.focus,admission:Q.focus,
     frame:G.scope,receipt:Scope.receipt,category:Q.category}
  datatype focus = Focus of
    {dynamic : D.focus,admission : Q.focus,frame : G.scope,
     receipt : Scope.receipt,auxiliary : Aux.receipt option,
     described : (IntInf.int * IntInf.int * description) option ref}
  datatype result = Result of
    {marker : unit ref,source : focus,target : focus,
     recipe : C.graph_conversion,raw : C.graph_conversion,
     receipts : G.carrier_alpha list}
  type outcome = {source : focus,target : focus,recipe : C.graph_conversion,
                  original_recipe : C.graph_conversion,
                  bounded : D.conversion option,body_result : Core.result option}
  datatype aux_target = AuxTarget of
    {owner:owner,marker:unit ref,original:focus,target:focus,
     law:Aux.receipt,converted:D.conversion}
  datatype source_target = SourceTarget of
    {owner:owner,marker:unit ref,original:focus,target:focus,raw_source:G.node,
     raw:C.graph_conversion option,receipts:G.carrier_alpha list}
  datatype raw_completion = RawReady of C.graph_conversion
    | RawPhases of C.graph_conversion * C.graph_conversion
  datatype raw_plan = RawAlpha of G.carrier_alpha * D.focus
    | RawApplication of G.node * raw_plan * raw_plan
    | RawClosed of G.carrier_alpha * D.focus * D.conversion * G.node
  fun close (Owner {work,...}) = W.close work
  fun protected owner action = action ()
    handle primary => (close owner;raise primary)
  fun validate (Owner
      {graph,scope,sources,work,limits,epoch,symbols,laws,backing,
       validated,frames,...}) =
    let
      val _ = W.validate work graph scope sources limits
      val _ = if Type.type_epoch () = epoch andalso
          Term.term_epoch () = symbols then () else
        raise ERR "owner" "retirement epoch changed"
      val _ = guard_app work (Scope.validate_lifetime_for work) (!frames)
      val revision = G.validation_revision graph scope
      val rows = !backing
      val hit = case !validated of SOME (old,held) =>
          old=revision andalso Portable.pointer_eq (held,rows)
        | NONE => false
    in if hit then () else
      (Laws.validate laws;guard_app work (fn guard => guard ()) rows;
       W.validate work graph scope sources limits;
       if Type.type_epoch () = epoch andalso Term.term_epoch () = symbols
           andalso G.validation_revision graph scope=revision andalso
           Portable.pointer_eq (rows,!backing) then
         validated := SOME (revision,rows) else
         raise ERR "active" "validation state changed during backing pass")
    end
  fun revalidate (owner as Owner {validated,fence,...}) =
    (fence := !fence+1;validated := NONE;validate owner)
  fun expected (Owner {graph,sources,work,...}) frame =
    {graph = graph,scope = frame,sources = sources,work = work}
  fun auxiliary (Focus {auxiliary,...}) = auxiliary
  fun describe (owner as Owner {graph,scope=root,fence,...})
      (Focus {dynamic,admission,frame,receipt,auxiliary,described}) =
    let val _ = validate owner val _ = G.validate_scope graph frame
        val revision=G.validation_revision graph root val generation= !fence
  fun full () =
    let val expectation = expected owner frame
        val Owner {work,graph,sources,scope = root,...} = owner
        val scope_data = Scope.description_for work receipt
        val _ = if Portable.pointer_eq (#graph scope_data,graph) andalso
            Portable.pointer_eq (#sources scope_data,sources) andalso
            #scope scope_data = frame then () else
          raise ERR "focus" "different authentic scope receipt"
        val lower = Q.describe_for expectation admission
        val upper = D.description_for expectation dynamic
        fun generated () = #category lower = Q.Generated andalso
          (case #provenance upper of D.GeneratedResult => true
            | D.GeneratedDescendant => true | _ => false)
        val lineage = case auxiliary of NONE =>
              (case #occurrence upper of
                 SOME n => n = #occurrence lower
               | NONE => #occurrence lower = ~1 andalso
                   (case #provenance upper of
                      D.OriginalPositiveGoal => #category lower = Q.Original
                    | D.PositiveGoalDescendant => #category lower = Q.Original
                    | D.UnopenedPositiveGoal => #category lower = Q.Original
                    | D.UnopenedGoalDescendant => #category lower = Q.Original
                    | _ => generated ()))
          | SOME law =>
              let val law_data = Aux.describe_for (expected owner root) law
                  val root_aux = #provenance upper = D.ClosedAuxiliaryRoot
                  val child_aux =
                    #provenance upper = D.ClosedAuxiliaryDescendant
                  val initial = (root_aux orelse child_aux) andalso
                    #category lower = Q.Auxiliary andalso
                    (not root_aux orelse
                     (frame = root andalso
                      #node upper = #node (#opened law_data)))
              in #occurrence upper = NONE andalso
                #occurrence lower = ~2 andalso (initial orelse generated ())
              end
        val _ = if #node lower = #node upper andalso
            #scope upper = frame andalso lineage then () else
          raise ERR "focus" "different exact owned node/frame/occurrence"
        val answer = {node = #node upper,child = #child lower,
          dynamic = dynamic,admission = admission,frame = frame,
          receipt = receipt,category = #category lower} : description
        val _ = validate owner
        val _ = if G.validation_revision graph root=revision andalso
            !fence=generation then () else
          raise ERR "focus" "validation state changed"
        val _ = described := SOME (revision,generation,answer)
    in answer end
    in case !described of SOME (old,held,answer) =>
         if old=revision andalso held=generation then answer else full ()
       | NONE => full () end
  fun capture owner auxiliary frame receipt dynamic admission =
    let val focus = Focus
          {dynamic = dynamic,admission = admission,frame = frame,
          receipt = receipt,auxiliary = auxiliary,described = ref NONE}
        val _ = ignore (describe owner focus)
        val Owner {work,backing,frames,...} = owner
        val _ = if guard_member work receipt (!frames) then () else
          frames := receipt :: !frames
        val expectation = expected owner frame
        val _ = backing := (fn () =>
          (case auxiliary of NONE => () | SOME law =>
             let val Owner {scope,...} = owner
             in Aux.validate_for (expected owner scope) law end;
           Q.validate_for expectation admission;
           ignore (D.description_for expectation dynamic))) :: !backing
    in focus end
  fun control (owner as Owner {work,...}) = W.with_step work (fn () =>
    (validate owner;W.spend work 1;validate owner))
  fun ordinal (owner as Owner {work,next,...}) = W.with_step work (fn () =>
    (validate owner;W.spend work 1;
     let val n = !next in next := n+1;n end))
  fun validate_for expected (owner as Owner {work,...}) =
    ((if Portable.pointer_eq (expected,work) then () else
        raise ERR "validate_for" "different original Work";
      validate owner)
     handle primary => (W.close expected;raise primary))
  fun revalidate_for expected (owner as Owner {work,...}) =
    ((if Portable.pointer_eq (expected,work) then () else
        raise ERR "revalidate_for" "different original Work";
      revalidate owner)
     handle primary => (W.close expected;raise primary))
  fun normalization_ordinal owner = protected owner (fn () => ordinal owner)
  fun policy (owner as Owner {check_type,...}) focus ty =
    (validate owner;ignore (describe owner focus);check_type ty;
     validate owner;ignore (describe owner focus))
  fun observer (owner as Owner {scope_opened,...}) focus frame =
    (validate owner;ignore (describe owner focus);scope_opened frame;
     validate owner;ignore (describe owner focus))
  fun in_action (owner as Owner {work,...}) focus action =
    W.with_step work (fn () =>
      let fun observe () =
            (ignore (describe owner focus);W.spend work 1)
          val result = action observe
      in ignore (describe owner focus);result end)
  fun identity (owner as Owner {graph,...}) focus =
    let val data = describe owner focus
    in in_action owner focus (fn observe => C.graph_identity graph
      (#frame data) {observe = observe} (#node data)) end
  fun realize (owner as Owner {work,...}) focus recipe =
    let val data = describe owner focus
        val plan = Core.prepare_in_scope work
          {frame = #receipt data,conversion = recipe,
          ordinal = ordinal owner,check_type = policy owner focus}
        val receipt = Core.execute work plan
        val Owner {backing,...} = owner
        val _ = backing := (fn () => ignore
          (Core.conversion_description_for work receipt)) :: !backing
        val dynamic = D.adopt_compact (#dynamic data) receipt
        val admission = Q.generated_compact (expected owner (#frame data))
          (#admission data) receipt
        val target = capture owner (auxiliary focus) (#frame data) (#receipt data)
          (D.target_focus dynamic) admission
    in {source = focus,target = target,recipe = recipe,
      original_recipe = recipe,bounded = SOME dynamic,
      body_result = SOME receipt}
      : outcome end
  (* The only closed-phase constructor prepares and executes this exact
     program, then wraps the SAME opaque result receipt. No theorem/node
     pair, semantic-node witness table or caller phase token is accepted. *)
  fun seal_program (owner as Owner {work,backing,...}) focus program =
    let val data = describe owner focus
        val plan = Core.prepare_in_scope work
          {frame = #receipt data,conversion = program,
           ordinal = ordinal owner,check_type = policy owner focus}
        val result = Core.execute work plan
        val _ = backing := (fn () => ignore
          (Core.conversion_description_for work result)) :: !backing
        val closed = in_action owner focus (fn observe =>
          C.graph_realized_leaf work
            {realization = Core.realization_for work result,
             observe = observe})
    in (closed,result) end
  (* A composed parent closes with its ALREADY executed Core result.
     The next ancestor sees one genuine leaf, rather than every old parent
     equality frame. Coherent legacy/fused parents retain their old route. *)
  fun close_application (owner as Owner {work,...}) focus
      (result : outcome) =
    let val body = case #body_result result of SOME receipt => receipt
          | NONE => raise ERR "close_application"
              "missing already executed application result"
        val closed = in_action owner focus (fn observe =>
          C.graph_realized_leaf work
            {realization = Core.realization_for work body,
             observe = observe})
    in {source = #source result,target = #target result,recipe = closed,
      original_recipe = #original_recipe result,bounded = #bounded result,
      body_result = SOME body} : outcome end
  fun join owner original NONE second = second
    | join owner original first NONE = first
    | join (owner as Owner {graph,...}) original
        (SOME (a : outcome)) (SOME (b : outcome)) =
        let val middle = describe owner (#target a)
            val beginning = describe owner (#source b)
            val _ = if #node middle = #node beginning andalso
                #frame middle = #frame beginning then () else
              raise ERR "join" "different exact continuation focus"
            (* Retain the exact phase recipes independently of their closed
               realization leaves. Same-node phases keep distinct objects. *)
            val history = in_action owner original (fn observe =>
              C.graph_sequence graph (#frame middle)
                {first = #original_recipe a,second = #original_recipe b,
                 observe = observe})
            val (left,_) = seal_program owner (#source a) (#recipe a)
            val (right,_) = seal_program owner (#source b) (#recipe b)
            val sequence = in_action owner original (fn observe =>
              C.graph_sequence graph (#frame middle)
                {first = left,second = right,observe = observe})
            val converted = realize owner original sequence
            val Owner {work,...} = owner
            val body = case #body_result converted of SOME result => result
              | NONE => raise ERR "join" "missing genuine closed phase result"
            val closed = in_action owner original (fn observe =>
              C.graph_realized_leaf work
                {realization = Core.realization_for work body,
                 observe = observe})
        in SOME {source = original,target = #target converted,recipe = closed,
          original_recipe = history,bounded = #bounded converted,
          body_result = SOME body} end
  fun local_result (owner as Owner {graph,work,limits,...}) focus converted =
    let val data = describe owner focus
        val expectation = expected owner (#frame data)
        val endpoints = D.conversion_description_for expectation converted
        val Owner {backing,...} = owner
        val _ = backing := (fn () => ignore
          (D.conversion_description_for expectation converted)) :: !backing
        val _ = if #source endpoints = #node data then () else
          raise ERR "local" "different source focus"
        val fact = D.closed_fact_for expectation converted
          {ordinal = ordinal owner,check_type = policy owner focus}
        val Owner {local_receipts,...} = owner
        val _ = local_receipts := (fact,converted) :: !local_receipts
        val admission = Q.generated expectation (#admission data) fact
        val target = capture owner (auxiliary focus) (#frame data) (#receipt data)
          (D.target_focus converted) admission
        val recipe = in_action owner focus (fn observe =>
          C.graph_conversion_with_closed graph (#frame data)
            {template_limit = #template_limit limits,revisit = false,
             propose = fn node =>
               if node = #node data then SOME fact else NONE,
             observe = observe} (#node data))
    in {source = focus,target = target,recipe = recipe,
      original_recipe = recipe,bounded = SOME converted,body_result = NONE}
      : outcome end
  fun probe owner carrier focus =
    let val _ = control owner
        val Owner {graph,sources,work,laws,...} = owner
        val data = describe owner focus
        val expectation = expected owner (#frame data)
        val request = {graph = graph,scope = #frame data,sources = sources,
          work = work,admission = #admission data}
        val checked = R.inspect_admitted request
        val _ = R.validate_for {graph = graph,scope = #frame data,
          sources = sources,work = work,focus = #child data} checked
        val _ = ignore (describe owner focus)
    in if carrier then case R.carrier checked of NONE => NONE
      | SOME kind =>
        let val flags = case kind of
                R.NumForall => {natural = true,universal = true}
              | R.NumExists => {natural = true,universal = false}
              | R.BagForall => {natural = false,universal = true}
              | R.BagExists => {natural = false,universal = false}
            val law = Laws.get laws flags
            val receipt = Carrier.execute (Carrier.prepare_closure_admitted
              {graph = graph,scope = #frame data,sources = sources,work = work,
               ordinal = ordinal owner,admission = #admission data,law = law,
               check_type = policy owner focus,
               scope_opened = observer owner focus})
        in SOME (local_result owner focus
          (D.adopt_carrier (#dynamic data) receipt)) end
      else if R.beta checked then
        let val receipt = B.execute (B.prepare_admitted
              {graph = graph,scope = #frame data,sources = sources,work = work,
               ordinal = ordinal owner,admission = #admission data,
               check_type = policy owner focus,
               scope_opened = observer owner focus})
        in SOME (local_result owner focus
          (D.adopt_beta (#dynamic data) receipt)) end
      else NONE
    end
  (* Compare actual canonical constructor incidence. Equal retained holes
     are reflexive aliases; unequal IDs alone never decide alpha inequality.
     A differing binder/opaque boundary uses the existing bounded decision. *)
  fun same (owner as Owner {graph,work,...}) left right =
    let val a = describe owner left val b = describe owner right
        val frame = #frame a
        val _ = if frame = #frame b then () else
          raise ERR "alpha" "different actual traversal frames"
    in W.with_step work (fn () =>
      let val memo = ref ([] : (G.node * G.node * bool) list)
          val held = ref ([] : G.closure_child list)
          fun tick () = (validate owner;W.spend work 1)
          fun lookup _ _ [] = NONE
            | lookup x y ((a,b,result)::rest) =
                (tick ();if x = a andalso y = b then SOME result
                 else lookup x y rest)
          fun compare x y =
            let val _ = tick ()
                val nx = G.closure_child_node graph frame x
                val ny = G.closure_child_node graph frame y
                val _ = held := x :: y :: !held
            in if nx = ny then true else
              case lookup nx ny (!memo) of SOME result => result | NONE =>
                let val result = if G.type_id graph nx <> G.type_id graph ny
                      then false else case (G.view graph nx,G.view graph ny) of
                      (G.Application _,G.Application _) =>
                        let val (xf,xx) =
                              G.closure_application_children graph frame x
                            val (yf,yx) =
                              G.closure_application_children graph frame y
                        in compare xf yf andalso compare xx yx end
                    | (G.Application _,_) => false
                    | (_,G.Application _) => false
                    | _ => SmtReplayOwnedAlpha.same_inside work
                        {caller = frame,traversal = frame,left = x,right = y}
                    val _ = tick ()
                    val _ = memo := (nx,ny,result) :: !memo
                in result end
            end
          val result = compare (#child a) (#child b)
          val _ = List.app (fn child =>
            (tick ();ignore (G.closure_child_node graph frame child))) (!held)
          val _ = ignore (describe owner left)
          val _ = ignore (describe owner right)
      in result end)
    end
  fun after original NONE = original
    | after _ (SOME (result : outcome)) = #target result
  fun repeat owner carrier original =
    let fun loop current accumulated = case probe owner carrier current of
            NONE => (current,accumulated)
          | SOME result =>
              loop (#target result)
                (join owner original accumulated (SOME result))
    in loop original NONE end
  fun top owner cache carrier original =
    let val data = describe owner original
        fun lookup [] = NONE
          | lookup ((node,frame,category,result)::rest) =
              (control owner;if node = #node data andalso frame = #frame data
                andalso category = #category data then SOME result
               else lookup rest)
    in case lookup (!cache) of SOME NONE => NONE
      | SOME (SOME (result : outcome)) => SOME
          {source = original,target = #target result,recipe = #recipe result,
           original_recipe = #original_recipe result,
           bounded = #bounded result,body_result = #body_result result}
      | NONE =>
        let val result = top_fresh owner cache carrier original
            val _ = control owner
            val _ = cache := (#node data,#frame data,#category data,result)
              :: !cache
        in result end
    end
  and top_fresh owner cache carrier original =
    let val _ = control owner
        val (middle,initial) = repeat owner carrier original
        val descent = descend owner cache carrier middle
    in case descent of NONE => initial | SOME changed =>
      if same owner middle (#target changed) then initial else
      let val prefix = join owner original initial (SOME changed)
          val target = #target changed
      in case probe owner carrier target of NONE => prefix | SOME retry =>
        let val prefix = join owner original prefix (SOME retry)
            val suffix = top owner cache carrier (#target retry)
        in join owner original prefix suffix end
      end end
  and descend (owner as Owner {graph,...}) cache carrier focus =
    let val _ = control owner val data = describe owner focus
        val frame = #frame data
    in case G.view graph (#node data) of
        G.Application _ =>
          let val (a,b) = D.application_children (#dynamic data)
              val (qa,qb) = Q.application_children (expected owner frame)
                (#admission data)
              val left = capture owner (auxiliary focus) frame (#receipt data) a qa
              val right = capture owner (auxiliary focus) frame (#receipt data) b qb
              (* The original right focus is used after the left finishes. *)
              val l = top owner cache carrier left
              val r = top owner cache carrier right
          in case (l,r) of (NONE,NONE) => NONE | _ =>
            let val lr = case l of NONE => identity owner left
                  | SOME result => #recipe result
                val rr = case r of NONE => identity owner right
                  | SOME result => #recipe result
                val recipe = in_action owner focus (fn observe =>
                  C.graph_application_fused graph frame
                    {source = #node data,left = lr,right = rr,
                     observe = observe})
                val converted = realize owner focus recipe
                val composed = in_action owner focus (fn observe =>
                  let val descriptor = C.graph_recipe_steps graph frame
                        {observe = observe} recipe
                      fun root [] = raise ERR "application"
                            "missing authentic root recipe frame"
                        | root ((row : C.recipe_step) :: rest) =
                            (observe ();
                             if #id row = #root descriptor then #kind row
                             else root rest)
                  in root (#steps descriptor) <> C.LegacyStep end)
            in SOME (if composed then close_application owner focus converted
              else converted) end
          end
      | G.AdmittedBinder _ =>
          let val body = D.binder_body (#dynamic data)
              val qb = Q.binder_body (expected owner frame) (#admission data)
              val Owner {work,...} = owner
              val body_receipt = Scope.body work
                (#receipt data) (#child data)
              val body_focus = capture owner (auxiliary focus) (D.scope body) body_receipt body qb
          in case top owner cache carrier body_focus of NONE => NONE
            | SOME result =>
              let val body_result = case #body_result result of
                    SOME proof => proof
                  | NONE => case #body_result (realize owner body_focus
                      (#recipe result)) of SOME proof => proof
                    | NONE => raise ERR "binder" "missing opaque Core body"
                  val plan = Lambda.prepare_admitted work
                    {frame = #receipt data,admission = #admission data,
                     body = body_result,ordinal = ordinal owner,
                     check_type = policy owner focus}
                  val receipt = Lambda.execute work plan
              in SOME (local_result owner focus
                (D.adopt_realized_lambda (#dynamic data) receipt)) end
          end
      | _ => NONE
    end
  fun raw_rebase (owner as Owner
      {graph,scope,work,limits,local_receipts,...}) focus semantic compact =
    let
      val dynamic = #dynamic (describe owner focus)
      val saved = D.root_sources dynamic
      val raw = #node (#original saved)
      val receipts = ref ([] : G.carrier_alpha list)
      val held = ref ([] : D.focus list)
      fun guard () =
        (ignore (describe owner focus);
         guard_app work (fn item => ignore (D.description_for
           (expected owner scope) item)) (!held);
         guard_app work (G.validate_carrier_alpha graph scope) (!receipts))
      val recipe = W.with_step work (fn () =>
        let
          val cap = #template_limit limits
          fun tick () = (guard ();W.spend work 1)
          fun allowance () =
            W.work_limit work - #charged (W.audit work)
          fun retain result =
            let val data = G.carrier_alpha_data graph scope result
                val _ = W.spend work (#visits data)
                val _ = receipts := result :: !receipts
            in data end
          val root_receipt = G.carrier_alpha_for graph scope (allowance ())
            {original = raw,source = #opened saved}
          val _ = ignore (retain root_receipt)
          fun plus a b = if a > cap orelse b > cap-a then
              raise ERR "raw_prefix" "bounded Alpha leaf exceeds template"
            else a+b
          fun type_size ty =
            (tick ();if Type.is_vartype ty then 1 else
              List.foldl (fn (ty,n) => plus n (type_size ty)) 1
                (#2 (Type.dest_type ty)))
          val types = ref ([] : Type.hol_type list)
          fun profile child =
            let val _ = tick ()
                val node = G.closure_child_node graph scope child
                val ty = G.type_of graph node val ann = type_size ty
                val _ = types := ty :: !types
            in case G.view graph node of G.Application _ =>
                  let val (f,x) = G.closure_application_children
                        graph scope child
                      val (ar,ai,aa) = profile f
                      val (br,bi,ba) = profile x
                  in (plus 1 (plus ar br),plus 1 (plus ai bi),
                    plus ann (plus aa ba)) end
              | G.AdmittedBinder _ =>
                  let val binder = G.closure_child_binder graph scope child
                      val data = G.binder_closure_data graph scope binder
                      val variable_type = G.type_of graph (#binder data)
                      val _ = types := variable_type :: !types
                      val variable_ann = type_size variable_type
                      val (r,i,a) = profile
                        (G.binder_closure_body graph scope binder)
                  in (plus 1 r,plus 2 i,plus ann (plus variable_ann a)) end
              | G.OpaqueRetained => raise ERR "raw_prefix"
                  "different opaque Alpha leaf lacks bounded closure"
              | _ => (1,1,ann)
            end
          fun equation (ar,ai,aa) (br,bi,ba) ty =
            (plus 3 (plus ar br),plus 3 (plus ai bi),
             plus 6 (plus (plus ty (plus ty ty)) (plus aa ba)))
          fun alpha_leaf raw rich
              (data : {original : G.node,source : G.source,
                       annotation : G.closure_child,visits : int}) converted =
            let val source_view = #source data
                val target_child = G.closure_root graph scope rich
                val _ = types := []
                val a = profile (#annotation data)
                val b = profile target_child
                val ty = type_size (G.type_of graph rich)
                (* Keep the original full raw/rich Alpha operand envelope,
                   even when the local semantic result is much smaller. *)
                val quotes = [equation a a ty,equation b b ty,
                  equation a b ty,equation a b ty]
                val _ = List.app (fn (_,i,a) =>
                  (W.spend work i;W.spend work a)) quotes
                val identity = G.plan_identity_closure_view graph scope cap
                  {target = target_child,retain = [#annotation data]}
                val _ = List.app (policy owner focus) (!types)
                val _ = guard ()
                val target_view = G.execute_identity_closure_view identity
                val _ = guard ()
                val theorem = case converted of NONE => #bridge source_view
                  | SOME leaf =>
                      let val described = D.conversion_description_for
                            (expected owner scope) leaf
                          val _ = if #source described = #node source_view
                              andalso #target described = rich then () else
                            raise ERR "raw_rebase" "different owned local leaf"
                          val _ = tick ()
                          val actual = D.endpoints leaf
                          val _ = guard () val _ = tick ()
                      in Thm.TRANS (#bridge source_view) (#theorem actual) end
                val _ = guard ()
                val converted = P.record_typed_conversion graph scope
                  {source = raw,source_view = source_view,target = rich,
                   target_view = target_view,theorem = theorem,
                   template_limit = cap,check_type = policy owner focus}
                val _ = guard ()
            in C.graph_leaf graph scope {conversion = converted,
              template_limit = cap,observe = tick} end
          (* These private searches are callback-free. Their caller has
             just guarded the portfolio; pay each probe without rescanning
             that entire portfolio for every immutable association link. *)
          fun lookup node [] = (W.spend work 1;NONE)
            | lookup node ((old,recipe)::rest) =
                (W.spend work 1;
                 if old = node then SOME recipe else lookup node rest)
          val memo = ref ([] : (G.node * C.graph_conversion) list)
          fun visit receipt current =
            let val _ = tick ()
                val data = G.carrier_alpha_data graph scope receipt
                val raw = #original data
                val rich = #node (D.description_for
                  (expected owner scope) current)
                val _ = held := current :: !held
                val _ = if #node (#source data) = rich then () else
                  raise ERR "raw_prefix" "different constructor correspondence"
            in case lookup raw (!memo) of SOME recipe => recipe | NONE =>
              let val result = if raw = rich then C.graph_identity graph scope
                    {observe = tick} raw else case G.view graph raw of
                    G.Application (f,x) =>
                      let val (a,b) = D.application_children current
                          val (left,right) =
                            G.carrier_alpha_application_children graph scope
                              (allowance ()) receipt
                          val ld = retain left val rd = retain right
                          val _ = if #original ld = f andalso #original rd = x
                              then () else raise ERR "raw_prefix"
                                "different private child recipes"
                          val l = visit left a val r = visit right b
                      in C.graph_application_fused graph scope
                        {source = raw,left = l,right = r,observe = tick} end
                  | _ =>
                      let val leaf = alpha_leaf raw rich data NONE
                          val projection = G.record_opened_type_projection
                            graph scope (allowance ()) receipt
                          val _ = W.spend work
                            (G.opened_type_projection_visits graph scope
                              projection)
                          val _ = guard ()
                      in leaf end
                  val _ = memo := (raw,result) :: !memo
              in result end
            end
          (* Fixed recipe/receipt correspondence precedes proof and policy.
             A slot is selected by exact private fact identity, never by a
             caller theorem/node or merely matching semantic endpoints. *)
          val {root,steps} = C.graph_recipe_steps graph scope
            {observe = tick} semantic
          fun row id [] =
                (W.spend work 1;
                 raise ERR "raw_rebase" "missing private recipe ID")
            | row id ((item : C.recipe_step)::rest) =
                (W.spend work 1;
                 if #id item = id then item else row id rest)
          fun leaf held [] = (W.spend work 1;NONE)
            | leaf held ((fact,converted)::rest) =
                (W.spend work 1;if Portable.pointer_eq (held,fact) then
                  SOME converted else leaf held rest)
          val planned = ref ([] : (int * G.node * raw_plan option) list)
          fun cached_plan id raw [] = (W.spend work 1;NONE)
            | cached_plan id raw ((old,node,answer)::rest) =
                (W.spend work 1;if old = id andalso node = raw then SOME answer
                 else cached_plan id raw rest)
          fun plan id alpha current =
            let val _ = tick ()
                val data = G.carrier_alpha_data graph scope alpha
                val node = #node (D.description_for
                  (expected owner scope) current)
                val _ = held := current :: !held
                val step = row id steps
                val _ = if #node (#source data) = node andalso
                    #source step = node then () else
                  raise ERR "raw_rebase" "different actual recipe source"
                fun children (a,b) =
                  let val (left,right) =
                        G.carrier_alpha_application_children graph scope
                          (allowance ()) alpha
                      val _ = ignore (retain left)
                      val _ = ignore (retain right)
                      val (f,x) = D.application_children current
                  in case (plan a left f,plan b right x) of
                      (SOME a,SOME b) =>
                        SOME (RawApplication (#original data,a,b))
                    | _ => NONE end
            in case cached_plan id (#original data) (!planned) of
                SOME answer => answer
              | NONE =>
                let val answer = if #kind step = C.SequenceRecipe orelse
                Option.isSome (#prefix step) orelse
                Option.isSome (#continuation step) then NONE
              else case (#closed step,#conversion step) of
                  (SOME fact,NONE) =>
                    if #kind step = C.LegacyStep andalso
                        #current step = #source step then
                      (case leaf fact (!local_receipts) of NONE => NONE
                       | SOME converted =>
                           let val described = D.conversion_description_for
                                 (expected owner scope) converted
                           in if #source described = node andalso
                               #target described = #result step then
                             SOME (RawClosed
                               (alpha,current,converted,#result step))
                             else raise ERR "raw_rebase"
                               "different same-result local witness" end)
                    else NONE
                | (NONE,NONE) =>
                    if #current step <> #result step then NONE else
                      (case #children step of SOME pair => children pair
                       | NONE => if #source step = #result step then
                           SOME (RawAlpha (alpha,current)) else NONE)
                | _ => NONE
                    val _ = planned :=
                      (id,#original data,answer) :: !planned
                in answer end
            end
          val assembled = ref ([] : (raw_plan * C.graph_conversion) list)
          fun cached_assembly item [] = (W.spend work 1;NONE)
            | cached_assembly item ((old,recipe)::rest) =
                (W.spend work 1;
                 if Portable.pointer_eq (item,old) then SOME recipe
                 else cached_assembly item rest)
          fun assemble item =
            let val _ = guard ()
            in case cached_assembly item (!assembled) of SOME recipe => recipe
              | NONE =>
                let val recipe = assemble_fresh item
                    val _ = assembled := (item,recipe) :: !assembled
                in recipe end
            end
          and assemble_fresh (RawAlpha (alpha,current)) = visit alpha current
            | assemble_fresh (RawApplication (source,a,b)) =
                let val left = assemble a val right = assemble b
                in C.graph_application_fused graph scope
                  {source = source,left = left,right = right,observe = tick} end
            | assemble_fresh (RawClosed (alpha,current,converted,target)) =
                let val _ = tick ()
                    val _ = G.carrier_alpha_source_for graph scope alpha
                    val _ = guard ()
                    val data = G.carrier_alpha_data graph scope alpha
                    val _ = ignore (D.description_for
                      (expected owner scope) current)
                in alpha_leaf (#original data) target data (SOME converted) end
          val result = case plan root root_receipt dynamic of
              SOME plan => RawReady (assemble plan)
            | NONE => RawPhases (visit root_receipt dynamic,compact)
          val _ = guard ()
        in result end)
      (* The raw Alpha prefix is closed on the original Root receipt. It
         is proof assembly only, never adopted as a forged D target focus. *)
      val result = case recipe of RawReady ready => ready
        | RawPhases (prefix,continuation) =>
          let val (first,_) = seal_program owner focus prefix
              val (second,_) = seal_program owner focus continuation
          in in_action owner focus (fn observe =>
            C.graph_realized_sequence work
              {first = first,second = second,observe = observe}) end
      val _ = C.validate_conversion_with_policy work result
      val _ = if C.graph_source result = raw andalso
          C.graph_result result = C.graph_result semantic then () else
        raise ERR "raw_rebase" "different exact raw/final endpoints"
      val _ = guard ()
    in (result,!receipts) end
  fun begin work {check_type,scope_opened} =
    let val sources = W.original_sources work
        val graph = S.owning_graph sources val scope = S.owning_scope sources
        val root_receipt = Scope.root work
        val callback_guard = ref (fn () =>
          W.validate work graph scope sources (W.semantic_limits work))
        fun checked_type ty =
          ((!callback_guard) ();check_type ty;(!callback_guard) ())
        val owner = Owner {marker = ref (),graph = graph,scope = scope,
          sources = sources,work = work,limits = W.semantic_limits work,
          epoch = Type.type_epoch (),symbols = Term.term_epoch (),
          laws = Laws.begin work {check_type = checked_type},next = ref 4,
          running = ref false,backing = ref [],validated = ref NONE,fence = ref 0,
          root_receipt = root_receipt,frames = ref [root_receipt],
          local_receipts = ref [],
          check_type = check_type,scope_opened = scope_opened}
        val _ = callback_guard := (fn () => validate owner)
    in validate owner;owner end
  fun perform (owner as Owner
      {work,scope,marker,running,graph,root_receipt,...}) goal
      occurrence view = protected owner (fn () =>
    (validate owner;if !running then raise ERR "run" "scheduler reentry"
      else running := true;
     case view of NONE => (running := false;NONE)
       | SOME _ =>
       let val dynamic = if goal then D.start_goal work {view = view}
             else D.start_assumption work {occurrence = occurrence,view = view}
           val admission = if goal then Q.initial_goal work {view = view}
             else Q.initial_assumption work
               {occurrence = occurrence,view = view}
           val original = capture owner NONE scope root_receipt dynamic admission
           val carrier_cache = ref []
           val carrier = top owner carrier_cache true original
           val middle = after original carrier
           (* Complete carrier phase precedes the first beta probe. *)
           val beta_cache = ref []
           val beta = top owner beta_cache false middle
           val complete = join owner original carrier beta
           val result = case complete of NONE => NONE | SOME converted =>
             if same owner original (#target converted) then NONE else
             let val (raw,receipts) = raw_rebase owner original
                   (#original_recipe converted) (#recipe converted)
             in SOME (Result {marker = marker,source = original,
               target = #target converted,recipe = #recipe converted,
               raw = raw,receipts = receipts}) end
           val _ = validate owner val _ = running := false
       in result end))
  fun run_assumption_owned owner {occurrence,view} =
    perform owner false occurrence view
  fun run_goal_owned owner {view} = perform owner true (~1) view
  (* Exact selected auxiliary entry. The fixed producer traversal completes
     before selecting changed/identity syntax. Both routes close by the SAME
     scoped Core and return a genuine D equality for the fixed continuation;
     no exception or unsupported branch is mapped to identity. *)
  fun run_aux_target_owned (owner as Owner
      {work,scope,marker,running,root_receipt,...}) {law} = protected owner (fn () =>
    let val _ = validate owner
        val _ = if !running then raise ERR "run_aux_owned" "scheduler reentry"
            else running := true
        val _ = Aux.validate_for (expected owner scope) law
        val dynamic = D.start_auxiliary work {law = law}
        val admission = Q.initial_auxiliary work {law = law}
        val original = capture owner (SOME law) scope root_receipt
          dynamic admission
        val carrier_cache = ref []
        val carrier = top owner carrier_cache true original
        val middle = after original carrier
        val beta_cache = ref []
        val beta = top owner beta_cache false middle
        val complete = join owner original carrier beta
        val (target,recipe) = case complete of NONE =>
              (original,identity owner original)
          | SOME changed => if same owner original (#target changed) then
              (original,identity owner original)
            else (#target changed,#recipe changed)
        val closed = realize owner original recipe
        val converted = case #bounded closed of SOME converted => converted
          | NONE => raise ERR "run_aux_owned" "missing owned D result"
        val description = D.conversion_description_for
          (expected owner scope) converted
        val law_data = Aux.describe_for (expected owner scope) law
        val _ = if #source description = #node (#opened law_data) andalso
            #target description = #node (describe owner target) then () else
          raise ERR "run_aux_owned" "different exact auxiliary result"
        val _ = validate owner
        val _ = Aux.validate_for (expected owner scope) law
        val _ = running := false
    in AuxTarget {owner=owner,marker=marker,original=original,
      target=target,law=law,converted=converted} end)
  fun run_aux_owned owner request =
    case run_aux_target_owned owner request of
      AuxTarget {converted,...} => converted
  (* Pure expected ownership precedes EVERY held getter. This is metadata,
     not an action frame, theorem pair, or a renewed allowance. *)
  fun aux_target_for expected_work
      (owner as Owner {work,marker,scope,...})
      (AuxTarget {marker=held,owner=held_owner,original,target,law,converted}) =
    ((if Portable.pointer_eq (expected_work,work) andalso
          Portable.pointer_eq (marker,held) andalso
          Portable.pointer_eq (owner,held_owner) then () else
        raise ERR "aux_target_for" "foreign expected Work or scheduler marker";
      protected owner (fn () =>
        let val _ = validate owner
            val origin = describe owner original
            val current = describe owner target
            val law_data = Aux.describe_for (expected owner scope) law
            val equality = D.conversion_description_for
              (expected owner scope) converted
            val _ = if #source equality= #node (#opened law_data) andalso
                #source equality= #node origin andalso
                #target equality= #node current then () else
              raise ERR "aux_target_for" "held auxiliary endpoint changed"
            val Focus {dynamic,admission,receipt,frame,...} = target
            val _ = if frame=scope then () else
              raise ERR "aux_target_for" "auxiliary target left original root"
            val _ = validate owner
        in {dynamic=dynamic,admission=admission,frame=receipt,conversion=converted} end))
     handle primary => (W.close expected_work;raise primary))

  (* Additive whole NUM handoff. The old perform/run APIs remain exact.
     The numeric consumer needs the actual original pair even when the
     carrier scan proved NONE; it must not reconstruct that pair later. *)
  fun perform_source_target (owner as Owner
      {work,scope,marker,running,root_receipt,sources,...})
      goal occurrence view =
    protected owner (fn () =>
    let val _ = validate owner
        val _ = if !running then raise ERR "run_source_target"
            "scheduler reentry" else running := true
        val dynamic = if goal then D.start_goal work {view=view}
          else D.start_assumption work {occurrence=occurrence,view=view}
        val admission = if goal then Q.initial_goal work {view=view}
          else Q.initial_assumption work {occurrence=occurrence,view=view}
        val original = capture owner NONE scope root_receipt
          dynamic admission
        val raw_source = #node (if goal then S.goal_source sources
          else List.nth (S.reconciliation_sources sources,occurrence))
        val (target,raw,receipts) = case view of NONE => (original,NONE,[])
          | SOME _ =>
            let val carrier = top owner (ref []) true original
                val middle = after original carrier
                val beta = top owner (ref []) false middle
                val complete = join owner original carrier beta
                val (target,history,recipe) = case complete of NONE =>
                      let val identity = identity owner original
                      in (original,identity,identity) end
                  | SOME converted =>
                      if same owner original (#target converted) then
                        let val identity = identity owner original
                        in (original,identity,identity) end
                      else (#target converted,#original_recipe converted,
                        #recipe converted)
                val (raw,receipts) = raw_rebase owner original history recipe
            in (target,SOME raw,receipts) end
        val _ = validate owner
        val _ = running := false
    in SourceTarget {owner=owner,marker=marker,original=original,
      target=target,raw_source=raw_source,raw=raw,receipts=receipts} end)
  fun run_assumption_target_owned owner {occurrence,view} =
    perform_source_target owner false occurrence view
  fun run_goal_target_owned owner {view} =
    perform_source_target owner true (~1) view
  fun source_target_for expected_work
      (owner as Owner {work,marker,graph,scope,...})
      (SourceTarget {owner=held_owner,marker=held,original,target,raw_source,
                     raw,receipts}) =
    ((if Portable.pointer_eq (expected_work,work) andalso
          Portable.pointer_eq (owner,held_owner) andalso
          Portable.pointer_eq (marker,held) then () else
        raise ERR "source_target_for" "foreign expected Work or owner";
      protected owner (fn () =>
        let val origin = describe owner original
            val current = describe owner target
            val _ = if #frame origin=scope andalso #frame current=scope
              then () else raise ERR "source_target_for"
                "source handoff left its authentic root frame"
            val _ = guard_app work
              (G.validate_carrier_alpha graph scope) receipts
            val _ = case raw of NONE =>
                  if #node origin= #node current andalso
                      #node origin=raw_source then () else
                    raise ERR "source_target_for" "missing changed prefix"
              | SOME prefix =>
                  (C.validate_conversion_with_policy work prefix;
                   if C.graph_source prefix=raw_source andalso
                       C.graph_result prefix= #node current then () else
                     raise ERR "source_target_for" "different actual target")
            val Focus {dynamic,admission,receipt,...} = target
            val _ = validate owner
        in {dynamic=dynamic,admission=admission,frame=receipt,raw=raw} end))
     handle primary => (W.close expected_work;raise primary))
  fun graph_conversion_for (owner as Owner {work,marker,graph,scope,...})
      (Result {marker = held,source,target,raw,receipts,...}) =
    protected owner (fn () =>
      (if Portable.pointer_eq (marker,held) then () else
         raise ERR "result" "different scheduler owner";
       validate owner;
       ignore (describe owner source);ignore (describe owner target);
       guard_app work (G.validate_carrier_alpha graph scope) receipts;raw))
  structure PolicyScheduler =
  struct
    structure NC=SmtReplayNativeContract
    structure RP=SmtReplayResourcePolicy
    datatype owner=Owner of
      {marker:unit ref,work:W.portfolio,graph:G.graph,root:G.scope,
       sources:S.sources,limits:RP.semantic_policy,contract:NC.contract,
       profiles:G.policy_opaque_profile list,frame:Scope.receipt,
       next:int ref,running:bool ref,epoch:int,symbols:int,
       backing:(unit -> unit) list ref,
       check_type:Type.hol_type -> unit,scope_opened:G.scope -> unit}
    datatype focus=Focus of
      {dynamic:D.policy_focus,admission:Q.policy_focus}
    datatype result=Result of
      {marker:unit ref,owner:owner,original:focus,target:focus,
       conversion:D.policy_conversion}

    fun protected work action=action () handle primary=>
      (W.close work;raise primary)
    fun active (Owner {work,graph,root,sources,limits,contract,frame,
        epoch,symbols,backing,...})=
      (NC.validate_for work contract;
       W.validate_policy work graph root sources limits;
       Scope.validate_lifetime_with_policy_for work frame;
       if Type.type_epoch ()=epoch andalso Term.term_epoch ()=symbols then
         guard_app work (fn guard=>guard ()) (!backing)
       else raise ERR "policy_scheduler" "retirement epoch changed")
    fun expected (Owner {work,graph,root,sources,...})=
      {graph=graph,scope=root,sources=sources,work=work}
    fun describe owner (Focus {dynamic,admission})=
      let val _=active owner val e=expected owner
          val d=D.description_with_policy_for e dynamic
          val q=Q.describe_with_policy_for e admission
          val generated=case #provenance d of D.GeneratedResult=>true
            | D.GeneratedDescendant=>true | _=>false
          val original=case #provenance d of D.OriginalOccurrence=>true
            | D.OriginalPositiveGoal=>true
            | D.UnopenedOriginalOccurrence=>true
            | D.UnopenedPositiveGoal=>true | _=>false
          val occurrence=case #occurrence d of SOME n=>n | NONE=> ~1
          val _=if #node d= #node q andalso occurrence= #occurrence q
              andalso ((generated andalso #category q=Q.Generated)
                orelse (original andalso #category q=Q.Original)) then ()
            else raise ERR "policy_scheduler" "different genuine focus pair"
      in {node= #node d,dynamic=dynamic,admission=admission} end
    fun ordinal (owner as Owner {work,next,...})=
      W.with_step work (fn()=>
        (active owner;W.spend_policy work 1;
         let val value= !next in next:=value+1;value end))
    fun validate_for expected_work (owner as Owner {work,...})=
      protected expected_work (fn()=>
        (if Portable.pointer_eq (expected_work,work) then () else
           raise ERR "policy_scheduler" "different original Work";
         active owner))
    fun begin work {native_contract,profiles,check_type,scope_opened}=
      protected work (fn()=>
        let val _=NC.validate_for work native_contract
            val sources=W.original_sources work
            val graph=S.owning_graph sources val root=S.owning_scope sources
            val limits=W.semantic_policy work
            val _=W.validate_policy work graph root sources limits
            val frame=Scope.root_with_policy work
            val owner=Owner {marker=ref (),work=work,graph=graph,root=root,
              sources=sources,limits=limits,contract=native_contract,
              profiles=profiles,frame=frame,next=ref 0,running=ref false,
              epoch=Type.type_epoch (),symbols=Term.term_epoch (),
              backing=ref [],check_type=check_type,scope_opened=scope_opened}
            val _=active owner
        in owner end)
    fun policy (owner as Owner {check_type,...}) focus ty=
      (ignore (describe owner focus);check_type ty;
       ignore (describe owner focus))
    fun observe (owner as Owner {scope_opened,...}) focus frame=
      (ignore (describe owner focus);scope_opened frame;
       ignore (describe owner focus))

    (* This first executable slice reduces actual ROOT redexes only. It
       does not claim carrier recognition, descent, or full normalization.
       The Beta producer independently validates/admit the genuine shape. *)
    fun probe (owner as Owner {work,graph,root,sources,contract,backing,...})
        focus=
      let val d=describe owner focus
          val beta=W.with_step work (fn()=>
            let val _=active owner val _=W.spend_policy work 1
                val result=case G.view graph (#node d) of
                    G.Application (operator,_)=>
                      (W.spend_policy work 1;
                       case G.view graph operator of
                         G.AdmittedBinder _=>true | _=>false)
                  | _=>false
                val _=active owner
            in result end)
      in if not beta then NONE else
        let val receipt=B.execute_with_policy
              (B.prepare_admitted_with_policy
                {graph=graph,scope=root,sources=sources,work=work,
                 ordinal=ordinal owner,admission= #admission d,
                 native_budget=contract,check_type=policy owner focus,
                 scope_opened=observe owner focus})
            val conversion=D.adopt_beta_with_policy (#dynamic d) receipt
            val guard=fn()=>ignore
              (D.conversion_description_with_policy_for
                (expected owner) conversion)
            val _=guard ()
            val _=backing:=guard:: !backing
            val fact=D.closed_fact_with_policy_for (expected owner)
              conversion {ordinal=ordinal owner,
                check_type=policy owner focus}
            val admission=Q.generated_with_policy (expected owner)
              (#admission d) fact
            val target=Focus
              {dynamic=D.target_focus_with_policy conversion,
               admission=admission}
            val _=ignore (describe owner target)
        in SOME (target,conversion) end
      end
    fun run owner original=
      let val Owner {work,marker,running,...}=owner
      in protected work (fn()=>
        let val _=active owner
            val _=if !running then raise ERR "policy_scheduler"
                "reentrant root traversal" else running:=true
            fun loop current saved=case probe owner current of NONE=>
                  Option.map (fn conversion=>Result
                    {marker=marker,owner=owner,original=original,
                     target=current,conversion=conversion}) saved
              | SOME (target,step)=>
                  let val combined=case saved of NONE=>step | SOME first=>
                        D.compose_with_policy
                          {first=first,second=step,ordinal=ordinal owner,
                           check_type=policy owner original}
                  in loop target (SOME combined) end
            val result=loop original NONE
            val _=active owner val _=running:=false
        in result end)
        handle primary=>(running:=false;W.close work;raise primary)
      end
    fun assumption (owner as Owner {work,contract,profiles,...})
        {occurrence,view}=
      protected work (fn()=>
        let val _=active owner
            val dynamic=D.start_assumption_with_policy work
              {occurrence=occurrence,view=view,native_contract=contract,
               profiles=profiles}
            val admission=Q.initial_assumption_with_policy work
              {occurrence=occurrence,view=view}
        in run owner (Focus {dynamic=dynamic,admission=admission}) end)
    fun goal (owner as Owner {work,contract,profiles,...}) {view}=
      protected work (fn()=>
        let val _=active owner
            val dynamic=D.start_goal_with_policy work
              {view=view,native_contract=contract,profiles=profiles}
            val admission=Q.initial_goal_with_policy work {view=view}
        in run owner (Focus {dynamic=dynamic,admission=admission}) end)
    (* Immutable result headers precede every paid owner guard, including
       callers that wrap this scheduler with an additional law owner. *)
    fun result_header_for expected_work (Owner {work,marker,...})
        (Result {marker=held,...})=
      protected expected_work (fn()=>
        (if Portable.pointer_eq (expected_work,work) then () else
           raise ERR "policy_scheduler" "different original Work";
         if marker=held then () else
           raise ERR "policy_scheduler" "different actual scheduler result"))
    fun result_for expected_work owner result=
      protected expected_work (fn()=>
        (result_header_for expected_work owner result;
         validate_for expected_work owner;
         let val Result {owner=saved,original,target,conversion,...}=result
             val _=active saved
             val _=ignore (describe saved original)
             val _=ignore (describe saved target)
             val _=ignore (D.conversion_description_with_policy_for
               (expected saved) conversion)
         in conversion end))
    fun source_for work owner result=
      let val conversion=result_for work owner result
          val Result {original,...}=result
      in D.source_conversion_with_policy conversion
        {ordinal=ordinal owner,check_type=policy owner original} end
    fun denial_for work owner result denial_view=
      let val conversion=result_for work owner result
          val Result {original,...}=result
      in D.denial_conversion_with_policy conversion
        {denial_view=denial_view,ordinal=ordinal owner,
         check_type=policy owner original} end
    fun target_for work owner result=
      let val conversion=result_for work owner result
      in #target (D.endpoints_with_policy conversion) end
  end
  type policy_owner=PolicyScheduler.owner
  type policy_result=PolicyScheduler.result
  val begin_with_policy=PolicyScheduler.begin
  val validate_with_policy_for=PolicyScheduler.validate_for
  val run_root_beta_assumption_with_policy=PolicyScheduler.assumption
  val run_root_beta_goal_with_policy=PolicyScheduler.goal
  val source_conversion_with_policy_for=PolicyScheduler.source_for
  val denial_conversion_with_policy_for=PolicyScheduler.denial_for
  val target_with_policy_for=PolicyScheduler.target_for
  (* Application descent keeps paired genuine D/Q paths. An abstraction
     which is not the operator of a beta redex remains unchanged here;
     descending its body requires the separate exact-body Lambda producer. *)
  structure RecursiveApplicationScheduler =
  struct
    structure PS=PolicyScheduler
    fun describe owner (PS.Focus {dynamic,admission})=
      let val _=PS.active owner val expected=PS.expected owner
          val d=D.description_with_policy_for expected dynamic
          val q=Q.describe_with_policy_for expected admission
          val category=case #provenance d of
              D.GeneratedResult=>Q.Generated
            | D.GeneratedDescendant=>Q.Generated
            | D.ClosedAuxiliaryRoot=>Q.Auxiliary
            | D.ClosedAuxiliaryDescendant=>Q.Auxiliary
            | _=>Q.Original
          val occurrence=case #occurrence d of SOME n=>n | NONE=> ~1
          val _=if #node d= #node q andalso occurrence= #occurrence q
              andalso category= #category q then () else
            raise ERR "recursive_beta" "different genuine child focus pair"
      in {node= #node d,provenance= #provenance d,
          dynamic=dynamic,admission=admission} end
    fun policy (owner as PS.Owner {check_type,...}) focus ty=
      (ignore (describe owner focus);check_type ty;
       ignore (describe owner focus))
    fun observe (owner as PS.Owner {scope_opened,...}) focus frame=
      (ignore (describe owner focus);scope_opened frame;
       ignore (describe owner focus))
    fun publish (owner as PS.Owner {backing,...}) parent conversion=
      let val d=describe owner parent
          fun guard ()=ignore (D.conversion_description_with_policy_for
            (PS.expected owner) conversion)
          val _=guard ()
          val _=backing:=guard:: !backing
          val fact=D.closed_fact_with_policy_for (PS.expected owner)
            conversion {ordinal=PS.ordinal owner,
              check_type=policy owner parent}
          val admission=Q.generated_with_policy (PS.expected owner)
            (#admission d) fact
          val target=PS.Focus
            {dynamic=D.target_focus_with_policy conversion,
             admission=admission}
          val _=ignore (describe owner target)
      in target end
    fun view (owner as PS.Owner {work,graph,...}) focus=
      W.with_step work (fn()=>
        let val d=describe owner focus val _=W.spend_policy work 1
            val result=G.view graph (#node d)
            val _=ignore (describe owner focus)
        in result end)
    fun beta (owner as PS.Owner
        {work,graph,root,sources,contract,...}) focus=
      let val d=describe owner focus
          val receipt=B.execute_with_policy
            (B.prepare_admitted_with_policy
              {graph=graph,scope=root,sources=sources,work=work,
               ordinal=PS.ordinal owner,admission= #admission d,
               native_budget=contract,check_type=policy owner focus,
               scope_opened=observe owner focus})
          val converted=D.adopt_beta_with_policy (#dynamic d) receipt
      in (publish owner focus converted,converted) end
    fun children owner focus=
      let val d=describe owner focus
          val (dl,dr)=D.application_children_with_policy (#dynamic d)
          val (ql,qr)=Q.application_children_with_policy
            (PS.expected owner) (#admission d)
          val left=PS.Focus {dynamic=dl,admission=ql}
          val right=PS.Focus {dynamic=dr,admission=qr}
          val _=ignore (describe owner left)
          val _=ignore (describe owner right)
      in (left,right) end

    fun run (owner as PS.Owner {work,graph,marker,running,...}) original=
      PS.protected work (fn()=>
      let val _=PS.active owner
          val _=if !running then raise ERR "recursive_beta"
              "reentrant traversal" else running:=true
          (* This cache belongs to ONE traversal of ONE original occurrence.
             Every lookup guards the actual paired paths. A hit is an
             immutable constructor result, never a Scope/lifetime waiver. *)
          val done=ref ([]:(G.node * D.provenance *
            (PS.focus * D.policy_conversion) option) list)
          fun saved node provenance []=NONE
            | saved node provenance ((held,kind,result)::rest)=
                (W.with_step work (fn()=>
                   (PS.active owner;W.spend_policy work 1));
                 if node=held andalso provenance=kind then SOME result
                 else saved node provenance rest)
          fun merge _ NONE next=next
            | merge initial (SOME first) (target,second)=
                (target,D.compose_with_policy
                  {first=first,second=second,ordinal=PS.ordinal owner,
                   check_type=policy owner initial})
          fun normalize focus=
            let val d=describe owner focus
            in case saved (#node d) (#provenance d) (!done) of
                SOME result=>
                  (case result of NONE=>NONE | SOME (target,conversion)=>
                     (ignore (describe owner target);
                      ignore (D.conversion_description_with_policy_for
                        (PS.expected owner) conversion);result))
              | NONE=>
                let val result=reduce focus NONE
                    val _=ignore (describe owner focus)
                    val _=W.with_step work (fn()=>
                      (PS.active owner;W.spend_policy work 1;
                       done:=(#node d,#provenance d,result):: !done))
                in result end
            end
          and reduce current accumulated=
            case view owner current of
              G.Application (operator,_)=>
                let val immediate=W.with_step work (fn()=>
                      (ignore (describe owner current);
                       W.spend_policy work 1;
                       case G.view graph operator of
                         G.AdmittedBinder _=>true | _=>false))
                in if immediate then
                    let val step=beta owner current
                        val combined=merge current accumulated step
                    in reduce (#1 step) (SOME (#2 combined)) end
                  else
                    let val (left,right)=children owner current
                        val lc=normalize left
                        val rc=normalize right
                    in case (lc,rc) of (NONE,NONE)=>
                         Option.map (fn proof=>(current,proof)) accumulated
                       | _=>
                         let val d=describe owner current
                             val plan=D.prepare_application_with_policy
                               {parent= #dynamic d,
                                left=Option.map #2 lc,
                                right=Option.map #2 rc,
                                ordinal=PS.ordinal owner,
                                check_type=policy owner current}
                             val converted=
                               D.execute_application_with_policy plan
                             val target=publish owner current converted
                             val combined=merge current accumulated
                               (target,converted)
                         in reduce target (SOME (#2 combined)) end
                    end
                end
            | _=>Option.map (fn proof=>(current,proof)) accumulated
          val final=normalize original
          val _=PS.active owner val _=running:=false
      in Option.map (fn (target,conversion)=>PS.Result
        {marker=marker,owner=owner,original=original,target=target,
         conversion=conversion}) final end)
      handle primary=>(running:=false;W.close work;raise primary)
    fun assumption (owner as PS.Owner {work,contract,profiles,...})
        {occurrence,view}=
      PS.protected work (fn()=>
        let val _=PS.active owner
            val dynamic=D.start_assumption_with_policy work
              {occurrence=occurrence,view=view,native_contract=contract,
               profiles=profiles}
            val admission=Q.initial_assumption_with_policy work
              {occurrence=occurrence,view=view}
        in run owner (PS.Focus {dynamic=dynamic,admission=admission}) end)
    fun goal (owner as PS.Owner {work,contract,profiles,...}) {view}=
      PS.protected work (fn()=>
        let val _=PS.active owner
            val dynamic=D.start_goal_with_policy work
              {view=view,native_contract=contract,profiles=profiles}
            val admission=Q.initial_goal_with_policy work {view=view}
        in run owner (PS.Focus {dynamic=dynamic,admission=admission}) end)
  end
  val run_recursive_application_beta_assumption_with_policy=
    RecursiveApplicationScheduler.assumption
  val run_recursive_application_beta_goal_with_policy=
    RecursiveApplicationScheduler.goal
  (* Every traversal frame is an actual root/body Scope receipt. Native
     Lambda lifting consumes the canonical equality of that SAME body. *)
  structure RecursiveScopedScheduler =
  struct
    structure PS=PolicyScheduler
    datatype focus=Focus of
      {dynamic:D.policy_focus,admission:Q.policy_focus,frame:Scope.receipt}
    (* This header guard must not call PS.active: published backing guards
       use it while PS.active is already walking that same backing list. *)
    fun expected (PS.Owner {work,graph,root,sources,contract,limits,...})
        (Focus {frame,...})=
      let val _=SmtReplayNativeContract.validate_for work contract
          val _=W.validate_policy work graph root sources limits
          val data=Scope.description_with_policy_for work frame
          val _=if Portable.pointer_eq(graph,#graph data) andalso
              root= #root data andalso
              Portable.pointer_eq(sources,#sources data) then () else
            raise ERR "scoped_beta" "different genuine Scope receipt"
      in {graph=graph,scope= #scope data,sources=sources,work=work} end
    fun describe owner (focus as Focus {dynamic,admission,...})=
      let val _=PS.active owner val e=expected owner focus
          val d=D.description_with_policy_for e dynamic
          val q=Q.describe_with_policy_for e admission
          val category=case #provenance d of
              D.GeneratedResult=>Q.Generated
            | D.GeneratedDescendant=>Q.Generated
            | D.ClosedAuxiliaryRoot=>Q.Auxiliary
            | D.ClosedAuxiliaryDescendant=>Q.Auxiliary
            | _=>Q.Original
          val occurrence=D.original_lineage_with_policy_for e dynamic
          val _=if #node d= #node q andalso occurrence= #occurrence q
              andalso category= #category q then () else
            raise ERR "recursive_beta" "different genuine child focus pair"
      in {node= #node d,scope= #scope e,provenance= #provenance d,
          dynamic=dynamic,admission=admission} end
    fun policy (owner as PS.Owner {check_type,...}) focus ty=
      (ignore (describe owner focus);check_type ty;
       ignore (describe owner focus))
    fun observe (owner as PS.Owner {scope_opened,...}) focus frame=
      (ignore (describe owner focus);scope_opened frame;
       ignore (describe owner focus))
    fun publish (owner as PS.Owner {backing,...}) parent conversion=
      let val d=describe owner parent
          val Focus {frame,...}=parent
          fun guard ()=ignore (D.conversion_description_with_policy_for
            (expected owner parent) conversion)
          val _=guard ()
          val _=backing:=guard:: !backing
          val fact=D.closed_generated_equality_with_policy_for
            (expected owner parent)
            conversion {ordinal=PS.ordinal owner,
              check_type=policy owner parent}
          val admission=Q.generated_scoped_with_policy (expected owner parent)
            (#admission d) fact
          val target=Focus
            {dynamic=D.target_focus_with_policy conversion,
             admission=admission,frame=frame}
          val _=ignore (describe owner target)
      in target end
    fun view (owner as PS.Owner {work,graph,...}) focus=
      W.with_step work (fn()=>
        let val d=describe owner focus val _=W.spend_policy work 1
            val result=G.view graph (#node d)
            val _=ignore (describe owner focus)
        in result end)
    fun beta (owner as PS.Owner
        {work,graph,root,sources,contract,...}) focus=
      let val d=describe owner focus
          val receipt=B.execute_with_policy
            (B.prepare_admitted_with_policy
              {graph=graph,scope= #scope d,sources=sources,work=work,
               ordinal=PS.ordinal owner,admission= #admission d,
               native_budget=contract,check_type=policy owner focus,
               scope_opened=observe owner focus})
          val converted=D.adopt_beta_with_policy (#dynamic d) receipt
      in (publish owner focus converted,converted) end
    fun children owner focus=
      let val d=describe owner focus
          val Focus {frame,...}=focus
          val (dl,dr)=D.application_children_with_policy (#dynamic d)
          val (ql,qr)=Q.application_children_with_policy
            (expected owner focus) (#admission d)
          val left=Focus {dynamic=dl,admission=ql,frame=frame}
          val right=Focus {dynamic=dr,admission=qr,frame=frame}
          val _=ignore (describe owner left)
          val _=ignore (describe owner right)
      in (left,right) end

    fun body (owner as PS.Owner {work,backing,...}) parent=
      let val d=describe owner parent
          val Focus {frame,...}=parent
          val child=D.child_with_policy (#dynamic d)
          val body_frame=Scope.body_with_policy work frame child
          fun guard ()=Scope.validate_lifetime_with_policy_for work body_frame
          val _=guard () val _=backing:=guard:: !backing
          val dynamic=D.binder_body_with_policy (#dynamic d)
          val admission=Q.binder_body_with_policy
            (expected owner parent) (#admission d)
          val result=Focus
            {dynamic=dynamic,admission=admission,frame=body_frame}
          val _=ignore(describe owner result)
      in result end

    fun run (owner as PS.Owner {work,graph,marker,running,...}) original=
      PS.protected work (fn()=>
      let val _=PS.active owner
          val _=if !running then raise ERR "recursive_beta"
              "reentrant traversal" else running:=true
          (* This cache belongs to ONE traversal of ONE original occurrence.
             Every lookup guards the actual paired paths. A hit is an
             immutable constructor result, never a Scope/lifetime waiver. *)
          val done=ref ([]:(G.node * G.scope * D.provenance *
            (focus * D.policy_conversion) option) list)
          fun saved node scope provenance []=NONE
            | saved node scope provenance ((held,frame,kind,result)::rest)=
                (W.with_step work (fn()=>
                   (PS.active owner;W.spend_policy work 1));
                 if node=held andalso scope=frame andalso provenance=kind
                   then SOME result
                 else saved node scope provenance rest)
          fun merge _ NONE next=next
            | merge initial (SOME first) (target,second)=
                (target,D.compose_with_policy
                  {first=first,second=second,ordinal=PS.ordinal owner,
                   check_type=policy owner initial})
          fun normalize focus=
            let val d=describe owner focus
            in case saved (#node d) (#scope d) (#provenance d) (!done) of
                SOME result=>
                  (case result of NONE=>NONE | SOME (target,conversion)=>
                     (ignore (describe owner target);
                      ignore (D.conversion_description_with_policy_for
                        (expected owner focus) conversion);result))
              | NONE=>
                let val result=reduce focus NONE
                    val _=ignore (describe owner focus)
                    val _=W.with_step work (fn()=>
                      (PS.active owner;W.spend_policy work 1;
                       done:=(#node d,#scope d,#provenance d,result):: !done))
                in result end
            end
          and reduce current accumulated=
            case view owner current of
              G.Application (operator,_)=>
                let val immediate=W.with_step work (fn()=>
                      (ignore (describe owner current);
                       W.spend_policy work 1;
                       case G.view graph operator of
                         G.AdmittedBinder _=>true | _=>false))
                in if immediate then
                    let val step=beta owner current
                        val combined=merge current accumulated step
                    in reduce (#1 step) (SOME (#2 combined)) end
                  else
                    let val (left,right)=children owner current
                        val lc=normalize left
                        val rc=normalize right
                    in case (lc,rc) of (NONE,NONE)=>
                         Option.map (fn proof=>(current,proof)) accumulated
                       | _=>
                         let val d=describe owner current
                             val plan=D.prepare_application_with_policy
                               {parent= #dynamic d,
                                left=Option.map #2 lc,
                                right=Option.map #2 rc,
                                ordinal=PS.ordinal owner,
                                check_type=policy owner current}
                             val converted=
                               D.execute_application_with_policy plan
                             val target=publish owner current converted
                             val combined=merge current accumulated
                               (target,converted)
                         in reduce target (SOME (#2 combined)) end
                    end
                end
            | G.AdmittedBinder _=>
                let val held=body owner current
                in case normalize held of NONE=>
                    Option.map (fn proof=>(current,proof)) accumulated
                  | SOME (_,body_conversion)=>
                      let val d=describe owner current
                          val converted=
                            D.lift_lambda_canonical_admitted_with_policy
                              {parent= #dynamic d,admission= #admission d,
                               body=body_conversion,
                               record_ordinal=PS.ordinal owner,
                               lift_ordinal=PS.ordinal owner,
                               check_type=policy owner current}
                          val target=publish owner current converted
                          val combined=merge current accumulated
                            (target,converted)
                      in reduce target (SOME (#2 combined)) end
                end
            | _=>Option.map (fn proof=>(current,proof)) accumulated
          val final=normalize original
          val _=PS.active owner val _=running:=false
          fun root_focus (value as Focus {dynamic,admission,...})=
            (ignore(PS.describe owner
               (PS.Focus {dynamic=dynamic,admission=admission}));
             PS.Focus {dynamic=dynamic,admission=admission})
      in Option.map (fn (target,conversion)=>PS.Result
        {marker=marker,owner=owner,original=root_focus original,
         target=root_focus target,conversion=conversion}) final end)
      handle primary=>(running:=false;W.close work;raise primary)
    fun assumption (owner as PS.Owner {work,contract,profiles,frame,...})
        {occurrence,view}=
      PS.protected work (fn()=>
        let val _=PS.active owner
            val dynamic=D.start_assumption_with_policy work
              {occurrence=occurrence,view=view,native_contract=contract,
               profiles=profiles}
            val admission=Q.initial_assumption_with_policy work
              {occurrence=occurrence,view=view}
        in run owner
          (Focus {dynamic=dynamic,admission=admission,frame=frame}) end)
    fun goal (owner as PS.Owner {work,contract,profiles,frame,...}) {view}=
      PS.protected work (fn()=>
        let val _=PS.active owner
            val dynamic=D.start_goal_with_policy work
              {view=view,native_contract=contract,profiles=profiles}
            val admission=Q.initial_goal_with_policy work {view=view}
        in run owner
          (Focus {dynamic=dynamic,admission=admission,frame=frame}) end)
  end
  val run_recursive_scope_beta_assumption_with_policy=
    RecursiveScopedScheduler.assumption
  val run_recursive_scope_beta_goal_with_policy=
    RecursiveScopedScheduler.goal
  (* Complete carrier traversal precedes the first beta probe, matching
     the finite scheduler. One invocation shares one lazy law owner. *)
  structure CarrierScopedScheduler =
  struct
    open RecursiveScopedScheduler
    structure RP=SmtReplayResourcePolicy
    datatype owner=Owner of
      {scheduler:PS.owner,laws:Laws.native_policy_owner}
    (* Structural decline before the one-attempt native producer. This is
       the finite recognizer's four actual fixed declarations, not a name
       spelling test or a whole Source-DAG acceptance cutoff. *)
    val all_id= #Name(Term.dest_thy_constid boolSyntax.universal)
    val exists_id= #Name(Term.dest_thy_constid boolSyntax.existential)
    val num_id= #Tyop(Type.dest_thy_typeid numSyntax.num)
    val fun_id= #Tyop(Type.dest_thy_typeid
      (Term.type_of boolSyntax.negation))
    fun carrier_kind (owner as PS.Owner
        {graph,work,contract,profiles,...}) focus operator=
      W.with_step work (fn()=>
      let val d=describe owner focus
          val e=expected owner focus
          val q=Q.describe_with_policy_for e (#admission d)
          val frame= #scope d
          val native=SmtReplayNativeContract.for_work work contract
          val limits= #semantic_limits native
          val native_cap=case #category q of Q.Original=> #input_limit limits
            | Q.Generated=> #output_limit limits
            | Q.Auxiliary=> #template_limit limits
          val captures=ref([]:G.profiled_metric list)
          fun guard ()=
            (ignore(describe owner focus);
             if Term.uptodate_term boolSyntax.universal andalso
                 Term.uptodate_term boolSyntax.existential andalso
                 Term.uptodate_term boolSyntax.negation andalso
                 Type.uptodate_type numSyntax.num then () else
               raise ERR "carrier_kind" "retired fixed root constructors";
             List.app(fn capture=>ignore
               (G.profiled_metric_data graph frame capture))(!captures))
          fun call operation=
            (guard();let val answer=operation()in guard();answer end)
          fun spend n=(guard();W.spend_policy work n;guard())
          fun same_id(a,b)=
            let val _=spend 1
                val na=KernelSig.name_of_id a
                val nb=KernelSig.name_of_id b
                fun bytes {Thy,Name}=IntInf.fromInt(String.size Thy)+
                  IntInf.fromInt(String.size Name)
                val amount=1+bytes na+bytes nb
                val _=spend amount
            in call(fn()=>KernelSig.id_compare(a,b))=EQUAL end
          fun view child=
            let val _=spend 1
                val node=call(fn()=>G.closure_child_node graph frame child)
            in (node,call(fn()=>G.view graph node))end
          fun number ty=
            (spend 1;if call(fn()=>Type.is_vartype ty)then false else
             let val {Tyop,Args,...}=call(fn()=>Type.dest_thy_typeid ty)
             in same_id(Tyop,num_id)andalso null Args end)
          fun carrier_type ty=
            if number ty then SOME true else
            (spend 1;if call(fn()=>Type.is_vartype ty)then NONE else
             let val {Tyop,Args,...}=call(fn()=>Type.dest_thy_typeid ty)
             in if same_id(Tyop,fun_id)then
                  (case Args of [_,range]=>
                     if number range then SOME false else NONE
                   | _=>raise ERR "carrier_kind"
                       "malformed function type metadata")
                else NONE end)
          fun predicate_domain child=
            let val(node,_)=view child
                val ty=call(fn()=>G.type_of graph node)
                val _=spend 1
                val _=if call(fn()=>Type.is_vartype ty)then
                    raise ERR "carrier_kind"
                      "quantifier predicate lacks function type" else ()
                val {Tyop,Args,...}=call(fn()=>Type.dest_thy_typeid ty)
            in if same_id(Tyop,fun_id)then
                 (case Args of [domain,_]=>domain
                  | _=>raise ERR "carrier_kind"
                    "malformed predicate function type")
               else raise ERR "carrier_kind"
                 "quantifier predicate is not a function" end
          fun applicable_input ()=
            let val _=spend 1
                val capture=call(fn()=>G.prepare_scoped_profiled_metric graph
                  frame {node= #node d,profiles=profiles})
                val data=call(fn()=>G.profiled_metric_data graph frame capture)
                val _=captures:=capture:: !captures
            in if #node data= #node d andalso
                #raw data<=IntInf.fromInt native_cap andalso
                #inc data<=IntInf.fromInt native_cap andalso
                RP.allows(#source_limit q)(#raw data)andalso
                RP.allows(#source_limit q)(#inc data)then () else
              raise ERR "carrier_kind" "applicable root exceeds original cap"
            end
          (* Preserve the finite recognizer's actual bounded Type portfolio
             and name quote before comparing the binder/domain Type ports. *)
          fun equal_domain left right=
            let val remaining=ref(#template_limit limits)
                val future=ref(0:IntInf.int)
                fun add n=future:= !future+IntInf.fromInt n
                fun quote pending=
                  (spend 1;case pending of []=>()|spine::more=>
                   (spend 1;case spine of []=>quote more|ty::rest=>
                    let val _=if !remaining>0 then remaining:= !remaining-1
                          else raise ERR "carrier_kind"
                            "binder type portfolio exceeds cap"
                        val _=spend 1 val _=add 2
                    in if call(fn()=>Type.is_vartype ty)then
                         let val name=call(fn()=>Type.dest_vartype ty)
                             val _=add(String.size name)val _=spend 1
                         in quote(rest::more)end
                       else let val {Tyop,Args,...}=call
                                  (fn()=>Type.dest_thy_typeid ty)
                                val {Thy,Name}=KernelSig.name_of_id Tyop
                                val _=add(String.size Thy)
                                val _=add(String.size Name)val _=spend 2
                            in quote(Args::rest::more)end end))
                val _=quote[[left,right]]
                val _=if !future<=IntInf.fromInt(#type_work_limit native)
                    then spend(!future) else
                  raise ERR "carrier_kind"
                    "binder type comparison exceeds Work"
            in call(fn()=>Type.compare(left,right))=EQUAL end
          fun quantify universal child=
            let val domain=predicate_domain child
            in case carrier_type domain of NONE=>NONE|SOME natural=>
              (case #2(view child)of
                 G.OpaqueRetained=>raise ERR "carrier_kind"
                   "applicable opaque binder requires recorded discovery"
               | G.AdmittedBinder _=>
                   let val _=applicable_input()
                       val closure=call
                         (fn()=>G.closure_child_binder graph frame child)
                       val data=call
                         (fn()=>G.binder_closure_data graph frame closure)
                       val ty=call(fn()=>G.type_of graph(#binder data))
                       val _=if equal_domain ty domain then ()else
                         raise ERR "carrier_kind" "binder differs from domain"
                   in SOME{natural=natural,universal=universal}end
               | _=>NONE)end
          val _=guard()
          val kind=case call(fn()=>G.view graph operator)of
              G.Constant id=>
                if same_id(id,all_id)then
                  quantify true (#2(call(fn()=>G.closure_application_children
                    graph frame (#child q))))
                else if same_id(id,exists_id)then
                  quantify false (#2(call(fn()=>G.closure_application_children
                    graph frame (#child q))))
                else NONE
            | G.OpaqueRetained=>raise ERR "carrier_kind"
                "applicable opaque operator requires recorded discovery"
            | _=>NONE
          val _=guard()
      in kind end)
    fun begin work {native_contract,profiles,check_type,scope_opened}=
      PS.protected work (fn()=>
      let val scheduler=PS.begin work
            {native_contract=native_contract,profiles=profiles,
             check_type=check_type,scope_opened=scope_opened}
          fun policy ty=(PS.active scheduler;check_type ty;PS.active scheduler)
          val laws=Laws.begin_native_with_policy work
            {native_contract=native_contract,check_type=policy}
          fun guard ()=Laws.validate_native_with_policy_for work laws
          val PS.Owner {backing,...}=scheduler
          val _=guard() val _=backing:=guard:: !backing
          val _=PS.active scheduler
      in Owner{scheduler=scheduler,laws=laws}end)
    fun for_work expected (Owner{scheduler,laws})=
      PS.protected expected (fn()=>
        (PS.validate_for expected scheduler;
         Laws.validate_native_with_policy_for expected laws;scheduler))
    fun validate_for expected held=ignore(for_work expected held)
    fun normalization_ordinal_for expected held=
      PS.ordinal(for_work expected held)
    fun carrier (owner as PS.Owner
        {work,graph,sources,contract,profiles,...}) laws focus operator=
      case carrier_kind owner focus operator of NONE=>NONE|SOME flags=>
        let val d=describe owner focus
            val law=Laws.get_native_with_policy_for work laws flags
            val _=ignore(describe owner focus)
            val receipt=Carrier.execute_profiled_with_policy
              (Carrier.prepare_closure_profiled_admitted_with_policy
                {graph=graph,scope= #scope d,sources=sources,work=work,
                 ordinal=PS.ordinal owner,admission= #admission d,law=law,
                 native_contract=contract,profiles=profiles,
                 check_type=policy owner focus,
                 scope_opened=observe owner focus})
            val converted=D.adopt_profiled_carrier_with_policy
              (#dynamic d) receipt
        in SOME(publish owner focus converted,converted)end
    (* Private traversal is called only while the producer owns the one
       running latch. Auxiliary identity and publication share that latch. *)
    fun traverse (Owner{scheduler=owner as PS.Owner
        {work,graph,running,...},laws}) original=
      let val _=PS.active owner
          val _=if !running then ()else raise ERR "carrier_scheduler"
            "private traversal lacks owned running latch"
          fun phase carrier_mode original=
          let
          (* This cache belongs to ONE traversal of ONE original occurrence.
             Every lookup guards the actual paired paths. A hit is an
             immutable constructor result, never a Scope/lifetime waiver. *)
          val done=ref ([]:(G.node * G.scope * D.provenance *
            (focus * D.policy_conversion) option) list)
          fun saved node scope provenance []=NONE
            | saved node scope provenance ((held,frame,kind,result)::rest)=
                (W.with_step work (fn()=>
                   (PS.active owner;W.spend_policy work 1));
                 if node=held andalso scope=frame andalso provenance=kind
                   then SOME result
                 else saved node scope provenance rest)
          fun merge _ NONE next=next
            | merge initial (SOME first) (target,second)=
                (target,D.compose_with_policy
                  {first=first,second=second,ordinal=PS.ordinal owner,
                   check_type=policy owner initial})
          fun normalize focus=
            let val d=describe owner focus
            in case saved (#node d) (#scope d) (#provenance d) (!done) of
                SOME result=>
                  (case result of NONE=>NONE | SOME (target,conversion)=>
                     (ignore (describe owner target);
                      ignore (D.conversion_description_with_policy_for
                        (expected owner focus) conversion);result))
              | NONE=>
                let val result=reduce focus NONE
                    val _=ignore (describe owner focus)
                    val _=W.with_step work (fn()=>
                      (PS.active owner;W.spend_policy work 1;
                       done:=(#node d,#scope d,#provenance d,result):: !done))
                in result end
            end
          and reduce current accumulated=
            case view owner current of
              G.Application (operator,_)=>
                let val step=if carrier_mode then
                      carrier owner laws current operator
                    else
                      let val immediate=W.with_step work (fn()=>
                            (ignore(describe owner current);
                             W.spend_policy work 1;
                             case G.view graph operator of
                               G.AdmittedBinder _=>true|_=>false))
                      in if immediate then SOME(beta owner current)
                         else NONE end
                in case step of SOME actual=>
                    let val combined=merge current accumulated actual
                    in reduce (#1 actual) (SOME (#2 combined)) end
                  | NONE=>
                    let val (left,right)=children owner current
                        val lc=normalize left
                        val rc=normalize right
                    in case (lc,rc) of (NONE,NONE)=>
                         Option.map (fn proof=>(current,proof)) accumulated
                       | _=>
                         let val d=describe owner current
                             val plan=D.prepare_application_with_policy
                               {parent= #dynamic d,
                                left=Option.map #2 lc,
                                right=Option.map #2 rc,
                                ordinal=PS.ordinal owner,
                                check_type=policy owner current}
                             val converted=
                               D.execute_application_with_policy plan
                             val target=publish owner current converted
                             val combined=merge current accumulated
                               (target,converted)
                         in reduce target (SOME (#2 combined)) end
                    end
                end
            | G.AdmittedBinder _=>
                let val held=body owner current
                in case normalize held of NONE=>
                    Option.map (fn proof=>(current,proof)) accumulated
                  | SOME (_,body_conversion)=>
                      let val d=describe owner current
                          val converted=
                            D.lift_lambda_canonical_admitted_with_policy
                              {parent= #dynamic d,admission= #admission d,
                               body=body_conversion,
                               record_ordinal=PS.ordinal owner,
                               lift_ordinal=PS.ordinal owner,
                               check_type=policy owner current}
                          val target=publish owner current converted
                          val combined=merge current accumulated
                            (target,converted)
                      in reduce target (SOME (#2 combined)) end
                end
            | _=>Option.map (fn proof=>(current,proof)) accumulated
          in normalize original end
          val carried=phase true original
          val middle=case carried of NONE=>original|SOME(target,_)=>target
          (* This fresh cache cannot confuse carrier and beta outcomes. *)
          val reduced=phase false middle
          val final=case(carried,reduced)of
              (NONE,result)=>result|(result,NONE)=>result
            | (SOME(_,first),SOME(target,second))=>
                SOME(target,D.compose_with_policy
                  {first=first,second=second,ordinal=PS.ordinal owner,
                   check_type=policy owner original})
          val _=PS.active owner
      in final end
    fun run (held as Owner{scheduler=owner as PS.Owner
        {work,marker,running,...},...}) original=
      PS.protected work (fn()=>
      let val _=PS.active owner
          val _=if !running then raise ERR "carrier_scheduler"
              "reentrant traversal" else running:=true
          val final=traverse held original
          fun root_focus(Focus{dynamic,admission,...})=
            (ignore(PS.describe owner
               (PS.Focus{dynamic=dynamic,admission=admission}));
             PS.Focus{dynamic=dynamic,admission=admission})
          val result=Option.map(fn(target,conversion)=>PS.Result
            {marker=marker,owner=owner,original=root_focus original,
             target=root_focus target,conversion=conversion})final
          val _=PS.active owner val _=running:=false
      in result end)
      handle primary=>(running:=false;W.close work;raise primary)
    fun assumption (held as Owner{scheduler=owner as PS.Owner
        {work,contract,profiles,frame,...},...}) {occurrence,view}=
      PS.protected work (fn()=>
      let val _=validate_for work held
          val dynamic=D.start_assumption_with_policy work
            {occurrence=occurrence,view=view,native_contract=contract,
             profiles=profiles}
          val admission=Q.initial_assumption_with_policy work
            {occurrence=occurrence,view=view}
      in run held (Focus{dynamic=dynamic,admission=admission,frame=frame})end)
    fun goal (held as Owner{scheduler=owner as PS.Owner
        {work,contract,profiles,frame,...},...}) {view}=
      PS.protected work (fn()=>
      let val _=validate_for work held
          val dynamic=D.start_goal_with_policy work
            {view=view,native_contract=contract,profiles=profiles}
          val admission=Q.initial_goal_with_policy work{view=view}
      in run held (Focus{dynamic=dynamic,admission=admission,frame=frame})end)
    fun result_owner_for work (owner as Owner{scheduler,...}) result=
      (PS.result_header_for work scheduler result;for_work work owner)
    fun source_for work owner result=
      PS.source_for work (result_owner_for work owner result) result
    fun denial_for work owner result view=
      PS.denial_for work (result_owner_for work owner result) result view
    fun target_for work owner result=
      PS.target_for work (result_owner_for work owner result) result
  end
  type policy_carrier_owner=CarrierScopedScheduler.owner
  val begin_carrier_with_policy=CarrierScopedScheduler.begin
  val validate_carrier_with_policy_for=CarrierScopedScheduler.validate_for
  val carrier_normalization_ordinal_with_policy_for=
    CarrierScopedScheduler.normalization_ordinal_for
  val run_carrier_assumption_with_policy=CarrierScopedScheduler.assumption
  val run_carrier_goal_with_policy=CarrierScopedScheduler.goal
  val carrier_source_conversion_with_policy_for=
    CarrierScopedScheduler.source_for
  val carrier_denial_conversion_with_policy_for=
    CarrierScopedScheduler.denial_for
  val carrier_target_with_policy_for=CarrierScopedScheduler.target_for
  (* Only a completed authentic selected-law traversal mints this lease.
     The actual root pair remains held even when no syntax changed. *)
  structure AuxiliaryCarrierScheduler =
  struct
    structure CS=CarrierScopedScheduler
    structure PS=PolicyScheduler
    structure RS=RecursiveScopedScheduler
    datatype target=Target of
      {owner:CS.owner,marker:unit ref,original:RS.focus,target:RS.focus,
       law:Aux.policy_receipt,conversion:D.policy_conversion}
    fun run (holder as CS.Owner{scheduler=base as PS.Owner
        {work,graph,root,sources,contract,profiles,frame,marker,running,
         backing,...},...}) {law}=
      PS.protected work (fn()=>
      let val _=CS.validate_for work holder
          val _=if !running then raise ERR "run_carrier_auxiliary"
              "scheduler reentry" else running:=true
          val expected={graph=graph,scope=root,sources=sources,work=work}
          val _=if Portable.pointer_eq(contract,
              Aux.native_contract_with_policy_for expected law)then ()else
            raise ERR "run_carrier_auxiliary"
              "different actual selected native contract"
          val dynamic=D.start_auxiliary_native_with_policy work
            {law=law,native_contract=contract,profiles=profiles}
          val admission=Q.initial_auxiliary_with_policy work {law=law}
          val original=RS.Focus
            {dynamic=dynamic,admission=admission,frame=frame}
          val origin=RS.describe base original
          val data=Aux.describe_with_policy_for expected law
          val _=if #node origin= #node(#opened data)then ()else
            raise ERR "run_carrier_auxiliary"
              "different actual selected law source"
          val completed=CS.traverse holder original
          val(target,conversion)=case completed of SOME actual=>actual|NONE=>
            (original,D.identity_auxiliary_with_policy_for expected dynamic
              {ordinal=PS.ordinal base,check_type=RS.policy base original})
          fun guard ()=
            (Aux.validate_with_policy_for expected law;
             ignore(D.conversion_description_with_policy_for expected
               conversion))
          val _=guard()val _=backing:=guard:: !backing
          val equality=D.conversion_description_with_policy_for expected
            conversion
          val current=RS.describe base target
          val _=if #source equality= #node origin andalso
              #target equality= #node current andalso #scope current=root
              then ()else raise ERR "run_carrier_auxiliary"
                "different actual auxiliary traversal endpoints"
          val _=CS.validate_for work holder
          val result=Target{owner=holder,marker=marker,original=original,
            target=target,law=law,conversion=conversion}
          val _=running:=false
      in result end)
      handle primary=>(running:=false;W.close work;raise primary)

    (* Compare only owner headers before activating any supplied lease. *)
    fun for_work expected holder
        (saved as Target{owner=held_owner,marker=held_marker,...})=
      ((let val CS.Owner{scheduler=PS.Owner{work,marker,...},...}=holder
            val _=if Portable.pointer_eq(expected,work)andalso
                Portable.pointer_eq(holder,held_owner)andalso
                Portable.pointer_eq(marker,held_marker)then ()else
              raise ERR "carrier_auxiliary_target_for"
                "foreign expected Work or scheduler marker"
            val _=CS.validate_for expected holder
            val CS.Owner{scheduler=base as PS.Owner
              {graph,root,sources,contract,...},...}=holder
            val expectation=
              {graph=graph,scope=root,sources=sources,work=expected}
            val Target{original,target,law,conversion,...}=saved
            val _=if Portable.pointer_eq(contract,
                Aux.native_contract_with_policy_for expectation law)then ()else
              raise ERR "carrier_auxiliary_target_for"
                "different actual selected native contract"
            val data=Aux.describe_with_policy_for expectation law
            val origin=RS.describe base original
            val current=RS.describe base target
            val equality=D.conversion_description_with_policy_for expectation
              conversion
            val _=if #source equality= #node(#opened data)andalso
                #source equality= #node origin andalso
                #target equality= #node current andalso #scope current=root
                then ()else raise ERR "carrier_auxiliary_target_for"
                  "held auxiliary endpoint changed"
            val RS.Focus{dynamic,admission,frame}=target
            val actual=Scope.description_with_policy_for expected frame
            val _=if #scope actual=root then ()else
              raise ERR "carrier_auxiliary_target_for"
                "auxiliary target left original root frame"
            val _=CS.validate_for expected holder
        in {dynamic=dynamic,admission=admission,frame=frame,
            conversion=conversion}end)
       handle primary=>(W.close expected;raise primary))
  end
  type policy_carrier_aux_target=AuxiliaryCarrierScheduler.target
  val run_carrier_aux_target_with_policy=AuxiliaryCarrierScheduler.run
  val carrier_aux_target_with_policy_for=AuxiliaryCarrierScheduler.for_work
  (* Actual owner header first. Equal numeric contracts cannot substitute
     for this scheduler's retained token or renew its shared ordinal. *)
  fun native_contract_carrier_with_policy_for expected held=
    let val actual=CarrierScopedScheduler.for_work expected held
        val PolicyScheduler.Owner{contract,...}=actual
    in contract end
  val _=SmtReplayProof.closed_fact_cut_with_policy_for
  val _=SmtReplayOwnedTransport.adopt_core_with_policy_for
  structure PolicySourceCarrierTraversal=
  struct
    structure PS=PolicyScheduler
    structure RS=RecursiveScopedScheduler
    structure CS=CarrierScopedScheduler
    type outcome={target:RS.focus,recipe:C.graph_conversion,
      converted:D.policy_conversion option}
    fun action(owner as PS.Owner{work,...})focus operation=
      W.with_step work(fn()=>
        let fun observe()=
              (ignore(RS.describe owner focus);W.spend_policy work 1)
            val answer=operation observe
            val _=ignore(RS.describe owner focus)
        in answer end)
    fun recipe_guard(owner as PS.Owner{work,...})source
        ({target,recipe,converted}:outcome)=
      let val original=RS.describe owner source
          val current=RS.describe owner target
          val _=C.validate_conversion_with_policy work recipe
          val _=Option.app(fn value=>ignore
            (D.conversion_description_with_policy_for
              (RS.expected owner source)value))converted
      in if C.graph_source recipe= #node original andalso
          C.graph_result recipe= #node current andalso
          #scope original= #scope current then ()else
        raise ERR "policy_source_carrier" "different actual recipe endpoints"
      end
    fun identity(owner as PS.Owner{graph,...})focus=
      let val data=RS.describe owner focus
      in action owner focus(fn observe=>C.graph_identity graph(#scope data)
        {observe=observe}(#node data))end
    (* A local native producer has already admitted its actual operation.
       Reuse ONE scoped fact for both Q publication and its typed cut. *)
    fun local_result(owner as PS.Owner{work,graph,limits,backing,...})
        source converted=
      let val data=RS.describe owner source
          val RS.Focus{frame,...}=source
          val expected_request=RS.expected owner source
          fun guard()=ignore(D.conversion_description_with_policy_for
            (RS.expected owner source)converted)
          val _=guard()
          val generated=D.closed_generated_equality_with_policy_for
            expected_request converted{ordinal=PS.ordinal owner,
              check_type=RS.policy owner source}
          val same=P.scoped_generated_equality_for graph(#scope data)
            (#template_limit limits)generated
          val cut=P.closed_fact_cut_with_policy_for work
            {frame=frame,fact= #fact same}
          val recipe=action owner source(fn observe=>
            C.graph_closed_fact_cut_with_policy work{cut=cut,observe=observe})
          val admission=Q.generated_scoped_with_policy expected_request
            (#admission data)generated
          val target=RS.Focus{dynamic=D.target_focus_with_policy converted,
            admission=admission,frame=frame}
          val result={target=target,recipe=recipe,
            converted=SOME converted}:outcome
          val _=backing:=guard:: !backing
          val _=recipe_guard owner source result
      in result end
    (* Compact Core, not a D whole-parent MK_COMB reservation, publishes a
       semantic parent focus when traversal needs to inspect it again. *)
    fun realize(owner as PS.Owner
        {work,contract,profiles,backing,...})source recipe=
      let val RS.Focus{frame,...}=source
          val initial_data=RS.describe owner source
          val _=C.validate_conversion_with_policy work recipe
          val _=if C.graph_source recipe= #node initial_data then ()else
            raise ERR "policy_source_carrier" "different Core source"
          val result=Core.execute_with_policy work
            (Core.prepare_in_scope_with_policy work
              {frame=frame,conversion=recipe,ordinal=PS.ordinal owner,
               native_contract=contract,profiles=profiles,
               check_type=RS.policy owner source})
          fun guard()=ignore
            (Core.conversion_description_with_policy_for work result)
          val _=guard()
          val wrapper=action owner source(fn observe=>
            (observe();P.policy_source_realization_generated_equality_for
              work(Core.realization_with_policy_for work result)
              {profiles=profiles}))
          val admission=Q.generated_scoped_with_policy
            (RS.expected owner source)(#admission initial_data)wrapper
          val converted=D.adopt_core_with_policy_for
            (RS.expected owner source)(#dynamic initial_data)result
          val target=RS.Focus{dynamic=D.target_focus_with_policy converted,
            admission=admission,frame=frame}
          val closed=action owner source(fn observe=>
            C.graph_realized_leaf_with_policy work
              {realization=Core.realization_with_policy_for work result,
               observe=observe})
          val answer={target=target,recipe=closed,
            converted=SOME converted}:outcome
          val _=backing:=guard:: !backing
          val _=recipe_guard owner source answer
      in (answer,converted)end
    fun join(owner as PS.Owner{work,...})source
        (first:outcome)(second:outcome)=
      let val _=ignore(RS.describe owner source)
          val _=recipe_guard owner source first
          val _=recipe_guard owner(#target first)second
          val recipe=action owner source(fn observe=>
            C.graph_cut_sequence_with_policy work
              {first= #recipe first,second= #recipe second,observe=observe})
          val result={target= #target second,recipe=recipe,
            converted=NONE}:outcome
          val _=recipe_guard owner source result
      in result end
    fun carrier(owner as PS.Owner
        {work,graph,sources,contract,profiles,...})laws focus operator=
      case CS.carrier_kind owner focus operator of NONE=>NONE|SOME flags=>
        let val data=RS.describe owner focus
            val law=Laws.get_native_with_policy_for work laws flags
            val _=ignore(RS.describe owner focus)
            val receipt=Carrier.execute_profiled_with_policy
              (Carrier.prepare_closure_profiled_admitted_with_policy
                {graph=graph,scope= #scope data,sources=sources,work=work,
                 ordinal=PS.ordinal owner,admission= #admission data,law=law,
                 native_contract=contract,profiles=profiles,
                 check_type=RS.policy owner focus,
                 scope_opened=RS.observe owner focus})
            val converted=D.adopt_profiled_carrier_with_policy
              (#dynamic data)receipt
        in SOME(local_result owner focus converted)end
    fun beta(owner as PS.Owner
        {work,graph,sources,contract,...})focus=
      let val data=RS.describe owner focus
          val receipt=B.execute_with_policy(B.prepare_admitted_with_policy
            {graph=graph,scope= #scope data,sources=sources,work=work,
             ordinal=PS.ordinal owner,admission= #admission data,
             native_budget=contract,check_type=RS.policy owner focus,
             scope_opened=RS.observe owner focus})
          val converted=D.adopt_beta_with_policy(#dynamic data)receipt
      in local_result owner focus converted end
    (* Caller owns the SAME scheduler running latch across initial pairing,
       this traversal and final SourceTarget publication. *)
    fun traverse(CS.Owner{scheduler=owner as PS.Owner
        {work,graph,running,...},laws})original=
      let val _=PS.active owner
          val _=if !running then ()else
            raise ERR "policy_source_carrier" "missing owned running latch"
          fun phase carrier_mode initial=
            let
              val memo=ref([]:(G.node*G.scope*D.provenance*
                outcome option)list)
              fun saved _ _ _ []=NONE
                | saved node scope provenance((n,s,p,result)::rest)=
                    (action owner initial(fn observe=>observe());
                     if node=n andalso scope=s andalso provenance=p then
                       SOME result else saved node scope provenance rest)
              fun merge source NONE next=next
                | merge source(SOME previous)next=
                    join owner source previous next
              fun normalize focus=
                let val data=RS.describe owner focus
                in case saved(#node data)(#scope data)(#provenance data)
                    (!memo)of SOME result=>
                      (Option.app(recipe_guard owner focus)result;result)
                  | NONE=>
                    let val result=reduce focus focus NONE
                        val _=ignore(RS.describe owner focus)
                        val _=action owner focus(fn observe=>
                          (observe();memo:=(#node data,#scope data,
                            #provenance data,result):: !memo))
                    in result end
                end
              and reduce start current accumulated=
                case RS.view owner current of
                  G.Application(operator,_)=>
                    let val step=if carrier_mode then
                          carrier owner laws current operator else
                          let val immediate=action owner current
                                (fn observe=>(observe();
                                  case G.view graph operator of
                                    G.AdmittedBinder _=>true|_=>false))
                          in if immediate then SOME(beta owner current)
                             else NONE end
                    in case step of SOME actual=>
                        let val combined=merge start accumulated actual
                        in reduce start(#target actual)(SOME combined)end
                      | NONE=>
                        let val(left,right)=RS.children owner current
                            val lc=normalize left val rc=normalize right
                        in case(lc,rc)of(NONE,NONE)=>accumulated | _=>
                          let val data=RS.describe owner current
                              val l=case lc of NONE=>identity owner left
                                | SOME result=> #recipe result
                              val r=case rc of NONE=>identity owner right
                                | SOME result=> #recipe result
                              val recipe=action owner current(fn observe=>
                                C.graph_application graph(#scope data)
                                  {source= #node data,left=l,right=r,
                                   observe=observe})
                              val(actual,_)=realize owner current recipe
                              val combined=merge start accumulated actual
                          in reduce start(#target actual)(SOME combined)end
                        end
                    end
                | G.AdmittedBinder _=>
                    let val body=RS.body owner current
                    in case normalize body of NONE=>accumulated
                      | SOME result=>
                        let val body_conversion=case #converted result of
                                SOME actual=>actual
                              | NONE=> #2(realize owner body(#recipe result))
                            val data=RS.describe owner current
                            val converted=
                              D.lift_lambda_canonical_admitted_with_policy
                                {parent= #dynamic data,
                                 admission= #admission data,
                                 body=body_conversion,
                                 record_ordinal=PS.ordinal owner,
                                 lift_ordinal=PS.ordinal owner,
                                 check_type=RS.policy owner current}
                            val actual=local_result owner current converted
                            val combined=merge start accumulated actual
                        in reduce start(#target actual)(SOME combined)end
                    end
                | _=>accumulated
            in normalize initial end
          val carried=phase true original
          val middle=case carried of NONE=>original
            | SOME result=> #target result
          (* A fresh cache preserves carrier-complete then whole-beta order. *)
          val reduced=phase false middle
          val result=case(carried,reduced)of(NONE,answer)=>answer
            | (answer,NONE)=>answer
            | (SOME first,SOME second)=>SOME(join owner original first second)
          val _=Option.app(recipe_guard owner original)result
          val _=PS.active owner
      in result end
  end

  (* The raw Source prefix remains the SAME genuine saved discovery. The
     suffix below starts at its actual view, not at a caller raw node. *)
  structure PolicyMetadataSourceTarget=
  struct
    structure MT=PolicySourceCarrierTraversal
    structure CS=CarrierScopedScheduler
    structure PS=PolicyScheduler
    structure RS=RecursiveScopedScheduler
    datatype target=Target of
      {owner:CS.owner,marker:unit ref,original:RS.focus,
       partial:G.policy_partial_discovery,alpha:G.carrier_alpha option,
       result:MT.outcome option}
    fun source_same(left:G.source)(right:G.source)=
      #node left= #node right andalso
      Portable.pointer_eq(#original left,#original right)andalso
      Portable.pointer_eq(#bridge left,#bridge right)
    (* Retained backing must not recurse through PS.active/RS.describe. *)
    fun guard_partial(owner as PS.Owner{graph,root,...})
        (focus as RS.Focus{dynamic,...})partial alpha=
      let val expected_request=RS.expected owner focus
          val ports=D.root_sources_with_policy_for
            expected_request dynamic
          val _=if #scope expected_request=root then ()else
            raise ERR "metadata_source_target" "not actual root frame"
          val actual=G.partial_source_header_with_policy graph root partial
          val _=if #original actual= #node(#original ports)then ()else
            raise ERR "metadata_source_target" "different original Source"
          val _=case(#view actual,#view ports)of(NONE,NONE)=>()
            | (SOME left,SOME right)=>
                if source_same left right then ()else
                  raise ERR "metadata_source_target" "different actual view"
            | _=>raise ERR "metadata_source_target" "different view option"
          val _=case alpha of NONE=>
                (case #view actual of NONE=>()|SOME _=>
                   raise ERR "metadata_source_target"
                     "missing genuine saved alpha recipe")
            | SOME held=>
                let val saved=G.carrier_alpha_data graph root held
                    val view=case #view actual of SOME value=>value
                      | NONE=>raise ERR "metadata_source_target"
                          "unexpected saved alpha recipe"
                in if #original saved= #original actual andalso
                    source_same(#source saved)view then ()else
                  raise ERR "metadata_source_target"
                    "different saved alpha Source"end
      in ports end
    fun run expected holder goal occurrence partial=
      PS.protected expected(fn()=>
      let val CS.Owner{scheduler=base as PS.Owner
            {work,graph,root,contract,profiles,frame,marker,running,
             backing,...},...}=holder
          val _=if Portable.pointer_eq(expected,work)then ()else
            raise ERR "metadata_source_target" "different original Work"
          val _=CS.validate_for expected holder
          val _=if !running then raise ERR "metadata_source_target"
              "scheduler reentry"else running:=true
          fun finish()=
            let val header=G.partial_source_header_with_policy
                  graph root partial
                val alpha=G.carrier_alpha_from_partial_with_policy
                  graph root partial
                val dynamic=if goal then D.start_goal_with_policy work
                    {view= #view header,native_contract=contract,
                     profiles=profiles}
                  else D.start_assumption_with_policy work
                    {occurrence=occurrence,view= #view header,
                     native_contract=contract,profiles=profiles}
                val admission=if goal then
                    Q.initial_goal_with_policy work{view= #view header}
                  else Q.initial_assumption_with_policy work
                    {occurrence=occurrence,view= #view header}
                val original=RS.Focus
                  {dynamic=dynamic,admission=admission,frame=frame}
                fun guard()=ignore
                  (guard_partial base original partial alpha)
                val _=guard()
                val result=MT.traverse holder original
                val _=Option.app(MT.recipe_guard base original)result
                val target=case result of NONE=>original
                  | SOME actual=> #target actual
                val current=RS.describe base target
                val _=if #scope current=root then ()else
                  raise ERR "metadata_source_target"
                    "target left actual root frame"
                val _=guard()
                val _=backing:=guard:: !backing
                val _=CS.validate_for expected holder
            in Target{owner=holder,marker=marker,original=original,
                partial=partial,alpha=alpha,result=result}end
          val answer=(finish()handle primary=>
            (running:=false;raise primary))
          val _=running:=false
      in answer end)
    fun assumption expected holder{occurrence,partial}=
      run expected holder false occurrence partial
    fun goal expected holder{partial}=run expected holder true (~1) partial
    fun for_work expected holder
        (Target{owner=held_owner,marker=held,original,partial,alpha,result})=
      PS.protected expected(fn()=>
      let val CS.Owner{scheduler=base as PS.Owner
            {work,root,marker,...},...}=holder
          val _=if Portable.pointer_eq(expected,work)andalso
              Portable.pointer_eq(holder,held_owner)andalso
              Portable.pointer_eq(marker,held)then ()else
            raise ERR "metadata_source_target_for"
              "foreign expected Work or scheduler marker"
          val _=CS.validate_for expected holder
          val ports=guard_partial base original partial alpha
          val _=Option.app(MT.recipe_guard base original)result
          val target=case result of NONE=>original
            | SOME actual=> #target actual
          val current=RS.describe base target
          val RS.Focus{dynamic,admission,frame}=target
          val actual=Scope.description_with_policy_for expected frame
          val _=if #scope current=root andalso #scope actual=root then ()else
            raise ERR "metadata_source_target_for"
              "source target left original root frame"
      in {dynamic=dynamic,admission=admission,frame=frame,
          original= #original ports,view= #view ports,
          partial=partial,alpha=alpha,
          suffix=Option.map #recipe result,
          conversion=case result of NONE=>NONE
            | SOME value=> #converted value}end)
  end
  type policy_metadata_source_target=PolicyMetadataSourceTarget.target
  val run_carrier_assumption_metadata_with_policy=
    PolicyMetadataSourceTarget.assumption
  val run_carrier_goal_metadata_with_policy=PolicyMetadataSourceTarget.goal
  val carrier_metadata_source_target_with_policy_for=
    PolicyMetadataSourceTarget.for_work

  val _=SmtReplayProof.prepare_alpha_leaf_with_policy
  val _=SmtReplayProof.execute_alpha_leaf_with_policy
  val _=SmtReplayGraph.alpha_metric_data_with_policy
  val _=SmtReplayProof.policy_source_realization_closed_fact_for
  structure PolicyCompleteSourceTarget=
  struct
    structure PS=PolicyScheduler
    structure RS=RecursiveScopedScheduler
    structure CS=CarrierScopedScheduler
    structure ST=PolicyMetadataSourceTarget
    type part={alpha:G.carrier_alpha,source:G.node,target:G.node,
      bridge:Thm.thm,recipe:C.graph_conversion option}
    datatype target=Complete of
      {owner:CS.owner,marker:unit ref,metadata:ST.target,
       source:G.node,target:G.node,recipe:C.graph_conversion option,
       guard:unit -> unit}
    fun complete expected holder
        (metadata as ST.Target{owner=held_owner,marker=held,original,
          partial,alpha,result})=
      PS.protected expected(fn()=>
      let
        val CS.Owner{scheduler=base as PS.Owner
          {work,graph,root,sources,contract,profiles,frame,marker,running,
           backing,...},...}=holder
        val _=if Portable.pointer_eq(expected,work)andalso
            Portable.pointer_eq(holder,held_owner)andalso
            Portable.pointer_eq(marker,held)then ()else
          raise ERR "complete_source_target" "foreign Work or scheduler"
        val _=CS.validate_for expected holder
        val _=if !running then raise ERR "complete_source_target"
            "scheduler reentry"else running:=true
        fun finish()=
          let
            val paths=ref([]:G.carrier_alpha list)
            val recipes=ref([]:C.graph_conversion list)
            val memo=ref([]:part list)
            fun guard()=
              ((SmtReplayNativeContract.validate_for work contract;
                ignore(ST.guard_partial base original partial alpha);
                guard_app work(fn saved=>ignore
                  (G.carrier_alpha_data graph root saved))(!paths);
                guard_app work
                  (C.validate_conversion_with_policy work)(!recipes))
               handle primary=>(W.close work;raise primary))
            fun action operation=W.with_step work(fn()=>
              let fun observe()=(guard();W.spend_policy work 1)
                  val _=guard()
                  val answer=operation observe
                  val _=guard()
              in answer end)
            fun keep converted=
              (C.validate_conversion_with_policy work converted;
               recipes:=converted:: !recipes;converted)
            fun tick()=action(fn observe=>observe())
            (* Close only this actual immediate application on compact names.
               Child proofs enter as genuine cut leaves, not re-INSTed
               expanded theorems. The receipt/fact/cut retain real lifetimes. *)
            fun close_application recipe=
              let
                val source=C.graph_source recipe
                val target=C.graph_result recipe
                val _=guard()
                val result=Core.execute_with_policy work
                  (Core.prepare_in_scope_with_policy work
                    {frame=frame,conversion=recipe,ordinal=PS.ordinal base,
                     native_contract=contract,profiles=profiles,
                     check_type=RS.policy base original})
                val _=guard()
                val actual=Core.conversion_description_with_policy_for
                  work result
                val native=Core.native_contract_with_policy_for work result
                val _=if Portable.pointer_eq(native,contract)andalso
                    Portable.pointer_eq(#graph actual,graph)andalso
                    Portable.pointer_eq(#sources actual,sources)andalso
                    #root actual=root andalso #scope actual=root andalso
                    #source actual=source andalso #target actual=target
                  then ()else raise ERR "source_alpha_prefix"
                    "different actual compact application result"
                val fact=P.policy_source_realization_closed_fact_for work
                  (Core.realization_with_policy_for work result)
                val cut=P.closed_fact_cut_with_policy_for work
                  {frame=frame,fact=fact}
                val closed=action(fn observe=>keep
                  (C.graph_closed_fact_cut_with_policy work
                    {cut=cut,observe=observe}))
                val _=guard()
              in closed end
            fun checked (data:{original:G.node,source:G.source,
                  annotation:G.closure_child,visits:int}) recipe=
              let val source= #original data val target= #node(#source data)
                  val _=case recipe of NONE=>
                        if source=target then ()else
                          raise ERR "source_alpha_prefix"
                            "nonidentity prefix lacks actual recipe"
                    | SOME converted=>
                        (C.validate_conversion_with_policy work converted;
                         if C.graph_source converted=source andalso
                             C.graph_result converted=target then ()else
                           raise ERR "source_alpha_prefix"
                             "actual saved alpha endpoints differ")
              in recipe end
            fun lookup (data:{original:G.node,source:G.source,
                  annotation:G.closure_child,visits:int}) []=(tick();NONE)
              | lookup data((saved:part)::rest)=
                  (tick();if #source saved= #original data andalso
                      #target saved= #node(#source data)andalso
                      Portable.pointer_eq(#bridge saved,
                        #bridge(#source data))then
                    (ignore(G.carrier_alpha_data graph root(#alpha saved));
                     SOME(checked data(#recipe saved)))
                   else lookup data rest)
            fun build saved=
              let
                val _=guard()
                val _=tick()
                val data=G.carrier_alpha_data graph root saved
                (* Keep each incoming genuine path before a completed hit.
                   All visits use this one actual requester/root frame. *)
                val _=paths:=saved:: !paths
                val answer=case lookup data(!memo)of SOME cached=>cached
                  | NONE=>
                    let
                      val source= #original data
                      val target= #node(#source data)
                      val converted=if source=target then NONE else
                        case G.view graph source of
                          G.Application _=>
                            let
                              val(left,right)=
                                G.carrier_alpha_application_children_with_policy
                                  graph root saved
                              val l=build left val r=build right
                              fun child actual NONE=
                                    let val incoming=
                                          G.carrier_alpha_data graph root actual
                                    in action(fn observe=>keep
                                      (C.graph_identity graph root
                                        {observe=observe}(#original incoming)))
                                    end
                                | child actual(SOME recipe)=
                                    let val incoming=
                                          G.carrier_alpha_data graph root actual
                                    in case checked incoming(SOME recipe)of
                                        SOME value=>value
                                      | NONE=>raise Fail "missing child recipe"
                                    end
                              val a=child left l val b=child right r
                              val recipe=action(fn observe=>keep
                                (C.graph_application graph root
                                  {source=source,left=a,right=b,
                                   observe=observe}))
                            in SOME(close_application recipe)end
                        | G.OpaqueRetained=>
                            let
                              val _=case G.view graph target of
                                  G.AdmittedBinder _=>()
                                | _=>raise ERR "source_alpha_prefix"
                                    "changed opaque leaf is not opened binder"
                              (* This captures existing rich graph DATA and
                                 retained authentic profiles. It performs no
                                 raw opening or new profile acquisition. *)
                              val capture=action(fn observe=>
                                (observe();G.prepare_scoped_profiled_metric
                                  graph root{node=target,profiles=profiles}))
                              val _=ignore(G.alpha_metric_data_with_policy
                                graph root saved capture)
                              val plan=P.prepare_alpha_leaf_with_policy work
                                {frame=frame,alpha=saved,capture=capture,
                                 native_contract=contract,
                                 check_type=RS.policy base original}
                              val fact=P.execute_alpha_leaf_with_policy
                                work plan
                              val _=guard()
                              val cut=P.closed_fact_cut_with_policy_for work
                                {frame=frame,fact=fact}
                              val recipe=action(fn observe=>keep
                                (C.graph_closed_fact_cut_with_policy work
                                  {cut=cut,observe=observe}))
                            in SOME recipe end
                        | _=>raise ERR "source_alpha_prefix"
                            "changed leaf lacks supported saved Alpha producer"
                      val converted=checked data converted
                      val _=tick()
                      val _=memo:={alpha=saved,source=source,target=target,
                        bridge= #bridge(#source data),recipe=converted}:: !memo
                      val _=guard()
                    in converted end
                val _=guard()
              in checked data answer end
            val ports=ST.guard_partial base original partial alpha
            val source= #node(#original ports)
            val view=case #view ports of NONE=>source
              | SOME value=> #node value
            val prefix=case alpha of NONE=>
                  if source=view then NONE else
                    raise ERR "source_alpha_prefix" "missing saved Alpha"
              | SOME saved=>build saved
            val _=case prefix of NONE=>
                  if source=view then ()else raise ERR "source_alpha_prefix"
                    "actual Source/view identity differs"
              | SOME recipe=>if C.graph_source recipe=source andalso
                    C.graph_result recipe=view then ()else
                  raise ERR "source_alpha_prefix" "Source prefix join differs"
            val suffix=Option.map #recipe result
            val recipe=case(prefix,suffix)of(NONE,NONE)=>NONE
              | (SOME actual,NONE)=>SOME actual
              | (NONE,SOME actual)=>SOME actual
              | (SOME first,SOME second)=>SOME(action(fn observe=>keep
                  (C.graph_cut_sequence_with_policy work
                    {first=first,second=second,observe=observe})))
            val target=case recipe of NONE=>source
              | SOME actual=>C.graph_result actual
            val _=Option.app(fn actual=>
              if C.graph_source actual=source then ()else
                raise ERR "source_alpha_prefix" "not original Source")recipe
            val current=case result of NONE=>original
              | SOME actual=> #target actual
            val actual=RS.describe base current
            val _=if #scope actual=root andalso #node actual=target then ()else
              raise ERR "source_alpha_prefix" "different actual final target"
            val _=guard()
            val _=backing:=guard:: !backing
            val _=CS.validate_for expected holder
          in Complete{owner=holder,marker=marker,metadata=metadata,
            source=source,target=target,recipe=recipe,guard=guard}end
        val answer=(finish()handle primary=>(running:=false;raise primary))
        val _=running:=false
      in answer end)
    fun for_work expected holder
        (Complete{owner=held_owner,marker=held,metadata,source,target,
          recipe,guard})=
      PS.protected expected(fn()=>
      let
        val CS.Owner{scheduler=PS.Owner{work,graph,root,sources,marker,...},
          ...}=holder
        val _=if Portable.pointer_eq(expected,work)andalso
            Portable.pointer_eq(holder,held_owner)andalso
            Portable.pointer_eq(marker,held)then ()else
          raise ERR "complete_source_target_for" "foreign Work or scheduler"
        val _=CS.validate_for expected holder
        val _=guard()
        val actual=ST.for_work expected holder metadata
        val data=D.description_with_policy_for
          {work=work,graph=graph,scope=root,sources=sources}(#dynamic actual)
        val _=if #node(#original actual)=source andalso #node data=target
            andalso #scope data=root then ()else
          raise ERR "complete_source_target_for" "actual Source target changed"
        val _=guard()
      in {dynamic= #dynamic actual,admission= #admission actual,
        frame= #frame actual,original= #original actual,view= #view actual,
        source=source,target=target,recipe=recipe}end)
  end
  type policy_complete_source_target=PolicyCompleteSourceTarget.target
  val complete_carrier_metadata_source_target_with_policy=
    PolicyCompleteSourceTarget.complete
  val carrier_complete_source_target_with_policy_for=
    PolicyCompleteSourceTarget.for_work

end
