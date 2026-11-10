(* Canonical owned carrier traversal followed by the complete beta stage.
   Unequal-cap and whole-stage resource/cost qualification remain open. *)
structure SmtLib_OwnedCarrierTraversal :> SmtLib_OwnedCarrierTraversal =
struct
  structure G = SmtReplayGraph
  structure S = SmtReplaySource
  structure W = SmtReplayInvocationWork
  structure F = SmtReplayFocusAdmission
  structure D = SmtReplayOwnedTransport
  structure R = SmtLib_TraversalRootRecognition
  structure B = SmtReplayRecordedBeta
  structure C = SmtLib_GraphCarrierRoot
  structure Laws = SmtLib_CarrierLaws
  val ERR = Feedback.mk_HOL_ERR "SmtLib_OwnedCarrierTraversal"
  val _ = SmtReplayFocusAdmission.initial
  val _ = SmtReplayOwnedTransport.lift_lambda_admitted
  val _ = SmtReplayOwnedTransport.start
  val _ = SmtLib_TraversalRootRecognition.inspect
  val _ = SmtLib_CarrierLaws.begin
  val _ = SmtLib_GraphCarrierRoot.prepare_closure
  val _ = SmtLib_CarrierTopDepthFn.loaded

  structure T =
  struct
    datatype owner = Owner of
      {marker : unit ref,graph : G.graph,root : G.scope,
       sources : S.sources,work : W.portfolio,limits : W.limits,
       epoch : int,laws : Laws.owner,next : int ref,running : bool ref,
       check_type : Type.hol_type -> unit,
       scope_opened : G.scope -> unit}
    datatype origin = SourceRoot | UnopenedSourceRoot
                    | OpenedPositiveRoot | UnopenedPositiveRoot
    datatype focus = Focus of
      {marker : unit ref,dynamic : D.focus,admission : F.focus,
       node : G.node,traversal : G.scope,origin : origin}
    datatype conversion = Conversion of
      {marker : unit ref,dynamic : D.conversion,initial : focus,target : focus}
    datatype shape = Atomic | Application of focus * focus | Binder of focus

    fun retire (Owner {work,...}) = W.close work
    fun protected owner action =
      action () handle primary => (retire owner;raise primary)
    fun validate_owner (owner as Owner
        {graph,root,sources,work,limits,epoch,laws,...}) =
      protected owner (fn () =>
        (W.validate work graph root sources limits;
         Laws.validate laws;
         if Type.type_epoch () = epoch then () else
           raise ERR "owner" "Type retirement epoch changed"))
    fun expected (Owner {graph,sources,work,...}) traversal =
      {graph = graph,scope = traversal,sources = sources,work = work}
    (* Expected marker/lower owner precede all dynamic D activation. The
       cached frame comes only from this private paired construction. *)
    fun describe_focus (owner as Owner {marker,...})
        (Focus {marker = held,dynamic,admission,node,traversal,origin}) =
      protected owner (fn () =>
        let val _ = validate_owner owner
            val _ = if Portable.pointer_eq (marker,held) then () else
              raise ERR "focus" "different traversal owner"
            val data = F.describe_for (expected owner traversal) admission
            val _ = if #node data = node then () else
              raise ERR "focus" "different lower canonical node"
            val description = D.description_for
              (expected owner traversal) dynamic
            val _ = if #node description = node andalso
                #scope description = traversal then () else
              raise ERR "focus" "different exact dynamic node/frame"
            val slot = case origin of SourceRoot =>
                #occurrence description = SOME (#occurrence data)
              | UnopenedSourceRoot =>
                #occurrence description = SOME (#occurrence data)
              | _ => #occurrence description = NONE andalso
                  #occurrence data = ~1
            val _ = if slot then () else
              raise ERR "focus" "different Source/positive Goal occurrence"
            val matching = case
                (origin,#provenance description,#category data) of
                (SourceRoot,D.OriginalOccurrence,F.Original) => true
              | (UnopenedSourceRoot,D.UnopenedOriginalOccurrence,F.Original) =>
                  true
              | (UnopenedSourceRoot,D.UnopenedOriginalDescendant,F.Original) =>
                  true
              | (SourceRoot,D.OriginalDescendant,F.Original) => true
              | (OpenedPositiveRoot,D.OriginalPositiveGoal,F.Original) => true
              | (OpenedPositiveRoot,D.PositiveGoalDescendant,F.Original) => true
              | (UnopenedPositiveRoot,D.UnopenedPositiveGoal,F.Original) => true
              | (UnopenedPositiveRoot,D.UnopenedGoalDescendant,F.Original) => true
              | (SourceRoot,D.GeneratedResult,F.Generated) => true
              | (SourceRoot,D.GeneratedDescendant,F.Generated) => true
              | (OpenedPositiveRoot,D.GeneratedResult,F.Generated) => true
              | (OpenedPositiveRoot,D.GeneratedDescendant,F.Generated) => true
              | _ => false
            val _ = if matching then () else
              raise ERR "focus" "different original/generated provenance"
        in {dynamic = dynamic,admission = admission,node = node,
            traversal = traversal,origin = origin} end)
    fun unwrap_focus owner focus = #dynamic (describe_focus owner focus)
    fun scope_of owner (focus as Focus {traversal,...}) =
      (ignore (unwrap_focus owner focus);traversal)
    fun admission_of owner (focus as Focus {admission,...}) =
      (ignore (unwrap_focus owner focus);admission)
    fun capture (owner as Owner {marker,...}) origin traversal dynamic admission =
      protected owner (fn () =>
        let val _ = validate_owner owner
            val data = F.describe_for (expected owner traversal) admission
            val result = Focus {marker = marker,dynamic = dynamic,
              admission = admission,node = #node data,traversal = traversal,
              origin = origin}
        in ignore (unwrap_focus owner result);result end)
    fun origin_of owner (focus as Focus {origin,...}) =
      (ignore (unwrap_focus owner focus);origin)
    fun unopened owner focus = case origin_of owner focus of
        UnopenedPositiveRoot => true | UnopenedSourceRoot => true
      | _ => false
    fun validate_focus owner focus =
      protected owner (fn () => ignore (unwrap_focus owner focus))
    fun unwrap_conversion (owner as Owner {marker,...})
        (Conversion {marker = held,dynamic,initial,target}) =
      protected owner (fn () =>
        let val _ = validate_owner owner
            val _ = if Portable.pointer_eq (marker,held) then () else
              raise ERR "conversion" "different traversal owner"
            val first = describe_focus owner initial
            val last = describe_focus owner target
            val description = D.conversion_description_for
              (expected owner (#traversal first)) dynamic
        in if #source description = #node first andalso
            #target description = #node last andalso
            #scope description = #traversal first andalso
            #traversal first = #traversal last then dynamic else
          raise ERR "conversion" "different paired endpoints/frame" end)
    fun invoke owner focus action = protected owner (fn () =>
      (validate_focus owner focus;
       let val result = action ()
       in validate_focus owner focus;result end))
    fun policy owner focus ty =
      let val Owner {check_type,...} = owner
      in invoke owner focus (fn () => check_type ty) end
    fun observer owner focus scope =
      let val Owner {scope_opened,...} = owner
      in invoke owner focus (fn () => scope_opened scope) end
    fun control (owner as Owner {work,...}) = W.with_step work (fn () =>
      (validate_owner owner;W.spend work 1;validate_owner owner))
    fun ordinal (owner as Owner {work,next,...}) =
      W.with_step work (fn () =>
        (validate_owner owner;W.spend work 1;
         let val value = !next
             val _ = next := value+1
         in value end))
    (* This wrapper owns each generated receipt: semantic equality proof
       is quoted/debited now, then F.generated uses a separate SAME W action.
       There is no externally supplied theorem/receipt or renewed allowance. *)
    fun wrap_conversion (owner as Owner {marker,...}) initial converted =
      protected owner (fn () =>
        let val first = describe_focus owner initial
            val traversal = #traversal first
            val admission = #admission first
            val description = D.conversion_description_for
              (expected owner traversal) converted
            val _ = if #source description = #node first then () else
              raise ERR "wrap" "different owned source"
            fun guard () =
              (validate_focus owner initial;
               ignore (D.conversion_description_for
                 (expected owner traversal) converted))
            fun check ty = (guard ();policy owner initial ty;guard ())
            val fact = D.closed_fact converted
              {ordinal = ordinal owner,check_type = check}
            val _ = guard ()
            val generated = F.generated (expected owner traversal) admission fact
            val _ = guard ()
            val target = capture owner (origin_of owner initial) traversal
              (D.target_focus converted)
              generated
            val result = Conversion {marker = marker,dynamic = converted,
              initial = initial,target = target}
        in ignore (unwrap_conversion owner result);result end)
    fun view owner focus = invoke owner focus (fn () =>
      let val {dynamic = current,admission,node,traversal,origin} =
            describe_focus owner focus
          val Owner {graph,...} = owner
      in if origin = UnopenedPositiveRoot orelse
          origin = UnopenedSourceRoot then Atomic else
        case G.view graph node of
          G.Application _ =>
            let val (left,right) = D.application_children current
                val (a,b) = F.application_children
                  (expected owner traversal) admission
            in Application (capture owner origin traversal left a,
                            capture owner origin traversal right b) end
        | G.AdmittedBinder _ =>
            let val closure = G.closure_child_binder graph traversal
                  (#child (F.describe_for (expected owner traversal) admission))
                val data = G.binder_closure_data graph traversal closure
                val dynamic = D.binder_body current
                val lower = F.binder_body (expected owner traversal) admission
            in Binder (capture owner origin
              (#body_frame data) dynamic lower) end
        | _ => Atomic
      end)
    fun request (owner as Owner {graph,sources,work,...}) focus =
      let val description = describe_focus owner focus
          val scope = #traversal description
          val admission = #admission description
      in {graph = graph,scope = scope,sources = sources,
          work = work,admission = admission} end
    fun inspect owner focus = invoke owner focus (fn () =>
      let val admitted = request owner focus
          val probe = R.inspect_admitted admitted
          val {graph,scope,sources,work,admission} = admitted
          val data = F.describe_for (expected owner scope) admission
          val _ = R.validate_for
            {graph = graph,scope = scope,sources = sources,work = work,
             focus = #child data} probe
      in probe end)
    fun beta owner focus = if unopened owner focus then NONE else
      let val probe = inspect owner focus
      in if not (R.beta probe) then NONE else invoke owner focus (fn () =>
        let val Owner {graph,sources,work,check_type,scope_opened,...} = owner
            val current = unwrap_focus owner focus
            val result = B.execute (B.prepare_admitted
              {graph = graph,scope = D.scope current,sources = sources,
               work = work,ordinal = ordinal owner,
               admission = admission_of owner focus,
               check_type = policy owner focus,
               scope_opened = observer owner focus})
        in SOME (wrap_conversion owner focus (D.adopt_beta current result)) end)
      end
    fun carrier owner focus = if unopened owner focus then NONE else
      let val probe = inspect owner focus
      in case R.carrier probe of NONE => NONE
        | SOME kind => invoke owner focus (fn () =>
          let
            val Owner {graph,sources,work,laws,check_type,
                       scope_opened,...} = owner
            val current = unwrap_focus owner focus
            val traversal = D.scope current
            val flags = case kind of
                R.NumForall => {natural = true,universal = true}
              | R.NumExists => {natural = true,universal = false}
              | R.BagForall => {natural = false,universal = true}
              | R.BagExists => {natural = false,universal = false}
            val law = Laws.get laws flags
            val result = C.execute (C.prepare_closure_admitted
              {graph = graph,scope = traversal,sources = sources,work = work,
               ordinal = ordinal owner,
               admission = admission_of owner focus,law = law,
               check_type = policy owner focus,
               scope_opened = observer owner focus})
          in SOME (wrap_conversion owner focus (D.adopt_carrier current result)) end)
      end
    fun validate_conversion owner focus conversion =
      invoke owner focus (fn () =>
        let val current = unwrap_focus owner focus
            val converted = unwrap_conversion owner conversion
        in if #source (D.endpoints converted) = D.node current then () else
          raise ERR "conversion" "different exact source occurrence" end)
    fun target owner (conversion as Conversion {target,...}) =
      protected owner (fn () =>
        (ignore (unwrap_conversion owner conversion);
         validate_focus owner target;target))
    fun compose owner (first as Conversion {initial,...}) second =
      protected owner (fn () =>
        let val a = unwrap_conversion owner first
            val b = unwrap_conversion owner second
        in wrap_conversion owner initial (D.compose
          {first = a,second = b,ordinal = ordinal owner,
           check_type = policy owner initial}) end)
    fun lift_application owner focus (left,right) =
      invoke owner focus (fn () =>
        let val parent = unwrap_focus owner focus
            val a = Option.map (unwrap_conversion owner) left
            val b = Option.map (unwrap_conversion owner) right
        in wrap_conversion owner focus (D.execute_application
          (D.prepare_application
            {parent = parent,left = a,right = b,ordinal = ordinal owner,
             check_type = policy owner focus})) end)
    fun lift_binder owner focus body =
      invoke owner focus (fn () =>
        let val parent = unwrap_focus owner focus
            val converted = unwrap_conversion owner body
            val record_ordinal = ordinal owner
            val lift_ordinal = ordinal owner
        in wrap_conversion owner focus (D.lift_lambda_admitted
          {parent = parent,admission = admission_of owner focus,
           body = converted,record_ordinal = record_ordinal,
           lift_ordinal = lift_ordinal,check_type = policy owner focus}) end)
    fun alpha_changed owner focus conversion =
      (validate_conversion owner focus conversion;
       invoke owner focus (fn () =>
         D.alpha_changed_admitted
           {conversion = unwrap_conversion owner conversion,
            admission = admission_of owner focus}))
  end

  structure Traverse = SmtLib_CarrierTopDepthFn (T)
  type owner = T.owner
  fun begin work {check_type,scope_opened} =
    let val sources = W.original_sources work
        val graph = S.owning_graph sources
        val root = S.owning_scope sources
        val owner = T.Owner
          {marker = ref (),graph = graph,root = root,sources = sources,
           work = work,limits = W.semantic_limits work,
           epoch = Type.type_epoch (),laws = Laws.begin work
             {check_type = check_type},next = ref 4,running = ref false,
           check_type = check_type,scope_opened = scope_opened}
    in T.validate_owner owner;owner end
  type result = T.conversion
  fun perform (owner as T.Owner {work,running,...}) {occurrence,view} finish =
    T.protected owner (fn () =>
      (T.validate_owner owner;
       if !running then raise ERR "run" "traversal reentry" else ();
       running := true;
       let val dynamic = D.start work {occurrence = occurrence,view = view}
           val lower = F.initial work {occurrence = occurrence,view = view}
           val T.Owner {root,...} = owner
           val focus = T.capture owner T.SourceRoot root dynamic lower
           val session = Traverse.start owner focus
           val result = finish (Traverse.run session)
       in T.validate_owner owner;running := false;result end))
  fun run_owned owner input = perform owner input (fn result => result)
  (* Genuine original assumption provenance; no opened recipe for NONE. *)
  fun run_assumption_owned
      (owner as T.Owner {work,running,root,...}) {occurrence,view} =
    T.protected owner (fn () =>
      (T.validate_owner owner;
       if !running then raise ERR "run_assumption" "traversal reentry" else ();
       running := true;
       let val dynamic = D.start_assumption work
             {occurrence = occurrence,view = view}
           val lower = F.initial_assumption work
             {occurrence = occurrence,view = view}
           val origin = case view of NONE => T.UnopenedSourceRoot
             | SOME _ => T.SourceRoot
           val focus = T.capture owner origin root dynamic lower
           val session = Traverse.start owner focus
           val result = Traverse.run session
       in T.validate_owner owner;running := false;result end))
  (* Only this constructor chooses positive provenance from a genuine
     registered view option. NONE is unchanged raw Goal DATA, never a
     fabricated opened recipe or a widened local-operation allowance. *)
  fun run_goal_owned (owner as T.Owner {work,running,root,...}) {view} =
    T.protected owner (fn () =>
      (T.validate_owner owner;
       if !running then raise ERR "run_goal" "traversal reentry" else ();
       running := true;
       let val dynamic = D.start_goal work {view = view}
           val lower = F.initial_goal work {view = view}
           val origin = case view of NONE => T.UnopenedPositiveRoot
             | SOME _ => T.OpenedPositiveRoot
           val focus = T.capture owner origin root dynamic lower
           val session = Traverse.start owner focus
           val result = Traverse.run session
       in T.validate_owner owner;running := false;result end))
  fun canonical_endpoints owner result = T.protected owner (fn () =>
    let val converted = T.unwrap_conversion owner result
        val {source,target,...} = D.endpoints converted
    in {source = source,target = target} end)
  fun result_policy (owner as T.Owner {check_type,...}) result ty =
    T.protected owner (fn () =>
      (ignore (T.unwrap_conversion owner result);
       check_type ty;
       ignore (T.unwrap_conversion owner result)))
  fun canonical_fact (owner as T.Owner {check_type,...}) result =
    T.protected owner (fn () =>
      let val converted = T.unwrap_conversion owner result
      in D.closed_fact converted
        {ordinal = T.ordinal owner,check_type = result_policy owner result} end)
  fun source_conversion (owner as T.Owner {check_type,...}) result =
    T.protected owner (fn () =>
      let val converted = T.unwrap_conversion owner result
      in D.source_conversion converted
        {ordinal = T.ordinal owner,check_type = result_policy owner result} end)
  fun denial_conversion owner result {denial_view} =
    T.protected owner (fn () =>
      let val converted = T.unwrap_conversion owner result
      in D.denial_conversion converted
        {denial_view = denial_view,ordinal = T.ordinal owner,
         check_type = result_policy owner result} end)
  fun restore_original (owner as T.Owner {check_type,...}) result =
    T.protected owner (fn () =>
      let val converted = T.unwrap_conversion owner result
      in D.restore_original converted
        {ordinal = T.ordinal owner,check_type = result_policy owner result} end)
  fun run owner input =
    perform owner input (Option.map (restore_original owner))
  val close = T.retire
end
