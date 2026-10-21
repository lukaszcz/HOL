(* Solver-independent discovery/lifecycle extraction. Source draft only. *)
structure SmtLib_CheckedCarrierProducer :> SmtLib_CheckedCarrierProducer =
struct
  structure G = SmtReplayGraph
  structure S = SmtReplaySource
  structure W = SmtReplayInvocationWork
  structure K = SmtLib_CompactPositiveGoalSourceStage
  structure Legacy = SmtLib_OwnedPositiveGoalSourceStage
  structure GP = SmtLib_GraphPreprocess
  val _ = SmtLib_CompactPositiveGoalSourceStage.begin_provenance
  val _ = SmtLib_CompactCarrierScheduler.run_assumption_owned
  val _ = SmtReplayGraph.discover_compact_shared_partial
  val _ = SmtCheckedGraph.prepare_original
  val ERR = Feedback.mk_HOL_ERR "SmtLib_CheckedCarrierCallsite"
  type request =
    {limits : SmtCheckedGraph.limits,semantic_limits : W.limits,
     work_limit : int,check_type : Type.hol_type -> unit,
     scope_opened : G.scope -> unit}
  type owned_preprocessing =
    {work : W.portfolio,preprocessing : GP.validation}
  (* Private companion retains discovery guards for the public run path.
     prepare_stage still exposes the same caller-owned K interface. *)
  fun prepare_stage_with discovery constructor work
      {import_limit,check_type,scope_opened} =
    let
      val sources = W.original_sources work
      val graph = S.owning_graph sources val scope = S.owning_scope sources
      val limits = W.semantic_limits work val epoch = Type.type_epoch ()
      val symbols = Term.term_epoch ()
      val plans = ref ([] : G.partial_discovery list)
      fun guard () =
        (W.validate work graph scope sources limits;
         if Type.type_epoch () = epoch andalso Term.term_epoch () = symbols
           then () else raise ERR "prepare_stage" "retirement epoch changed";
         List.app (G.validate_partial graph scope) (!plans))
      fun protected action = action () handle primary =>
        (W.close work;raise primary)
      fun step () = (guard ();W.spend work 1;guard ())
      fun checked_type ty = (guard ();check_type ty;guard ())
      fun opened_scope child = (guard ();scope_opened child;guard ())
      fun choices () = W.with_step work (fn () =>
        let
          val _ = guard ()
          val _ = if import_limit > 0 then () else
            raise ERR "prepare_stage" "nonpositive import discovery limit"
          val (denial,assumptions) = case S.reconciliation_sources sources of
              denied::rest => (denied,rest)
            | [] => raise ERR "prepare_stage" "original denial absent"
          val positive = S.goal_source sources
          fun discover (source : G.source) =
            let val plan = discovery graph scope
                  {original = #node source,maximum = import_limit,
                   scan_limit = W.work_limit work,step = step}
                val _ = plans := plan :: !plans
                val _ = guard ()
            in G.partial_view graph scope plan end
          (* Each NONE is a completed whole-root rule scan. Applications
             can retain unrelated opaque children in a private partial recipe.
             No unknown body or exhausted scan is mapped to NONE. *)
          fun ordered [] = []
            | ordered (source::rest) =
                let val view = discover source
                in view :: ordered rest end
          val assumption_views = ordered assumptions
          val goal_view = discover positive
          (* A changed positive goal requires the authentic old denial recipe;
             discovery and fixed-denial transport remain last, respectively. *)
          val denial_view = case goal_view of NONE => NONE
            | SOME _ => discover denial
          val _ = guard ()
        in {assumption_views = assumption_views,goal_view = goal_view,
            denial_view = denial_view} end)
    in protected (fn () =>
      let val {assumption_views,goal_view,denial_view} = choices ()
          val stage = constructor work
            {assumption_views = assumption_views,goal_view = goal_view,
             denial_view = denial_view,check_type = checked_type,
             scope_opened = opened_scope}
      in guard ();{stage = stage,guard = guard} end)
    end
  fun prepare_stage_guarded work request =
    prepare_stage_with G.discover_compact_shared_partial K.begin_provenance
      work request
  fun prepare_stage work request =
    #stage (prepare_stage_with G.discover_partial Legacy.begin_provenance
      work request)
  fun prepare_compact_stage work request =
    #stage (prepare_stage_guarded work request)
  fun run ({limits,semantic_limits,work_limit,check_type,scope_opened}
           : request) solver original =
    let
      val _ = SmtCheckedGraph.validate limits
      val _ = if #template_limit semantic_limits =
          #template_limit (#recipe_limits limits) then () else
        raise ERR "run" "preprocessing and replay template contracts differ"
      (* All retained state belongs to THIS public call, never a reusable
         global factory/counter or a new Source made from processed goal. *)
      val work_ref = ref (NONE : W.portfolio option)
      val stage_ref = ref (NONE : K.owner option)
      val started = ref false
      fun complete () = case !stage_ref of
          SOME stage => K.close stage
        | NONE => Option.app W.close (!work_ref)
      fun discover sources =
        let
          val _ = if not (!started) then started := true else
            raise ERR "discover" "original discovery is one shot"
          val graph = S.owning_graph sources
          val scope = S.owning_scope sources
          val work = W.begin graph scope sources
            {limits = semantic_limits,work_limit = work_limit}
          val _ = work_ref := SOME work
          val epoch = Type.type_epoch ()
          fun guard () =
            (W.validate work graph scope sources semantic_limits;
             if Type.type_epoch () = epoch then () else
               raise ERR "discover" "Type retirement epoch changed")
          val {stage,guard = discovery_guard} = prepare_stage_guarded work
            {import_limit = #import_limit limits,check_type = check_type,
             scope_opened = scope_opened}
          val _ = stage_ref := SOME stage
          val validation = K.build stage
          val _ = discovery_guard () val _ = guard ()
          val _ = if Portable.pointer_eq
              (GP.original_sources validation,sources) andalso
              GP.source_nodes validation = S.assumption_nodes sources @
                [S.denied_goal_node sources] then () else
            raise ERR "discover" "original Source occurrence prefix changed"
        in validation end
      (* Existing optional wrappers run the real external solver and perform
         same-original live accept + immutable late audit. Do not close K at
         discover return: GP evidence still needs the SAME live Work later. *)
    in SolverSpec.complete_owned complete (solver discover) original end
  fun run_cvc_with_work
      ({limits,semantic_limits,work_limit,check_type,scope_opened}
           : request) solver original =
    let
      val _ = SmtCheckedGraph.validate limits
      val _ = if #template_limit semantic_limits =
          #template_limit (#recipe_limits limits) then () else
        raise ERR "run" "preprocessing and replay template contracts differ"
      (* All retained state belongs to THIS public call, never a reusable
         global factory/counter or a new Source made from processed goal. *)
      val work_ref = ref (NONE : W.portfolio option)
      val stage_ref = ref (NONE : K.owner option)
      val started = ref false
      fun complete () = case !stage_ref of
          SOME stage => K.close stage
        | NONE => Option.app W.close (!work_ref)
      fun discover sources =
        let
          val _ = if not (!started) then started := true else
            raise ERR "discover" "original discovery is one shot"
          val graph = S.owning_graph sources
          val scope = S.owning_scope sources
          val work = W.begin_with_scope_guard graph scope sources
            {limits = semantic_limits,work_limit = work_limit}
          val _ = work_ref := SOME work
          val epoch = Type.type_epoch ()
          fun guard () =
            (W.validate work graph scope sources semantic_limits;
             if Type.type_epoch () = epoch then () else
               raise ERR "discover" "Type retirement epoch changed")
          val {stage,guard = discovery_guard} = prepare_stage_guarded work
            {import_limit = #import_limit limits,check_type = check_type,
             scope_opened = scope_opened}
          val _ = stage_ref := SOME stage
          val validation = K.build stage
          val _ = discovery_guard () val _ = guard ()
          val _ = GP.validate_with_work work validation
          val _ = if Portable.pointer_eq
              (GP.original_sources validation,sources) andalso
              GP.source_nodes validation = S.assumption_nodes sources @
                [S.denied_goal_node sources] then () else
            raise ERR "discover" "original Source occurrence prefix changed"
        in {work = work,preprocessing = validation} end
      (* Existing optional wrappers run the real external solver and perform
         same-original live accept + immutable late audit. Do not close K at
         discover return: GP evidence still needs the SAME live Work later. *)
    in SolverSpec.complete_owned complete (solver discover) original end
  val _ = SmtLib_OwnedFixedNumSourceStage.begin
  val _ = SmtLib_OwnedFixedNumSourceStage.build_needed
  fun prepare_fixed_num_stage work request =
    SmtLib_OwnedFixedNumSourceStage.begin work request
  (* Fixed internal producer only; no caller normalization callback. *)
  fun run_fixed_num_with_work
      ({limits,semantic_limits,work_limit,check_type,scope_opened}:request)
      solver original =
    let val _=SmtCheckedGraph.validate limits
        val _=if #template_limit semantic_limits=
            #template_limit (#recipe_limits limits) then () else
          raise ERR "run_fixed_num" "template contracts differ"
        val work_ref=ref (NONE:W.portfolio option)
        val stage_ref=ref (NONE:SmtLib_OwnedFixedNumSourceStage.owner option)
        val started=ref false
        fun complete () = case !stage_ref of SOME stage =>
              SmtLib_OwnedFixedNumSourceStage.close stage
          | NONE => Option.app W.close (!work_ref)
        fun discover sources =
          let val _=if not (!started) then started := true else
                raise ERR "discover_fixed_num" "original attempt is one-shot"
              val graph=S.owning_graph sources
              val root=S.owning_scope sources
              val work=W.begin_with_scope_guard graph root sources
                {limits=semantic_limits,work_limit=work_limit}
              val _=work_ref := SOME work
              val stage=prepare_fixed_num_stage work
                {import_limit= #import_limit limits,check_type=check_type,
                 scope_opened=scope_opened}
              val _=stage_ref := SOME stage
              val validation=SmtLib_OwnedFixedNumSourceStage.build_needed stage
              val _=GP.validate_with_work work validation
              val _=if Portable.pointer_eq
                    (GP.original_sources validation,sources) andalso
                  GP.source_nodes validation=S.assumption_nodes sources @
                    [S.denied_goal_node sources] then () else
                raise ERR "discover_fixed_num" "original Source changed"
          in {work=work,preprocessing=validation} end
    in SolverSpec.complete_owned complete (solver discover) original end
  structure RP = SmtReplayResourcePolicy

  (* All discovery fuel is the actual caller's work policy. A NONE view is
     returned only by the completed G discovery, never by catching a limit
     error. The original ordered Source object is retained throughout. *)
  fun prepare_compact_stage_with_policy work
      {import_limit,check_type,scope_opened} =
    let
      val sources = W.original_sources work
      val graph = S.owning_graph sources val scope = S.owning_scope sources
      val limits = W.semantic_policy work val epoch = Type.type_epoch ()
      val symbols = Term.term_epoch ()
      val plans = ref ([] : G.policy_partial_discovery list)
      fun guard () =
        (W.validate_policy work graph scope sources limits;
         if Type.type_epoch () = epoch andalso Term.term_epoch () = symbols
           then () else raise ERR "prepare_compact_stage_with_policy"
             "retirement epoch changed";
         List.app (G.validate_partial_with_policy graph scope) (!plans))
      fun protected action = action () handle primary =>
        (W.close work;raise primary)
      fun step () = (guard ();W.spend_policy work 1;guard ())
      fun checked_type ty = (guard ();check_type ty;guard ())
      fun opened_scope child = (guard ();scope_opened child;guard ())
      fun choices () = W.with_step work (fn () =>
        let
          val _ = guard ()
          val _ = if RP.positive import_limit then () else
            raise ERR "prepare_compact_stage_with_policy"
              "nonpositive import discovery limit"
          val (denial,assumptions) = case S.reconciliation_sources sources of
              denied::rest => (denied,rest)
            | [] => raise ERR "prepare_compact_stage_with_policy"
                "original denial absent"
          val positive = S.goal_source sources
          fun discover (source:G.source) =
            let
              val plan = G.discover_partial_with_policy graph scope
                {original = #node source,maximum = import_limit,
                 scan_limit = W.work_policy work,step = step}
              val _ = plans := plan :: !plans val _ = guard ()
            in G.partial_view_with_policy graph scope plan end
          fun ordered [] = []
            | ordered (source::rest) =
                let val view = discover source
                in view :: ordered rest end
          val assumption_views = ordered assumptions
          val goal_view = discover positive
          val denial_view = case goal_view of NONE => NONE
            | SOME _ => discover denial
          val _ = guard ()
        in {assumption_views=assumption_views,goal_view=goal_view,
            denial_view=denial_view} end)
    in protected (fn () =>
      let
        val {assumption_views,goal_view,denial_view} = choices ()
        val stage = K.begin_provenance_with_policy work
          {assumption_views=assumption_views,goal_view=goal_view,
           denial_view=denial_view,check_type=checked_type,
           scope_opened=opened_scope,discoveries=List.rev (!plans)}
        val _ = guard ()
      in stage end)
    end

  datatype native_policy_preparation = NativePolicyPreparation of
    {work:W.portfolio,prepared:K.policy_preparation,
     budget:SmtReplayNativeContract.contract,request:request}

  (* The two inputs have different jobs. The RP ceiling governs generic
     construction/discovery bookkeeping. The old caller's finite import
     contract still gates each actual opened native binder in G discovery. *)
  fun native_discovery_limit metadata (native:int) =
    case metadata of RP.Uncapped => RP.from_int native
      | RP.AtMost cap => RP.AtMost (IntInf.min (cap,IntInf.fromInt native))

  fun prepare_compact_native_discovery work
      {import_limit,scan_limit,check_type,scope_opened} =
    let
      val sources = W.original_sources work
      val graph = S.owning_graph sources val scope = S.owning_scope sources
      val limits = W.semantic_policy work val epoch = Type.type_epoch ()
      val symbols = Term.term_epoch ()
      val plans = ref ([] : G.policy_partial_discovery list)
      fun guard () =
        (W.validate_policy work graph scope sources limits;
         if Type.type_epoch () = epoch andalso Term.term_epoch () = symbols
           then () else raise ERR "prepare_compact_stage_with_policy"
             "retirement epoch changed";
         List.app (G.validate_partial_with_policy graph scope) (!plans))
      fun protected action = action () handle primary =>
        (W.close work;raise primary)
      fun step () = (guard ();W.spend_policy work 1;guard ())
      fun checked_type ty = (guard ();check_type ty;guard ())
      fun opened_scope child = (guard ();scope_opened child;guard ())
      fun choices () = W.with_step work (fn () =>
        let
          val _ = guard ()
          val _ = if RP.positive import_limit then () else
            raise ERR "prepare_compact_stage_with_policy"
              "nonpositive import discovery limit"
          val (denial,assumptions) = case S.reconciliation_sources sources of
              denied::rest => (denied,rest)
            | [] => raise ERR "prepare_compact_stage_with_policy"
                "original denial absent"
          val positive = S.goal_source sources
          fun discover (source:G.source) =
            let
              val plan = G.discover_partial_with_policy graph scope
                {original = #node source,maximum = import_limit,
                 scan_limit = scan_limit,step = step}
              val _ = plans := plan :: !plans val _ = guard ()
            in G.partial_view_with_policy graph scope plan end
          fun ordered [] = []
            | ordered (source::rest) =
                let val view = discover source
                in view :: ordered rest end
          val assumption_views = ordered assumptions
          val goal_view = discover positive
          val denial_view = case goal_view of NONE => NONE
            | SOME _ => discover denial
          val _ = guard ()
        in {assumption_views=assumption_views,goal_view=goal_view,
            denial_view=denial_view} end)
    in protected (fn () =>
      let
        val {assumption_views,goal_view,denial_view} = choices ()
        val stage = K.begin_provenance_with_policy work
          {assumption_views=assumption_views,goal_view=goal_view,
           denial_view=denial_view,check_type=checked_type,
           scope_opened=opened_scope,discoveries=List.rev (!plans)}
        val _ = guard ()
      in stage end)
    end


  fun prepare_compact_native_stage_with_policy work
      (request as {limits,semantic_limits,work_limit,check_type,scope_opened}
        :request) {import_limit} =
    ((let
        val _ = SmtCheckedGraph.validate limits
        val _ = if #template_limit semantic_limits =
            #template_limit (#recipe_limits limits) then () else
          raise ERR "prepare_compact_native_stage_with_policy"
            "preprocessing and replay template contracts differ"
        val budget = SmtReplayNativeContract.capture
          work {semantic_limits=semantic_limits,
                import_limit= #import_limit limits,
                type_work_limit=work_limit}
        val opened_limit = native_discovery_limit import_limit
          (#import_limit limits)
        val scan_limit = native_discovery_limit (W.remaining_policy work)
          work_limit
        val prepared = prepare_compact_native_discovery work
          {import_limit=opened_limit,scan_limit=scan_limit,
           check_type=check_type,scope_opened=scope_opened}
      in NativePolicyPreparation
        {work=work,prepared=prepared,budget=budget,request=request} end)
     handle primary => (W.close work;raise primary))

  (* The actual captured request token travels with its genuine preparation.
     No detached prepared stage/caller replacement contract pair is adopted. *)
  fun build_compact_native_root_beta_with_policy expected
      (as_preparation as NativePolicyPreparation {work,...})=
    ((if Portable.pointer_eq (expected,work) then () else
        raise ERR "build_compact_native_root_beta_with_policy"
          "different original Work";
      let val NativePolicyPreparation {prepared,budget,...}=as_preparation
      in K.build_root_beta_with_policy expected prepared
        {native_contract=budget} end)
     handle primary=>(W.close expected;raise primary))
  (* The actual request token, not a replacement budget with equal fields.
     This passive getter grants neither reusable credit nor native action. *)
  fun native_contract_with_policy_for expected
      (preparation as NativePolicyPreparation {work,...})=
    ((if Portable.pointer_eq (expected,work) then () else
        raise ERR "native_contract_with_policy_for" "different original Work";
      let val NativePolicyPreparation {prepared,budget,...}=preparation
          val _=SmtReplayNativeContract.validate_for expected budget
          val data=K.preparation_with_policy_for expected prepared
          val sources= #sources data
          val graph=S.owning_graph sources val root=S.owning_scope sources
          fun held (row:{occurrence:IntInf.int,index:IntInf.int,
              original:G.source,view:G.source option})=
            case #view row of NONE=>() | SOME view=>
              G.validate_opened_view graph root (#node (#original row)) view
          val _=List.app held (#rows data)
          val _=case #goal_view data of NONE=>() | SOME view=>
            G.validate_opened_view graph root
              (#node (S.goal_source sources)) view
          val _=case #denial_view data of NONE=>() | SOME view=>
            G.validate_opened_view graph root (#node (#denial data)) view
          val _=SmtReplayNativeContract.validate_for expected budget
      in budget end)
     handle primary=>(W.close expected;raise primary))

  fun build_compact_native_application_beta_with_policy expected
      (preparation as NativePolicyPreparation {work,...})=
    ((if Portable.pointer_eq (expected,work) then () else
        raise ERR "build_compact_native_application_beta_with_policy"
          "different original Work";
      let val NativePolicyPreparation {prepared,budget,...}=preparation
      in K.build_application_beta_with_policy expected prepared
        {native_contract=budget} end)
     handle primary=>(W.close expected;raise primary))
  fun build_compact_native_scope_beta_with_policy expected
      (preparation as NativePolicyPreparation {work,...})=
    ((if Portable.pointer_eq (expected,work) then () else
        raise ERR "build_compact_native_scope_beta_with_policy"
          "different original Work";
      let val NativePolicyPreparation {prepared,budget,...}=preparation
      in K.build_scope_beta_with_policy expected prepared
        {native_contract=budget} end)
     handle primary=>(W.close expected;raise primary))
  fun build_compact_native_carrier_with_policy expected
      (preparation as NativePolicyPreparation {work,...})=
    ((if Portable.pointer_eq (expected,work) then () else
        raise ERR "build_compact_native_carrier_with_policy"
          "different original Work";
      let val NativePolicyPreparation {prepared,budget,...}=preparation
      in K.build_carrier_with_policy expected prepared
        {native_contract=budget} end)
     handle primary=>(W.close expected;raise primary))
  fun prepare_compact_native_stage_from_contract_with_policy work
      (request as {limits,semantic_limits,work_limit,check_type,scope_opened}
        :request) budget {import_limit} =
    ((let
        val native=SmtReplayNativeContract.for_work work budget
        val _ = SmtCheckedGraph.validate limits
        val _ = if #template_limit semantic_limits =
            #template_limit (#recipe_limits limits) then () else
          raise ERR "prepare_compact_native_stage_with_policy"
            "preprocessing and replay template contracts differ"
        val _=if native={semantic_limits=semantic_limits,
            import_limit= #import_limit limits,type_work_limit=work_limit}
            then ()else
          raise ERR "prepare_compact_native_stage_from_contract_with_policy"
            "different actual native caller request"
        val opened_limit = native_discovery_limit import_limit
          (#import_limit limits)
        val scan_limit = native_discovery_limit (W.remaining_policy work)
          work_limit
        val prepared = prepare_compact_native_discovery work
          {import_limit=opened_limit,scan_limit=scan_limit,
           check_type=check_type,scope_opened=scope_opened}
      in NativePolicyPreparation
        {work=work,prepared=prepared,budget=budget,request=request} end)
     handle primary => (W.close work;raise primary))
end
