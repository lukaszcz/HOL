(* Source proposal only; no compiled or full coverage claim. *)
structure SmtCheckedGraph :> SmtCheckedGraph =
struct
  structure G = SmtReplayGraph
  structure S = SmtReplaySource
  structure Q = SmtLib_GraphProof
  type limits =
    {import_limit : int, literal_limit : int, binder_limit : int,
     recipe_limits : SmtLib_GraphTheories.limits}
  exception ParseFailure of exn
  exception ReplayFailure of exn
  val ERR = Feedback.mk_HOL_ERR "SmtCheckedGraph"
  fun validate ({import_limit,literal_limit,binder_limit,recipe_limits}
                : limits) =
    let
      val {template_limit,index_limit,operand_limit,token_limit} = recipe_limits
      val maximum = SmtResource.max_bv_replay_term_nodes
      val terms = [import_limit,literal_limit,binder_limit,template_limit,
                   index_limit,operand_limit]
      val _ = if List.all (fn n => n > 0 andalso n <= maximum) terms andalso
          token_limit > 0 andalso token_limit <= SmtResource.max_proof_bytes
        then () else raise ERR "validate" "invalid opt-in graph limits"
    in () end
  fun options (limits : limits) graph scope
      (translation : SmtLib.translation) : SmtLib_GraphFrontend.options =
    {graph = graph,scope = scope,logic = #logic translation,sources = [],
     sorts = Redblackmap.mkDict String.compare,binder_lists = [],
     import_limit = #import_limit limits,literal_limit = #literal_limit limits,
     binder_limit = #binder_limit limits,recipe_limits = #recipe_limits limits,
     special = fn _ => fn _ => NONE,
     ascribed = fn _ => fn _ => fn _ => NONE}

  fun run solver limits translation version (assumptions,goal) parse replay
      input =
    let
      val _ = validate limits
      val graph = G.new ()
      val scope = G.root_scope graph
      val packet = ref NONE
      fun work () =
        let
          (* Sources precede flexible parser names and proof callbacks. *)
          val sources = S.new graph scope (#import_limit limits)
            {goal = goal,assumptions = assumptions}
          val parsed = parse (options limits graph scope translation) input
            handle error => raise ParseFailure error
          val _ = packet := SOME parsed
          val _ = if Portable.pointer_eq (Q.graph parsed,graph) andalso
              Q.scope parsed = scope andalso Q.solver parsed = solver andalso
              #requested (Q.versions parsed) = version then () else
            raise ERR "run" "foreign graph packet ownership or solver"
          val result = replay graph scope sources (Q.proof parsed)
            handle error => raise ReplayFailure error
          val _ = S.check_goal sources result
        in result end
      val outcome = Exn.capture work ()
      (* Attempt both closes. A replay primary survives all cleanup errors. *)
      val packet_close = Exn.capture
        (fn () => Option.app Q.close (!packet)) ()
      val scope_close = Exn.capture (fn () => G.close_scope graph scope) ()
    in case outcome of
        Exn.Exn error => raise error
      | Exn.Res result =>
          (Exn.release packet_close;Exn.release scope_close;result)
    end

  fun z3 limits translation version goal input =
    run "Z3" limits translation version goal
      (fn options => SmtResource.profile_phase "z3/parse+graph-construction"
        (Z3_ProofParser.parse_graph_translation_packet_with_version
          options translation version))
      (fn graph => fn scope => fn sources => fn proof =>
        SmtResource.profile_phase "z3/replay"
          (Z3_ProofReplay.check_graph_proof_with_definitions
            (SmtLib.translation_definitions translation) graph scope)
          {sources = sources,proof = proof,
           template_limit = SmtResource.max_bv_replay_term_nodes}) input

  fun cvc limits translation version goal input =
    run "cvc5" limits translation version goal
      (fn options => SmtResource.profile_phase "cvc/cpc-parse"
        (CPC_ProofParser.parse_graph_translation_packet_with_version
          options translation version))
      (fn graph => fn scope => fn sources => fn proof =>
        SmtResource.profile_phase "cvc/cpc-replay"
          (CPC_ProofReplay.prove_graph_proof_with_definitions
            (SmtLib.translation_definitions translation))
          {graph = graph,scope = scope,sources = sources,proof = proof}) input

  structure W = SmtReplayWrapperSession
  structure D = SmtReplaySourceConsumerSession
  datatype invocation = Invocation of
    {limits : limits,session : SmtReplayWrapperSession.session,
     translation : SmtLib.translation option ref,replay_started : bool ref}

  fun prepare_original limits discover original =
    let
      val _ = validate limits
      val graph = G.new ()
      val scope = G.root_scope graph
      fun work () =
        let
          val (assumptions,goal) = original
          val sources = S.new graph scope (#import_limit limits)
            {assumptions = assumptions,goal = goal}
          (* Exact original owner exists before the producer callback. *)
          val session =
            SmtReplaySourceConsumerSession.start sources original
          val _ = D.discover session discover
        in Invocation {limits = limits,session = session,
          translation = ref NONE,replay_started = ref false} end
    in work () handle primary =>
      ((G.close_scope graph scope handle _ => ());raise primary) end

  fun processed_goal (Invocation {session,...}) = W.processed_goal session
  fun close_original (Invocation {session,...}) = W.close session
  fun audit_original (Invocation {session,...}) = W.audit session

  fun admit_translation (Invocation {session,translation = selected,...})
      translation =
    let
      val _ = ignore (W.sources session)
      val _ = case !selected of
          NONE => ()
        | SOME original =>
            if Portable.pointer_eq (original,translation) then () else
              raise ERR "admit_translation" "different invocation translation"
      (* The existing emitted-definition consumers have a different checked
         policy. Never silently omit emitted definitions on the GP route. *)
      val definitions = SmtLib.translation_definitions translation
      val _ = ignore (W.preprocessing session)
    in if List.null definitions then selected := SOME translation else
      raise ERR "admit_translation"
        "original Source route needs checked emitted-definition integration"
    end handle primary =>
      ((W.close session handle _ => ());raise primary)

  fun run_original
      (invocation as Invocation {limits,session,replay_started,...})
      solver translation version
      parse replay input =
    let
      val graph = W.graph session
      val scope = W.scope session
      val packet = ref NONE
      fun work () =
        let
          val _ = if !replay_started then
              raise ERR "run_original" "invocation replay is one-shot"
            else replay_started := true
          val _ = admit_translation invocation translation
          val parsed = parse (options limits graph scope translation) input
            handle error => raise ParseFailure error
          val _ = packet := SOME parsed
          val _ = if Portable.pointer_eq (Q.graph parsed,graph) andalso
              Q.scope parsed = scope andalso Q.solver parsed = solver andalso
              #requested (Q.versions parsed) = version then () else
            raise ERR "run_original" "foreign parser packet owner or solver"
          val theorem = replay session (Q.proof parsed)
            handle error => raise ReplayFailure error
        in theorem end
      val outcome = Exn.capture work ()
      val packet_close = Exn.capture
        (fn () => Option.app Q.close (!packet)) ()
      val scope_close = Exn.capture (fn () => W.close session) ()
    in case outcome of
        Exn.Exn primary => raise primary
      | Exn.Res theorem =>
          (Exn.release packet_close;Exn.release scope_close;theorem)
    end

  fun z3_original (invocation as Invocation {limits,...}) translation version
      {local_law,nnf} =
    run_original invocation "Z3" translation version
      (fn options => Z3_ProofParser.parse_graph_translation_packet_with_version
        options translation version)
      (fn session => fn proof => D.prove_z3_using session
        {proof = proof,template_limit = #template_limit (#recipe_limits limits),
         local_law = local_law,nnf = nnf})

  fun cvc_original (invocation as Invocation {limits,...}) translation version
      {ordinary_limit,worker,force_worker} =
    run_original invocation "cvc5" translation version
      (fn options => CPC_ProofParser.parse_graph_translation_packet_with_version
        options translation version)
      (fn session => fn proof => D.prove_cpc_using session
        {proof = proof,ordinary_limit = ordinary_limit,
         template_limit = #template_limit (#recipe_limits limits),
         worker = worker,force_worker = force_worker})

  structure I = SmtReplayInvocationWork
  structure Emissions = SmtLib_GraphOwnedEmissions
  val _ = SmtLib_GraphOwnedEmissions.emit
  datatype owned_invocation = OwnedInvocation of
    {invocation : invocation,work : I.portfolio,
     emissions : Emissions.receipt option ref}
  val _ = SmtReplaySourceConsumerSession.discover_with_work
  val _ = SmtReplaySourceConsumerSession.prove_cpc_with_work_using
  fun prepare_original_with_work limits discover original =
    let val _ = validate limits val graph = G.new ()
        val scope = G.root_scope graph
        fun prepare () =
          let val (assumptions,goal) = original
              val sources = S.new graph scope (#import_limit limits)
                {assumptions = assumptions,goal = goal}
              val session = D.start sources original
              val work = D.discover_with_work session discover
              val invocation = Invocation {limits = limits,session = session,
                translation = ref NONE,replay_started = ref false}
          in OwnedInvocation {invocation = invocation,work = work,
            emissions = ref NONE} end
    in prepare () handle primary =>
      ((G.close_scope graph scope handle _ => ());raise primary) end
  fun processed_goal_with_work (OwnedInvocation
      {invocation = Invocation {session,...},work,...}) =
    W.processed_goal_with_work work session
  fun admit_translation_with_work (OwnedInvocation
      {invocation = invocation as Invocation
        {session,translation = selected,...},work,emissions}) translation =
    ((W.validate_with_work work session;
      (case !emissions of NONE => admit_translation invocation translation
       | SOME receipt =>
         let val input = W.preprocessing_with_work work session
             val _ = Emissions.validate_input_for work input receipt
             val exact = Emissions.translation_for work receipt
             val _ = if Portable.pointer_eq (translation,exact) then () else
               raise ERR "admit_translation_with_work"
                 "different genuine emitted translation"
             val _ = case !selected of NONE => () | SOME previous =>
               if Portable.pointer_eq (previous,translation) then () else
                 raise ERR "admit_translation_with_work"
                   "different invocation translation"
         in selected := SOME translation end);
      W.validate_with_work work session)
     handle primary =>
       ((W.close session handle _ => ());I.close work;raise primary))
  fun audit_original_with_work (OwnedInvocation
      {invocation = Invocation {session,...},work,...}) =
    W.audit_with_work work session
  fun close_original_with_work (OwnedInvocation {invocation,work,...}) =
    let val close_session = Exn.capture close_original invocation
        val close_work = Exn.capture I.close work
    in Exn.release close_session;Exn.release close_work end
  (* Emission is generated from THIS opaque session's actual GP goal.
     Caller supplies neither a translation record nor an unfolding theorem. *)
  fun emit_translation_with_work
      (OwnedInvocation {invocation = Invocation {session,...},work,...})
      options =
    (W.validate_with_work work session;
     Emissions.emit work (W.preprocessing_with_work work session) options)
  fun admit_emitted_translation_with_work
      (owned as OwnedInvocation
        {invocation = Invocation {session,...},work,emissions}) receipt =
    ((W.validate_with_work work session;
      Emissions.validate_input_for work
        (W.preprocessing_with_work work session) receipt;
      let val translation = Emissions.translation_for work receipt
          val _ = case !emissions of NONE => emissions := SOME receipt
            | SOME previous => if Portable.pointer_eq (previous,receipt)
                then () else raise ERR "admit_emitted_translation_with_work"
                  "emitted admission is one-shot"
      in admit_translation_with_work owned translation end)
     handle primary =>
       ((W.close session handle _ => ());I.close work;raise primary))

  fun cvc_original_with_work
      (owned as OwnedInvocation
        {invocation = invocation as Invocation
          {limits,session,replay_started,...},work,...}) translation version
      {ordinary_limit,worker,force_worker} input =
    let
      val _ = W.validate_with_work work session
      val graph = W.graph session val scope = W.scope session
      val packet = ref NONE
      fun replay () =
        let val _ = if !replay_started then raise ERR "cvc_original_with_work"
                  "invocation replay is one-shot" else replay_started := true
            val _ = admit_translation_with_work owned translation
            val parsed =
              CPC_ProofParser.parse_graph_translation_packet_with_version
              (options limits graph scope translation) translation version input
              handle error => raise ParseFailure error
            val _ = packet := SOME parsed
            val _ = if Portable.pointer_eq (Q.graph parsed,graph) andalso
                Q.scope parsed = scope andalso Q.solver parsed = "cvc5" andalso
                #requested (Q.versions parsed) = version then () else
              raise ERR "cvc_original_with_work" "foreign parser packet"
        in D.prove_cpc_with_work_using work session
          {proof = Q.proof parsed,ordinary_limit = ordinary_limit,
           template_limit = #template_limit (#recipe_limits limits),
           worker = worker,force_worker = force_worker}
          handle error => raise ReplayFailure error end
      val outcome = Exn.capture replay ()
      val packet_close = Exn.capture (fn () => Option.app Q.close (!packet)) ()
      val scope_close = Exn.capture close_original_with_work owned
    in case outcome of Exn.Exn primary => raise primary
      | Exn.Res theorem =>
          (Exn.release packet_close;Exn.release scope_close;theorem) end

  fun cvc_original_with_clauses_and_work
      (owned as OwnedInvocation
        {invocation = invocation as Invocation
          {limits,session,replay_started,...},work,...}) translation version
      {ordinary_limit,worker,clause_worker,force_worker} input =
    let
      val _ = W.validate_with_work work session
      val graph = W.graph session val scope = W.scope session
      val packet = ref NONE
      fun replay () =
        let val _ = if !replay_started then
                  raise ERR "cvc_original_with_clauses_and_work"
                    "invocation replay is one-shot"
                else replay_started := true
            val _ = admit_translation_with_work owned translation
            val parsed = SmtResource.profile_phase "cvc/emitted-parse"
              (CPC_ProofParser.parse_graph_translation_packet_with_version
                (options limits graph scope translation) translation version)
              input
              handle error => raise ParseFailure error
            val _ = packet := SOME parsed
            val _ = if Portable.pointer_eq (Q.graph parsed,graph) andalso
                Q.scope parsed = scope andalso Q.solver parsed = "cvc5" andalso
                #requested (Q.versions parsed) = version then () else
              raise ERR "cvc_original_with_clauses_and_work"
                "foreign parser packet"
        in SmtResource.profile_phase "cvc/emitted-replay-total"
          (D.prove_cpc_with_clauses_and_work_using work session)
          {proof = Q.proof parsed,ordinary_limit = ordinary_limit,
           template_limit = #template_limit (#recipe_limits limits),
           worker = worker,clause_worker = clause_worker,
           force_worker = force_worker}
          handle error => raise ReplayFailure error end
      val outcome = Exn.capture replay ()
      val packet_close = Exn.capture (fn () => Option.app Q.close (!packet)) ()
      val scope_close = Exn.capture close_original_with_work owned
    in case outcome of Exn.Exn primary => raise primary
      | Exn.Res theorem =>
          (Exn.release packet_close;Exn.release scope_close;theorem) end

  fun z3_original_with_work
      (owned as OwnedInvocation
        {invocation = invocation as Invocation
          {limits,session,replay_started,...},work,...}) translation version
      {local_law,nnf} input =
    let
      val _ = W.validate_with_work work session
      val graph = W.graph session val scope = W.scope session
      val packet = ref NONE
      fun replay () =
        let val _ = if !replay_started then raise ERR "z3_original_with_work"
                  "invocation replay is one-shot" else replay_started := true
            val _ = admit_translation_with_work owned translation
            val parsed =
              Z3_ProofParser.parse_graph_translation_packet_with_version
              (options limits graph scope translation) translation version input
              handle error => raise ParseFailure error
            val _ = packet := SOME parsed
            val _ = if Portable.pointer_eq (Q.graph parsed,graph) andalso
                Q.scope parsed = scope andalso Q.solver parsed = "Z3" andalso
                #requested (Q.versions parsed) = version then () else
              raise ERR "z3_original_with_work" "foreign parser packet"
        in D.prove_z3_with_work_using work session
          {proof = Q.proof parsed,
           template_limit = #template_limit (#recipe_limits limits),
           local_law = local_law,nnf = nnf}
          handle error => raise ReplayFailure error end
      val outcome = Exn.capture replay ()
      val packet_close = Exn.capture (fn () => Option.app Q.close (!packet)) ()
      val scope_close = Exn.capture close_original_with_work owned
    in case outcome of Exn.Exn primary => raise primary
      | Exn.Res theorem =>
          (Exn.release packet_close;Exn.release scope_close;theorem) end

  (* This route selects the exact existing bounded stock workers from the
     opaque same-input emission receipt; it is not a normalizer callback. *)
  fun cvc_original_emitted_with_work
      (owned as OwnedInvocation {work,...}) receipt version ordinary_limit
      input =
    let val _ = admit_emitted_translation_with_work owned receipt
        val translation = Emissions.translation_for work receipt
        val worker = Emissions.worker_for work receipt
        val force = Emissions.force_worker_for work receipt
        val clause_worker = Emissions.clause_worker_for work receipt
    in cvc_original_with_clauses_and_work owned translation version
      {ordinary_limit = ordinary_limit,worker = worker,
       clause_worker = clause_worker,
       force_worker = SOME force} input end


  (* The actual same-owner parsed proof supplies the fixed Z3 producer's
     variable/version metadata. No public normalizer callback is accepted. *)
  fun z3_original_emitted_with_work
      (owned as OwnedInvocation
        {invocation = Invocation {limits,session,replay_started,...},
         work,...}) receipt version input =
    let
      val _ = W.validate_with_work work session
      val _ = admit_emitted_translation_with_work owned receipt
      val translation = Emissions.translation_for work receipt
      val graph = W.graph session val scope = W.scope session
      val packet = ref NONE
      fun replay () =
        let val _ = if !replay_started then
                  raise ERR "z3_original_emitted_with_work"
                    "invocation replay is one-shot"
                else replay_started := true
            val _ = admit_translation_with_work owned translation
            val parsed =
              Z3_ProofParser.parse_graph_translation_packet_with_version
                (options limits graph scope translation) translation version
                input handle error => raise ParseFailure error
            val _ = packet := SOME parsed
            val _ = if Portable.pointer_eq (Q.graph parsed,graph) andalso
                Q.scope parsed = scope andalso Q.solver parsed = "Z3" andalso
                #requested (Q.versions parsed) = version then () else
              raise ERR "z3_original_emitted_with_work" "foreign parser packet"
            val fixed = Emissions.z3_workers_for work receipt (Q.proof parsed)
        in D.prove_z3_with_work_using work session
          {proof = Q.proof parsed,
           template_limit = #template_limit (#recipe_limits limits),
           local_law = #local_law fixed,nnf = #nnf fixed}
          handle error => raise ReplayFailure error end
      val outcome = Exn.capture replay ()
      val packet_close = Exn.capture (fn () => Option.app Q.close (!packet)) ()
      val scope_close = Exn.capture close_original_with_work owned
    in case outcome of Exn.Exn primary => raise primary
      | Exn.Res theorem =>
          (Exn.release packet_close;Exn.release scope_close;theorem) end

  structure RP=SmtReplayResourcePolicy
  structure GP=SmtLib_GraphPreprocess
  structure NC=SmtReplayNativeContract
  type policy_request=
    {construction_limits:RP.graph_policy,semantic_limits:RP.semantic_policy,
     work_limit:RP.limit,native_limits:NC.limits}
  datatype policy_invocation=PolicyInvocation of
    {request:policy_request,session:W.session,work:I.portfolio,
     native_contract:NC.contract,translation:SmtLib.translation option ref,
     replay_started:bool ref}
  fun validate_policy_request
      ({construction_limits,semantic_limits,work_limit,...}:policy_request)=
    let val recipe= #recipe_limits construction_limits
        val entries=[#import_limit construction_limits,
          #literal_limit construction_limits,#binder_limit construction_limits,
          #template_limit recipe,#index_limit recipe,#operand_limit recipe,
          #token_limit recipe,#input_limit semantic_limits,
          #output_limit semantic_limits,#template_limit semantic_limits,
          work_limit]
    in if List.all RP.positive entries then ()else
      raise ERR "prepare_original_with_policy" "nonpositive policy request"end
  (* Source, Work and the one actual finite caller token are created before
     discovery. The callback returns only a checked GP of THESE originals. *)
  fun prepare_original_with_policy (request:policy_request) discover original=
    let val _=validate_policy_request request
        val graph=G.new()val scope=G.root_scope graph
        val held=ref(NONE:I.portfolio option)
        fun prepare ()=
          let val (assumptions,goal)=original
              val sources=S.new_with_policy graph scope
                (#import_limit(#construction_limits request))
                {goal=goal,assumptions=assumptions}
              val session=D.start sources original
              val work=I.begin_with_scope_guard_policy graph scope sources
                {limits= #semantic_limits request,
                 work_limit= #work_limit request}
              val _=held:=SOME work
              val contract=NC.capture work(#native_limits request)
              val _=D.discover_with_policy work session
                (fn actual=>discover work contract actual)
              val validation=W.preprocessing_with_policy work session
              val _=if Portable.pointer_eq
                    (GP.original_sources validation,sources)andalso
                  GP.source_nodes validation=S.assumption_nodes sources @
                    [S.denied_goal_node sources]then ()else
                raise ERR "prepare_original_with_policy"
                  "original Source occurrence prefix changed"
              val result=PolicyInvocation
                {request=request,session=session,work=work,
                 native_contract=contract,translation=ref NONE,
                 replay_started=ref false}
          in {work=work,invocation=result}end
    in prepare()handle primary=>
      (Option.app I.close (!held);
       (G.close_scope graph scope handle _=>());raise primary)end

  (* A single G-born Bool App is published Ready before caller pre. The
     retained handoff cannot import an externally supplied goal. *)
  datatype children_first_handoff = ChildrenFirst of
    {request:policy_request,sources:S.sources,work:I.portfolio,
     graph:G.graph,scope:G.scope,original:Abbrev.goal,used:bool ref}
  fun exact_children_goal ((lefts,left),(rights,right)) =
    List.null lefts andalso List.null rights andalso
    Portable.pointer_eq(left,right)
  fun native_fits_owned (owned:SmtReplayOriginalAcquisition.request)
      (native:NC.limits) =
    let val policy= #native_limits owned
        val ps= #semantic_limits policy
        val ns= #semantic_limits native
        fun fit limit amount = amount>0 andalso
          RP.allows limit (IntInf.fromInt amount)
    in fit (#input_limit ps) (#input_limit ns) andalso
      fit (#output_limit ps) (#output_limit ns) andalso
      fit (#template_limit ps) (#template_limit ns) andalso
      fit (#import_limit policy) (#import_limit native) andalso
      fit (#type_work_limit policy) (#type_work_limit native)end
  fun begin_children_first_boolean_application
      {owned:SmtReplayOriginalAcquisition.request,
       native:NC.limits} children =
    let val request:policy_request =
          {construction_limits= #construction_limits owned,
           semantic_limits= #semantic_limits owned,
           work_limit= #work_limit owned,native_limits=native}
        val _=validate_policy_request request
        val _=if native_fits_owned owned native then ()else
          raise ERR "begin_children_first_boolean_application"
            "finite native contract exceeds A owned request"
        val {sources,portfolio,application} =
          I.begin_owned_boolean_application owned children
        val {graph,scope}=S.owner_for_scope_guard sources
        fun ready ()=
          let val context=I.prepare_owned_application_context
                portfolio application
              val _=I.complete_owned_application_source
                portfolio application context
              val _=I.complete_owned_application_denial
                portfolio application context
              val _=I.prepare_ordered_original_sources portfolio context
              val _=I.complete_ordered_original_acquisition
                portfolio context
              val original=S.original_goal sources
              val _=if exact_children_goal
                  (original,([], #original(S.goal_source sources)))
                then ()else raise ERR "begin_children_first_boolean_application"
                  "Ready goal is not the exact constructor result"
              val handoff=ChildrenFirst
                {request=request,sources=sources,work=portfolio,
                 graph=graph,scope=scope,original=original,used=ref false}
          in {goal=original,handoff=handoff}end
    in ready()handle primary=>
      (I.close portfolio;(G.close_scope graph scope handle _=>());
       raise primary)end
  fun close_children_first_handoff
      (ChildrenFirst{work,graph,scope,used,...})=
    if !used then ()else
      (used:=true;I.close work;G.close_scope graph scope)
  (* CVC has already caused I birth and Ready. No G.new/S.new/I.begin here.
     The I token is consumed before any adoption result is exposed. *)
  fun validate_caller_owned_children_first_request
      {owned:SmtReplayOriginalAcquisition.request,native:NC.limits} =
    let val request:policy_request =
          {construction_limits= #construction_limits owned,
           semantic_limits= #semantic_limits owned,
           work_limit= #work_limit owned,native_limits=native}
        val _=validate_policy_request request
    in if native_fits_owned owned native then () else
       raise ERR "validate_caller_owned_children_first_request"
         "finite native contract exceeds A owned request" end
  fun adopt_caller_owned_children_first (native:NC.limits) token =
    let val {sources,portfolio,goal,owned}=
          I.take_ready_checked_owned_boolean_application token
        fun adopt () =
          let val _=validate_caller_owned_children_first_request
                {owned=owned,native=native}
              val {graph,scope}=S.owner_for_scope_guard sources
              val request:policy_request =
                {construction_limits= #construction_limits owned,
                 semantic_limits= #semantic_limits owned,
                 work_limit= #work_limit owned,native_limits=native}
              val handoff=ChildrenFirst
                {request=request,sources=sources,work=portfolio,
                 graph=graph,scope=scope,original=goal,used=ref false}
          in {goal=goal,handoff=handoff} end
    in adopt () handle primary =>
      ((I.close portfolio handle _=>());
       (let val {graph,scope}=S.owner_for_scope_guard sources
        in G.close_scope graph scope end handle _=>());
       raise primary) end
  fun prepare_children_first_with_policy
      (ChildrenFirst{request,sources,work,graph,scope,original,used})
      discover supplied =
    if !used then raise ERR "prepare_children_first_with_policy"
      "children-first handoff already consumed"
    else
      let val _=used:=true
          val session=ref(NONE:W.session option)
          fun prepare ()=
            let val _=if exact_children_goal(original,supplied)then ()else
                  raise ERR "prepare_children_first_with_policy"
                    "caller goal differs from exact A-born goal"
                val _=I.validate_policy work graph scope sources
                  (#semantic_limits request)
                val _=if I.work_policy work = #work_limit request
                  then ()else raise ERR "prepare_children_first_with_policy"
                    "retained Work limit differs"
                (* D.start is the third Ready getter on the SAME meter. *)
                val started=D.start sources supplied
                val _=session:=SOME started
                val contract=NC.capture work (#native_limits request)
                val _=D.discover_with_policy work started
                  (fn actual=>discover work contract actual)
                val validation=W.preprocessing_with_policy work started
                val _=if Portable.pointer_eq
                    (GP.original_sources validation,sources)andalso
                    GP.source_nodes validation=S.assumption_nodes sources @
                      [S.denied_goal_node sources]then ()else
                  raise ERR "prepare_children_first_with_policy"
                    "original Source occurrence prefix changed"
                val invocation=PolicyInvocation
                  {request=request,session=started,work=work,
                   native_contract=contract,translation=ref NONE,
                   replay_started=ref false}
            in {work=work,invocation=invocation}end
      in prepare()handle primary=>
        (Option.app (fn s=>(W.close s handle _=>())) (!session);
         I.close work;(G.close_scope graph scope handle _=>());
         raise primary)end
  (* Header comparison precedes retained NC, Source or GP activation. *)
  fun validate_with_policy expected
      (PolicyInvocation{work,session,native_contract,...})=
    ((if Portable.pointer_eq(expected,work)then ()else
        raise ERR "validate_with_policy" "different original Work";
      NC.validate_for expected native_contract;
      W.validate_with_policy expected session)
     handle primary=>(I.close expected;raise primary))
  fun source_session_with_policy_for expected
      (saved as PolicyInvocation{session,...})=
    (validate_with_policy expected saved;session)
  fun preprocessing_with_policy_for expected
      (saved as PolicyInvocation{session,...})=
    (validate_with_policy expected saved;
     W.preprocessing_with_policy expected session)
  fun native_contract_with_policy_for expected
      (saved as PolicyInvocation{native_contract,...})=
    (validate_with_policy expected saved;native_contract)
  fun processed_goal_with_policy expected saved=
    GP.processed_goal(preprocessing_with_policy_for expected saved)
  fun original_sources_with_policy_for expected
      (saved as PolicyInvocation{session,...})=
    (validate_with_policy expected saved;W.sources session)
  fun admit_translation_with_policy expected
      (saved as PolicyInvocation{translation=selected,...}) translation=
    ((validate_with_policy expected saved;
      (case !selected of NONE=>()|SOME previous=>
        if Portable.pointer_eq(previous,translation)then ()else
          raise ERR "admit_translation_with_policy"
            "different invocation translation");
      if null(SmtLib.translation_definitions translation)then
        selected:=SOME translation else
        raise ERR "admit_translation_with_policy"
          "original Source route needs checked emitted-definition integration";
      validate_with_policy expected saved)
     handle primary=>(I.close expected;raise primary))
  fun close_original_with_policy expected
      (PolicyInvocation{work,session,...})=
    ((if Portable.pointer_eq(expected,work)then ()else
        raise ERR "close_original_with_policy" "different original Work";
      let val session_close=Exn.capture W.close session
          val work_close=Exn.capture I.close expected
      in Exn.release session_close;Exn.release work_close end)
     handle primary=>(I.close expected;raise primary))
  (* This immutable audit deliberately does not call validate_with_policy:
     accepted late results cannot reactivate retired Work, NC, Source or GP. *)
  fun audit_original_with_policy expected
      (PolicyInvocation{work,session,...}) original theorem=
    ((if Portable.pointer_eq(expected,work)then ()else
        raise ERR "audit_original_with_policy" "different original Work";
      W.audit_with_policy expected session original theorem)
     handle primary=>(I.close expected;raise primary))

  type policy_replay_options=
    {profiles:G.policy_opaque_profile list,
     check_type:Type.hol_type -> unit,ordinal:int}
  val _=CPC_ProofParser.parse_graph_translation_packet_with_version_with_policy
  val _=Z3_ProofParser.parse_graph_translation_packet_with_version_with_policy
  val _=SmtReplaySourceConsumerSession.prove_cpc_with_policy
  val _=SmtReplaySourceConsumerSession.prove_z3_with_policy
  structure CP=CPC_ProofParser
  structure ZP=Z3_ProofParser

  fun replay_options_with_policy
      ({construction_limits,...}:policy_request) graph scope
      (translation:SmtLib.translation):SmtLib_GraphFrontend.policy_options=
    {graph=graph,scope=scope,logic= #logic translation,sources=[],
     sorts=Redblackmap.mkDict String.compare,binder_lists=[],
     import_limit= #import_limit construction_limits,
     literal_limit= #literal_limit construction_limits,
     binder_limit= #binder_limit construction_limits,
     recipe_limits= #recipe_limits construction_limits,
     special=fn _=>fn _=>NONE,ascribed=fn _=>fn _=>fn _=>NONE}

  (* This latch belongs to the opaque invocation that captured the one NC.
     It is claimed before translation checks or parsing, including failures.
     Neither a caller packet nor a callback supplies an occurrence map. *)
  fun claim_policy_replay
      (PolicyInvocation{replay_started,...})=
    if !replay_started then raise ERR "policy_replay"
      "invocation replay is one-shot"else replay_started:=true

  fun cvc_original_with_policy_parser parse_packet expected saved
      translation version
      ({profiles,check_type,ordinal}:policy_replay_options) input=
    let
      (* This header check is outside owned cleanup: a foreign expected
         Work must not close the held invocation's original Source scope. *)
      val _=validate_with_policy expected saved
      val PolicyInvocation{request,session,native_contract,...}=saved
      val graph=W.graph session val scope=W.scope session
      val packet=ref NONE
      fun replay ()=
        let
          val _=claim_policy_replay saved
          (* Existing emitted-definition refusal is retained verbatim in
             admit_translation_with_policy. No finite emitter is reused. *)
          val _=admit_translation_with_policy expected saved translation
          val parsed=
            parse_packet
              (replay_options_with_policy request graph scope translation)
              translation version input
              (* The paid input owner may reject after parser return.
                 Publish before its callback exits so this packet is
                 still closed by the outer exception bracket. *)
              (fn parsed => packet:=SOME parsed)
            handle primary=>raise ParseFailure primary
          val _=if Portable.pointer_eq(Q.graph parsed,graph)andalso
              Q.scope parsed=scope andalso Q.solver parsed="cvc5"andalso
              #requested(Q.versions parsed)=version then ()else
            raise ERR "cvc_original_with_policy" "foreign parser packet"
          val _=validate_with_policy expected saved
        in D.prove_cpc_with_policy expected native_contract session
          {packet=parsed,profiles=profiles,
           check_type=check_type,ordinal=ordinal}
          handle primary=>raise ReplayFailure primary end
      val outcome=Exn.capture replay ()
      val packet_close=Exn.capture(fn()=>Option.app Q.close(!packet))()
      val invocation_close=Exn.capture
        (fn()=>close_original_with_policy expected saved)()
    in case outcome of Exn.Exn primary=>raise primary
      | Exn.Res theorem=>
          (Exn.release packet_close;Exn.release invocation_close;theorem)
    end

  fun cvc_original_with_policy expected saved translation version
      options input =
    let
      fun parse_packet parse_options selected requested supplied publish =
        let val parsed =
              CP.parse_graph_translation_packet_with_version_with_policy
                parse_options selected requested supplied
        in publish parsed;parsed end
    in cvc_original_with_policy_parser parse_packet
      expected saved translation version options input end

  (* The paid supplier remains private to this checked receiver. I's
     opaque receipt authenticates the same OriginalPortfolio and Source;
     no public callback can substitute an unmetered input function. *)
  fun cvc_original_with_policy_paid expected saved translation version
      options receipt =
    let
      val from_input =
        CP.parse_graph_translation_packet_with_version_with_policy_from_input
      fun parse_packet parse_options selected requested held publish =
        I.with_cpc_certificate_input expected held
          (fn supplier =>
            let val parsed =
                  from_input parse_options selected requested supplier
            in publish parsed;parsed end)
    in cvc_original_with_policy_parser parse_packet
      expected saved translation version options receipt end

  fun z3_original_with_policy_parser parse_packet expected saved
      translation version
      ({profiles,check_type,ordinal}:policy_replay_options) input=
    let
      val _=validate_with_policy expected saved
      val PolicyInvocation{request,session,native_contract,...}=saved
      val graph=W.graph session val scope=W.scope session
      val packet=ref NONE
      fun replay ()=
        let
          val _=claim_policy_replay saved
          val _=admit_translation_with_policy expected saved translation
          val parsed=
            parse_packet
              (replay_options_with_policy request graph scope translation)
              translation version input
              (fn parsed => packet:=SOME parsed)
            handle primary=>raise ParseFailure primary
          val _=if Portable.pointer_eq(Q.graph parsed,graph)andalso
              Q.scope parsed=scope andalso Q.solver parsed="Z3"andalso
              #requested(Q.versions parsed)=version then ()else
            raise ERR "z3_original_with_policy" "foreign parser packet"
          val _=validate_with_policy expected saved
        in D.prove_z3_with_policy expected native_contract session
          {packet=parsed,profiles=profiles,
           check_type=check_type,ordinal=ordinal}
          handle primary=>raise ReplayFailure primary end
      val outcome=Exn.capture replay ()
      val packet_close=Exn.capture(fn()=>Option.app Q.close(!packet))()
      val invocation_close=Exn.capture
        (fn()=>close_original_with_policy expected saved)()
    in case outcome of Exn.Exn primary=>raise primary
      | Exn.Res theorem=>
          (Exn.release packet_close;Exn.release invocation_close;theorem)
    end

  fun z3_original_with_policy expected saved translation version
      options input =
    let
      fun parse_packet parse_options selected requested supplied publish =
        let val parsed =
              ZP.parse_graph_translation_packet_with_version_with_policy
                parse_options selected requested supplied
        in publish parsed;parsed end
    in z3_original_with_policy_parser parse_packet
      expected saved translation version options input end

  fun z3_original_with_policy_paid expected saved translation version
      options receipt =
    let
      val from_input =
        ZP.parse_graph_translation_packet_with_version_with_policy_from_input
      fun parse_packet parse_options selected requested held publish =
        I.with_z3_certificate_input expected held
          (fn supplier =>
            let val parsed =
                  from_input parse_options selected requested supplier
            in publish parsed;parsed end)
    in z3_original_with_policy_parser parse_packet
      expected saved translation version options receipt end
end
