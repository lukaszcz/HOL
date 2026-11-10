(* Copyright (c) 2026 The HOL4 contributors. *)
structure SmtReplayWrapperSession :> SmtReplayWrapperSession =
struct
  structure G = SmtReplayGraph
  structure S = SmtReplaySource
  structure GP = SmtLib_GraphPreprocess
  val ERR = Feedback.mk_HOL_ERR "SmtReplayWrapperSession"
  datatype phase = Preparing | Discovering | Prepared | Replaying
    | Accepted of Thm.thm
    | Retired of Thm.thm option
  datatype session = Session of
    {graph : G.graph,scope : G.scope,sources : S.sources,
     original : Abbrev.goal,validation : GP.validation option ref,
     phase : phase ref,
     owned_work : SmtReplayInvocationWork.portfolio option ref}
  fun exact ((lefts,left),(rights,right)) =
    Portable.pointer_eq (left,right) andalso
    List.length lefts = List.length rights andalso
    ListPair.allEq Portable.pointer_eq (lefts,rights)
  fun active (Session {graph,scope,phase,...}) =
    (case !phase of Retired _ => raise ERR "active" "wrapper session closed"
     | _ => G.validate_scope graph scope)
  fun close (Session {graph,scope,phase,...}) =
    case !phase of Retired _ => ()
    | Accepted theorem =>
        (phase := Retired (SOME theorem);G.close_scope graph scope)
    | _ => (phase := Retired NONE;G.close_scope graph scope)
  fun poison (Session {graph,scope,phase,...}) =
    (phase := Retired NONE;G.close_scope graph scope)
  fun checked session action =
    (active session;action ()) handle primary =>
      ((poison session handle _ => ());raise primary)
  fun checked_validation graph scope sources validation =
    let
      val _ = if Portable.pointer_eq
          (GP.original_sources validation,sources) then () else
        raise ERR "prepare" "preprocessing has a different Source owner"
      val _ = List.app (fn node =>
        if G.scope_visible graph scope (G.node_scope graph node) then ()
        else raise ERR "prepare" "foreign preprocessing root")
        (GP.roots validation @ GP.source_nodes validation)
    in () end
  fun start sources original =
    let
      val graph = S.owning_graph sources
      val scope = S.owning_scope sources
      val _ = if exact (S.original_goal sources,original) then () else
        raise ERR "start" "original Source occurrence portfolio differs"
    in Session {graph = graph,scope = scope,sources = sources,
      original = original,validation = ref NONE,phase = ref Preparing,
      owned_work = ref NONE} end
  fun discover
      (session as Session {graph,scope,sources,validation,phase,...}) callback =
    checked session (fn () => case !phase of
      Preparing =>
        let
          val _ = phase := Discovering
          val prepared = callback sources
          (* A caught reentrant refusal or close cannot resurrect a session. *)
          val _ = active session
          val _ = case !phase of Discovering => ()
            | _ => raise ERR "discover" "preprocessing discovery retired"
          val _ = checked_validation graph scope sources prepared
          val _ = active session
          val _ = case !phase of Discovering => ()
            | _ => raise ERR "discover" "preprocessing discovery retired"
          val _ = validation := SOME prepared
          val _ = phase := Prepared
        in () end
    | _ => raise ERR "discover" "preprocessing discovery is not one-shot")
  fun prepare graph scope sources original validation =
    let
      val _ = G.validate_scope graph scope
      val _ = if exact (S.original_goal sources,original) then () else
        raise ERR "prepare" "original Source occurrence portfolio differs"
      val _ = checked_validation graph scope sources validation
    in Session {graph = graph,scope = scope,sources = sources,
      original = original,validation = ref (SOME validation),
      phase = ref Prepared,owned_work = ref NONE} end
  fun graph (session as Session {graph,...}) = (active session;graph)
  fun scope (session as Session {scope,...}) = (active session;scope)
  fun sources (session as Session {sources,...}) = (active session;sources)
  fun preprocessing (session as Session {validation,...}) =
    (active session;case !validation of SOME prepared => prepared
     | NONE => raise ERR "preprocessing" "preprocessing is not prepared")
  fun processed_goal session = GP.processed_goal (preprocessing session)
  fun roots session = GP.roots (preprocessing session) @
    GP.source_nodes (preprocessing session)
  fun begin_replay (session as Session {phase,...}) =
    checked session (fn () => case !phase of
      Prepared => phase := Replaying
    | _ => raise ERR "begin_replay" "wrapper replay is not one-shot")
  fun accept (session as Session {sources,phase,...}) theorem =
    checked session (fn () => case !phase of
      Replaying => (S.check_goal sources theorem;phase := Accepted theorem)
    | _ => raise ERR "accept" "wrapper result outside replay lifetime")
  fun audit (session as Session {sources,original,phase,...}) goal theorem =
    let
      val _ = if exact (original,goal) then () else
        raise ERR "audit" "solver invocation original goal differs"
      fun retained proof = if Portable.pointer_eq (proof,theorem) then ()
        else raise ERR "audit" "solver returned a different theorem"
    in case !phase of
        Accepted proof => (active session;retained proof;
          S.check_goal sources theorem)
      | Retired (SOME proof) => retained proof
      | _ => raise ERR "audit" "solver result has not been Source-checked"
    end handle primary =>
      ((poison session handle _ => ());raise primary)
  structure I = SmtReplayInvocationWork
  val _ = SmtLib_GraphPreprocess.validate_with_work
  fun compare_original_work expected
      (Session {graph,scope,sources,...}) =
    let val original = I.original_sources expected
        val owner = S.owning_graph original val root = S.owning_scope original
        val limits = I.semantic_limits expected
        val _ = I.validate expected owner root original limits
    in if Portable.pointer_eq (graph,owner) andalso scope = root andalso
        Portable.pointer_eq (sources,original) then () else
      raise ERR "validate_with_work" "different original invocation" end
  fun retained_work expected (Session {owned_work,...}) =
    case !owned_work of SOME actual =>
      if Portable.pointer_eq (expected,actual) then () else
        raise ERR "retained_work" "different original Work"
    | NONE => raise ERR "retained_work" "original Work was not retained"
  fun validate_with_work expected
      (session as Session {validation,...}) =
    ((retained_work expected session;compare_original_work expected session;
      Option.app (GP.validate_with_work expected) (!validation);active session)
     handle primary => (I.close expected;raise primary))
  fun discover_with_work
      (session as Session
        {graph,scope,sources,validation,phase,owned_work,...}) callback =
    checked session (fn () => case !phase of
      Preparing =>
        let val _ = phase := Discovering
            val {work,preprocessing = prepared} = callback sources
            val _ = (let
              val _ = compare_original_work work session
              val _ = active session
              val _ = case !phase of Discovering => ()
              | _ => raise ERR "discover_with_work"
                  "preprocessing discovery retired"
              val _ = GP.validate_with_work work prepared
              val _ = checked_validation graph scope sources prepared
              val _ = compare_original_work work session
              val _ = active session
              val _ = case !phase of Discovering => ()
              | _ => raise ERR "discover_with_work"
                  "preprocessing discovery retired"
              val _ = owned_work := SOME work
              val _ = validation := SOME prepared
              val _ = phase := Prepared
            in () end handle primary => (I.close work;raise primary))
        in work end
    | _ => raise ERR "discover_with_work"
        "preprocessing discovery is not one-shot")
  fun preprocessing_with_work expected session =
    (validate_with_work expected session;
     let val result = preprocessing session
         val _ = GP.validate_with_work expected result
     in result end)
  fun processed_goal_with_work expected session =
    GP.processed_goal (preprocessing_with_work expected session)

  (* After close, ONLY cached Work association plus old accepted-result
     pointer/goal audit is used. No retired Work or G/GP/S is reactivated. *)
  fun audit_with_work expected session original theorem =
    ((retained_work expected session;audit session original theorem)
     handle primary => (I.close expected;raise primary))

  (* Compare expected Work/Source ownership before touching a held session's
     Scope or GP backing. Existing finite entry programmes stay literal. *)
  fun compare_original_policy expected
      (Session {graph,scope,sources,...})=
    let val original=I.original_sources expected
        val owner=S.owning_graph original val root=S.owning_scope original
        val limits=I.semantic_policy expected
        val _=I.validate_policy expected owner root original limits
    in if Portable.pointer_eq(graph,owner)andalso scope=root andalso
        Portable.pointer_eq(sources,original)then ()else
      raise ERR "validate_with_policy" "different original invocation" end
  fun validate_with_policy expected
      (session as Session {validation,...})=
    ((retained_work expected session;compare_original_policy expected session;
      Option.app(GP.validate_with_policy expected)(!validation);active session)
     handle primary=>(I.close expected;raise primary))

  (* Work already exists and is fixed BEFORE the callback. Neither a
     returned GP nor a reentrant callback can replace that actual owner. *)
  fun discover_with_policy expected
      (session as Session
        {graph,scope,sources,validation,phase,owned_work,...}) callback=
    ((compare_original_policy expected session;
      checked session (fn()=>case !phase of Preparing=>
        let val _=case !owned_work of NONE=>owned_work:=SOME expected
              | SOME actual=>if Portable.pointer_eq(actual,expected)then ()else
                  raise ERR "discover_with_policy" "different original Work"
            val _=phase:=Discovering
            val prepared=callback sources
            fun discovering ()=
              (compare_original_policy expected session;active session;
               case !phase of Discovering=>()|_=>
                 raise ERR "discover_with_policy"
                   "preprocessing discovery retired")
            val _=discovering()
            val _=GP.validate_with_policy expected prepared
            val _=checked_validation graph scope sources prepared
            val _=discovering()
            val _=validation:=SOME prepared val _=phase:=Prepared
        in ()end
      | _=>raise ERR "discover_with_policy"
          "preprocessing discovery is not one-shot"))
     handle primary=>(I.close expected;raise primary))
  fun preprocessing_with_policy expected session=
    (validate_with_policy expected session;
     let val result=preprocessing session
         val _=GP.validate_with_policy expected result
     in result end)
  fun processed_goal_with_policy expected session=
    GP.processed_goal(preprocessing_with_policy expected session)
  (* Retired accepted results use only exact cached Work and theorem/Goal
     pointers, as on the finite route. No retired graph is reopened. *)
  fun audit_with_policy expected session original theorem=
    ((retained_work expected session;audit session original theorem)
     handle primary=>(I.close expected;raise primary))
end
