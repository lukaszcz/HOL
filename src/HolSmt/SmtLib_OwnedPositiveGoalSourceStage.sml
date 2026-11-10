(* SAME original Source and Work; assertions precede positive Goal.
   Whole-assumption admission compatibility and full pipeline stay open. *)
structure SmtLib_OwnedPositiveGoalSourceStage :>
    SmtLib_OwnedPositiveGoalSourceStage =
struct
  structure G = SmtReplayGraph
  structure S = SmtReplaySource
  structure W = SmtReplayInvocationWork
  structure T = SmtLib_OwnedCarrierTraversal
  structure F = SmtLib_GraphSourcePortfolio
  structure GP = SmtLib_GraphPreprocess
  structure P = SmtReplayProof
  val _ = SmtReplaySource.goal_source
  val _ = SmtLib_OwnedCarrierTraversal.run_goal_owned
  val _ = SmtLib_OwnedCarrierTraversal.denial_conversion
  val _ = SmtLib_GraphSourcePortfolio.binder_transport
  val _ = SmtLib_GraphPreprocess.from_portfolio
  val ERR = Feedback.mk_HOL_ERR "SmtLib_OwnedPositiveGoalSourceStage"
  datatype phase = Ready | Building | Complete | Retired
  datatype assumption_mode = LegacyViews | OriginalProvenance
  type row = {occurrence : int,index : int,original : G.source,
    view : G.source option}
  datatype owner = Owner of
    {graph : G.graph,root : G.scope,sources : S.sources,work : W.portfolio,
     limits : W.limits,epoch : int,traversal : T.owner,rows : row list,
      assumption_mode : assumption_mode,
     goal_view : G.source option,denial_view : G.source option,
     denial : G.source,denial_index : int,phase : phase ref}
  fun close (Owner {work,traversal,phase,...}) =
    (phase := Retired;T.close traversal;W.close work)
  fun protected owner action = action () handle primary =>
    (close owner;raise primary)
  fun active (Owner {graph,root,sources,work,limits,epoch,phase,...}) =
    (if !phase = Retired then raise ERR "owner" "stage retired" else ();
     W.validate work graph root sources limits;
     if Type.type_epoch () = epoch then () else
       raise ERR "owner" "Type retirement epoch changed")
  fun meta (owner as Owner {work,...}) action = protected owner (fn () =>
    W.with_step work (fn () =>
      (active owner;let val value = action () val _ = active owner
                    in value end)))
  fun begin_internal mode work {assumption_views,goal_view,denial_view,
                               check_type,scope_opened} =
    let
      val sources = W.original_sources work
      val graph = S.owning_graph sources val root = S.owning_scope sources
      val limits = W.semantic_limits work val epoch = Type.type_epoch ()
      fun guard () =
        (W.validate work graph root sources limits;
         if Type.type_epoch () = epoch then () else
           raise ERR "begin" "Type retirement epoch changed")
      fun prepare () = W.with_step work (fn () =>
        let
          val _ = guard ()
          val (denial,assumptions) = case S.reconciliation_sources sources of
              denied::rest => (denied,rest)
            | [] => raise ERR "begin" "original denial missing"
          fun rows [] [] _ = []
            | rows ((original : G.source)::rest)
                ((view : G.source option)::more) index =
              let val _ = guard ()
                  val _ = case view of NONE => () | SOME opened =>
                    G.validate_opened_view graph root (#node original) opened
                  val _ = guard () val _ = W.spend work 2
              in {occurrence = index+1,index = index,
                  original = original,view = view} :: rows rest more (index+1)
              end
            | rows _ _ _ = raise ERR "begin" "assumption view count differs"
          val result = rows assumptions assumption_views 0
          fun count [] n = n
            | count (_::rest) n = (W.spend work 1;count rest (n+1))
          val total = count result 0
          val _ = case (goal_view,denial_view) of
              (SOME positive,SOME negative) =>
                (G.validate_opened_view graph root
                   (#node (S.goal_source sources)) positive;
                 guard ();
                 G.validate_opened_view graph root (#node denial) negative;
                 guard ();W.spend work 2)
            | (SOME _,NONE) => raise ERR "begin"
                "opened positive Goal requires original denial view"
            | (NONE,SOME negative) =>
                (G.validate_opened_view graph root (#node denial) negative;
                 guard ();W.spend work 1)
            | (NONE,NONE) => ()
          val _ = guard ()
        in (result,denial,total) end)
      val (rows,denial,total) = prepare ()
        handle primary => (W.close work;raise primary)
      val traversal = T.begin work {check_type = check_type,
        scope_opened = scope_opened}
        handle primary => (W.close work;raise primary)
      val owner = Owner {graph = graph,root = root,sources = sources,
        work = work,limits = limits,epoch = epoch,traversal = traversal,
        rows = rows,assumption_mode = mode,
        goal_view = goal_view,denial_view = denial_view,
        denial = denial,denial_index = total,phase = ref Ready}
    in protected owner (fn () => (active owner;owner)) end
  fun begin work {assumption_views,goal_view,denial_view,
                  check_type,scope_opened} =
    begin_internal LegacyViews work
      {assumption_views = List.map SOME assumption_views,
       goal_view = goal_view,denial_view = denial_view,
       check_type = check_type,scope_opened = scope_opened}
  fun begin_provenance work input =
    begin_internal OriginalProvenance work input
  fun build (owner as Owner
      {graph,root,sources,work,limits,traversal,rows,phase,assumption_mode,
       goal_view,denial_view,denial,denial_index,...}) =
    protected owner (fn () =>
      let
        val _ = active owner
        val _ = if !phase = Ready then phase := Building else
          raise ERR "build" "stage already used or reentrant"
        fun original index node = meta owner (fn () =>
          let val _ = W.spend work 1
              val fact = F.original graph root sources index
          in if F.endpoint fact = node then fact else
            raise ERR "build" "original occurrence mapping differs" end)
        fun transport plan fact = meta owner (fn () =>
          (W.spend work 1;
           P.validate_conversion graph root (#template_limit limits) plan;
           F.binder_transport graph root plan fact))
        fun process ({occurrence,index,original = saved,view} : row) =
          let val fact = original index (#node saved)
              val result = case assumption_mode of
                  OriginalProvenance => T.run_assumption_owned traversal
                    {occurrence = occurrence,view = view}
                | LegacyViews => (case view of SOME opened =>
                    T.run_owned traversal
                      {occurrence = occurrence,view = opened}
                  | NONE => raise ERR "build" "legacy opened view absent")
              val _ = active owner
          in case result of NONE => fact | SOME converted =>
            let val plan = T.source_conversion traversal converted
                val _ = active owner
            in transport plan fact end end
        (* Ordered assertions consume the SAME persistent traversal owner
           before positive Goal. The positive record never becomes P.Source. *)
        val assumptions = List.map process rows
        val denied = original denial_index (#node denial)
        val result = T.run_goal_owned traversal {view = goal_view}
        val _ = active owner
        val (goal,negative) = case result of NONE =>
            (#node (S.goal_source sources),denied)
          | SOME converted =>
            let val {target,...} = T.canonical_endpoints traversal converted
                val view = case denial_view of SOME view => view
                  | NONE => raise ERR "build" "denial view missing"
                val plan = T.denial_conversion traversal converted
                  {denial_view = view}
                val _ = active owner
            in (target,transport plan denied) end
        val validation = meta owner (fn () =>
          let val checked = F.validate graph root sources
                {assumptions = assumptions,goal = goal,denied = negative,
                 template_limit = #template_limit limits}
              val result = GP.from_portfolio checked
              val _ = if Portable.pointer_eq
                  (GP.original_sources result,sources) andalso
                  GP.source_nodes result = S.assumption_nodes sources @
                    [S.denied_goal_node sources] then () else
                raise ERR "build" "original Source prefix changed"
          in result end)
        val _ = active owner val _ = phase := Complete
      in validation end)
end
