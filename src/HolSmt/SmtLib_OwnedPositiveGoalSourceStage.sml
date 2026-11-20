(* SAME original Source and Work; assertions precede positive Goal.
   Whole-assumption admission compatibility and full pipeline stay open. *)
structure SmtLib_OwnedPositiveGoalSourceStage :>
    SmtLib_OwnedPositiveGoalSourceStage =
struct
  structure T = SmtLib_OwnedCarrierTraversal
  structure F = SmtLib_GraphSourcePortfolio
  structure GP = SmtLib_GraphPreprocess
  structure P = SmtReplayProof
  val _ = SmtReplaySource.goal_source
  val _ = SmtLib_OwnedCarrierTraversal.run_goal_owned
  val _ = SmtLib_OwnedCarrierTraversal.denial_conversion
  val _ = SmtLib_GraphSourcePortfolio.binder_transport
  val _ = SmtLib_GraphPreprocess.from_portfolio
  structure Base = SmtLib_PositiveGoalSourceStageFn
    (struct open T val origin = "SmtLib_OwnedPositiveGoalSourceStage" end)
  (* G, S, W and ERR come from `open Base`. *)
  open Base
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
