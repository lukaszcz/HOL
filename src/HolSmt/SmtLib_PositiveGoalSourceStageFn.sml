(* The ordered-assumption prefix shared by the Owned and Compact positive
   Goal Source stages: owner record, retirement, metering and `begin`.  The
   traversal supplies the persistent carrier owner and the diagnostic origin
   is the client's own, so each stage keeps its lifecycle and messages. *)
signature SmtLib_PositiveGoalSourceStageInput =
sig
  type owner
  val begin : SmtReplayInvocationWork.portfolio ->
    {check_type : Type.hol_type -> unit,
     scope_opened : SmtReplayGraph.scope -> unit} -> owner
  val close : owner -> unit
  (* Origin of every diagnostic, as Feedback.mk_HOL_ERR takes it. *)
  val origin : string
end

functor SmtLib_PositiveGoalSourceStageFn
    (T : SmtLib_PositiveGoalSourceStageInput) =
struct
  structure G = SmtReplayGraph
  structure S = SmtReplaySource
  structure W = SmtReplayInvocationWork
  val ERR = Feedback.mk_HOL_ERR T.origin
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
end
