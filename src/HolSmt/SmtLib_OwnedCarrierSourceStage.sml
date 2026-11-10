(* SAME original Source/Work checked carrier + complete-beta substage.
   All preprocessing/default/query-parity and global/private costs stay open. *)
structure SmtLib_OwnedCarrierSourceStage :> SmtLib_OwnedCarrierSourceStage =
struct
  structure G = SmtReplayGraph
  structure S = SmtReplaySource
  structure W = SmtReplayInvocationWork
  structure T = SmtLib_OwnedCarrierTraversal
  structure F = SmtLib_GraphSourcePortfolio
  structure GP = SmtLib_GraphPreprocess
  structure P = SmtReplayProof
  val _ = SmtLib_OwnedCarrierTraversal.source_conversion
  val _ = SmtLib_GraphSourcePortfolio.binder_transport
  val _ = SmtLib_GraphPreprocess.from_portfolio
  val ERR = Feedback.mk_HOL_ERR "SmtLib_OwnedCarrierSourceStage"
  datatype phase = Ready | Building | Complete | Retired
  type row = {occurrence : int,index : int,original : G.source,view : G.source}
  datatype owner = Owner of
    {graph : G.graph,root : G.scope,sources : S.sources,work : W.portfolio,
     limits : W.limits,epoch : int,traversal : T.owner,
     rows : row list,phase : phase ref}
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
  fun begin work {views,check_type,scope_opened} =
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
          val originals = S.reconciliation_sources sources
          fun count [] n = n
            | count (_::rest) n = (W.spend work 1;count rest (n+1))
          val total = count originals 0
          val _ = if total > 0 then () else
            raise ERR "begin" "original denial missing"
          fun rows [] [] _ = []
            | rows ((original : G.source)::rest)
                ((view : G.source)::more) occurrence =
              let val _ = guard ()
                  val _ = G.validate_opened_view graph root
                    (#node original) view
                  val _ = guard ()
                  (* Exactly the retained row and list incidence; private
                     getters/constructor work is not a global cost receipt. *)
                  val _ = W.spend work 2
                  val index = if occurrence = 0 then total-1 else occurrence-1
              in {occurrence = occurrence,index = index,
                  original = original,view = view} ::
                 rows rest more (occurrence+1) end
            | rows _ _ _ = raise ERR "begin" "exact Source view count differs"
          val result = rows originals views 0
          val _ = guard ()
        in result end)
      val rows = prepare () handle primary => (W.close work;raise primary)
      val traversal = T.begin work {check_type = check_type,
        scope_opened = scope_opened}
        handle primary => (W.close work;raise primary)
      val owner = Owner {graph = graph,root = root,sources = sources,
        work = work,limits = limits,epoch = epoch,traversal = traversal,
        rows = rows,phase = ref Ready}
    in protected owner (fn () => (active owner;owner)) end
  fun build (owner as Owner
      {graph,root,sources,work,limits,traversal,rows,phase,...}) =
    protected owner (fn () =>
      let
        val _ = active owner
        val _ = if !phase = Ready then phase := Building else
          raise ERR "build" "stage already used or reentrant"
        fun original ({index,original,...} : row) = meta owner (fn () =>
          let val _ = W.spend work 1
              val fact = F.original graph root sources index
          in if F.endpoint fact = #node original then fact else
            raise ERR "build" "denial/assumption occurrence mapping differs"
          end)
        fun process (row as {occurrence,view,...} : row) =
          let val fact = original row val _ = active owner
              val result = T.run_owned traversal
                {occurrence = occurrence,view = view}
              val _ = active owner
          in case result of NONE => fact
            | SOME converted =>
              let val plan = T.source_conversion traversal converted
                  val _ = active owner
              in meta owner (fn () =>
                let val _ = W.spend work 1
                    val _ = P.validate_conversion graph root
                      (#template_limit limits) plan
                in F.binder_transport graph root plan fact end) end
          end
        val (first,rest) = case rows of denied::assumptions =>
            (process denied,List.map process assumptions)
          | [] => raise ERR "build" "original denial missing"
        (* No new negation, raw import or arbitrary goal override: the query
           goal is the existing child of the exact original negation head.
           Initial denial retains its original input-cap policy unchanged. *)
        val goal = meta owner (fn () =>
          let val old = case rows of ({original,...} : row)::_ => #node original
                | [] => raise ERR "build" "denial missing"
              val old_head = case G.view graph old of G.Application (f,_) => f
                | _ => raise ERR "build" "original denial not application"
              val _ = W.spend work 2
          in case G.view graph (F.endpoint first) of G.Application (head,body) =>
              if head = old_head then body else
                raise ERR "build" "processed denial changed negation head"
            | _ => raise ERR "build" "processed denial not negation" end)
        val validation = meta owner (fn () =>
          let val checked = F.validate graph root sources
                {assumptions = rest,goal = goal,denied = first,
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
