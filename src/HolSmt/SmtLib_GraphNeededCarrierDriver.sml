(* Copyright (c) 2026 The HOL4 contributors. *)
structure SmtLib_GraphNeededCarrierDriver :>
    SmtLib_GraphNeededCarrierDriver =
struct
  structure G = SmtReplayGraph
  structure S = SmtReplaySource
  structure W = SmtReplayInvocationWork
  structure F = SmtLib_GraphSourcePortfolio
  structure GP = SmtLib_GraphPreprocess
  structure N = SmtLib_GraphNeededTheorems
  structure X = SmtLib_GraphSelectedAuxiliary
  structure T = SmtLib_CompactCarrierScheduler
  val _ = SmtLib_CompactCarrierScheduler.run_aux_owned
  val _ = SmtLib_CompactCarrierScheduler.normalization_ordinal
  val _ = SmtLib_GraphNeededTheorems.pending_selections
  val _ = SmtLib_GraphSelectedAuxiliary.prepare
  val ERR = Feedback.mk_HOL_ERR "SmtLib_GraphNeededCarrierDriver"
  datatype phase = Ready | Building | Complete | Retired
  datatype owner = Owner of
    {work : W.portfolio,graph : G.graph,root : G.scope,sources : S.sources,
     limits : W.limits,epoch : int,symbols : int,scheduler : T.owner,
     portfolio : F.validation,needed : N.owner,
     check_type : Type.hol_type -> unit,phase : phase ref}
  fun close (Owner {work,scheduler,phase,...}) =
    (phase := Retired;T.close scheduler;W.close work)
  fun protected owner action = action () handle primary =>
    (close owner;raise primary)
  fun active (Owner {work,graph,root,sources,limits,epoch,symbols,
                     scheduler,portfolio,phase,...}) =
    (if !phase = Retired then raise ERR "active" "driver retired" else ();
     W.validate work graph root sources limits;
     T.validate_for work scheduler;
     F.validate_for graph root sources portfolio;
     if Type.type_epoch () = epoch andalso Term.term_epoch () = symbols
     then () else raise ERR "active" "type or term retirement changed")
  fun begin work {scheduler,portfolio,check_type} =
    let
      val sources = W.original_sources work
      val graph = S.owning_graph sources val root = S.owning_scope sources
      val limits = W.semantic_limits work
      val _ = W.validate work graph root sources limits
      (* Expected owner before any scheduler or foreign portfolio getter. *)
      val _ = T.validate_for work scheduler
      val _ = F.validate_for graph root sources portfolio
      val epoch = Type.type_epoch () val symbols = Term.term_epoch ()
      fun backing () =
        (W.validate work graph root sources limits;
         T.validate_for work scheduler;
         F.validate_for graph root sources portfolio;
         if Type.type_epoch () = epoch andalso Term.term_epoch () = symbols
         then () else raise ERR "begin" "policy retirement changed")
      fun checked_type ty = (backing ();check_type ty;backing ())
      val needed = N.begin work
        {portfolio = portfolio,check_type = checked_type}
      val owner = Owner {work = work,graph = graph,root = root,
        sources = sources,limits = limits,epoch = epoch,
        symbols = symbols,scheduler = scheduler,
        portfolio = portfolio,needed = needed,check_type = check_type,
        phase = ref Ready}
    in protected owner (fn () => (active owner;owner)) end
    handle primary => (W.close work;raise primary)
  fun meta (owner as Owner {work,...}) action = protected owner (fn () =>
    W.with_step work (fn () =>
      (active owner;W.spend work 1;
       let val result = action () in active owner;result end)))
  fun policy owner check_type ty =
    (active owner;check_type ty;active owner)
  fun build (owner as Owner
      {work,graph,root,sources,limits,scheduler,needed,check_type,phase,...}) =
    protected owner (fn () =>
    let
      val _ = active owner
      val _ = if !phase = Ready then phase := Building else
        raise ERR "build" "driver already consumed or reentrant"
      fun batch pending =
        let
          (* N already aligned these opaque one-call selections with the
             exact originals in legacy theorem order. Never reselect. *)
          val selections = meta owner (fn () => N.pending_selections pending)
          fun reverse [] answer = answer
            | reverse (value :: rest) answer =
                (W.spend work 2;reverse rest (value :: answer))
          fun normalize [] accumulated =
                meta owner (fn () => reverse accumulated [])
            | normalize ((selected :
                  {selection : SmtLib_GraphNumericStock.selection,
                   ordinal : int}) :: rest) accumulated =
              let
                val _ = meta owner (fn () => W.spend work 1)
                val law = X.execute (X.prepare (X.begin work
                  {selection = #selection selected,
                   ordinal = #ordinal selected,
                   check_type = policy owner check_type}))
                val _ = active owner
                (* Identity also returns a genuine checked equality. No
                   unsupported or failed producer can become identity. *)
                val conversion = T.run_aux_owned scheduler {law = law}
                val _ = active owner
                val ordinal = T.normalization_ordinal scheduler
                val completed = N.normalize_result pending
                  {law = law,conversion = conversion,ordinal = ordinal}
                val _ = active owner
                val _ = meta owner (fn () => W.spend work 2)
              in normalize rest (completed :: accumulated) end
          val completed = normalize selections []
          val _ = active owner
        in N.resume pending completed end
      fun finish (N.NeedsNormalization pending) = finish (batch pending)
        | finish (N.Complete validation) =
          let val _ = meta owner (fn () =>
                if Portable.pointer_eq
                    (GP.original_sources validation,sources) andalso
                    GP.source_nodes validation = S.assumption_nodes sources @
                      [S.denied_goal_node sources] andalso
                    GP.template_limit validation =
                      SOME (#template_limit limits) then () else
                  raise ERR "build" "original Source or template changed")
              val _ = active owner
              val _ = phase := Complete
          in validation end
    in finish (N.collect needed) end)
end
