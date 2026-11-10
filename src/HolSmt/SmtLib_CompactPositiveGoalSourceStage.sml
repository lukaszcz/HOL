(* SAME original Source and Work; assertions precede positive Goal.
   Whole-assumption admission compatibility and full pipeline stay open. *)
structure SmtLib_CompactPositiveGoalSourceStage :>
    SmtLib_CompactPositiveGoalSourceStage =
struct
  structure G = SmtReplayGraph
  structure S = SmtReplaySource
  structure W = SmtReplayInvocationWork
  structure T = SmtLib_CompactCarrierScheduler
  structure C = SmtReplayCanonGraph
  structure F = SmtLib_GraphSourcePortfolio
  structure GP = SmtLib_GraphPreprocess
  structure P = SmtReplayProof
  val _ = SmtReplaySource.goal_source
  val _ = SmtLib_CompactCarrierScheduler.run_goal_owned
  val _ = SmtLib_GraphSourcePortfolio.transport
  val _ = SmtLib_GraphPreprocess.from_portfolio
  val ERR = Feedback.mk_HOL_ERR "SmtLib_CompactPositiveGoalSourceStage"
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
  fun build_internal numeric (owner as Owner
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
           if C.graph_source plan = F.endpoint fact then () else
             raise ERR "transport" "different original occurrence endpoint";
           F.transport graph root plan fact))
        fun process ({occurrence,index,original = saved,view} : row) =
          let val fact = original index (#node saved)
              val result = case assumption_mode of
                  OriginalProvenance => T.run_assumption_owned traversal
                    {occurrence = occurrence,view = view}
                | LegacyViews => (case view of SOME opened =>
                    T.run_assumption_owned traversal
                      {occurrence = occurrence,view = SOME opened}
                  | NONE => raise ERR "build" "legacy opened view absent")
              val _ = active owner
          in case result of NONE => fact | SOME converted =>
            let val plan = T.graph_conversion_for traversal converted
                val _ = active owner
            in transport plan fact end end
        (* Ordered assertions consume the SAME persistent traversal owner
           before positive Goal. The positive record never becomes P.Source. *)
        val normalize = numeric owner
        fun normalize_fact fact = case normalize (F.endpoint fact) of
            NONE => fact
          | SOME plan => transport plan fact
        val assumptions = List.map (normalize_fact o process) rows
        val denied = original denial_index (#node denial)
        val result = T.run_goal_owned traversal {view = goal_view}
        val _ = active owner
        val (goal,negative) = case result of NONE =>
            (#node (S.goal_source sources),denied)
          | SOME converted =>
            let val positive = T.graph_conversion_for traversal converted
                val target = C.graph_result positive
                val plan = meta owner (fn () =>
                  let fun observe () = (active owner;W.spend work 1)
                      val (head,operand) = case G.view graph (#node denial) of
                          G.Application pair => pair
                        | _ => raise ERR "build" "original denial shape differs"
                      val _ = if operand = C.graph_source positive andalso
                          Term.same_const (G.representative graph head)
                            boolSyntax.negation then () else
                        raise ERR "build" "original denial constructor differs"
                      val left = C.graph_identity graph root
                        {observe = observe} head
                  in C.graph_application graph root
                    {source = #node denial,left = left,right = positive,
                     observe = observe} end)
                val _ = active owner
            in (target,transport plan denied) end
        val (goal,negative) = case normalize goal of NONE => (goal,negative)
          | SOME positive =>
            let val target = C.graph_result positive
                val plan = meta owner (fn () =>
                  let fun observe () = (active owner;W.spend work 1)
                      val denied = F.endpoint negative
                      val (head,operand) = case G.view graph denied of
                          G.Application pair => pair
                        | _ => raise ERR "build" "denial is not application"
                      val _ = if operand = C.graph_source positive then ()
                        else raise ERR "build" "numeric denial mismatch"
                      val left = C.graph_identity graph root
                        {observe = observe} head
                  in C.graph_application graph root
                    {source = denied,left = left,right = positive,
                     observe = observe} end)
            in (target,transport plan negative) end
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
  fun build owner = build_internal (fn _ => fn _ => NONE) owner
  fun build_integer_division owner {check_type} =
    build_internal (fn owner as Owner {work,...} =>
      let val convert = meta owner (fn () =>
            SmtLib_GraphIntegerDivision.conversion work
              {check_type = check_type})
      in fn node => meta owner (fn () => convert node) end) owner
  val _ = SmtLib_GraphNeededCarrierDriver.begin
  fun build_needed (owner as Owner {work,traversal,...}) {check_type} =
    protected owner (fn () =>
      let val preprocessed = build owner
          val portfolio = meta owner (fn () =>
            case GP.portfolio_validation preprocessed of SOME value => value
              | NONE => raise ERR "build_needed"
                  "stage lost its original dependency portfolio")
          val driver = SmtLib_GraphNeededCarrierDriver.begin work
            {scheduler = traversal,portfolio = portfolio,
             check_type = check_type}
          val result = SmtLib_GraphNeededCarrierDriver.build driver
          val _ = active owner
      in result end)

  (* Preparation is distinct from an executable legacy owner. In particular,
     retaining genuine views does not issue carrier conversions or a checked
     preprocessing portfolio. Those consumers still need policy entrypoints. *)
  structure RP = SmtReplayResourcePolicy
  structure PolicyScope = SmtReplayOwnedScopeReceipt
  type policy_row =
    {occurrence:IntInf.int,index:IntInf.int,original:G.source,
     view:G.source option}
  datatype policy_preparation = PolicyPreparation of
    {graph:G.graph,root:G.scope,sources:S.sources,work:W.portfolio,
     limits:RP.semantic_policy,epoch:int,symbols:int,
     receipt:PolicyScope.receipt,rows:policy_row list,
     goal_view:G.source option,denial_view:G.source option,
     denial:G.source,denial_index:IntInf.int,
     check_type:Type.hol_type -> unit,scope_opened:G.scope -> unit,
     discoveries:G.policy_partial_discovery list,retired:bool ref,
     built:bool ref}

  fun close_preparation_with_policy
      (PolicyPreparation {work,retired,...}) =
    (retired := true;W.close work)

  fun policy_preparation_guard expected
      (prepared as PolicyPreparation {work,...}) =
    ((if Portable.pointer_eq (expected,work) then () else
        raise ERR "policy_preparation" "different original Work";
      let
        val PolicyPreparation
          {graph,root,sources,limits,epoch,symbols,receipt,
           discoveries,retired,...} = prepared
        val _ = if !retired then
            raise ERR "policy_preparation" "preparation retired" else ()
        val _ = W.validate_policy expected graph root sources limits
        val _ = if Type.type_epoch () = epoch andalso
            Term.term_epoch () = symbols then () else
          raise ERR "policy_preparation" "retirement epoch changed"
        val _ = PolicyScope.validate_lifetime_with_policy_for
          expected receipt
        val _ = List.app (G.validate_partial_with_policy graph root)
          discoveries
      in W.validate_policy expected graph root sources limits end)
     handle primary => (W.close expected;raise primary))

  fun begin_provenance_with_policy work
      {assumption_views,goal_view,denial_view,check_type,scope_opened,
       discoveries} =
    let
      val sources = W.original_sources work
      val graph = S.owning_graph sources val root = S.owning_scope sources
      val limits = W.semantic_policy work
      val epoch = Type.type_epoch () val symbols = Term.term_epoch ()
      fun guard () =
        (W.validate_policy work graph root sources limits;
         if Type.type_epoch () = epoch andalso
             Term.term_epoch () = symbols then () else
           raise ERR "begin_with_policy" "retirement epoch changed";
         List.app (G.validate_partial_with_policy graph root) discoveries;
         W.validate_policy work graph root sources limits)
      fun prepare () = W.with_step work (fn () =>
        let
          val _ = guard ()
          val (denial,assumptions) = case S.reconciliation_sources sources of
              denied::rest => (denied,rest)
            | [] => raise ERR "begin_with_policy" "original denial missing"
          fun rows [] [] (index:IntInf.int) = ([],index)
            | rows ((original:G.source)::rest)
                ((view:G.source option)::more) index =
              let
                val _ = guard ()
                val _ = case view of NONE => () | SOME opened =>
                  G.validate_opened_view graph root (#node original) opened
                val _ = guard () val _ = W.spend_policy work 2
                val (tail,total) = rows rest more (index+1)
              in ({occurrence=index+1,index=index,original=original,
                   view=view}::tail,total) end
            | rows _ _ _ = raise ERR "begin_with_policy"
                "assumption view count differs"
          val (rows,total) = rows assumptions assumption_views 0
          fun pay_rows [] = ()
            | pay_rows (_::rest) =
                (W.spend_policy work 1;pay_rows rest)
          val _ = pay_rows rows
          val _ = case (goal_view,denial_view) of
              (SOME positive,SOME negative) =>
                (G.validate_opened_view graph root
                   (#node (S.goal_source sources)) positive;
                 guard ();
                 G.validate_opened_view graph root (#node denial) negative;
                 guard ();W.spend_policy work 2)
            | (SOME _,NONE) => raise ERR "begin_with_policy"
                "opened positive Goal requires original denial view"
            | (NONE,SOME negative) =>
                (G.validate_opened_view graph root (#node denial) negative;
                 guard ();W.spend_policy work 1)
            | (NONE,NONE) => ()
          val _ = guard ()
        in (rows,denial,total) end)
      fun create () =
        let
          val (rows,denial,total) = prepare ()
          val receipt = PolicyScope.root_with_policy work
          val prepared = PolicyPreparation
            {graph=graph,root=root,sources=sources,work=work,limits=limits,
             epoch=epoch,symbols=symbols,receipt=receipt,rows=rows,
             goal_view=goal_view,denial_view=denial_view,denial=denial,
             denial_index=total,check_type=check_type,
             scope_opened=scope_opened,discoveries=discoveries,
             retired=ref false,built=ref false}
          val _ = policy_preparation_guard work prepared
        in prepared end
    in create () handle primary => (W.close work;raise primary) end

  fun preparation_with_policy_for expected
      (prepared as PolicyPreparation {work,...}) =
    (policy_preparation_guard expected prepared;
     let val PolicyPreparation {sources,receipt,rows,goal_view,denial_view,
           denial,denial_index,...} = prepared
     in {sources=sources,receipt=receipt,rows=rows,goal_view=goal_view,
         denial_view=denial_view,denial=denial,denial_index=denial_index}
     end)

  (* Revalidate actual opened views independently of the caller-supplied
     discovery list. Plans are not a complete ancestry inventory. *)
  fun fresh_preparation_views expected
      (prepared as PolicyPreparation {work,...}) =
    (policy_preparation_guard expected prepared;
     let
       val PolicyPreparation {graph,root,sources,rows,goal_view,
         denial_view,denial,...} = prepared
       fun check original NONE = ()
         | check original (SOME opened) =
             (G.validate_opened_view graph root original opened;
              policy_preparation_guard expected prepared)
       val _ = List.app (fn ({original,view,...}:policy_row)=>
         check (#node original) view) rows
       val _ = check (#node (S.goal_source sources)) goal_view
       val _ = check (#node denial) denial_view
     in policy_preparation_guard expected prepared end)

  (* A checked original-only portfolio is useful when genuine discovery
     found no conversion. Changed views require the actual carrier owner
     migration; refusing them cannot fabricate an executable stage. *)
  fun build_original_with_policy expected
      (prepared as PolicyPreparation {work,...}) =
    ((policy_preparation_guard expected prepared;
      let
        val PolicyPreparation {sources,rows,goal_view,denial_view,built,...} =
          prepared
        val _ = if !built then raise ERR "build_original_with_policy"
            "preparation already used or reentrant" else built := true
      in W.with_step work (fn () =>
        let
          val _ = fresh_preparation_views expected prepared
          val _ = if List.all
                (fn ({view,...}:policy_row)=>not (Option.isSome view)) rows
              andalso not (Option.isSome goal_view)
              andalso not (Option.isSome denial_view) then () else
            raise ERR "build_original_with_policy"
              "changed views require policy carrier execution"
          val _ = List.app (fn _=>W.spend_policy work 1) rows
          val _ = W.spend_policy work 1
          val {assumptions,denied} = F.originals_with_policy work
          val checked = F.validate_portfolio_with_policy work
            {assumptions=assumptions,goal= #node (S.goal_source sources),
             denied=denied}
          val result = GP.from_portfolio_with_policy work checked
          val _ = if Portable.pointer_eq
                (GP.original_sources result,sources) andalso
              GP.source_nodes result=S.assumption_nodes sources @
                [S.denied_goal_node sources] then () else
            raise ERR "build_original_with_policy"
              "original Source prefix changed"
          val _ = fresh_preparation_views expected prepared
        in result end)
      end)
     handle primary => (W.close expected;raise primary))

  (* Genuine root-beta execution only. Carrier rules and recursive descent
     remain separate; unchanged rows retain their exact original facts. *)
  fun build_root_beta_with_policy expected prepared {native_contract}=
    ((let val PolicyPreparation {work,...}=prepared
      in if Portable.pointer_eq (expected,work) then () else
        raise ERR "build_root_beta_with_policy" "different original Work"
      end;
      SmtReplayNativeContract.validate_for expected native_contract;
      policy_preparation_guard expected prepared;
      let val PolicyPreparation {work,graph,root,sources,rows,discoveries,
            goal_view,denial_view,check_type,scope_opened,built,...}=prepared
          val _=if !built then raise ERR "build_root_beta_with_policy"
              "preparation already used or reentrant" else built:=true
          val _=fresh_preparation_views expected prepared
          val profiles=List.concat (List.map
            (G.partial_profiles_with_policy graph root) discoveries)
          val scheduler=T.begin_with_policy work
            {native_contract=native_contract,profiles=profiles,
             check_type=check_type,scope_opened=scope_opened}
          fun guard ()=
            (fresh_preparation_views expected prepared;
             T.validate_with_policy_for expected scheduler)
          fun meta action=W.with_step work (fn()=>
            (guard ();let val value=action () in guard ();value end))
          val {assumptions=originals,denied}=meta (fn()=>
            F.originals_with_policy work)
          fun process [] []=[]
            | process ((row:policy_row)::rest) (original::more)=
                let val _=guard ()
                    val _=if F.endpoint original= #node (#original row)
                      then () else raise ERR "build_root_beta_with_policy"
                        "different original occurrence mapping"
                    val result=case #view row of NONE=>NONE | SOME view=>
                      T.run_root_beta_assumption_with_policy scheduler
                        {occurrence= #occurrence row,view=SOME view}
                    val fact=case result of NONE=>original | SOME actual=>
                      let val conversion=T.source_conversion_with_policy_for
                            work scheduler actual
                      in meta (fn()=>
                        (W.spend_policy work 1;
                         F.binder_transport_with_policy work conversion
                           original)) end
                    val _=guard ()
                in fact::process rest more end
            | process _ _=raise ERR "build_root_beta_with_policy"
                "original assumption count changed"
          val assumptions=process rows originals
          val positive=case goal_view of NONE=>NONE | SOME view=>
            T.run_root_beta_goal_with_policy scheduler {view=SOME view}
          val _=guard ()
          val (goal,negative)=case positive of NONE=>
                (#node (S.goal_source sources),denied)
            | SOME actual=>
                let val view=case denial_view of SOME view=>view | NONE=>
                      raise ERR "build_root_beta_with_policy"
                        "missing actual original denial view"
                    val conversion=T.denial_conversion_with_policy_for
                      work scheduler actual view
                    val goal=T.target_with_policy_for work scheduler actual
                    val fact=meta (fn()=>
                      (W.spend_policy work 1;
                       F.binder_transport_with_policy work conversion denied))
                in (goal,fact) end
          val result=meta (fn()=>
            let val checked=F.validate_portfolio_with_policy work
                  {assumptions=assumptions,goal=goal,denied=negative}
                val result=GP.from_portfolio_with_policy work checked
                val _=if Portable.pointer_eq
                      (GP.original_sources result,sources) andalso
                    GP.source_nodes result=S.assumption_nodes sources @
                      [S.denied_goal_node sources] then () else
                  raise ERR "build_root_beta_with_policy"
                    "original Source prefix changed"
            in result end)
          val _=guard ()
      in result end)
     handle primary=>(W.close expected;raise primary))
  (* Genuine application descent plus beta execution. Standalone binder
     bodies and carrier rules remain separate; unchanged rows stay original. *)
  fun build_application_beta_with_policy expected prepared {native_contract}=
    ((let val PolicyPreparation {work,...}=prepared
      in if Portable.pointer_eq (expected,work) then () else
        raise ERR "build_application_beta_with_policy"
          "different original Work"
      end;
      SmtReplayNativeContract.validate_for expected native_contract;
      policy_preparation_guard expected prepared;
      let val PolicyPreparation {work,graph,root,sources,rows,discoveries,
            goal_view,denial_view,check_type,scope_opened,built,...}=prepared
          val _=if !built then raise ERR "build_application_beta_with_policy"
              "preparation already used or reentrant" else built:=true
          val _=fresh_preparation_views expected prepared
          val profiles=List.concat (List.map
            (G.partial_profiles_with_policy graph root) discoveries)
          val scheduler=T.begin_with_policy work
            {native_contract=native_contract,profiles=profiles,
             check_type=check_type,scope_opened=scope_opened}
          fun guard ()=
            (fresh_preparation_views expected prepared;
             T.validate_with_policy_for expected scheduler)
          fun meta action=W.with_step work (fn()=>
            (guard ();let val value=action () in guard ();value end))
          val {assumptions=originals,denied}=meta (fn()=>
            F.originals_with_policy work)
          fun process [] []=[]
            | process ((row:policy_row)::rest) (original::more)=
                let val _=guard ()
                    val _=if F.endpoint original= #node (#original row)
                      then () else
                        raise ERR "build_application_beta_with_policy"
                        "different original occurrence mapping"
                    val result=case #view row of NONE=>NONE | SOME view=>
                      T.run_recursive_application_beta_assumption_with_policy
                        scheduler
                        {occurrence= #occurrence row,view=SOME view}
                    val fact=case result of NONE=>original | SOME actual=>
                      let val conversion=T.source_conversion_with_policy_for
                            work scheduler actual
                      in meta (fn()=>
                        (W.spend_policy work 1;
                         F.binder_transport_with_policy work conversion
                           original)) end
                    val _=guard ()
                in fact::process rest more end
            | process _ _=raise ERR "build_application_beta_with_policy"
                "original assumption count changed"
          val assumptions=process rows originals
          val positive=case goal_view of NONE=>NONE | SOME view=>
            T.run_recursive_application_beta_goal_with_policy
              scheduler {view=SOME view}
          val _=guard ()
          val (goal,negative)=case positive of NONE=>
                (#node (S.goal_source sources),denied)
            | SOME actual=>
                let val view=case denial_view of SOME view=>view | NONE=>
                      raise ERR "build_application_beta_with_policy"
                        "missing actual original denial view"
                    val conversion=T.denial_conversion_with_policy_for
                      work scheduler actual view
                    val goal=T.target_with_policy_for work scheduler actual
                    val fact=meta (fn()=>
                      (W.spend_policy work 1;
                       F.binder_transport_with_policy work conversion denied))
                in (goal,fact) end
          val result=meta (fn()=>
            let val checked=F.validate_portfolio_with_policy work
                  {assumptions=assumptions,goal=goal,denied=negative}
                val result=GP.from_portfolio_with_policy work checked
                val _=if Portable.pointer_eq
                      (GP.original_sources result,sources) andalso
                    GP.source_nodes result=S.assumption_nodes sources @
                      [S.denied_goal_node sources] then () else
                  raise ERR "build_application_beta_with_policy"
                    "original Source prefix changed"
            in result end)
          val _=guard ()
      in result end)
     handle primary=>(W.close expected;raise primary))
  (* Genuine application/body traversal, retaining original Source rows.
     Native admission remains the same actual captured caller contract. *)
  fun build_scope_beta_with_policy expected prepared {native_contract}=
    ((let val PolicyPreparation {work,...}=prepared
      in if Portable.pointer_eq (expected,work) then () else
        raise ERR "build_scope_beta_with_policy"
          "different original Work"
      end;
      SmtReplayNativeContract.validate_for expected native_contract;
      policy_preparation_guard expected prepared;
      let val PolicyPreparation {work,graph,root,sources,rows,discoveries,
            goal_view,denial_view,check_type,scope_opened,built,...}=prepared
          val _=if !built then raise ERR "build_scope_beta_with_policy"
              "preparation already used or reentrant" else built:=true
          val _=fresh_preparation_views expected prepared
          val profiles=List.concat (List.map
            (G.partial_profiles_with_policy graph root) discoveries)
          val scheduler=T.begin_with_policy work
            {native_contract=native_contract,profiles=profiles,
             check_type=check_type,scope_opened=scope_opened}
          fun guard ()=
            (fresh_preparation_views expected prepared;
             T.validate_with_policy_for expected scheduler)
          fun meta action=W.with_step work (fn()=>
            (guard ();let val value=action () in guard ();value end))
          val {assumptions=originals,denied}=meta (fn()=>
            F.originals_with_policy work)
          fun process [] []=[]
            | process ((row:policy_row)::rest) (original::more)=
                let val _=guard ()
                    val _=if F.endpoint original= #node (#original row)
                      then () else
                        raise ERR "build_scope_beta_with_policy"
                        "different original occurrence mapping"
                    val result=case #view row of NONE=>NONE | SOME view=>
                      T.run_recursive_scope_beta_assumption_with_policy
                        scheduler
                        {occurrence= #occurrence row,view=SOME view}
                    val fact=case result of NONE=>original | SOME actual=>
                      let val conversion=T.source_conversion_with_policy_for
                            work scheduler actual
                      in meta (fn()=>
                        (W.spend_policy work 1;
                         F.binder_transport_with_policy work conversion
                           original)) end
                    val _=guard ()
                in fact::process rest more end
            | process _ _=raise ERR "build_scope_beta_with_policy"
                "original assumption count changed"
          val assumptions=process rows originals
          val positive=case goal_view of NONE=>NONE | SOME view=>
            T.run_recursive_scope_beta_goal_with_policy
              scheduler {view=SOME view}
          val _=guard ()
          val (goal,negative)=case positive of NONE=>
                (#node (S.goal_source sources),denied)
            | SOME actual=>
                let val view=case denial_view of SOME view=>view | NONE=>
                      raise ERR "build_scope_beta_with_policy"
                        "missing actual original denial view"
                    val conversion=T.denial_conversion_with_policy_for
                      work scheduler actual view
                    val goal=T.target_with_policy_for work scheduler actual
                    val fact=meta (fn()=>
                      (W.spend_policy work 1;
                       F.binder_transport_with_policy work conversion denied))
                in (goal,fact) end
          val result=meta (fn()=>
            let val checked=F.validate_portfolio_with_policy work
                  {assumptions=assumptions,goal=goal,denied=negative}
                val result=GP.from_portfolio_with_policy work checked
                val _=if Portable.pointer_eq
                      (GP.original_sources result,sources) andalso
                    GP.source_nodes result=S.assumption_nodes sources @
                      [S.denied_goal_node sources] then () else
                  raise ERR "build_scope_beta_with_policy"
                    "original Source prefix changed"
            in result end)
          val _=guard ()
      in result end)
     handle primary=>(W.close expected;raise primary))
  (* Complete carrier then beta traversal; retain original Source rows.
     Native admission remains the same actual captured caller contract. *)
  fun build_carrier_with_policy expected prepared {native_contract}=
    ((let val PolicyPreparation {work,...}=prepared
      in if Portable.pointer_eq (expected,work) then () else
        raise ERR "build_carrier_with_policy"
          "different original Work"
      end;
      SmtReplayNativeContract.validate_for expected native_contract;
      policy_preparation_guard expected prepared;
      let val PolicyPreparation {work,graph,root,sources,rows,discoveries,
            goal_view,denial_view,check_type,scope_opened,built,...}=prepared
          val _=if !built then raise ERR "build_carrier_with_policy"
              "preparation already used or reentrant" else built:=true
          val _=fresh_preparation_views expected prepared
          val profiles=List.concat (List.map
            (G.partial_profiles_with_policy graph root) discoveries)
          val scheduler=T.begin_carrier_with_policy work
            {native_contract=native_contract,profiles=profiles,
             check_type=check_type,scope_opened=scope_opened}
          fun guard ()=
            (fresh_preparation_views expected prepared;
             T.validate_carrier_with_policy_for expected scheduler)
          fun meta action=W.with_step work (fn()=>
            (guard ();let val value=action () in guard ();value end))
          val {assumptions=originals,denied}=meta (fn()=>
            F.originals_with_policy work)
          fun process [] []=[]
            | process ((row:policy_row)::rest) (original::more)=
                let val _=guard ()
                    val _=if F.endpoint original= #node (#original row)
                      then () else
                        raise ERR "build_carrier_with_policy"
                        "different original occurrence mapping"
                    val result=case #view row of NONE=>NONE | SOME view=>
                      T.run_carrier_assumption_with_policy
                        scheduler
                        {occurrence= #occurrence row,view=SOME view}
                    val fact=case result of NONE=>original | SOME actual=>
                      let val conversion=
                            T.carrier_source_conversion_with_policy_for
                            work scheduler actual
                      in meta (fn()=>
                        (W.spend_policy work 1;
                         F.binder_transport_with_policy work conversion
                           original)) end
                    val _=guard ()
                in fact::process rest more end
            | process _ _=raise ERR "build_carrier_with_policy"
                "original assumption count changed"
          val assumptions=process rows originals
          val positive=case goal_view of NONE=>NONE | SOME view=>
            T.run_carrier_goal_with_policy
              scheduler {view=SOME view}
          val _=guard ()
          val (goal,negative)=case positive of NONE=>
                (#node (S.goal_source sources),denied)
            | SOME actual=>
                let val view=case denial_view of SOME view=>view | NONE=>
                      raise ERR "build_carrier_with_policy"
                        "missing actual original denial view"
                    val conversion=T.carrier_denial_conversion_with_policy_for
                      work scheduler actual view
                    val goal=T.carrier_target_with_policy_for
                      work scheduler actual
                    val fact=meta (fn()=>
                      (W.spend_policy work 1;
                       F.binder_transport_with_policy work conversion denied))
                in (goal,fact) end
          val result=meta (fn()=>
            let val checked=F.validate_portfolio_with_policy work
                  {assumptions=assumptions,goal=goal,denied=negative}
                val result=GP.from_portfolio_with_policy work checked
                val _=if Portable.pointer_eq
                      (GP.original_sources result,sources) andalso
                    GP.source_nodes result=S.assumption_nodes sources @
                      [S.denied_goal_node sources] then () else
                  raise ERR "build_carrier_with_policy"
                    "original Source prefix changed"
            in result end)
          val _=guard ()
      in result end)
     handle primary=>(W.close expected;raise primary))
end
