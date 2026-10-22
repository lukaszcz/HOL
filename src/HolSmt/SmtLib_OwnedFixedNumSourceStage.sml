(* One original Source/Work; fixed numeric PURE context, never Source simp. *)
structure SmtLib_OwnedFixedNumSourceStage :>
    SmtLib_OwnedFixedNumSourceStage =
struct
  structure G = SmtReplayGraph
  structure S = SmtReplaySource
  structure W = SmtReplayInvocationWork
  structure Scope = SmtReplayOwnedScopeReceipt
  structure T = SmtLib_CompactCarrierScheduler
  structure C = SmtReplayCanonGraph
  structure Core = SmtReplayOwnedLargeProofCore
  structure Raw = SmtLib_GraphNumericRewriteCatalogue
  structure Canonical = SmtLib_GraphNumericCanonical
  structure Numeric = SmtLib_FixedNumericSimple
  structure F = SmtLib_GraphSourcePortfolio
  structure GP = SmtLib_GraphPreprocess
  structure Needed = SmtLib_GraphNeededTheorems
  structure Aux = SmtLib_GraphSelectedAuxiliary
  val _ = SmtLib_CompactCarrierScheduler.revalidate_for
  val _ = SmtLib_FixedNumericSimple.execute_changed
  val _ = SmtLib_CompactCarrierScheduler.run_assumption_target_owned
  val _ = SmtLib_CompactCarrierScheduler.source_target_for
  val _ = SmtLib_GraphNeededTheorems.normalize_result
  val ERR = Feedback.mk_HOL_ERR "SmtLib_OwnedFixedNumSourceStage"
  fun diagnostic work label describe =
    if not ((OS.Process.getEnv "HOL4_HOLSMT_REPLAY_DIAGNOSTICS" = SOME "1")
        handle _ => false) then () else
      ((let val audit = W.audit work
        in TextIO.output (TextIO.stdErr,
          "FIXED_NUM_WORK phase=" ^ label ^ " charged=" ^
          Int.toString (#charged audit) ^ " retired=" ^
          Bool.toString (#retired audit) ^ describe () ^ "\n");
          TextIO.flushOut TextIO.stdErr end) handle _ => ())
  datatype phase = Ready | Building | Complete | Retired
  type row = {index:int,original:G.source}
  type saved = {node:G.node,view:G.source option,
    recipe:C.graph_conversion option}
  datatype owner = Owner of
    {work:W.portfolio,graph:G.graph,root:G.scope,sources:S.sources,
     limits:W.limits,epoch:int,symbols:int,import_limit:int,
     traversal:T.owner,numeric:Numeric.owner,catalogue:Canonical.catalogue,
     rows:row list,positive:G.source,denial:G.source,denial_index:int,
     check_type:Type.hol_type -> unit,phase:phase ref,
     discoveries:G.partial_discovery list ref,
     targets:T.source_target list ref,
     proofs:Core.result list ref,memo:saved list ref,
     recording:Type.hol_type list ref option ref,
     validated:(IntInf.int * G.partial_discovery list *
       T.source_target list * Core.result list) option ref}
  fun close (Owner {work,traversal,phase,...}) =
    (phase := Retired;T.close traversal;W.close work)
  fun protected owner action = action () handle primary =>
    (close owner;raise primary)
  fun guard_app work action rows = case rows of
      [] => W.spend_guard_policy work 1
    | row::rest =>
        (W.spend_guard_policy work 1;action row;guard_app work action rest)
  fun active (Owner {work,graph,root,sources,limits,epoch,symbols,
                    phase,traversal,catalogue,discoveries,
                    targets,proofs,validated,...}) =
    let
      val _ = if !phase=Retired then raise ERR "active" "stage retired" else ()
      val _ = W.validate work graph root sources limits
      val _ = if Type.type_epoch ()=epoch andalso Term.term_epoch ()=symbols
        then () else raise ERR "active" "declaration retirement changed"
      val revision = G.validation_revision graph root
      val ds= !discoveries val ts= !targets val ps= !proofs
      val hit=case !validated of SOME (old,d,t,p) => old=revision andalso
          Portable.pointer_eq (d,ds) andalso Portable.pointer_eq (t,ts)
          andalso Portable.pointer_eq (p,ps)
        | NONE => false
    in if hit then () else
      (T.revalidate_for work traversal;Canonical.validate_for work catalogue;
       guard_app work (G.validate_partial graph root) ds;
       guard_app work (fn target => ignore
         (T.source_target_for work traversal target)) ts;
       guard_app work (fn proof => ignore
         (Core.conversion_description_for work proof)) ps;
       W.validate work graph root sources limits;
       if Type.type_epoch ()=epoch andalso Term.term_epoch ()=symbols
           andalso G.validation_revision graph root=revision andalso
           Portable.pointer_eq (ds,!discoveries) andalso
           Portable.pointer_eq (ts,!targets) andalso
           Portable.pointer_eq (ps,!proofs) then
         validated := SOME (revision,ds,ts,ps) else
         raise ERR "active" "validation state changed during backing pass")
    end
  fun revalidate (owner as Owner {validated,...}) =
    (validated := NONE;active owner)
  fun meta (owner as Owner {work,...}) action = protected owner (fn () =>
    W.with_step work (fn () =>
      (active owner;W.spend work 1;
       let val value=action () in active owner;value end)))
  fun note work recording ty = case !recording of NONE => ()
    | SOME transcript => (W.spend work 1;transcript := ty:: !transcript)
  fun policy (owner as Owner {work,check_type,recording,...}) ty =
    (active owner;note work recording ty;
     check_type ty;active owner)
  fun begin work {import_limit,check_type,scope_opened} =
    let val sources=W.original_sources work
        val graph=S.owning_graph sources val root=S.owning_scope sources
        val limits=W.semantic_limits work
        val epoch=Type.type_epoch () val symbols=Term.term_epoch ()
        fun guard () =
          (W.validate work graph root sources limits;
           if Type.type_epoch ()=epoch andalso Term.term_epoch ()=symbols
             then () else raise ERR "begin" "declaration retirement changed")
        val callback_guard = ref guard
        val recording = ref NONE
        fun checked_type ty =
          ((!callback_guard) ();note work recording ty;
           check_type ty;(!callback_guard) ())
        fun opened child =
          ((!callback_guard) ();G.validate_scope graph child;
           scope_opened child;G.validate_scope graph child;
           (!callback_guard) ())
        val _ = if import_limit>0 then () else
          raise ERR "begin" "nonpositive original discovery limit"
        val (rows,positive,denial,total) = W.with_step work (fn () =>
          let val _=guard ()
              val (denial,assumptions) = case
                  S.reconciliation_sources sources of denied::rest =>
                    (denied,rest)
                | [] => raise ERR "begin" "original denial absent"
              fun rows [] index = ([],index)
                | rows (source::rest) index =
                  let val _=guard () val _=W.spend work 2
                      val (more,total)=rows rest (index+1)
                  in ({index=index,original=source}::more,total) end
              val (rows,total)=rows assumptions 0
          in (rows,S.goal_source sources,denial,total) end)
        val _ = diagnostic work "traversal.before" (fn () => "")
        val traversal=T.begin work
          {check_type=checked_type,scope_opened=opened}
        val _ = diagnostic work "traversal.after" (fn () => "")
        val raw_owner=Raw.begin work {check_type=checked_type}
        val _ = diagnostic work "raw.begin.after" (fn () => "")
        val raw_plan=Raw.prepare raw_owner
        val _ = diagnostic work "raw.prepare.after" (fn () => "")
        val raw=Raw.execute raw_plan
        val _ = diagnostic work "raw.execute.after" (fn () => "")
        val canonical_owner=Canonical.begin work raw {check_type=checked_type}
        val _ = diagnostic work "canonical.begin.after" (fn () => "")
        val canonical_plan=Canonical.prepare canonical_owner
        val _ = diagnostic work "canonical.prepare.after" (fn () => "")
        val catalogue=Canonical.execute canonical_plan
        val _ = diagnostic work "canonical.execute.after" (fn () => "")
        val numeric=Numeric.begin work
          {catalogue=catalogue,traversal=traversal,check_type=checked_type}
        val _ = diagnostic work "numeric.begin.after" (fn () => "")
        val owner=Owner {work=work,graph=graph,root=root,sources=sources,
          limits=limits,epoch=epoch,symbols=symbols,import_limit=import_limit,
          traversal=traversal,numeric=numeric,catalogue=catalogue,
          rows=rows,positive=positive,denial=denial,denial_index=total,
          check_type=check_type,phase=ref Ready,discoveries=ref [],
          targets=ref [],proofs=ref [],memo=ref [],recording=recording,
          validated=ref NONE}
        val _ = callback_guard := (fn () => active owner)
    in active owner;
      diagnostic work "begin.after" (fn () => "");owner
    end handle primary => (W.close work;raise primary)
  fun carrier_view (owner as Owner
      {graph,root,work,import_limit,discoveries,...}) (source:G.source) =
    meta owner (fn () =>
      let fun step () = (active owner;W.spend work 1;active owner)
          val plan=G.discover_compact_shared_partial graph root
            {original= #node source,maximum=import_limit,
             scan_limit=W.work_limit work,step=step}
          val _=discoveries := plan:: !discoveries
          val _=active owner
      in G.partial_view graph root plan end)
  fun process (owner as Owner
      {work,graph,root,traversal,numeric,targets,proofs,memo,...})
      goal occurrence (source:G.source) =
    let
        fun phase label = diagnostic work label (fn () =>
          " source=" ^ Int.toString (G.node_id (#node source)) ^
          " occurrence=" ^ Int.toString occurrence ^
          " positive=" ^ Bool.toString goal)
        val _ = phase "process.before"
        fun cached [] = NONE
          | cached ((held:saved)::rest) =
            (active owner;W.spend work 1;
             if #node held= #node source then
               (case #view held of NONE => () | SOME view =>
                  G.validate_opened_view graph root (#node source) view;
                SOME (#recipe held))
             else cached rest)
        val cached_result=meta owner (fn () => cached (!memo))
    in case cached_result of SOME answer =>
        (phase "process.cache.hit";answer)
      | NONE =>
        let val view=carrier_view owner source
            val _ = phase "process.discovery.after"
            val held=if goal then
              T.run_goal_target_owned traversal {view=view}
            else T.run_assumption_target_owned traversal
              {occurrence=occurrence,view=view}
            val _ = phase "process.carrier.after"
            val _=targets := held:: !targets
            val current=T.source_target_for work traversal held
            val plan=Numeric.prepare numeric
              {frame= #frame current,admission= #admission current}
            val _ = phase "process.numeric.prepare.after"
            val changed=Numeric.execute_changed plan
            val _ = phase "process.numeric.execute.after"
            val recipe=case changed of NONE => #raw current
              | SOME result =>
                let val proof=Numeric.core_for work result
                    val _=proofs := proof:: !proofs
                    val local_recipe=meta owner (fn () =>
                      C.graph_realized_leaf work
                        {realization=Core.realization_for work proof,
                         observe=fn () => (active owner;W.spend work 1)})
                in case #raw current of NONE => SOME local_recipe
                  | SOME prefix => SOME (meta owner (fn () =>
                      let
                        (* The raw carrier prefix is an ordinary recipe;
                           only the numeric suffix has a realized receipt.
                           Preserve both grammars for the checked assembler. *)
                        val _=C.validate_conversion_with_policy work prefix
                        val _=C.validate_conversion_with_policy
                          work local_recipe
                        val composed=C.graph_sequence graph root
                          {first=prefix,second=local_recipe,
                           observe=fn () => (active owner;W.spend work 1)}
                        val _=C.validate_conversion_with_policy work composed
                      in composed end))
                end
            val _=meta owner (fn () => case recipe of NONE => ()
              | SOME converted =>
                  (C.validate_conversion_with_policy work converted;
                   if C.graph_source converted= #node source then () else
                     raise ERR "process" "original raw endpoint changed"))
            val _=memo := {node= #node source,view=view,recipe=recipe}:: !memo
            val _=active owner
            val _ = phase "process.after"
        in recipe end
    end
  fun build_internal include_needed (owner as Owner
      {work,graph,root,sources,limits,traversal,numeric,rows,
       positive,denial,denial_index,phase,recording,...}) =
    protected owner (fn () =>
    let val _=active owner
        val _=if !phase=Ready then phase := Building else
          raise ERR "build" "stage consumed or reentrant"
        fun original index node = meta owner (fn () =>
          let val fact=F.original graph root sources index
          in if F.endpoint fact=node then fact else
            raise ERR "build" "original occurrence mapping changed" end)
        fun transport fact recipe = meta owner (fn () =>
          (if C.graph_source recipe=F.endpoint fact then () else
             raise ERR "build" "different exact Source dependency";
           F.transport_with_work work recipe fact))
        fun assertion ({index,original=saved}:row) =
          let val fact=original index (#node saved)
          in case process owner false (index+1) saved of NONE => fact
            | SOME recipe => transport fact recipe end
        val assertions=List.map assertion rows
        val _ = diagnostic work "build.assertions.after" (fn () => "")
        val goal_recipe=process owner true (~1) positive
        val _ = diagnostic work "build.positive.after" (fn () => "")
        (* Denial is a fixed constructor over the original POSITIVE node.
           No denial-first scan or doubled positive Source occurrence. *)
        val denied=original denial_index (#node denial)
        val (goal,negative)=case goal_recipe of NONE => (#node positive,denied)
          | SOME recipe =>
            let val wrapped=meta owner (fn () =>
                  let val (head,operand)=case G.view graph (#node denial) of
                        G.Application pair => pair
                      | _ => raise ERR "build" "original denial shape changed"
                      val _=if operand= #node positive andalso
                          operand=C.graph_source recipe andalso
                          Term.same_const (G.representative graph head)
                            boolSyntax.negation then () else
                        raise ERR "build" "original denial operand changed"
                      fun observe () = (active owner;W.spend work 1)
                      val left=C.graph_identity graph root
                        {observe=observe} head
                  in C.graph_application graph root
                    {source= #node denial,left=left,right=recipe,
                     observe=observe} end)
            in (C.graph_result recipe,transport denied wrapped) end
        val portfolio=meta owner (fn () => F.validate_portfolio_with_work work
          {assumptions=assertions,goal=goal,denied=negative})
        val _ = diagnostic work "build.portfolio.after" (fn () => "")
        fun needed () =
          let val owner_needed=Needed.begin work
                {portfolio=portfolio,check_type=policy owner}
              val _ = diagnostic work "needed.begin.after" (fn () => "")
              (* This cache belongs to exactly this Stage/Needed/Numeric
                 portfolio. It holds completed proofs, never a supplied
                 theorem/normalizer or a past Work/policy credit. *)
              type saved_law = {head:Term.term,ordinal:int,original:Thm.thm,
                completed:Needed.normalized,policies:Type.hol_type list}
              val completed_laws=ref ([] : saved_law list)
              fun lookup head ordinal original = meta owner (fn () =>
                let
                  fun loop [] = NONE
                    | loop ((held:saved_law)::rest) =
                        (active owner;W.spend work 1;
                         if ordinal= #ordinal held andalso
                             Portable.pointer_eq (original,#original held)
                             andalso Term.compare (head,#head held)=EQUAL
                         then SOME held else loop rest)
                in loop (!completed_laws) end)
              fun replay pending (held:saved_law) =
                let
                  (* Inspect the entire retained type portfolio and debit its
                     future callback incidences before the FIRST callback.
                     No graph/proof operations of an absent replay are priced
                     as though they happened; the first proof stays genuine. *)
                  val _=Numeric.validate_for work numeric
                  val _=meta owner (fn () =>
                    let
                      fun tywalk ty =
                        (active owner;W.spend work 1;
                         if Type.is_vartype ty then
                           W.spend work (String.size (Type.dest_vartype ty))
                         else let val {Thy,Tyop,Args}=Type.dest_thy_type ty
                                  val _=W.spend work
                                    (String.size Thy+String.size Tyop)
                                  val _=List.app (fn _ => W.spend work 1) Args
                              in List.app tywalk Args end;
                         active owner)
                      val _=List.app tywalk (#policies held)
                      val _=List.app (fn _ => W.spend work 1)
                        (#policies held)
                    in () end)
                  val _=W.with_step work (fn () =>
                    List.app (fn ty =>
                      let val Owner {check_type,...}=owner
                          fun fence () =
                            (active owner;
                             Numeric.validate_cached_for work numeric;
                             Needed.validate_reuse_cached pending
                               (#completed held);
                             active owner)
                          (* Every callback still runs in original order.
                             Each fence checks W/S/root/phase/Type/Term and
                             graph revision + private inventory generation.
                             A changed witness forces full actual backings
                             BEFORE the next callback or metadata use. *)
                      in fence ();check_type ty;fence () end)
                      (#policies held))
                  val _=Numeric.validate_for work numeric
                in () end
              fun batch pending =
                let val selections=meta owner (fn () =>
                      Needed.pending_selections pending)
                    fun normalize (selected:
                        {selection:SmtLib_GraphNumericStock.selection,
                         ordinal:int}) =
                      let
                        val _=active owner
                        val selection= #selection selected
                        val law_ordinal= #ordinal selected
                        fun phase label = diagnostic work label (fn () =>
                          " ordinal=" ^ Int.toString law_ordinal)
                        val _ = phase "needed.law.before"
                        val (head,original)=meta owner (fn () =>
                          let
                            val data=
                              SmtLib_GraphNumericStock.selection_data selection
                            fun chosen [] _ = raise ERR "needed"
                                  "selected law ordinal absent"
                              | chosen (th::rest) n =
                                  (W.spend work 1;if n=0 then th
                                   else chosen rest (n-1))
                            val _=if law_ordinal>=0 then () else
                              raise ERR "needed" "negative law ordinal"
                          in (#head data,chosen (#laws data) law_ordinal) end)
                      in case lookup head law_ordinal original of
                          SOME held =>
                            let
                              val _ = phase "needed.law.cache.hit"
                              (* Authenticate the new pending request before
                                 policy replay; retired/foreign evidence is
                                 never activated by this owner's callbacks. *)
                              val completed=Needed.reuse pending
                                {completed= #completed held,
                                 selection=selection,ordinal=law_ordinal}
                              val _=replay pending held
                              val checked=Needed.reuse pending
                                {completed=completed,selection=selection,
                                 ordinal=law_ordinal}
                              val _ = phase "needed.law.after"
                            in checked end
                        | NONE =>
                          let
                            val transcript=meta owner (fn () =>
                              let val _=W.spend work 1 val saved=ref []
                                  val _=if Option.isSome (!recording) then
                                    raise ERR "needed" "nested law recording"
                                    else recording := SOME saved
                              in saved end)
                            val law=Aux.execute (Aux.prepare (Aux.begin work
                              {selection=selection,ordinal=law_ordinal,
                               check_type=policy owner}))
                            val _ = phase "needed.law.auxiliary.after"
                            val target=T.run_aux_target_owned traversal
                              {law=law}
                            val _ = phase "needed.law.carrier.after"
                            val conversion=Numeric.normalize_aux numeric target
                            val _ = phase "needed.law.numeric.after"
                            val _=active owner
                            val ordinal=T.normalization_ordinal traversal
                            val completed=Needed.normalize_result pending
                              {law=law,conversion=conversion,ordinal=ordinal}
                            val _ = phase "needed.law.result.after"
                            val policies=meta owner (fn () =>
                              (List.app (fn _ => W.spend work 1) (!transcript);
                               List.rev (!transcript)))
                            val _=recording := NONE
                            val _=meta owner (fn () =>
                              (W.spend work 1;
                               completed_laws := {head=head,
                                 ordinal=law_ordinal,original=original,
                                 completed=completed,policies=policies}
                                 :: !completed_laws))
                            val _ = phase "needed.law.after"
                          in completed end
                      end
                    val completed=List.map normalize selections
                in active owner;Needed.resume pending completed end
              fun finish (Needed.Complete result) = result
                | finish (Needed.NeedsNormalization pending) =
                    finish (batch pending)
          in finish (Needed.collect owner_needed) end
        val validation=if include_needed then needed () else
          meta owner (fn () => GP.from_portfolio_with_work work portfolio)
        val _ = diagnostic work "build.validation.after" (fn () => "")
        val _=meta owner (fn () =>
          (GP.validate_with_work work validation;
           if Portable.pointer_eq (GP.original_sources validation,sources)
              andalso GP.source_nodes validation=S.assumption_nodes sources @
                [S.denied_goal_node sources] andalso
              GP.template_limit validation=SOME (#template_limit limits)
            then () else raise ERR "build" "Source prefix/template changed"))
        val _=active owner val _=phase := Complete
        val _ = diagnostic work "build.after" (fn () => "")
    in validation end)
  fun build owner = build_internal false owner
  fun build_needed owner = build_internal true owner
  (* A genuine Needed completion component. Source reconstruction belongs to
     the caller's owned Stage; no callback may supply a proof or normalizer. *)
  val _=SmtLib_FixedNumericSimple.normalize_aux_with_policy
  val _=SmtLib_GraphNeededTheorems.normalize_result_with_policy
  val _=SmtReplayNativeContract.for_work
  structure PolicyNeededStage=
  struct
    structure NC=SmtReplayNativeContract
    datatype owner=Owner of
      {work:W.portfolio,graph:G.graph,scope:G.scope,sources:S.sources,
       native:NC.contract,profiles:G.policy_opaque_profile list,
       traversal:T.policy_carrier_owner,
       catalogue:Canonical.policy_catalogue,numeric:Numeric.policy_owner,
       portfolio:F.validation option ref,
       symbols:int,types:int,phase:phase ref,
       check_type:Type.hol_type->unit,
       recording:Type.hol_type list ref option ref,
       answer:GP.validation option ref}
    type saved_law={head:Term.term,ordinal:int,original:Thm.thm,
      completed:Needed.policy_normalized,policies:Type.hol_type list}
    fun close(Owner{work,phase,...})=(phase:=Retired;W.close work)
    fun protect owner action=action()handle primary=>
      (close owner;raise primary)
    fun active(Owner{work,graph,scope,sources,native,traversal,catalogue,
        numeric,portfolio,symbols,types,phase,answer,...})=
      (if !phase=Retired then raise ERR "policy_needed_stage"
         "needed stage retired"else();
       NC.validate_for work native;
       W.validate_policy work graph scope sources(W.semantic_policy work);
       if Type.type_epoch()=types andalso Term.term_epoch()=symbols then ()
       else raise ERR "policy_needed_stage" "declaration retirement changed";
       if Portable.pointer_eq
           (T.native_contract_carrier_with_policy_for work traversal,native)
           andalso Portable.pointer_eq
             (Canonical.native_contract_for work catalogue,native)then ()
       else raise ERR "policy_needed_stage" "different actual native contract";
       Numeric.validate_cached_with_policy_for work numeric;
       (case !portfolio of NONE=>()|SOME value=>
          F.validate_with_policy work value);
       case !answer of NONE=>()|SOME result=>
         GP.validate_with_policy work result)
    fun for_work expected(owner as Owner{work,...})=
      ((if Portable.pointer_eq(expected,work)then active owner else
          raise ERR "policy_needed_stage" "different original Work")
       handle primary=>(W.close expected;raise primary))
    fun meta(owner as Owner{work,...}) action=protect owner(fn()=>
      W.with_step work(fn()=>
        (active owner;W.spend_policy work 1;
         let val value=action()in active owner;value end)))
    fun checked(owner as Owner{work,check_type,recording,...})ty=
      (active owner;
       (case !recording of NONE=>()|SOME transcript=>
          (W.spend_policy work 1;transcript:=ty:: !transcript));
       check_type ty;active owner)
    fun begin_policy work
        {native_contract,profiles,check_type,scope_opened}=
      ((let
          val _=NC.validate_for work native_contract
          val sources=W.original_sources work
          val graph=S.owning_graph sources
          val scope=S.owning_scope sources
          val symbols=Term.term_epoch()val types=Type.type_epoch()
          fun base()=
            (NC.validate_for work native_contract;
             W.validate_policy work graph scope sources
               (W.semantic_policy work);
             if Term.term_epoch()=symbols andalso Type.type_epoch()=types
               then ()else raise ERR "policy_needed_stage"
                 "declaration retirement changed")
          val held=ref(NONE:owner option)
          val recording=ref NONE
          fun policy ty=case !held of SOME owner=>checked owner ty
            | NONE=>(base();check_type ty;base())
          fun opened body_frame=
            let fun guard()=case !held of NONE=>base()
                  | SOME owner=>active owner
            in guard();G.validate_scope graph body_frame;
              scope_opened body_frame;G.validate_scope graph body_frame;
              guard()end
          (* The actual traversal/catalogue/Simple producers all capture the
             SAME callback. Their normalization callbacks are consequently
             present in the saved transcript, including carrier and beta. *)
          val traversal=T.begin_carrier_with_policy work
            {native_contract=native_contract,profiles=profiles,
             check_type=policy,scope_opened=opened}
          val raw=Raw.execute_with_policy(Raw.prepare_with_policy
            (Raw.begin_with_policy work
              {native_contract=native_contract,check_type=policy}))
          val catalogue=Canonical.execute_with_policy
            (Canonical.prepare_with_policy
              (Canonical.begin_with_policy work raw{check_type=policy}))
          val numeric=Numeric.begin_with_policy work
            {catalogue=catalogue,traversal=traversal,
             native_contract=native_contract,profiles=profiles,
             check_type=policy}
          val result=Owner{work=work,graph=graph,scope=scope,sources=sources,
            native=native_contract,profiles=profiles,
            traversal=traversal,catalogue=catalogue,
            numeric=numeric,portfolio=ref NONE,
            symbols=symbols,types=types,phase=ref Ready,
            check_type=check_type,recording=recording,answer=ref NONE}
          val _=held:=SOME result
          val _=active result
        in result end)
       handle primary=>(W.close work;raise primary))
    fun traversal_for expected(owner as Owner{traversal,...})=
      (for_work expected owner;traversal)
    fun numeric_for expected(owner as Owner{numeric,...})=
      (for_work expected owner;numeric)
    fun finish expected(owner as Owner
        {work,graph,scope,sources,native,profiles,
        traversal,numeric,portfolio,phase,recording,answer,...})
        actual_portfolio=
      (for_work expected owner;
       protect owner(fn()=>
       let
         val _=if !phase=Ready then phase:=Building else
           raise ERR "policy_needed_stage" "stage consumed or reentrant"
         val _=F.validate_with_policy work actual_portfolio
         val _=if Portable.pointer_eq
             (F.original_sources actual_portfolio,sources)then ()else
           raise ERR "policy_needed_stage" "different Source portfolio"
         val _=portfolio:=SOME actual_portfolio
         val needed=Needed.begin_with_policy work
           {portfolio=actual_portfolio,native_contract=native,
            profiles=profiles,
            check_type=checked owner}
         val completed_laws=ref([]:saved_law list)
         fun lookup head ordinal original=meta owner(fn()=>
           let fun loop []=NONE
                 | loop((held:saved_law)::rest)=
                     (active owner;W.spend_policy work 1;
                      if ordinal= #ordinal held andalso
                          Portable.pointer_eq(original,#original held)
                          andalso Term.compare(head,#head held)=EQUAL
                        then SOME held else loop rest)
           in loop(!completed_laws)end)
         fun replay pending(held:saved_law)=
           let
             val _=Numeric.validate_with_policy_for work numeric
             (* Inspect and debit every retained callback incidence before
                replay's first external callback. No proof is repeated. *)
             val _=meta owner(fn()=>
               let fun tywalk ty=
                     (active owner;W.spend_policy work 1;
                      if Type.is_vartype ty then W.spend_policy work
                        (IntInf.fromInt(String.size(Type.dest_vartype ty)))
                      else let val{Thy,Tyop,Args}=Type.dest_thy_type ty
                               val _=W.spend_policy work
                                 (IntInf.fromInt(String.size Thy)+
                                  IntInf.fromInt(String.size Tyop))
                               val _=List.app
                                 (fn _=>W.spend_policy work 1)Args
                           in List.app tywalk Args end;
                      active owner)
                   val _=List.app tywalk(#policies held)
               in List.app(fn _=>W.spend_policy work 1)(#policies held)end)
             val _=W.with_step work(fn()=>
               List.app(fn ty=>
                 let fun fence()=
                       (active owner;
                        Numeric.validate_cached_with_policy_for work numeric;
                        Needed.validate_reuse_cached_with_policy pending
                          (#completed held);active owner)
                     val Owner{check_type,...}=owner
                 in fence();check_type ty;fence()end)(#policies held))
             val _=Numeric.validate_with_policy_for work numeric
           in ()end
         fun batch pending=
           let val selections=meta owner(fn()=>
                 Needed.pending_selections_with_policy pending)
               fun normalize(selected:
                   {selection:SmtLib_GraphNumericStock.selection,
                    ordinal:int})=
                 let
                   val _=active owner
                   val selection= #selection selected
                   val law_ordinal= #ordinal selected
                   val(head,original)=meta owner(fn()=>
                     let val data=
                           SmtLib_GraphNumericStock.selection_data selection
                         fun chosen [] _=raise ERR "policy_needed_stage"
                               "selected law ordinal absent"
                           | chosen(th::rest)n=
                               (W.spend_policy work 1;
                                if n=0 then th else chosen rest(n-1))
                         val _=if law_ordinal>=0 then ()else
                           raise ERR "policy_needed_stage"
                             "negative selected law ordinal"
                     in (#head data,chosen(#laws data)law_ordinal)end)
                 in case lookup head law_ordinal original of
                     SOME held=>
                       let val completed=Needed.reuse_with_policy pending
                             {completed= #completed held,selection=selection,
                              ordinal=law_ordinal}
                           val _=replay pending held
                       in Needed.reuse_with_policy pending
                         {completed=completed,selection=selection,
                          ordinal=law_ordinal}end
                   | NONE=>
                       let
                         val transcript=meta owner(fn()=>
                           let val _=W.spend_policy work 1 val saved=ref[]
                               val _=if Option.isSome(!recording)then
                                 raise ERR "policy_needed_stage"
                                   "nested law recording"
                                 else recording:=SOME saved
                           in saved end)
                         val law=Aux.execute_with_policy
                           (Aux.prepare_with_policy
                             (Aux.begin_with_policy work
                               {selection=selection,ordinal=law_ordinal,
                                native_contract=native,
                                check_type=checked owner}))
                         val target=T.run_carrier_aux_target_with_policy
                           traversal{law=law}
                         val conversion=Numeric.normalize_aux_with_policy
                           numeric target
                         val _=active owner
                         val ordinal=
                           T.carrier_normalization_ordinal_with_policy_for
                             work traversal
                         val completed=Needed.normalize_result_with_policy
                           pending{law=law,conversion=conversion,
                             ordinal=ordinal}
                         val policies=meta owner(fn()=>
                           (List.app(fn _=>W.spend_policy work 1)(!transcript);
                            List.rev(!transcript)))
                         val _=recording:=NONE
                         val _=meta owner(fn()=>
                           (W.spend_policy work 1;
                            completed_laws:={head=head,ordinal=law_ordinal,
                              original=original,completed=completed,
                              policies=policies}:: !completed_laws))
                       in completed end
                 end
               val completed=List.map normalize selections
           in active owner;Needed.resume_with_policy pending completed end
         fun loop(Needed.PolicyComplete result)=result
           | loop(Needed.PolicyNeedsNormalization pending)=
               loop(batch pending)
         val result=loop(Needed.collect_with_policy needed)
         val _=meta owner(fn()=>
           (GP.validate_with_policy work result;
            if Portable.pointer_eq(GP.original_sources result,sources)andalso
                GP.source_nodes result=S.assumption_nodes sources@
                  [S.denied_goal_node sources]then ()else
              raise ERR "policy_needed_stage"
                "original Source prefix changed"))
         val _=answer:=SOME result
         val _=active owner
         val _=phase:=Complete
       in result end))
  end
  type policy_needed_owner=PolicyNeededStage.owner
  val begin_needed_with_policy=PolicyNeededStage.begin_policy
  val traversal_needed_with_policy_for=PolicyNeededStage.traversal_for
  val numeric_needed_with_policy_for=PolicyNeededStage.numeric_for
  val finish_needed_with_policy=PolicyNeededStage.finish
  val validate_needed_with_policy_for=PolicyNeededStage.for_work

end
