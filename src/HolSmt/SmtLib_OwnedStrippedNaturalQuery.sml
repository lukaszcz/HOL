(* Exact bounded GEN/DISCH receiver, on SAME original Source/Work. *)
structure SmtLib_OwnedStrippedNaturalQuery :>
    SmtLib_OwnedStrippedNaturalQuery =
struct
  structure G = SmtReplayGraph
  structure S = SmtReplaySource
  structure W = SmtReplayInvocationWork
  structure N = SmtLib_OwnedNaturalSequentTransfer
  structure T = SmtLib_CompactCarrierScheduler
  structure Scope = SmtReplayOwnedScopeReceipt
  structure P = SmtReplayProof
  structure Core = SmtReplayOwnedLargeProofCore
  val _ = SmtLib_OwnedNaturalSequentTransfer.claim_query
  val _ = SmtReplayProof.prepare_needed_sources_with_work
  val _ = SmtReplayProof.validate_block_for
  val _ = SmtReplayOwnedScopeReceipt.body
  val ERR = Feedback.mk_HOL_ERR "SmtLib_OwnedStrippedNaturalQuery"
  datatype phase = New | Prepared | Executed | Frozen | Closed | Retired
  datatype step = Generalize of {variable:Term.term,parent:Term.term}
    | Discharge of {assumption:Term.term,parent:Term.term}
    | SplitConjunction of {original:Term.term,left:Term.term,right:Term.term}
    | ChooseWitness of {original:Term.term,variable:Term.term,
        body:Term.term,bridge:Thm.thm}
  datatype owner = Owner of
    {work:W.portfolio,graph:G.graph,root:G.scope,sources:S.sources,
     limits:W.limits,transfer:N.receipt,claim:N.query_claim,
     traversal:T.owner,epoch:int,symbols:int,phase:phase ref,
     frames:Scope.receipt list ref,normalizations:Core.result list ref,
     paths:(G.scope * G.closure_child) list ref,
     check_type:Type.hol_type -> unit,scope_opened:G.scope -> unit}
  datatype plan = Plan of
    {owner:owner,frame:Scope.receipt,assumptions:G.node list,goal:G.node,
     steps:step list,types:Type.hol_type list,
     normalization:Core.result option,solved:(G.node * bool) option}
  exception Terminal of Scope.receipt * G.node list * step list *
    G.node * bool
  datatype query = Query of
    {plan:plan,denied:G.node,block:P.block option ref}
  fun close (Owner {work,phase,...}) = (phase := Retired;W.close work)
  fun protected owner action = action () handle primary =>
    (close owner;raise primary)
  fun active (Owner {work,graph,root,sources,limits,transfer,epoch,symbols,
                    phase,frames,paths,normalizations,...}) =
    (if !phase=Retired then raise ERR "active" "query owner retired" else ();
     W.validate work graph root sources limits;
     if Type.type_epoch ()=epoch andalso Term.term_epoch ()=symbols then ()
       else raise ERR "active" "declaration retirement changed";
     ignore (N.description_for work transfer);
     ignore (N.target_import_for work transfer);
     List.app (fn result => ignore
       (Core.conversion_description_for work result)) (!normalizations);
     List.app (fn frame => ignore (Scope.description_for work frame)) (!frames);
     List.app (fn (caller,child) =>
       ignore (G.closure_child_node graph caller child)) (!paths))
  fun inspect owner operation =
    (active owner;let val result=operation () in active owner;result end)
  fun expected_owner expected
      (owner as Owner {work,...}) =
    ((if Portable.pointer_eq (expected,work) then () else
        raise ERR "owner" "foreign expected Work";
      active owner;owner)
     handle primary => (W.close expected;raise primary))
  fun begin work {transfer,check_type,scope_opened} =
    let val data=N.description_for work transfer
        val claim=N.claim_query work transfer
        val traversal=N.query_traversal_for work claim
        val sources= #original_sources data
        val graph=S.owning_graph sources val root=S.owning_scope sources
        val frame=Scope.root work
        val owner=Owner {work=work,graph=graph,root=root,sources=sources,
          limits=W.semantic_limits work,transfer=transfer,claim=claim,
          traversal=traversal,epoch=Type.type_epoch (),
          symbols=Term.term_epoch (),phase=ref New,frames=ref [frame],
          normalizations=ref [],
          paths=ref [],check_type=check_type,scope_opened=scope_opened}
    in active owner;owner end handle primary => (W.close work;raise primary)
  (* Independent type/name work is charged to original remaining W. Every
     repeated annotation and binder VARIABLE is walked; no scalar grant. *)
  fun profile (owner as Owner {work,...}) limit types term =
    let fun tick n=(active owner;W.spend work n;active owner)
        fun ty t =
          (tick 1;types := t:: !types;
           if Type.is_vartype t then
             tick (String.size (Type.dest_vartype t))
           else let val {Thy,Tyop,Args}=Type.dest_thy_type t
                in tick (String.size Thy+String.size Tyop);
                   List.app ty Args end)
        fun walk [] raw inc = ()
          | walk (current::rest) raw inc =
              let val _=tick 1 val raw=raw+1 val inc=inc+1
                  val _=if raw<=limit andalso inc<=limit then () else
                    raise ERR "profile" "fully realized operation bound"
                  val _=ty (Term.type_of current)
              in if Term.is_comb current then
                   let val (f,x)=Term.dest_comb current
                   in walk (f::x::rest) raw inc end
                 else if Term.is_abs current then
                   let val (v,b)=Term.dest_abs current
                       val _=if inc+1<=limit then () else
                         raise ERR "profile" "binder VARIABLE bound"
                       val _=ty (Term.type_of v)
                       val _=tick (String.size (#1 (Term.dest_var v)))
                   in walk (b::rest) raw (inc+1) end
                 else
                   (if Term.is_var current then
                      tick (String.size (#1 (Term.dest_var current)))
                    else if Term.is_const current then
                      let val {Thy,Name,...}=Term.dest_thy_const current
                      in tick (String.size Thy+String.size Name) end else ();
                    walk rest raw inc) end
    in walk [term] 0 0 end
  fun quote owner limit terms =
    let val Owner {work,...}=owner
    in W.with_step work (fn () =>
      let val types=ref ([]:Type.hol_type list)
          val _=List.app (profile owner limit types) terms
      in List.rev (!types) end) end
  (* Local admission has no past-work grant. Each prospective grammar is
     charged, then every actual policy is bracketed before proof effects. *)
  fun admit_effect owner limit terms =
    let val Owner {work,check_type,...}=owner
        val types=quote owner limit terms
    in W.with_step work (fn () =>
      List.app (fn ty => inspect owner (fn () => check_type ty)) types) end
  fun retain (owner as Owner {graph,paths,...}) caller node =
    let val child=inspect owner (fn () => G.closure_root graph caller node)
        val _=paths := (caller,child):: !paths
    in child end
  fun prepare_internal split_assumptions normalization (owner as Owner
      {work,graph,root,transfer,limits,phase,frames,normalizations,
       traversal,...}) =
    protected owner (fn () =>
    let val _=active owner
        val _=if !phase=New then phase := Prepared else
          raise ERR "prepare" "query preparation consumed"
        val data=N.description_for work transfer
        val start=case normalization of NONE => #node (#target data)
          | SOME result =>
              let val actual=Core.conversion_description_for work result
              in if Portable.pointer_eq (#graph actual,graph) andalso
                  #root actual=root andalso #scope actual=root andalso
                  Portable.pointer_eq (#sources actual,#original_sources data)
                  andalso #source actual= #node (#target data) then
                    #target actual else raise ERR "prepare"
                      "different owned whole-target normalization" end
        val _=case normalization of NONE => ()
          | SOME result => normalizations := result:: !normalizations
        val initial=hd (!frames)
        val types=ref ([]:Type.hol_type list)
        fun admit terms =
          types := quote owner (#output_limit limits) terms @ !types
        fun operator node constant = case G.view graph node of
            G.Constant _ => Term.same_const (G.representative graph node) constant
          | _ => false
        fun strip frame node assumptions steps =
          let val state=Scope.description_for work frame val caller= #scope state
              val term=G.representative graph node
              val _=admit [term]
              val child=retain owner caller node
          in case G.view graph node of G.Application (head,argument) =>
             if operator head boolSyntax.universal then
               let val binder_child=retain owner caller argument
                   val closure=G.closure_child_binder graph caller binder_child
                   val held=G.binder_closure_data graph caller closure
                   val variable= #binder_term held
                   val _=if List.exists (fn assumption =>
                     Term.free_in variable (G.representative graph assumption))
                       assumptions then raise ERR "prepare"
                         "GEN eigenvariable is free in earlier assumptions"
                     else ()
                   val _=admit [variable]
                   val next=Scope.body work frame binder_child
                   val _=frames := next:: !frames
                   val body=G.closure_child_node graph caller
                     (G.binder_closure_body graph caller closure)
               in strip next body assumptions
                 (Generalize {variable=variable,parent=term}::steps) end
             else (case G.view graph head of G.Application (imp,antecedent) =>
               if operator imp boolSyntax.implication then
                 strip frame argument (antecedent::assumptions)
                   (Discharge {assumption=G.representative graph antecedent,
                     parent=term}::steps)
               else (frame,node,assumptions,steps)
              | _ => (frame,node,assumptions,steps))
            | _ => (frame,node,assumptions,steps)
          end
        val (frame,goal,assumptions,steps)=strip initial start [] []
        val goal_term=G.representative graph goal
        (* A following phase, never silently selected by old prepare. The
           caller's owned context-SIMPLE producer must precede this phase.
           Exact POP_ASSUM repetition count/order is retained: pushing an
           atom to the front can cause it to be processed again. *)
        fun expand frame original rest steps =
          let val caller= #scope (Scope.description_for work frame)
              val term=G.representative graph original
              val _=admit [term]
              val child=retain owner caller original
              fun atom () =
                let val _=admit [term,goal_term]
                in if Term.is_const term andalso
                    Term.same_const term boolSyntax.F then
                  raise Terminal (frame,original::rest,steps,original,true)
                else if inspect owner (fn () => Term.aconv term goal_term) then
                  raise Terminal (frame,original::rest,steps,original,false)
                else (frame,original::rest,steps) end
              fun operator node constant = case G.view graph node of
                  G.Constant _ => Term.same_const
                    (G.representative graph node) constant
                | _ => false
          in case G.view graph original of G.Application (head,arg) =>
            if operator head boolSyntax.existential then
              let val predicate=retain owner caller arg
                  val closure=G.closure_child_binder graph caller predicate
                  val captured=G.binder_closure_data graph caller closure
                  val old_variable= #binder_term captured
                  val body_child=G.binder_closure_body graph caller closure
                  val old_body=G.closure_child_node graph caller body_child
                  val body_term=G.representative graph old_body
                  val _=admit [old_variable,body_term]
                  val counter=T.normalization_ordinal traversal
                  val seed=Term.mk_var ("__smt_choose_" ^
                    Int.toString counter,Term.type_of old_variable)
                  val avoid=Term.free_varsl (goal_term::term::
                    List.map (G.representative graph) rest)
                  val variable=Term.variant avoid seed
                  (* Only one SMALL, same-type variable is substituted. The
                     body and full ALPHA/import equality grammar are bounded
                     and debited before substitution/public proof effects. *)
                  val _=admit_effect owner (#output_limit limits)
                    [variable,body_term,
                     boolSyntax.mk_eq (body_term,body_term)]
                  val body=inspect owner (fn () => Term.subst
                    [{redex=old_variable,residue=variable}] body_term)
                  val _=admit_effect owner (#output_limit limits)
                    [body,boolSyntax.mk_eq (body,body)]
                  val (binder_frame,body_frame,binder)=
                    W.with_step work (fn () => inspect owner (fn () =>
                      let val _=W.spend work 3
                          val binder_frame=G.new_scope graph caller []
                          val binder=G.variable graph binder_frame G.Bound
                            variable
                          val body_frame=G.new_scope graph binder_frame
                            [(variable,binder)]
                      in (binder_frame,body_frame,binder) end))
                  val imported=inspect owner (fn () => G.import graph
                    body_frame (#output_limit limits) body)
                  val opened=inspect owner (fn () => G.record_opened_view
                    graph body_frame (#output_limit limits) (#node imported))
                  val binder=inspect owner (fn () => G.recorded_abstraction
                    graph caller (#output_limit limits)
                    {binder=binder,body= #node opened,body_frame=body_frame})
                  val new_path=retain owner caller binder
                  val next=Scope.body work frame new_path
                  val _=frames := next:: !frames
                  val _=G.validate_scope graph binder_frame
                  val _=admit_effect owner (#output_limit limits)
                    [Thm.concl (#bridge imported),
                     Thm.concl (#bridge opened),boolSyntax.mk_eq
                       (body,G.representative graph (#node opened))]
                  val bridge=W.with_step work (fn () => inspect owner (fn () =>
                    Thm.TRANS (#bridge imported) (#bridge opened)))
                  val step=ChooseWitness {original=term,variable=variable,
                    body=body,bridge=bridge}
              in expand next (#node opened) rest (step::steps) end
            else (case G.view graph head of G.Application (conj,left) =>
              if operator conj boolSyntax.conjunction then
                let val l=G.representative graph left
                    val r=G.representative graph arg
                    val recorded=SplitConjunction
                      {original=term,left=l,right=r}::steps
                    val (next,tail,recorded)=expand frame left rest recorded
                in expand next arg tail recorded end
              else atom ()
            | _ => atom ())
           | _ => atom ()
          end
        fun pop 0 frame assumptions steps = (frame,assumptions,steps)
          | pop count frame assumptions steps =
              (case assumptions of [] =>
                 raise ERR "prepare" "legacy POP_ASSUM count changed"
               | head::rest =>
                 let val (next,tail,recorded)=expand frame head rest steps
                 in pop (count-1) next tail recorded end)
        val (frame,assumptions,steps,solved)=
          ((if split_assumptions then
              let val (f,a,s)=pop (length assumptions) frame assumptions steps
              in (f,a,s,NONE) end
            else (frame,assumptions,steps,NONE))
           handle Terminal (f,a,s,node,contradiction) =>
             (f,a,s,SOME (node,contradiction)))
        val denied=boolSyntax.mk_neg goal_term
        (* The receiver never inserts under a binder: sparse realization
           yields this local Goal first; GEN is an explicitly bounded later
           kernel operation, with its complete actual result/Hyp admitted. *)
        val _=admit [goal_term,denied]
        val _=List.app (fn node => admit [G.representative graph node]) assumptions
    in Plan {owner=owner,frame=frame,goal=goal,assumptions=assumptions,
      steps=steps,types=List.rev (!types),normalization=normalization,
      solved=solved} end)
  fun prepare owner = prepare_internal false NONE owner
  fun prepare_normalized owner result =
    prepare_internal false (SOME result) owner
  fun prepare_no_split owner = prepare_internal true NONE owner
  fun prepare_normalized_no_split owner result =
    prepare_internal true (SOME result) owner
  fun execute (plan as Plan {owner=owner as Owner
      {work,graph,root,limits,phase,check_type,scope_opened,frames,...},
       frame,goal,types,...}) = protected owner (fn () =>
    W.with_step work (fn () =>
      let val _=active owner
          val _=if !phase=Prepared then phase := Executed else
            raise ERR "execute" "query plan consumed"
          val _=List.app (fn ty => inspect owner (fn () => check_type ty)) types
          val _=List.app (fn held =>
            let val actual= #scope (Scope.description_for work held)
            in if actual=root then () else
              (G.validate_scope graph actual;
               inspect owner (fn () => scope_opened actual);
               G.validate_scope graph actual) end) (List.rev (!frames))
          val actual= #scope (Scope.description_for work frame)
          val denied=inspect owner (fn () => G.application graph actual
            (G.constant graph actual boolSyntax.negation,goal))
      in Query {plan=plan,denied=denied,block=ref NONE} end))
  fun held expected (query as Query {plan=Plan {owner,...},...}) =
    (ignore (expected_owner expected owner);query)
  fun description_for expected query =
    let val Query {plan=Plan {owner=Owner {sources,...},frame,assumptions,goal,...},
                  denied,...}=held expected query
    in {frame=frame,assumptions=assumptions,goal=goal,denied=denied,
      original_sources=sources} end
  fun freeze_for expected query {roots,closed_facts,conversions} =
    let val Query {plan=Plan {owner=owner as Owner {phase,graph,...},
          frame,assumptions,goal,...},denied,block}=held expected query
    in protected owner (fn () =>
      let val _=if !phase=Executed then phase := Frozen else
            raise ERR "freeze" "query freeze consumed"
          val scope= #scope (Scope.description_for expected frame)
          val bottom=G.constant graph scope boolSyntax.F
          val prepared=P.prepare_needed_sources_with_work expected
            {frame=frame,roots=goal::denied::bottom::roots,
             additional_sources=assumptions @ [denied],
             closed_facts=closed_facts,conversions=conversions}
          val _=block := SOME prepared
      in prepared end) end
  (* Internal fixed callback only. Every prospective compact result and Hyp
     is quoted BEFORE P.compose invokes its kernel operation. No public
     theorem/operation/counter parameter exists on this receiver. *)
  fun compose owner block results operation premises =
    let val Owner {work,limits,...}=owner
        val proofs=List.map (P.theorem block) premises
        val terms=results @ List.concat
          (List.map (fn th => Thm.concl th::Thm.hyp th) proofs)
        val _=admit_effect owner (#template_limit limits) terms
    in W.with_step work (fn () =>
      inspect owner (fn () => P.compose block operation premises)) end
  fun finish (Plan {owner=owner as Owner
      {work,graph,root,sources,limits,transfer,claim,check_type,...},
       assumptions,steps,normalization,...}) proved =
    let
          val allowed=List.map (G.representative graph) assumptions
          val _=if List.all (fn h => List.exists
              (fn a => Portable.pointer_eq (h,a)) allowed) (Thm.hyp proved)
            then () else raise ERR "close" "local proof retained foreign Hyp"
          fun replay (Generalize {variable,parent},proof) =
                let val result=boolSyntax.mk_forall (variable,Thm.concl proof)
                    val _=if List.exists (Term.free_in variable) (Thm.hyp proof)
                      then raise ERR "close" "GEN freshness changed" else ()
                    val _=admit_effect owner (#output_limit limits)
                      (result::parent::Thm.concl proof::Thm.hyp proof)
                    val raw=W.with_step work (fn () =>
                      inspect owner (fn () => Thm.GEN variable proof))
                    val _=admit_effect owner (#output_limit limits)
                      [boolSyntax.mk_eq (Thm.concl raw,parent)]
                in W.with_step work (fn () => inspect owner (fn () =>
                  Thm.EQ_MP (Thm.ALPHA (Thm.concl raw) parent) raw)) end
            | replay (Discharge {assumption,parent},proof) =
                let val result=boolSyntax.mk_imp (assumption,Thm.concl proof)
                    val _=admit_effect owner (#output_limit limits)
                      (result::parent::Thm.concl proof::Thm.hyp proof)
                    val raw=W.with_step work (fn () =>
                      inspect owner (fn () => Thm.DISCH assumption proof))
                    val _=admit_effect owner (#output_limit limits)
                      [boolSyntax.mk_eq (Thm.concl raw,parent)]
                in W.with_step work (fn () => inspect owner (fn () =>
                  Thm.EQ_MP (Thm.ALPHA (Thm.concl raw) parent) raw)) end
            | replay (SplitConjunction {original,left,right},proof) =
                let val _=admit_effect owner (#output_limit limits)
                      ((original::left::right::Thm.concl proof::Thm.hyp proof) @
                       [boolSyntax.mk_imp (left,Thm.concl proof),
                        boolSyntax.mk_imp (right,Thm.concl proof)])
                in W.with_step work (fn () => inspect owner (fn () =>
                  let val assumed=Thm.ASSUME original
                      val a=Thm.CONJUNCT1 assumed
                      val b=Thm.CONJUNCT2 assumed
                  in Drule.PROVE_HYP a (Drule.PROVE_HYP b proof) end)) end
            | replay (ChooseWitness {original,variable,body,bridge},proof) =
                let val canonical= #2 (boolSyntax.dest_eq (Thm.concl bridge))
                    val _=admit_effect owner (#output_limit limits)
                      ((original::variable::body::canonical::
                       Thm.concl bridge::Thm.concl proof::Thm.hyp proof) @
                       [boolSyntax.mk_imp (canonical,Thm.concl proof)])
                in W.with_step work (fn () => inspect owner (fn () =>
                  let val assumed=Thm.ASSUME body
                      val local_proof=Thm.EQ_MP bridge assumed
                      val transferred=Drule.PROVE_HYP local_proof proof
                  in Thm.CHOOSE (variable,Thm.ASSUME original) transferred end))
                end
          val rebuilt=List.foldl replay proved steps
          val rebuilt=case normalization of NONE => rebuilt
            | SOME result =>
              let val equality=Core.theorem_for work result
                  val (old,new)=boolSyntax.dest_eq (Thm.concl equality)
                  val _=if Term.aconv (Thm.concl rebuilt) new then () else
                    raise ERR "close" "normalized whole Goal changed"
                  val _=admit_effect owner (#output_limit limits)
                    [Thm.concl equality,boolSyntax.mk_eq (new,old),
                     Thm.concl rebuilt,old]
              in W.with_step work (fn () => inspect owner (fn () =>
                Thm.EQ_MP (Thm.SYM equality) rebuilt)) end
          val target= #target (N.description_for work transfer)
          val _=if null (Thm.hyp rebuilt) andalso
              Term.aconv (Thm.concl rebuilt) (G.representative graph (#node target))
            then () else raise ERR "close" "stripped Goal did not close sequent"
          val imported=N.target_import_for work transfer
          val whole=boolSyntax.mk_eq
            (#original imported,G.representative graph (#node target))
          val reversed=boolSyntax.mk_eq
            (G.representative graph (#node target),#original imported)
          val _=admit_effect owner (#output_limit limits)
            [Thm.concl (#bridge imported),Thm.concl (#bridge target),
             whole,reversed,Thm.concl rebuilt,#original imported]
          val bridge=W.with_step work (fn () => inspect owner (fn () =>
            Thm.TRANS (#bridge imported) (#bridge target)))
          val equation=W.with_step work (fn () => inspect owner (fn () =>
            Thm.SYM bridge))
          val raw=W.with_step work (fn () => inspect owner (fn () =>
            Thm.EQ_MP equation rebuilt))
          val closed=W.with_step work (fn () => inspect owner (fn () =>
            P.record_closed_from_import graph root
              {node= #node target,theorem=raw,
               template_limit= #template_limit limits,
               check_type=fn ty => inspect owner (fn () => check_type ty)}))
    in N.close_query_proof work claim closed end
  fun solved_for expected query =
    let val Query {plan=Plan {solved,...},...}=held expected query
    in Option.isSome solved end
  fun close_solved expected query =
    let val Query {plan=plan as Plan {owner=owner as Owner
          {work,graph,limits,phase,...},goal,solved,...},...}=
          held expected query
    in protected owner (fn () =>
      let val _=if !phase=Executed then phase := Closed else
            raise ERR "close_solved" "zero-subgoal receiver consumed"
          val (node,contradiction)=case solved of SOME data => data
            | NONE => raise ERR "close_solved" "not a solved NO_SPLIT query"
          val atom=G.representative graph node
          val target=G.representative graph goal
          val _=admit_effect owner (#output_limit limits)
            [atom,target,boolSyntax.mk_eq (atom,target)]
          val proof=W.with_step work (fn () => inspect owner (fn () =>
            let val assumed=Thm.ASSUME atom
            in if contradiction then Drule.CONTR target assumed else
              Thm.EQ_MP (Thm.ALPHA atom target) assumed end))
      in finish plan proof end) end
  fun close_for expected query supplied edge =
    let val Query {plan=Plan {owner=owner as Owner
          {work,graph,root,sources,limits,transfer,claim,phase,check_type,...},
          frame,goal,assumptions,steps,normalization,...},denied,block}=
          held expected query
        val _=case !block of SOME actual =>
          if Portable.pointer_eq (actual,supplied) then () else
            (W.close expected;raise ERR "close" "foreign registered block")
        | NONE => (W.close expected;raise ERR "close" "query was not frozen")
    in protected owner (fn () =>
      let val _=if !phase=Frozen then phase := Closed else
            raise ERR "close" "query receiver consumed"
          val _=P.validate_block_for expected supplied
          val scope= #scope (Scope.description_for work frame)
          val _=if P.scope supplied=scope andalso
              P.sources supplied=S.assumption_nodes sources @
                [S.denied_goal_node sources] @ assumptions @ [denied]
            then () else raise ERR "close" "actual frame/Source prefix changed"
          val bottom=G.constant graph scope boolSyntax.F
          val negate=G.constant graph scope boolSyntax.negation
          (* Owned private table lookup is actual SAME-W work, even though
             the returned name/definition is only retained metadata. *)
          val (name_goal,name_bottom,name_denied,false_edge,name_negate,
               denied_definition,negate_definition)=
            W.with_step work (fn () => inspect owner (fn () =>
              (P.name supplied goal,P.name supplied bottom,
               P.name supplied denied,P.definition supplied bottom,
               P.name supplied negate,P.definition supplied denied,
               P.definition supplied negate)))
          val negative=boolSyntax.mk_neg name_goal
          val proxy=Term.mk_comb (name_negate,name_goal)
          (* AP_THM of the constant definition, then TRANS with the actual
             application definition. Both complete conclusions and Hyp
             are admitted before constructor performs either operation. *)
          val constructor_terms=
            [boolSyntax.mk_eq (proxy,negative),
             boolSyntax.mk_eq (name_denied,negative)] @
            List.concat (List.map (fn th => Thm.concl th::Thm.hyp th)
              [P.theorem supplied denied_definition,
               P.theorem supplied negate_definition])
          val _=admit_effect owner (#template_limit limits) constructor_terms
          val denial_edge=W.with_step work (fn () =>
            inspect owner (fn () => P.constructor supplied denied))
          val _=if Term.aconv (Thm.concl (P.theorem supplied edge)) name_bottom
            then () else raise ERR "close" "edge is not THIS contradiction"
          val named=compose owner supplied
            [name_goal,negative,name_denied,boolSyntax.F,
             boolSyntax.mk_imp (name_denied,boolSyntax.F),
             boolSyntax.mk_eq (name_denied,negative),
             boolSyntax.mk_eq (negative,name_denied)]
            (fn [contradiction,truth_false,denial] =>
              let val contradiction=Thm.EQ_MP truth_false contradiction
                  val assumed=Thm.ASSUME negative
                  val proxy=Thm.EQ_MP (Thm.SYM denial) assumed
                  val contradiction=Drule.PROVE_HYP proxy contradiction
              in Thm.CCONTR name_goal contradiction end
             | _ => raise ERR "close" "fixed CCONTR arity")
            [edge,false_edge,denial_edge]
          val proved=W.with_step work (fn () =>
            inspect owner (fn () => P.realize supplied goal named))
      in finish (Plan {owner=owner,frame=frame,goal=goal,
          assumptions=assumptions,steps=steps,types=[],
          normalization=normalization,solved=NONE}) proved end) end
end
