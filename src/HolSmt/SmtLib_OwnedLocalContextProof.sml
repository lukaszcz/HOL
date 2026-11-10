structure SmtLib_OwnedLocalContextProof :> SmtLib_OwnedLocalContextProof =
struct
  structure G=SmtReplayGraph
  structure S=SmtReplaySource
  structure W=SmtReplayInvocationWork
  structure P=SmtReplayProof
  structure Q=SmtLib_OwnedStrippedNaturalQuery
  structure Ctx=SmtLib_OwnedLocalContextRules
  structure M=SmtLib_LocalContextRuleMatch
  structure Scope=SmtReplayOwnedScopeReceipt
  val _=SmtLib_OwnedLocalContextRules.context_for
  val _=SmtLib_LocalContextRuleMatch.instance_context_for
  val _=SmtLib_OwnedStrippedNaturalQuery.close_for
  val ERR=Feedback.mk_HOL_ERR "SmtLib_OwnedLocalContextProof"
  datatype phase=Open | Closing | Closed | Retired
  datatype owner=Owner of
    {work:W.portfolio,graph:G.graph,root:G.scope,sources:S.sources,
     query:Q.query,catalogue:Ctx.catalogue,frame:Scope.receipt,
     scope:G.scope,assumptions:G.node list,goal:G.node,denied:G.node,
     epoch:int,symbols:int,phase:phase ref,
     paths:G.closure_child list ref,
     derivations:(Term.term * Thm.thm) list ref,
     instances:M.instance list ref,check_type:Type.hol_type -> unit}
  datatype proof=Proof of {owner:owner,theorem:Thm.thm}
  fun retire (Owner {work,phase,...})=(phase:=Retired;W.close work)
  fun protect owner action=action () handle primary=>
    (retire owner;raise primary)
  fun active (Owner {work,graph,root,sources,query,catalogue,frame,scope,
      assumptions,goal,denied,epoch,symbols,phase,paths,instances,...})=
    (if !phase=Open orelse !phase=Closing then () else
       raise ERR "active" "local proof owner retired or closed";
     W.validate work graph root sources (W.semantic_limits work);
     if Type.type_epoch ()=epoch andalso Term.term_epoch ()=symbols then ()
       else raise ERR "active" "declaration retirement changed";
     Ctx.validate_for work catalogue;
     let val data=Q.description_for work query
         val where_=Scope.description_for work frame
     in if Portable.pointer_eq (#frame data,frame) andalso
           #scope where_=scope andalso #assumptions data=assumptions andalso
           #goal data=goal andalso #denied data=denied then () else
          raise ERR "active" "authentic query context changed" end;
     List.app (fn child=>ignore
       (G.closure_child_node graph scope child)) (!paths);
     List.app (fn instance=>ignore
       (M.instance_fact_for work instance)) (!instances))
  fun inspect owner action=
    (active owner;let val value=action () in active owner;value end)
  fun tick (owner as Owner {work,...}) amount=
    inspect owner (fn()=>W.spend work amount)
  fun expected work (owner as Owner {work=held,...})=
    ((if Portable.pointer_eq (work,held) then active owner else
        raise ERR "expected" "foreign expected Work")
     handle primary=>(W.close work;raise primary))
  fun owned owner (Proof {owner=held,theorem})=
    (if Portable.pointer_eq (owner,held) then () else
       raise ERR "owned" "foreign local proof";
     active owner;theorem)
  fun begin work {catalogue,check_type}=
    let val data=Ctx.context_for work catalogue
        val query= #query data val original=Q.description_for work query
        val sources=W.original_sources work
        val graph=S.owning_graph sources val root=S.owning_scope sources
        val frame= #frame data
        val where_=Scope.description_for work frame
        val owner=Owner {work=work,graph=graph,root=root,sources=sources,
          query=query,catalogue=catalogue,frame=frame,scope= #scope where_,
          assumptions= #assumptions data,goal= #goal original,
          denied= #denied original,epoch=Type.type_epoch (),
          symbols=Term.term_epoch (),phase=ref Open,paths=ref [],
          derivations=ref [],instances=ref [],check_type=check_type}
    in active owner;owner end handle primary=>(W.close work;raise primary)
  (* Actual repeated annotations and binder VARIABLE incidence. This is
     charged metadata, not a universal bound on private/kernel work. *)
  fun quote owner limit types term=
    let
      fun ty t=
        (tick owner 1;types:=t:: !types;
         if Type.is_vartype t then
           tick owner (String.size (Type.dest_vartype t))
         else let val {Thy,Tyop,Args}=Type.dest_thy_type t
              in tick owner (String.size Thy+String.size Tyop);
                 List.app ty Args end)
      fun walk [] raw inc=()
        | walk (term::rest) raw inc=
          let val _=tick owner 1 val raw=raw+1 val inc=inc+1
              val _=if raw<=limit andalso inc<=limit then () else
                raise ERR "quote" "local proof operation exceeds syntax cap"
              val _=ty (Term.type_of term)
          in if Term.is_comb term then let val (f,x)=Term.dest_comb term
               in walk (f::x::rest) raw inc end
             else if Term.is_abs term then let val (v,b)=Term.dest_abs term
                 val _=if inc+1<=limit then () else
                   raise ERR "quote" "binder VARIABLE exceeds syntax cap"
                 val _=ty (Term.type_of v)
                 val _=tick owner (String.size (#1 (Term.dest_var v)))
               in walk (b::rest) raw (inc+1) end
             else (if Term.is_var term then
                 tick owner (String.size (#1 (Term.dest_var term)))
               else if Term.is_const term then
                 let val {Thy,Name,...}=Term.dest_thy_const term
                 in tick owner (String.size Thy+String.size Name) end else ();
               walk rest raw inc) end
    in walk [term] 0 0 end
  fun admit owner limit terms=
    let val Owner {check_type,...}=owner
        val types=ref ([]:Type.hol_type list)
        val _=List.app (quote owner limit types) terms
    in List.app (fn ty=>inspect owner (fn()=>check_type ty))
      (List.rev (!types)) end
  fun raw owner node=case owner of Owner {graph,scope,paths,...}=>
    let val child=inspect owner (fn()=>G.closure_root graph scope node)
        val _=paths:=child:: !paths
    in inspect owner (fn()=>G.representative graph node) end
  fun clean theorem=
    let val (oracles,_)=Tag.dest_tag (Thm.tag theorem)
    in List.all (fn oracle=>oracle="DISK_THM") oracles andalso
       null (Tag.axioms_of (Thm.tag theorem)) end
  fun capture (owner as Owner {assumptions,derivations,...}) theorem=
    let val allowed=List.map (raw owner) assumptions @
          List.map #1 (!derivations)
        val _=if clean theorem andalso List.all (fn h=>List.exists
          (fn actual=>Portable.pointer_eq (actual,h)) allowed)
          (Thm.hyp theorem) then () else
            raise ERR "capture" "foreign Hyp or proof tag escaped"
    in Proof {owner=owner,theorem=theorem} end
  fun assumption (owner as Owner {work,assumptions,...}) slot=
    protect owner (fn()=>W.with_step work (fn()=>
      let val _=active owner
          val _=if slot>=0 andalso slot<length assumptions then () else
            raise ERR "assumption" "absent actual local occurrence"
          val term=raw owner (List.nth (assumptions,slot))
          val _=admit owner (#output_limit (W.semantic_limits work)) [term]
      in capture owner (inspect owner (fn()=>Thm.ASSUME term)) end))
  fun assume_derived (owner as Owner {work,derivations,...}) value=
    protect owner (fn()=>W.with_step work (fn()=>
      let val theorem=owned owner value val term=Thm.concl theorem
          val _=if List.exists (fn h=>inspect owner
              (fn()=>Term.aconv h term)) (Thm.hyp theorem) then
            raise ERR "assume_derived" "cyclic local hypothesis derivation"
            else ()
          val _=admit owner (#output_limit (W.semantic_limits work))
            (term::Thm.hyp theorem)
          (* Only a completed SAME-owner derivation issues this slot.
             It is local Gamma', never an Original Source occurrence. *)
          val _=tick owner 1
          val _=derivations:=(term,theorem):: !derivations
      in capture owner (inspect owner (fn()=>Thm.ASSUME term)) end))
  fun truth (owner as Owner {work,...})=
    protect owner (fn()=>W.with_step work (fn()=>
      (admit owner (#output_limit (W.semantic_limits work)) [boolSyntax.T];
       capture owner (inspect owner (fn()=>boolTheory.TRUTH)))))
  fun apply (owner as Owner {work,query,frame,scope,assumptions,instances,...})
      {instance,conditions}=
    protect owner (fn()=>W.with_step work (fn()=>
    let
      (* Authenticate SAME context before activating foreign proof inputs. *)
      val context=M.instance_context_for work instance
      val _=if Portable.pointer_eq (#query context,query) andalso
          Portable.pointer_eq (#frame context,frame) andalso
          #original_assumptions context=assumptions then () else
        raise ERR "apply" "instance belongs to a different local context"
      val target=M.instance_target_for work instance
      val _=if #traversal target=scope then () else
        raise ERR "apply" "instance has a different actual traversal frame"
      val premises=List.map (owned owner) conditions
      val fact=M.instance_fact_for work instance
      val rule=P.closed_original fact
      val slot= #assumption_slot context
      val original=raw owner (List.nth (assumptions,slot))
      val terms=ref [Thm.concl rule,original]
      fun forecast current []=current
        | forecast current (proof::rest)=
          let val (ant,body)=boolSyntax.dest_imp current
              val value=Thm.concl proof
              val _=terms:=ant::value::body::
                boolSyntax.mk_eq (value,ant)::Thm.hyp proof @ !terms
              val _=if inspect owner (fn()=>Term.aconv value ant) then () else
                raise ERR "apply" "unproved or different local condition"
          in forecast body rest end
      val (first,rest)=boolSyntax.dest_imp (Thm.concl rule)
      val _=if inspect owner (fn()=>Term.aconv first original) then () else
        raise ERR "apply" "rigid original antecedent changed"
      val final=forecast rest premises
      val _=if boolSyntax.is_imp final then
        raise ERR "apply" "missing local condition proof" else ()
      val _=admit owner (#output_limit (W.semantic_limits work)) (!terms)
      val _=instances:=instance:: !instances
      val assumed=inspect owner (fn()=>Thm.ASSUME original)
      val first=inspect owner (fn()=>Thm.MP rule assumed)
      fun discharge (premise,theorem)=
        let val ant= #1 (boolSyntax.dest_imp (Thm.concl theorem))
            val aligned=inspect owner (fn()=>Thm.EQ_MP
              (Thm.ALPHA (Thm.concl premise) ant) premise)
        in inspect owner (fn()=>Thm.MP theorem aligned) end
      val proved=List.foldl discharge first premises
    in capture owner proved end))
  fun rewrite (owner as Owner {work,...}) {equality,premise,reverse}=
    protect owner (fn()=>W.with_step work (fn()=>
      let val equation=owned owner equality val proof=owned owner premise
          val (left,right)=boolSyntax.dest_eq (Thm.concl equation)
          val (from,to)=if reverse then (right,left) else (left,right)
          val _=admit owner (#output_limit (W.semantic_limits work))
            (Thm.concl equation::boolSyntax.mk_eq (from,to)::
             boolSyntax.mk_eq (Thm.concl proof,from)::to::
             Thm.concl proof::Thm.hyp equation @ Thm.hyp proof)
          val _=if inspect owner (fn()=>Term.aconv
              (Thm.concl proof) from) then () else
            raise ERR "rewrite" "proof is not the equality operand"
          val equation=if reverse then
            inspect owner (fn()=>Thm.SYM equation) else equation
          val proof=inspect owner (fn()=>Thm.EQ_MP
            (Thm.ALPHA (Thm.concl proof) from) proof)
      in capture owner (inspect owner (fn()=>Thm.EQ_MP equation proof)) end))
  fun replace_hyp (owner as Owner {work,...}) {hypothesis,premise}=
    protect owner (fn()=>W.with_step work (fn()=>
      let val hp=owned owner hypothesis val proof=owned owner premise
          val _=admit owner (#output_limit (W.semantic_limits work))
            (boolSyntax.mk_imp (Thm.concl hp,Thm.concl proof)::
             Thm.concl hp::Thm.concl proof::Thm.hyp hp @ Thm.hyp proof)
      in capture owner (inspect owner (fn()=>Drule.PROVE_HYP hp proof)) end))
  fun conjunct (owner as Owner {work,...}) {premise,left}=
    protect owner (fn()=>W.with_step work (fn()=>
      let val proof=owned owner premise
          val (a,b)=boolSyntax.dest_conj (Thm.concl proof)
          val final=if left then a else b
          val _=admit owner (#output_limit (W.semantic_limits work))
            (final::Thm.concl proof::Thm.hyp proof)
      in capture owner (inspect owner (fn()=>if left then
        Thm.CONJUNCT1 proof else Thm.CONJUNCT2 proof)) end))
  fun describe_for work (Proof {owner,theorem})=
    (expected work owner;case owner of Owner {frame,...}=>
      {frame=frame,conclusion=Thm.concl theorem,hypotheses=Thm.hyp theorem})
  (* All conditional hypotheses are discharged before recording. The
     receiver uses the old registered query block and its exact Source
     prefix; no new local assertion is called an Original Source. *)
  fun close_goal (owner as Owner {work,graph,scope,sources,query,goal,
      denied,assumptions,derivations,phase,check_type,...}) value=
    protect owner (fn()=>
    let
      val incoming=owned owner value
      val proof=W.with_step work (fn()=>
        let fun transfer ((term,derived),proof)=
              let val _=admit owner
                    (#output_limit (W.semantic_limits work))
                    (boolSyntax.mk_imp (term,Thm.concl proof)::
                     term::Thm.concl proof::Thm.hyp proof @ Thm.hyp derived)
              in inspect owner (fn()=>Drule.PROVE_HYP derived proof) end
            val transported=List.foldl transfer incoming (!derivations)
            val allowed=List.map (raw owner) assumptions
            val _=if List.all (fn h=>List.exists
              (fn actual=>Portable.pointer_eq (h,actual)) allowed)
              (Thm.hyp transported) then () else
                raise ERR "close_goal" "Gamma prime did not return to Gamma"
        in transported end)
      val wanted=raw owner goal
      val _=if inspect owner (fn()=>Term.aconv (Thm.concl proof) wanted)
          then () else raise ERR "close_goal" "not this query's local goal"
      val _=phase:=Closing
      val output= #output_limit (W.semantic_limits work)
      val template= #template_limit (W.semantic_limits work)
      val terms=List.map (raw owner) assumptions
      val statement=List.foldr boolSyntax.mk_imp wanted terms
      val conditional=W.with_step work (fn()=>
        let val portfolio=ref [Thm.concl proof,wanted,statement,
              boolSyntax.mk_eq (Thm.concl proof,wanted)]
            fun forecast (ant,current)=
              let val next=boolSyntax.mk_imp (ant,current)
              in portfolio:=next::current::ant:: !portfolio;next end
            val _=List.foldr forecast wanted terms
            val _=admit owner output (!portfolio @ Thm.hyp proof)
            val _=admit owner template
              [statement,boolSyntax.mk_eq (statement,statement)]
            val aligned=inspect owner (fn()=>Thm.EQ_MP
              (Thm.ALPHA (Thm.concl proof) wanted) proof)
        in List.foldr (fn (ant,th)=>inspect owner
          (fn()=>Thm.DISCH ant th)) aligned terms end)
      val (node,fact)=W.with_step work (fn()=>
        let val imp=inspect owner (fn()=>G.constant graph scope
              boolSyntax.implication)
            fun build (ant,body)=inspect owner (fn()=>G.application graph
              scope (G.application graph scope (imp,ant),body))
            val node=List.foldr build goal assumptions
            val actual=raw owner node
            val bridge=boolSyntax.mk_eq (Thm.concl conditional,actual)
            val _=admit owner template
              [Thm.concl conditional,actual,bridge]
            val aligned=inspect owner (fn()=>Thm.EQ_MP
              (Thm.ALPHA (Thm.concl conditional) actual) conditional)
            val fact=inspect owner (fn()=>P.record_closed graph scope
              {node=node,theorem=aligned,template_limit=template,
               check_type=fn ty=>inspect owner (fn()=>check_type ty)})
        in (node,fact) end)
      val block=Q.freeze_for work query
        {roots=[node],closed_facts=[fact],conversions=[]}
      (* Constructor traverses only the authentic application spine. All
         AP_THM and TRANS conclusions plus actual definition Hyp are quoted
         before the constructor's first kernel operation. *)
      fun named_constructor node=W.with_step work (fn()=>
        let
          val portfolio=ref ([]:Term.term list)
          fun forecast current=
            let val name=P.name block current
                val (actual,extras)=case G.view graph current of
                    G.Application (f,x)=>
                      let val operator=forecast f val operand=P.name block x
                          val actual=Term.mk_comb (operator,operand)
                          val partial=Term.mk_comb (P.name block f,operand)
                          val definition=P.theorem block
                            (P.definition block current)
                      in (actual,Thm.concl definition::Thm.hyp definition @
                        [boolSyntax.mk_eq (partial,actual)]) end
                  | G.Constant _=>
                      let val definition=P.theorem block
                            (P.definition block current)
                      in (G.representative graph current,
                        Thm.concl definition::Thm.hyp definition) end
                  | _=>(name,[])
                val _=portfolio:=boolSyntax.mk_eq (name,actual)::
                  extras @ !portfolio
            in actual end
          val _=inspect owner (fn()=>forecast node)
          val _=admit owner template (!portfolio)
        in inspect owner (fn()=>P.constructor block node) end)
      fun named_compose results operation premises=
        W.with_step work (fn()=>
          let val proofs=List.map (P.theorem block) premises
              val _=admit owner template (results @ List.concat
                (List.map (fn th=>Thm.concl th::Thm.hyp th) proofs))
          in inspect owner (fn()=>P.compose block operation premises) end)
      val seed=W.with_step work
        (fn()=>inspect owner (fn()=>P.closed block fact))
      val base=length (S.assumption_nodes sources)+1
      fun consume ([],_,edge,_)=edge
        | consume (ant::rest,current,edge,index)=
          let val (head,body)=case G.view graph current of
                    G.Application (head,body)=>(head,body)
                | _=>raise ERR "close_goal" "recorded implication disappeared"
              val actual=case G.view graph head of
                  G.Application (_,actual)=>actual
                | _=>raise ERR "close_goal" "recorded implication malformed"
              val _=if actual=ant then () else
                raise ERR "close_goal" "actual Gamma occurrence changed"
              val constructor=named_constructor current
              val (source,name_ant,name_body)=W.with_step work
                (fn()=>inspect owner (fn()=>
                  (P.source block index,P.name block ant,P.name block body)))
              val next=named_compose
                [boolSyntax.mk_imp (name_ant,name_body),name_body]
                (fn [law,shape,premise]=>
                   Thm.MP (Thm.EQ_MP shape law) premise
                  | _=>raise ERR "close_goal" "fixed MP arity")
                [edge,constructor,source]
          in consume (rest,body,next,index+1) end
      val goal_edge=consume (assumptions,node,seed,base)
      val denial_shape=named_constructor denied
      val (denial_edge,false_shape,name_goal,name_false,
           name_denied)=W.with_step work (fn()=>inspect owner (fn()=>
          let val bottom=G.constant graph scope boolSyntax.F
          in (P.source block (base+length assumptions),
            P.definition block bottom,
            P.name block goal,P.name block bottom,P.name block denied) end))
      val contradiction=named_compose
        [boolSyntax.mk_neg name_goal,
         boolSyntax.mk_imp (name_goal,boolSyntax.F),boolSyntax.F,
         boolSyntax.mk_eq (boolSyntax.F,name_false),name_false,name_denied]
        (fn [proved,denial,shape,bottom]=>
           let val neg=Thm.EQ_MP shape denial
               val falsehood=Thm.MP (Thm.NOT_ELIM neg) proved
           in Thm.EQ_MP (Thm.SYM bottom) falsehood end
         | _=>raise ERR "close_goal" "fixed contradiction arity")
        [goal_edge,denial_edge,denial_shape,false_shape]
      val result=Q.close_for work query block contradiction
      val _=phase:=Closed
    in result end)
end
