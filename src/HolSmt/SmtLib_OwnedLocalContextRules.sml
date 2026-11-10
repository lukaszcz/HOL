(* Bounded conditional proof seeds; no PURE or REV_FULL_SIMP replacement. *)
structure SmtLib_OwnedLocalContextRules :> SmtLib_OwnedLocalContextRules =
struct
  structure G=SmtReplayGraph
  structure S=SmtReplaySource
  structure W=SmtReplayInvocationWork
  structure P=SmtReplayProof
  structure Q=SmtLib_OwnedStrippedNaturalQuery
  structure Scope=SmtReplayOwnedScopeReceipt
  val _=SmtLib_OwnedStrippedNaturalQuery.description_for
  val ERR=Feedback.mk_HOL_ERR "SmtLib_OwnedLocalContextRules"
  datatype phase=Fresh | Prepared | Executed | Retired
  datatype owner=Owner of
    {work:W.portfolio,graph:G.graph,root:G.scope,sources:S.sources,
     query:Q.query,frame:Scope.receipt,scope:G.scope,
     assumptions:G.node list,goal:G.node,denied:G.node,
     limits:W.limits,epoch:int,symbols:int,phase:phase ref,
     paths:G.closure_child list ref,
     check_type:Type.hol_type -> unit}
  datatype proof=Proof of {conclusion:Term.term,rule:operation}
  and operation=Assume of G.node | Conjunct of bool * proof
    | Truth of proof | Falsehood of proof
    | Discharge of Term.term * proof
  datatype syntax=Held of G.node | Constant of Term.term
    | Application of syntax * syntax
  type row={slot:int,assumption:G.node,fixed:Term.term list,
    generalized:Term.term list,program:proof,target:syntax}
  datatype plan=Plan of {owner:owner,rows:row list,used:bool ref}
  datatype catalogue=Catalogue of {owner:owner,rules:rule list}
  and rule=Rule of {owner:owner,row:row,conditional:P.closed_fact}
  fun close (Owner {work,phase,...})=(phase:=Retired;W.close work)
  fun protect owner action=action () handle primary =>
    (close owner;raise primary)
  fun active (Owner {work,graph,root,sources,query,frame,scope,
      assumptions,goal,denied,limits,epoch,symbols,phase,paths,...})=
    (if !phase=Retired then raise ERR "active" "context owner retired"
       else ();
     W.validate work graph root sources limits;
     if Type.type_epoch ()=epoch andalso Term.term_epoch ()=symbols then ()
       else raise ERR "active" "declaration retirement changed";
     let val data=Q.description_for work query
         val actual=Scope.description_for work frame
     in if Portable.pointer_eq (#frame data,frame) andalso
           #scope actual=scope andalso #assumptions data=assumptions andalso
           #goal data=goal andalso #denied data=denied andalso
           Portable.pointer_eq (#original_sources data,sources) then () else
          raise ERR "active" "genuine query context changed" end;
     List.app (fn child=>ignore
       (G.closure_child_node graph scope child)) (!paths))
  fun expected expected_work owner=case owner of Owner {work,...} =>
    ((if Portable.pointer_eq (work,expected_work) then active owner else
       raise ERR "expected" "foreign expected Work")
     handle primary => (W.close expected_work;raise primary))
  fun inspect owner action=
    (active owner;let val answer=action () in active owner;answer end)
  fun tick (owner as Owner {work,...}) n=
    (active owner;W.spend work n;active owner)
  fun begin work {query,check_type}=
    let val data=Q.description_for work query
        val sources=W.original_sources work
        val graph=S.owning_graph sources val root=S.owning_scope sources
        val frame= #frame data
        val actual=Scope.description_for work frame
        val _=if Portable.pointer_eq (#original_sources data,sources) andalso
            Portable.pointer_eq (#graph actual,graph) andalso
            Portable.pointer_eq (#sources actual,sources) andalso
            #root actual=root then () else
          raise ERR "begin" "foreign query context"
        val owner=Owner {work=work,graph=graph,root=root,sources=sources,
          query=query,frame=frame,scope= #scope actual,
          assumptions= #assumptions data,goal= #goal data,denied= #denied data,
          limits=W.semantic_limits work,epoch=Type.type_epoch (),
          symbols=Term.term_epoch (),phase=ref Fresh,paths=ref [],
          check_type=check_type}
    in active owner;owner end handle primary => (W.close work;raise primary)
  fun conclusion (Proof {conclusion,...})=conclusion
  fun make term rule=Proof {conclusion=term,rule=rule}
  fun raw owner node=case owner of Owner {graph,...}=>
    inspect owner (fn()=>G.representative graph node)
  fun children (Proof {rule,...})=case rule of Assume _=>[]
    | Conjunct (_,p)=>[p] | Truth p=>[p]
    | Falsehood p=>[p] | Discharge (_,p)=>[p]
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
        | walk (t::rest) raw inc=
          let val _=tick owner 1 val raw=raw+1 val inc=inc+1
              val _=if raw<=limit andalso inc<=limit then () else
                raise ERR "quote" "bounded context proof operation exceeded"
              val _=ty (Term.type_of t)
          in if Term.is_comb t then let val (f,x)=Term.dest_comb t
               in walk (f::x::rest) raw inc end
             else if Term.is_abs t then let val (v,b)=Term.dest_abs t
                 val _=if inc+1<=limit then () else
                   raise ERR "quote" "binder VARIABLE operation exceeded"
                 val _=ty (Term.type_of v)
                 val _=tick owner (String.size (#1 (Term.dest_var v)))
               in walk (b::rest) raw (inc+1) end
             else (if Term.is_var t then
                 tick owner (String.size (#1 (Term.dest_var t)))
               else if Term.is_const t then
                 let val {Thy,Name,...}=Term.dest_thy_const t
                 in tick owner (String.size Thy+String.size Name) end else ();
               walk rest raw inc) end
    in walk [term] 0 0 end
  fun held owner node=
    let val Owner {graph,scope,paths,...}=owner
        val child=inspect owner (fn()=>G.closure_root graph scope node)
        val _=paths:=child:: !paths
    in child end
  fun operator owner node term=case owner of Owner {graph,...}=>
    (tick owner 1;case G.view graph node of G.Constant _=>
       Term.same_const (raw owner node) term | _=>false)
  fun binary owner child term=
    let val Owner {graph,scope,...}=owner val _=tick owner 1
        val node=G.closure_child_node graph scope child
    in case G.view graph node of G.Application _=>
      let val (left,right)=G.closure_application_children graph scope child
          val n=G.closure_child_node graph scope left
      in case G.view graph n of G.Application _=>
           let val (head,a)=G.closure_application_children graph scope left
           in if operator owner (G.closure_child_node graph scope head) term
                then SOME (a,right) else NONE end
         | _=>NONE end
      | _=>NONE end
  fun unary owner child term=
    let val Owner {graph,scope,...}=owner val _=tick owner 1
        val node=G.closure_child_node graph scope child
    in case G.view graph node of G.Application _=>
      let val (head,a)=G.closure_application_children graph scope child
      in if operator owner (G.closure_child_node graph scope head) term
           then SOME a else NONE end
      | _=>NONE end
  fun node_of owner child=case owner of Owner {graph,scope,...}=>
    inspect owner (fn()=>G.closure_child_node graph scope child)
  fun prepare (owner as Owner
      {work,graph,scope,assumptions,limits,phase,check_type,...})=
    protect owner (fn()=>W.with_step work (fn()=>
    let
      val _=active owner
      val _=if !phase=Fresh then phase:=Prepared else
        raise ERR "prepare" "context preparation consumed"
      val types=ref ([]:Type.hol_type list)
      val cap= #output_limit limits
      fun inspected term=quote owner cap types term
      (* The equality operator is derived from the already admitted leaf
         type. It is syntax metadata here, not a graph node or proof. *)
      fun eqop t=
        #1 (Term.dest_comb (#1 (Term.dest_comb
          (boolSyntax.mk_eq (t,t)))))
      fun imp a b=Application (Application
        (Constant boolSyntax.implication,Held a),b)
      fun original slot assumption=
        let val term=raw owner assumption
            val _=inspected term
            (* FV enumeration is prospective metadata; actual primitive
               constructor/name work is quoted by the full syntax walk. *)
            val fixed=inspect owner (fn()=>Term.free_vars term)
            val seed=make term (Assume assumption)
            fun leaves child program=
              case binary owner child boolSyntax.conjunction of
                SOME (a,b)=>
                  let val pa=make (raw owner (node_of owner a))
                        (Conjunct (true,program))
                      val pb=make (raw owner (node_of owner b))
                        (Conjunct (false,program))
                  in leaves a pa @
                     leaves b pb end
              | NONE=>
                  let
                    val current=node_of owner child
                    val value=raw owner current
                    val (base,target)=case binary owner child
                        (eqop value) of
                        SOME _ => (program,Held current)
                      | NONE=> if boolSyntax.is_imp_only value then
                          (program,Held current)
                        else (case unary owner child boolSyntax.universal of
                          SOME _ => (program,Held current)
                        | NONE=> (case unary owner child boolSyntax.negation of
                          SOME p=>
                            let val n=node_of owner p val t=raw owner n
                            in (make (boolSyntax.mk_eq (t,boolSyntax.F))
                                  (Falsehood program),
                                Application (Application
                                  (Constant (eqop t),Held n),
                                  Constant boolSyntax.F)) end
                        | NONE=>
                            (make (boolSyntax.mk_eq (value,boolSyntax.T))
                               (Truth program),
                             Application (Application
                               (Constant (eqop value),Held current),
                               Constant boolSyntax.T))))
                    val closed=make (boolSyntax.mk_imp (term,conclusion base))
                      (Discharge (term,base))
                  in [{slot=slot,assumption=assumption,fixed=fixed,
                    generalized=[],program=closed,
                    target=imp assumption target}:row] end
        in leaves (held owner assumption) seed end
      fun rows [] _=[]
        | rows (a::rest) slot=(tick owner 1;
            original slot a @ rows rest (slot+1))
      val prepared=rows assumptions 0
      fun portfolio (row:row)=
        let val origin=raw owner (#assumption row)
            fun walk p=
              (List.app walk (children p);
               inspected (conclusion p);inspected origin;
               case p of Proof {rule=Truth previous,...}=>
                   let val t=conclusion previous
                       val v= #1 (boolSyntax.dest_forall
                         (Thm.concl boolTheory.EQ_CLAUSES))
                       val instantiated=boolSyntax.mk_eq
                         (boolSyntax.mk_eq (t,boolSyntax.T),t)
                       val original=boolSyntax.mk_forall (v,
                         boolSyntax.mk_eq
                           (boolSyntax.mk_eq (v,boolSyntax.T),v))
                   in inspected instantiated;
                      quote owner (#template_limit limits) types original end
                 | Proof {rule=Falsehood previous,...}=>
                   let val t=boolSyntax.dest_neg (conclusion previous)
                       val v= #1 (boolSyntax.dest_forall
                         (Thm.concl boolTheory.EQ_CLAUSES))
                       val instantiated=boolSyntax.mk_eq
                         (boolSyntax.mk_eq (t,boolSyntax.F),
                           boolSyntax.mk_neg t)
                       val original=boolSyntax.mk_forall (v,
                         boolSyntax.mk_eq (boolSyntax.mk_eq (v,boolSyntax.F),
                           boolSyntax.mk_neg v))
                   in inspected instantiated;
                      quote owner (#template_limit limits) types original end
                 | _=>())
            val _=walk (#program row)
            val final=conclusion (#program row)
            val bridge=boolSyntax.mk_eq (final,final)
            val _=List.app inspected [final,bridge]
            val _=List.app (quote owner (#template_limit limits) types)
              [final,bridge,bridge,bridge]
        in () end
      val _=List.app portfolio prepared
      val _=List.app (fn ty=>inspect owner (fn()=>check_type ty))
        (List.rev (!types))
    in Plan {owner=owner,rows=prepared,used=ref false} end))
  fun materialize owner caller target =
    let val Owner {graph,limits,...}=owner
        val cap= #template_limit limits
    in case target of Held node=>
         (tick owner 1;ignore (G.type_of graph node);node)
      | Constant term=>inspect owner (fn()=>G.constant graph caller term)
      | Application (left,right)=>
          let val f=materialize owner caller left
              val x=materialize owner caller right
          in inspect owner (fn()=>G.application graph caller (f,x)) end
    end
  fun execute (Plan {owner=owner as Owner
      {work,graph,scope,limits,phase,check_type,...},rows,used})=
    protect owner (fn()=>W.with_step work (fn()=>
    let
      val _=active owner
      val _=if !phase=Prepared andalso not (!used) then
        (used:=true;phase:=Executed) else
        raise ERR "execute" "context rule plan consumed"
      val memo=ref ([]:(proof * Thm.thm) list)
      fun replay value=
        let
          fun find []=NONE
            | find ((held,theorem)::rest)=
                (tick owner 1;if Portable.pointer_eq (held,value) then
                   SOME theorem else find rest)
          fun compute (Proof {conclusion=statement,rule})=
            let
              val theorem=case rule of
                  Assume node=>inspect owner
                    (fn()=>Thm.ASSUME (raw owner node))
                | Conjunct (yes,proof)=>
                    let val th=replay proof in inspect owner (fn()=>
                      if yes then Thm.CONJUNCT1 th else Thm.CONJUNCT2 th) end
                | Truth proof=>
                    let val th=replay proof in inspect owner
                      (fn()=>Drule.EQT_INTRO th) end
                | Falsehood proof=>
                    let val th=replay proof in inspect owner
                      (fn()=>Drule.EQF_INTRO th) end
                | Discharge (assumption,proof)=>
                    let val th=replay proof in inspect owner
                      (fn()=>Thm.DISCH assumption th) end
              val _=if Portable.pointer_eq (Thm.concl theorem,statement)
                  orelse inspect owner (fn()=>Term.aconv
                    (Thm.concl theorem) statement) then () else
                raise ERR "execute" "prospective context statement changed"
            in theorem end
          val _=active owner
          val answer=case find (!memo) of SOME theorem=>theorem
            | NONE=>let val th=compute value
                    in memo:=(value,th):: !memo;th end
          val _=active owner
        in answer end
      fun record (row:row)=
        let val theorem=replay (#program row)
            val node=materialize owner scope (#target row)
            val statement=raw owner node
            val aligned=inspect owner (fn()=>Thm.EQ_MP
              (Thm.ALPHA (Thm.concl theorem) statement) theorem)
            val _=if null (Thm.hyp aligned) then () else
              raise ERR "execute" "local hypothesis escaped its condition"
            val fact=inspect owner (fn()=>P.record_closed graph scope
              {node=node,theorem=aligned,
               template_limit= #template_limit limits,
               check_type=fn ty=>inspect owner (fn()=>check_type ty)})
        in Rule {owner=owner,row=row,conditional=fact} end
      val rules=List.map record rows
    in Catalogue {owner=owner,rules=rules} end))
  fun validate_for work (Catalogue {owner,rules})=
    (expected work owner;
     List.app (fn Rule {conditional,...}=>
       case owner of Owner {graph,scope,limits,...}=>
         P.validate_closed_fact graph scope (#template_limit limits)
           conditional) rules;
     expected work owner)
    handle primary=>(W.close work;raise primary)
  fun context_for work (Catalogue {owner,...}) =
    let val _=expected work owner
        val Owner {query,frame,assumptions,...}=owner
    in {query=query,frame=frame,assumptions=assumptions} end
  fun rules_for work (catalogue as Catalogue {rules,...})=
    (validate_for work catalogue;rules)
  fun describe_for work (Rule {owner,row,conditional})=
    let val _=expected work owner
        val Owner {query,frame,assumptions,graph,scope,limits,...}=owner
        val _=P.validate_closed_fact graph scope
          (#template_limit limits) conditional
        val _=expected work owner
    in {query=query,frame=frame,original_assumptions=assumptions,
      assumption_slot= #slot row,assumption= #assumption row,
      fixed_variables= #fixed row,generalized_variables= #generalized row,
      conditional=conditional} end
    handle primary=>(W.close work;raise primary)
end
