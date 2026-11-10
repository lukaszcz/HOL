(* Fixed original Source Goal closure; no receipt publication.
   Owning adapters provide the authentic proof/Source/NC/frame guard. *)
structure SmtReplayGoalClose :> SmtReplayGoalClose =
struct
  structure G=SmtReplayGraph
  structure W=SmtReplayInvocationWork
  structure Scope=SmtReplayOwnedScopeReceipt
  structure RP=SmtReplayResourcePolicy
  type profile=SmtReplayNamedContext.profile
  fun clean theorem =
    let val (oracles, _) = Tag.dest_tag (Thm.tag theorem) in
      List.all (fn oracle => oracle = "DISK_THM") oracles andalso
      List.null (Tag.axioms_of (Thm.tag theorem))
    end
  datatype pc_type_task = PCTypeVisit of Type.hol_type
    | PCTypeJoin of Type.hol_type * Type.hol_type list
  fun type_counter error () =
    let
      val memo=ref ([]:(Type.hol_type * IntInf.int) list)
      fun known ty=case List.find
          (fn (held,_)=>Portable.pointer_eq (ty,held)) (!memo) of
          NONE=>NONE | SOME(_,amount)=>SOME amount
      fun saved ty=case known ty of SOME amount=>amount
        | NONE=>raise error ()
      fun count root =
        let
          fun loop []=saved root
            | loop (PCTypeVisit ty::rest)=
                (case known ty of SOME _=>loop rest
                 | NONE=>if Type.is_vartype ty then
                     (memo := (ty,1):: !memo;loop rest)
                   else let val children= #2 (Type.dest_type ty)
                     in loop (List.map PCTypeVisit children @
                       PCTypeJoin (ty,children)::rest) end)
            | loop (PCTypeJoin (ty,children)::rest)=
                let val amount=List.foldl
                      (fn (child,total)=>total+saved child) 1 children
                in memo := (ty,amount):: !memo;loop rest end
        in loop [PCTypeVisit root] end
    in count end
  (* Only the already admitted Source import skeleton is observed here.
     A shared opaque term is cut by pointer identity; a distinct opaque
     pair declines this optimization without opening either binder. Thus
     the final alpha comparison cannot enter a nonidentical abstraction.
     These helpers return a prospectively paid comparison envelope, never
     a proof or a Source correspondence. *)
  exception AlphaOpaque
  fun alpha_type_cost pay ty =
    (pay 4;
     if Type.is_vartype ty then
       let val _=pay 4 val name=Type.dest_vartype ty
           val n=IntInf.fromInt(String.size name)
           val _=pay n
       in 8+n end
     else
       let val _=pay 13 val {Thy,Tyop,Args}=Type.dest_thy_type ty
           val n=IntInf.fromInt(String.size Thy+String.size Tyop)
           val _=pay n
       in 8+n+alpha_types_cost pay Args end)
  and alpha_types_cost pay []=(pay 1;0)
    | alpha_types_cost pay(ty::rest)=
        (pay 4;3+alpha_type_cost pay ty+alpha_types_cost pay rest)
  fun alpha_atom_cost pay term =
    let val _=pay 5
        val ty=Term.type_of term
        val types=alpha_type_cost pay ty
    in if Term.is_var term then
         let val _=pay 7 val(name,_)=Term.dest_var term
             val n=IntInf.fromInt(String.size name)
             val _=pay n
         in 8+types+n end
       else if Term.is_const term then
         let val _=pay 12 val {Thy,Name,...}=Term.dest_thy_const term
             val n=IntInf.fromInt(String.size Thy+String.size Name)
             val _=pay n
         in 8+types+n end
       else (pay 1;raise AlphaOpaque)
    end
  fun alpha_source_cost valid pay graph node left right =
    (valid();pay 6;
     if Portable.pointer_eq(left,right)then 1
     else case G.view graph node of
       G.Application(a,b)=>
         let val _=pay 9
             val _=if Term.is_comb left andalso Term.is_comb right then ()
               else raise AlphaOpaque
             val(x,y)=Term.dest_comb left
             val(u,v)=Term.dest_comb right
             val _=pay 8
             val l=alpha_source_cost valid pay graph a x u
             val r=alpha_source_cost valid pay graph b y v
         in 6+l+r end
     | G.Variable _=>
         (pay 2;alpha_atom_cost pay left+alpha_atom_cost pay right)
     | G.Constant _=>
         (pay 2;alpha_atom_cost pay left+alpha_atom_cost pay right)
     | _=>(pay 1;raise AlphaOpaque))
  datatype plan=Plan of
    {work:W.portfolio,guard:unit -> unit,error:string -> exn,
     contract:SmtReplayNativeContract.contract,
     sources:SmtReplaySource.sources,graph:G.graph,scope:G.scope,
     frame:Scope.receipt,goal:Term.term,canonical:Term.term,bridge:Thm.thm,
     proof:Thm.thm,metrics:(G.node * G.profiled_metric) list,
     profiles:G.policy_opaque_profile list,types:Type.hol_type list,
     check_type:Type.hol_type -> unit,epoch:int,symbols:int,
     direct:bool,used:bool ref}
  fun prepare
      {work,contract,native=(native:SmtReplayNativeContract.limits),
       sources,graph,scope,frame,proof,guard,
       profiles,check_type,error,type_weight,counter} =
    let
        fun pay amount=W.spend_policy work amount
        fun spend amount=pay(IntInf.fromInt amount)
        fun future amount=W.spend_policy work amount
        val _=SmtReplaySource.check_contradiction sources proof
        val goal_source=SmtReplaySource.goal_source sources
        val goal= #original goal_source
        val canonical=SmtReplaySource.canonical_goal sources
        val bridge=SmtReplaySource.goal_bridge sources
        val _=if clean bridge andalso List.null(Thm.hyp bridge)then ()else
          raise error "actual Goal bridge tags/Hyp changed"
        val epoch=Type.type_epoch()val symbols=Term.term_epoch()
        val limits= #semantic_limits native
        val input=IntInf.fromInt(#input_limit limits)
        val output=IntInf.fromInt(#output_limit limits)
        val ceiling=IntInf.fromInt(#type_work_limit native)
        val policy=W.semantic_policy work
        val metrics=ref([]:(G.node * G.profiled_metric)list)
        fun fail text=raise error text
        fun valid()=
          (guard ();
           SmtReplayNativeContract.validate_for work contract;
           ignore(Scope.description_with_policy_for work frame);
           if epoch=Type.type_epoch()andalso symbols=Term.term_epoch()
             then ()else fail "native epochs changed";
           List.app(fn(node,capture)=>
             if #node(G.profiled_metric_data graph scope capture)=node then ()
             else fail "actual Source geometry changed")(!metrics))
        fun tick()=(valid();spend 1)
        fun bounded role cap maximum(p:profile)=
          if #raw p<=cap andalso #inc p<=cap andalso
              RP.allows maximum(#raw p)andalso
              RP.allows maximum(#inc p)andalso #ann p<=ceiling then ()else
            fail role
        fun in_bound p=bounded "final Source input exceeds caller cap"
          input(#input_limit policy)p
        fun out_bound p=bounded "final Source output exceeds caller cap"
          output(#output_limit policy)p
        val types=ref([]:Type.hol_type list)
        val count_type=counter()
        fun own ty=
          let val _=tick()val n=count_type ty
              val _=pay(1+n)
              val _=if n<=ceiling then ()else
                fail "final Source Type exceeds caller cap"
              val _=types:=ty:: !types
          in n end
        val memo=ref([]:(G.node * profile)list)
        fun find_node _ []=NONE
          | find_node n((old,p)::rest)=
              (tick();if old=n then SOME p else find_node n rest)
        fun opaque node=
          let fun seek []=fail "final Source lacks actual opaque profile"
                | seek(p::rest)=
                    (tick();case G.opaque_profile_for_node_with_policy
                       graph scope node p of SOME data=>data
                     | NONE=>seek rest)
          in seek profiles end
        (* No Term destructor or binder opening precedes this genuine graph
           acquisition. Source import itself only exposes applications;
           its opaque leaves retain the identical original term object. *)
        fun graph_shape node=case find_node node(!memo)of SOME p=>p|NONE=>
          let val _=tick()val ty=own(G.type_of graph node)
              val p:profile=case G.view graph node of
                  G.Application(a,b)=>
                    let val x=graph_shape a val y=graph_shape b
                    in {raw=1+ #raw x+ #raw y,inc=1+ #inc x+ #inc y,
                        ann=ty+ #ann x+ #ann y,ty=ty}end
                | G.OpaqueRetained=>
                    let val data=opaque node
                        val _=types:=List.revAppend(#types data,!types)
                    in if #ty data=ty then
                      {raw= #raw data,inc= #inc data,ann= #ann data,ty=ty}
                    else fail "actual opaque Source Type differs"end
                | G.Variable _=>{raw=1,inc=1,ann=ty,ty=ty}
                | G.Constant _=>{raw=1,inc=1,ann=ty,ty=ty}
                | _=>fail "Source import geometry needs its genuine producer"
              val _=in_bound p
              val _=memo:=(node,p):: !memo
          in p end
        fun geometry node=
          let val _=tick()
              val capture=G.prepare_scoped_profiled_metric graph scope
                {node=node,profiles=profiles}
              val data=G.profiled_metric_data graph scope capture
              val _=if #raw data<=input andalso #inc data<=input andalso
                  RP.allows(#input_limit policy)(#raw data)andalso
                  RP.allows(#input_limit policy)(#inc data)then ()else
                fail "final Source geometry exceeds caller input cap"
              val _=metrics:=(node,capture):: !metrics
              val p=graph_shape node
              val _=if #raw p= #raw data andalso #inc p= #inc data then ()
                else fail "actual Source geometry differs"
          in p end
        val canonical_p=geometry(#node goal_source)
        val sources_list=SmtReplaySource.reconciliation_sources sources
        fun hyp_node term []=fail "actual Hyp is outside original Source"
          | hyp_node term((source:G.source)::rest)=
              (tick();if Portable.pointer_eq(term,
                G.representative graph(#node source))then #node source
                else hyp_node term rest)
        val hypotheses=Thm.hyp proof
        val hyp_profiles=List.map(fn term=>
          geometry(hyp_node term sources_list))hypotheses
        (* Source_for/execute_import retain this pairing, not an arbitrary
           ALPHA theorem. Actual original Type ports are measured separately
           and every original application follows the retained graph child. *)
        val original_memo=ref([]:
          (G.node * Term.term * profile)list)
        fun find_original _ _ []=NONE
          | find_original node term((n,t,p)::rest)=
              (tick();if n=node andalso Portable.pointer_eq(t,term)then SOME p
               else find_original node term rest)
        fun original_shape node term=
          case find_original node term(!original_memo)of SOME p=>p|NONE=>
          let val known=graph_shape node
              val _=in_bound known
              val _=tick()val ty=own(Term.type_of term)
              val p:profile=case G.view graph node of
                  G.Application(a,b)=>
                    let val _=if Term.is_comb term then ()else
                          fail "original Source application differs"
                        val(x,y)=Term.dest_comb term
                        val l=original_shape a x val r=original_shape b y
                    in {raw=1+ #raw l+ #raw r,inc=1+ #inc l+ #inc r,
                        ann=ty+ #ann l+ #ann r,ty=ty}end
                | G.OpaqueRetained=>
                    if Portable.pointer_eq(term,G.representative graph node)
                    then known else fail "original opaque Source changed"
                | G.Variable _=>if Term.is_var term then
                    {raw=1,inc=1,ann=ty,ty=ty}else
                      fail "original Source variable differs"
                | G.Constant _=>if Term.is_const term then
                    {raw=1,inc=1,ann=ty,ty=ty}else
                      fail "original Source constant differs"
                | _=>fail "unsupported original Source import producer"
              val _=in_bound p
              val _=original_memo:=(node,term,p):: !original_memo
          in p end
        val original_p=original_shape(#node goal_source)goal
        val bool_ty=own Type.bool
        val false_p:profile={raw=1,inc=1,ann=bool_ty,ty=bool_ty}
        fun negate(p:profile):profile=
          {raw=2+ #raw p,inc=2+ #inc p,ann=4+ #ann p,ty=bool_ty}
        fun equality(a:profile)(b:profile)
              :profile=
          {raw=3+ #raw a+ #raw b,inc=3+ #inc a+ #inc b,
           ann=9+ #ann a+ #ann b,ty=bool_ty}
        val denied_p=negate canonical_p
        val bridge_p=equality original_p canonical_p
        val inverse_p=equality canonical_p original_p
        val (left,right)=boolSyntax.dest_eq(Thm.concl bridge)
        val _=if Portable.pointer_eq(left,goal)andalso
            Portable.pointer_eq(right,canonical)then ()else
          fail "actual Goal bridge endpoints changed"
        (* The exact source bridge remains authenticated even when its
           equality is not an operand of the selected closing programme. *)
        val _=pay 7
        val direct=
          ((let val cost=alpha_source_cost valid pay graph
                  (#node goal_source)goal canonical
                val _=pay(1+cost)
                val _=valid()
                val answer=Term.aconv goal canonical
                val _=valid()
            in answer end)
           handle AlphaOpaque=>(pay 1;false))
        val _=pay 1
        val original_denied_p=if direct then
            (pay 12;negate original_p)else denied_p
        val _=if direct then
            (List.app in_bound
               (false_p::original_p::original_denied_p::hyp_profiles);
             out_bound original_p)
          else
            (List.app in_bound
               (false_p::canonical_p::denied_p::bridge_p::hyp_profiles);
             List.app out_bound[canonical_p,inverse_p,original_p])
        (* Fixed function ports are actual operands of the native wrapper,
           even when Goal and all Hyp roots have only Boolean root types.
           Check their fixed structural envelope before the public getters;
           no new Type constructor is needed for this borrowed portfolio. *)
        val _=if ceiling>=7 then ()else
          fail "final Source fixed function Type exceeds caller cap"
        val neg_type=Term.type_of boolSyntax.negation
        val (partial,_)=Term.dest_comb(Thm.concl bridge)
        val (head,_)=Term.dest_comb partial
        val equality_type=Term.type_of head
        val partial_type=Term.type_of partial
        val _=if own neg_type=3 andalso own equality_type=5 andalso
            own partial_type=3 then ()else
          fail "actual final Source function Type differs"
        fun weight(p:profile)= #raw p+ #inc p+ #ann p
        fun sum ps=List.foldl(fn(p,n)=>n+weight p)0 ps
        fun quote result inputs incoming outgoing=
          let val n=1+weight result+sum inputs+sum incoming+sum outgoing
          in if n<=ceiling then n else
            fail "final Source native input/result/Hyp/Type exceeds caller cap"
          end
        (* Incoming Hyp incidences are retained separately per operand. No
           deduplication or early CCONTR removal reduces this native quote. *)
        val closure_work=if direct then
            quote original_p[original_p,false_p,original_denied_p]
              hyp_profiles hyp_profiles
          else
            let val ccontr=quote canonical_p
                  [canonical_p,false_p,denied_p]hyp_profiles hyp_profiles
                val sym=quote inverse_p[bridge_p][][]
                val eqmp=quote original_p[inverse_p,canonical_p]
                  hyp_profiles hyp_profiles
            in ccontr+sym+eqmp end
        val forest=List.rev(!types)
        val callback_work=List.foldl(fn(ty,n)=>
          n+type_weight ceiling ty)0 forest
        val _=if callback_work<=ceiling then ()else
          fail "final Source callback Type forest exceeds caller cap"
        val _=future(closure_work+callback_work+60)
        val _=valid()
    in Plan{work=work,guard=guard,error=error,contract=contract,
      sources=sources,graph=graph,scope=scope,frame=frame,goal=goal,
      canonical=canonical,bridge=bridge,proof=proof,metrics= !metrics,
      profiles=profiles,types=forest,check_type=check_type,
      epoch=epoch,symbols=symbols,direct=direct,used=ref false}end
  fun execute expected (saved as Plan{work,error,...}) =
    ((if Portable.pointer_eq(expected,work)then ()else
        raise error "different original Work";
      let val Plan{guard,contract,sources,graph,scope,
            frame,goal,canonical,bridge,proof,metrics,types,check_type,
            epoch,symbols,direct,used,...}=saved
          fun valid()=
            (guard ();
             SmtReplayNativeContract.validate_for work contract;
             ignore(Scope.description_with_policy_for work frame);
             if epoch=Type.type_epoch()andalso symbols=Term.term_epoch()
               andalso Portable.pointer_eq(goal,
                 #original(SmtReplaySource.goal_source sources))andalso
               Portable.pointer_eq(canonical,
                 SmtReplaySource.canonical_goal sources)andalso
               Portable.pointer_eq(bridge,SmtReplaySource.goal_bridge sources)
               then ()else raise error
                 "actual Source closure owner changed";
             List.app(fn(node,capture)=>
               if #node(G.profiled_metric_data graph scope capture)=node
               then ()else raise error
                 "actual Source geometry changed")metrics)
          val _=valid()val _=W.spend_policy work 0
          val _=if !used then raise error "used plan"
            else used:=true
          val _=List.app(fn ty=>(valid();check_type ty;valid()))types
          fun call action=
            (valid();let val answer=action()val _=valid()
             in if clean answer then answer else
               raise error "native proof tag changed"end)
          val result=if direct then call(fn()=>
              SmtReplayRuleObservation.CCONTR goal proof)
            else
              let val canonical_proof=call(fn()=>
                    SmtReplayRuleObservation.CCONTR canonical proof)
                  val inverse=call(fn()=>
                    SmtReplayRuleObservation.SYM bridge)
              in call(fn()=>SmtReplayRuleObservation.EQ_MP
                inverse canonical_proof)end
          val _=SmtReplaySource.check_goal sources result
      in result end)
     handle primary=>(W.close expected;raise primary))
end
