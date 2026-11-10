(* Free Source variables AND types are rigid. Only explicit forall binds.
   The originating large Source Hyp is retained, never INSTed or inspected. *)
structure SmtLib_ProjectedSourceRuleMatch :>
    SmtLib_ProjectedSourceRuleMatch =
struct
  structure G=SmtReplayGraph
  structure S=SmtReplaySource
  structure W=SmtReplayInvocationWork
  structure C=SmtLib_OwnedNamedContextSeeds
  structure Scope=SmtReplayOwnedScopeReceipt
  val _=SmtLib_OwnedNamedContextSeeds.projected_rule_for
  val _=SmtReplayOwnedScopeReceipt.validate_lifetime_for
  val ERR=Feedback.mk_HOL_ERR "SmtLib_ProjectedSourceRuleMatch"
  datatype terminal=Equality | Positive | Negative
  type profile={raw:IntInf.int,inc:IntInf.int,ann:IntInf.int}
  datatype tree=Tree of {term:Term.term,ty:Type.hol_type,
    shape:shape,profile:profile,binding:int option}
  and shape=Atom | App of tree*tree | Lam of tree*tree
  datatype phase=Fresh | Compiled | Retired
  datatype owner=Owner of {marker:unit ref,work:W.portfolio,
    graph:G.graph,root:G.scope,sources:S.sources,limits:W.limits,
    rules:C.projected_rule list,frame:Scope.receipt,scope:G.scope,
    epoch:int,symbols:int,phase:phase ref}
  datatype operation=Specialize of tree | Select of bool | Undisch
  datatype schema=Schema of {owner:owner,source:C.projected_rule,
    whole:tree,left:tree,right:tree option,binders:tree list,
    operations:operation list,terminal:terminal}
  datatype matched=Match of {schema:schema,caller:G.scope,
    traversal:G.scope,child:G.closure_child,target:G.node,
    actual:tree,arguments:(int*tree) list,used:bool ref,
    target_frame:Scope.receipt option}
  datatype instance=Instance of {matched:matched,theorem:Thm.thm,
    conditions:Term.term list}
  datatype result=NoMatch | NeedsHigherOrder | Matched of matched
  exception Mismatch
  exception HigherOrder
  fun data (Tree d)=d
  fun term value= #term (data value)
  fun close (Owner {work,phase,...})=(phase:=Retired;W.close work)
  fun protect owner operation=operation () handle primary=>
    (close owner;raise primary)
  fun active (Owner {work,graph,root,sources,limits,rules,frame,scope,
                      epoch,symbols,phase,...})=
    (if !phase<>Retired then () else raise ERR "active" "retired owner";
     W.validate work graph root sources limits;
     Scope.validate_lifetime_for work frame;
     G.validate_scope graph scope;
     if Type.type_epoch ()=epoch andalso Term.term_epoch ()=symbols then ()
       else raise ERR "active" "declaration retirement changed";
     List.app (fn source=>ignore (C.projected_rule_for work source)) rules)
  fun expected work (owner as Owner {work=held,...})=
    ((if Portable.pointer_eq (work,held) then active owner else
        raise ERR "expected" "foreign expected Work")
     handle primary=>(W.close work;raise primary))
  fun call owner operation=
    (active owner;let val value=operation () in active owner;value end)
  fun tick (owner as Owner {work,...}) n=
    (active owner;W.spend work n;active owner)
  fun begin work rules=
    let val sources=W.original_sources work
        val graph=S.owning_graph sources val root=S.owning_scope sources
        val first=case rules of []=>raise ERR "begin" "empty Source rules"
          | source::_=>C.projected_rule_for work source
        val frame= #frame first
        val scope= #scope (Scope.description_for work frame)
        val _=List.app (fn source=>
          let val d=C.projected_rule_for work source
          in if Portable.pointer_eq (#frame d,frame) then () else
            raise ERR "begin" "Source rules have different actual frames"
          end) rules
        val owner=Owner {marker=ref (),work=work,graph=graph,root=root,
          sources=sources,limits=W.semantic_limits work,rules=rules,
          frame=frame,scope=scope,epoch=Type.type_epoch (),
          symbols=Term.term_epoch (),phase=ref Fresh}
    in active owner;owner end
    handle primary=>(W.close work;raise primary)
  fun add (a:profile) (b:profile):profile=
    {raw= #raw a+ #raw b,inc= #inc a+ #inc b,ann= #ann a+ #ann b}
  fun type_weight owner ty=
    (tick owner 1;
     if Type.is_vartype ty then
       (tick owner (String.size (Type.dest_vartype ty));1:IntInf.int)
     else let val {Thy,Tyop,Args}=Type.dest_thy_type ty
              val _=tick owner (String.size Thy+String.size Tyop)
          in List.foldl (fn (t,n)=>n+type_weight owner t) 1 Args end)
  fun bounded (owner as Owner {limits,...}) value=
    let val cap= #output_limit limits
        val _=case SmtReplayImport.bounded_raw_size cap value of
          SOME n=>tick owner n | NONE=>raise ERR "tree" "raw operand bound"
        val _=case SmtReplayImport.bounded_binder_size cap value of
          SOME n=>tick owner n | NONE=>raise ERR "tree" "binder operand bound"
    in () end
  (* IDs are private lexical occurrences within this WHOLE tree.
     Names/types alone cannot identify shadowed explicit binders. *)
  fun tree owner value=
    let val next=ref 0
        fun find bound variable=case bound of []=>NONE
          | (v,id)::rest=>if call owner
              (fn()=>Term.term_eq v variable) then SOME id
              else find rest variable
        fun walk bound value=
          let val _=tick owner 1
              val ty=call owner (fn()=>Term.type_of value)
              val ann=type_weight owner ty
              val base:profile={raw=1,inc=1,ann=ann}
              val binding=if Term.is_var value then find bound value
                else NONE
              val (shape,p)=if Term.is_comb value then
                  let val (f,x)=call owner (fn()=>Term.dest_comb value)
                      val a=walk bound f val b=walk bound x
                  in (App (a,b),add base
                    (add (#profile (data a)) (#profile (data b)))) end
                else if Term.is_abs value then
                  let val (v,b)=call owner (fn()=>Term.dest_abs value)
                      val id= !next val _=tick owner 1 val _=next:=id+1
                      val bt=call owner (fn()=>Term.type_of v)
                      val ba=type_weight owner bt
                      val binder=Tree {term=v,ty=bt,shape=Atom,
                        profile={raw=1,inc=1,ann=ba},binding=SOME id}
                      val body=walk ((v,id)::bound) b
                  in (Lam (binder,body),add
                    {raw=1,inc=2,ann=ann+ba} (#profile (data body))) end
                else let val _=if Term.is_var value then
                      tick owner (String.size (#1 (Term.dest_var value)))
                    else if Term.is_const value then
                      let val {Thy,Name,...}=Term.dest_thy_const value
                      in tick owner (String.size Thy+String.size Name) end
                    else ()
                  in (Atom,base) end
          in Tree {term=value,ty=ty,shape=shape,profile=p,
            binding=binding} end
    in walk [] value end
  fun binder_id value=case #binding (data value) of SOME id=>id
    | NONE=>raise ERR "binder_id" "missing actual lexical binder identity"
  fun same_type owner a b=
    (ignore (type_weight owner a);ignore (type_weight owner b);
     call owner (fn()=>Type.compare (a,b))=EQUAL)
  fun head owner thy name value=
    Term.is_const (term value) andalso
      let val {Thy,Name,...}=call owner
            (fn()=>Term.dest_thy_const (term value))
      in Thy=thy andalso Name=name end
  fun unary owner thy name value=case #shape (data value) of
      App (f,x)=>if head owner thy name f then SOME x else NONE
    | _=>NONE
  fun binary owner thy name value=case #shape (data value) of
      App (f,y)=>(case #shape (data f) of App (h,x)=>
        if head owner thy name h then SOME (x,y) else NONE | _=>NONE)
    | _=>NONE
  fun equal owner a b=(tick owner 1;
    call owner (fn()=>Term.term_eq a b))
  fun compile (owner as Owner {work,rules,phase,...})=
    protect owner (fn()=>W.with_step work (fn()=>
    let val _=active owner
        val _=if !phase=Fresh then phase:=Compiled else
          raise ERR "compile" "compilation consumed"
        fun routes source whole variables operations value=
          case unary owner "bool" "!" value of SOME predicate=>
            (case #shape (data predicate) of Lam (binder,body)=>
              routes source whole (variables@[binder])
                (operations@[Specialize binder]) body
             | _=>raise ERR "compile" "forall missing actual lambda")
          | NONE=>(case binary owner "bool" "/\\" value of SOME (a,b)=>
              routes source whole variables (operations@[Select true]) a @
              routes source whole variables (operations@[Select false]) b
            | NONE=>(case binary owner "min" "==>" value of SOME (_,b)=>
                routes source whole variables (operations@[Undisch]) b
              | NONE=>let val (kind,l,r)=
                  case binary owner "min" "=" value of
                    SOME (a,b)=>(Equality,a,SOME b)
                  | NONE=>(case unary owner "bool" "~" value of
                      SOME a=>(Negative,a,NONE) | NONE=>(Positive,value,NONE))
                in [Schema {owner=owner,source=source,whole=whole,
                  left=l,right=r,binders=variables,operations=operations,
                  terminal=kind}] end))
        fun compile_one source=
          let val d=C.projected_rule_for work source
              val original=Thm.concl (#theorem d)
              val _=bounded owner original val whole=tree owner original
          in routes source whole [] [] whole end
    in List.concat (List.map compile_one rules) end))
  fun schema_owner (Schema {owner,...})=owner
  fun focus_guard owner caller traversal child target=
    let val Owner {graph,root,scope,...}=owner
        val _=active owner val _=G.validate_scope graph caller
        val _=G.validate_scope graph traversal
        val actual=G.closure_child_node graph caller child
    in if actual=target andalso G.scope_visible graph caller root andalso
        G.scope_visible graph traversal scope andalso
        G.scope_visible graph traversal caller then () else
      raise ERR "focus_guard" "foreign or invisible genuine target" end
  fun target_guard (owner as Owner {work,graph,root,sources,...})
      frame traversal=case frame of NONE=>() | SOME held=>
    let val d=Scope.description_for work held
    in if Portable.pointer_eq (#graph d,graph) andalso #root d=root
        andalso Portable.pointer_eq (#sources d,sources) andalso
        #scope d=traversal then () else
      raise ERR "target_guard" "actual target frame changed" end
  fun prepare_internal (owner as Owner {work,graph,marker,...})
      target_frame
      {schema=schema as Schema {owner=Owner {marker=held,...},
        left,binders,...},caller,traversal,target}=
    protect owner (fn()=>
    (if Portable.pointer_eq (marker,held) then () else
       raise ERR "prepare" "foreign schema";
     W.with_step work (fn()=>
     let val _=target_guard owner target_frame traversal
         val node=G.closure_child_node graph caller target
         val _=focus_guard owner caller traversal target node
         val value=G.representative graph node
         val _=bounded owner value val actual=tree owner value
         val arguments=ref ([]:(int*tree) list)
         fun lookup key pending=case pending of []=>NONE
           | (k,v)::rest=>(tick owner 1;
               if key=k then SOME v else lookup key rest)
         fun captures bound value=
           let fun walk locally_bound current=
                 (tick owner 1;
                  case #shape (data current) of
                    App (a,b)=>walk locally_bound a orelse
                      walk locally_bound b
                  | Lam (v,b)=>walk (binder_id v::locally_bound) b
                  | Atom=>(case #binding (data current) of NONE=>false
                    | SOME id=>not (List.exists (fn n=>n=id) locally_bound)
                        andalso List.exists (fn (_,n)=>n=id) bound))
           in walk [] value end
         fun atom_same bound p a=
           case (#binding (data p),#binding (data a)) of
             (NONE,NONE)=>equal owner (term p) (term a)
           | (SOME id,SOME actual)=>(case lookup id bound of
               SOME mapped=>mapped=actual | NONE=>id=actual)
           | _=>false
         fun same bound p a=
           same_type owner (#ty (data p)) (#ty (data a)) andalso
           (case (#shape (data p),#shape (data a)) of
             (App (f,x),App (g,y))=>same bound f g andalso same bound x y
           | (Lam (v,b),Lam (w,c))=>same
               ((binder_id v,binder_id w)::bound) b c
           | (Atom,Atom)=>atom_same bound p a | _=>false)
         fun flexible_head p=case #shape (data p) of
             App (f,_)=>flexible_head f
           | Atom=>(case #binding (data p) of NONE=>false
               | SOME id=>List.exists (fn b=>binder_id b=id) binders)
           | _=>false
         fun match bound p a=
           (if same_type owner (#ty (data p)) (#ty (data a)) then ()
              else raise Mismatch;
            case #binding (data p) of SOME id=>
              (case lookup id bound of SOME local_id=>
                 (case #binding (data a) of SOME actual=>
                    if actual=local_id then () else raise Mismatch
                  | NONE=>raise Mismatch)
               | NONE=>if List.exists (fn b=>binder_id b=id) binders then
                   (if captures bound a then raise HigherOrder else ();
                    case lookup id (!arguments) of NONE=>
                      arguments:=(id,a):: !arguments
                    | SOME previous=>if same [] previous a then ()
                      else raise Mismatch)
                 else if atom_same bound p a then () else raise Mismatch)
            | NONE=>case (#shape (data p),#shape (data a)) of
                (App (f,x),App (g,y))=>(match bound f g;match bound x y)
              | (Lam (v,b),Lam (w,c))=>match
                  ((binder_id v,binder_id w)::bound) b c
              | (Atom,Atom)=>if atom_same bound p a then ()
                  else raise Mismatch
              | _=>if flexible_head p then raise HigherOrder
                  else raise Mismatch)
         val result=((match [] left actual;
           Matched (Match {schema=schema,caller=caller,traversal=traversal,
             child=target,target=node,actual=actual,
             arguments=List.rev (!arguments),used=ref false,
             target_frame=target_frame}))
           handle Mismatch=>NoMatch | HigherOrder=>NeedsHigherOrder)
         val _=focus_guard owner caller traversal target node
     in result end)))
  fun prepare owner request=prepare_internal owner NONE request
  fun prepare_scoped (owner as Owner {work,marker,...})
      {schema=schema as Schema {owner=Owner {marker=held,...},...},
       caller,frame,target}=
    protect owner (fn()=>
      (if Portable.pointer_eq (marker,held) then () else
         raise ERR "prepare_scoped" "foreign schema";
       let val d=Scope.description_for work frame
       in prepare_internal owner (SOME frame)
         {schema=schema,caller=caller,traversal= #scope d,target=target} end))
  fun validate_match work (Match {schema,caller,traversal,child,
                                   target,target_frame,...})=
    let val owner=schema_owner schema val _=expected work owner
        val _=target_guard owner target_frame traversal
    in focus_guard owner caller traversal child target end
  fun instantiate (value as Match {schema=Schema {owner=owner as Owner
      {work,limits,...},source,whole,operations,terminal,left,...},
      arguments,used,actual,...}) {check_type}=
    protect owner (fn()=>W.with_step work (fn()=>
    let val _=active owner
        val _=if !used then raise ERR "instantiate" "instance consumed"
          else ()
        val _=validate_match work value val _=used:=true
        (* Each prospective conclusion/Hyp is an exact typed constructor
           inventory. Source Gamma stays retained unchanged: no INST_TYPE,
           INST, GEN_ALL or raw Source-Hyp traversal is performed. *)
        datatype type_recipe=Captured of Type.hol_type
          | Function of type_recipe*type_recipe
        type inventory=profile*type_recipe list
        fun snapshot ty=
          Captured ty :: (if Type.is_vartype ty then [] else
            List.concat (List.map snapshot (#Args (Type.dest_thy_type ty))))
        fun lookup key pending=case pending of []=>NONE
          | (k,v)::rest=>(tick owner 1;
              if key=k then SOME v else lookup key rest)
        fun inventory substitutions current:inventory=
          case (case #binding (data current) of NONE=>NONE
              | SOME id=>lookup id substitutions) of SOME replacement=>
              inventory [] replacement
          | NONE=>let val d=data current val ty= #ty d
                  val ann=type_weight owner ty val types=snapshot ty
              in case #shape d of Atom=>({raw=1,inc=1,ann=ann},types)
               | App (a,b)=>
                   let val (pa,ta)=inventory substitutions a
                       val (pb,tb)=inventory substitutions b
                   in (add {raw=1,inc=1,ann=ann} (add pa pb),
                     types @ ta @ tb) end
               | Lam (v,b)=>
                   let val vt= #ty (data v)
                       val (pb,tb)=inventory (List.filter
                         (fn (key,_)=>key<>binder_id v)
                         substitutions) b
                   in (add {raw=1,inc=2,
                       ann=ann+type_weight owner vt} pb,
                     types @ snapshot vt @ tb) end end
        val bool=Captured Type.bool
        val arrow=Function (bool,bool)
        val binary_type=Function (bool,arrow)
        val header=[binary_type,bool,arrow,bool,bool,arrow,bool,bool,bool]
        fun combined (pa,ta) (pb,tb):inventory=
          (add {raw=3,inc=3,ann=9} (add pa pb),header @ ta @ tb)
        val truth:inventory=({raw=1,inc=1,ann=1},[bool])
        fun negative (p,types):inventory=
          (add {raw=2,inc=2,ann=4} p,[bool,arrow,bool,bool] @ types)
        val quota=IntInf.fromInt (W.work_limit work)
        val cap=IntInf.fromInt (#output_limit limits)
        val quote=ref (0:IntInf.int)
        val policy_types=ref ([]:type_recipe list)
        fun record hypotheses (p,types):inventory=
          let val actual=List.foldl (fn ((h,_),sum)=>add h sum) p hypotheses
              val hyp_types=List.concat (List.map #2 hypotheses)
              val _=if #raw p<=cap andalso #inc p<=cap then () else
                raise ERR "instantiate" "prospective result bound"
              val _=quote:= !quote+ #raw actual+ #inc actual+ #ann actual
              val _=policy_types:=types @ hyp_types @ !policy_types
              val _=if !quote<=quota then () else
                raise ERR "instantiate" "prospective type/proof Work"
          in (p,types) end
        fun play [] current substitutions conditions=
              (current,substitutions,conditions)
          | play (opn::rest) current substitutions conditions=
            (tick owner 1;case opn of Specialize binder=>
              let val predicate=case unary owner "bool" "!" current of
                    SOME p=>p | NONE=>raise ERR "instantiate" "forall route"
                  val body=case #shape (data predicate) of Lam (_,b)=>b
                    | _=>raise ERR "instantiate" "forall lambda"
                  val argument=case lookup (binder_id binder) arguments of
                    SOME a=>a | NONE=>binder
                  val next=(binder_id binder,argument)::substitutions
                  val _=record [] (inventory [] argument)
                  val _=record conditions (inventory next body)
              in play rest body next conditions end
            | Select choose_left=>
              let val (a,b)=case binary owner "bool" "/\\" current of
                    SOME p=>p | NONE=>raise ERR "instantiate" "conj route"
                  val body=if choose_left then a else b
                  val _=record conditions (inventory substitutions body)
              in play rest body substitutions conditions end
            | Undisch=>
              let val (a,b)=case binary owner "min" "==>" current of
                    SOME p=>p | NONE=>raise ERR "instantiate" "imp route"
                  val h=inventory substitutions a
                  val _=record [h] h
                  val _=record (h::conditions) (inventory substitutions b)
              in play rest b substitutions (h::conditions) end)
        val _=record [] (inventory [] whole)
        val (last,substitutions,conditions)=play operations whole [] []
        val operand=inventory substitutions left
        val final=case terminal of Equality=>inventory substitutions last
          | Positive=>
              let val result=combined operand truth
                  val _=record [] (combined result operand)
              in result end
          | Negative=>
              let val result=combined operand truth
                  val _=record [] (combined (negative operand) result)
              in result end
        val _=record conditions final
        fun discharge [] current=current
          | discharge (h::rest) current=
              discharge rest (record rest (combined h current))
        val (final,_)=discharge conditions final
        val _=if #raw final<=IntInf.fromInt (#template_limit limits)
            andalso #inc final<=IntInf.fromInt (#template_limit limits)
          then () else raise ERR "instantiate" "conditional template bound"
        val _=record [] (inventory [] actual)
        (* Original Work covers every repeated future annotation before
           any Type constructor, supplied policy or proof effect. *)
        val _=W.spend work (IntInf.toInt (!quote))
        fun guard operation=(validate_match work value;
          let val result=operation () in validate_match work value;result end)
        fun materialize (Captured ty)=guard (fn()=>ty)
          | materialize (Function (a,b))=
              let val left=materialize a val right=materialize b
              in guard (fn()=>Type.mk_thy_type
                {Thy="min",Tyop="fun",Args=[left,right]}) end
        val checked=List.map materialize (!policy_types)
        val _=List.app (fn ty=>guard (fn()=>check_type ty)) checked
        val original= #theorem (C.projected_rule_for work source)
        val hyp=Thm.hyp original
        fun execute [] theorem assumptions=(theorem,assumptions)
          | execute (opn::rest) theorem assumptions=
            (case opn of Specialize binder=>
              let val argument=case lookup (binder_id binder) arguments of
                    SOME a=>term a | NONE=>term binder
              in execute rest (guard (fn()=>Thm.SPEC argument theorem))
                assumptions end
            | Select choose_left=>execute rest
                (guard (fn()=>if choose_left then Thm.CONJUNCT1 theorem
                  else Thm.CONJUNCT2 theorem)) assumptions
            | Undisch=>let val condition=guard (fn()=>
                  #1 (boolSyntax.dest_imp (Thm.concl theorem)))
                  val proof=guard (fn()=>Thm.ASSUME condition)
                  val next=guard (fn()=>Thm.MP theorem proof)
              in execute rest next (condition::assumptions) end)
        val (body,conditions)=execute operations original []
        val body=case terminal of Equality=>body
          | Positive=>guard (fn()=>Drule.EQT_INTRO body)
          | Negative=>guard (fn()=>Drule.EQF_INTRO body)
        val theorem=List.foldl (fn (c,t)=>guard (fn()=>Thm.DISCH c t))
          body conditions
        val _=if ListPair.allEq Portable.pointer_eq (hyp,Thm.hyp theorem)
          then () else raise ERR "instantiate" "actual Source Hyp changed"
        fun consequent t=if boolSyntax.is_imp_only t then
            consequent (#2 (boolSyntax.dest_imp t)) else t
        val lhs=guard (fn()=>boolSyntax.lhs (consequent (Thm.concl theorem)))
        val _=if guard (fn()=>Term.aconv lhs (term actual)) then () else
          raise ERR "instantiate" "actual proved operand changed"
        (* EQT/EQF use the fixed EQ_CLAUSES theory dependency. Preserve
           its actual tag; do not clear it or admit another oracle/axiom. *)
        val expected_tag=case terminal of Equality=>Thm.tag original
          | _=>Tag.merge (Thm.tag original) (Thm.tag boolTheory.EQ_CLAUSES)
        val actual_tag=Thm.tag theorem
        val (oracles,_)=Tag.dest_tag actual_tag
        val (expected_oracles,_)=Tag.dest_tag expected_tag
        val _=if List.all (fn name=>name="DISK_THM") oracles andalso
            oracles=expected_oracles andalso
            null (Tag.axioms_of actual_tag) andalso
            null (Tag.axioms_of expected_tag) then () else
          raise ERR "instantiate" "unexpected proof oracle or axiom"
    in Instance {matched=value,theorem=theorem,
      conditions=List.rev conditions} end))
  fun instance_for work (Instance {matched=value as Match
      {schema=Schema {source,terminal,...},target,caller,traversal,
       target_frame,...},
       theorem,conditions})=
    (validate_match work value;
     let val d=C.projected_rule_for work source
     in {source=source,frame= #frame d,theorem=theorem,conditions=conditions,
       target=target,caller=caller,traversal=traversal,
       target_frame=target_frame,terminal=terminal} end)
  fun pattern_for work (Schema {owner,source,left,right,terminal,...})=
    (expected work owner;ignore (C.projected_rule_for work source);
     {left=term left,right=Option.map term right,terminal=terminal})
  fun prepare_source_recipe
      (value as Match {schema=Schema {owner=owner as Owner
        {work,graph,...},source,operations,terminal,...},
        caller,child,arguments,used,target_frame,...}) {check_type} =
    protect owner (fn()=>
    let
      val _=active owner
      val _=if !used then raise ERR "prepare_source_recipe"
        "instance consumed" else ()
      val _=validate_match work value
      val frame=case target_frame of SOME held=>held | NONE=>
        raise ERR "prepare_source_recipe" "actual target frame required"
      val source_data=C.projected_rule_for work source
      (* Capture authentic immediate child paths, including real body
         backing, in a callback-free SAME Work action. Matching is only
         against bounded argument trees already admitted by this Match.
         This search creates neither a term, graph node nor proof. *)
      val paths=W.with_step work (fn()=>
        let
          val seen=ref (Redblackset.empty Int.compare)
          val paths=ref ([]:(Term.term*G.closure_child) list)
          fun walk current=
            let val _=tick owner 1
                val node=G.closure_child_node graph caller current
                val id=G.node_id node
            in if Redblackset.member(!seen,id) then () else
              (seen:=Redblackset.add(!seen,id);
               paths:=(G.representative graph node,current):: !paths;
               case G.view graph node of G.Application _=>
                 let val (left,right)=
                   G.closure_application_children graph caller current
                 in walk left;walk right end
               | G.AdmittedBinder _=>walk(G.binder_closure_body graph caller
                   (G.closure_child_binder graph caller current))
               | _=>()) end
          val _=walk child val _=validate_match work value
        in !paths end)
      fun argument binder=
        case List.find (fn (id,_)=>
          (tick owner 1;id=binder_id binder)) arguments of
          NONE=>raise ERR "prepare_source_recipe"
            "missing binder needs complete context freshening"
        | SOME (_,actual)=>
            (case List.find (fn (held,_)=>
                (tick owner 1;Term.aconv held (term actual)))
                paths of SOME (_,path)=>path | NONE=>
              raise ERR "prepare_source_recipe"
                "matched argument has no authentic target child path")
      val steps=W.with_step work (fn()=>
        let fun choose binder=
              (tick owner 1;argument binder)
        in List.map (fn Specialize binder=>
            SmtReplayProof.SourceSpec(choose binder)
          | Select left=>SmtReplayProof.SourceConjunct left
          | Undisch=>SmtReplayProof.SourceCondition) operations end)
      val terminal=case terminal of Equality=>SmtReplayProof.SourceEquality
        | Positive=>SmtReplayProof.SourceTruth
        | Negative=>SmtReplayProof.SourceFalse
      (* P owns the complete local constructor/INST/realization forecast
         and actual policy fences. This call is outside the search action. *)
      val plan=SmtReplayProof.prepare_source_rule work
        {source= #proof source_data,frame=frame,caller=caller,steps=steps,
         terminal=terminal,check_type=check_type}
      val _=validate_match work value
      val _=used:=true
    in plan end)

end
