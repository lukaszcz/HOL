(* Only compact constructor equations are inspected here. Source Gamma
   remains an ordered graph portfolio, including duplicate occurrences. *)
structure SmtLib_OwnedNamedContextSeeds :> SmtLib_OwnedNamedContextSeeds =
struct
  structure G=SmtReplayGraph
  structure S=SmtReplaySource
  structure W=SmtReplayInvocationWork
  structure P=SmtReplayProof
  structure Q=SmtLib_OwnedStrippedNaturalQuery
  structure Scope=SmtReplayOwnedScopeReceipt
  val _=SmtReplayProof.prepare_needed_sources_with_work
  val _=SmtLib_OwnedStrippedNaturalQuery.freeze_for
  val ERR=Feedback.mk_HOL_ERR "SmtLib_OwnedNamedContextSeeds"
  datatype phase=Fresh | Prepared | Live | Closed | Retired
  datatype receiver=Original | Stripped of Q.query
    | RuleOriginal | RuleStripped of Q.query
  datatype owner=Owner of
    {marker:unit ref,work:W.portfolio,graph:G.graph,root:G.scope,
     sources:S.sources,limits:W.limits,frame:Scope.receipt,scope:G.scope,
     receiver:receiver,assumptions:G.node list,goal:G.node,denied:G.node,
     epoch:int,symbols:int,phase:phase ref,check_type:Type.hol_type -> unit}
  type row={slot:int,occurrence:int,node:G.node,path:bool list,
    rigid:G.node list option}
  datatype plan=Plan of
    {owner:owner,rows:row list,paths:G.node list,used:bool ref}
  datatype shared_prefix=SharedPrefix of
    {occurrence:int,node:G.node,path:bool list,
     receipt:P.source_realization option ref}
  datatype catalogue=Catalogue of
    {owner:owner,block:P.block,seeds:seed list,prefixes:shared_prefix list}
  and seed=Seed of {owner:owner,block:P.block,row:row,edge:P.edge}
  datatype projected_rule=ProjectedRule of
    {owner:owner,row:row,proof:P.source_realization,
     fixed:Term.term list,rigid_types:Type.hol_type list}
  fun close (Owner {work,phase,...})=(phase:=Retired;W.close work)
  fun protect owner action=action () handle primary=>
    (close owner;raise primary)
  fun active (Owner {work,graph,root,sources,limits,frame,scope,receiver,
                    assumptions,goal,denied,epoch,symbols,phase,...})=
    (if !phase=Retired orelse !phase=Closed then
       raise ERR "active" "context retired" else ();
     W.validate work graph root sources limits;
     Scope.validate_lifetime_for work frame;
     if Type.type_epoch ()=epoch andalso Term.term_epoch ()=symbols then ()
       else raise ERR "active" "declaration retirement changed";
     G.validate_scope graph scope;
     let fun query_guard query=let val d=Q.description_for work query
         in if Portable.pointer_eq (#frame d,frame) andalso
             #assumptions d=assumptions andalso #goal d=goal andalso
             #denied d=denied then () else
           raise ERR "active" "registered context changed" end
     in case receiver of Original=>() | RuleOriginal=>()
       | Stripped query=>query_guard query
       | RuleStripped query=>query_guard query end)
  fun expected work owner=case owner of Owner {work=held,...}=>
    ((if Portable.pointer_eq (work,held) then active owner else
       raise ERR "expected" "foreign expected Work")
     handle primary=>(W.close work;raise primary))
  fun call owner action=
    (active owner;let val value=action () in active owner;value end)
  fun make work receiver frame assumptions goal denied check_type=
    let val sources=W.original_sources work val graph=S.owning_graph sources
        val root=S.owning_scope sources
        val d=Scope.description_for work frame
        val owner=Owner {marker=ref (),work=work,graph=graph,root=root,
          sources=sources,limits=W.semantic_limits work,frame=frame,
          scope= #scope d,receiver=receiver,assumptions=assumptions,
          goal=goal,denied=denied,epoch=Type.type_epoch (),
          symbols=Term.term_epoch (),phase=ref Fresh,check_type=check_type}
    in active owner;owner end
  fun begin_original_nonnum work {check_type}=
    let val sources=W.original_sources work
    in make work Original (Scope.root work) (S.assumption_nodes sources)
      (#node (S.goal_source sources)) (S.denied_goal_node sources) check_type
    end handle primary=>(W.close work;raise primary)
  fun begin_query work {query,check_type}=
    let val d=Q.description_for work query
    in make work (Stripped query) (#frame d) (#assumptions d)
      (#goal d) (#denied d) check_type end
    handle primary=>(W.close work;raise primary)
  (* Projection provenance only; never a no-NUM absence certificate. *)
  fun begin_rules_original work {check_type}=
    let val sources=W.original_sources work
    in make work RuleOriginal (Scope.root work) (S.assumption_nodes sources)
      (#node (S.goal_source sources)) (S.denied_goal_node sources) check_type
    end handle primary=>(W.close work;raise primary)
  fun begin_rules_query work {query,check_type}=
    let val d=Q.description_for work query
    in make work (RuleStripped query) (#frame d) (#assumptions d)
      (#goal d) (#denied d) check_type end
    handle primary=>(W.close work;raise primary)
  (* A tick is callback-free bookkeeping inside an entry/exit checked
     span. W.spend still debits the SAME live original Work. In particular
     call/effect retain BOTH guards around every public callback. *)
  fun tick (Owner {work,...}) n=W.spend work n
  fun diagnostic (Owner {work,...}) label describe=
    if not ((OS.Process.getEnv "HOL4_HOLSMT_REPLAY_DIAGNOSTICS"=SOME "1")
        handle _=>false) then () else
      ((let val audit=W.audit work
        in TextIO.output (TextIO.stdErr,
          "TABLES_WORK phase=catalogue." ^ label ^ " charged=" ^
          Int.toString (#charged audit) ^ " retired=" ^
          Bool.toString (#retired audit) ^ describe () ^ "\n");
          TextIO.flushOut TextIO.stdErr end) handle _=>())
  fun rigid owner node=case owner of Owner {graph,...}=>
    (tick owner 1;call owner (fn()=>G.free_variable_nodes graph node))
  fun binary (owner as Owner {graph,...}) node=
    (tick owner 1;case G.view graph node of G.Application (a,b)=>
      (case G.view graph a of G.Application (opnode,x)=>
         (case G.view graph opnode of G.Constant _=>
            if Term.same_const (G.representative graph opnode)
                boolSyntax.conjunction then SOME (x,b) else NONE
          | _=>NONE)
       | _=>NONE)
     | _=>NONE)
  fun prepare (owner as Owner {work,graph,sources,receiver,assumptions,
                              goal,phase,...})=
    protect owner (fn()=>W.with_step work (fn()=>call owner (fn()=>
    let val _=diagnostic owner "prepare.before" (fn()=>"")
        val _=if !phase=Fresh then phase:=Prepared else
          raise ERR "prepare" "context plan consumed"
        fun nonnum node=case rigid owner node of NONE=>
              raise ERR "prepare" "unknown original free-variable summary"
          | SOME variables=>List.app (fn variable=>
              let val _=tick owner 1
                  val ty=G.type_of graph variable
                  val numeric=Type.compare (ty,numSyntax.num)=EQUAL
                  val bag=case Lib.total Type.dom_rng ty of SOME (_,r)=>
                        Type.compare (r,numSyntax.num)=EQUAL | NONE=>false
              in if numeric orelse bag then
                raise ERR "prepare" "natural/BAG free-variable prefix required"
              else () end) variables
        val _=case receiver of Original=>List.app nonnum (goal::assumptions)
          | _=>()
        (* Every projected conjunction and its constructor rator spine
           is an actual immutable node discovered from Source incidence.
           Reserve all of them before freeze, never fabricate a name. *)
        val paths=ref (Redblackmap.mkDict Int.compare)
        fun require node=
          let val _=tick owner 1 val id=G.node_id node
          in case Redblackmap.peek (!paths,id) of SOME _=>()
           | NONE=>(paths:=Redblackmap.insert (!paths,id,node);
             case G.view graph node of G.Application (head,_)=>require head
              | _=>()) end
        val base=case receiver of Original=>0 | RuleOriginal=>0
          | _=>length (S.assumption_nodes sources)+1
        fun slot (index,assumption)=
          let val fixed=rigid owner assumption
              val seen=ref (Redblackset.empty Int.compare)
              fun walk node path=
                let val _=tick owner 1 val id=G.node_id node
                in if Redblackset.member (!seen,id) then [] else
                  (seen:=Redblackset.add (!seen,id);require node;
                   case binary owner node of SOME (a,b)=>
                     walk a (true::path) @ walk b (false::path)
                   | NONE=>[{slot=index,occurrence=base+index,node=node,
                     path=List.rev path,rigid=fixed}]) end
          in walk assumption [] end
        val rows=List.concat (Portable.mapi (fn index=>fn assumption=>
          slot (index,assumption)) assumptions)
        val _=diagnostic owner "prepare.after"
          (fn()=>" rows=" ^ Int.toString (length rows))
    in Plan {owner=owner,rows=rows,
      paths=List.map #2 (Redblackmap.listItems (!paths)),used=ref false}
    end)))
  (* Actual compact theorem grammar only, including every Hyp/name/type
     occurrence. No expanded Source Gamma is passed to this preflight. *)
  fun quote (owner as Owner {limits,...}) terms=
    let val types=ref ([]:Type.hol_type list)
        fun ty t=(tick owner 1;types:=t:: !types;
          if Type.is_vartype t then tick owner
            (String.size (Type.dest_vartype t)) else
          let val {Thy,Tyop,Args}=Type.dest_thy_type t
          in tick owner (String.size Thy+String.size Tyop);
             List.app ty Args end)
        fun walk [] raw inc=()
          | walk (t::rest) raw inc=
            let val _=tick owner 1 val raw=raw+1 val inc=inc+1
                val _=if raw<= #template_limit limits andalso
                    inc<= #template_limit limits then () else
                  raise ERR "quote" "compact context operation bound"
                val _=ty (Term.type_of t)
            in if Term.is_comb t then let val (a,b)=Term.dest_comb t
                 in walk (a::b::rest) raw inc end
               else if Term.is_abs t then
                 raise ERR "quote" "unexpected binder in named projection"
               else walk rest raw inc end
    in List.app (fn t=>walk [t] 0 0) terms;List.rev (!types) end
  fun effect (owner as Owner {work,check_type,...}) terms operation=
    let val types=W.with_step work (fn()=>call owner
          (fn()=>quote owner terms))
    in W.with_step work (fn()=>
      (List.app (fn ty=>call owner (fn()=>check_type ty)) types;
       call owner operation)) end
  (* One callback-free billed inspection. Do not wrap effect or any
     public producer which already owns an action in this span. *)
  fun metadata (owner as Owner {work,...}) operation=
    W.with_step work (fn()=>call owner operation)
  fun named owner block node=metadata owner (fn()=>P.name block node)
  fun constructor owner block node=case owner of Owner {graph,...}=>
    let fun spine n=case G.view graph n of G.Application (a,b)=>
              Term.mk_comb (spine a,P.name block b)
          | G.Constant _=>G.representative graph n | _=>P.name block n
        fun terms n=case G.view graph n of G.Application (a,b)=>
              boolSyntax.mk_eq (P.name block n,spine n)::
              boolSyntax.mk_eq (P.name block n,
                Term.mk_comb (P.name block a,P.name block b))::terms a
          | G.Constant _=>[boolSyntax.mk_eq
              (P.name block n,G.representative graph n)]
          | _=>[boolSyntax.mk_eq (P.name block n,P.name block n)]
        val prospective=metadata owner (fn()=>terms node)
    in effect owner prospective (fn()=>P.constructor block node) end
  fun compose owner block result premises operation=
    let val actual=metadata owner
          (fn()=>List.map (P.theorem block) premises)
        val terms=result::List.concat
          (List.map (fn th=>Thm.concl th::Thm.hyp th) actual)
    in effect owner terms (fn()=>P.compose block operation premises) end
  fun execute (Plan {owner=owner as Owner {work,frame,receiver,assumptions,
                       goal,denied,graph,scope,phase,...},rows,paths,used})=
    protect owner (fn()=>call owner (fn()=>
    let val _=diagnostic owner "execute.before"
          (fn()=>" rows=" ^ Int.toString (length rows))
        val _=if !used then raise ERR "execute" "plan consumed" else used:=true
        val bottom=W.with_step work (fn()=>
          (tick owner 1;call owner (fn()=>
            G.constant graph scope boolSyntax.F)))
        val roots=bottom::goal::denied::paths
        fun sparse extras=P.prepare_needed_sources_with_work work
          {frame=frame,roots=roots,additional_sources=extras,
           closed_facts=[],conversions=[]}
        val _=diagnostic owner "freeze.before" (fn()=>"")
        val block=case receiver of Original=>sparse []
          | RuleOriginal=>sparse []
          | RuleStripped _=>sparse (assumptions @ [denied])
          | Stripped query=>Q.freeze_for work query
              {roots=roots,closed_facts=[],conversions=[]}
        val _=diagnostic owner "freeze.after" (fn()=>"")
        val _=phase:=Live
        (* This trie holds genuine edges in the SAME unconsumed block.
           Roots are actual occurrences, never graph-node identities. *)
        datatype branch=Branch of
          {node:G.node,edge:P.edge,left:branch option ref,
           right:branch option ref}
        (* Local metadata ledger, on the SAME Work: setup24 pays the
           map/ref/closure fields; edge20 pays branch/path dispatch;
           cache16 pays option/ref reads, stores and branch allocation.
           List-cell16 pays lookupNode's case/fields/index/tail call and
           common's two cell views/comparison/cons; its terminal fee is8.
           Neither setup nor a cache fee buys a tree search: EACH actual
           balanced-map comparison below has its own debit, before compare.
           All uses of these helpers are inside metadata's Busy span. *)
        fun compareOccurrence keys=(tick owner 1;Int.compare keys)
        fun branch node edge=(tick owner 16;Branch
          {node=node,edge=edge,left=ref NONE,right=ref NONE})
        fun lookupNode slot=
          let fun nth nodes index=(tick owner 16;case nodes of
                  []=>raise Subscript
                | node::rest=>if index=0 then node else nth rest (index-1))
          in nth assumptions slot end
        val branches=metadata owner (fn()=>(tick owner 24;
          ref (Redblackmap.mkDict compareOccurrence)))
        fun project saved path=
          let val Branch {node,edge,left,right}=metadata owner (fn()=>
                (tick owner 20;saved))
          in case path of
            []=>edge
          | direction::rest=>
            let val port=if direction then left else right
                val held=metadata owner (fn()=>(tick owner 16;!port))
                val next=case held of SOME saved=>saved
                  | NONE=>
                    (case metadata owner (fn()=>binary owner node) of NONE=>
                       raise ERR "execute" "genuine conjunction path changed"
                     | SOME (a,b)=>
                       let val law=constructor owner block node
                           val conjunction=metadata owner (fn()=>
                             boolSyntax.mk_conj
                               (P.name block a,P.name block b))
                           val both=compose owner block conjunction [law,edge]
                             (fn [eq,p]=>Thm.EQ_MP eq p
                               | _=>raise ERR "execute" "projection premises")
                           val child=if direction then a else b
                           val proof=compose owner block
                             (named owner block child) [both]
                             (fn [p]=>if direction then Thm.CONJUNCT1 p
                               else Thm.CONJUNCT2 p
                               | _=>raise ERR "execute" "conjunct premise")
                           val saved=metadata owner (fn()=>
                             let val _=tick owner 16
                                 val saved=branch child proof
                             in port:=SOME saved;saved end)
                       in saved end)
            in project next rest end end
        fun seed (row:row)=
          let val held=metadata owner (fn()=>(tick owner 20;
                Redblackmap.peek (!branches,#occurrence row)))
              val root=case held of SOME saved=>saved | NONE=>
                let val edge=W.with_step work (fn()=>call owner
                      (fn()=>P.source block (#occurrence row)))
                    val saved=metadata owner (fn()=>
                      let val _=tick owner 16
                          val saved=branch (lookupNode (#slot row)) edge
                      in branches:=Redblackmap.insert
                        (!branches,#occurrence row,saved);saved end)
                in saved end
              val proof=project root (#path row)
          in Seed {owner=owner,block=block,row=row,edge=proof} end
        val _=diagnostic owner "seeds.before" (fn()=>"")
        val seeds=List.map seed rows
        val _=diagnostic owner "seeds.after" (fn()=>"")
        val prefixes=metadata owner (fn()=>
          let
            val _=tick owner 24
            fun common (a::xs) (b::ys)=
                  (tick owner 16;if a=b then a::common xs ys else [])
              | common _ _=(tick owner 8;[])
            fun insert (row:row,table)=
              let val _=tick owner 20 val key= #occurrence row
                  val value=case Redblackmap.peek (table,key) of
                      NONE=>(row,#path row,false)
                    | SOME (first,path,_)=>
                        (first,common path (#path row),true)
              in tick owner 16;Redblackmap.insert (table,key,value) end
            fun endpoint node path=(tick owner 20;case path of []=>node
              | left::rest=>case binary owner node of
                  SOME (a,b)=>endpoint (if left then a else b) rest
                | NONE=>raise ERR "execute" "common Source path changed")
            val Owner {limits,...}=owner
            (* unfolded_nodes reserves its maximum as a saturation value.
               This is only a sharing forecast, not a changed Source cap. *)
            val maximum=case Int.maxInt of SOME n=>n | NONE=>1073741823
            val cap=Int.min (maximum-1,
              Int.min (#output_limit limits,#template_limit limits))
            fun compact node metric=case G.unfolded_nodes_observed
                (fn()=>tick owner 1) graph metric cap node of
                  SOME n=>n<=cap | NONE=>false
            fun retain (_,((row:row),path,multiple))=
              (tick owner 20;
              if not multiple orelse null path then NONE else
              let val node=endpoint (lookupNode (#slot row)) path
              (* Optional planning only. Unknown/large common clauses keep
                 the old independent producer; no new admission/refusal.
                 A cut target aliasing an ordinary Source slot would add
                 that slot to sparse incidence. Leave it ordinary. *)
              in if not (List.exists (fn original=>(tick owner 16;
                    original=node)) (denied::assumptions)) andalso
                  compact node G.RawNodes andalso
                  compact node G.BinderInclusiveNodes then
                (tick owner 16;
                 SOME (SharedPrefix {occurrence= #occurrence row,
                   node=node,path=path,receipt=ref NONE})) else NONE end)
          in case receiver of RuleOriginal=>
              let val table=List.foldl insert
                    (Redblackmap.mkDict compareOccurrence) rows
                  (* Exact entry count, not a root-call or logarithmic
                     guess. Per entry24 covers the tree view/fields,
                     recursive control/empty leaves, pair/list words and
                     mapPartial's input/output cells; setup/last leaf8.
                     Pay BEFORE listItems traverses/allocates anything. *)
                  val _=tick owner (8+24*Redblackmap.numItems table)
              in List.mapPartial retain (Redblackmap.listItems table) end
            | _=>[] end)
    in Catalogue {owner=owner,block=block,seeds=seeds,
      prefixes=prefixes} end))
  fun seeds_for work (Catalogue {owner,seeds,...})=
    (expected work owner;seeds)
  fun description_for work (Seed {owner,row,...})=
    (expected work owner;{node= #node row,assumption_slot= #slot row,
      source_occurrence= #occurrence row,rigid_variables= #rigid row})
  fun named_theorem_for work (Seed {owner,block,edge,...})=
    (expected work owner;P.validate_block_for work block;P.theorem block edge)
  fun finish_goal work (owner as Owner
      {receiver,sources,graph,goal,denied,assumptions,phase,...}) block edge=
    ((expected work owner;
      protect owner (fn()=>
      let val result=case receiver of Original=>
            let val proved=W.with_step work (fn()=>call owner
                  (fn()=>P.realize block goal edge))
                val bridge=S.goal_bridge sources
            in effect owner [Thm.concl bridge,
                boolSyntax.mk_eq (S.canonical_goal sources,
                  #2 (S.original_goal sources))]
                (fn()=>Thm.EQ_MP (Thm.SYM bridge) proved) end
          | Stripped query=>
            let val index=length (S.assumption_nodes sources)+1+
                  length assumptions
                val denial=W.with_step work (fn()=>call owner
                  (fn()=>P.source block index))
                val law=constructor owner block denied
                val negation=boolSyntax.mk_neg (named owner block goal)
                val negated=compose owner block negation [law,denial]
                  (fn [eq,p]=>Thm.EQ_MP eq p
                    | _=>raise ERR "close_goal" "denial premises")
                val bottom=W.with_step work (fn()=>
                  (tick owner 1;call owner (fn()=>
                    G.constant graph (P.scope block) boolSyntax.F)))
                val contradiction=compose owner block boolSyntax.F
                  [negated,edge] (fn [n,p]=>Thm.MP (Thm.NOT_ELIM n) p
                    | _=>raise ERR "close_goal" "contradiction premises")
                val definition=constructor owner block bottom
                val named=compose owner block (named owner block bottom)
                  [definition,contradiction]
                  (fn [eq,p]=>Thm.EQ_MP (Thm.SYM eq) p
                    | _=>raise ERR "close_goal" "false definition")
            in Q.close_for work query block named end
          | _=>raise ERR "finish_goal"
              "projection-only context does not own final Goal closure"
          val _=S.check_goal sources result
          val _=phase:=Closed
      in result end)) handle primary=>(W.close work;raise primary))
  fun close_goal work (Catalogue {owner=owner as Owner
      {marker,goal,...},block,...})
      (Seed {owner=Owner {marker=other,...},block=otherblock,row,edge})=
    ((expected work owner;
      if Portable.pointer_eq (marker,other) andalso
          Portable.pointer_eq (block,otherblock) andalso #node row=goal then ()
      else raise ERR "close_goal" "foreign seed or different exact Goal";
      finish_goal work owner block edge)
     handle primary=>(W.close work;raise primary))
  datatype derivation=Given of seed
    | Forward of seed * derivation | Backward of seed * derivation
  (* Exact typed graph IDs are ground matching keys, not semantic equations.
     No INST/INST_TYPE or schematic generalization is performed. *)
  fun close_ground_goal work (Catalogue
      {owner=owner as Owner {graph,goal,...},block,seeds,...})=
    ((expected work owner;protect owner (fn()=>
    let
      fun boolean node=Type.compare (G.type_of graph node,Type.bool)=EQUAL
      fun equation (seed as Seed {row,...})=
        let val node= #node row
        in case G.view graph node of G.Application (a,y)=>
          (case G.view graph a of G.Application (head,x)=>
            (case G.view graph head of G.Constant _=>
               if Term.same_const (G.representative graph head)
                   boolSyntax.equality andalso boolean x andalso boolean y
               then SOME (x,y,seed) else NONE
             | _=>NONE)
           | _=>NONE)
         | _=>NONE end
      val equations=W.with_step work (fn()=>call owner (fn()=>
        List.mapPartial (fn seed=>(tick owner 1;equation seed)) seeds))
      val program=W.with_step work (fn()=>call owner (fn()=>
        let val known=ref (Redblackmap.mkDict Int.compare)
            fun lookup node=(tick owner 1;
              Redblackmap.peek (!known,G.node_id node))
            fun add node proof=(tick owner 1;
              known:=Redblackmap.insert (!known,G.node_id node,proof))
            val _=List.app (fn seed as Seed {row,...}=>
              add (#node row) (Given seed)) seeds
            fun pass [] changed=changed
              | pass ((left,right,seed)::rest) changed=
                  let val l=lookup left val r=lookup right
                  in case (l,r) of
                    (SOME proof,NONE)=>(add right (Forward (seed,proof));
                      pass rest true)
                  | (NONE,SOME proof)=>(add left (Backward (seed,proof));
                      pass rest true)
                  | _=>pass rest changed end
            fun complete ()=case lookup goal of SOME proof=>proof
              | NONE=>if pass equations false then complete () else
                  raise ERR "close_ground_goal" "no exact ground context proof"
        in complete () end))
      fun run (Given (Seed {edge,...}))=edge
        | run (Forward (seed,inner))=transfer false seed inner
        | run (Backward (seed,inner))=transfer true seed inner
      and transfer reverse (Seed {row,edge,...}) inner=
        let val node= #node row
            val (left,right)=case equation
                (Seed {owner=owner,block=block,row=row,edge=edge}) of
                  SOME (a,b,_)=> (a,b)
                | NONE=>raise ERR "close_ground_goal" "equation changed"
            val law=constructor owner block node
            val equality=metadata owner (fn()=>boolSyntax.mk_eq
              (P.name block left,P.name block right))
            val proved=compose owner block equality [law,edge]
              (fn [eq,p]=>Thm.EQ_MP eq p
                | _=>raise ERR "close_ground_goal" "equality premises")
            val reversed=metadata owner (fn()=>boolSyntax.mk_eq
              (P.name block right,P.name block left))
            val oriented=if reverse then compose owner block reversed
                [proved] (fn [eq]=>Thm.SYM eq
                  | _=>raise ERR "close_ground_goal" "symmetry premise")
              else proved
            val premise=run inner
            val target=if reverse then left else right
            val result=compose owner block (named owner block target)
              [oriented,premise]
              (fn [eq,p]=>Thm.EQ_MP eq p
                | _=>raise ERR "close_ground_goal" "transfer premises")
        in result end
      val edge=run program
    in finish_goal work owner block edge end))
    handle primary=>(W.close work;raise primary))
  (* Fully realized clause only, never the originating Source Gamma.
     Count-only bounded metrics precede binding/FV inspection. *)
  fun clause_profile owner term=
    let val Owner {limits,...}=owner
        val limit= #output_limit limits
        val _=case SmtReplayImport.bounded_raw_size limit term of
            SOME _=>() | NONE=>raise ERR "project_rule" "raw clause bound"
        val _=case SmtReplayImport.bounded_binder_size limit term of
            SOME _=>() | NONE=>raise ERR "project_rule" "binder clause bound"
        val types=ref ([]:Type.hol_type list)
        fun ty t=(tick owner 1;types:=t:: !types;
          if Type.is_vartype t then
            tick owner (String.size (Type.dest_vartype t)) else
          let val {Thy,Tyop,Args}=Type.dest_thy_type t
          in tick owner (String.size Thy+String.size Tyop);
             List.app ty Args end)
        fun visit t=
          (tick owner 1;ty (Term.type_of t);
           if Term.is_comb t then let val (a,b)=Term.dest_comb t
             in visit a;visit b end
           else if Term.is_abs t then let val (v,b)=Term.dest_abs t
             in ty (Term.type_of v);visit b end
           else if Term.is_var t then
             tick owner (String.size (#1 (Term.dest_var t)))
           else if Term.is_const t then
             let val {Thy,Name,...}=Term.dest_thy_const t
             in tick owner (String.size Thy+String.size Name) end else ())
        val _=visit term
    in List.rev (!types) end
  fun project_rule work (Catalogue {owner=owner as Owner
      {marker,receiver,graph,frame,scope,assumptions,check_type,...},
       block,prefixes,...})
      (Seed {owner=Owner {marker=other,...},block=otherblock,row,edge})=
    ((expected work owner;
      if Portable.pointer_eq (marker,other) andalso
          Portable.pointer_eq (block,otherblock) then () else
        raise ERR "project_rule" "foreign projection seed";
      case receiver of RuleOriginal=>() | RuleStripped _=>()
        | _=>raise ERR "project_rule" "final receiver block is not expendable";
      protect owner (fn()=>
      let
          (* Each exported clause has its OWN expendable block. Source
             realization consumes that block; the catalogue and every
             other genuine Source path remain available. No final Q
             receiver block or previously consumed edge is reused. *)
          val bottom=metadata owner (fn()=>
            (tick owner 1;G.constant graph scope boolSyntax.F))
          val extras=case receiver of RuleStripped _=>
                assumptions @ [#denied (case owner of Owner d=>d)]
            | _=>[]
          val _=diagnostic owner "rule.freeze.before"
            (fn()=>" slot=" ^ Int.toString (#slot row))
          fun project fresh node [] edge=edge
            | project fresh node (left::path) edge=
              (case metadata owner (fn()=>binary owner node) of NONE=>
                  raise ERR "project_rule" "Source conjunction path changed"
               | SOME (a,b)=>
                 let val law=constructor owner fresh node
                     val conjunction=metadata owner (fn()=>
                       boolSyntax.mk_conj
                         (P.name fresh a,P.name fresh b))
                     val both=compose owner fresh conjunction [law,edge]
                       (fn [eq,p]=>Thm.EQ_MP eq p
                         | _=>raise ERR "project_rule" "projection premises")
                     val child=if left then a else b
                     val next=compose owner fresh
                       (named owner fresh child) [both]
                       (fn [p]=>if left then Thm.CONJUNCT1 p
                         else Thm.CONJUNCT2 p
                         | _=>raise ERR "project_rule" "conjunct premise")
                 in project fresh child path next end)
          val source=List.nth (assumptions,#slot row)
          fun validate target proof=
            let val _=active owner
                val d=P.source_realization_data_for work proof
                val _=metadata owner (fn()=>
                  if Portable.pointer_eq (#frame d,frame) andalso
                      #scope d=scope andalso #target d=target andalso
                      List.exists (fn (index,node)=>(tick owner 1;
                        index= #occurrence row andalso node=source))
                        (#source_occurrences d) then () else
                    raise ERR "project_rule" "Source incidence changed")
            in active owner end
          fun independent ()=
            let val fresh=P.prepare_needed_sources_with_work work
                  {frame=frame,roots=[bottom,#node row],
                   additional_sources=extras,closed_facts=[],conversions=[]}
                val initial=W.with_step work (fn()=>call owner
                  (fn()=>P.source fresh (#occurrence row)))
            in (fresh,source,#path row,initial,fn projected=>
              P.realize_source_owned_receipt work fresh
                (#node row) projected) end
          fun shared (SharedPrefix {node,path,receipt,...})=
            let
              val held=metadata owner (fn()=>(tick owner 1;!receipt))
              val proof=case held of SOME completed=>
                    (validate node completed;
                     diagnostic owner "rule.prefix.hit" (fn()=>
                       " occurrence=" ^ Int.toString (#occurrence row));
                     completed)
                | NONE=>
                  let
                    (* Empty receipt-owned preparation gives the actual
                       original ordered slots OriginalPrefixSlot origins.
                       A normal block receipt would mint block-local support
                       origins and append Gamma on every subsequent cut. *)
                    val prefix=P.prepare_source_cut_block work
                      {frame=frame,roots=[bottom,node],
                       additional_sources=[],closed_facts=[],conversions=[],
                       receipts=[]}
                    val producer=P.source_cut_block_for work prefix
                    val initial=W.with_step work (fn()=>call owner
                      (fn()=>P.source producer (#occurrence row)))
                    val _=diagnostic owner "rule.prefix.project.before"
                      (fn()=>"")
                    val projected=project producer source path initial
                    val _=active owner
                    val _=diagnostic owner "rule.prefix.realize.before"
                      (fn()=>"")
                    val completed=P.realize_source_cut_receipt work prefix
                      node projected
                    val _=validate node completed
                    val _=metadata owner (fn()=>(tick owner 1;
                      receipt:=SOME completed))
                    val _=diagnostic owner "rule.prefix.realize.after"
                      (fn()=>"")
                  in completed end
              val _=active owner
              (* No consumed edge crosses this boundary. The genuine
                 completed Source proof supplies a NEW one-shot native
                 programme with its actual opaque Gamma witnesses. *)
              val cut=P.prepare_source_cut_constructor_block work
                {frame=frame,roots=[bottom,#node row],
                 additional_sources=[],closed_facts=[],conversions=[],
                 receipts=[proof]}
              val fresh=P.source_cut_block_for work cut
              val initial=P.source_cut_edge_for work cut proof
              val rest=metadata owner (fn()=>
                let fun drop [] rest=rest
                      | drop (a::xs) (b::ys)=
                          (tick owner 1;if a=b then drop xs ys else
                            raise ERR "project_rule" "common path differs")
                      | drop _ _=raise ERR "project_rule" "short Source path"
                in drop path (#path row) end)
            in (fresh,node,rest,initial,fn projected=>
              P.realize_source_cut_receipt work cut
                (#node row) projected) end
          val prefix=metadata owner (fn()=>List.find
            (fn SharedPrefix {occurrence,...}=>
              (tick owner 1;occurrence= #occurrence row)) prefixes)
          val (fresh,start,path,initial,realize)=case prefix of
              NONE=>independent () | SOME saved=>shared saved
          val _=diagnostic owner "rule.project.before" (fn()=>"")
          val projected=project fresh start path initial
          val _=diagnostic owner "rule.profile.before" (fn()=>"")
          val term=G.representative graph (#node row)
          val types=metadata owner (fn()=>clause_profile owner term)
          (* CONJUNCT source incidence fixes every free variable/type of
             this leaf. Explicit forall binders are not generalized here. *)
          val fixed=metadata owner (fn()=>
            (tick owner 1;Term.free_vars term))
          val rigid_types=metadata owner (fn()=>
            (tick owner 1;Term.type_vars_in_term term))
          val _=W.with_step work (fn()=>List.app
            (fn ty=>call owner (fn()=>check_type ty)) types)
          val _=active owner
          (* This genuine provider OWNS its action; never wrap it in
             metadata/effect/with_step. It derives actual sparse slots. *)
          val _=diagnostic owner "rule.realize.before" (fn()=>"")
          val proof=realize projected
          val _=diagnostic owner "rule.realize.after" (fn()=>"")
          val _=validate (#node row) proof
      in ProjectedRule {owner=owner,row=row,proof=proof,
        fixed=fixed,rigid_types=rigid_types} end))
    handle primary=>(W.close work;raise primary))
  fun projected_rule_for work (ProjectedRule {owner=owner as Owner
      {frame,assumptions,receiver,...},row,proof,fixed,rigid_types})=
    (expected work owner;
     let val d=P.source_realization_data_for work proof
         val theorem=P.source_realization_theorem_for work proof
         val query=case receiver of RuleStripped query=>SOME query | _=>NONE
     in {frame=frame,query=query,assumption=List.nth (assumptions,#slot row),
       assumption_slot= #slot row,source_occurrence= #occurrence row,
       clause= #node row,proof=proof,theorem=theorem,
       fixed_variables=fixed,rigid_types=rigid_types} end)
  (* Completeness comes from the genuine private Catalogue.seeds program.
     FV(A /\ B)=FV(A) union FV(B); project_rule admits each actual leaf before
     inspecting its variables/types. Raw Source Gamma is never inspected. *)
  datatype rule_context=RuleContext of
    {catalogue:catalogue,rules:projected_rule list,
     origin_rules:projected_rule list,variables:Term.term list,
     rigid_types:Type.hol_type list}
  fun context_for work (RuleContext {catalogue=Catalogue
      {owner=owner as Owner {frame,receiver,...},...},rules,origin_rules,
       variables,
       rigid_types}) =
    (expected work owner;
     List.app (fn rule=>ignore (projected_rule_for work rule))
       (origin_rules @ rules);
     {frame=frame,query=case receiver of RuleStripped query=>SOME query
       | RuleOriginal=>NONE | _=>raise ERR "context_for"
           "not an independent projected Source catalogue",
      rules=rules,variables=variables,rigid_types=rigid_types})
    handle primary=>(W.close work;raise primary)
  fun project_context work (catalogue as Catalogue
      {owner=owner as Owner {receiver,check_type,...},seeds,...}) =
    ((expected work owner;
      case receiver of RuleOriginal=>() | RuleStripped _=>()
        | _=>raise ERR "project_context"
            "final Goal catalogue is not an independent rule producer";
      let
        (* Each actual occurrence is kept in original catalogue order.
           Duplicate Source slots are never collapsed into one origin. *)
        val rules=List.map (project_rule work catalogue) seeds
        (* Local stripped assumptions need not be the original S prefix.
           Capture its complete genuine catalogue too; no renewed Work,
           caller FV list, or full expanded Hyp inspection is introduced. *)
        val origin_rules=case receiver of RuleOriginal=>[]
          | RuleStripped _=>
              let val original=execute (prepare
                    (begin_rules_original work {check_type=check_type}))
                  val Catalogue {seeds=original_seeds,...}=original
              in List.map (project_rule work original) original_seeds end
          | _=>raise ERR "project_context" "Source receiver changed"
        val (variables,rigid_types)=W.with_step work (fn()=>call owner
          (fn()=>let
            fun variable_member _ []=false
              | variable_member term (held::rest)=
                  (tick owner 1;
                   Term.term_eq term held orelse variable_member term rest)
            fun type_member _ []=false
              | type_member ty (held::rest)=
                  (tick owner 1;
                   Type.compare (ty,held)=EQUAL orelse type_member ty rest)
            fun insert_variable (term,held)=
              (tick owner 1;
               if variable_member term held then held else held @ [term])
            fun insert_type (ty,held)=
              (tick owner 1;
               if type_member ty held then held else held @ [ty])
            fun collect (rule,(variables,rigid_types))=
              let val d=projected_rule_for work rule
                  val _=tick owner 1
              in (List.foldl insert_variable variables (#fixed_variables d),
                List.foldl insert_type rigid_types
                  (#rigid_types d)) end
          in List.foldl collect ([],[]) (origin_rules @ rules) end))
        val result=RuleContext {catalogue=catalogue,rules=rules,
          origin_rules=origin_rules,variables=variables,
          rigid_types=rigid_types}
        val _=ignore (context_for work result)
      in result end)
     handle primary=>(W.close work;raise primary))

  datatype context_candidate=ContextCandidate of {marker:unit ref,seed:seed}
  datatype context_metadata=ContextMetadata of
    {catalogue:catalogue,marker:unit ref,
     variables:Term.term list option,rigid_types:Type.hol_type list option,
     candidates:context_candidate list,held:G.node list,
     profiles:G.opaque_profile list,
     closures:(G.scope*G.binder_closure) list,
     selected:projected_rule list}
  fun context_metadata_for work (ContextMetadata
      {catalogue=Catalogue {owner=owner as Owner {frame,graph,scope,...},...},
       variables,rigid_types,candidates,held,profiles,closures,selected,...}) =
    (expected work owner;
     List.app (fn rule=>ignore(projected_rule_for work rule)) selected;
     List.app (fn node=>ignore(G.view graph node)) held;
     List.app (fn (caller,closure)=>ignore
       (G.binder_closure_data graph caller closure)) closures;
     List.app (fn profile=>ignore
       (G.opaque_profile_data graph scope profile)) profiles;
     {frame=frame,variables=variables,rigid_types=rigid_types,
      candidates=candidates}) handle primary=>(W.close work;raise primary)
  fun capture_context_metadata_roots work selected roots
      (catalogue as Catalogue
      {owner=owner as Owner {graph,sources,assumptions,scope,receiver,...},
       seeds,...}) =
    ((expected work owner;
      case receiver of RuleOriginal=>() | RuleStripped _=>()
        | _=>raise ERR "prepare_context_metadata"
            "not an independent context catalogue";
      W.with_step work (fn()=>call owner (fn()=>
      let
        val roots=roots(sources,assumptions)
        val selected_data=List.map (projected_rule_for work) selected
        fun override node=List.find (fn d=> #clause d=node) selected_data
        val variables=ref ([]:Term.term list)
        val types=ref ([]:Type.hol_type list)
        val fv_known=ref true val types_known=ref true
        val seen=ref (Redblackset.empty Int.compare)
        val held=ref ([]:G.node list)
        val profiles=ref ([]:G.opaque_profile list)
        val closures=ref ([]:(G.scope*G.binder_closure) list)
        fun variable term=
          (tick owner 1;
           if List.exists (fn held=>(tick owner 1;
               Term.term_eq held term)) (!variables) then ()
           else variables:= !variables @ [term])
        fun ty actual=
          (tick owner 1;
           if Type.is_vartype actual then
             (tick owner (String.size (Type.dest_vartype actual));
              if List.exists (fn held=>(tick owner 1;
                  Type.compare(held,actual)=EQUAL)) (!types) then ()
              else types:= !types @ [actual])
           else let val {Thy,Tyop,Args}=Type.dest_thy_type actual
             in tick owner (String.size Thy+String.size Tyop);
               List.app ty Args end)
        fun key_compare ((n,xs),(m,ys))=case Int.compare(n,m) of
            EQUAL=>Lib.list_compare Int.compare (xs,ys) | result=>result
        val fv_seen=ref (Redblackset.empty key_compare)
        fun free excluded node=
          let val _=tick owner 1
              val key=(G.node_id node,List.map (G.node_id o #1) excluded)
              fun allowed value=not(List.exists (fn (_,held)=>
                (tick owner 1;Term.term_eq held value)) excluded)
          in if Redblackset.member(!fv_seen,key) then () else
            (fv_seen:=Redblackset.add(!fv_seen,key);
             case override node of SOME d=>
               List.app (fn value=>if allowed value then variable value
                 else ()) (#fixed_variables d)
             | NONE=>case G.view graph node of G.Application(a,b)=>
               (free excluded a;free excluded b)
             | G.AdmittedBinder {binder,body,...}=>
                 free ((binder,G.representative graph binder)::excluded) body
             | G.Variable _=>if List.exists (fn (held,_)=>held=node)
                 excluded then () else variable(G.representative graph node)
             | G.Constant _=>()
             | G.OpaqueRetained=>fv_known:=false) end
        val geometry_seen=ref(Redblackset.empty Int.compare)
        fun geometry caller node=
          let val id=G.node_id node
          in if Redblackset.member(!geometry_seen,id) then () else
            (tick owner 1;geometry_seen:=Redblackset.add(!geometry_seen,id);
             held:=node:: !held;
             case G.view graph node of G.Application(a,b)=>
               (geometry caller a;geometry caller b)
             | G.AdmittedBinder {binder,body,...}=>
                 let val closure=G.binder_closure graph caller node
                     val d=G.binder_closure_data graph caller closure
                 in closures:=(caller,closure):: !closures;
                    geometry (#body_frame d) binder;
                    geometry (#body_frame d) body end
             | _=>()) end
        fun annotations caller node=
          let val _=tick owner 1 val id=G.node_id node
          in if Redblackset.member(!seen,id) then () else
            (seen:=Redblackset.add(!seen,id);held:=node:: !held;
             ty(G.type_of graph node);
             case override node of SOME d=>
               (List.app ty (#rigid_types d);geometry caller node)
             | NONE=>case G.view graph node of
               G.Application(a,b)=>
                 (annotations caller a;annotations caller b)
             | G.AdmittedBinder {binder,body,...}=>
                 let val closure=G.binder_closure graph caller node
                     val d=G.binder_closure_data graph caller closure
                 in closures:=(caller,closure):: !closures;
                    annotations (#body_frame d) binder;
                    annotations (#body_frame d) body end
             | G.OpaqueRetained=>
                 (case G.opaque_profile_for graph scope node of NONE=>
                    types_known:=false
                  | SOME profile=>
                      (profiles:=profile:: !profiles;List.app ty
                        (#types(G.opaque_profile_data graph scope profile))))
             | _=>()) end
        (* Actual graph identities/binding exclusions supply FV metadata.
           No bounded raw leaf projection or Source Gamma flattening occurs.
           Unknown opaque data remains explicit until a genuine receipt is
           available; it is never treated as an empty/closed context. *)
        val _=List.app (free []) roots
        val _=List.app (annotations scope) roots
        val marker=ref ()
        val candidates=List.map (fn seed=>
          ContextCandidate {marker=marker,seed=seed}) seeds
        val result=ContextMetadata {catalogue=catalogue,marker=marker,
          variables=if !fv_known then SOME (!variables) else NONE,
          rigid_types=if !types_known then SOME (!types) else NONE,
          candidates=candidates,held= !held,profiles= !profiles,
          closures= !closures,selected=selected}
        val _=ignore(context_metadata_for work result)
      in result end))) handle primary=>(W.close work;raise primary))
  fun capture_context_metadata work selected (catalogue as Catalogue
      {owner=Owner {sources,assumptions,...},...})=
    capture_context_metadata_roots work selected
      (fn(sources,assumptions)=>S.assumption_nodes sources @ assumptions)
      catalogue
  fun project_context_candidate work
      (metadata as ContextMetadata {catalogue,marker,...})
      (ContextCandidate {marker=held,seed}) =
    ((if Portable.pointer_eq(marker,held) then () else
        (W.close work;raise ERR "project_context_candidate"
          "different authentic candidate portfolio");
      ignore(context_metadata_for work metadata);
      (* Only this ACTUAL matching operation invokes bounded projection. *)
      project_rule work catalogue seed)
     handle primary=>(W.close work;raise primary))
  fun prepare_context_metadata work catalogue=
    capture_context_metadata work [] catalogue
  fun refine_context_candidate work
      (metadata as ContextMetadata {catalogue,selected,...}) candidate=
    let val rule=project_context_candidate work metadata candidate
        (* Only this genuine selected projection can refine an unknown
           opaque summary; its exact clause identity is held privately.
           No caller FV table or old semantic theorem is admitted. *)
        val refined=capture_context_metadata work (selected@[rule]) catalogue
    in {rule=rule,metadata=refined} end
    handle primary=>(W.close work;raise primary)

  (* A slice remains a distinct type; it cannot masquerade as the full
     context portfolio required for higher-order rigidity/freshness. *)
  datatype context_origin_metadata=ContextOriginMetadata of
    {whole:context_metadata,origin:G.node,slice:context_metadata}
  fun prepare_context_origin_metadata work
      (whole as ContextMetadata {catalogue=Catalogue
        {owner=owner as Owner {sources,assumptions,...},...},selected,...})
      origin=
    ((ignore(context_metadata_for work whole);
      W.with_step work(fn()=>call owner (fn()=>
        if List.exists(fn node=>(tick owner 1;node=origin))
            (S.assumption_nodes sources @ assumptions)then ()else
          raise ERR "context_origin_metadata"
            "node is not an authentic context assumption origin"));
      let val slice=capture_context_metadata_roots work selected
            (fn _=>[origin])
            (case whole of ContextMetadata {catalogue,...}=>catalogue)
          val result=ContextOriginMetadata
            {whole=whole,origin=origin,slice=slice}
          val _=expected work owner
      in result end)handle primary=>(W.close work;raise primary))
  fun context_origin_metadata_for work
      (ContextOriginMetadata {whole,origin,slice})=
    ((ignore(context_metadata_for work whole);
      let val d=context_metadata_for work slice
      in {frame= #frame d,origin=origin,variables= #variables d,
        rigid_types= #rigid_types d}end)
      handle primary=>(W.close work;raise primary))

end
