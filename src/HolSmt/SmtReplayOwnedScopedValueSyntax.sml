structure SmtReplayOwnedScopedValueSyntax :>
    SmtReplayOwnedScopedValueSyntax =
struct
  structure W=SmtReplayInvocationWork
  structure G=SmtReplayGraph
  structure C=SmtReplayOwnedScopedValueContext
  structure PV=SmtLib_GraphParserValue
  structure N=SmtReplayNamedContext
  structure Names=SmtReplayValueNames
  structure I=SmtReplayValueInterpretation
  structure NC=SmtReplayNativeContract
  structure Z=Z3_GraphProofParser
  val ERR=Feedback.mk_HOL_ERR "SmtReplayOwnedScopedValueSyntax"
  type syntax=PV.proof_term
  datatype requirement=NativeOpening of syntax
  exception Missing of requirement
  type data={context:C.context,body:syntax,body_profile:N.profile,
    key:syntax -> int,name:syntax -> Term.term,
    profile:syntax -> N.profile,semantic:syntax -> G.node,
    view:syntax -> syntax N.view,
    reachable:syntax list,cells:I.cell list,type_ports:Type.hol_type list,
    freeze:syntax N.freeze_plan}
  datatype plan=Plan of
    {work:W.portfolio,guard:unit -> unit,data:data}
  datatype preparation=Prepared of plan | Needs of requirement list
  datatype result=Finished of plan | Pending of requirement
  fun prepare expected captured=((
    case W.with_step expected (fn()=>
      ((let
        val _=W.spend_policy expected 1
        val held=SmtReplayOwnedScopedValueContext.data_for
          expected captured
        val values= #values held
        val native=NC.for_work expected (#native_contract held)
        val semantic= #semantic_limits native
        val cap=IntInf.fromInt(Int.min(#template_limit semantic,
          Int.min(#input_limit semantic,#output_limit semantic)))
        val ceiling=IntInf.fromInt (#type_work_limit native)
        (* Private visitors, dictionaries/refs and closures.
           Repeated visitors/records below have their own actual quotes. *)
        val _=W.spend_policy expected 43
        val _=W.spend_policy expected 1
        val native_error=ERR "native"
        (* The captured context checks these same declaration stamps. *)
        fun guard ()=ignore(C.data_for expected captured)
        fun pay amount=(guard ();W.spend_policy expected amount)
        fun tick ()=pay 1
        fun pair_compare((a,b),(c,d))=
          (tick ();case Int.compare(a,c)of EQUAL=>
             (tick ();Int.compare(b,d))|other=>other)
        fun id_compare(a,b)=(tick ();Int.compare(a,b))
        val keys=ref(Redblackmap.mkDict pair_compare)
        val serial=ref 0
        val locked=ref false
        fun key term=
          let val actual=PV.proof_key values term val _=tick ()
          in case Redblackmap.peek(!keys,actual)of SOME id=>id | NONE=>
            let val _=tick()
                val _=if !locked then raise ERR "key"
                    "syntax outside the sealed scoped inventory"else ()
                val _=pay 4 val id= !serial
                val _=serial:=id+1
                val _=keys:=Redblackmap.insert(!keys,actual,id)
            in id end end
        fun reverse rows=
          let val _=tick ()
              fun loop [] result=(guard ();result)
                | loop(x::rest)result=(pay 2;loop rest(x::result))
          in loop rows [] end
        fun map action []=(guard ();[])
          | map action (x::rest)=(pay 2;action x::map action rest)
        fun append [] tail=(guard ();tail)
          | append(x::rest)tail=(pay 2;x::append rest tail)
        val profiles=ref(Redblackmap.mkDict id_compare)
        val ordered=ref([]:syntax list)
        val type_ports=ref([]:Type.hol_type list)
        fun remember_type ty=(pay 2;type_ports:=ty:: !type_ports)
        fun weight ty=N.type_weight_using pay native_error ceiling ty
        fun visit term=
          let val _=tick () val id=key term
          in case Redblackmap.peek(!profiles,id)of SOME p=>p | NONE=>
            let
              val ty=PV.proof_type_of values term
              val own=weight ty
              val _=remember_type ty
              val _=pay 5
              val p:N.profile=case PV.proof_view values term of
                  PV.ProofVariable _=>{raw=1,inc=1,ann=own,ty=own}
                | PV.ProofConstant _=>{raw=1,inc=1,ann=own,ty=own}
                | PV.ProofApplication(f,x)=>
                    let val a=visit f val b=visit x
                    in {raw=1+ #raw a+ #raw b,
                      inc=1+ #inc a+ #inc b,
                      ann=own+ #ann a+ #ann b,ty=own}end
                | _=>(pay 2;raise Missing(NativeOpening term))
              val _=if #raw p<=cap andalso #inc p<=cap andalso
                  #ann p<=ceiling then ()else
                raise ERR "prepare" "actual scoped native syntax cap"
              val _=pay 4
              val _=profiles:=Redblackmap.insert(!profiles,id,p)
              val _=ordered:=term:: !ordered
            in p end
          end
        fun same_id(Z.Named a,Z.Named b)=
              (tick ();Int.compare(a,b)=EQUAL)
          | same_id(Z.Anonymous a,Z.Anonymous b)=
              (tick ();Int.compare(a,b)=EQUAL)
          | same_id _=(tick ();false)
        fun body []=raise ERR "prepare" "missing actual scoped body"
          | body(({id,target,...}:C.command)::rest)=
              (tick ();if same_id(id,#body held)then target else body rest)
        val actual_body=body(#commands held)
        val body_profile=visit actual_body
        val _=pay 2
        val _=List.app(fn value=>
          ignore(visit(PV.proof_term values value)))(#roots held)
        val reachable=reverse(!ordered)
        (* The shared allocator inventories genuine free IDs, actual
           binder atoms and fixed schema names. Its Type callback is a
           private inventory collector, never the caller policy callback. *)
        val _=pay 2
        val variables= #variables
          (SmtLib_GraphValueProof.binding_frame_data_for
            expected (#query held) (#binding held))
        val binders=map (PV.proof_term values) variables
        val names=Names.allocate guard tick pay values key native
          remember_type ERR append append map map variables (#roots held)
          binders reachable
        val _=tick()
        val _=locked:=true
        fun view term=(tick ();case PV.proof_view values term of
            PV.ProofVariable _=>N.Atom
          | PV.ProofConstant atom=>N.Constant atom
          | PV.ProofApplication(f,x)=>N.Application(f,x)
          | _=>raise ERR "view" "unadmitted scoped syntax")
        (* Validate every atomic image before publishing any compound
           image. Exact graph references retain the actual free/Bound ID;
           printed names cannot supply an otherwise missing atomic port. *)
        val _=pay 5
        val atoms=ref(Redblackmap.mkDict id_compare)
        val images=ref(Redblackmap.mkDict id_compare)
        fun image term=
          let val _=tick()val id=key term
          in case Redblackmap.peek(!images,id)of SOME node=>node
            | NONE=>raise ERR "semantic" "missing earlier typed image"end
        fun atomic []=guard()
          | atomic(term::rest)=
            let val _=tick()
                val actual=case PV.proof_view values term of
                    PV.ProofVariable _=>
                      (case PV.proof_graph_reference values term of
                          SOME reference=>
                            let val _=pay 3
                                val _=if Portable.pointer_eq
                                    (#graph reference,#graph held)then ()
                                  else raise ERR "semantic"
                                    "different actual atomic graph"
                                val node=G.closure_child_node(#graph held)
                                  (#scope reference)(#child reference)
                                val _=ignore(G.closure_root(#graph held)
                                  (#child held)node)
                            in SOME node end
                        | NONE=>raise Missing(NativeOpening term))
                  | _=>NONE
                val _=case actual of NONE=>()|SOME node=>
                  (pay 2;atoms:=Redblackmap.insert(!atoms,key term,node))
            in atomic rest end
        val _=atomic reachable
        fun compile []=guard()
          | compile(term::rest)=
            let val _=tick()val id=key term
                val node=case PV.proof_view values term of
                    PV.ProofVariable _=>
                      (tick();Redblackmap.find(!atoms,id))
                  | PV.ProofConstant atom=>
                      (pay 3;G.constant(#graph held)(#child held)atom)
                  | PV.ProofApplication(f,x)=>
                      (pay 4;G.application(#graph held)(#child held)
                        (image f,image x))
                  | _=>raise ERR "semantic" "unadmitted typed image"
                val _=pay 3
                val _=images:=Redblackmap.insert(!images,id,node)
            in compile rest end
        val _=compile reachable
        fun measured term=
          (tick();Redblackmap.find(!profiles,key term))
        (* Eight fields+record, one partial Type reader and native closure.
           The resulting N plan performs no ASSUME or user callback. *)
        val _=pay 11
        val operations:syntax N.operations=
          {guard=guard,spend=pay,key=key,type_of=PV.proof_type_of values,
           view=view,name=names,check_type=remember_type,
           native_limits=fn()=>native}
        val _=pay 4
        val freeze=N.prepare_freeze operations
          {nodes=reachable,sources=[],template_limit= #template_limit
            semantic}
        fun cell term=
          let val _=pay 7 val actual=PV.proof_key values term
              val ty=PV.proof_type_of values term
              val shape=case PV.proof_view values term of
                  PV.ProofVariable _=>
                    (case PV.proof_graph_reference values term of
                        SOME actual=>
                          let val _=pay 3
                              val _=if Portable.pointer_eq
                                  (#graph actual,#graph held)then ()else
                                raise ERR "cell" "different atomic graph"
                              val node=G.closure_child_node (#graph held)
                                (#scope actual)(#child actual)
                              val _=ignore(G.closure_root (#graph held)
                                (#child held)node)
                          in I.Borrowed node end
                      | NONE=>raise ERR "cell"
                          "admitted atomic graph port changed")
                | PV.ProofConstant atom=>I.Atomic atom
                | PV.ProofApplication(f,x)=>
                    (pay 3;I.Application(PV.proof_key values f,
                      PV.proof_key values x))
                | _=>raise ERR "cell" "unadmitted scoped syntax"
          in {key=actual,name=names term,hol_type=ty,body=shape}:I.cell end
        val cells=map cell reachable
        val ports=reverse(!type_ports)
        (* Twelve data fields+record, three owner fields+constructor and
           publication wrappers. No scoped result/Ready constructor. *)
        val _=pay 19
        val data:data={context=captured,body=actual_body,
          body_profile=body_profile,key=key,name=names,
          profile=measured,semantic=image,view=view,
          reachable=reachable,cells=cells,type_ports=ports,freeze=freeze}
        val value=Plan{work=expected,guard=guard,data=data}
        val _=guard ()
      in Finished value end)
      handle Missing required=>
        (W.spend_policy expected 3;Pending required))) of
        Finished value=>Prepared value
      | Pending required=>Needs[required])
    handle primary=>(W.close expected;raise primary))
  fun data_for expected (Plan{work,guard,data})=((
    (if Portable.pointer_eq(expected,work)then ()else
       raise ERR "data_for" "different Work portfolio";
     guard ();data))
    handle primary=>(W.close expected;raise primary))
end
