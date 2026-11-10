(* SAME equality/congruence programme. Static proof observation is DATA;
   every actual inference remains an authenticated caller-owned port. *)
signature SmtReplayNamedEqualityInput =
sig
  type proof
  val concl : proof -> Term.term
end

functor SmtReplayNamedEqualityFn (Native:SmtReplayNamedEqualityInput) =
struct
  type ('node,'edge) operations =
    {guard:unit -> unit,tick:unit -> unit,key:'node -> int,
     compare_keys:int * int -> order,
     same:'node * 'node -> bool,name:'node -> Term.term,
     equality:'node -> ('node * 'node) option,
     application:'node -> ('node * 'node) option,
     theorem:'edge -> Native.proof,constructor:'node -> 'edge,
     definition:'node -> 'edge,reflexive:'node -> 'edge,
     symmetry:'edge list -> 'edge,transitivity:'edge list -> 'edge,
     congruence:'edge list -> 'edge,equality_mp:'edge list -> 'edge,
     conjunction:'edge list -> 'edge,conjunct_left:'edge list -> 'edge,
     error:string -> exn}
  (* Fully applied, new-list-only helpers. No extra old-route
     closure, context record or list is constructed for []. *)
  fun checked_equations (operations:('node,'edge) operations) []=[]
    | checked_equations operations (((left,right),edge)::rest)=
        let
          val _=(#guard operations)()
          val _=(#tick operations)()
          val proof=(#theorem operations)edge
          val conclusion=Native.concl proof
          val (a,b)=boolSyntax.dest_eq conclusion
            handle Feedback.HOL_ERR _=>raise (#error operations)
              "non-equality additional equation"
          val _=(#tick operations)()
          val x=(#name operations)left
          val y=(#name operations)right
          val _=(#tick operations)()
          val _=if Portable.pointer_eq(a,x)andalso
              Portable.pointer_eq(b,y)then ()else
            raise (#error operations) "additional equation endpoint differs"
          val _=(#guard operations)()
          val _=(#tick operations)()
        in ((left,right),edge)::checked_equations operations rest end
  fun equations_append (operations:('node,'edge) operations) [] tail=tail
    | equations_append operations (value::rest) tail=
        ((#guard operations)();(#tick operations)();
         (#tick operations)();
         value::equations_append operations rest tail)
  fun retain_equations (operations:('node,'edge) operations) [] result=
        ((#guard operations)();result)
    | retain_equations operations ((_,support)::rest) result=
        ((#guard operations)();(#tick operations)();
         retain_equations operations rest
           ((#conjunct_left operations)
             [(#conjunction operations)[result,support]]))

  fun assemble_with_equations equations
      (operations:('node,'edge) operations)
      {rule,target,premises} =
    let
    fun valid ()=(#guard operations) ()
    fun tick ()=(#tick operations) ()
    fun endpoint(node,edge)=
      let val _=valid ()val _=tick ()
      in if Portable.pointer_eq(Native.concl((#theorem operations) edge),
          (#name operations) node)then ()else
        raise (#error operations) "incorrect named premise endpoint"end
    val _=List.app endpoint premises
    val(left,right)=case (#equality operations) target of SOME pair=>pair
      | NONE=>raise (#error operations) "non-equality conclusion"
    val _=ignore((#name operations) left)val _=ignore((#name operations) right)
    fun expose(node,edge)=
      let val _=tick ()
          val pair=case (#equality operations) node of SOME pair=>pair
            | NONE=>raise (#error operations) "non-equality premise"
          val bridge=(#constructor operations) node
      in (pair,(#equality_mp operations) [bridge,edge])end
    val incoming=List.map expose premises
    val extra=case equations of []=>[]
      | _=>checked_equations operations equations
    val available=case extra of []=>incoming
      | _=>equations_append operations extra incoming
    fun same(a,b)(c,d)=(#same operations)(a,c) andalso (#same operations)(b,d)
    fun find pair entries=case entries of []=>NONE
      | (candidate,proof)::rest=>
          (tick ();if same pair candidate then SOME proof
           else find pair rest)
    val memo=ref(Redblackmap.mkDict
      (fn((a,b),(c,d))=>case (#compare_keys operations)(a,c)of
        EQUAL=>(#compare_keys operations)(b,d)|result=>result))
    fun congruent(lhs,rhs)=
      (valid ();tick ();
       if (#same operations)(lhs,rhs) then (#reflexive operations) lhs else
       case find(lhs,rhs)available of SOME proof=>proof|NONE=>
       case find(rhs,lhs)available of SOME proof=>(#symmetry operations)[proof]
       | NONE=>
         let val key=((#key operations) lhs,(#key operations) rhs)
         in case Redblackmap.peek(!memo,key)of SOME proof=>proof|NONE=>
           let
             val proof=case((#application operations) lhs,(#application
               operations) rhs)of
                 (SOME(f,x),SOME(g,y))=>
                   let val left=(#definition operations) lhs
                       val a=congruent(f,g)val b=congruent(x,y)
                       val middle=(#congruence operations)[a,b]
                       val right=(#symmetry operations)[(#definition
                         operations) rhs]
                   in (#transitivity operations)
                     [(#transitivity operations)[left,middle],right]end
               | _=>raise (#error operations)
                   "unproved congruence leaf"
             val _=memo:=Redblackmap.insert(!memo,key,proof)
           in proof end
         end)
    fun ordered [] _=raise (#error operations) "empty transitivity"
      | ordered [((a,b),proof)] wanted=
          (tick ();if (#same operations)(a,wanted) andalso (#same
            operations)(b,right) then proof else
            raise (#error operations) "transitivity endpoint mismatch")
      | ordered(((a,b),proof)::rest)wanted=
          (tick ();if (#same operations)(a,wanted) then
            (#transitivity operations)[proof,ordered rest b]else
            raise (#error operations) "transitivity chain mismatch")
    fun symmetric_chain ()=
      let
        val neighbors=ref(Redblackmap.mkDict (#compare_keys operations))
        fun add(from,to,proof)=
          let val _=tick ()val key=(#key operations) from
          in neighbors:=Redblackmap.insert(!neighbors,key,
            (to,proof)::Option.getOpt
              (Redblackmap.peek(!neighbors,key),[]))end
        val _=List.app(fn((a,b),proof)=>
          (add(a,b,proof);add(b,a,(#symmetry operations)[proof])))available
        fun search [] [] _=raise (#error operations)
              "no symmetric transitivity path"
          | search [] back seen=search(List.rev back)[]seen
          | search((node,path)::rest)back seen=
              (valid ();tick ();if (#same operations)(node,right) then path
                else
               let fun enqueue((next,proof),(back,seen))=
                 (tick ();if Redblackset.member(seen,(#key operations)
                   next)then
                    (back,seen)else
                   ((next,(#transitivity operations)[path,proof])::back,
                    Redblackset.add(seen,(#key operations) next)))
                   val(back,seen)=List.foldl enqueue(back,seen)
                     (Option.getOpt
                       (Redblackmap.peek(!neighbors,(#key operations)
                         node),[]))
               in search rest back seen end)
      in search[(left,(#reflexive operations) left)][]
        (Redblackset.singleton (#compare_keys operations)((#key operations)
          left))end
    val proof=case rule of
        "refl"=>(case extra of []=>
          if null premises andalso (#same operations)(left,right) then
            (#reflexive operations) left else
            raise (#error operations) "invalid reflexivity endpoints"
        | _=>if null premises then congruent(left,right)else
            raise (#error operations) "invalid reflexivity endpoints")
      | "symm"=>(case extra of []=>
          (case incoming of [((a,b),proof)]=>
            if (#same operations)(a,right) andalso (#same
              operations)(b,left) then (#symmetry operations)[proof]else
              raise (#error operations) "invalid symmetry endpoints"
          | _=>raise (#error operations) "symmetry expects one premise")
        | _=>(case incoming of [((a,b),proof)]=>
            let val first=congruent(left,b)
                val middle=(#symmetry operations)[proof]
                val last=congruent(a,right)
            in (#transitivity operations)
              [(#transitivity operations)[first,middle],last]end
          | _=>raise (#error operations) "symmetry expects one premise"))
      | "trans"=>(case extra of []=>ordered incoming left
        | _=>symmetric_chain())
      | "cong"=>congruent(left,right)
      | "trans-star"=>symmetric_chain()
      | _=>raise (#error operations) "unknown equality procedure"
    val target_bridge=(#constructor operations) target
    val named=(#equality_mp operations)
      [(#symmetry operations)[target_bridge],proof]
    (* The old procedure retains all premise dependencies, including a
       redundant support. Preserve that actual proof operation here. *)
    val result=List.foldl(fn((_,support),result)=>
      (#conjunct_left operations)
        [(#conjunction operations)[result,support]])named premises
    val result=case extra of []=>result
      | _=>retain_equations operations extra result
    val _=endpoint(target,result)val _=valid ()
    in result end
  fun assemble operations inputs=
    assemble_with_equations [] operations inputs
end
