(* Paid typed ordinary-App comparison, never an equality certificate. *)
structure SmtReplayValueAtomPairs :> SmtReplayValueAtomPairs =
struct
  structure W=SmtReplayInvocationWork
  structure GP=SmtLib_GraphPreprocess
  structure VP=SmtLib_GraphValueProof
  structure PV=SmtLib_GraphParserValue
  val ERR=Feedback.mk_HOL_ERR "SmtReplayValueAtomPairs"
  type key=(int * int) * (int * int)
  datatype state=State of
    {work:W.portfolio,context:PV.context,guard:unit -> unit,
     compared:key Redblackset.set ref,
     weights:(Type.hol_type * IntInf.int) list ref,
     pairs:(PV.proof_term * PV.proof_term) list ref,
     xors:PV.proof_term list ref}
  fun header expected (State{work,...})=
    if Portable.pointer_eq(expected,work)then ()else
      raise ERR "owner" "different original Work"
  fun live expected(saved as State{guard,...})=
    (header expected saved;guard())
  fun pay expected saved amount=
    (live expected saved;W.spend_policy expected amount)
  fun create expected query packet=
    let
      val _=GP.validate_query_with_policy expected query
      val contents=VP.contents_with_policy_for expected query packet
      (* Seven stored fields/record/constructor, four refs, empty set,
         guard/comparator/pay/tick closures, and actual context projection. *)
      val _=W.spend_policy expected 19
      val context= #context contents
      fun guard()=ignore(VP.contents_with_policy_for expected query packet)
      fun spend amount=(guard();W.spend_policy expected amount)
      fun tick()=spend 1
      fun compare((a,b),(c,d))=
        let val _=spend 1
            fun pair((x,y),(z,w))=
              (tick();case Int.compare(x,z)of EQUAL=>
                 (tick();Int.compare(y,w))|answer=>answer)
        in case pair(a,c)of EQUAL=>pair(b,d)|answer=>answer end
      val state=State{work=expected,context=context,guard=guard,
        compared=ref(Redblackset.empty compare),weights=ref[],
        pairs=ref[],xors=ref[]}
      val _=live expected state
    in state end
    handle primary=>(W.close expected;raise primary)
  fun type_weight expected(saved as State{weights,...})ty=
    let
      val _=live expected saved
      (* Success-only physical Type memo; incidences are summed exactly
         even when two child edges point at the same cached Type. *)
      val _=pay expected saved 2
      fun find []=(pay expected saved 1;NONE)
        | find((held,weight)::rest)=
            (pay expected saved 2;
             if Portable.pointer_eq(ty,held)then
               (pay expected saved 1;SOME weight)else find rest)
      fun sum [] total=(pay expected saved 1;total)
        | sum(child::rest)total=
            (pay expected saved 2;
             sum rest(total+type_weight expected saved child))
    in case find(!weights)of SOME value=>value | NONE=>
      let
        val _=pay expected saved 1
        val value=if Type.is_vartype ty then
            let val _=pay expected saved 2
                val text=Type.dest_vartype ty
                val amount=IntInf.fromInt(String.size text)
                val _=pay expected saved(1+amount)
            in 1+amount end
          else
            let val _=pay expected saved 3
                val(name,children)=Type.dest_type ty
                val _=pay expected saved
                  (1+IntInf.fromInt(String.size name))
            in sum children 1 end
        val _=pay expected saved 4
        val _=weights:=(ty,value):: !weights
      in value end
    end
  fun constant_weight expected saved atom=
    let val _=pay expected saved 4
        val {Thy,Name,Ty}=Term.dest_thy_const atom
        val amount=1+IntInf.fromInt(String.size Thy)+
          IntInf.fromInt(String.size Name)+type_weight expected saved Ty
        val _=pay expected saved amount
    in amount end
  fun same_key expected saved((a,b),(c,d))=
    (pay expected saved 1;
     a=c andalso(pay expected saved 1;b=d))
  fun demand expected(saved as State{context,compared,pairs,...})
      (left,right)=
    let
      val _=live expected saved
      (* One recursive walk closure; no new state on the caller's NONE
         identity route, which never invokes this module. *)
      val _=pay expected saved 1
      fun visit(a,b)=
        let
          val _=pay expected saved 3
          val key_a=PV.proof_key context a
          val key_b=PV.proof_key context b
          val key=(key_a,key_b)
          val _=pay expected saved 1
        in if Redblackset.member(!compared,key)then true else
          let
            val _=pay expected saved 2
            val answer=if same_key expected saved key then true else
              let
                val _=pay expected saved 2
                val ty_a=PV.proof_type_of context a
                val ty_b=PV.proof_type_of context b
                val x=type_weight expected saved ty_a
                val y=type_weight expected saved ty_b
                val _=pay expected saved(1+x+y)
              in Type.compare(ty_a,ty_b)=EQUAL andalso
                (pay expected saved 3;
                 case(PV.proof_view context a,PV.proof_view context b)of
                   (PV.ProofApplication(f,x),PV.ProofApplication(g,y))=>
                     visit(f,g)andalso visit(x,y)
                 | (PV.ProofConstant x,PV.ProofConstant y)=>
                     let val a=constant_weight expected saved x
                         val b=constant_weight expected saved y
                         val _=pay expected saved(1+a+b)
                     in Term.compare(x,y)=EQUAL end
                 (* A variable/binder/opaque leaf keeps its genuine key.
                    Same printed names or Types grant no correspondence. *)
                 | _=>false)
              end
            val _=if answer then
                (pay expected saved 2;
                 compared:=Redblackset.add(!compared,key))else()
          in answer end
        end
      val answer=visit(left,right)
      val _=if answer then
          (pay expected saved 4;pairs:=(left,right):: !pairs)else()
      val _=live expected saved
    in answer end
    handle primary=>(W.close expected;raise primary)
  fun pairs_for expected(saved as State{pairs,...})=
    let val _=live expected saved
        val _=pay expected saved 1
        fun reverse [] result=(live expected saved;result)
          | reverse(pair::rest)result=
              (pay expected saved 2;reverse rest(pair::result))
    in reverse(!pairs)[]end
    handle primary=>(W.close expected;raise primary)
  (* A fixed-law demand is DATA only. Its actual constructor and
     native definition are authenticated later by the genuine N block. *)
  fun demand_xor expected(saved as State{context,xors,...})node=

      let val _=live expected saved
          val _=pay expected saved 5
          val _=ignore(PV.proof_type_of context node)
          val _=xors:=node:: !xors
      in live expected saved end
    handle primary=>(W.close expected;raise primary)
  fun xors_for expected(saved as State{xors,...})=
    let val _=live expected saved val _=pay expected saved 1
        fun reverse [] result=(live expected saved;result)
          | reverse(node::rest)result=
              (pay expected saved 2;reverse rest(node::result))
    in reverse(!xors)[]end
    handle primary=>(W.close expected;raise primary)

end
