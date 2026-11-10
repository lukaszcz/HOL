(* SAME witnessed implication programme, specialized once on owner ports. *)
functor SmtReplayImplicationLawFn
  (Native:sig
     type block
     type edge
     val owner_for:SmtReplayInvocationWork.portfolio -> block ->
       {graph:SmtReplayGraph.graph,scope:SmtReplayGraph.scope,
        contract:SmtReplayNativeContract.contract}
     val theorem:SmtReplayInvocationWork.portfolio -> block -> edge ->
       Thm.thm
     val name:SmtReplayInvocationWork.portfolio -> block ->
       SmtReplayGraph.node -> Term.term
     val constructor:SmtReplayInvocationWork.portfolio -> block ->
       SmtReplayGraph.node -> edge
     val derive:SmtReplayInvocationWork.portfolio -> block ->
       SmtReplayProof.compact_primitive -> edge list -> edge
     val implication_mp:SmtReplayInvocationWork.portfolio -> block ->
       edge -> edge -> edge
     val error:string -> string -> exn
   end) =
struct
  structure G=SmtReplayGraph
  structure P=SmtReplayProof
  val ERR=Native.error
  fun apply_implication_law_with_policy work graph block
      {law=(law_node,law_edge),target,premises} =
    ((let val owner=Native.owner_for work block
          val _=if Portable.pointer_eq(graph,#graph owner) then () else
            raise ERR "policy_apply_law" "different graph"
          val _=SmtReplayInvocationWork.spend_policy work 0
          fun valid ()=ignore(Native.owner_for work block)
          fun endpoint(node,edge)=
            let val _=valid ()
                val proof=Native.theorem work block edge
                val named=Native.name work block node
            in if Portable.pointer_eq(Thm.concl proof,named) then () else
              raise ERR "policy_apply_law" "incorrect named endpoint" end
          val _=List.app endpoint ((law_node,law_edge)::premises)
          fun fixed opcode inputs=Native.derive work block opcode inputs
          fun modus law premise=
            Native.implication_mp work block law premise
          fun walk node proof []=
                if node=target then proof else
                  raise ERR "policy_apply_law" "different final target"
            | walk node proof ((wanted,premise)::rest)=
              let val _=valid ()
                  val _=SmtReplayInvocationWork.spend_policy work 3
                  val(part,next)=case G.view graph node of
                      G.Application pair=>pair
                    | _=>raise ERR "policy_apply_law" "law not implication"
                  val(head,antecedent)=case G.view graph part of
                      G.Application pair=>pair
                    | _=>raise ERR "policy_apply_law" "law not implication"
                  val _=case G.view graph head of G.Constant _=>
                      if Term.same_const (G.representative graph head)
                          boolSyntax.implication then () else
                        raise ERR "policy_apply_law" "law not implication"
                    | _=>raise ERR "policy_apply_law" "law not implication"
                  val _=if antecedent=wanted then () else
                    raise ERR "policy_apply_law" "different actual premise"
                  val exposed=fixed P.EqualityMP
                    [Native.constructor work block node,proof]
                  val result=modus exposed premise
              in walk next result rest end
          val result=walk law_node law_edge premises
          val _=endpoint(target,result)
          val _=valid ()
      in result end)
     handle primary=>(SmtReplayInvocationWork.close work;raise primary))

end
