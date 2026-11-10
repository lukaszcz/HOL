(* SAME actual preprocessing assembler over static authentic owner ports.
   The validation datatype stays private in GraphPreprocess. *)
functor SmtReplayPreprocessAssemblyFn
  (Input:sig
     type block
     type edge
  datatype validation = Validation of
    {graph : SmtReplayGraph.graph,  scope : SmtReplayGraph.scope,  sources :
       SmtReplaySource.sources,
     assumptions : SmtReplayCanonGraph.graph_conversion list,
     goal : SmtReplayCanonGraph.graph_conversion,  denied :
       SmtReplayGraph.node,  roots : SmtReplayGraph.node list}
    | Portfolio of SmtLib_GraphSourcePortfolio.validation
     val owner_for:SmtReplayInvocationWork.portfolio -> block ->
       {graph:SmtReplayGraph.graph,scope:SmtReplayGraph.scope,
        contract:SmtReplayNativeContract.contract}
     val sources:SmtReplayInvocationWork.portfolio -> block ->
       SmtReplayGraph.node list
     val source:SmtReplayInvocationWork.portfolio -> block -> int -> edge
     val name:SmtReplayInvocationWork.portfolio -> block ->
       SmtReplayGraph.node -> Term.term
     val derive:SmtReplayInvocationWork.portfolio -> block ->
       SmtReplayProof.compact_primitive -> edge list -> edge
     val constructor:SmtReplayInvocationWork.portfolio -> block ->
       SmtReplayGraph.node -> edge
     val definition:SmtReplayInvocationWork.portfolio -> block ->
       SmtReplayGraph.node -> edge
     val graph_assemble:SmtReplayInvocationWork.portfolio ->
       SmtReplayGraph.graph -> block -> SmtReplayCanonGraph.graph_conversion ->
       edge
     val portfolio_assemble:SmtReplayInvocationWork.portfolio ->
       SmtLib_GraphSourcePortfolio.validation -> block ->
       SmtReplayGraph.node -> edge option
     val validate_with_policy:SmtReplayInvocationWork.portfolio ->
       validation -> unit
     val source_nodes:validation -> SmtReplayGraph.node list
     val error:string -> string -> exn
   end) =
struct
  structure G=SmtReplayGraph
  structure C=SmtReplayCanonGraph
  structure P=SmtReplayProof
  structure S=SmtReplaySource
  structure W=SmtReplayInvocationWork
  open Input
  val ERR=Input.error
  fun assembler_with_policy work (Portfolio value) block =
        Input.portfolio_assemble work value block
    | assembler_with_policy work (validation as Validation
        {graph,scope,sources,assumptions,goal,denied,...}) block =
      ((W.with_step work (fn () =>
        let
          val owner = Input.owner_for work block
          fun valid () =
            (validate_with_policy work validation;
             ignore (Input.owner_for work block))
          val _ = valid ()
          val _ = if Portable.pointer_eq (graph,#graph owner) andalso
              G.scope_visible graph (#scope owner) scope then () else
            raise ERR "policy_assembler" "different graph or invisible scope"
          val originals = source_nodes validation
          fun prefix [] _ = ()
            | prefix (_::_) [] =
                raise ERR "policy_assembler" "original Source prefix absent"
            | prefix (wanted::rest) (held::tail) =
                (W.spend_policy work 2;
                 if wanted=held then prefix rest tail else
                   raise ERR "policy_assembler" "original Source changed")
          val _ = prefix originals (Input.sources work block)
          fun source node =
            let fun seek [] _ =
                      raise ERR "policy_assembler" "original Source absent"
                  | seek (held::rest) index =
                      (W.spend_policy work 2;
                       if node=held then Input.source work block index else
                         seek rest (index+1))
            in seek originals 0 end
          fun rule opcode inputs = Input.derive work block opcode inputs
          fun equality conversion =
            let val converted=Input.graph_assemble
                  work graph block conversion
            in rule P.EqualityMP
              [Input.constructor work block
                 (C.graph_equality conversion),converted] end
          fun assumption conversion =
            if C.graph_source conversion=C.graph_result conversion then
              source (C.graph_source conversion)
            else rule P.EqualityMP
              [equality conversion,source (C.graph_source conversion)]
          fun denied_goal () =
            let val original = S.denied_goal_node sources in
              if original=denied then source original else
                let
                  val operator = case G.view graph original of
                      G.Application (operator,_) => operator
                    | _ => raise ERR "policy_assembler"
                        "original denied goal has no negation operator"
                  val definition = Input.definition work block operator
                  val reflexive = rule P.Transitivity
                    [rule P.Symmetry [definition],definition]
                  val negative = rule P.Congruence
                    [reflexive,equality goal]
                  val old_fact = rule P.EqualityMP
                    [Input.constructor work block original,
                     source original]
                  val new_fact = rule P.EqualityMP [negative,old_fact]
                in rule P.EqualityMP
                  [rule P.Symmetry
                     [Input.constructor work block denied],
                   new_fact] end
            end
          val memo = ref ([]:(G.node * Input.edge) list)
          fun saved _ [] = NONE
            | saved node ((held,edge)::rest) =
                (W.spend_policy work 1;
                 if node=held then SOME edge else saved node rest)
          fun find _ [] = NONE
            | find node (conversion::rest) =
                (W.spend_policy work 2;
                 if C.graph_result conversion=node then SOME conversion else
                   find node rest)
          fun assemble node = W.with_step work (fn () =>
            let
              val _ = valid ()
              val _ = W.spend_policy work 1
              val _ = ignore (Input.name work block node)
              val result = case saved node (!memo) of
                  SOME edge => SOME edge
                | NONE =>
                    let val edge = case find node assumptions of
                            SOME conversion => SOME (assumption conversion)
                          | NONE => if node=denied then SOME (denied_goal ())
                              else NONE
                        val _ = Option.app (fn held =>
                          (W.spend_policy work 1;
                           memo := (node,held):: !memo)) edge
                    in edge end
              val _ = valid ()
            in result end)
          val _ = valid ()
        in assemble end))
       handle primary => (W.close work;raise primary))

end
