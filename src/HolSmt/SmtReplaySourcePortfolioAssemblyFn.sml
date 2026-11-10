(* SAME SourcePortfolio assembler, statically specialized to an owner.
   Original private fact/validation datatypes stay inside the sealed owner. *)
functor SmtReplaySourcePortfolioAssemblyFn
  (Input:sig
     type block
     type edge
     type inst_plan
  datatype fact = Fact of
    {identity : int, graph : SmtReplayGraph.graph, scope :
       SmtReplayGraph.scope, node : SmtReplayGraph.node, row : row}
  and row = Original of SmtReplaySource.sources * int
    | PolicyOriginal of SmtReplaySource.sources * IntInf.int *
       SmtReplayGraph.node
    | Closed of SmtReplayCanonGraph.graph_conversion
    | RecordedClosed of SmtReplayProof.closed_fact
    | Transport of SmtReplayCanonGraph.graph_conversion * fact
    | BinderTransport of SmtReplayProof.closed_conversion * fact
    | Apply of {law : fact,premises : fact list}
  datatype validation = Validation of
    {graph : SmtReplayGraph.graph, scope : SmtReplayGraph.scope, sources :
       SmtReplaySource.sources,
     assumptions : fact list, goal : SmtReplayGraph.node, denied : fact, roots
       : SmtReplayGraph.node list,
     template_limit : int,closed_facts : SmtReplayProof.closed_fact list,
     conversions : SmtReplayProof.closed_conversion list}
    | PolicyValidation of
    {work:SmtReplayInvocationWork.portfolio, graph:SmtReplayGraph.graph,
       scope:SmtReplayGraph.scope, sources:SmtReplaySource.sources,
     limits:SmtReplayResourcePolicy.semantic_policy, assumptions:fact list,
       goal:SmtReplayGraph.node,
     denied:fact, roots:SmtReplayGraph.node list,
       closed_facts:SmtReplayProof.closed_fact list,
     conversions:SmtReplayProof.closed_conversion list}
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
     val closed:SmtReplayInvocationWork.portfolio -> block ->
       SmtReplayProof.closed_fact -> edge
     val conversion:SmtReplayInvocationWork.portfolio -> block ->
       SmtReplayProof.closed_conversion -> edge
     val prepare_inst:SmtReplayInvocationWork.portfolio -> block ->
       {substitution:(Term.term,Term.term)Lib.subst,theorem:Thm.thm} ->
       inst_plan
     val execute_inst:SmtReplayInvocationWork.portfolio -> inst_plan -> edge
     val graph_assemble:SmtReplayInvocationWork.portfolio ->
       SmtReplayGraph.graph -> block -> SmtReplayCanonGraph.graph_conversion ->
       edge
     val apply_law:SmtReplayInvocationWork.portfolio -> SmtReplayGraph.graph ->
       block -> {law:SmtReplayGraph.node * edge,target:SmtReplayGraph.node,
         premises:(SmtReplayGraph.node * edge) list} -> edge
     val validate_with_policy:SmtReplayInvocationWork.portfolio ->
       validation -> unit
     val nodes:SmtReplaySource.sources -> SmtReplayGraph.node list
     val endpoint:fact -> SmtReplayGraph.node
     val error:string -> string -> exn
   end) =
struct
  structure G=SmtReplayGraph
  structure C=SmtReplayCanonGraph
  structure P=SmtReplayProof
  structure W=SmtReplayInvocationWork
  open Input
  val ERR=Input.error
  fun assembler_with_policy expected value block =
    ((W.with_step expected (fn () =>
      let
        val _ = case value of PolicyValidation {work,...} =>
            if Portable.pointer_eq (expected,work) then () else
              raise ERR "policy_assembler" "different original Work"
          | _ => raise ERR "policy_assembler" "policy portfolio required"
        val owner = Input.owner_for expected block
        fun valid () =
          (validate_with_policy expected value;
           ignore (Input.owner_for expected block))
        val _ = valid ()
        val PolicyValidation {graph,scope,sources,assumptions,denied,...} =
          value
        val _ = if Portable.pointer_eq (graph,#graph owner) andalso
            G.scope_visible graph (#scope owner) scope then () else
          raise ERR "policy_assembler" "different graph or invisible scope"
        val originals = nodes sources
        val actual = Input.sources expected block
        (* Compare the actual ordered Source prefix, including duplicates.
           The returned int is an index into the admitted native vector;
           no policy ceiling or caller ordinal is narrowed to an int. *)
        fun prefix [] _ = ()
          | prefix (_::_) [] =
              raise ERR "policy_assembler" "original Source prefix absent"
          | prefix (wanted::rest) (held::tail) =
              (W.spend_policy expected 2;
               if wanted=held then prefix rest tail else
                 raise ERR "policy_assembler" "original Source prefix changed")
        val _ = prefix originals actual
        fun original index node =
          let fun seek [] _ _ =
                    raise ERR "policy_assembler" "original occurrence absent"
                | seek (held::rest) ordinal native =
                    (W.spend_policy expected 2;
                     if ordinal=(0:IntInf.int) then
                       if held=node then Input.source expected block native
                       else
                         raise ERR "policy_assembler" "Source endpoint changed"
                     else seek rest (ordinal-1) (native+1))
          in if index<0 then
               raise ERR "policy_assembler" "negative original occurrence"
             else seek originals index 0 end
        val built = ref ([]:(fact * Input.edge) list)
        fun saved _ [] = NONE
          | saved fact ((held,edge)::rest) =
              (W.spend_policy expected 1;
               if Portable.pointer_eq (fact,held) then SOME edge else
                 saved fact rest)
        fun rule opcode premises =
          Input.derive expected block opcode premises
        fun equality conversion =
          let val converted=Input.graph_assemble
                expected graph block conversion
          in rule P.EqualityMP
            [Input.constructor expected block
               (C.graph_equality conversion),converted] end
        fun truth () = Input.execute_inst expected
          (Input.prepare_inst expected block
            {substitution=[],theorem=boolTheory.TRUTH})
        fun build (fact as Fact {node,row,...}) =
          (valid ();W.spend_policy expected 2;
           ignore (Input.name expected block node);
           case saved fact (!built) of SOME edge => edge
           | NONE =>
             let val edge = case row of
                   Original (_,index) => original (IntInf.fromInt index) node
                 | PolicyOriginal (_,index,held) =>
                     if held=node then original index node else
                       raise ERR "policy_assembler" "Source endpoint changed"
                 | RecordedClosed plan => Input.closed expected block plan
                 | BinderTransport (conversion,source) =>
                     let val proof = build source
                         val _ = P.validate_conversion_for expected conversion
                         val equality = Input.conversion expected block
                           conversion
                     in rule P.EqualityMP [equality,proof] end
                 | Closed conversion =>
                     let val equation = rule P.Transitivity
                           [equality conversion,
                            Input.definition expected block
                              (C.graph_result conversion)]
                     in rule P.EqualityMP
                       [rule P.Symmetry [equation],truth ()] end
                 | Transport (conversion,source) => rule P.EqualityMP
                     [equality conversion,build source]
                 | Apply {law,premises} =>
                     Input.apply_law expected graph block
                       {law=(endpoint law,build law),target=node,
                        premises=List.map (fn premise =>
                          (endpoint premise,build premise)) premises}
                 val _ = valid ()
                 val _ = W.spend_policy expected 1
                 val _ = built := (fact,edge):: !built
             in edge end)
        fun query _ [] = NONE
          | query node (fact::rest) =
              (W.spend_policy expected 2;
               if endpoint fact=node then SOME fact else query node rest)
        val queries = assumptions @ [denied]
        fun assemble node =
          W.with_step expected (fn () =>
            (valid ();W.spend_policy expected 1;
             ignore (Input.name expected block node);
             let val result = Option.map build (query node queries)
                 val _ = valid ()
             in result end))
        val _ = valid ()
      in assemble end))
     handle primary => (W.close expected;raise primary))

end
