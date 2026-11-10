structure SmtLib_GraphOrderedConversionScoped :> SmtLib_GraphOrderedConversionScoped =
struct
  open SmtLib_GraphBinderConversionScoped SmtReplayGraph SmtReplayProof
    SmtReplayCanonGraph
  structure G = SmtReplayGraph
  structure P = SmtReplayProof
  structure B = SmtLib_GraphBinderConversionScoped
  val ERR = Feedback.mk_HOL_ERR "SmtLib_GraphOrderedConversionScoped"
  type pass =
    {name : string,propose : G.scope -> G.node ->
      SmtReplayCanonGraph.graph_schema option}
  type options =
    {graph : G.graph,scope : G.scope,admission : SmtReplayBinder.admission,
     template_limit : int,passes : pass list}
  datatype conversion = Conversion of
    {graph : G.graph,scope : G.scope,source : G.node,result : G.node,
     equality : G.node,passes : (string * B.conversion) list,
     witnesses : (G.node * Thm.thm) list}
  fun source (Conversion {source,...}) = source
  fun result (Conversion {result,...}) = result
  fun equality (Conversion {equality,...}) = equality
  fun witnesses (Conversion {witnesses,...}) = witnesses
  fun stages (Conversion {passes,...}) = List.map
    (fn (name,pass) => (name,B.source pass,B.result pass)) passes
  fun gaps (Conversion {passes,...}) =
    List.map (fn (name,pass) => (name,B.gaps pass)) passes
  fun roots (Conversion {source,result,equality,passes,...}) =
    source :: result :: equality ::
      List.concat (List.map (B.roots o #2) passes)
  fun equation graph scope left right =
    let
      val operator = G.constant graph scope (Term.inst
        (Type.match_type (Term.type_of boolSyntax.equality)
          (boolSyntax.list_mk_fun
            ([G.type_of graph left,G.type_of graph left],Type.bool)))
        boolSyntax.equality)
    in G.application graph scope
      (G.application graph scope (operator,left),right) end
  fun discover
      ({graph,scope,admission,template_limit,passes} : options) source =
    let
      val _ = G.validate_scope graph scope
      val _ = ignore (G.type_of graph source)
      val _ = if G.scope_visible graph scope (G.node_scope graph source)
        then () else raise ERR "discover" "source escapes active scope"
      val _ = if #input_limit admission > 0 andalso
          #output_limit admission > 0 andalso template_limit > 0 then () else
        raise ERR "discover" "nonpositive ordered conversion contract"
      fun run [] current completed = (current,List.rev completed)
        | run ({name,propose} :: rest) current completed =
            let val converted = B.discover
                  {graph = graph,scope = scope,admission = admission,
                   template_limit = template_limit,propose = propose} current
            in run rest (B.result converted)
              ((name,converted) :: completed) end
      val (result,completed) = run passes source []
      val equality = equation graph scope source result
      val table = ref (Redblackmap.mkDict Int.compare)
      val witnesses = ref []
      fun register (node,theorem) =
        if Option.isSome (Redblackmap.peek (!table,G.node_id node)) then ()
        else (table := Redblackmap.insert (!table,G.node_id node,());
              witnesses := (node,theorem) :: !witnesses)
      val _ = List.app (List.app register o B.witnesses o #2) completed
    in Conversion {graph = graph,scope = scope,source = source,
      result = result,equality = equality,passes = completed,
      witnesses = List.rev (!witnesses)} end
  fun assemble
      (Conversion {graph,scope,source,equality,passes,...}) block =
    let
      val _ = G.validate_scope graph scope
      (* All TRANS operands are compact equations in the same frozen block.
         Expanded sources enter only the caller's one final realization. *)
      val initial = P.checked block (Thm.REFL (P.name block source))
      fun append ((_,conversion),prefix) =
        let
          val edge = B.assemble conversion block
          val exposed = P.compose block
            (fn [proof,constructor] => Thm.EQ_MP constructor proof
              | _ => raise Fail "ordered conversion expose")
            [edge,P.constructor block (B.equality conversion)]
        in P.compose block
          (fn [previous,next] => Thm.TRANS previous next
            | _ => raise Fail "ordered conversion composition")
          [prefix,exposed] end
      val proof = List.foldl append initial passes
    in P.compose block
      (fn [proof,constructor] => Thm.EQ_MP (Thm.SYM constructor) proof
        | _ => raise Fail "ordered conversion anchor")
      [proof,P.constructor block equality] end
end
