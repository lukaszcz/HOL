(* Copyright (c) 2026 The HOL4 contributors. *)
structure SmtLib_GraphDeclarationMetadata :> SmtLib_GraphDeclarationMetadata =
struct
  structure Q = SmtLib_GraphQueryAnalysis
  structure M = SmtLib_GraphParserMapping
  structure S = SmtLib_GraphCarrierStore
  val ERR = Feedback.mk_HOL_ERR "SmtLib_GraphDeclarationMetadata"
  type term_declaration =
    {symbol:M.declaration,domain_sorts:string list,range_sort:string,
     declaration:string}
  type encoding =
    {input:M.node_id,head:M.node_id,atomic_head:Term.term option,
     smt_symbol:string,arity:int}
  type definition =
    {encoding:encoding,replay_head:Term.term,unfolding:Thm.thm}
  type assertion = {scope:SmtReplayGraph.scope,node:SmtReplayGraph.node,
    syntax:M.node_id}
  type held_assertion = {scope:SmtReplayGraph.scope,node:SmtReplayGraph.node,
    syntax:M.node_id,child:SmtReplayGraph.closure_child}
  datatype metadata = Metadata of
    {mapping:M.mapping,type_records:SmtLib.translation_record list,
     term_declarations:term_declaration list,encodings:encoding list,
     definitions:definition list,graph:SmtReplayGraph.graph,
     scope:SmtReplayGraph.scope,assertions:held_assertion list option}
  fun validate (Metadata {mapping,...}) = M.validate mapping
  fun mapping (value as Metadata {mapping,...}) = (validate value;mapping)
  fun mapping_for graph scope (Metadata {mapping,...}) =
    (M.validate_for graph scope mapping;mapping)
  fun type_records (value as Metadata {type_records,...}) =
    (validate value;type_records)
  fun term_declarations (value as Metadata {term_declarations,...}) =
    (validate value;term_declarations)
  fun encodings (value as Metadata {encodings,...}) =
    (validate value;encodings)
  fun definitions (value as Metadata {definitions,...}) =
    (validate value;definitions)

  fun assertion_header graph scope (Metadata {graph=held,scope=root,...}) =
    if Portable.pointer_eq(graph,held) andalso scope=root then () else
      raise ERR "assertions" "different expected graph or root"
  fun has_assertions_for graph scope (saved as Metadata {assertions,...}) =
    (assertion_header graph scope saved;Option.isSome assertions)
  fun assertions_for graph scope {assumptions,denied,observe}
      (saved as Metadata {mapping,assertions,...}) =
    let
      val _=assertion_header graph scope saved
      fun tick()=(assertion_header graph scope saved;observe();
        assertion_header graph scope saved)
      fun same node ({scope=caller,node=held,...}:held_assertion)=
        (tick();if caller=scope andalso(tick();held=node)then ()else
          raise ERR "assertions" "different ordered current query roots")
      fun roots [] [last]=(same denied last;tick())
        | roots(node::rest)(row::more)=(same node row;roots rest more)
        | roots _ _=raise ERR "assertions" "current assertion count changed"
      fun copy []=(tick();[])
        | copy(({scope=caller,node,syntax,child}:held_assertion)::rest)=
            let val _=tick()
                val _=if SmtReplayGraph.closure_child_node graph caller child
                    =node then ()else raise ERR "assertions"
                      "retained assertion endpoint changed"
                val _=tick()val _=tick()
            in ({scope=caller,node=node,syntax=syntax}:assertion)
              ::copy rest end
    in case assertions of NONE=>NONE|SOME held=>
      (roots assumptions held;M.validate_for graph scope mapping;
       tick();SOME(copy held))end

  fun freeze_using retain (context:Q.outbound_context)
      {graph,scope,regime,backend,operations,emission} =
    let
      val backend : SmtLib.outbound_backend_context = backend
      val operations : Q.carrier
          SmtLib.outbound_term_translation_operations = operations
      val {types,symbols,encodings=events,...} :
          SmtLib_GraphDispatcher.result = emission
      fun live () =
        (ignore ((#key context) (#goal context));
         ignore ((#snapshot backend) ()))
      fun guard current = ignore ((#key context) current)
      val _ = live ()
      fun inputs ({input,head,atomic_head,arity,...}:S.encoding) =
        let
          val _ = guard input val _ = guard head
          val (actual,_) = (#strip_comb context) input
          val _ = if (#key context) actual=(#key context) head then () else
            raise ERR "freeze" "encoding head does not match its input"
          val observed = case (#view context) head of
              Q.ConstantView atom => SOME atom
            | Q.VariableView (_,atom) => SOME atom | _ => NONE
          val same = case (atomic_head,observed) of
              (NONE,NONE) => true
            | (SOME left,SOME right) => Term.aconv left right
            | _ => false
          val _ = if same andalso arity>=0 then () else
            raise ERR "freeze" "encoding atomic metadata mismatch"
          val _ = (#step context) ()
        in [input,head] end
      val additional = List.concat (List.map inputs events)
      fun tick()=(live();(#step context)();live())
      fun append [] tail=(tick();tail)
        | append(value::rest)tail=(tick();tick();value::append rest tail)
      val assertion_inputs=if retain then
          (tick();tick();tick();tick();
           SOME(append(#assumptions context)[#denied context]))else NONE
      val additional=case assertion_inputs of NONE=>additional
        | SOME roots=>append additional roots
      val {mapping,inputs=ids} = M.freeze_with_inputs context
        {graph=graph,scope=scope,regime=regime,types=types,symbols=symbols,
         inputs=additional}
      fun attach ([],[]) = []
        | attach (({atomic_head,smt_symbol,arity,...}:S.encoding)::rest,
            input::head::ids) =
            ({input=input,head=head,atomic_head=atomic_head,
              smt_symbol=smt_symbol,arity=arity}:encoding) :: attach (rest,ids)
        | attach _ = raise ERR "freeze" "encoding input count changed"
      fun split [] remaining=(tick();tick();([],remaining))
        | split(_::rest)(input::head::remaining)=
            let val _=tick()val _=tick()
                val(encoded_tail,after)=split rest remaining
                val _=tick()val _=tick()val _=tick()
            in(input::head::encoded_tail,after)end
        | split _ _=raise ERR "freeze" "encoding input count changed"
      val(encodings,assertion_ids)=case assertion_inputs of
          NONE=>(attach(events,ids),NONE)
        | SOME roots=>let val(encoded,remaining)=split events ids
          in tick();tick();tick();
            (attach(events,encoded),SOME(roots,remaining))end
      fun hold([],[])=(tick();[])
        | hold(current::rest,id::more)=
            let val _=guard current val _=tick()
                val{scope=caller,node}=case(#graph_node context)current of
                    SOME actual=>actual|NONE=>raise ERR "freeze"
                      "assertion is not authentic graph syntax"
                val child=SmtReplayGraph.closure_root graph caller node
                val _=tick()val _=tick()
            in({scope=caller,node=node,syntax=id,child=child}:held_assertion)
              ::hold(rest,more)end
        | hold _=raise ERR "freeze" "assertion input count changed"
      val assertions=case assertion_ids of NONE=>NONE
        | SOME roots=>(tick();SOME(hold roots))
      fun declaration ((symbol:S.symbol),(value:M.declaration)) =
        let
          val _ = guard (#syntax symbol)
          val description = SmtLib.outbound_term_declaration_metadata
            {type_of= #type_of context,
             is_injected_string= #is_injected_string operations,
             is_injected_float= #is_injected_float operations,
             recorded_sorts=fn _ => #sorts symbol,
             sort_of_type=(#sort_of_type backend) regime types}
            regime ((#syntax symbol,#arity symbol),#name symbol)
          val _ = (#step context) ()
          val _ = guard (#syntax symbol)
        in {symbol=value,domain_sorts= #domain_sorts description,
          range_sort= #range_sort description,
          declaration= #declaration description}:term_declaration end
      val declarations = ListPair.mapEq declaration
        (symbols,M.declarations mapping)
      fun declaration_text document =
        let val chunks = ref []
            fun keep chunk = ((#step context) ();chunks := chunk :: !chunks)
            val _ = SmtLib_OutputFragments.render keep document
        in String.concat (List.rev (!chunks)) end
      val type_records = (#type_declaration_records backend) types
        (List.concat (List.map
          (fn ({declarations,...}:SmtLib_GraphDispatcher.root) =>
            List.map declaration_text declarations) (#roots emission)))
      fun definition (encoding:encoding) =
        case #atomic_head encoding of NONE => NONE | SOME atom =>
          if not (Term.is_const atom) then NONE else Option.map
            (fn SmtLib.EmittedDefinition {replay_head,unfolding,...} =>
              {encoding=encoding,replay_head=replay_head,
               unfolding=unfolding}:definition)
            (SmtLib.definition_for_record (SmtLib.EncodedSymbol
              {hol_term=atom,smt_symbol= #smt_symbol encoding,
               arity= #arity encoding}))
      val definitions = List.mapPartial definition encodings
      val _ = live ()
      val result = Metadata {mapping=mapping,type_records=type_records,
        term_declarations=declarations,encodings=encodings,
        definitions=definitions,graph=graph,scope=scope,
        assertions=assertions}
      val _ = validate result
    in result end
  fun freeze context options=freeze_using false context options
  fun freeze_with_assertions context options=freeze_using true context options
end
