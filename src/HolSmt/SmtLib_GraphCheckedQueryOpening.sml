(* A current query changes only through genuine closed leaf/parent proofs. *)
structure SmtLib_GraphCheckedQueryOpening :>
    SmtLib_GraphCheckedQueryOpening =
struct
  structure G = SmtReplayGraph
  structure W = SmtReplayInvocationWork
  structure S = SmtReplaySource
  structure V = SmtLib_GraphSourcePortfolio
  structure Scope = SmtReplayOwnedScopeReceipt
  structure NC = SmtReplayNativeContract
  structure P = SmtReplayProof
  structure C = SmtReplayCanonGraph
  structure Core = SmtReplayOwnedLargeProofCore
  structure Opening = SmtLib_GraphCheckedOpening
  val ERR = Feedback.mk_HOL_ERR "SmtLib_GraphCheckedQueryOpening"
  type opening = {scope:G.scope,original:G.node,opened:G.node}
  type opened_query =
    {validation:V.validation,
     assumptions:{occurrence:IntInf.int,
       conversion:P.closed_conversion option} list,
     goal:P.closed_conversion option,denied:P.closed_conversion option}
  datatype row = Atom | Open of G.node | App of G.node * G.node
  type item = {node:G.node,row:row,changed:bool}
  datatype task = Visit of G.node | Join of G.node * G.node * G.node

  fun transport_internal finish work
      {validation,openings,native_contract,profiles,ordinal,check_type} =
    ((let
      (* The retained validation's passive expected-Work fence is first. *)
      val current = W.with_step work (fn () =>
        V.current_facts_with_policy_for work validation)
      val sources = W.original_sources work
      val graph = S.owning_graph sources val scope = S.owning_scope sources
      val frame = Scope.root_with_policy work
      val epoch = Type.type_epoch () val symbols = Term.term_epoch ()
      val _ = NC.validate_for work native_contract
      fun guard () =
        let val owner = Scope.description_with_policy_for work frame
            val _ = NC.validate_for work native_contract
        in if Portable.pointer_eq (#graph owner,graph) andalso
            #root owner=scope andalso #scope owner=scope andalso
            Portable.pointer_eq (#sources owner,sources) andalso
            Type.type_epoch ()=epoch andalso Term.term_epoch ()=symbols
          then () else raise ERR "transport" "original owner or epoch changed"
        end
      fun action compute = W.with_step work (fn () =>
        let fun observe () = (guard ();W.spend_policy work 1)
            val _ = guard () val result = compute observe
            val _ = guard ()
        in result end)
      fun node_key node =
        (guard ();ignore (G.closure_root graph scope node);G.node_id node)
      fun registered (original,opened) =
        let val _ = ignore (node_key original)
            val _ = ignore (node_key opened)
            val source = G.cached_opened_view graph scope original
            val _ = G.validate_opened_view graph scope original source
        in if #node source=opened then () else
          raise ERR "transport" "different registered opening endpoint" end
      val selected = action (fn observe =>
        let
          fun add ({scope=caller,original,opened}:opening,table) =
            let
              val _ = observe ()
              val _ = if caller=scope then () else
                raise ERR "transport" "opening is outside the query frame"
              val _ = registered (original,opened)
              val _ = case G.view graph original of
                  G.OpaqueRetained => ()
                | _ => raise ERR "transport" "selected opening is not opaque"
              val index = node_key original
              val _ = case Redblackmap.peek (table,index) of NONE => ()
                | SOME (saved,target) =>
                    if saved=original andalso target=opened then () else
                      raise ERR "transport" "different duplicate opening"
            in Redblackmap.insert (table,index,(original,opened)) end
        in List.foldl add (Redblackmap.mkDict Int.compare) openings end)
      val inventory = ref (Redblackmap.mkDict Int.compare :
        (int,item) Redblackmap.dict)
      fun lookup node = action (fn observe =>
        (observe ();case Redblackmap.peek (!inventory,node_key node) of
           NONE => NONE
         | SOME (saved:item) =>
             if #node saved=node then SOME saved else
               raise ERR "transport" "different inventory node identity"))
      fun saved node = case lookup node of SOME value => value
        | NONE => raise ERR "transport" "missing completed query child"
      fun save (value:item) = action (fn observe =>
        (observe ();inventory := Redblackmap.insert
          (!inventory,node_key (#node value),value)))
      fun scan [] = ()
        | scan (Visit node::rest) =
            (case lookup node of SOME _ => scan rest
             | NONE =>
               let
                 val syntax = action (fn observe =>
                   (observe ();G.view graph node))
               in case syntax of
                   G.Application (left,right) =>
                     scan (Visit left::Visit right::
                       Join (node,left,right)::rest)
                 | _ =>
                   let
                     val target = action (fn observe =>
                       (observe ();
                        case Redblackmap.peek (selected,node_key node) of
                          NONE => NONE
                        | SOME (original,opened) =>
                            (registered (original,opened);SOME opened)))
                     val value = case target of NONE =>
                           {node=node,row=Atom,changed=false}
                       | SOME opened =>
                           {node=node,row=Open opened,changed=node<>opened}
                   in save value;scan rest end
               end)
        | scan (Join (node,left,right)::rest) =
            let val a = saved left val b = saved right
                val _ = save {node=node,row=App (left,right),
                  changed= #changed a orelse #changed b}
            in scan rest end
      val assumption_nodes = List.map V.endpoint (#assumptions current)
      val goal = #goal current val denied = V.endpoint (#denied current)
      val roots = assumption_nodes @ [goal,denied]
      val _ = scan (List.map Visit roots)
      val proofs = ref (Redblackmap.mkDict Int.compare :
        (int,G.node * C.graph_conversion) Redblackmap.dict)
      fun proof node = action (fn observe =>
        (observe ();case Redblackmap.peek (!proofs,node_key node) of
           NONE => NONE
         | SOME (original,recipe) =>
             if original=node then
               (C.validate_conversion_for work recipe;SOME recipe)
             else raise ERR "transport" "different proof node identity"))
      fun completed node = case proof node of SOME recipe => recipe
        | NONE => raise ERR "transport" "missing completed child proof"
      fun publish node recipe = action (fn observe =>
        (observe ();C.validate_conversion_for work recipe;
         if C.graph_source recipe=node then () else
           raise ERR "transport" "child proof source differs";
         proofs := Redblackmap.insert
           (!proofs,node_key node,(node,recipe))))
      fun close recipe =
        let
          val _ = guard ()
          val actual_ordinal = action (fn observe =>
            (observe ();W.unused_policy_ordinal work
              {role=W.FinalFreeze,minimum=ordinal}))
          val result = Core.execute_with_policy work
            (Core.prepare_in_scope_with_policy work
              {frame=frame,conversion=recipe,ordinal=actual_ordinal,
               native_contract=native_contract,profiles=profiles,
               check_type=check_type})
          val actual = Core.conversion_description_with_policy_for work result
          val contract = Core.native_contract_with_policy_for work result
          val _ = if Portable.pointer_eq (contract,native_contract) andalso
              Portable.pointer_eq (#graph actual,graph) andalso
              Portable.pointer_eq (#sources actual,sources) andalso
              #root actual=scope andalso #scope actual=scope andalso
              #source actual=C.graph_source recipe andalso
              #target actual=C.graph_result recipe then () else
            raise ERR "transport" "different actual compact realization"
          val _ = guard ()
        in result end
      fun cut recipe =
        let val result = close recipe
            val fact = P.completed_policy_source_realization_closed_fact_for
              work
              (Core.realization_with_policy_for work result)
            val held = P.closed_fact_cut_with_policy_for work
              {frame=frame,fact=fact}
        in action (fn observe =>
          C.graph_closed_fact_cut_with_policy work
            {cut=held,observe=observe}) end
      (* Only changed Apps close on already closed child names. Retained
         subgraphs reuse the existing identity programme as one child;
         they acquire no new per-node native admission or opening. *)
      fun build [] = ()
        | build (Visit node::rest) =
            (case proof node of SOME _ => build rest
             | NONE =>
               let val item = saved node in
               if not (#changed item) then
                 (publish node (action (fn observe =>
                   C.graph_identity graph scope {observe=observe} node));
                  build rest)
               else (case #row item of
                  App (left,right) =>
                    build (Visit left::Visit right::
                      Join (node,left,right)::rest)
                | Atom =>
                    (publish node (action (fn observe =>
                      C.graph_identity graph scope {observe=observe} node));
                     build rest)
                | Open opened =>
                    let
                      val _ = registered (node,opened)
                      val conversion = Opening.bridge_with_policy work
                        {frame=frame,original=node,opened=opened,
                         native_contract=native_contract,profiles=profiles,
                         ordinal=ordinal,check_type=check_type}
                      val recipe = action (fn observe =>
                        C.graph_leaf_with_policy work
                          {frame=frame,conversion=conversion,observe=observe})
                      val _ = publish node recipe
                    in build rest end) end)
        | build (Join (node,left,right)::rest) =
            let val a = completed left val b = completed right
                val recipe = action (fn observe =>
                  C.graph_application graph scope
                    {source=node,left=a,right=b,observe=observe})
                val recipe = cut recipe
                val _ = publish node recipe
            in build rest end
      fun conversion node =
        if not (#changed (saved node)) then NONE else
          let val _ = build [Visit node]
              val recipe = completed node
              (* build closes every changed App on its actual child cuts;
                 an opened leaf already carries its checked conversion.
                 A sole exact root slot is the completed proof, not a new
                 native admission. Keep the established priced programme. *)
              val direct = if not (W.ordinary_policy_guard_mode work) then
                  NONE else action (fn observe =>
                    (observe ();
                     case C.graph_conversions_for work recipe of
                       [converted] =>
                         if P.conversion_source converted=node andalso
                             P.conversion_target converted=
                               C.graph_result recipe then
                           (W.validate_policy_ordinal_minimum work ordinal;
                            SOME converted)
                         else NONE
                     | _ => NONE))
              val converted = case direct of SOME converted => converted
                | NONE => Core.conversion_with_policy_for work
                    (close recipe)
              val _ = P.validate_conversion_for work converted
              val _ = if P.conversion_source converted=node then () else
                raise ERR "transport" "final proof source differs"
          in SOME converted end
      fun assumptions _ [] = []
        | assumptions index (node::rest) =
            let val converted = conversion node
                val _ = action (fn observe => observe ())
            in {occurrence=index,conversion=converted} ::
              assumptions (index+1:IntInf.int) rest end
      val selection = assumptions (0:IntInf.int) assumption_nodes
      val positive = conversion goal val negative = conversion denied
      val _ = guard ()
      val result = V.transport_query_with_policy work validation
        {assumptions=selection,goal=positive,denied=negative}
      val _ = guard ()
    in finish {validation=result,assumptions=selection,
      goal=positive,denied=negative} end)
     handle primary => (W.close work;raise primary))
  fun transport_with_policy work input =
    transport_internal (fn {validation,...}:opened_query => validation)
      work input
  fun transport_with_conversions_with_policy work input =
    transport_internal (fn result:opened_query => result) work input
end
