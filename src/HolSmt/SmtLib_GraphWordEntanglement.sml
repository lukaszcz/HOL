(* Copyright (c) 2026 The HOL4 contributors. *)
structure SmtLib_GraphWordEntanglement
  :> SmtLib_GraphWordEntanglement =
struct
  structure G = SmtReplayGraph
  val ERR = Feedback.mk_HOL_ERR "SmtLib_GraphWordEntanglement"
  type options =
    {graph : G.graph,scope : G.scope,dag_limit : int,type_limit : int}
  datatype inventory = Inventory of
    {graph : G.graph,scope : G.scope,complete : bool,entangled : bool,
     inspected_nodes : int,gaps : G.node list,frames : G.scope list}
  fun active (Inventory {graph,scope,frames,...}) =
    (G.validate_scope graph scope;List.app (G.validate_scope graph) frames)
  fun complete (value as Inventory {complete,...}) = (active value;complete)
  fun entangled (value as Inventory {entangled,...}) =
    (active value;entangled)
  fun inspected_nodes (value as Inventory {inspected_nodes,...}) =
    (active value;inspected_nodes)
  fun gaps (value as Inventory {gaps,...}) = (active value;gaps)
  type summary =
    {head_word : bool,length_head : bool,num_argument : bool,
     argument_word : bool,below : bool,known : bool}
  datatype work = Visit of G.scope * G.node
    | Finish of G.node * G.node * G.node
    | FinishBinder of G.node * G.node
  fun inspect ({graph,scope,dag_limit,type_limit} : options) roots =
    let
      val _ = G.validate_scope graph scope
      val _ = if dag_limit > 0 andalso type_limit > 0 then () else
        raise ERR "inspect" "nonpositive structural contract"
      val _ = List.app (fn node =>
        (ignore (G.type_of graph node);
         if G.scope_visible graph scope (G.node_scope graph node) then () else
           raise ERR "inspect" "root escapes active inventory owner")) roots
      val memo = ref (Redblackmap.mkDict Int.compare)
      val count = ref 0
      val found = ref false
      val missing = ref []
      val exhausted = ref false
      val frames = ref ([] : G.scope list)
      val temporary = ref ([] : G.scope list)
      fun close () = List.app (G.close_scope graph) (!temporary)
      fun get node : summary = Redblackmap.find (!memo,G.node_id node)
      fun put node value =
        memo := Redblackmap.insert (!memo,G.node_id node,value)
      fun word_type ty =
        let
          fun walk _ [] result = SOME result
            | walk 0 _ _ = NONE
            | walk fuel (ty :: rest) result =
                if Type.is_vartype ty then walk (fuel-1) rest result
                else
                  let val {Thy,Tyop,Args} = Type.dest_thy_type ty
                      val descend = case (Tyop,Args) of
                          ("fun",[domain,range]) => [domain,range]
                        | ("list",[element]) => [element]
                        | _ => []
                      val word = case (Thy,Tyop,Args) of
                          ("fcp","cart",[element,_]) =>
                            Type.compare (element,Type.bool) = EQUAL
                        | _ => false
                  in walk (fuel-1) (descend @ rest) (result orelse word)
                  end
        in walk type_limit [ty] false end
      fun numeric node = Type.compare (G.type_of graph node,numSyntax.num)
        = EQUAL
      fun mark node = missing := node :: !missing
      fun unknown node =
        (mark node;put node {head_word = false,length_head = false,
          num_argument = false,argument_word = false,below = false,
          known = false})
      fun leaf node length_head opaque =
        case word_type (G.type_of graph node) of NONE => unknown node
        | SOME word =>
          (if opaque then mark node else ();
           put node {head_word = word,length_head = length_head,
             num_argument = false,argument_word = false,
             below = word andalso not length_head,known = not opaque})
      fun owned_free active node =
        case G.free_variable_nodes graph node of NONE => NONE
        | SOME variables =>
            if List.all (fn variable => G.scope_visible graph active
                (G.node_scope graph variable)) variables then SOME variables
            else raise ERR "inspect" "binder captures a foreign free ID"
      (* Rehome may retain an abstraction's closed historical frame. Only a
         whole bounded admitted abstraction is re-admitted with its exact
         known free IDs. Owned temporary frames are closed on every exit. *)
      fun readmit active node =
        case owned_free active node of NONE => NONE | SOME variables =>
          let val maximum = if dag_limit >= 3 then (dag_limit-3) div 2 else 0
              fun bounded metric = case G.unfolded_nodes graph metric
                  maximum node of SOME count => count <= maximum | NONE => false
          in if maximum <= 0 orelse not (bounded G.RawNodes) orelse
              not (bounded G.BinderInclusiveNodes) then NONE else
            let val bindings = List.map (fn variable =>
                  (G.representative graph variable,variable)) variables
                val child = G.new_scope graph active bindings
                val _ = temporary := child :: !temporary
                val admitted = G.admit_binder graph child maximum
                  (G.representative graph node)
                val ids = G.free_variable_nodes graph (#node admitted)
                val _ = if Option.map (Listsort.sort Int.compare o
                    List.map G.node_id) ids = SOME (Listsort.sort Int.compare
                      (List.map G.node_id variables)) then () else
                  raise ERR "inspect" "bounded re-admission changed free IDs"
            in case G.view graph (#node admitted) of
                G.AdmittedBinder {body,frame,...} => SOME (body,frame)
              | _ => raise ERR "inspect" "bounded re-admission lost binder"
            end end
      fun original_frame frame = not (List.exists (fn owned =>
        G.scope_visible graph frame owned) (!temporary))
      fun loop [] = ()
        | loop (Visit (active,node) :: rest) =
            if not (G.scope_visible graph active (G.node_scope graph node))
            then raise ERR "inspect" "node escapes active binder owner"
            else if Option.isSome (Redblackmap.peek (!memo,G.node_id node)) then
              loop rest
            else if !count >= dag_limit then
              (exhausted := true;mark node)
            else
              let
                val _ = count := !count+1
                val _ = ignore (G.type_of graph node)
                val _ = if G.scope_visible graph active
                    (G.node_scope graph node) then () else
                  raise ERR "inspect" "node escapes active inventory owner"
              in case G.view graph node of
                  G.Application (operator,operand) =>
                    loop (Visit (active,operator) :: Visit (active,operand) ::
                      Finish (node,operator,operand) :: rest)
                | G.Constant _ =>
                    let val {Thy,Name,...} = Term.dest_thy_const
                          (G.representative graph node)
                    in leaf node (Thy = "list" andalso Name = "LENGTH")
                      false;loop rest end
                | G.Variable _ => (leaf node false false;loop rest)
                | G.OpaqueRetained => (leaf node false true;loop rest)
                | G.AdmittedBinder {binder,body,frame} =>
                    let
                      val _ = ignore (owned_free active node)
                      val live = Lib.can (G.validate_scope graph) frame
                      val parts = if live then
                          if G.scope_visible graph frame
                              (G.node_scope graph node) andalso
                              G.scope_visible graph frame
                                (G.node_scope graph binder)
                          then SOME (body,frame) else
                            raise ERR "inspect" "unowned admitted binder frame"
                        else readmit active node
                    in case parts of NONE =>
                        (unknown node;loop rest)
                      | SOME (body,frame) =>
                          let val body_scope = G.node_scope graph body
                              val local_scope = if G.scope_visible graph
                                  body_scope frame then body_scope else frame
                              val _ = if original_frame frame then
                                  frames := frame :: local_scope :: !frames
                                else ()
                          in loop (Visit (local_scope,body) ::
                            FinishBinder (node,body) :: rest) end
                    end
              end
        | loop (FinishBinder (node,body) :: rest) =
            (leaf node false (not (#known (get body)));loop rest)
        | loop (Finish (node,operator,operand) :: rest) =
            let
              val left = get operator
              val right = get operand
              val own_word = word_type (G.type_of graph node)
              val arguments = #argument_word left orelse #below right
              val numeric_arguments = #num_argument left orelse
                numeric operand
              val below = not (#length_head left) andalso
                (Option.getOpt (own_word,false) orelse arguments)
              val known = #known left andalso #known right andalso
                Option.isSome own_word
              val _ = if Option.isSome own_word then () else mark node
              val _ = if known andalso
                  ((numeric node andalso below) orelse
                   (#head_word left andalso numeric_arguments)) then
                found := true else ()
              val summary = {head_word = #head_word left,
                length_head = #length_head left,
                num_argument = numeric_arguments,argument_word = arguments,
                below = below,known = known}
            in put node summary;loop rest end
      val _ = (loop (List.map (fn node => Visit (scope,node)) roots)
        handle error => (close ();raise error))
      val _ = close ()
    in Inventory {graph = graph,scope = scope,
      complete = not (!exhausted) andalso null (!missing),
      entangled = !found,inspected_nodes = !count,gaps = List.rev (!missing),
      frames = !frames}
    end
end
