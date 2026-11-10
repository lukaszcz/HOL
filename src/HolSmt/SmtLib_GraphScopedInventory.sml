structure SmtLib_GraphScopedInventory :> SmtLib_GraphScopedInventory =
struct
  open SmtReplayGraph SmtReplayBinder SmtLib_GraphFrontend
    SmtLib_GraphBackend SmtReplayImport
  structure G = SmtReplayGraph
  structure F = SmtLib_GraphFrontend
  structure K = SmtLib_GraphBackend
  val ERR = Feedback.mk_HOL_ERR "SmtLib_GraphScopedInventory"
  datatype kind = Natural | NativeFloat | String
  datatype entry = Entry of
    {image : G.node,operands : G.node list,kind : kind,
     scope : G.scope,free : G.node list option}
  datatype packet = Packet of
    {source : G.node,target : G.node,bound : G.node,
     source_bound : G.node option,body : G.node,
     scope : G.scope,temporary : G.scope,variables : G.node list,
     theorem : Thm.thm}
  datatype classification =
      RootAlias of {image : G.node,bridge : Thm.thm}
    | TargetPacket of packet
    | Unresolved of string
  type completion =
    {source : G.node,target : G.node,temporary : G.scope,body_scope : G.scope,
     theorem : Thm.thm}
  datatype inventory = Inventory of
    {graph : G.graph,scope : G.scope,admission : SmtReplayBinder.admission,
     active : bool ref,entries : (int,entry) Redblackmap.dict ref,
     packets : packet list ref}
  fun image (Entry {image,...}) = image
  fun operands (Entry {operands,...}) = operands
  fun entry_kind (Entry {kind,...}) = kind
  fun packet_target (Packet {target,...}) = target
  fun packet_source (Packet {source,...}) = source
  fun packet_bound (Packet {bound,...}) = bound
  fun packet_source_bound (Packet {source_bound,...}) = source_bound
  fun packet_scope (Packet {scope,...}) = scope
  fun packet_variables (Packet {variables,...}) = variables
  fun packet_bridge (Packet {theorem,...}) = theorem
  fun live (Inventory {graph,scope,active,...}) =
    (if !active then () else raise ERR "live" "inventory is closed";
     G.validate_scope graph scope)
  fun create graph scope (admission : SmtReplayBinder.admission) =
    (G.validate_scope graph scope;
     if #input_limit admission > 0 andalso #output_limit admission > 0 then ()
     else raise ERR "create" "nonpositive whole-law contract";
     Inventory {graph = graph,scope = scope,admission = admission,
       active = ref true,entries = ref (Redblackmap.mkDict Int.compare),
       packets = ref []})
  fun visible graph scope node =
    (ignore (G.type_of graph node);
     if G.scope_visible graph scope (G.node_scope graph node) then () else
       raise ERR "visible" "node escapes its active owner")
  fun capture (inventory as Inventory {graph,entries,...}) scope kind
      {image,operands = actual_operands} =
    let val _ = live inventory
        val _ = G.validate_scope graph scope
        val _ = List.app (visible graph scope) (image :: actual_operands)
        val free = G.free_variable_nodes graph image
        val _ = Option.app (List.app (visible graph scope)) free
        val entry = Entry {image = image,operands = actual_operands,kind = kind,
          scope = scope,free = free}
    in case Redblackmap.peek (!entries,G.node_id image) of NONE =>
        entries := Redblackmap.insert (!entries,G.node_id image,entry)
      | SOME previous => if entry_kind previous = kind andalso
          operands previous = actual_operands then ()
        else raise ERR "capture" "conflicting exact image inventory" end
  fun completed
      (inventory as Inventory {graph,scope = owner,admission,packets,...})
      ({source,target,temporary,body_scope,theorem} : completion) =
    let
      val _ = live inventory
      val _ = G.validate_scope graph temporary
      val _ = G.validate_scope graph body_scope
      val _ = if temporary <> owner andalso
          G.scope_visible graph temporary owner andalso
          G.scope_visible graph body_scope temporary then () else
        raise ERR "completed" "temporary frame has no owned lifetime"
      val limit = #output_limit admission
      val actual = Thm.concl theorem
      val count = case #metric admission of G.RawNodes =>
          SmtReplayImport.bounded_raw_size limit actual
        | G.BinderInclusiveNodes =>
            SmtReplayImport.bounded_binder_size limit actual
      val _ = case count of SOME _ => () | NONE =>
        raise ERR "completed" "whole packet bridge exceeds quota"
      val (left,right) = boolSyntax.dest_eq actual
      val _ = if Portable.pointer_eq (left,G.representative graph source)
          andalso Portable.pointer_eq (right,G.representative graph target)
          andalso null (Thm.hyp theorem) then () else
        raise ERR "completed" "packet bridge lost exact Source endpoints"
      val (tags,_) = Tag.dest_tag (Thm.tag theorem)
      val _ = if List.all (fn tag => tag = "DISK_THM") tags andalso
          null (Tag.axioms_of (Thm.tag theorem)) then () else
        raise ERR "completed" "packet bridge has untrusted tags"
      val (bound,body) = case G.view graph target of
          G.AdmittedBinder {binder,body,...} => (binder,body)
        | _ => raise ERR "completed" "packet target is not an owned binder"
      val _ = List.app (visible graph body_scope) [bound,body]
      val ancestors = case G.free_variable_nodes graph target of SOME nodes =>
          nodes | NONE => raise ERR "completed" "unknown target binder free IDs"
      val _ = List.app (visible graph body_scope) ancestors
      val source_bound = case G.view graph source of
          G.AdmittedBinder {binder,...} => SOME binder | _ => NONE
      val packet = Packet {source = source,target = target,bound = bound,
        source_bound = source_bound,
        body = body,scope = body_scope,temporary = temporary,
        variables = bound :: ancestors,theorem = theorem}
    in packets := packet :: !packets end
  fun contains graph root needle =
    List.exists (fn node => node = needle) (G.reachable graph [root])
  fun classify (inventory as Inventory {graph,scope,entries,packets,...})
      roots =
    let
      val _ = live inventory
      val _ = List.app (visible graph scope) roots
      val reachable = G.reachable graph roots
      fun occurs node = List.exists (fn seen => seen = node) reachable
      fun one (entry as Entry {image,free,scope = owner,...}) =
        let val classification = case free of NONE =>
              Unresolved "unknown exact image free-ID metadata"
            | SOME variables =>
                if not (occurs image) then
                  Unresolved "image not in authoritative final output"
                else if List.all (fn node => G.scope_visible graph scope
                    (G.node_scope graph node)) variables then
                  let val _ = G.validate_scope graph owner
                      val moved = G.rehome graph scope image
                  in RootAlias {image = #node moved,bridge = #bridge moved} end
                else case List.find (fn Packet
                    {target,body,scope = local_scope,...} =>
                    occurs target andalso contains graph body image andalso
                    G.scope_visible graph local_scope (G.node_scope graph image)
                    andalso List.all (fn node => G.scope_visible graph
                      local_scope (G.node_scope graph node)) variables)
                    (!packets) of
                  SOME packet => TargetPacket packet
                | NONE => Unresolved "no checked target binder transport"
        in (entry,classification) end
    in List.map (one o #2) (Redblackmap.listItems (!entries)) end
  fun install_packet (inventory as Inventory {graph,...})
      (packet as Packet {target,bound,body,scope,...}) (session : F.session)
      {variables,aliases} =
    let
      val _ = live inventory
      val _ = G.validate_scope graph scope
      val reader = #reader session
      val _ = if G.root_scope (#graph reader) = G.root_scope graph andalso
          #scope reader = scope then ()
        else raise ERR "install_packet" "reader is not the exact target frame"
      val backend = #backend reader
      fun install (token,node) =
        let
          val _ = visible graph scope node
          fun parse frame _ indices arguments =
            if not (null indices andalso null arguments) then
              raise ERR "parse" "packet declaration is nullary"
            else let val current = valOf (K.frame_scope backend frame)
                     val _ = visible graph current node
                 in node end
        in #add_source_parser session (token,G.type_of graph node,parse) end
      val _ = case G.view graph target of G.AdmittedBinder {binder,...} =>
          if binder = bound then () else
            raise ERR "install_packet" "target Bound ID changed"
        | _ => raise ERR "install_packet" "target binder disappeared"
      val _ = List.app (fn (_,entry) =>
        if contains graph body (image entry) then () else
          raise ERR "install_packet" "alias lacks target body provenance")
        aliases
      val supplied = Listsort.sort Int.compare
        (List.map (G.node_id o #2) variables)
      val expected = Listsort.sort Int.compare
        (List.map G.node_id (packet_variables packet))
      val _ = if supplied = expected then () else
        raise ERR "install_packet" "incomplete exact owned declaration IDs"
      val tokens = List.map #1 variables @ List.map #1 aliases
      val normalized = List.map (#symbol_key session) tokens
      val _ = if List.length (HOLset.listItems
          (HOLset.addList (HOLset.empty String.compare,normalized))) =
          List.length tokens then () else
        raise ERR "install_packet" "duplicate typed packet declaration token"
      val _ = List.app install variables
    in List.app (fn (token,entry) => install (token,image entry)) aliases end
  fun close (Inventory {graph,active,packets,...}) =
    if not (!active) then () else
      (active := false;
       List.app (fn Packet {temporary,...} =>
         G.close_scope graph temporary) (!packets))
end
