(* Actual durable Mapping consumer above the low-level parser backend. *)
structure SmtLib_GraphParserMappingBackend :>
    SmtLib_GraphParserMappingBackend =
struct
  structure G = SmtReplayGraph
  structure W = SmtReplayInvocationWork
  structure M = SmtLib_GraphParserMapping
  structure PV = SmtLib_GraphParserValue
  structure B = SmtLib_GraphBackend
  structure Owned = SmtReplayOwnedParserValue
  val ERR = Feedback.mk_HOL_ERR "SmtLib_GraphParserMappingBackend"
  type value_backend =
    {backend:PV.value B.backend,context:PV.context,
     owner:Owned.owner,
     mapping_value:PV.value B.frame -> M.node_id -> PV.value,
     declarations:PV.value B.frame -> (M.declaration * PV.value) list,
     apply_declaration:PV.value B.frame -> M.declaration -> PV.value list ->
       PV.value,
     binding_origin_data:G.scope -> PV.value B.binding_origin ->
       {scope:G.scope,variables:PV.value list,
        descriptors:(string * string * Type.hol_type) list,binders:bool},
     close:unit -> unit}
  fun create work {graph,scope,mapping,import_limit,literal_limit,binder_limit}
      : value_backend =
    let
      val sources = W.original_sources work
      val limits = W.semantic_policy work
      fun owner () = W.validate_policy work graph scope sources limits
      fun guard () = (owner ();ignore (M.types mapping))
      val _ = owner ()
      val _ = M.validate_for graph scope mapping
      val parser_owner = SmtReplayOwnedParserValue.create work
        {graph=graph,scope=scope,validate_metadata=guard,
         import_limit=import_limit,literal_limit=literal_limit,
         binder_limit=binder_limit}
      val factory = Owned.factory_for work parser_owner
      val context = #context factory
      val backend = #backend factory
      fun step () = (guard ();PV.spend context 1)
      fun protect action = PV.protect context action
      fun descriptor value = B.variable_descriptor backend value
      fun compare_environment ((ls,lv),(rs,rv)) =
        case Int.compare (ls,rs) of EQUAL => Int.compare (lv,rv)
          | result => result
      fun compare_mapping ((ln,lf,le),(rn,rf,re)) =
        case Int.compare (ln,rn) of EQUAL =>
          (case Int.compare (lf,rf) of EQUAL =>
             List.collate compare_environment (le,re)
           | result => result)
        | result => result
      val memo = ref (Redblackmap.mkDict compare_mapping)
      fun mapped frame environment id =
        let
          val _ = step ()
          val current_scope = valOf (B.frame_scope backend frame)
          fun keys [] = []
            | keys ((slot,value)::rest) =
                (PV.spend context 1;
                 (slot,PV.key context value)::keys rest)
          val index = (id,G.scope_id current_scope,keys environment)
        in case Redblackmap.peek (!memo,index) of
            SOME value => (PV.usable context current_scope value;value)
          | NONE =>
              let
                val entry = M.entry mapping id
                val value = case #form entry of
                    M.ExistingGraph reference => PV.graph_leaf context
                      current_scope (M.reference_node mapping reference)
                  | M.Constant atom => B.literal backend frame atom
                  | M.FreeVariable fields =>
                      PV.mapped_variable context current_scope fields
                  | M.BoundSlot slot =>
                      (case List.find (fn (held,_) => held=slot) environment of
                         SOME (_,value) => value
                       | NONE => raise ERR "mapping" "unbound mapping slot")
                  | M.Application (function,argument) =>
                      B.application backend frame
                        (mapped frame environment function,
                         mapped frame environment argument)
                  | M.Abstraction {slot,lexical,body} =>
                      let val (name,ty) = Term.dest_var lexical
                          val key = "__mapping_slot_" ^ Int.toString slot
                      in B.abstraction backend frame (key,name,ty) (fn child =>
                        let val binder = valOf (B.lookup backend child key)
                        in mapped child ((slot,binder)::environment) body end)
                      end
                val _ = if Type.compare
                    (PV.type_of context value,#hol_type entry)=EQUAL then ()
                  else raise ERR "mapping" "interpreted type differs"
                val _ = PV.usable context current_scope value
                val _ = memo := Redblackmap.insert (!memo,index,value)
              in value end
        end
      fun mapping_value frame id = protect (fn () => mapped frame [] id)
      fun declarations frame = protect (fn () =>
        let
          val _ = step ()
          fun copy [] = []
            | copy ((declaration:M.declaration)::rest) =
                (PV.spend context 1;
                 (declaration,mapping_value frame (#value declaration)) ::
                   copy rest)
        in copy (M.declarations mapping) end)
      fun apply_declaration frame (declaration:M.declaration) arguments =
        protect (fn () =>
          let val original = mapping_value frame (#value declaration)
              val value = case descriptor original of SOME lexical =>
                    B.reference backend frame (lexical,original)
                  | NONE => original
              val count = length arguments
              val accepted = case #arity declaration of
                  M.Exact expected => count=expected
                | M.AtMost maximum => count<=maximum
              val _ = if accepted orelse value<>original then () else
                raise ERR "mapping" "wrong declaration argument count"
          in case (#selector_body declaration,value=original,arguments) of
              (SOME (slot,body),true,[argument]) =>
                let val current_scope = valOf (B.frame_scope backend frame)
                    val (domain,_) = Type.dom_rng (#hol_type declaration)
                    val _ = PV.usable context current_scope argument
                    val _ = if Type.compare
                        (PV.type_of context argument,domain)=EQUAL then ()
                      else raise ERR "mapping" "selector argument type differs"
                in mapped frame [(slot,argument)] body end
            | _ => List.foldl (fn (argument,function) =>
                B.application backend frame (function,argument)) value arguments
          end)
    in {backend=backend,context=context,owner=parser_owner,
      mapping_value=mapping_value,
      declarations=declarations,apply_declaration=apply_declaration,
      binding_origin_data= #binding_origin_data factory,
      close=fn () => Owned.close parser_owner} end
    handle primary => (W.close work;raise primary)
end
