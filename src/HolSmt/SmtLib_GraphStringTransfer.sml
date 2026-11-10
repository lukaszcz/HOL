structure SmtLib_GraphStringTransfer :> SmtLib_GraphStringTransfer =
struct
  open SmtReplayGraph SmtReplayCanonGraph SmtReplayImport
    SmtLib_GraphFrontend SmtLib_GraphBackend SmtLib_GraphPreprocessFacts
    SmtLib_GraphPreprocessDerived SmtLib_Theories smtstringTheory
  structure G = SmtReplayGraph
  structure C = SmtReplayCanonGraph
  structure B = SmtLib_GraphBackend
  structure F = SmtLib_GraphPreprocessFacts
  structure D = SmtLib_GraphPreprocessDerived
  val ERR = Feedback.mk_HOL_ERR "SmtLib_GraphStringTransfer"
  type alias =
    {image : G.node,operand : G.node,free_variables : G.node list}
  type producer =
    {propose : G.node -> C.graph_schema option,aliases : unit -> alias list,
     install_aliases : SmtLib_GraphFrontend.session ->
       (string * G.node) list -> unit,
     character_bound : G.node -> {fact : F.fact,target : G.node},
     substring_after_end : {string : G.node,start : G.node,length : G.node} ->
       {rule : D.rule,premise : G.node,target : G.node}}
  fun create graph scope {template_limit,prefix_depth,check_type} : producer =
    let
      val _ = G.validate_scope graph scope
      val _ = if template_limit > 4 andalso prefix_depth > 0 then () else
        raise ERR "create" "nonpositive or insufficient string schema contract"
      fun bounded limit term =
        case SmtReplayImport.bounded_raw_size limit term of SOME _ => ()
        | NONE => raise ERR "schema" "expanded string schema"
      val laws = [smtstringTheory.str_inj_11,smtstringTheory.str_inj_STRCAT,
        smtstringTheory.str_inj_isPREFIX,smtstringTheory.str_inj_string_lt,
        smtstringTheory.str_inj_string_le]
      val _ = List.app (bounded template_limit o Thm.concl) laws
      val rules = Conv.GSYM (hd laws) :: tl laws
      val auxiliary = [smtstringTheory.ORD_unicode_bound,
        smtstringTheory.smtstr_substr_empty_start]
      (* Equality-to-true adds exactly four raw nodes. Admit that whole
         prospective schema before SPEC_ALL or any local law destructor. *)
      val _ = List.app (bounded (template_limit-4) o Thm.concl) auxiliary
      val char_law = Drule.SPEC_ALL (hd auxiliary)
      val substring_law = Drule.SPEC_ALL (List.nth (auxiliary,1))
      val _ = List.app (bounded (template_limit-4) o Thm.concl)
        [char_law,substring_law]
      val intro = Term.prim_mk_const {Thy = "smtstring",Name = "str_inj"}
      val substring = Term.prim_mk_const
        {Thy = "smtstring",Name = "smtstr_substr"}
      val types = ref (Redblackset.empty Int.compare)
      val images = ref (Redblackmap.mkDict Int.compare)
      fun active () = G.validate_scope graph scope
      fun admit node =
        let
          val _ = active ()
          (* Ownership is checked before consulting the numeric type cache. *)
          val ty = G.type_of graph node
          val _ = if G.scope_visible graph scope (G.node_scope graph node)
            then () else raise ERR "admit" "string operand escapes scope"
          val id = G.type_id graph node
        in if Redblackset.member (!types,id) then () else
          (check_type ty;types := Redblackset.add (!types,id)) end
      fun term_types [] = ()
        | term_types (term :: pending) =
            (check_type (Term.type_of term);
             if Term.is_comb term then
               let val (operator,operand) = Term.dest_comb term in
                 term_types (operator :: operand :: pending) end
             else if Term.is_abs term then
               raise ERR "schema" "string binder transfer unsupported"
             else term_types pending)
      fun conversion term =
        let
          (* Each transfer adds at most two injection applications per
             rewritten binary observer/equality. Result size is at most
             three times input; the complete equality adds three nodes. *)
          val _ = bounded ((template_limit-3) div 4) term
          val _ = term_types [term]
          val result = Rewrite.PURE_REWRITE_CONV rules term
          val _ = bounded template_limit (Thm.concl result)
          val _ = term_types [Thm.concl result]
        in result end
      fun remember node = case G.view graph node of
          G.Application (operator,operand) =>
            (case G.view graph operator of G.Constant _ =>
               if Term.same_const (G.representative graph operator) intro then
                 let
                   val variables = case G.free_variable_nodes graph node of
                       SOME variables => variables
                     | NONE => raise ERR "alias" "unknown string image IDs"
                   val _ = List.app (fn variable =>
                     if G.scope_visible graph scope
                         (G.node_scope graph variable) then () else
                       raise ERR "alias" "string image free ID escapes")
                     variables
                 in images := Redblackmap.insert (!images,G.node_id node,
                   {image = node,operand = operand,free_variables = variables})
                 end
               else ()
             | _ => ())
        | _ => ()
      fun propose node =
        let
          val _ = admit node
          val _ = List.app admit (G.block_reachable graph [node])
          val result = case G.view graph node of
              G.OpaqueRetained => NONE | G.AdmittedBinder _ => NONE
            | _ => C.graph_schema_conversion graph scope
                {conversion = conversion,template_limit = template_limit,
                 prefix_depth = prefix_depth} node
          val _ = case result of NONE => () | SOME schema =>
            let val output = C.graph_schema_result schema
                val reached = G.block_reachable graph [output]
                val _ = List.app admit reached
            in List.app remember reached end
        in result end
      fun aliases () =
        (active ();List.map #2 (Redblackmap.listItems (!images)))
      fun install_aliases (session : SmtLib_GraphFrontend.session) entries =
        let
          val _ = active ()
          val backend = #backend (#reader session)
          val _ = G.validate_scope graph (#scope (#reader session))
          fun install (token,image) =
            let
              val _ = admit image
              val ty = G.type_of graph image
              val _ = case Redblackmap.peek (!images,G.node_id image) of
                  SOME {image = owned,...} => if image = owned then () else
                    raise ERR "alias" "string image identity changed"
                | NONE => raise ERR "alias" "unrecorded string image"
              fun parse frame _ indices arguments =
                if not (null indices andalso null arguments) then
                  SmtLib_Theories.decline "string image"
                    "nullary alias required"
                else let val active = valOf (B.frame_scope backend frame) in
                  if G.scope_visible graph active (G.node_scope graph image)
                  then image else raise ERR "alias" "image escapes reader scope"
                end
            in (#add_source_parser session) (token,ty,parse) end
        in List.app install entries end
      fun named_arguments theorem =
        (bounded (template_limit-4) (Thm.concl theorem);
         Term.free_vars (Thm.concl theorem))
      fun character_bound operand =
        let
          val _ = admit operand
          val _ = if Type.compare (G.type_of graph operand,
              stringSyntax.char_ty) = EQUAL then () else
            raise ERR "character_bound" "operand is not a native HOL char"
          val holes = named_arguments char_law
          val _ = if List.length holes = 1 then () else
            raise ERR "character_bound" "changed authoritative char schema"
          val schema = C.checked_graph_schema graph scope
            {theorem = Drule.EQT_INTRO char_law,holes = holes,
             operands = [operand],template_limit = template_limit}
          val fact = F.checked_fact graph scope
            {theorem = char_law,holes = holes,operands = [operand],
             template_limit = template_limit}
        in {fact = fact,target = C.graph_schema_source schema} end
      fun substring_after_end {string,start,length} =
        let
          val _ = List.app admit [string,start,length]
          val (_,target_term) = boolSyntax.dest_imp (Thm.concl substring_law)
          val (head,holes) = boolSyntax.strip_comb
            (#1 (boolSyntax.dest_eq target_term))
          val _ = if Term.same_const head substring andalso
              List.length holes = 3 andalso List.all Term.is_var holes then ()
            else raise ERR "substring_after_end" "changed substring schema"
          val schema = C.checked_graph_schema graph scope
            {theorem = Drule.EQT_INTRO substring_law,holes = holes,
             operands = [string,start,length],template_limit = template_limit}
          val law = C.graph_schema_source schema
          val (premise,target) = case G.view graph law of
              G.Application (left,target) => (case G.view graph left of
                G.Application (operator,premise) =>
                  if Term.same_const (G.representative graph operator)
                    boolSyntax.implication then (premise,target) else
                      raise ERR "substring_after_end" "nonimplication schema"
              | _ => raise ERR "substring_after_end" "malformed implication")
            | _ => raise ERR "substring_after_end" "malformed implication"
          val rule = D.checked_rule graph scope
            {theorem = substring_law,holes = holes,
             operands = [string,start,length],premises = [premise],
             target = target,template_limit = template_limit}
        in {rule = rule,premise = premise,target = target} end
    in {propose = propose,aliases = aliases,install_aliases = install_aliases,
        character_bound = character_bound,
        substring_after_end = substring_after_end} end
end
