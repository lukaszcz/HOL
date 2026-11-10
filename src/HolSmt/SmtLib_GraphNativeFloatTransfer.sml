structure SmtLib_GraphNativeFloatTransfer :> SmtLib_GraphNativeFloatTransfer =
struct
  open SmtReplayGraph SmtReplayCanonGraph SmtLib smtfloatTheory
    SmtLib_GraphFrontend SmtLib_GraphBackend
  structure G = SmtReplayGraph
  structure C = SmtReplayCanonGraph
  structure B = SmtLib_GraphBackend
  val ERR = Feedback.mk_HOL_ERR "SmtLib_GraphNativeFloatTransfer"
  type alias =
    {image : G.node, operands : G.node list,free_variables : G.node list}
  type producer =
    {propose : G.node -> C.graph_schema option,aliases : unit -> alias list,
     install_aliases : SmtLib_GraphFrontend.session ->
       (string * G.node) list -> unit}
  (* Deliberately exclude quantified and guarded transfer theorems.
     Their assumptions cannot become unchecked preprocessing sources. *)
  val laws = [smtfloatTheory.native_float_bits_transfer,
    smtfloatTheory.native_float_special_transfer,
    smtfloatTheory.native_float_classification_transfer,
    smtfloatTheory.native_float_finite_integral_transfer,
    smtfloatTheory.native_float_signalling_transfer,
    smtfloatTheory.native_float_sign_transfer,
    smtfloatTheory.native_float_abs_transfer,
    smtfloatTheory.native_float_neg_transfer,
    smtfloatTheory.native_float_comparison_transfer,
    smtfloatTheory.native_float_add_transfer,
    smtfloatTheory.native_float_sub_transfer,
    smtfloatTheory.native_float_mul_transfer,
    smtfloatTheory.native_float_div_transfer,
    smtfloatTheory.native_float_sqrt_transfer,
    smtfloatTheory.native_float_fma_transfer,
    smtfloatTheory.native_float_word_conversion_transfer,
    smtfloatTheory.native_float_ieee_bv_transfer,
    smtfloatTheory.native_float_min_transfer,
    smtfloatTheory.native_float_max_transfer,
    smtfloatTheory.native_float_rem_transfer]
  val expansions = [smtfloatTheory.smtfp_is_finite_expansion,
    smtfloatTheory.smtfp_is_integral_expansion,
    smtfloatTheory.smtfp_is_signalling_expansion]
  fun create graph scope {template_limit,prefix_depth,check_type} : producer =
    let
      val _ = G.validate_scope graph scope
      val _ = if template_limit > 0 andalso prefix_depth > 0 then () else
        raise ERR "create" "nonpositive native-float schema contract"
      fun bounded term =
        case SmtReplayImport.bounded_raw_size template_limit term of
          SOME _ => () | NONE => raise ERR "schema" "expanded float schema"
      val _ = List.app (bounded o Thm.concl) (laws @ expansions)
      val rules = List.concat (List.map
        (List.map Drule.SPEC_ALL o Drule.CONJUNCTS) laws) @ expansions
      val _ = List.app (bounded o Thm.concl) rules
      val types = ref (Redblackset.empty Int.compare)
      val images = ref (Redblackmap.mkDict Int.compare)
      val intro = Term.prim_mk_const {Thy = "smtfloat",Name = "smtfp_intro"}
      val bits = Term.prim_mk_const {Thy = "smtfloat",Name = "smtfp_bits"}
      fun admit node =
        let val id = G.type_id graph node in
          if Redblackset.member (!types,id) then () else
            (check_type (G.type_of graph node);
             types := Redblackset.add (!types,id)) end
      fun term_types [] = ()
        | term_types (term :: pending) =
            (check_type (Term.type_of term);
             if Term.is_comb term then
               let val (operator,operand) = Term.dest_comb term in
                 term_types (operator :: operand :: pending) end
             else if Term.is_abs term then
               raise ERR "schema" "native-float binder schema unsupported"
             else term_types pending)
      fun conversion term =
        let
          val _ = bounded term
          val _ = term_types [term]
          val result = Rewrite.PURE_REWRITE_CONV rules term
          val _ = bounded (Thm.concl result)
          val _ = term_types [Thm.concl result]
        in result end
      fun spine node arguments = case G.view graph node of
          G.Application (operator,operand) => spine operator
            (operand :: arguments)
        | G.Constant _ => SOME (G.representative graph node,arguments)
        | _ => NONE
      fun remember node =
        case spine node [] of SOME (head,operands) =>
          if (Term.same_const head intro andalso List.length operands = 1)
              orelse (Term.same_const head bits andalso
                List.length operands = 3) then
            let
              val variables = case G.free_variable_nodes graph node of
                  SOME variables => variables
                | NONE => raise ERR "alias" "unknown native-float image IDs"
              val _ = List.app (fn variable =>
                if G.scope_visible graph scope (G.node_scope graph variable)
                then () else raise ERR "alias" "float image ID escapes scope")
                variables
            in images := Redblackmap.insert (!images,G.node_id node,
              {image = node,operands = operands,free_variables = variables}) end
          else ()
        | NONE => ()
      fun propose node =
        let
          val _ = G.validate_scope graph scope
          val _ = if G.scope_visible graph scope (G.node_scope graph node)
            then () else raise ERR "propose" "float source escapes scope"
          val _ = List.app admit (G.block_reachable graph [node])
          val result = case G.view graph node of
              G.OpaqueRetained => NONE | G.AdmittedBinder _ => NONE
            | _ => C.graph_schema_conversion graph scope
                {conversion = conversion,template_limit = template_limit,
                 prefix_depth = prefix_depth} node
          val _ = case result of NONE => () | SOME schema =>
            let val output = C.graph_schema_result schema
                val _ = List.app admit (G.block_reachable graph [output])
            in List.app remember (G.block_reachable graph [output]) end
        in result end
      fun aliases () =
        (G.validate_scope graph scope;
         List.map #2 (Redblackmap.listItems (!images)))
      fun install_aliases (session : SmtLib_GraphFrontend.session) entries =
        let
          val _ = G.validate_scope graph scope
          val backend = #backend (#reader session)
          val _ = G.validate_scope graph (#scope (#reader session))
          fun install (token,image) =
            let
              (* Owner admission precedes the numeric provenance lookup. *)
              val ty = G.type_of graph image
              val _ = case Redblackmap.peek (!images,G.node_id image) of
                  SOME {image = owned,...} => if image = owned then () else
                    raise ERR "alias" "native image identity changed"
                | NONE => raise ERR "alias" "unrecorded native image"
              fun parse frame _ indices arguments =
                if not (null indices andalso null arguments) then
                  SmtLib_Theories.decline "float image" "nullary alias required"
                else let val active = valOf (B.frame_scope backend frame) in
                  if G.scope_visible graph active (G.node_scope graph image)
                  then image else raise ERR "alias" "image escapes reader scope"
                end
            in (#add_source_parser session) (token,ty,parse) end
        in List.app install entries end
    in {propose = propose,aliases = aliases,install_aliases = install_aliases}
    end
end
