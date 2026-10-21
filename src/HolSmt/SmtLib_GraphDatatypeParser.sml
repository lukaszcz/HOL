(* The shared bounded datatype templates, with carrier-neutral operands. *)
structure SmtLib_GraphDatatypeParser :> SmtLib_GraphDatatypeParser =
struct
  structure B = SmtLib_GraphBackend
  structure F = SmtLib_GraphFrontend
  fun sort_dictionary_from_types types =
    Redblackmap.foldl (fn (ty,token,dictionary) =>
      Redblackmap.insert (dictionary,token,[SmtLib_Theories.K_zero_zero ty]))
      (Redblackmap.mkDict String.compare) types

  fun install_with_policy
      {limits:SmtReplayResourcePolicy.recipe_policy,error}
      types declarations guard
      (session:'a F.constructed_session) record =
    let
      val _ = guard ()
      val backend = #backend (#reader session)
      val admission = SmtWordGraph.new_type_admission ()
      fun admit ty = SmtWordGraph.admit_primitive_type admission ty
      val _ = Redblackmap.foldl
        (fn (ty, _, ()) => admit ty) () types
      val declarations = declarations ()
      fun compile holes template =
        let
          val _ = admit (Term.type_of template)
          val _ = List.app (admit o Term.type_of) holes
        in B.compile_recipe_with_policy
          {template = template, holes = holes,
           template_limit = #template_limit limits} end
      fun apply recipe expected frame token indices arguments =
        let val _ = guard () in
        if not (List.null indices) orelse
           List.length expected <> List.length arguments then
          SmtLib_Theories.decline ("<" ^ token ^ ">")
            "wrong number of arguments"
        else if not (ListPair.allEq (fn (ty, argument) =>
            Type.compare (ty, B.type_of backend argument) = EQUAL)
            (expected, arguments)) then
          SmtLib_Theories.decline ("<" ^ token ^ ">")
            "datatype operand sort mismatch"
        else
          let val built = B.construct_with_branches_with_policy backend frame
                recipe arguments
              val _ = record (#branches built)
              val _ = guard ()
          in #value built end
        end
      fun declaration
          ({hol_type, constructors} : SmtLib.parser_datatype_declaration) =
        let
          val scrutinee = Term.mk_var ("__smt_datatype_scrutinee", hol_type)
          fun constructor
              ({constructor, token, selectors} :
                SmtLib.parser_datatype_constructor) =
            let
              val _ = admit (Term.type_of constructor)
              val (domains, result) = boolSyntax.strip_fun
                (Term.type_of constructor)
              val _ = if Type.compare (result, hol_type) = EQUAL then ()
                else raise error "datatype" "constructor result type mismatch"
              val holes = Lib.mapi (fn index => fn ty => Term.mk_var
                ("__smt_datatype_field_" ^ Int.toString index, ty)) domains
              val constructor_recipe = compile holes
                (Term.list_mk_comb (constructor, holes))
              val _ = (#add_source_parser session)
                (token, Term.type_of constructor,
                 apply constructor_recipe domains)
              val tester = compile [scrutinee]
                (SmtLib.parser_datatype_tester_template hol_type
                  constructor scrutinee)
              fun tester_parse frame name indices arguments =
                (guard ();case indices of
                  [SmtLib_Parser.SymbolIndex index] =>
                    if index = SmtLib_Parser.proof_symbol_text token then
                      apply tester [hol_type] frame name [] arguments
                    else SmtLib_Theories.decline ("<" ^ name ^ ">")
                      "tester constructor mismatch"
                | _ => SmtLib_Theories.decline ("<" ^ name ^ ">")
                    "one constructor index expected")
              val _ = (#add_symbolic_index session) ("is", token)
              val _ = (#add_constructor_parser session) ("is", tester_parse)
              fun selector (index, (name, ty)) =
                let
                  val _ = admit ty
                  val recipe = compile [scrutinee]
                    (SmtLib.parser_datatype_selector_template hol_type
                      constructor index scrutinee)
                in (#add_source_parser session)
                  (name, Type.--> (hol_type, ty), apply recipe [hol_type]) end
              val _ = List.app selector
                (ListPair.zipEq
                  (List.tabulate (List.length selectors, fn index => index),
                   selectors))
            in () end
        in List.app constructor constructors end
    in List.app declaration (List.rev declarations);guard () end

end
