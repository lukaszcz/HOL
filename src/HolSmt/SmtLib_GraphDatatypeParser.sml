(* The shared bounded datatype templates, with carrier-neutral operands. *)
structure SmtLib_GraphDatatypeParser :> SmtLib_GraphDatatypeParser =
struct
  structure B = SmtLib_GraphBackend
  structure F = SmtLib_GraphFrontend
  structure P = SmtLib_Parser
  structure R = SmtLib_GraphTheories
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
        in (B.compile_recipe_with_policy
          {template = template, holes = holes,
           template_limit = #template_limit limits},holes,template) end
      (* Arity/indices decline in the individual callbacks, just as in
         SmtLib.add_datatype_parser_entries. A sort mismatch must instead
         reach the same native builder: it is not an overload decline.
         Only fresh, typed atoms reach that builder, never query operands.
         If the native case builder accepts the types, retain its result. *)
      fun apply recipe expected native frame arguments =
        let
          val _ = guard ()
          val recipe =
            if ListPair.allEq (fn (ty, argument) =>
                Type.compare (ty, B.type_of backend argument) = EQUAL)
                (expected, arguments) then recipe
            else
              let
                val holes = Lib.mapi (fn index => fn argument =>
                  Term.mk_var ("__smt_datatype_operand_" ^ Int.toString index,
                    B.type_of backend argument)) arguments
              in compile holes (native holes) end
          val (recipe,holes,template) = recipe
          val _ = case B.constructor_sources backend of NONE => ()
            | SOME {arguments,...} =>
              (B.syntax_spend backend
                 (3+4*IntInf.fromInt (List.length holes));
               B.note_constructor_source backend
                 (SmtLib_ConstructorSyntax.from_template
                   {template=template,holes=holes,operands=arguments}))
          val built = B.construct_with_branches_with_policy backend frame
            recipe arguments
          val _ = record (#branches built)
          val _ = guard ()
        in #value built end
      (* Tester dispatch observes only atom identity/name. A compound stand-in
         deliberately reaches the ordinary Term.dest_thy_const failure; no
         operand is unfolded, even when the literal-index budget is small. *)
      val compound_index = Term.mk_comb (boolSyntax.negation, boolSyntax.T)
      fun shallow_index frame value = case B.view backend frame value of
          B.Atom term => term
        | _ => Term.mk_comb (Term.mk_var ("__smt_datatype_index",
            Type.--> (Type.bool,B.type_of backend value)),boolSyntax.T)
      val (_, ordinary_dictionary) =
        SmtLib_Logics.parsedicts_of_any_solver_logic "ALL"
      fun source_index frame (_, source : 'a P.index_source) =
        case !(#literal source) of SOME literal => literal
        | NONE =>
            (case R.diagnostic_index backend frame (#index_limit limits)
                ordinary_dictionary source of
              SOME term => term
            | NONE => compound_index)
      fun tester_index frame index = case index of
          P.SymbolIndex name =>
            Term.mk_var (name,Type.mk_vartype "'smtlib_index")
        | P.LiteralIndex term => term
        | P.LexicalIndex (value,name) => Term.mk_var
            (P.proof_symbol_text name,B.type_of backend value)
        | P.ValueIndex (value,_) => shallow_index frame value
        | P.SourceIndex pair => source_index frame pair
      (* Entries are prepended: the first installed tester is tried last.
         Only that final indexed decline renders the ordinary diagnostic.
         Without indices the dispatcher's formatting is already exact:
         decline normally so a nullary lexical '_' can still accept.
         Earlier mismatches must allow another constructor to accept. *)
      val first_tester = ref true
      fun tester_decline last frame name token indices arguments message =
        if not last orelse List.null indices then SmtLib_Theories.decline
          ("<" ^ name ^ " " ^ token ^ ">") message
        else
          let
            fun reject _ _ _ = SmtLib_Theories.decline
              ("<" ^ name ^ " " ^ token ^ ">") message
            val dictionary = Library.extend_dict ((name,reject),
              Redblackmap.mkDict String.compare)
            val holes = Lib.mapi (fn index => fn argument => Term.mk_var
              ("__smt_datatype_diagnostic_" ^ Int.toString index,
               B.type_of backend argument)) arguments
            (* Reuse native error formatting with bounded original indices
               and typed atoms, never actual native query operands. *)
            val _ = P.apply_term dictionary name
              (List.map (tester_index frame) indices) holes
          in raise Match end
      fun declaration
          ({hol_type, constructors} : SmtLib.parser_datatype_declaration) =
        let
          val scrutinee = Term.mk_var ("__smt_datatype_scrutinee", hol_type)
          fun constructor
              ({constructor, token, selectors} :
                SmtLib.parser_datatype_constructor) =
            let
              val last_tester = !first_tester
              val _ = first_tester := false
              val _ = admit (Term.type_of constructor)
              val (domains, result) = boolSyntax.strip_fun
                (Term.type_of constructor)
              val _ = if Type.compare (result, hol_type) = EQUAL then ()
                else raise error "datatype" "constructor result type mismatch"
              val holes = Lib.mapi (fn index => fn ty => Term.mk_var
                ("__smt_datatype_field_" ^ Int.toString index, ty)) domains
              val constructor_recipe = compile holes
                (Term.list_mk_comb (constructor, holes))
              fun constructor_native arguments =
                Term.list_mk_comb (constructor, arguments)
              fun constructor_parse frame name indices arguments =
                (guard ();
                 if List.null indices andalso
                    List.length arguments = List.length domains then
                   apply constructor_recipe domains constructor_native
                     frame arguments
                 else SmtLib_Theories.decline ("<" ^ name ^ ">")
                   "wrong number of arguments")
              (* A declared datatype token is authoritative. Retrying an
                 emitted-value fallback would overwrite its arity diagnostic. *)
              val _ = (#replace_source_parser session)
                (token, Term.type_of constructor, constructor_parse)
              fun tester_native [arg] =
                    SmtLib.parser_datatype_tester_template hol_type
                      constructor arg
                | tester_native _ = raise Match
              val tester = compile [scrutinee] (tester_native [scrutinee])
              fun tester_parse frame name indices arguments =
                (guard ();case (indices, arguments) of
                  ([index], [_]) =>
                    let
                      val index = tester_index frame index
                      val matches = Term.same_const index constructor
                        handle Feedback.HOL_ERR _ => false
                      val index_name = Lib.fst (Term.dest_var index)
                        handle Feedback.HOL_ERR _ =>
                          #Name (Term.dest_thy_const index)
                    in
                      if index_name = token orelse matches then
                        apply tester [hol_type] tester_native frame arguments
                      else tester_decline last_tester frame name token
                        indices arguments "tester constructor mismatch"
                    end
                | _ => tester_decline last_tester frame name token
                    indices arguments
                    "one constructor index and one argument expected")
              val _ = (#add_symbolic_index session) ("is", token)
              val _ = (#add_constructor_parser session) ("is", tester_parse)
              fun selector (index, (name, ty)) =
                let
                  val _ = admit ty
                  fun native [arg] =
                        SmtLib.parser_datatype_selector_template hol_type
                          constructor index arg
                    | native _ = raise Match
                  val recipe = compile [scrutinee] (native [scrutinee])
                  fun parse frame token indices arguments =
                    (guard ();case (indices, arguments) of
                      ([], [_]) => apply recipe [hol_type] native
                        frame arguments
                    | _ => SmtLib_Theories.decline ("<" ^ token ^ ">")
                        "one argument expected")
                in (#replace_source_parser session)
                  (name, Type.--> (hol_type, ty), parse) end
              val _ = List.app selector
                (ListPair.zipEq
                  (List.tabulate (List.length selectors, fn index => index),
                   selectors))
            in () end
        in List.app constructor constructors end
    in List.app declaration (List.rev declarations);guard () end

end
