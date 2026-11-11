(* Copyright (c) 2026 The HOL4 contributors. *)
structure SmtLib_GraphCarrierOperations =
struct
  structure Q = SmtLib_GraphQueryAnalysis
  structure T = SmtLib_GraphTranslation
  structure L = SmtLib_CarrierLetBindings

  (* These are actual production policy dependencies, not optional probes.
     Their implementation must preserve original-query/proof transport.
     All other dispatcher syntax is implemented over the borrowed carrier. *)
  type datatype_callbacks =
    {parser_case:Q.carrier ->
       Q.carrier SmtLib.outbound_carrier_parser_case option,
     datatype_selector_term:Type.hol_type -> Term.term -> int ->
       Q.carrier -> Q.carrier,
     is_case:Q.carrier -> bool,
     term_to_string:Q.carrier -> string}

  fun make (context:Q.outbound_context) {sequence_emission}
      (callbacks:datatype_callbacks)
      : Q.carrier SmtLib.outbound_term_translation_operations =
    let
      val builtin = T.outbound_builtin_operations context
      val syntax_error = #syntax_error builtin
      val is_syntax_error = #is_syntax_error builtin
      val native = SmtLib.outbound_term_translation_operations
      val _ = ignore ((#key context) (#goal context))
      fun guard term = ignore ((#key context) term)
      fun checked observe term =
        (guard term;
         let val answer = observe term val _ = guard term in answer end)
      fun failure function message = raise syntax_error function message
      fun metadata_error primary = case primary of
          Feedback.HOL_ERR error => syntax_error
            (Feedback.top_function_of error) (Feedback.message_of error)
        | _ => primary
      (* Only pure type/atomic-schema work belongs inside this boundary. *)
      fun metadata thunk = thunk ()
        handle primary as Feedback.HOL_ERR _ => raise metadata_error primary
      fun accepts observe term = (ignore (observe term);true)
        handle primary =>
          if is_syntax_error primary then false else raise primary
      fun optional observe term = SOME (observe term)
        handle primary =>
          if is_syntax_error primary then NONE else raise primary
      fun dest_comb term = case (#view context) term of
          Q.ApplicationView pair => pair
        | _ => failure "dest_comb" "application expected"
      fun dest_abs term = case (#view context) term of
          Q.AbstractionView pair => pair
        | _ => failure "dest_abs" "abstraction expected"
      fun is_var term = case (#view context) term of
          Q.VariableView _ => true | _ => false
      fun is_const term = case (#view context) term of
          Q.ConstantView _ => true | _ => false
      fun same_const term expected = case (#view context) term of
          Q.ConstantView atom => Library.same_const atom expected
        | _ => false
      fun term_same_const term expected = case (#view context) term of
          Q.ConstantView atom => Term.same_const atom expected
        | _ => false
      fun known_same_const expected term = case (#view context) term of
          Q.ConstantView atom => Library.same_const expected atom
        | _ => false
      fun unary head term =
        let val (actual,argument) = dest_comb term
        in if same_const actual head then argument
           else failure "unary" "different constant head" end
      fun binary head term =
        let val (prefix,right) = dest_comb term
            val (actual,left) = dest_comb prefix
        in if same_const actual head then (left,right)
           else failure "binary" "different constant head" end
      fun strip_abs term =
        let fun loop term variables = case optional dest_abs term of
                NONE => (List.rev variables,term)
              | SOME (variable,body) => loop body (variable::variables)
        in loop term [] end
      fun strip_binder head term =
        let fun one term = dest_abs (unary head term)
            fun loop term variables = case optional one term of
                NONE => (List.rev variables,term)
              | SOME (variable,body) => loop body (variable::variables)
        in loop term [] end
      val list_mk_comb = #list_mk_comb builtin
      (* Instantiate trusted atomic schemas using authenticated operand
         types. Never catch an operand observation or construction error. *)
      fun apply_known (head,arguments) =
        let val types = List.map (#type_of context) arguments
            val atom = metadata (fn () =>
              let
                fun match _ [] substitutions = substitutions
                  | match ty (argument_ty::rest) substitutions =
                      let val (domain,range) = Type.dom_rng ty
                      in match range rest (Type.match_type_in_context
                        domain argument_ty substitutions) end
              in Term.inst (match (Term.type_of head) types []) head end)
        in list_mk_comb ((#constant context) atom,arguments) end
      fun apply_constant (head,argument) =
        (#mk_comb context) ((#constant context) head,argument)
      fun pair (left,right) = apply_known (pairSyntax.comma_tm,[left,right])
      val pabs : Q.carrier L.pabs_operations =
        {dest_abs=dest_abs,dest_uncurry=unary pairSyntax.uncurry_tm,
         mk_pair=pair,is_syntax_error=is_syntax_error}
      fun dest_let term = binary boolSyntax.let_tm term
      fun dest_plet term =
        let val (function,value) = dest_let term
            val (pattern,body) = L.dest_pabs pabs function
        in (pattern,value,body) end
      val lets : Q.carrier L.operations =
        {dest_abs=dest_abs,dest_let=dest_let,dest_plet=dest_plet,
         strip_pabs=L.strip_pabs pabs,list_mk_comb=list_mk_comb,
         is_let=accepts dest_let,is_syntax_error=is_syntax_error,
         not_a_let=fn () => syntax_error "dest_anylet" "not a let term"}
      (* The generic literal grammar supplies only its fixed closed zero
         templates here. Traverse those templates, never query syntax. *)
      fun known_template raw =
        if Term.is_const raw then (#constant context) raw
        else if Term.is_comb raw then
          let val (left,right) = Term.dest_comb raw
          in (#mk_comb context) (known_template left,known_template right) end
        else failure "known_template" "closed constant template expected"
      fun aconv_known term raw =
        (#same context) (term,known_template raw)
      fun free_in variable term =
        List.exists (fn free => (#same context) (variable,free))
          ((#free_variables context) term)
      fun compare_key ((a,b),(c,d)) = case Int.compare (a,c) of
          EQUAL => Int.compare (b,d) | order => order
      val string_cache = ref (Redblackmap.mkDict compare_key)
      fun memo_string term compute =
        let val key = (#key context) term
        in case Redblackmap.peek (!string_cache,key) of
            SOME answer => (guard term;answer)
          | NONE =>
              let val answer = compute () val _ = guard term
                  val _ = string_cache :=
                    Redblackmap.insert (!string_cache,key,answer)
              in answer end
        end
      val literal_operations :
          Q.carrier SmtLib.outbound_carrier_literal_operations =
        {builtin=builtin,dest_comb=dest_comb,dest_abs=dest_abs,
         strip_comb= #strip_comb context,term_same_const=term_same_const,
         same_const=same_const,known_same_const=known_same_const,
         aconv=fn left => fn right => (#same context) (left,right),
         aconv_known=aconv_known,free_in=free_in,
         is_Num=accepts (unary intSyntax.Num_tm),
         dest_Num=unary intSyntax.Num_tm,dest_leq=binary intSyntax.leq_tm,
         is_numeral=accepts (#dest_numeral builtin),
         apply_constant=apply_constant,optional_error=is_syntax_error,
         memo_string_expression=memo_string}
      val literals =
        SmtLib.outbound_carrier_literal_recognizers literal_operations
      val encode = T.outbound_query_builtin_encoder context
      fun encode_builtin (head,arguments) =
        case encode (head,arguments) of SOME result => result
        | NONE => failure "encode_builtin" "no builtin encoding"
      fun builtin_encoding term =
        let val (head,arguments) = (#strip_comb context) term
        in case encode (head,arguments) of
            SOME (symbol,_) => SOME (symbol,length arguments)
          | NONE =>
              let val ty = (#type_of context) term
                  val function = Option.isSome
                    (metadata (fn () => SOME (Type.dom_rng ty))
                     handle primary =>
                       if is_syntax_error primary then NONE
                       else raise primary)
              in if function then NONE else
                Option.map (fn (symbol,_) => (symbol,0)) (encode (term,[]))
              end
        end
      fun leaf observe default term = case (#view context) term of
          Q.ConstantView atom => observe atom | _ => default
      fun declared_arity term = case (#view context) term of
          Q.ConstantView atom => SmtLib.outbound_constant_arity atom
        | _ => failure "declared_const_arity" "constant expected"
      fun set_element_type term =
        let val ty = (#type_of context) term
        in if SmtLib.outbound_is_set_type ty then
             metadata (fn () => #1 (Type.dom_rng ty))
           else failure "set_element_type" "not a set-valued term" end
      fun bag_element_type term =
        let val ty = (#type_of context) term
        in if SmtLib.outbound_is_bag_type ty then
             metadata (fn () => #1 (Type.dom_rng ty))
           else failure "bag_element_type" "not a bag-valued term" end
      fun sequence_element_type term =
        let val ty = (#type_of context) term
        in if SmtLib.outbound_is_native_sequence_type ty then
             metadata (fn () => listSyntax.dest_list_type ty)
           else failure "sequence_element_type" "not a native sequence" end
      fun has_contextual term =
        let val ty = (#type_of context) term
            fun domains ty =
              (let val (_,range) = Type.dom_rng ty in 1 + domains range end)
              handle Feedback.HOL_ERR _ => 0
            val count = domains ty
            fun loop index = index < count andalso
              (Option.isSome ((#contextual_argument context) (term,index))
               orelse loop (index+1))
        in loop 0 end
      fun mk_nil ty =
        (guard (#goal context);
         (#constant context) (metadata (fn () =>
           Term.inst [{redex=Type.alpha,residue=ty}] listSyntax.nil_tm)))
      fun selector ty constructor index term =
        let val _ = guard term
            val result = (#datatype_selector_term callbacks)
              ty constructor index term
            val _ = guard term val _ = guard result
        in result end
      fun parser_case term =
        let val answer = checked (#parser_case callbacks) term
            val _ = case answer of
                NONE => ()
              | SOME (SmtLib.CarrierSelector {scrutinee,...}) =>
                  guard scrutinee
              | SOME (SmtLib.CarrierTester {scrutinee,...}) => guard scrutinee
        in answer end
      val collections = T.outbound_query_collection_recognizers context
        {sequence_emission=sequence_emission}
    in
      {type_of= #type_of context,is_var=is_var,is_const=is_const,
       dest_comb=dest_comb,dest_abs=dest_abs,strip_abs=strip_abs,
       strip_comb= #strip_comb context,list_mk_abs= #list_mk_abs context,
       list_mk_comb=list_mk_comb,mk_comb= #mk_comb context,
       apply_constant=apply_constant,free_vars= #free_variables context,
       aconv=fn left => fn right => (#same context) (left,right),
       genvar= #genvar context,same_const=same_const,
       known_const_matches=known_same_const,
       declared_const_arity=declared_arity,
       term_to_string=checked (#term_to_string callbacks),
       is_forall=accepts (dest_abs o unary boolSyntax.universal),
       is_exists=accepts (dest_abs o unary boolSyntax.existential),
       strip_forall=strip_binder boolSyntax.universal,
       strip_exists=strip_binder boolSyntax.existential,
       dest_let=L.dest_anylet lets,
       beta_reduce=SmtLib_GraphCarrierBeta.reduce context,
       is_marked_set_term= #is_set context,is_marked_bag_term= #is_bag context,
       is_raw_number= #is_raw_number context,
       set_element_type=set_element_type,bag_element_type=bag_element_type,
       sequence_element_type=sequence_element_type,
       contextual_collection_argument=fn term => fn index =>
         (#contextual_argument context) (term,index),
       has_contextual_collection_argument=checked has_contextual,
       is_empty_set=fn term => same_const term pred_setSyntax.empty_tm,
       is_univ_set=fn term => same_const term pred_setSyntax.univ_tm,
       dest_set_card=unary pred_setSyntax.card_tm,
       is_empty_bag=fn term => same_const term bagSyntax.EMPTY_BAG_tm,
       dest_bag_card=unary bagSyntax.BAG_CARD_tm,
       is_nil=fn term => same_const term listSyntax.nil_tm,
       mk_cons=fn (left,right) =>
         apply_known (listSyntax.cons_tm,[left,right]),
       mk_nil=mk_nil,is_parsed_bag_literal= #is_parsed_bag_literal literals,
       dest_parsed_bag_literal= #dest_parsed_bag_literal literals,
       native_string_literal= #native_string_literal literals,
       is_injected_string= #is_injected_string literals,
       dest_injected_string= #dest_injected_string literals,
       is_injected_float= #is_injected_float literals,
       dest_injected_float= #dest_injected_float literals,
       is_injected_string_operation= #is_injected_string_operation literals,
       dest_injected_string_operation=
         #dest_injected_string_operation literals,
       hexadecimal_string= #hexadecimal_string literals,
       encode_builtin=encode_builtin,builtin_encoding=builtin_encoding,
       is_constructor=leaf (#is_constructor native) false,
       parser_case=parser_case,datatype_selector_term=selector,
       has_ranked_semantics=leaf (#has_ranked_semantics native) false,
       is_case=checked (#is_case callbacks),
       is_update_comb=accepts (fn term =>
         let val (prefix,_) = dest_comb term
         in binary combinSyntax.update_tm prefix end),
       dest_update_comb=fn term =>
         let val (prefix,argument) = dest_comb term
         in (binary combinSyntax.update_tm prefix,argument) end,
       reject_unsupported_smtfloat_constant=
         leaf (#reject_unsupported_smtfloat_constant native) (),
       collection_recognizers=collections,syntax_error=syntax_error,
       is_fallback_error=is_syntax_error,is_optional_error=is_syntax_error,
       metadata_error=metadata_error,commit_error=SmtLib.NestedTranslation}
    end

  (* Complete production datatype callbacks. The formatter is
     still supplied by the caller; it may not unfold a large Query term.
     These callbacks produce syntax DATA, not preprocessing proof transport. *)
  fun make_with_datatypes (context:Q.outbound_context) options
      {term_to_string} =
    let
      val builtin = T.outbound_builtin_operations context
      val syntax_error = #syntax_error builtin
      val datatype_hooks = SmtLib_GraphCarrierDatatype.make context
        {syntax_error=syntax_error,is_mismatch= #is_syntax_error builtin}
    in make context options
      {parser_case= #parser_case datatype_hooks,
       datatype_selector_term= #datatype_selector_term datatype_hooks,
       is_case= #is_case datatype_hooks,
       term_to_string=term_to_string} end
end
