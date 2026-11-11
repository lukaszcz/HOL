(* Copyright (c) 2026 The HOL4 contributors. *)
structure SmtLib_GraphTranslation =
struct
  open SmtLib SmtLib_GraphFrontend SmtLib_GraphBackend SmtWordGraph
  structure F = SmtLib_GraphFrontend
  structure B = SmtLib_GraphBackend
  structure G = SmtReplayGraph
  structure Q = SmtLib_GraphQueryAnalysis
  val ERR = Feedback.mk_HOL_ERR "SmtLib_GraphTranslation"
  (* Retain the translation's actual declaration and regime contracts. *)
  fun source_declarations ({regime, tmdict, ...} : SmtLib.translation)
      : F.source_declaration list =
    Redblackmap.foldr (fn ((original, count), token, declarations) =>
      let val arity = case regime of
          SmtLib.FirstOrder => F.Exact count
        | SmtLib.HigherOrder _ => F.AtMost
            (List.length (#1 (boolSyntax.strip_fun (Term.type_of original))))
      in {token = token, original = original, arity = arity}
        :: declarations end) [] tmdict
  fun sort_dictionary_from_types tydict
      : Type.hol_type SmtLib_Parser.dict =
    Redblackmap.foldl (fn (ty, token, dictionary) =>
      Redblackmap.insert (dictionary, token,
        [SmtLib_Theories.K_zero_zero ty]))
      (Redblackmap.mkDict String.compare) tydict
  fun sort_dictionary ({tydict,...}:SmtLib.translation) =
    sort_dictionary_from_types tydict

  fun install_datatypes_with_branches (options : F.options) translation
      (session : F.session) record =
    let
      val {template_limit,index_limit,operand_limit,token_limit} =
        #recipe_limits options
      fun finite n = SmtReplayResourcePolicy.AtMost (IntInf.fromInt n)
      val limits = {template_limit=finite template_limit,
        index_limit=finite index_limit,operand_limit=finite operand_limit,
        token_limit=finite token_limit}
      val backend = #backend (#reader session)
      fun guard () = ignore (B.frame_scope backend (B.root backend))
    in SmtLib_GraphDatatypeParser.install_with_policy
      {limits=limits,error=ERR} (#tydict translation)
      (fn () => SmtLib.parser_datatype_declarations translation)
      guard session record end

  fun install_datatypes options translation session =
    install_datatypes_with_branches options translation session (fn _ => ())

  fun configured_options (base : F.options)
      (translation : SmtLib.translation) : F.configured_options =
    {base =
      {graph = #graph base, scope = #scope base, logic = #logic translation,
       sources = #sources base, sorts = sort_dictionary translation,
       binder_lists = #binder_lists base, import_limit = #import_limit base,
       literal_limit = #literal_limit base, binder_limit = #binder_limit base,
       recipe_limits = #recipe_limits base, special = #special base,
       ascribed = #ascribed base},
     source_declarations = source_declarations translation}

  fun create_session base translation description tokens =
    let
      val configured = configured_options base translation
      val session = F.create_configured_session configured description tokens
      val _ = install_datatypes (#base configured) translation session
    in session end

  fun install_declared_datatypes_with_policy_and_branches
      (options:F.policy_options) types declarations guard
      (session:F.session) record =
    SmtLib_GraphDatatypeParser.install_with_policy
      {limits= #recipe_limits options,error=ERR}
      types declarations guard session record

  fun install_datatypes_with_policy_and_branches options
      (translation:SmtLib.translation) session record =
    install_declared_datatypes_with_policy_and_branches options
      (#tydict translation)
      (fn () => SmtLib.parser_datatype_declarations translation)
      (fn () => ()) session record

  fun install_datatypes_with_policy options translation session =
    install_datatypes_with_policy_and_branches options translation session (fn _ => ())

  fun configured_options_with_policy (base : F.policy_options)
      (translation : SmtLib.translation) : F.policy_configured_options =
    {base =
      {graph = #graph base, scope = #scope base, logic = #logic translation,
       sources = #sources base, sorts = sort_dictionary translation,
       binder_lists = #binder_lists base, import_limit = #import_limit base,
       literal_limit = #literal_limit base, binder_limit = #binder_limit base,
       recipe_limits = #recipe_limits base, special = #special base,
       ascribed = #ascribed base},
     source_declarations = source_declarations translation}

  fun create_session_with_policy base translation description tokens =
    let
      val configured = configured_options_with_policy base translation
      val session = F.create_configured_session_with_policy configured description tokens
      val _ = install_datatypes_with_policy (#base configured) translation session
    in session end

  (* Graph-native lexical initialization for a future outbound serializer.
     The declarations are DATA and must match that serializer's actual
     emitted names, like the old translation tmdict. They create no Sources,
     bridges, proof edges or permission to assume their represented terms.
     Sorts and constructor recipes remain the caller's emission contract. *)
  fun create_query_session_with_policy expected query
      (base:F.policy_options) declarations description tokens =
    ((let
        val data = SmtLib_GraphPreprocess.query_nodes_with_policy_for
          expected query
        val _ = if Portable.pointer_eq (#graph base,#graph data) andalso
            #scope base = #scope data then () else
          raise ERR "create_query_session_with_policy"
            "different query graph or scope"
        val session = F.create_graph_configured_session_with_policy
          {base=base,graph_source_declarations=declarations}
          description tokens
        val _ = SmtLib_GraphPreprocess.validate_query_with_policy
          expected query
      in session end)
     handle primary => (SmtReplayInvocationWork.close expected;raise primary))

  (* This installs datatype syntax only. General Mapping recipe closures
     still need their own parser interpretation and checked transport.
     Existing graph declaration DATA is supplied explicitly, never obtained
     by dropping mapping declarations that do not have a graph alias. *)
  fun create_metadata_query_session_aux expected query (base:F.policy_options)
      {metadata,declarations} description tokens record =
    ((let
        val data = SmtLib_GraphPreprocess.query_nodes_with_policy_for
          expected query
        val _ = if Portable.pointer_eq (#graph base,#graph data) andalso
            #scope base = #scope data then () else
          raise ERR "create_metadata_query_session_with_policy"
            "different query graph or scope"
        val sources = #sources data
        val limits = SmtReplayInvocationWork.semantic_policy expected
        val mapping = SmtLib_GraphDeclarationMetadata.mapping_for
          (#graph base) (#scope base) metadata
        val types = SmtLib_GraphParserMapping.types mapping
        (* Datatype recipes use only the retained type dictionary. Header
           validation checks its graph/scope/epochs without rescanning every
           unrelated declaration DAG node on each parser application. *)
        fun guard () =
          ((SmtReplayInvocationWork.validate_policy expected
             (#graph base) (#scope base) sources limits;
            ignore (SmtLib_GraphParserMapping.types mapping))
           handle primary =>
             (SmtReplayInvocationWork.close expected;raise primary))
        val configured : F.policy_options =
          {graph= #graph base,scope= #scope base,logic= #logic base,
           sources= #sources base,sorts=sort_dictionary_from_types types,
           binder_lists= #binder_lists base,import_limit= #import_limit base,
           literal_limit= #literal_limit base,binder_limit= #binder_limit base,
           recipe_limits= #recipe_limits base,special= #special base,
           ascribed= #ascribed base}
        val session = F.create_graph_configured_session_with_policy
          {base=configured,graph_source_declarations=declarations}
          description tokens
        val _ = install_declared_datatypes_with_policy_and_branches configured
          types (fn () => SmtLib.parser_datatype_declarations_from_types types)
          guard session record
        val _ = SmtLib_GraphPreprocess.validate_query_with_policy
          expected query
        val _ = guard ()
      in {session=session,guard=guard} end)
     handle primary => (SmtReplayInvocationWork.close expected;raise primary))

  fun create_metadata_query_session_with_policy expected query base data
      description tokens =
    #session (create_metadata_query_session_aux expected query base data
      description tokens (fn _ => ()))

  (* Only the installed constructor/tester/selector recipes can record these
     branch nodes. Printed names or a caller's graph declaration list do not
     populate the branch set. *)
  fun create_metadata_alignment_session_with_policy expected query
      (base:F.policy_options) data description tokens =
    let
      val branches = ref (Redblackset.empty Int.compare)
      val graph = #graph base val scope = #scope base
      fun record nodes = branches := Redblackset.addList
        (!branches,List.map G.node_id nodes)
      val {session,guard} = create_metadata_query_session_aux expected query
        base data description tokens record
      fun admitted_branch (_,parsed) =
        (guard ();G.validate_scope graph scope;
         ignore (G.type_of graph parsed);
         Redblackset.member (!branches,G.node_id parsed))
    in {session=session,admitted_branch=admitted_branch} end

  (* The registry's keys are atomic constants or literal wildcard variables.
     Net.match sends every nonconstant candidate to the same wildcard list;
     a small variable probe therefore avoids exposing a whole graph term.
     constant_leaf authenticates each lookup carrier, including the
     nonconstant case. Retry is deliberately selective: Lib.tryfind would
     hide failures from graph ownership, admission or native callbacks. *)
  fun native_builtin_encoder
      (operations : 'a SmtLib.outbound_builtin_operations)
      {constant_leaf,is_mismatch} =
    let
      val entries = SmtLib.outbound_builtin_symbol_encodings operations
      val index = List.foldl (Lib.uncurry Net.insert) Net.empty entries
      val probe = Term.mk_var ("smt_builtin_lookup_probe",Type.bool)
      fun candidates current =
        let
          val lookup = case constant_leaf current of
              NONE => probe
            | SOME atom =>
                if Term.is_const atom then atom
                else raise ERR "native_builtin_encoder"
                  "constant callback returned nonconstant syntax"
        in Net.match lookup index end
      fun encode (input as (current,_)) =
        let
          fun attempt [] = NONE
            | attempt (parse :: rest) =
                (SOME (parse input)
                 handle primary =>
                   if is_mismatch primary then attempt rest
                   else raise primary)
        in attempt (candidates current) end
    in encode end

  (* Literal observations borrow the completed query carrier. Cache keys are
     authenticated before EVERY hit, and only successful observations are
     published. These caches and constructors grant no authority beyond that
     borrow. All operator encodings still come from the shared registry. *)
  local
    exception NativeBuiltinMismatch of string * string
    fun mismatch function message =
      NativeBuiltinMismatch (function,message)
    fun is_mismatch (NativeBuiltinMismatch _) = true
      | is_mismatch _ = false
    fun library_mismatch primary =
      let
        fun known error =
          List.exists (fn (structure_name,functions) =>
            Feedback.top_structure_of error = structure_name andalso
            List.exists (fn name => Feedback.top_function_of error = name)
              functions)
            [("Type",["dest_type","dest_thy_type"]),
             ("fcpSyntax",["dest_numeric_type","dest_cart_types"]),
             ("wordsSyntax",["dest_word_type"]),
             ("listSyntax",["dest_list_type"]),
             ("SmtLib",["smtfp_format"])]
        fun convert error = mismatch (Feedback.top_function_of error)
          (Feedback.message_of error)
      in
        case primary of
          Feedback.HOL_ERR error =>
            if known error then convert error else primary
        | SmtLib_Theories.ParseDecline (Feedback.HOL_ERR error) =>
            if Feedback.top_structure_of error = "SmtLib_Theories" andalso
               List.exists (fn name => Feedback.top_function_of error = name)
                 ["one_arg","two_args","three_args"]
            then convert error else primary
        | _ => primary
      end
  in
  type native_builtin_syntax =
    {view:Q.carrier -> Q.carrier_view,key:Q.carrier -> int * int,
     type_of:Q.carrier -> Type.hol_type,constant:Term.term -> Q.carrier,
     mk_comb:Q.carrier * Q.carrier -> Q.carrier}

  fun native_builtin_operations_with_syntax (context:native_builtin_syntax)
      : Q.carrier SmtLib.outbound_builtin_operations =
    let
      fun compare_key ((left_scope,left_node),(right_scope,right_node)) =
        case Int.compare (left_scope,right_scope) of
          EQUAL => Int.compare (left_node,right_node)
        | order => order
      fun memo_recursive observe =
        let val cache = ref (Redblackmap.mkDict compare_key)
            fun read current =
          let val key = (#key context) current
          in case Redblackmap.peek (!cache,key) of
              SOME result => result
            | NONE =>
                let val result = observe read current
                    val _ = (#key context) current
                    val _ = cache := Redblackmap.insert (!cache,key,result)
                in result end
          end
        in read end
      fun memo observe = memo_recursive (fn _ => observe)
      fun matches current expected =
        case (#view context) current of
          Q.ConstantView atom => Library.same_const atom expected
        | _ => false
      fun application function current =
        case (#view context) current of
          Q.ApplicationView operands => operands
        | _ => raise mismatch function "application expected"
      fun unary function expected current =
        let val (head,argument) = application function current
        in if matches head expected then argument
           else raise mismatch function "different literal head" end
      fun accepts observe current =
        (ignore (observe current);true)
        handle primary => if is_mismatch primary then false else raise primary
      fun optional observe current = SOME (observe current)
        handle primary => if is_mismatch primary then NONE else raise primary
      (* Only the pure type inspection is inside this selective boundary;
         carrier type_of/authentication failures never enter it. *)
      fun inspect_type inspect ty = inspect ty
        handle primary => raise library_mismatch primary
      val dim_of = memo (fn current =>
        let val ty = (#type_of context) current
        in inspect_type wordsSyntax.dest_word_type ty end)
      val dest_bits = memo_recursive (fn bits => fn current =>
            if matches current numSyntax.alt_zero_tm then Arbnum.zero
            else
              let val (head,argument) = application "dest_numeral" current
              in if matches head numSyntax.bit1_tm then
                   Arbnum.+ (Arbnum.* (Arbnum.two,bits argument),Arbnum.one)
                 else if matches head numSyntax.bit2_tm then
                   Arbnum.+ (Arbnum.* (Arbnum.two,bits argument),Arbnum.two)
                 else raise mismatch "dest_numeral" "not numeral bits"
              end)
      val dest_numeral = memo (fn current =>
        if matches current numSyntax.zero_tm then Arbnum.zero
        else dest_bits (unary "dest_numeral" numSyntax.numeral_tm current))
      fun is_negated head current =
        accepts (unary "is_negated" head) current
      val int_of_term = memo_recursive (fn integer => fn current =>
            let val (head,argument) = application "int_of_term" current
            in if matches head intSyntax.negate_tm then
                 Arbint.~ (integer argument)
               else if matches head intSyntax.int_injection then
                 Arbint.fromNat (dest_numeral argument)
               else raise mismatch "int_of_term" "not an integer literal"
            end)
      val is_real_literal = memo_recursive (fn real => fn current =>
        case optional (unary "is_real_literal" realSyntax.negate_tm)
            current of
          SOME argument => real argument
        | NONE => accepts (fn current => dest_numeral
            (unary "is_real_literal" realSyntax.real_injection current))
            current)
      val real_int_of_term = memo (fn current =>
        let
          val negative = optional
            (unary "real_int_of_term" realSyntax.negate_tm) current
          val number = case negative of NONE => current | SOME value => value
          val value = Arbint.fromNat (dest_numeral
            (unary "real_int_of_term" realSyntax.real_injection number))
        in case negative of NONE => value | SOME _ => Arbint.~ value end)
      val dest_word_literal = memo (fn current =>
        let val argument = unary "dest_word_literal" wordsSyntax.n2w_tm current
            val _ = dim_of current
        in dest_numeral argument end)
      val list_elements = memo_recursive (fn elements => fn current =>
            case optional (fn current =>
                let val (prefix,tail) = application "dest_list" current
                    val head = unary "dest_list" listSyntax.cons_tm prefix
                in (head,tail) end) current of
              SOME (head,tail) => head :: elements tail
            | NONE => if matches current listSyntax.nil_tm then []
                else raise mismatch "dest_list" "not a list")
      val dest_list = memo (fn current =>
        let
          val values = list_elements current
          val ty = (#type_of context) current
          val element_type = inspect_type listSyntax.dest_list_type ty
        in (values,element_type) end)
      fun list_mk_comb (head,arguments) =
        ((#key context) head;
         List.foldl (fn (argument,function) =>
           (#mk_comb context) (function,argument)) head arguments)
      fun mk_integer value =
        let
          fun positive value =
            let
              val numeral = Literal.gen_mk_numeral
                {mk_comb= #mk_comb context,
                 ZERO=(#constant context) numSyntax.zero_tm,
                 ALT_ZERO=(#constant context) numSyntax.alt_zero_tm,
                 NUMERAL=(#constant context) numSyntax.numeral_tm,
                 BIT1=(#constant context) numSyntax.bit1_tm,
                 BIT2=(#constant context) numSyntax.bit2_tm}
                (Arbint.toNat value)
            in (#mk_comb context)
              ((#constant context) intSyntax.int_injection,numeral) end
        in if Arbint.< (value,Arbint.zero) then
             (#mk_comb context) ((#constant context) intSyntax.negate_tm,
               positive (Arbint.~ value))
           else positive value
        end
    in
      {type_of= #type_of context,dest_list=dest_list,
       dest_numeral=dest_numeral,is_int_literal=accepts int_of_term,
       is_int_negated=is_negated intSyntax.negate_tm,
       int_of_term=int_of_term,is_real_literal=is_real_literal,
       is_real_negated=is_negated realSyntax.negate_tm,
       real_int_of_term=real_int_of_term,
       is_word_literal=accepts dest_word_literal,
       dest_word_literal=dest_word_literal,dim_of=dim_of,
       constant= #constant context,mk_comb= #mk_comb context,
       list_mk_comb=list_mk_comb,mk_integer=mk_integer,
       is_syntax_error=is_mismatch,syntax_error=mismatch,
       library_syntax_error=library_mismatch}
    end

  fun native_builtin_operations (context:Q.native_context) =
    native_builtin_operations_with_syntax
      {view= #view context,key= #key context,type_of= #type_of context,
       constant= #constant context,mk_comb= #mk_comb context}

  fun outbound_builtin_operations (context:Q.outbound_context) =
    native_builtin_operations_with_syntax
      {view= #view context,key= #key context,type_of= #type_of context,
       constant= #constant context,mk_comb= #mk_comb context}

  fun native_query_builtin_encoder_with_syntax
      (context:native_builtin_syntax) =
    let val operations = native_builtin_operations_with_syntax context
        fun constant_leaf current = case (#view context) current of
            Q.ConstantView atom => SOME atom
          | _ => NONE
    in native_builtin_encoder operations
      {constant_leaf=constant_leaf,is_mismatch=is_mismatch} end

  fun native_query_builtin_encoder (context:Q.native_context) =
    native_query_builtin_encoder_with_syntax
      {view= #view context,key= #key context,type_of= #type_of context,
       constant= #constant context,mk_comb= #mk_comb context}

  fun outbound_query_builtin_encoder (context:Q.outbound_context) =
    native_query_builtin_encoder_with_syntax
      {view= #view context,key= #key context,type_of= #type_of context,
       constant= #constant context,mk_comb= #mk_comb context}

  type native_collection_syntax =
    {view:Q.carrier -> Q.carrier_view,key:Q.carrier -> int * int,
     type_of:Q.carrier -> Type.hol_type,constant:Term.term -> Q.carrier,
     mk_comb:Q.carrier * Q.carrier -> Q.carrier,
     same:Q.carrier * Q.carrier -> bool,
     strip_comb:Q.carrier -> Q.carrier * Q.carrier list}

  fun native_collection_recognition_operations_with_syntax
      (context:native_collection_syntax)
      : Q.carrier SmtLib.outbound_collection_recognition_operations =
    let
      val builtins = native_builtin_operations_with_syntax
        {view= #view context,key= #key context,type_of= #type_of context,
         constant= #constant context,mk_comb= #mk_comb context}
      fun application current = case (#view context) current of
          Q.ApplicationView operands => operands
        | _ => raise mismatch "collection_syntax" "application expected"
      fun same_const current expected = case (#view context) current of
          Q.ConstantView atom => Library.same_const atom expected
        | _ => false
      fun unary expected current =
        let val (head,argument) = application current
        in if same_const head expected then argument
           else raise mismatch "collection_syntax" "different unary head"
        end
      fun binary expected current =
        let val (prefix,right) = application current
            val (head,left) = application prefix
        in if same_const head expected then (left,right)
           else raise mismatch "collection_syntax" "different binary head"
        end
      fun conditional current =
        let val (prefix,right) = application current
            val (test,left) = binary boolSyntax.conditional prefix
        in (test,left,right) end
      fun accepts observe current = (ignore (observe current);true)
        handle primary => if is_mismatch primary then false else raise primary
      fun inspect_type inspect ty = inspect ty
        handle primary => raise library_mismatch primary
      fun nil_type current =
        if same_const current listSyntax.nil_tm then
          let val ty = (#type_of context) current
          in inspect_type listSyntax.dest_list_type ty end
        else raise mismatch "collection_syntax" "NIL expected"
      fun element_type current =
        if SmtLib.outbound_is_native_sequence_type
            ((#type_of context) current) then
          let val ty = (#type_of context) current
          in inspect_type listSyntax.dest_list_type ty end
        else raise mismatch "sequence_element_type"
          "not a native sequence term"
      (* Instantiate only a stock atomic head. Read authenticated operand
         types BEFORE the isolated pure matching/instantiation boundary;
         construction and its native guards also remain outside it. *)
      fun apply_known (head,arguments) =
        let
          val argument_types = List.map (#type_of context) arguments
          val atom =
            (let
               val _ = if Term.is_const head then () else
                 raise mismatch "collection_syntax" "stock constant required"
               fun match ty [] substitutions = substitutions
                 | match ty (argument_ty :: rest) substitutions =
                     let val (domain,range) = Type.dom_rng ty
                         val substitutions = Type.match_type_in_context
                           domain argument_ty substitutions
                     in match range rest substitutions end
             in Term.inst (match (Term.type_of head) argument_types []) head
             end
             handle Feedback.HOL_ERR _ =>
               raise mismatch "collection_syntax" "stock head type mismatch")
          val constant = (#constant context) atom
        in (#list_mk_comb builtins) (constant,arguments) end
      fun disjunction (left,right) =
        apply_known (boolSyntax.disjunction,[left,right])
      fun disjunctions [] =
            raise mismatch "collection_syntax" "empty disjunction"
        | disjunctions [current] = ((#key context) current;current)
        | disjunctions (current :: rest) =
            disjunction (current,disjunctions rest)
      fun set_head current = case (#view context) current of
          Q.ConstantView atom => SmtLib.outbound_is_native_set_head atom
        | _ => false
    in
      {type_of= #type_of context,same_const=same_const,
       is_native_set_head=set_head,
       same=fn left => fn right => (#same context) (left,right),
       strip_comb= #strip_comb context,dest_comb=application,
       dest_cond=conditional,dest_take=binary listSyntax.take_tm,
       dest_drop=binary listSyntax.drop_tm,dest_Num=unary intSyntax.Num_tm,
       dest_cons=binary listSyntax.cons_tm,dest_el=binary listSyntax.el_tm,
       is_nil=accepts nil_type,dest_nil=nil_type,
       sequence_element_type=element_type,
       int_less=fn (left,right) =>
         apply_known (intSyntax.less_tm,[left,right]),
       int_leq=fn (left,right) =>
         apply_known (intSyntax.leq_tm,[left,right]),
       num_leq=fn (left,right) =>
         apply_known (numSyntax.leq_tm,[left,right]),
       length=fn current => apply_known (listSyntax.length_tm,[current]),
       disjunction=disjunction,disjunctions=disjunctions,
       int_zero=fn () => (#mk_integer builtins) Arbint.zero,
       mk_comb= #mk_comb context,list_mk_comb= #list_mk_comb builtins,
       set_card=accepts (unary pred_setSyntax.card_tm),
       bag_card=accepts (unary bagSyntax.BAG_CARD_tm),
       optional_error=is_mismatch,syntax_error=mismatch}
    end

  fun native_collection_recognition_operations (context:Q.native_context) =
    native_collection_recognition_operations_with_syntax
      {view= #view context,key= #key context,type_of= #type_of context,
       constant= #constant context,mk_comb= #mk_comb context,
       same= #same context,strip_comb= #strip_comb context}

  fun outbound_collection_recognition_operations (context:Q.outbound_context) =
    native_collection_recognition_operations_with_syntax
      {view= #view context,key= #key context,type_of= #type_of context,
       constant= #constant context,mk_comb= #mk_comb context,
       same= #same context,strip_comb= #strip_comb context}

  fun native_query_collection_recognizers_with_syntax
      (context:native_collection_syntax) is_raw_number {sequence_emission} =
    let
      val operations =
        native_collection_recognition_operations_with_syntax context
      val {string_nth_shape,seq_extract_shape,seq_at_shape,sequence_symbol,
           set_symbol,bag_symbol,bag_count_application} =
        SmtLib.outbound_collection_recognizers operations
          {sequence_emission=fn () => sequence_emission,
           is_raw_number=is_raw_number}
      fun guard current = ignore ((#key context) current)
      fun one observe current =
        (guard current;
         let val result = observe current val _ = guard current
         in result end)
      fun application observe head arguments =
        let val _ = guard head val _ = List.app guard arguments
            val result = observe head arguments
            val _ = guard head val _ = List.app guard arguments
        in result end
      fun sequence current head arguments =
        (guard current;
         let val result = application (sequence_symbol current) head arguments
             val _ = guard current
         in result end)
    in
      {string_nth_shape=one string_nth_shape,
       seq_extract_shape=one seq_extract_shape,seq_at_shape=one seq_at_shape,
       sequence_symbol=sequence,set_symbol=application set_symbol,
       bag_symbol=application bag_symbol,
       bag_count_application=application bag_count_application}
    end

  fun native_query_collection_recognizers (context:Q.native_context)
      {sequence_emission} =
    native_query_collection_recognizers_with_syntax
      {view= #view context,key= #key context,type_of= #type_of context,
       constant= #constant context,mk_comb= #mk_comb context,
       same= #same context,strip_comb= #strip_comb context}
      (#is_raw_number context) {sequence_emission=sequence_emission}

  fun outbound_query_collection_recognizers (context:Q.outbound_context)
      {sequence_emission} =
    native_query_collection_recognizers_with_syntax
      {view= #view context,key= #key context,type_of= #type_of context,
       constant= #constant context,mk_comb= #mk_comb context,
       same= #same context,strip_comb= #strip_comb context}
      (#is_raw_number context) {sequence_emission=sequence_emission}

  (* This is the shared native selection stage, not a serializer. Preparing
     a node observes its base type once; the whole/application thunks stay
     separate and do not inspect a decomposed spine until it is requested.
     A selected equality has a committed continuation: its callback failure
     escapes unchanged rather than becoming a different symbol candidate. *)
  fun native_query_dispatch (context:Q.native_context)
      {sequence_emission,regime} =
    let
      fun guard current = ignore ((#key context) current)
      fun inputs head arguments = (guard head;List.app guard arguments)
      fun same_const current expected = case (#view context) current of
          Q.ConstantView atom => Library.same_const atom expected
        | _ => false
      fun is_constant current = case (#view context) current of
          Q.ConstantView _ => true | _ => false
      fun declared_arity current = case (#view context) current of
          Q.ConstantView atom => SmtLib.outbound_constant_arity atom
        | _ => raise mismatch "native_dispatch" "constant head required"
      val operations : Q.carrier SmtLib.outbound_native_dispatch_operations =
        {same_const=same_const,is_constant=is_constant,
         declared_arity=declared_arity,type_of= #type_of context,
         is_raw_number= #is_raw_number context,syntax_error=mismatch}
      val dispatch = SmtLib.outbound_native_dispatch operations
        (native_query_collection_recognizers context
          {sequence_emission=sequence_emission}) regime
      val encode = native_query_builtin_encoder context
      fun prepare current =
        let
          val _ = guard current
          val ty = (#type_of context) current
          val base_type =
            (ignore (Type.dom_rng ty);false)
            handle Feedback.HOL_ERR _ => true
          fun whole () =
            (guard current;
             let val result = (#whole_candidate dispatch) base_type current
                 val _ = guard current
             in result end)
          fun application () =
            let val _ = guard current
                val (head,arguments) = (#strip_comb context) current
                val result = (#application_candidate dispatch)
                  base_type current head arguments
                val _ = guard current
            in result end
        in {whole=whole,application=application} end
      fun builtin current (head,arguments) =
        let val _ = guard current val _ = inputs head arguments
            val _ = (#guard_builtin dispatch) current head
            val result = encode (head,arguments)
            val _ = guard current val _ = inputs head arguments
        in result end
      fun equality_operands (head,arguments) =
        let val _ = inputs head arguments
            val result as (left,right) =
              (#equality_operands dispatch) head arguments
            val _ = guard left val _ = guard right
        in result end
      fun with_equality action input =
        let val operands as (left,right) = equality_operands input
            val result = action operands
            val _ = guard left val _ = guard right
        in result end
    in
      {prepare=prepare,builtin=builtin,equality_operands=equality_operands,
       with_equality=with_equality}
    end
  end

  (* Reuse the outbound registry at genuine constant leaves. No whole graph
     representative is reconstructed or inspected by these callbacks. *)
  fun native_query_syntax graph : Q.native_syntax =
    let
      fun constant node =
        case G.view graph node of
          G.Constant _ => G.representative graph node
        | _ => raise ERR "native_query_syntax" "constant leaf required"
      fun matches node expected = Library.same_const (constant node) expected
      fun set_role {head,atomic} =
        let val atom = constant head
        in SmtLib.outbound_set_marker_role (Library.same_const atom)
          (fn () => atomic andalso pred_setSyntax.is_empty atom)
          (fn () => atomic andalso pred_setSyntax.is_univ atom) () end
      fun bag_role {head,atomic} =
        let val atom = constant head
        in SmtLib.outbound_bag_marker_role (Library.same_const atom)
          (fn () => atomic andalso bagSyntax.is_empty atom) () end
    in
      {set_role=set_role,bag_role=bag_role,
       is_set_type=SmtLib.outbound_is_set_type,
       is_bag_type=SmtLib.outbound_is_bag_type,
       is_cond=fn node => matches node boolSyntax.conditional,
       is_let=fn node => matches node boolSyntax.let_tm,
       is_uncurry=fn node => matches node pairSyntax.uncurry_tm,
       pair_constant=SmtLib.outbound_pair_constant,
       is_integer_coercion=fn node =>
         SmtLib.outbound_is_integer_coercion (constant node),
       is_num_head=fn node => SmtLib.outbound_is_num_head (constant node),
       is_bag_card_head=fn node =>
         SmtLib.outbound_is_bag_card_head (constant node),
       number_type=SmtLib.outbound_number_type}
    end

  fun native_query_options_with_policy expected query open_opaque =
    let
        val {graph,...} = SmtLib_GraphPreprocess.query_nodes_with_policy_for
          expected query
        fun arity node = case G.view graph node of
            G.Constant _ =>
              SmtLib.outbound_constant_arity (G.representative graph node)
          | _ => raise ERR "analyse_native_query_with_policy"
              "constant leaf required"
    in {syntax=native_query_syntax graph,declared_const_arity=arity,
        open_opaque=open_opaque} end

  fun analyse_native_query_with_policy expected query open_opaque =
    (Q.analyse_native_collections_with_policy expected query
       (native_query_options_with_policy expected query open_opaque)
     handle primary => (SmtReplayInvocationWork.close expected;raise primary))

  fun with_native_query_analysis_with_policy expected query open_opaque action =
    (Q.with_native_analysis_with_policy expected query
       (native_query_options_with_policy expected query open_opaque) action
     handle primary => (SmtReplayInvocationWork.close expected;raise primary))

  fun with_outbound_query_analysis_with_policy expected query open_opaque
      action =
    (Q.with_outbound_analysis_with_policy expected query
       (native_query_options_with_policy expected query open_opaque) action
     handle primary => (SmtReplayInvocationWork.close expected;raise primary))

  fun with_outbound_seeded_query_analysis_with_policy expected query
      open_opaque seeds action =
    (Q.with_outbound_seeded_analysis_with_policy expected query
       (native_query_options_with_policy expected query open_opaque)
       seeds action
     handle primary => (SmtReplayInvocationWork.close expected;raise primary))

end
