(* Copyright (c) 2010-2011 Tjark Weber. All rights reserved. *)

(* Parsing of SMT-LIB 2 benchmarks *)

structure SmtLib_Parser =
struct

  type 'a parse_fn = string -> Term.term list -> 'a list -> 'a

  type 'a dict = (string, 'a parse_fn list) Redblackmap.dict

  type dicts = Type.hol_type dict * Term.term dict

  type bindings = (string * Term.term * Term.term) list

  type source_pos = {line: int, column: int, offset: int}

  datatype source_span =
    SourceSpan of {start: source_pos, stop: source_pos}

  datatype 'a located =
    Located of {loc: source_span, node: 'a}

  datatype sexp_ast =
      SexpAtom of string
    | SexpList of sexp_ast located list

  datatype sort_ast =
      SortIdentifier of string
    | SortIndexed of string located * string located list
    | SortApply of string located * sort_ast located list

  datatype term_ast =
      TermIdentifier of string
    | TermIndexed of string located * term_ast located list
    | TermApply of term_ast located * term_ast located list
    | TermLet of (string located * term_ast located) list * term_ast located
    | TermForall of sorted_var_ast located list * term_ast located
    | TermExists of sorted_var_ast located list * term_ast located
    | TermAnnotated of term_ast located * sexp_ast located list
  and sorted_var_ast =
      SortedVar of string located * sort_ast located

  datatype datatype_selector_ast =
      DatatypeSelector of string located * sort_ast located

  datatype datatype_tester_ast =
      DatatypeTester of string located

  datatype datatype_constructor_ast =
      DatatypeConstructor of string located * datatype_tester_ast located *
        datatype_selector_ast located list

  datatype datatype_decl_ast =
      DatatypeDecl of string located list * datatype_constructor_ast located list

  datatype datatype_binding_ast =
      DatatypeBinding of string located * string located

  datatype function_signature_ast =
      FunctionSignature of string located * sorted_var_ast located list *
        sort_ast located

  datatype command_ast =
      CmdSetInfo of sexp_ast located list
    | CmdSetOption of sexp_ast located list
    | CmdSetLogic of string located
    | CmdGetInfo of string located
    | CmdGetOption of string located
    | CmdDeclareSort of string located * string located
    | CmdDefineSort of string located * string located list * sort_ast located
    | CmdDeclareConst of string located * sort_ast located
    | CmdDeclareFun of string located * sort_ast located list * sort_ast located
    | CmdDefineConst of string located * sort_ast located * term_ast located
    | CmdDefineFun of string located * sorted_var_ast located list *
        sort_ast located * term_ast located
    | CmdDefineFunRec of string located * sorted_var_ast located list *
        sort_ast located * term_ast located
    | CmdDefineFunsRec of function_signature_ast located list *
        term_ast located list
    | CmdDeclareDatatype of string located * datatype_decl_ast located
    | CmdDeclareDatatypes of datatype_binding_ast located list *
        datatype_decl_ast located list
    | CmdAssert of term_ast located
    | CmdPush of string located option
    | CmdPop of string located option
    | CmdReset
    | CmdResetAssertions
    | CmdCheckSat
    | CmdCheckSatAssuming of term_ast located list
    | CmdGetProof
    | CmdGetUnsatAssumptions
    | CmdGetUnsatCore
    | CmdGetModel
    | CmdGetValue of term_ast located list
    | CmdGetAssignment
    | CmdGetAssertions
    | CmdEcho of string located
    | CmdExit
    | CmdUnknown of string located * sexp_ast located list

  type script_ast = command_ast located list

  type parser_cfg = {
    mk_let_bindings: dicts * bindings -> Term.term dict,
    mk_let: bindings * Term.term -> Term.term,
    parse_lambda: bool
  }

  datatype query_command =
      QueryCheckSat of Term.term list
    | QueryGetProof
    | QueryGetUnsatAssumptions
    | QueryGetUnsatCore
    | QueryGetModel
    | QueryGetValue of Term.term list
    | QueryGetAssignment
    | QueryGetAssertions

  type command_state_snapshot = {
    logic: string,
    tydict: Type.hol_type dict,
    tmdict: Term.term dict,
    assertions: Term.term list,
    named_assertions: (string * Term.term) list,
    local_definitions: Term.term list,
    queries: query_command list
  }

  type checked_script = command_state_snapshot

local

  val ERR = Feedback.mk_HOL_ERR "SmtLib_Parser"
  val WARNING = Feedback.HOL_WARNING "SmtLib_Parser"

  (***************************************************************************)
  (* source-located SMT-LIB script AST                                       *)
  (***************************************************************************)

  fun loc_of (Located {loc, ...}) = loc
  fun node_of (Located {node, ...}) = node

  fun span_start (SourceSpan {start, ...}) = start
  fun span_stop (SourceSpan {stop, ...}) = stop

  fun source_pos_to_string ({line, column, ...}: source_pos) =
    "line " ^ Int.toString line ^ ", column " ^ Int.toString column

  fun source_span_to_string span =
    source_pos_to_string (span_start span)

  fun combine_span start_span stop_span =
    SourceSpan {start = span_start start_span, stop = span_stop stop_span}

  fun located loc node = Located {loc = loc, node = node}

  datatype located_token = Token of {text: string, loc: source_span}

  fun token_text (Token {text, ...}) = text
  fun token_loc (Token {loc, ...}) = loc

  fun syntax_error fn_name loc msg =
    raise ERR fn_name (msg ^ " at " ^ source_span_to_string loc)

  fun mk_point_span pos = SourceSpan {start = pos, stop = pos}

  fun make_located_tokenizer (text: string) : unit -> located_token option =
  let
    val len = String.size text
    val index = ref 0
    val line = ref 1
    val column = ref 1

    fun pos () = {line = !line, column = !column, offset = !index}

    fun peek () =
      if !index >= len then NONE else SOME (String.sub (text, !index))

    fun advance () =
      case peek () of
        NONE => NONE
      | SOME c =>
          (index := !index + 1;
           if c = #"\n" then (line := !line + 1; column := 1)
           else column := !column + 1;
           SOME c)

    fun skip_comment () =
      case advance () of
        NONE => ()
      | SOME #"\n" => ()
      | SOME _ => skip_comment ()

    fun skip_space_and_comments () =
      case peek () of
        SOME #" " => (ignore (advance ()); skip_space_and_comments ())
      | SOME #"\t" => (ignore (advance ()); skip_space_and_comments ())
      | SOME #"\n" => (ignore (advance ()); skip_space_and_comments ())
      | SOME #"\r" => (ignore (advance ()); skip_space_and_comments ())
      | SOME #";" => (skip_comment (); skip_space_and_comments ())
      | _ => ()

    fun token start chars =
      Token {text = String.implode (List.rev chars),
             loc = SourceSpan {start = start, stop = pos ()}}

    fun atom start chars =
      case peek () of
        NONE => token start chars
      | SOME c =>
          if c = #" " orelse c = #"\t" orelse c = #"\n" orelse
             c = #"\r" orelse c = #"(" orelse c = #")" orelse c = #";"
          then token start chars
          else (ignore (advance ()); atom start (c :: chars))

    fun quoted_symbol start chars =
      case advance () of
        NONE => syntax_error "get_token" (mk_point_span (pos ()))
          "unterminated quoted symbol"
      | SOME #"|" => token start chars
      | SOME c => quoted_symbol start (c :: chars)

    fun string_lit start chars =
      case advance () of
        NONE => syntax_error "get_token" (mk_point_span (pos ()))
          "unterminated string literal"
      | SOME #"\"" => token start chars
      | SOME #"\\" =>
          (case advance () of
             NONE => syntax_error "get_token" (mk_point_span (pos ()))
               "unterminated string escape"
           | SOME c => string_lit start (c :: chars))
      | SOME c => string_lit start (c :: chars)
  in
    fn () =>
      (skip_space_and_comments ();
       case peek () of
         NONE => NONE
       | SOME #"(" =>
           let val start = pos ()
               val _ = advance ()
           in SOME (token start [#"("]) end
       | SOME #")" =>
           let val start = pos ()
               val _ = advance ()
           in SOME (token start [#")"]) end
       | SOME #"|" =>
           let val start = pos ()
               val _ = advance ()
           in SOME (quoted_symbol start []) end
       | SOME #"\"" =>
           let val start = pos ()
               val _ = advance ()
           in SOME (string_lit start []) end
       | SOME c =>
           let val start = pos ()
               val _ = advance ()
           in SOME (atom start [c]) end)
  end

  fun parse_script_tokens next_token : script_ast =
  let
    val last_loc =
      ref (mk_point_span {line = 1, column = 1, offset = 0})

    fun get_next_token () =
      case next_token () of
        NONE => NONE
      | SOME tok => (last_loc := token_loc tok; SOME tok)

    fun eof_loc () =
      !last_loc

    fun need_token fn_name what =
      case get_next_token () of
        SOME tok => tok
      | NONE => syntax_error fn_name (eof_loc ()) ("expected " ^ what)

    fun expect_token fn_name expected tok =
      if token_text tok = expected then ()
      else syntax_error fn_name (token_loc tok)
        ("expected '" ^ expected ^ "', found '" ^ token_text tok ^ "'")

    fun parse_atom_name fn_name tok =
      if token_text tok = "(" orelse token_text tok = ")" then
        syntax_error fn_name (token_loc tok)
          ("expected atom, found '" ^ token_text tok ^ "'")
      else located (token_loc tok) (token_text tok)

    fun parse_until_rparen fn_name parse_item acc =
      let
        val tok = need_token fn_name "')'"
      in
        if token_text tok = ")" then
          (List.rev acc, tok)
        else
          parse_until_rparen fn_name parse_item (parse_item tok :: acc)
      end

    fun parse_sexp_from_first tok =
      if token_text tok = "(" then
        let
          val (items, close_tok) =
            parse_until_rparen "parse_sexp" parse_sexp_from_first []
          val loc = combine_span (token_loc tok) (token_loc close_tok)
        in
          located loc (SexpList items)
        end
      else if token_text tok = ")" then
        syntax_error "parse_sexp" (token_loc tok) "unexpected ')'"
      else
        located (token_loc tok) (SexpAtom (token_text tok))

    fun parse_sort_from_first tok =
      if token_text tok = "(" then
        let
          val head_tok = need_token "parse_sort" "sort head"
        in
          if token_text head_tok = "_" then
            let
              val name = parse_atom_name "parse_sort" (need_token "parse_sort" "indexed sort name")
              fun indices acc =
                let val tok = need_token "parse_sort" "')'"
                in
                  if token_text tok = ")" then (List.rev acc, tok)
                  else indices (parse_atom_name "parse_sort" tok :: acc)
                end
              val (idxs, close_tok) = indices []
              val loc = combine_span (token_loc tok) (token_loc close_tok)
            in
              located loc (SortIndexed (name, idxs))
            end
          else if token_text head_tok = ")" then
            syntax_error "parse_sort" (token_loc head_tok) "empty sort application"
          else
            let
              val head = parse_atom_name "parse_sort" head_tok
              val (args, close_tok) =
                parse_until_rparen "parse_sort" parse_sort_from_first []
              val loc = combine_span (token_loc tok) (token_loc close_tok)
            in
              located loc (SortApply (head, args))
            end
        end
      else if token_text tok = ")" then
        syntax_error "parse_sort" (token_loc tok) "unexpected ')'"
      else
        located (token_loc tok) (SortIdentifier (token_text tok))

    fun parse_sort () =
      parse_sort_from_first (need_token "parse_sort" "sort")

    fun parse_sorted_var_from_first tok =
      let
        val _ = expect_token "parse_sorted_var" "(" tok
        val name = parse_atom_name "parse_sorted_var"
          (need_token "parse_sorted_var" "variable name")
        val sort = parse_sort ()
        val close_tok = need_token "parse_sorted_var" "')'"
        val _ = expect_token "parse_sorted_var" ")" close_tok
        val loc = combine_span (token_loc tok) (token_loc close_tok)
      in
        located loc (SortedVar (name, sort))
      end

    fun parse_sorted_var_list () =
      let
        val open_tok = need_token "parse_sorted_var_list" "'('"
        val _ = expect_token "parse_sorted_var_list" "(" open_tok
        val (vars, _) =
          parse_until_rparen "parse_sorted_var_list"
            parse_sorted_var_from_first []
      in
        vars
      end

    fun parse_term_from_first tok =
      if token_text tok = "(" then
        parse_term_list tok
      else if token_text tok = ")" then
        syntax_error "parse_term" (token_loc tok) "unexpected ')'"
      else
        located (token_loc tok) (TermIdentifier (token_text tok))

    and parse_term_list open_tok =
      let
        val head_tok = need_token "parse_term" "term head"
        val head_text = token_text head_tok
      in
        if head_text = "_" then
          let
            val name = parse_atom_name "parse_term"
              (need_token "parse_term" "indexed term name")
            val (indices, close_tok) =
              parse_until_rparen "parse_term" parse_term_from_first []
            val loc = combine_span (token_loc open_tok) (token_loc close_tok)
          in
            located loc (TermIndexed (name, indices))
          end
        else if head_text = "let" then
          let
            val bindings_open = need_token "parse_term" "'('"
            val _ = expect_token "parse_term" "(" bindings_open
            fun parse_binding tok =
              let
                val _ = expect_token "parse_term" "(" tok
                val name = parse_atom_name "parse_term"
                  (need_token "parse_term" "let binding name")
                val term = parse_term_from_first (need_token "parse_term" "let binding term")
                val close_tok = need_token "parse_term" "')'"
                val _ = expect_token "parse_term" ")" close_tok
              in
                (name, term)
              end
            val (bindings, _) =
              parse_until_rparen "parse_term" parse_binding []
            val body = parse_term_from_first (need_token "parse_term" "let body")
            val close_tok = need_token "parse_term" "')'"
            val _ = expect_token "parse_term" ")" close_tok
            val loc = combine_span (token_loc open_tok) (token_loc close_tok)
          in
            located loc (TermLet (bindings, body))
          end
        else if head_text = "forall" orelse head_text = "exists" then
          let
            val vars = parse_sorted_var_list ()
            val body = parse_term_from_first (need_token "parse_term" "quantifier body")
            val close_tok = need_token "parse_term" "')'"
            val _ = expect_token "parse_term" ")" close_tok
            val loc = combine_span (token_loc open_tok) (token_loc close_tok)
          in
            if head_text = "forall" then
              located loc (TermForall (vars, body))
            else
              located loc (TermExists (vars, body))
          end
        else if head_text = "!" then
          let
            val term = parse_term_from_first (need_token "parse_term" "annotated term")
            val (attrs, close_tok) =
              parse_until_rparen "parse_term" parse_sexp_from_first []
            val loc = combine_span (token_loc open_tok) (token_loc close_tok)
          in
            located loc (TermAnnotated (term, attrs))
          end
        else
          let
            val head = parse_term_from_first head_tok
            val (args, close_tok) =
              parse_until_rparen "parse_term" parse_term_from_first []
            val loc = combine_span (token_loc open_tok) (token_loc close_tok)
          in
            located loc (TermApply (head, args))
          end
      end

    fun parse_sort_list () =
      let
        val open_tok = need_token "parse_sort_list" "'('"
        val _ = expect_token "parse_sort_list" "(" open_tok
        val (sorts, _) =
          parse_until_rparen "parse_sort_list" parse_sort_from_first []
      in
        sorts
      end

    fun parse_symbol_list () =
      let
        val open_tok = need_token "parse_symbol_list" "'('"
        val _ = expect_token "parse_symbol_list" "(" open_tok
        val (symbols, _) =
          parse_until_rparen "parse_symbol_list"
            (parse_atom_name "parse_symbol_list") []
      in
        symbols
      end

    fun parse_datatype_selector_from_first tok =
      let
        val _ = expect_token "parse_datatype_selector" "(" tok
        val name = parse_atom_name "parse_datatype_selector"
          (need_token "parse_datatype_selector" "selector name")
        val sort = parse_sort ()
        val close_tok = need_token "parse_datatype_selector" "')'"
        val _ = expect_token "parse_datatype_selector" ")" close_tok
        val loc = combine_span (token_loc tok) (token_loc close_tok)
      in
        located loc (DatatypeSelector (name, sort))
      end

    fun parse_datatype_constructor_from_first tok =
      let
        val _ = expect_token "parse_datatype_constructor" "(" tok
        val name = parse_atom_name "parse_datatype_constructor"
          (need_token "parse_datatype_constructor" "constructor name")
        fun parse_selector tok =
          if token_text tok = "(" then
            parse_datatype_selector_from_first tok
          else
            syntax_error "parse_datatype_constructor" (token_loc tok)
              ("expected selector declaration or ')', found '" ^
               token_text tok ^ "'")
        val (selectors, close_tok) =
          parse_until_rparen "parse_datatype_constructor" parse_selector []
        val loc = combine_span (token_loc tok) (token_loc close_tok)
        val tester = located (loc_of name) (DatatypeTester name)
      in
        located loc (DatatypeConstructor (name, tester, selectors))
      end

    fun parse_datatype_constructor_list_from_open open_tok =
      let
        val _ = expect_token "parse_datatype_constructor_list" "(" open_tok
        fun parse_constructor tok =
          if token_text tok = "(" then
            parse_datatype_constructor_from_first tok
          else
            syntax_error "parse_datatype_constructor_list" (token_loc tok)
              ("expected constructor declaration or ')', found '" ^
               token_text tok ^ "'")
        val (constructors, close_tok) =
          parse_until_rparen "parse_datatype_constructor_list"
            parse_constructor []
      in
        (constructors, close_tok)
      end

    fun parse_datatype_decl_from_first tok =
      let
        val _ = expect_token "parse_datatype_decl" "(" tok
        val next = need_token "parse_datatype_decl"
          "'par' or constructor declaration"
      in
        if token_text next = "par" then
          let
            val params = parse_symbol_list ()
            val ctors_open = need_token "parse_datatype_decl"
              "constructor declaration list"
            val (constructors, close_ctors) =
              parse_datatype_constructor_list_from_open ctors_open
            val close_tok = need_token "parse_datatype_decl" "')'"
            val _ = expect_token "parse_datatype_decl" ")" close_tok
            val loc = combine_span (token_loc tok) (token_loc close_tok)
          in
            located loc (DatatypeDecl (params, constructors))
          end
        else if token_text next = "(" then
          let
            val first_ctor = parse_datatype_constructor_from_first next
            fun parse_constructor tok =
              if token_text tok = "(" then
                parse_datatype_constructor_from_first tok
              else
                syntax_error "parse_datatype_decl" (token_loc tok)
                  ("expected constructor declaration or ')', found '" ^
                   token_text tok ^ "'")
            val (rest, close_tok) =
              parse_until_rparen "parse_datatype_decl" parse_constructor []
            val loc = combine_span (token_loc tok) (token_loc close_tok)
          in
            located loc (DatatypeDecl ([], first_ctor :: rest))
          end
        else
          syntax_error "parse_datatype_decl" (token_loc next)
            ("expected 'par' or constructor declaration, found '" ^
             token_text next ^ "'")
      end

    fun parse_datatype_binding_from_first tok =
      let
        val _ = expect_token "parse_datatype_binding" "(" tok
        val name = parse_atom_name "parse_datatype_binding"
          (need_token "parse_datatype_binding" "datatype name")
        val arity = parse_atom_name "parse_datatype_binding"
          (need_token "parse_datatype_binding" "datatype arity")
        val close_tok = need_token "parse_datatype_binding" "')'"
        val _ = expect_token "parse_datatype_binding" ")" close_tok
        val loc = combine_span (token_loc tok) (token_loc close_tok)
      in
        located loc (DatatypeBinding (name, arity))
      end

    fun parse_datatype_binding_list () =
      let
        val open_tok = need_token "parse_datatype_binding_list" "'('"
        val _ = expect_token "parse_datatype_binding_list" "(" open_tok
        val (bindings, _) =
          parse_until_rparen "parse_datatype_binding_list"
            parse_datatype_binding_from_first []
      in
        bindings
      end

    fun parse_datatype_decl_list () =
      let
        val open_tok = need_token "parse_datatype_decl_list" "'('"
        val _ = expect_token "parse_datatype_decl_list" "(" open_tok
        val (decls, _) =
          parse_until_rparen "parse_datatype_decl_list"
            parse_datatype_decl_from_first []
      in
        decls
      end

    fun parse_function_signature_from_first tok =
      let
        val _ = expect_token "parse_function_signature" "(" tok
        val name = parse_atom_name "parse_function_signature"
          (need_token "parse_function_signature" "function name")
        val vars = parse_sorted_var_list ()
        val range = parse_sort ()
        val close_tok = need_token "parse_function_signature" "')'"
        val _ = expect_token "parse_function_signature" ")" close_tok
        val loc = combine_span (token_loc tok) (token_loc close_tok)
      in
        located loc (FunctionSignature (name, vars, range))
      end

    fun parse_function_signature_list () =
      let
        val open_tok = need_token "parse_function_signature_list" "'('"
        val _ = expect_token "parse_function_signature_list" "(" open_tok
        val (sigs, _) =
          parse_until_rparen "parse_function_signature_list"
            parse_function_signature_from_first []
      in
        sigs
      end

    fun parse_term_list_ast () =
      let
        val open_tok = need_token "parse_term_list" "'('"
        val _ = expect_token "parse_term_list" "(" open_tok
        val (terms, _) =
          parse_until_rparen "parse_term_list" parse_term_from_first []
      in
        terms
      end

    fun parse_empty_command fn_name open_tok node =
      let
        val close_tok = need_token fn_name "')'"
        val _ = expect_token fn_name ")" close_tok
      in
        located (combine_span (token_loc open_tok) (token_loc close_tok)) node
      end

    fun parse_command_from_first open_tok =
      let
        val _ = expect_token "parse_command" "(" open_tok
        val cmd_tok = need_token "parse_command" "command name"
        val cmd = token_text cmd_tok
        fun command_error loc msg =
          syntax_error "parse_command" loc (cmd ^ ": " ^ msg)
        fun command_need what =
          case get_next_token () of
            SOME tok => tok
          | NONE => command_error (eof_loc ()) ("expected " ^ what)
        fun command_expect expected tok =
          if token_text tok = expected then ()
          else command_error (token_loc tok)
            ("expected '" ^ expected ^ "', found '" ^ token_text tok ^ "'")
        fun command_atom what =
          let val tok = command_need what
          in
            if token_text tok = "(" orelse token_text tok = ")" then
              command_error (token_loc tok)
                ("expected atom, found '" ^ token_text tok ^ "'")
            else
              located (token_loc tok) (token_text tok)
          end
        fun finish node close_tok =
          located (combine_span (token_loc open_tok) (token_loc close_tok)) node
        fun finish_with_close node =
          let
            val close_tok = command_need "')'"
            val _ = command_expect ")" close_tok
          in
            finish node close_tok
          end
        fun parse_optional_atom_command what mk =
          let
            val tok = command_need ("')' or " ^ what)
          in
            if token_text tok = ")" then
              finish (mk NONE) tok
            else if token_text tok = "(" then
              command_error (token_loc tok)
                ("expected atom, found '" ^ token_text tok ^ "'")
            else
              let
                val arg = located (token_loc tok) (token_text tok)
                val close_tok = command_need "')'"
                val _ = command_expect ")" close_tok
              in
                finish (mk (SOME arg)) close_tok
              end
          end
        fun parse_command_term_list what =
          let
            val open_args = command_need what
            val _ = command_expect "(" open_args
            val (terms, close_args) =
              parse_until_rparen "parse_command" parse_term_from_first []
            val close_tok = command_need "')'"
            val _ = command_expect ")" close_tok
          in
            (terms, close_tok)
          end
      in
        case cmd of
          "set-info" =>
            let val (items, close_tok) =
                  parse_until_rparen "parse_command" parse_sexp_from_first []
            in finish (CmdSetInfo items) close_tok end
        | "set-option" =>
            let val (items, close_tok) =
                  parse_until_rparen "parse_command" parse_sexp_from_first []
            in finish (CmdSetOption items) close_tok end
        | "set-logic" =>
            let
              val logic = command_atom "logic name"
              val close_tok = command_need "')'"
              val _ = command_expect ")" close_tok
            in
              finish (CmdSetLogic logic) close_tok
            end
        | "get-info" =>
            let
              val keyword = command_atom "info keyword"
            in
              finish_with_close (CmdGetInfo keyword)
            end
        | "get-option" =>
            let
              val keyword = command_atom "option keyword"
            in
              finish_with_close (CmdGetOption keyword)
            end
        | "declare-sort" =>
            let
              val name = command_atom "sort name"
              val arity = command_atom "sort arity"
              val close_tok = command_need "')'"
              val _ = command_expect ")" close_tok
            in
              finish (CmdDeclareSort (name, arity)) close_tok
            end
        | "define-sort" =>
            let
              val name = command_atom "sort name"
              val params = parse_symbol_list ()
              val body = parse_sort ()
            in
              finish_with_close (CmdDefineSort (name, params, body))
            end
        | "declare-const" =>
            let
              val name = command_atom "constant name"
              val sort = parse_sort ()
              val close_tok = command_need "')'"
              val _ = command_expect ")" close_tok
            in
              finish (CmdDeclareConst (name, sort)) close_tok
            end
        | "declare-fun" =>
            let
              val name = command_atom "function name"
              val domain = parse_sort_list ()
              val range = parse_sort ()
              val close_tok = command_need "')'"
              val _ = command_expect ")" close_tok
            in
              finish (CmdDeclareFun (name, domain, range)) close_tok
            end
        | "define-const" =>
            let
              val name = command_atom "constant name"
              val sort = parse_sort ()
              val body = parse_term_from_first
                (command_need "constant definition body")
            in
              finish_with_close (CmdDefineConst (name, sort, body))
            end
        | "define-fun" =>
            let
              val name = command_atom "function name"
              val vars = parse_sorted_var_list ()
              val range = parse_sort ()
              val body = parse_term_from_first (command_need "function body")
              val close_tok = command_need "')'"
              val _ = command_expect ")" close_tok
            in
              finish (CmdDefineFun (name, vars, range, body)) close_tok
            end
        | "define-fun-rec" =>
            let
              val name = command_atom "recursive function name"
              val vars = parse_sorted_var_list ()
              val range = parse_sort ()
              val body = parse_term_from_first
                (command_need "recursive function body")
              val close_tok = command_need "')'"
              val _ = command_expect ")" close_tok
            in
              finish (CmdDefineFunRec (name, vars, range, body)) close_tok
            end
        | "define-funs-rec" =>
            let
              val sigs = parse_function_signature_list ()
              val bodies = parse_term_list_ast ()
              val close_tok = command_need "')'"
              val _ = command_expect ")" close_tok
            in
              finish (CmdDefineFunsRec (sigs, bodies)) close_tok
            end
        | "declare-datatype" =>
            let
              val name = command_atom "datatype name"
              val decl = parse_datatype_decl_from_first
                (command_need "datatype declaration")
              val close_tok = command_need "')'"
              val _ = command_expect ")" close_tok
            in
              finish (CmdDeclareDatatype (name, decl)) close_tok
            end
        | "declare-datatypes" =>
            let
              val bindings = parse_datatype_binding_list ()
              val decls = parse_datatype_decl_list ()
              val close_tok = command_need "')'"
              val _ = command_expect ")" close_tok
            in
              finish (CmdDeclareDatatypes (bindings, decls)) close_tok
            end
        | "assert" =>
            let
              val term = parse_term_from_first (command_need "assertion")
              val close_tok = command_need "')'"
              val _ = command_expect ")" close_tok
            in
              finish (CmdAssert term) close_tok
            end
        | "push" => parse_optional_atom_command "push level" CmdPush
        | "pop" => parse_optional_atom_command "pop level" CmdPop
        | "reset" => parse_empty_command "parse_command" open_tok CmdReset
        | "reset-assertions" =>
            parse_empty_command "parse_command" open_tok CmdResetAssertions
        | "check-sat" => parse_empty_command "parse_command" open_tok CmdCheckSat
        | "check-sat-assuming" =>
            let
              val (assumptions, close_tok) =
                parse_command_term_list "assumption list"
            in
              finish (CmdCheckSatAssuming assumptions) close_tok
            end
        | "get-proof" => parse_empty_command "parse_command" open_tok CmdGetProof
        | "get-unsat-assumptions" =>
            parse_empty_command "parse_command" open_tok CmdGetUnsatAssumptions
        | "get-unsat-core" =>
            parse_empty_command "parse_command" open_tok CmdGetUnsatCore
        | "get-model" => parse_empty_command "parse_command" open_tok CmdGetModel
        | "get-value" =>
            let
              val (terms, close_tok) =
                parse_command_term_list "value term list"
            in
              finish (CmdGetValue terms) close_tok
            end
        | "get-assignment" =>
            parse_empty_command "parse_command" open_tok CmdGetAssignment
        | "get-assertions" =>
            parse_empty_command "parse_command" open_tok CmdGetAssertions
        | "echo" =>
            let
              val msg = command_atom "echo string"
              val close_tok = command_need "')'"
              val _ = command_expect ")" close_tok
            in
              finish (CmdEcho msg) close_tok
            end
        | "exit" => parse_empty_command "parse_command" open_tok CmdExit
        | _ =>
            let val (payload, close_tok) =
                  parse_until_rparen "parse_command" parse_sexp_from_first []
            in
              finish (CmdUnknown (located (token_loc cmd_tok) cmd, payload))
                close_tok
            end
      end

    fun parse_commands acc =
      case get_next_token () of
        NONE => List.rev acc
      | SOME tok =>
          if token_text tok = "(" then
            parse_commands (parse_command_from_first tok :: acc)
          else
            syntax_error "parse_script" (token_loc tok)
              ("expected command, found '" ^ token_text tok ^ "'")
  in
    parse_commands []
  end

  fun parse_script_string text =
    parse_script_tokens (make_located_tokenizer text)

  fun parse_script_file path =
  let
    val instream = TextIO.openIn path
    val text = TextIO.inputAll instream
    val _ = TextIO.closeIn instream
  in
    parse_script_string text
  end

  (***************************************************************************)
  (* parsing of types/terms                                                  *)
  (***************************************************************************)

  (* 'parse_type' parses an SMT-LIB 2 type, returning a HOL4 type.

     'parse_term' parses an SMT-LIB 2 term, returning a HOL4 term.

     There are various requirements that affect the implementation:
     1. Parsing must be reasonably fast (i.e., dictionary-based, at
     least for most tokens). 2. The dictionary depends on the SMT-LIB
     logic, and possibly on local term definitions ("let"). 3. Due to
     overloading, there may be several dictionary entries for the same
     token. 4. Parsing a function symbol in some cases requires that
     the function arguments have been parsed (e.g., to instantiate
     types and to resolve overloading). 5. Parsing must deal with
     indexed identifiers, i.e., "(_ token m n ...)". 6. Parsing must
     deal with numerals. At least for these (but also for indexed
     tokens of the form tokenX, with X a numeral), a dictionary-based
     approach is not sufficient in general (but should still be used
     if possible).

     These are my solutions: 1. 'parse_term' takes a dictionary
     argument. 2. The dictionary is properly initialized by the
     caller. 3. The dictionary maps tokens to a list of parsing
     functions. 4. Each parsing function maps a (possibly empty) list
     of function arguments (parsed as HOL terms) to the HOL term that
     results from applying the (function corresponding to the) token
     to these arguments. It raises 'HOL_ERR' if the arguments are not
     valid. 'parse_term' uses the result of the first parsing function
     that does not raise 'HOL_ERR'. 5. Each parsing function
     additionally takes a list of indices, each one a `Term.term`. This
     list will be empty for non-indexed identifiers, and non-empty for
     indexed identifiers. Non-indexed identifiers are therefore
     parsed as a special case of indexed identifiers. This allows
     parsing functions for indexed and non-indexed identifiers to be
     stored in the same dictionary. 6. To deal with numerals and other
     tokens for which a dictionary-based approach is not sufficient,
     the dictionary additionally contains an entry for "_". If there
     is no dictionary entry for a token (or every parsing function in
     its dictionary entry raised 'HOL_ERR'), 'parse_term' uses the
     result of the first parsing function in the entry for "_" that
     does not raise 'HOL_ERR'. So the dictionary key "_" is NOT used
     for indexed identifiers (which are instead keyed by the first
     token following "_" in SMT-LIB syntax), but is instead used as a
     catch-all entry. The token itself is passed verbatim.

     FIXME: The current setup doesn't do implicit conversions
            properly. Certain SMT-LIB logics, e.g., AUFLIRA, insert
            implicit conversions, e.g., from Int to Real, under
            certain conditions. These could perhaps be inserted by
            'parse_compound_term' (below), only there is no way at the
            moment to tell 'parse_compound_term' what the conversions
            are, and when they should be applied.

     Some of the basic infrastructure for parsing types/terms is
     identical, but some of the high-level parsing functions
     necessarily differ: parsing terms requires two dictionaries (one
     for declared types, one for declared terms), while parsing types
     only requires one dictionary (for declared types). *)

  fun t_with_args dict (token : string) (indices : Term.term list)
      (args : 'a list) : 'a =
    Lib.tryfind (fn f => f token indices args) (Redblackmap.find (dict, token)
      handle Redblackmap.NotFound => [])
    handle Feedback.HOL_ERR _ =>
    (* catch-all *)
    Lib.tryfind (fn f => f token indices args) (Redblackmap.find (dict, "_")
      handle Redblackmap.NotFound => [])
    handle Feedback.HOL_ERR _ =>
      raise ERR "t_with_args" ("failed to parse '" ^ token ^
        "' (with indices [" ^ String.concatWith ", "
        (List.map Hol_pp.term_to_string indices) ^ "] and " ^
        Int.toString (List.length args) ^ " argument(s))")

  (***************************************************************************)
  (* type-specific parsing functions                                         *)
  (***************************************************************************)

  fun parse_indexed_type get_token dict : Type.hol_type list -> Type.hol_type =
  let
    (* returns all tokens before the next ")" *)
    fun get_tokens acc =
    let
      val token = get_token ()
    in
      if token = ")" then
        List.rev acc
      else
        get_tokens (token :: acc)
    end
  in
    case get_tokens [] of
      [] => raise ERR "parse_indexed_type" "'_' immediately followed by ')'"
    | hd::tl =>
        t_with_args dict hd (List.map (numSyntax.mk_numeral o
          Library.parse_arbnum) tl)
  end

  fun parse_type_operands get_token tydict acc : Type.hol_type list =
  let
    val token = get_token ()
  in
    if token = ")" then
      List.rev acc
    else
      let
        (* operands don't take arguments *)
        val operand = parse_type_aux get_token tydict token []
      in
        parse_type_operands get_token tydict (operand :: acc)
      end
  end

  and parse_compound_type get_token tydict (token : string) : Type.hol_type =
   let
    val headfn = parse_type_aux get_token tydict token
    val operands = parse_type_operands get_token tydict []
  in
    headfn operands
  end

  and parse_indexed_or_compound_type get_token tydict
    : Type.hol_type list -> Type.hol_type =
  let
    val token = get_token ()
  in
    if token = "_" then
      parse_indexed_type get_token tydict
    else
      let
        val t = parse_compound_type get_token tydict token
      in
        (* compounds don't take arguments *)
        fn [] => t
          | _ => raise ERR "parse_indexed_or_compound_type"
            "compound: no arguments expected"
      end
  end

  and parse_type_aux get_token tydict (token : string)
    : Type.hol_type list -> Type.hol_type =
    if token = "(" then
      parse_indexed_or_compound_type get_token tydict
    else
      t_with_args tydict token []

  fun parse_type get_token tydict : Type.hol_type =
    parse_type_aux get_token tydict (get_token ()) []

  fun parse_type_list get_token tydict : Type.hol_type list =
  (
    Library.expect_token "(" (get_token ());
    parse_type_operands get_token tydict []
  )

  (***************************************************************************)
  (* term-specific parsing functions                                         *)
  (***************************************************************************)

  fun parse_indexed_term cfg get_token (tydict, tmdict)
    : Term.term list -> Term.term =
  let
    val head = get_token ()

    (* returns all terms corresponding to the indices *)
    fun get_indices acc =
    let
      val token = get_token ()
      val get_token' = Library.undo_look_ahead [token] get_token
      fun parse_index () =
        intSyntax.term_of_int (Arbint.fromNat (Library.parse_arbnum token))
        handle Feedback.HOL_ERR _ =>
          parse_term_with_cfg cfg get_token' (tydict, tmdict)
          handle Feedback.HOL_ERR _ =>
            Term.mk_var (token, Type.mk_vartype "'smtlib_index")
    in
      if token = ")" then
        List.rev acc
      else
        get_indices (parse_index () :: acc)
    end
  in
    t_with_args tmdict head (get_indices [])
  end

  and parse_var_bindings cfg get_token (tydict, tmdict)
    : (string * Term.term) list =
  let
    val _ = Library.expect_token "(" (get_token ())
    fun aux acc =
    let
      val token = get_token ()
    in
      if token = ")" then
        List.rev acc
      else
        let
          val _ = Library.expect_token "(" token
          val symbol = get_token ()
          val term = parse_term_with_cfg cfg get_token (tydict, tmdict)
          val _ = Library.expect_token ")" (get_token ())
        in
          aux ((symbol, term) :: acc)
        end
    end
  in
    aux []
  end

  and parse_let_term cfg get_token (tydict, tmdict) : Term.term =
  let
    val bindings = parse_var_bindings cfg get_token (tydict, tmdict)
    val bindings = List.map
      (fn (s, t) => (s, Term.mk_var (s, Term.type_of t), t)) bindings
    val tmdict = (#mk_let_bindings cfg) ((tydict, tmdict), bindings)
    val body = parse_term_with_cfg cfg get_token (tydict, tmdict)
    val _ = Library.expect_token ")" (get_token ())
  in
    (#mk_let cfg) (bindings, body)
  end

  and parse_sorted_vars get_token tydict : (string * Type.hol_type) list =
  let
    val _ = Library.expect_token "(" (get_token ())
    fun aux acc =
    let
      val token = get_token ()
    in
      if token = ")" then
        List.rev acc
      else
        let
          val _ = Library.expect_token "(" token
          val symbol = get_token ()
          val typ = parse_type get_token tydict
          val _ = Library.expect_token ")" (get_token ())
        in
          aux ((symbol, typ) :: acc)
        end
    end
  in
    aux []
  end

  and parse_binder_term cfg get_token (tydict, tmdict) mk_binder : Term.term =
  let
    val vars = parse_sorted_vars get_token tydict
    val vars = List.map (fn vT => (Lib.fst vT, Term.mk_var vT)) vars
    (* variables don't take arguments *)
    fun parsefn var token indices args =
      if List.null indices andalso List.null args then
        var
      else
        raise ERR ("<" ^ Hol_pp.term_to_string var ^ ">")
          "wrong number of arguments"
    val tmdict = List.foldl Library.extend_dict tmdict
      (List.map (Lib.apsnd parsefn) vars)
    val body = parse_term_with_cfg cfg get_token (tydict, tmdict)
    val _ = Library.expect_token ")" (get_token ())
  in
    mk_binder (List.map Lib.snd vars, body)
  end

  and parse_annotated_term cfg get_token (tydict, tmdict) : Term.term =
  let
    val term = parse_term_with_cfg cfg get_token (tydict, tmdict)
    (* we ignore all attributes; since these can be S-expressions, we
       need to count parentheses *)
    fun parse_attributes n =
    let
      val token = get_token ()
    in
      if token = ")" then
        if n = 0 then () else parse_attributes (n - 1)
      else if token = "(" then
        parse_attributes (n + 1)
      else
        parse_attributes n
    end
  in
    parse_attributes 0;
    term
  end

  and parse_term_operands cfg get_token (tydict, tmdict) acc : Term.term list =
  let
    val token = get_token ()
  in
    if token = ")" then
      List.rev acc
    else
      let
        (* operands don't take arguments *)
        val operand = parse_term_aux cfg get_token (tydict, tmdict) token []
      in
        parse_term_operands cfg get_token (tydict, tmdict) (operand :: acc)
      end
  end

  and parse_compound_term cfg get_token (tydict, tmdict) (token : string)
    : Term.term =
   let
    val headfn = parse_term_aux cfg get_token (tydict, tmdict) token
    val operands = parse_term_operands cfg get_token (tydict, tmdict) []
  in
    headfn operands
  end

  and parse_indexed_or_compound_term cfg get_token (tydict, tmdict)
    : Term.term list -> Term.term =
  let
    val token = get_token ()
  in
    if token = "_" then
      parse_indexed_term cfg get_token (tydict, tmdict)
    else
      let
        val t = if token = "let" then
            parse_let_term cfg get_token (tydict, tmdict)
          else if token = "forall" then
            parse_binder_term cfg get_token (tydict, tmdict)
              boolSyntax.list_mk_forall
          else if token = "exists" then
            parse_binder_term cfg get_token (tydict, tmdict)
              boolSyntax.list_mk_exists
          (* SMT-LIB 2.6 doesn't have special `lambda` terms, but Z3 proof
             certificates do. So we only parse them when allowed by the
             parser configuration, otherwise we will parse identifiers that are
             coincidentally named `lambda` as if they were special (this cannot
             happen in Z3 proof certificates since all user identifiers are
             renamed to non-conflicting names).
             In Z3 proof certificates, `lambda` terms only seem to be a local
             declaration of variable names/types that apparently need to be
             interpreted as free variables in the enclosed term. *)
          else if token = "lambda" andalso #parse_lambda cfg then
            parse_binder_term cfg get_token (tydict, tmdict)
              Lib.snd
          else if token = "!" then
            parse_annotated_term cfg get_token (tydict, tmdict)
          else
            parse_compound_term cfg get_token (tydict, tmdict) token
      in
        (* compounds don't take arguments *)
        fn [] => t
          | _ => raise ERR "parse_indexed_or_compound_term"
            "compound: no arguments expected"
      end
  end

  and parse_term_aux cfg get_token (tydict, tmdict) (token : string)
    : Term.term list -> Term.term =
    if token = "(" then
      parse_indexed_or_compound_term cfg get_token (tydict, tmdict)
    else
      t_with_args tmdict token []

  and parse_term_with_cfg cfg get_token (tydict, tmdict) : Term.term =
    parse_term_aux cfg get_token (tydict, tmdict) (get_token ()) []

  (* the SMT-LIB version of `mk_let_bindings` binds each name to a HOL4 variable
     with the same name *)
  fun smtlib_mk_let_bindings ((tydict, tmdict), bindings) : Term.term dict =
  let
    (* variables don't take arguments *)
    fun parsefn var token indices args =
      if List.null indices andalso List.null args then
        var
      else
        raise ERR ("<" ^ Hol_pp.term_to_string var ^ ">")
          "wrong number of arguments"
  in
    List.foldl Library.extend_dict tmdict
      (List.map (fn (s, var, _) => (s, parsefn var)) bindings)
  end

  (* the SMT-LIB version of `mk_let` constructs a HOL4 `let` term *)
  fun smtlib_mk_let (bindings, body) : Term.term =
    pairSyntax.mk_anylet (List.map (fn (_, var, t) => (var, t)) bindings, body)

  val smtlib_cfg = {
    mk_let_bindings = smtlib_mk_let_bindings,
    mk_let = smtlib_mk_let,
    parse_lambda = false
  }

  val parse_term = parse_term_with_cfg smtlib_cfg

  fun parse_term_list get_token (tydict, tmdict) : Term.term list =
  (
    Library.expect_token "(" (get_token ());
    parse_term_operands smtlib_cfg get_token (tydict, tmdict) []
  )

  (***************************************************************************)
  (* parsing of benchmarks                                                   *)
  (***************************************************************************)

  (* we simply ignore all following tokens up to the next ")" *)
  fun parse_set_info get_token =
    if get_token () = ")" then
      ()
    else
      parse_set_info get_token

  val parse_set_option = parse_set_info

  fun parse_get_info get_token =
    let
      val _ = get_token ()
      val _ = Library.expect_token ")" (get_token ())
    in
      ()
    end

  val parse_get_option = parse_get_info

  (* returns the SMT-LIB logic name and its type/term dictionaries *)
  fun parse_set_logic get_token =
  let
    val logic = get_token ()
    val (tydict, tmdict) = SmtLib_Logics.parsedicts_of_logic logic
    val _ = Library.expect_token ")" (get_token ())
  in
    (logic, tydict, tmdict)
  end

  (* returns an extended 'tydict' *)
  (* FIXME: We only allow sort declarations of arity 0 at present. *)
  fun parse_declare_sort get_token tydict =
  let
    val name = get_token ()
    val _ = Library.expect_token "0" (get_token ())
    val _ = Library.expect_token ")" (get_token ())
    val ty = Type.mk_vartype ("'" ^ name)
    fun parsefn token indices args =
      if List.null indices andalso List.null args then
        ty
      else
        raise ERR ("<" ^ name ^ ">") "wrong number of arguments"
  in
    Library.extend_dict ((name, parsefn), tydict)
  end

  fun parse_define_sort get_token tydict =
  let
    val _ = get_token ()
    val _ = Library.expect_token "(" (get_token ())
    fun skip_params () =
      if get_token () = ")" then ()
      else skip_params ()
    fun skip_balanced 0 = ()
      | skip_balanced depth =
          (case get_token () of
             "(" => skip_balanced (depth + 1)
           | ")" => skip_balanced (depth - 1)
           | _ => skip_balanced depth)
    fun skip_sort () =
      case get_token () of
        "(" => skip_balanced 1
      | ")" => raise ERR "parse_define_sort" "missing sort body"
      | _ => ()
    val _ = skip_params ()
    val _ = skip_sort ()
    val _ = Library.expect_token ")" (get_token ())
  in
    tydict
  end

  (* returns an extended 'tmdict' *)
  fun parse_declare_const_fun parse_types get_token (tydict, tmdict) =
  let
    val name = get_token ()
    val domain_types =
      if parse_types then
        parse_type_list get_token tydict
      else
        []
    val range_type = parse_type get_token tydict
    val _ = Library.expect_token ")" (get_token ())
    val tm = Term.mk_var (name,
      boolSyntax.list_mk_fun (domain_types, range_type))
    val args_count = List.length domain_types
    fun parsefn token indices args =
      if List.null indices andalso List.length args = args_count then
        Term.list_mk_comb (tm, args)
      else
        raise ERR ("<" ^ name ^ ">") "wrong number of arguments"
  in
    (tm, Library.extend_dict ((name, parsefn), tmdict))
  end

  val parse_declare_const = parse_declare_const_fun false
  val parse_declare_fun = parse_declare_const_fun true

  fun parse_declare_datatype get_token (tydict, tmdict) =
  let
    val name = get_token ()
    val datatype_ty = Type.mk_vartype ("'smtlib_dt_" ^ name)
    fun reject_recursive selector_ty =
      if selector_ty = datatype_ty then
        raise ERR "declare-datatype"
          "recursive datatype declarations are parsed by the script AST but not installed in the HOL dictionary"
      else
        ()
    fun parse_ty token indices args =
      if List.null indices andalso List.null args then
        datatype_ty
      else
        raise ERR ("<" ^ name ^ ">") "wrong number of arguments"
    val tydict = Library.extend_dict ((name, parse_ty), tydict)

    fun add_constructor (ctor_name, selectors, tmdict) =
      let
        val arg_tys = List.map Lib.snd selectors
        val ctor_tm = Term.mk_var (ctor_name,
          boolSyntax.list_mk_fun (arg_tys, datatype_ty))
        val args_count = List.length arg_tys
        fun ctor_parse token indices args =
          if List.null indices andalso List.length args = args_count then
            Term.list_mk_comb (ctor_tm, args)
          else
            raise ERR ("<" ^ ctor_name ^ ">") "wrong number of arguments"
        fun selector_entry ((selector_name, selector_ty), tmdict) =
          let
            val selector_tm = Term.mk_var (selector_name,
              Type.--> (datatype_ty, selector_ty))
            fun selector_parse token indices args =
              if List.null indices andalso List.length args = 1 then
                Term.list_mk_comb (selector_tm, args)
              else
                raise ERR ("<" ^ selector_name ^ ">")
                  "wrong number of arguments"
          in
            Library.extend_dict ((selector_name, selector_parse), tmdict)
          end
        fun tester_parse token indices args =
          case (indices, args) of
            ([index], [arg]) =>
              let
                val index_name = Lib.fst (Term.dest_var index)
              in
                if index_name = ctor_name then
                  Term.list_mk_comb
                    (Term.mk_var ("is_" ^ ctor_name,
                       Type.--> (datatype_ty, Type.bool)),
                     [arg])
                else
                  raise ERR ("<is " ^ ctor_name ^ ">")
                    "tester constructor mismatch"
              end
          | _ => raise ERR ("<is " ^ ctor_name ^ ">")
              "one constructor index and one argument expected"
        val tmdict = Library.extend_dict ((ctor_name, ctor_parse), tmdict)
        val tmdict = Library.extend_dict (("is", tester_parse), tmdict)
      in
        List.foldl selector_entry tmdict selectors
      end

    fun parse_selector selectors =
      let
        val selector_name = get_token ()
        val selector_ty = parse_type get_token tydict
        val _ = reject_recursive selector_ty
        val _ = Library.expect_token ")" (get_token ())
      in
        (selector_name, selector_ty) :: selectors
      end

    fun parse_constructor_open tmdict =
      let
        val ctor_name = get_token ()
        fun selectors acc =
          let val token = get_token ()
          in
            if token = ")" then List.rev acc
            else (
              Library.expect_token "(" token;
              selectors (parse_selector acc)
            )
          end
        val selectors = selectors []
      in
        add_constructor (ctor_name, selectors, tmdict)
      end

    val _ = Library.expect_token "(" (get_token ())
    val first = get_token ()
    val _ =
      if first = "par" then
        raise ERR "declare-datatype"
          "parametric datatype declarations are parsed by the script AST but not installed in the HOL dictionary"
      else
        Library.expect_token "(" first

    fun constructors tmdict =
      let
        val tmdict = parse_constructor_open tmdict
        val token = get_token ()
      in
        if token = ")" then tmdict
        else (
          Library.expect_token "(" token;
          constructors tmdict
        )
      end

    val tmdict = constructors tmdict
    val _ = Library.expect_token ")" (get_token ())
  in
    (tydict, tmdict)
  end

  fun define_fun_term name vars range_type definiens tmdict =
  let
    val domain_types = List.map (Term.type_of o Lib.snd) vars
    val tm = Term.mk_var (name,
      boolSyntax.list_mk_fun (domain_types, range_type))
    val args_count = List.length domain_types
    fun parsefn token indices args =
      if List.null indices andalso List.length args = args_count then
        Term.list_mk_comb (tm, args)
      else
        raise ERR ("<" ^ name ^ ">") "wrong number of arguments"
    val tmdict = Library.extend_dict ((name, parsefn), tmdict)
    val vars = List.map Lib.snd vars
    val definition = boolSyntax.list_mk_forall (vars,
      boolSyntax.mk_eq (Term.list_mk_comb (tm, vars), definiens))
  in
    (tmdict, definition)
  end

  fun parse_define_const get_token (tydict, tmdict) =
  let
    val name = get_token ()
    val range_type = parse_type get_token tydict
    val definiens = parse_term get_token (tydict, tmdict)
    val _ = Library.expect_token ")" (get_token ())
  in
    define_fun_term name [] range_type definiens tmdict
  end

  (* returns an extended 'tmdict', and the definition (as a formula) *)
  fun parse_define_fun get_token (tydict, tmdict) =
  let
    val name = get_token ()
    val vars = parse_sorted_vars get_token tydict
    val range_type = parse_type get_token tydict
    val vars = List.map (fn vT => (Lib.fst vT, Term.mk_var vT)) vars
    (* variables don't take arguments *)
    fun var_parsefn var token indices args =
      if List.null indices andalso List.null args then
        var
      else
        raise ERR ("<" ^ Hol_pp.term_to_string var ^ ">")
          "wrong number of arguments"
    val definiens_tmdict = List.foldl Library.extend_dict tmdict
      (List.map (Lib.apsnd var_parsefn) vars)
    val definiens = parse_term get_token (tydict, definiens_tmdict)
    val _ = Library.expect_token ")" (get_token ())
  in
    define_fun_term name vars range_type definiens tmdict
  end

  type assertion_frame = {
    tydict: Type.hol_type dict,
    tmdict: Term.term dict,
    assertions: Term.term list,
    named_assertions: (string * Term.term) list,
    local_definitions: Term.term list
  }

  type command_state = {
    logic: string,
    frames: assertion_frame list,
    queries: query_command list
  }

  fun frame_tydict ({tydict, ...}: assertion_frame) = tydict
  fun frame_tmdict ({tmdict, ...}: assertion_frame) = tmdict
  fun frame_assertions ({assertions, ...}: assertion_frame) = assertions
  fun frame_named_assertions ({named_assertions, ...}: assertion_frame) =
    named_assertions
  fun frame_local_definitions ({local_definitions, ...}: assertion_frame) =
    local_definitions

  fun mk_frame tydict tmdict = {
    tydict = tydict,
    tmdict = tmdict,
    assertions = [],
    named_assertions = [],
    local_definitions = []
  }

  fun current_frame ({frames, ...}: command_state) =
    case frames of
      frame :: _ => frame
    | [] => raise ERR "current_frame" "empty assertion stack"

  fun current_dicts state =
    let val frame = current_frame state
    in (frame_tydict frame, frame_tmdict frame) end

  fun update_current_frame f ({logic, frames, queries}: command_state) =
    case frames of
      frame :: rest => {logic = logic, frames = f frame :: rest, queries = queries}
    | [] => raise ERR "update_current_frame" "empty assertion stack"

  fun update_current_dicts (tydict, tmdict) state =
    update_current_frame
      (fn frame => {
        tydict = tydict,
        tmdict = tmdict,
        assertions = frame_assertions frame,
        named_assertions = frame_named_assertions frame,
        local_definitions = frame_local_definitions frame
      }) state

  fun add_assertion assertion name state =
    update_current_frame
      (fn frame => {
        tydict = frame_tydict frame,
        tmdict = frame_tmdict frame,
        assertions = assertion :: frame_assertions frame,
        named_assertions =
          (case name of
             NONE => frame_named_assertions frame
           | SOME n => (n, assertion) :: frame_named_assertions frame),
        local_definitions = frame_local_definitions frame
      }) state

  fun add_definition assertion state =
    update_current_frame
      (fn frame => {
        tydict = frame_tydict frame,
        tmdict = frame_tmdict frame,
        assertions = assertion :: frame_assertions frame,
        named_assertions = frame_named_assertions frame,
        local_definitions = assertion :: frame_local_definitions frame
      }) state

  fun add_query query ({logic, frames, queries}: command_state) =
    {logic = logic, frames = frames, queries = query :: queries}

  fun active_assertions ({frames, ...}: command_state) =
    List.concat (List.map (List.rev o frame_assertions) (List.rev frames))

  fun active_named_assertions ({frames, ...}: command_state) =
    List.concat
      (List.map (List.rev o frame_named_assertions) (List.rev frames))

  fun active_local_definitions ({frames, ...}: command_state) =
    List.concat
      (List.map (List.rev o frame_local_definitions) (List.rev frames))

  fun new_state logic tydict tmdict =
    {logic = logic, frames = [mk_frame tydict tmdict], queries = []}

  fun dest_state cmd (SOME x) = x
    | dest_state cmd NONE     =
        raise ERR "dest_state" ("received " ^ cmd ^ " before set-logic")

  fun parse_stack_count cmd NONE = 1
    | parse_stack_count cmd (SOME token) =
        (case Int.fromString token of
           SOME n =>
             if n < 0 then
               raise ERR cmd "stack count must be non-negative"
             else n
         | NONE => raise ERR cmd ("expected non-negative integer, got '" ^
             token ^ "'"))

  fun push_frames 0 state = state
    | push_frames n ({logic, frames, queries}: command_state) =
        let
          val top = current_frame {logic = logic, frames = frames, queries = queries}
          val frame = mk_frame (frame_tydict top) (frame_tmdict top)
        in
          push_frames (n - 1)
            {logic = logic, frames = frame :: frames, queries = queries}
        end

  fun pop_frames 0 state = state
    | pop_frames n ({logic, frames, queries}: command_state) =
        (case frames of
           _ :: rest =>
             if List.null rest then
               raise ERR "pop" "pop scope underflow: cannot pop the base assertion scope"
             else
               pop_frames (n - 1)
                 {logic = logic, frames = rest, queries = queries}
         | [] => raise ERR "pop" "empty assertion stack")

  fun reset_assertions ({logic, frames, queries}: command_state) =
    let val frame = current_frame {logic = logic, frames = frames, queries = queries}
    in
      {logic = logic,
       frames = [mk_frame (frame_tydict frame) (frame_tmdict frame)],
       queries = queries}
    end

  fun parse_top_level_assertion get_token (tydict, tmdict) =
  let
    fun parse_attributes depth named =
      let
        val token = get_token ()
      in
        if token = ")" then
          if depth = 0 then named else parse_attributes (depth - 1) named
        else if token = "(" then
          parse_attributes (depth + 1) named
        else if token = ":named" andalso depth = 0 then
          parse_attributes depth (SOME (get_token ()))
        else
          parse_attributes depth named
      end

    val first = get_token ()
  in
    if first = "(" then
      let
        val second = get_token ()
      in
        if second = "!" then
          let
            val term = parse_term get_token (tydict, tmdict)
            val name = parse_attributes 0 NONE
          in
            (term, name)
          end
        else
          let
            val get_token' = Library.undo_look_ahead [first, second] get_token
          in
            (parse_term get_token' (tydict, tmdict), NONE)
          end
      end
    else
      (parse_term_aux smtlib_cfg get_token (tydict, tmdict) first [], NONE)
  end

  fun query_warning cmd msg =
    WARNING cmd ("parsed command is not meaningful in proof reconstruction " ^
      "mode: " ^ msg)

  fun finalize_state cmd state : command_state_snapshot =
  let
    val command_state as {logic, queries, ...} = dest_state cmd state
    val (tydict, tmdict) = current_dicts command_state
  in
    {logic = logic,
     tydict = tydict,
     tmdict = tmdict,
     assertions = active_assertions command_state,
     named_assertions = active_named_assertions command_state,
     local_definitions = active_local_definitions command_state,
     queries = List.rev queries}
  end

  (* returns the logic's name, its 'tydict', its 'tmdict' extended with
     declared function symbols, and a list of asserted formulas *)
  and parse_command command get_token state =
    case command of "set-info" =>
      let
        val _ = parse_set_info get_token
      in
        parse_commands get_token state
      end
    | "set-option" =>
      let
        val _ = parse_set_option get_token
      in
        parse_commands get_token state
      end
    | "set-logic" =>
      let
        val _ = not (Option.isSome state) orelse
          raise ERR "parse_commands" "set-logic issued more than once"
        val (logic, tydict, tmdict) = parse_set_logic get_token
      in
        parse_commands get_token (SOME (new_state logic tydict tmdict))
      end
    | "get-info" =>
      let
        val _ = parse_get_info get_token
      in
        parse_commands get_token state
      end
    | "get-option" =>
      let
        val _ = parse_get_option get_token
      in
        parse_commands get_token state
      end
    | "declare-sort" =>
      let
        val command_state = dest_state "declare-sort" state
        val (tydict, tmdict) = current_dicts command_state
        val tydict = parse_declare_sort get_token tydict
      in
        parse_commands get_token
          (SOME (update_current_dicts (tydict, tmdict) command_state))
      end
    | "define-sort" =>
      let
        val command_state = dest_state "define-sort" state
        val (tydict, tmdict) = current_dicts command_state
        val tydict = parse_define_sort get_token tydict
      in
        parse_commands get_token
          (SOME (update_current_dicts (tydict, tmdict) command_state))
      end
    | "declare-const" =>
      let
        val command_state = dest_state "declare-const" state
        val (tydict, tmdict) = current_dicts command_state
        val (_, tmdict) = parse_declare_const get_token (tydict, tmdict)
      in
        parse_commands get_token
          (SOME (update_current_dicts (tydict, tmdict) command_state))
      end
    | "declare-fun" =>
      let
        val command_state = dest_state "declare-fun" state
        val (tydict, tmdict) = current_dicts command_state
        val (_, tmdict) = parse_declare_fun get_token (tydict, tmdict)
      in
        parse_commands get_token
          (SOME (update_current_dicts (tydict, tmdict) command_state))
      end
    | "define-const" =>
      let
        val command_state = dest_state "define-const" state
        val (tydict, tmdict) = current_dicts command_state
        val (tmdict, def) = parse_define_const get_token (tydict, tmdict)
        val command_state = update_current_dicts (tydict, tmdict) command_state
      in
        parse_commands get_token (SOME (add_definition def command_state))
      end
    | "define-fun" =>
      let
        val command_state = dest_state "define-fun" state
        val (tydict, tmdict) = current_dicts command_state
        val (tmdict, def) = parse_define_fun get_token (tydict, tmdict)
        val command_state = update_current_dicts (tydict, tmdict) command_state
      in
        parse_commands get_token (SOME (add_definition def command_state))
      end
    | "define-fun-rec" =>
      raise ERR "parse_commands"
        "unsupported command 'define-fun-rec': recursive definitions are parsed by the script AST but not expanded into HOL definitions"
    | "define-funs-rec" =>
      raise ERR "parse_commands"
        "unsupported command 'define-funs-rec': mutually recursive definitions are parsed by the script AST but not expanded into HOL definitions"
    | "declare-datatype" =>
      let
        val command_state = dest_state "declare-datatype" state
        val (tydict, tmdict) = current_dicts command_state
        val (tydict, tmdict) = parse_declare_datatype get_token
          (tydict, tmdict)
      in
        parse_commands get_token
          (SOME (update_current_dicts (tydict, tmdict) command_state))
      end
    | "declare-datatypes" =>
      raise ERR "parse_commands"
        "unsupported command 'declare-datatypes': mutual datatype declarations are parsed by the script AST but not installed in the HOL dictionary"
    | "assert" =>
      let
        val command_state = dest_state "assert" state
        val (tydict, tmdict) = current_dicts command_state
        val (assertion, name) =
          parse_top_level_assertion get_token (tydict, tmdict)
        val _ = Library.expect_token ")" (get_token ())
      in
        parse_commands get_token
          (SOME (add_assertion assertion name command_state))
      end
    | "push" =>
      let
        val command_state = dest_state "push" state
        val next = get_token ()
        val count =
          if next = ")" then 1
          else parse_stack_count "push" (SOME next)
        val _ = if next = ")" then () else Library.expect_token ")" (get_token ())
      in
        parse_commands get_token (SOME (push_frames count command_state))
      end
    | "pop" =>
      let
        val command_state = dest_state "pop" state
        val next = get_token ()
        val count =
          if next = ")" then 1
          else parse_stack_count "pop" (SOME next)
        val _ = if next = ")" then () else Library.expect_token ")" (get_token ())
      in
        parse_commands get_token (SOME (pop_frames count command_state))
      end
    | "reset" =>
      let
        val _ = Library.expect_token ")" (get_token ())
      in
        parse_commands get_token NONE
      end
    | "reset-assertions" =>
      let
        val command_state = dest_state "reset-assertions" state
        val _ = Library.expect_token ")" (get_token ())
      in
        parse_commands get_token (SOME (reset_assertions command_state))
      end
    | "check-sat" =>
      let
        val command_state = dest_state "check-sat" state
        val _ = Library.expect_token ")" (get_token ())
      in
        parse_commands get_token
          (SOME (add_query (QueryCheckSat []) command_state))
      end
    | "check-sat-assuming" =>
      let
        val command_state = dest_state "check-sat-assuming" state
        val assumptions = parse_term_list get_token (current_dicts command_state)
        val _ = Library.expect_token ")" (get_token ())
        val _ = query_warning "check-sat-assuming"
          "assumptions are recorded but not replayed by Z3_TAC"
      in
        parse_commands get_token
          (SOME (add_query (QueryCheckSat assumptions) command_state))
      end
    | "get-proof" =>
      let
        val command_state = dest_state "get-proof" state
        val _ = Library.expect_token ")" (get_token ())
      in
        parse_commands get_token (SOME (add_query QueryGetProof command_state))
      end
    | "get-unsat-assumptions" =>
      let
        val command_state = dest_state "get-unsat-assumptions" state
        val _ = Library.expect_token ")" (get_token ())
        val _ = query_warning "get-unsat-assumptions"
          "unsat-assumption extraction is not implemented"
      in
        parse_commands get_token
          (SOME (add_query QueryGetUnsatAssumptions command_state))
      end
    | "get-unsat-core" =>
      let
        val command_state = dest_state "get-unsat-core" state
        val _ = Library.expect_token ")" (get_token ())
        val _ = query_warning "get-unsat-core"
          "unsat-core extraction is not implemented"
      in
        parse_commands get_token
          (SOME (add_query QueryGetUnsatCore command_state))
      end
    | "get-model" =>
      let
        val command_state = dest_state "get-model" state
        val _ = Library.expect_token ")" (get_token ())
        val _ = query_warning "get-model" "models are not produced by Z3_TAC"
      in
        parse_commands get_token (SOME (add_query QueryGetModel command_state))
      end
    | "get-value" =>
      let
        val command_state = dest_state "get-value" state
        val terms = parse_term_list get_token (current_dicts command_state)
        val _ = Library.expect_token ")" (get_token ())
        val _ = query_warning "get-value"
          "term values are not produced by Z3_TAC"
      in
        parse_commands get_token
          (SOME (add_query (QueryGetValue terms) command_state))
      end
    | "get-assignment" =>
      let
        val command_state = dest_state "get-assignment" state
        val _ = Library.expect_token ")" (get_token ())
        val _ = query_warning "get-assignment"
          "assignments are not produced by Z3_TAC"
      in
        parse_commands get_token
          (SOME (add_query QueryGetAssignment command_state))
      end
    | "get-assertions" =>
      let
        val command_state = dest_state "get-assertions" state
        val _ = Library.expect_token ")" (get_token ())
        val _ = query_warning "get-assertions"
          "assertion output is not produced by Z3_TAC"
      in
        parse_commands get_token
          (SOME (add_query QueryGetAssertions command_state))
      end
    | "echo" =>
      let
        val _ = get_token ()
        val _ = Library.expect_token ")" (get_token ())
      in
        parse_commands get_token state
      end
    | "exit" =>
      finalize_state "exit" state
        before Library.expect_token ")" (get_token ())
    | _ =>
      raise ERR "parse_commands" ("unknown command '" ^ command ^ "'")

  (* returns the logic's name, its 'tydict', its 'tmdict' extended with
     declared function symbols, and a list of asserted formulas *)
  and parse_commands get_token state =
  let
    val tok = SOME (get_token ())
      (* assume an error to be end-of-stream *)
      handle _ => NONE
  in
    case tok of
      NONE => finalize_state "(end-of-stream)" state
    | SOME t => (
        Library.expect_token "(" t;
        parse_command (get_token ()) get_token state
      )
  end

  fun legacy_result_of_state
    ({logic, tydict, tmdict, assertions, ...}: command_state_snapshot) =
    (logic, tydict, tmdict, assertions)

  (* entry point into the parser (i.e., the grammar's start symbol) *)
  fun parse_benchmark_state get_token =
    parse_commands get_token NONE

  fun parse_benchmark get_token =
    legacy_result_of_state (parse_benchmark_state get_token)

  (***************************************************************************)
  (* source-located typechecking and HOL term construction                    *)
  (***************************************************************************)

  type function_signature = {
    tm: Term.term,
    domain: Type.hol_type list,
    range: Type.hol_type
  }

  type function_signature_dict =
    (string, function_signature list) Redblackmap.dict

  type typecheck_frame = {
    tydict: Type.hol_type dict,
    tmdict: Term.term dict,
    sigdict: function_signature_dict,
    assertions: Term.term list,
    named_assertions: (string * Term.term) list,
    local_definitions: Term.term list
  }

  type typecheck_state = {
    logic: string,
    frames: typecheck_frame list,
    queries: query_command list
  }

  datatype checked_term =
    CheckedTerm of {term: Term.term, sort: Type.hol_type}

  fun checked_term_of t = CheckedTerm {term = t, sort = Term.type_of t}
  fun checked_term (CheckedTerm {term, ...}) = term
  fun checked_sort (CheckedTerm {sort, ...}) = sort

  fun type_to_string ty = Hol_pp.type_to_string ty

  fun sort_list_to_string tys =
    "[" ^ String.concatWith ", " (List.map type_to_string tys) ^ "]"

  fun command_context command =
    "command '" ^ command ^ "'"

  fun type_error fn_name context loc expected actual detail =
    let
      val expected_s =
        case expected of NONE => "" | SOME ty => ", expected sort " ^
          type_to_string ty
      val actual_s =
        case actual of NONE => "" | SOME ty => ", actual sort " ^
          type_to_string ty
    in
      raise ERR fn_name
        ("invalid SMT-LIB input at " ^ source_span_to_string loc ^
         " in " ^ context ^ expected_s ^ actual_s ^ ": " ^ detail)
    end

  fun expect_checked_sort fn_name context loc expected checked =
    if checked_sort checked = expected then
      checked_term checked
    else
      type_error fn_name context loc (SOME expected) (SOME (checked_sort checked))
        "sort mismatch"

  fun located_string_node x = node_of x

  fun typecheck_frame_tydict ({tydict, ...}: typecheck_frame) = tydict
  fun typecheck_frame_tmdict ({tmdict, ...}: typecheck_frame) = tmdict
  fun typecheck_frame_sigdict ({sigdict, ...}: typecheck_frame) = sigdict
  fun typecheck_frame_assertions ({assertions, ...}: typecheck_frame) = assertions
  fun typecheck_frame_named_assertions ({named_assertions, ...}: typecheck_frame) =
    named_assertions
  fun typecheck_frame_local_definitions ({local_definitions, ...}: typecheck_frame) =
    local_definitions

  fun empty_sigdict () : function_signature_dict =
    Redblackmap.mkDict String.compare

  fun mk_typecheck_frame tydict tmdict sigdict = {
    tydict = tydict,
    tmdict = tmdict,
    sigdict = sigdict,
    assertions = [],
    named_assertions = [],
    local_definitions = []
  }

  fun current_typecheck_frame ({frames, ...}: typecheck_state) =
    case frames of
      frame :: _ => frame
    | [] => raise ERR "current_typecheck_frame" "empty assertion stack"

  fun current_typecheck_dicts state =
    let val frame = current_typecheck_frame state
    in
      (typecheck_frame_tydict frame, typecheck_frame_tmdict frame,
       typecheck_frame_sigdict frame)
    end

  fun update_current_typecheck_frame f
      ({logic, frames, queries}: typecheck_state) =
    case frames of
      frame :: rest => {logic = logic, frames = f frame :: rest, queries = queries}
    | [] => raise ERR "update_current_typecheck_frame" "empty assertion stack"

  fun update_current_typecheck_dicts (tydict, tmdict, sigdict) state =
    update_current_typecheck_frame
      (fn frame => {
        tydict = tydict,
        tmdict = tmdict,
        sigdict = sigdict,
        assertions = typecheck_frame_assertions frame,
        named_assertions = typecheck_frame_named_assertions frame,
        local_definitions = typecheck_frame_local_definitions frame
      }) state

  fun add_typechecked_assertion assertion name state =
    update_current_typecheck_frame
      (fn frame => {
        tydict = typecheck_frame_tydict frame,
        tmdict = typecheck_frame_tmdict frame,
        sigdict = typecheck_frame_sigdict frame,
        assertions = assertion :: typecheck_frame_assertions frame,
        named_assertions =
          (case name of
             NONE => typecheck_frame_named_assertions frame
           | SOME n => (n, assertion) :: typecheck_frame_named_assertions frame),
        local_definitions = typecheck_frame_local_definitions frame
      }) state

  fun add_typechecked_definition assertion state =
    update_current_typecheck_frame
      (fn frame => {
        tydict = typecheck_frame_tydict frame,
        tmdict = typecheck_frame_tmdict frame,
        sigdict = typecheck_frame_sigdict frame,
        assertions = assertion :: typecheck_frame_assertions frame,
        named_assertions = typecheck_frame_named_assertions frame,
        local_definitions = assertion :: typecheck_frame_local_definitions frame
      }) state

  fun add_typechecked_query query ({logic, frames, queries}: typecheck_state) =
    {logic = logic, frames = frames, queries = query :: queries}

  fun active_typechecked_assertions ({frames, ...}: typecheck_state) =
    List.concat
      (List.map (List.rev o typecheck_frame_assertions) (List.rev frames))

  fun active_typechecked_named_assertions ({frames, ...}: typecheck_state) =
    List.concat
      (List.map (List.rev o typecheck_frame_named_assertions) (List.rev frames))

  fun active_typechecked_local_definitions ({frames, ...}: typecheck_state) =
    List.concat
      (List.map (List.rev o typecheck_frame_local_definitions) (List.rev frames))

  fun new_typecheck_state logic tydict tmdict =
    {logic = logic,
     frames = [mk_typecheck_frame tydict tmdict (empty_sigdict ())],
     queries = []}

  fun dest_typecheck_state cmd (SOME x) = x
    | dest_typecheck_state cmd NONE =
        raise ERR "typecheck_script" ("received " ^ cmd ^ " before set-logic")

  fun finalize_typecheck_state cmd state : command_state_snapshot =
  let
    val command_state as {logic, queries, ...} =
      dest_typecheck_state cmd state
    val (tydict, tmdict, _) = current_typecheck_dicts command_state
  in
    {logic = logic,
     tydict = tydict,
     tmdict = tmdict,
     assertions = active_typechecked_assertions command_state,
     named_assertions = active_typechecked_named_assertions command_state,
     local_definitions = active_typechecked_local_definitions command_state,
     queries = List.rev queries}
  end

  fun push_typecheck_frames 0 state = state
    | push_typecheck_frames n ({logic, frames, queries}: typecheck_state) =
        let
          val top = current_typecheck_frame
            {logic = logic, frames = frames, queries = queries}
          val frame = mk_typecheck_frame
            (typecheck_frame_tydict top)
            (typecheck_frame_tmdict top)
            (typecheck_frame_sigdict top)
        in
          push_typecheck_frames (n - 1)
            {logic = logic, frames = frame :: frames, queries = queries}
        end

  fun pop_typecheck_frames 0 state = state
    | pop_typecheck_frames n ({logic, frames, queries}: typecheck_state) =
        (case frames of
           _ :: rest =>
             if List.null rest then
               raise ERR "pop" "pop scope underflow: cannot pop the base assertion scope"
             else
               pop_typecheck_frames (n - 1)
                 {logic = logic, frames = rest, queries = queries}
         | [] => raise ERR "pop" "empty assertion stack")

  fun reset_typecheck_assertions
      ({logic, frames, queries}: typecheck_state) =
    let
      val frame = current_typecheck_frame
        {logic = logic, frames = frames, queries = queries}
    in
      {logic = logic,
       frames = [mk_typecheck_frame
         (typecheck_frame_tydict frame)
         (typecheck_frame_tmdict frame)
         (typecheck_frame_sigdict frame)],
       queries = queries}
    end

  fun add_signature name sig_entry sigdict =
    Library.extend_dict ((name, sig_entry), sigdict)

  fun peek_signatures (sigdict, name) =
    SOME (Redblackmap.find (sigdict, name))
    handle Redblackmap.NotFound => NONE

  fun same_signature domain range
      ({domain = existing_domain, range = existing_range, ...}
         : function_signature) =
    existing_domain = domain andalso existing_range = range

  fun reject_duplicate_signature context loc name domain range sigdict =
    case peek_signatures (sigdict, name) of
      NONE => ()
    | SOME _ =>
        type_error "reject_duplicate_signature" context loc NONE NONE
          ("duplicate declaration for symbol '" ^ name ^ "'")

  fun make_decl_parsefn name tm args_count token indices args =
    if List.null indices andalso List.length args = args_count then
      Term.list_mk_comb (tm, args)
    else
      raise ERR ("<" ^ name ^ ">") "wrong number of arguments"

  fun add_value_signature name domain range (tmdict, sigdict) =
    let
      val tm = Term.mk_var (name, boolSyntax.list_mk_fun (domain, range))
      val parsefn = make_decl_parsefn name tm (List.length domain)
      val tmdict = Library.extend_dict ((name, parsefn), tmdict)
      val sigdict = add_signature name
        {tm = tm, domain = domain, range = range} sigdict
    in
      (tm, tmdict, sigdict)
    end

  fun add_value_term_signature name tm domain range (tmdict, sigdict) =
    let
      val parsefn = make_decl_parsefn name tm (List.length domain)
      val tmdict = Library.extend_dict ((name, parsefn), tmdict)
      val sigdict = add_signature name
        {tm = tm, domain = domain, range = range} sigdict
    in
      (tmdict, sigdict)
    end

  fun index_term_from_ast context (tydict, tmdict, sigdict) term_ast =
    let
      fun parse_numeral token =
        intSyntax.term_of_int (Arbint.fromNat (Library.parse_arbnum token))
    in
      case node_of term_ast of
        TermIdentifier token =>
          (parse_numeral token
           handle Feedback.HOL_ERR _ =>
             ((checked_term o typecheck_term context (tydict, tmdict, sigdict))
                term_ast
              handle Feedback.HOL_ERR _ =>
                Term.mk_var (token, Type.mk_vartype "'smtlib_index")))
      | _ => checked_term (typecheck_term context (tydict, tmdict, sigdict) term_ast)
    end

  and typecheck_sort context tydict sort_ast =
    let
      fun arg_sorts args = List.map (typecheck_sort context tydict) args
      fun parse_index name_loc indices args =
        let
          val token = located_string_node name_loc
          val idx_terms = List.map
            (fn idx =>
              numSyntax.mk_numeral
                (Library.parse_arbnum (located_string_node idx))
              handle Feedback.HOL_ERR _ =>
                type_error "typecheck_sort" context (loc_of idx) NONE NONE
                  ("invalid sort index '" ^ located_string_node idx ^ "'"))
            indices
        in
          t_with_args tydict token idx_terms args
          handle Feedback.HOL_ERR holerr =>
            type_error "typecheck_sort" context (loc_of sort_ast) NONE NONE
              (Feedback.message_of holerr)
        end
    in
      case node_of sort_ast of
        SortIdentifier name =>
          (t_with_args tydict name [] []
           handle Feedback.HOL_ERR holerr =>
             type_error "typecheck_sort" context (loc_of sort_ast) NONE NONE
               (Feedback.message_of holerr))
      | SortIndexed (name, indices) =>
          parse_index name indices []
      | SortApply (head, args) =>
          (t_with_args tydict (located_string_node head) []
             (arg_sorts args)
           handle Feedback.HOL_ERR holerr =>
             type_error "typecheck_sort" context (loc_of sort_ast) NONE NONE
               (Feedback.message_of holerr))
    end

  and typecheck_sorted_var context tydict sorted_var =
    case node_of sorted_var of
      SortedVar (name, sort) =>
        (located_string_node name, typecheck_sort context tydict sort)

  and function_signature_mismatch_detail name arg_sorts signatures =
    let
      val arity_matches =
        List.filter
          (fn {domain, ...}: function_signature =>
            List.length domain = List.length arg_sorts)
          signatures
    in
      case arity_matches of
        [] =>
          "function arity mismatch: wrong number of arguments for '" ^ name ^
          "': actual sorts " ^
          sort_list_to_string arg_sorts
      | {domain, ...} :: _ =>
          "argument sort mismatch for '" ^ name ^ "': expected sorts " ^
          sort_list_to_string domain ^ ", actual sorts " ^
          sort_list_to_string arg_sorts
    end

  and signature_applies arg_sorts ({domain, ...}: function_signature) =
    List.length domain = List.length arg_sorts andalso
    List.all (fn (expected, actual) => expected = actual)
      (ListPair.zip (domain, arg_sorts))

  and apply_user_signature fn_name context loc name args signatures =
    let
      val arg_terms = List.map checked_term args
      val arg_sorts = List.map checked_sort args
    in
      case List.find (signature_applies arg_sorts) signatures of
        SOME {tm, range, ...} =>
          CheckedTerm {term = Term.list_mk_comb (tm, arg_terms), sort = range}
      | NONE =>
          let
            val actual =
              case arg_sorts of [] => NONE | ty :: _ => SOME ty
            val expected =
              case signatures of
                {domain = ty :: _, ...} :: _ => SOME ty
              | {range, domain = [], ...} :: _ => SOME range
              | _ => NONE
          in
            type_error fn_name context loc expected actual
              (function_signature_mismatch_detail name arg_sorts signatures)
          end
    end

  and apply_symbol fn_name context loc (tydict, tmdict, sigdict)
      name indices args =
    if List.null indices then
      (case peek_signatures (sigdict, name) of
         SOME signatures =>
           apply_user_signature fn_name context loc name args signatures
       | NONE =>
         let
           val arg_terms = List.map checked_term args
           val arg_sorts = List.map checked_sort args
           val t =
             t_with_args tmdict name [] arg_terms
             handle Feedback.HOL_ERR holerr =>
               type_error fn_name context loc NONE NONE
                 ("could not resolve symbol '" ^ name ^ "' for actual sorts " ^
                  sort_list_to_string arg_sorts ^ ": " ^
                  Feedback.message_of holerr)
         in
           checked_term_of t
         end)
    else
      let
        val arg_terms = List.map checked_term args
        val arg_sorts = List.map checked_sort args
        val t =
          t_with_args tmdict name indices arg_terms
          handle Feedback.HOL_ERR holerr =>
            type_error fn_name context loc NONE NONE
              ("could not resolve indexed symbol '" ^ name ^
               "' for actual sorts " ^ sort_list_to_string arg_sorts ^
               ": " ^ Feedback.message_of holerr)
      in
        checked_term_of t
      end

  and typecheck_term context env term_ast =
    let
      val (tydict, tmdict, sigdict) = env
      fun check t = typecheck_term context env t
      fun check_index t = index_term_from_ast context env t
      fun apply_head loc head args =
        case node_of head of
          TermIdentifier name =>
            apply_symbol "typecheck_term" context loc env name []
              (List.map check args)
        | TermIndexed (name, indices) =>
            apply_symbol "typecheck_term" context loc env
              (located_string_node name) (List.map check_index indices)
              (List.map check args)
        | _ =>
            let
              val head_checked = check head
              val arg_terms = List.map (checked_term o check) args
              val t =
                Term.list_mk_comb (checked_term head_checked, arg_terms)
                handle Feedback.HOL_ERR holerr =>
                  type_error "typecheck_term" context loc NONE
                    (SOME (checked_sort head_checked))
                    ("invalid higher-order application: " ^
                     Feedback.message_of holerr)
            in
              checked_term_of t
            end
    in
      case node_of term_ast of
        TermIdentifier name =>
          apply_symbol "typecheck_term" context (loc_of term_ast) env name [] []
      | TermIndexed (name, indices) =>
          apply_symbol "typecheck_term" context (loc_of term_ast) env
            (located_string_node name) (List.map check_index indices) []
      | TermApply (head, args) =>
          apply_head (loc_of term_ast) head args
      | TermLet (bindings, body) =>
          let
            val checked_bindings =
              List.map (fn (name, body) =>
                let val checked = check body
                in
                  (located_string_node name,
                   Term.mk_var (located_string_node name, checked_sort checked),
                   checked_term checked)
                end) bindings
            val (tmdict, sigdict) =
              List.foldl
                (fn ((name, var, _), (tmdict, sigdict)) =>
                  add_value_term_signature name var [] (Term.type_of var)
                    (tmdict, sigdict))
                (tmdict, sigdict) checked_bindings
            val body_checked =
              typecheck_term context (tydict, tmdict, sigdict) body
            val t = (#mk_let smtlib_cfg) (checked_bindings,
              checked_term body_checked)
          in
            checked_term_of t
          end
      | TermForall (vars, body) =>
          typecheck_binder context env term_ast vars body boolSyntax.list_mk_forall
      | TermExists (vars, body) =>
          typecheck_binder context env term_ast vars body boolSyntax.list_mk_exists
      | TermAnnotated (term, _) =>
          check term
    end

  and typecheck_binder context (tydict, tmdict, sigdict) term_ast vars body
      mk_binder =
    let
      val vars = List.map (typecheck_sorted_var context tydict) vars
      val vars = List.map (fn vT => (Lib.fst vT, Term.mk_var vT)) vars
      val (tmdict, sigdict) =
        List.foldl
          (fn ((name, var), (tmdict, sigdict)) =>
            add_value_term_signature name var [] (Term.type_of var)
              (tmdict, sigdict))
          (tmdict, sigdict) vars
      val body_checked =
        typecheck_term context (tydict, tmdict, sigdict) body
      val body = expect_checked_sort "typecheck_binder" context (loc_of body)
        Type.bool body_checked
    in
      checked_term_of (mk_binder (List.map Lib.snd vars, body))
    end

  fun typecheck_define_sort context tydict name params body =
    let
      fun add_param (param, (tydict, param_tys)) =
        let
          val pname = located_string_node param
          val ty = Type.mk_vartype ("'" ^ pname)
          fun parsefn token indices args =
            if List.null indices andalso List.null args then ty
            else raise ERR ("<" ^ pname ^ ">") "wrong number of arguments"
        in
          (Library.extend_dict ((pname, parsefn), tydict),
           (pname, ty) :: param_tys)
        end
      val alias_name = located_string_node name
      fun sort_mentions_alias sort =
        case node_of sort of
          SortIdentifier n => n = alias_name
        | SortIndexed (head, _) => located_string_node head = alias_name
        | SortApply (head, args) =>
            located_string_node head = alias_name orelse
            List.exists sort_mentions_alias args
      val _ =
        if sort_mentions_alias body then
          type_error "typecheck_define_sort" context (loc_of body) NONE NONE
            "recursive sort alias"
        else ()
      val (temp_tydict, param_tys) =
        List.foldl add_param (tydict, []) params
      val param_tys = List.rev param_tys
      val body_ty = typecheck_sort context temp_tydict body
      fun parsefn token indices args =
        if List.null indices andalso List.length args = List.length param_tys then
          let
            val subst = ListPair.map
              (fn ((_, param_ty), arg_ty) =>
                {redex = param_ty, residue = arg_ty})
              (param_tys, args)
          in
            Type.type_subst subst body_ty
          end
        else
          raise ERR ("<" ^ alias_name ^ ">") "wrong number of arguments"
    in
      Library.extend_dict ((alias_name, parsefn), tydict)
    end

  fun typecheck_declare_sort context name arity tydict =
    let
      val sort_name = located_string_node name
      val arity_text = located_string_node arity
      val _ =
        if arity_text = "0" then ()
        else type_error "typecheck_declare_sort" context (loc_of arity)
          NONE NONE
          ("declare-sort arity: unsupported sort arity for '" ^ sort_name ^
           "': expected 0, actual " ^ arity_text)
      val ty = Type.mk_vartype ("'" ^ sort_name)
      fun parsefn token indices args =
        if List.null indices andalso List.null args then ty
        else raise ERR ("<" ^ sort_name ^ ">") "wrong number of arguments"
    in
      Library.extend_dict ((sort_name, parsefn), tydict)
    end

  fun typecheck_declare_datatype context name decl (tydict, tmdict, sigdict) =
    let
      val datatype_name = located_string_node name
      val datatype_ty = Type.mk_vartype ("'smtlib_dt_" ^ datatype_name)
      fun reject_recursive loc selector_ty =
        if selector_ty = datatype_ty then
          type_error "typecheck_declare_datatype" context loc NONE NONE
            "recursive datatype declarations are parsed by the script AST but not installed in the HOL dictionary"
        else
          ()
      fun parse_ty token indices args =
        if List.null indices andalso List.null args then datatype_ty
        else raise ERR ("<" ^ datatype_name ^ ">") "wrong number of arguments"
      val tydict = Library.extend_dict ((datatype_name, parse_ty), tydict)

      fun add_constructor (ctor, (tmdict, sigdict)) =
        case node_of ctor of
          DatatypeConstructor (ctor_name, _, selectors) =>
            let
              val ctor_name_s = located_string_node ctor_name
              fun selector_info selector =
                case node_of selector of
                  DatatypeSelector (selector_name, selector_sort) =>
                    let
                      val selector_ty = typecheck_sort context tydict selector_sort
                      val _ = reject_recursive (loc_of selector_sort) selector_ty
                    in
                      (located_string_node selector_name, selector_ty)
                    end
              val selectors = List.map selector_info selectors
              val arg_tys = List.map Lib.snd selectors
              val ctor_tm = Term.mk_var (ctor_name_s,
                boolSyntax.list_mk_fun (arg_tys, datatype_ty))
              val (tmdict, sigdict) =
                add_value_term_signature ctor_name_s ctor_tm arg_tys datatype_ty
                  (tmdict, sigdict)

              fun add_selector ((selector_name, selector_ty), (tmdict, sigdict)) =
                let
                  val selector_tm = Term.mk_var (selector_name,
                    Type.--> (datatype_ty, selector_ty))
                in
                  add_value_term_signature selector_name selector_tm
                    [datatype_ty] selector_ty (tmdict, sigdict)
                end

              fun tester_parse token indices args =
                case (indices, args) of
                  ([index], [arg]) =>
                    let
                      val index_name = Lib.fst (Term.dest_var index)
                    in
                      if index_name = ctor_name_s then
                        Term.list_mk_comb
                          (Term.mk_var ("is_" ^ ctor_name_s,
                             Type.--> (datatype_ty, Type.bool)),
                           [arg])
                      else
                        raise ERR ("<is " ^ ctor_name_s ^ ">")
                          "tester constructor mismatch"
                    end
                | _ => raise ERR ("<is " ^ ctor_name_s ^ ">")
                    "one constructor index and one argument expected"
              val tmdict = Library.extend_dict (("is", tester_parse), tmdict)
            in
              List.foldl add_selector (tmdict, sigdict) selectors
            end
    in
      case node_of decl of
        DatatypeDecl ([], constructors) =>
          let
            val (tmdict, sigdict) =
              List.foldl add_constructor (tmdict, sigdict) constructors
          in
            (tydict, tmdict, sigdict)
          end
      | DatatypeDecl _ =>
          type_error "typecheck_declare_datatype" context (loc_of decl)
            NONE NONE
            "unsupported parametric datatype declaration"
    end

  fun define_typechecked_fun context loc name vars range_type definiens
      (tmdict, sigdict) =
    let
      val _ =
        case peek_signatures (sigdict, name) of
          NONE => ()
        | SOME _ =>
            type_error "define_typechecked_fun" context loc NONE NONE
              ("duplicate define-const/define-fun declaration for symbol '" ^
               name ^ "'")
      val domain_types = List.map (Term.type_of o Lib.snd) vars
      val (tm, tmdict, sigdict) =
        add_value_signature name domain_types range_type (tmdict, sigdict)
      val vars = List.map Lib.snd vars
      val definition = boolSyntax.list_mk_forall (vars,
        boolSyntax.mk_eq (Term.list_mk_comb (tm, vars), definiens))
    in
      (tmdict, sigdict, definition)
    end

  fun typecheck_define_const context name sort body (tydict, tmdict, sigdict) =
    let
      val name_loc = loc_of name
      val name = located_string_node name
      val range_type = typecheck_sort context tydict sort
      val body_checked = typecheck_term context (tydict, tmdict, sigdict) body
      val body_term = expect_checked_sort "typecheck_define_const" context
        (loc_of body) range_type body_checked
      val (tmdict, sigdict, definition) =
        define_typechecked_fun context name_loc name [] range_type body_term
          (tmdict, sigdict)
    in
      (tmdict, sigdict, definition)
    end

  fun typecheck_define_fun context name sorted_vars range body
      (tydict, tmdict, sigdict) =
    let
      val name_loc = loc_of name
      val name = located_string_node name
      fun term_mentions_name term =
        case node_of term of
          TermIdentifier n => n = name
        | TermIndexed (head, indices) =>
            located_string_node head = name orelse
            List.exists term_mentions_name indices
        | TermApply (head, args) =>
            term_mentions_name head orelse List.exists term_mentions_name args
        | TermLet (bindings, body) =>
            List.exists (term_mentions_name o Lib.snd) bindings orelse
            term_mentions_name body
        | TermForall (_, body) => term_mentions_name body
        | TermExists (_, body) => term_mentions_name body
        | TermAnnotated (term, _) => term_mentions_name term
      val _ =
        if term_mentions_name body then
          type_error "typecheck_define_fun" context (loc_of body) NONE NONE
            "recursive self-reference"
        else ()
      val range_type = typecheck_sort context tydict range
      val vars = List.map (typecheck_sorted_var context tydict) sorted_vars
      val vars = List.map (fn vT => (Lib.fst vT, Term.mk_var vT)) vars
      val (body_tmdict, body_sigdict) =
        List.foldl
          (fn ((vname, var), (tmdict, sigdict)) =>
            add_value_term_signature vname var [] (Term.type_of var)
              (tmdict, sigdict))
          (tmdict, sigdict) vars
      val body_checked =
        typecheck_term context (tydict, body_tmdict, body_sigdict) body
      val body_term = expect_checked_sort "typecheck_define_fun" context
        (loc_of body) range_type body_checked
      val (tmdict, sigdict, definition) =
        define_typechecked_fun context name_loc name vars range_type
          body_term (tmdict, sigdict)
    in
      (tmdict, sigdict, definition)
    end

  fun named_attribute attrs =
    let
      fun sexp_atom sexp =
        case node_of sexp of
          SexpAtom atom => SOME atom
        | _ => NONE
      fun scan [] = NONE
        | scan (x :: y :: rest) =
            if sexp_atom x = SOME ":named" then sexp_atom y
            else scan (y :: rest)
        | scan _ = NONE
    in
      scan attrs
    end

  fun split_assertion_term term =
    case node_of term of
      TermAnnotated (body, attrs) => (body, named_attribute attrs)
    | _ => (term, NONE)

  fun typecheck_bool_terms context env fn_name terms =
    List.map (fn term =>
      let
        val checked = typecheck_term context env term
      in
        if checked_sort checked = Type.bool then checked_term checked
        else
          type_error fn_name context (loc_of term) (SOME Type.bool)
            (SOME (checked_sort checked))
            "assumption literal must have Bool sort"
      end) terms

  fun typecheck_command command state =
    let
      val context = command_context
      fun finish state = SOME state
      fun typecheck_define_fun_command command_name name vars range body state =
        let
          val command_state = dest_typecheck_state command_name state
          val (tydict, tmdict, sigdict) =
            current_typecheck_dicts command_state
          val (tmdict, sigdict, def) =
            typecheck_define_fun (context command_name) name vars range body
              (tydict, tmdict, sigdict)
          val command_state = update_current_typecheck_dicts
            (tydict, tmdict, sigdict) command_state
        in
          finish (add_typechecked_definition def command_state)
        end
      fun typecheck_define_funs_rec sigs bodies state =
        let
          val _ =
            if List.length sigs = List.length bodies then ()
            else raise ERR "typecheck_script"
              "malformed recursive definition block: function signature count does not match body count"
          fun one (sig_ast, body, state) =
            case node_of sig_ast of
              FunctionSignature (name, vars, range) =>
                typecheck_define_fun_command "define-funs-rec"
                  name vars range body state
        in
          ListPair.foldl one state (sigs, bodies)
        end
    in
      case node_of command of
        CmdSetInfo _ => state
      | CmdSetOption _ =>
          if Option.isSome state then
            raise ERR "typecheck_script"
              "set-option after logic or assertions"
          else state
      | CmdSetLogic logic =>
          let
            val _ = not (Option.isSome state) orelse
              raise ERR "typecheck_script"
                "duplicate set-logic: set-logic issued more than once"
            val logic_name = located_string_node logic
            val (tydict, tmdict) = SmtLib_Logics.parsedicts_of_logic logic_name
          in
            finish (new_typecheck_state logic_name tydict tmdict)
          end
      | CmdGetInfo _ => state
      | CmdGetOption _ => state
      | CmdDeclareSort (name, arity) =>
          let
            val command_state =
              dest_typecheck_state "declare-sort" state
            val (tydict, tmdict, sigdict) =
              current_typecheck_dicts command_state
            val tydict = typecheck_declare_sort (context "declare-sort")
              name arity tydict
          in
            finish (update_current_typecheck_dicts
              (tydict, tmdict, sigdict) command_state)
          end
      | CmdDefineSort (name, params, body) =>
          let
            val command_state =
              dest_typecheck_state "define-sort" state
            val (tydict, tmdict, sigdict) =
              current_typecheck_dicts command_state
            val tydict = typecheck_define_sort (context "define-sort")
              tydict name params body
          in
            finish (update_current_typecheck_dicts
              (tydict, tmdict, sigdict) command_state)
          end
      | CmdDeclareConst (name, sort) =>
          let
            val command_state =
              dest_typecheck_state "declare-const" state
            val (tydict, tmdict, sigdict) =
              current_typecheck_dicts command_state
            val range = typecheck_sort (context "declare-const") tydict sort
            val name_text = located_string_node name
            val _ = reject_duplicate_signature (context "declare-const")
              (loc_of name) name_text [] range sigdict
            val (_, tmdict, sigdict) =
              add_value_signature name_text [] range (tmdict, sigdict)
          in
            finish (update_current_typecheck_dicts
              (tydict, tmdict, sigdict) command_state)
          end
      | CmdDeclareFun (name, domain, range) =>
          let
            val command_state =
              dest_typecheck_state "declare-fun" state
            val (tydict, tmdict, sigdict) =
              current_typecheck_dicts command_state
            val domain = List.map
              (typecheck_sort (context "declare-fun") tydict) domain
            val range = typecheck_sort (context "declare-fun") tydict range
            val name_text = located_string_node name
            val _ = reject_duplicate_signature (context "declare-fun")
              (loc_of name) name_text domain range sigdict
            val (_, tmdict, sigdict) =
              add_value_signature name_text domain range (tmdict, sigdict)
          in
            finish (update_current_typecheck_dicts
              (tydict, tmdict, sigdict) command_state)
          end
      | CmdDefineConst (name, sort, body) =>
          let
            val command_state =
              dest_typecheck_state "define-const" state
            val (tydict, tmdict, sigdict) =
              current_typecheck_dicts command_state
            val (tmdict, sigdict, def) =
              typecheck_define_const (context "define-const") name sort body
                (tydict, tmdict, sigdict)
            val command_state = update_current_typecheck_dicts
              (tydict, tmdict, sigdict) command_state
          in
            finish (add_typechecked_definition def command_state)
          end
      | CmdDefineFun (name, vars, range, body) =>
          typecheck_define_fun_command "define-fun" name vars range body state
      | CmdDefineFunRec (name, vars, range, body) =>
          typecheck_define_fun_command "define-fun-rec" name vars range body state
      | CmdDefineFunsRec (sigs, bodies) =>
          typecheck_define_funs_rec sigs bodies state
      | CmdDeclareDatatype (name, decl) =>
          let
            val command_state =
              dest_typecheck_state "declare-datatype" state
            val (tydict, tmdict, sigdict) =
              current_typecheck_dicts command_state
            val (tydict, tmdict, sigdict) =
              typecheck_declare_datatype (context "declare-datatype")
                name decl (tydict, tmdict, sigdict)
          in
            finish (update_current_typecheck_dicts
              (tydict, tmdict, sigdict) command_state)
          end
      | CmdDeclareDatatypes _ =>
          (case node_of command of
             CmdDeclareDatatypes ([binding], [decl]) =>
               (case node_of binding of
                  DatatypeBinding (name, arity) =>
                    let
                      val command_state =
                        dest_typecheck_state "declare-datatypes" state
                      val (tydict, tmdict, sigdict) =
                        current_typecheck_dicts command_state
                      val _ =
                        if located_string_node arity = "0" then ()
                        else type_error "typecheck_declare_datatypes"
                          (context "declare-datatypes") (loc_of arity)
                          NONE NONE
                          ("declare-datatypes arity for '" ^
                           located_string_node name ^ "': expected 0, actual " ^
                           located_string_node arity)
                      val (tydict, tmdict, sigdict) =
                        typecheck_declare_datatype
                          (context "declare-datatypes")
                          name decl (tydict, tmdict, sigdict)
                    in
                      finish (update_current_typecheck_dicts
                        (tydict, tmdict, sigdict) command_state)
                    end)
           | _ =>
               raise ERR "typecheck_script"
                 "unsupported command 'declare-datatypes': mutual datatype declarations are parsed by the script AST but not installed in the HOL dictionary")
      | CmdAssert term =>
          let
            val command_state = dest_typecheck_state "assert" state
            val env = current_typecheck_dicts command_state
            val (term, name) = split_assertion_term term
            val checked = typecheck_term (context "assert") env term
            val assertion =
              if checked_sort checked = Type.bool then checked_term checked
              else
                type_error "typecheck_assert" (context "assert") (loc_of term)
                  (SOME Type.bool) (SOME (checked_sort checked))
                  "assert term must have Bool sort"
          in
            finish (add_typechecked_assertion assertion name command_state)
          end
      | CmdPush count =>
          let
            val command_state = dest_typecheck_state "push" state
            val count = parse_stack_count "push"
              (Option.map located_string_node count)
          in
            finish (push_typecheck_frames count command_state)
          end
      | CmdPop count =>
          let
            val command_state = dest_typecheck_state "pop" state
            val count = parse_stack_count "pop"
              (Option.map located_string_node count)
          in
            finish (pop_typecheck_frames count command_state)
          end
      | CmdReset =>
          let
            val command_state = dest_typecheck_state "reset" state
            val logic = #logic command_state
            val (tydict, tmdict) = SmtLib_Logics.parsedicts_of_logic logic
          in
            finish (new_typecheck_state logic tydict tmdict)
          end
      | CmdResetAssertions =>
          let
            val command_state =
              dest_typecheck_state "reset-assertions" state
          in
            finish (reset_typecheck_assertions command_state)
          end
      | CmdCheckSat =>
          let val command_state = dest_typecheck_state "check-sat" state
          in finish (add_typechecked_query (QueryCheckSat []) command_state) end
      | CmdCheckSatAssuming assumptions =>
          let
            val command_state =
              dest_typecheck_state "check-sat-assuming" state
            val assumptions = typecheck_bool_terms
              (context "check-sat-assuming")
              (current_typecheck_dicts command_state)
              "typecheck_check_sat_assuming" assumptions
            val _ = query_warning "check-sat-assuming"
              "assumptions are recorded but not replayed by Z3_TAC"
          in
            finish (add_typechecked_query (QueryCheckSat assumptions)
              command_state)
          end
      | CmdGetProof =>
          let val command_state = dest_typecheck_state "get-proof" state
          in finish (add_typechecked_query QueryGetProof command_state) end
      | CmdGetUnsatAssumptions =>
          let
            val command_state =
              dest_typecheck_state "get-unsat-assumptions" state
            val _ = query_warning "get-unsat-assumptions"
              "unsat-assumption extraction is not implemented"
          in
            finish (add_typechecked_query QueryGetUnsatAssumptions command_state)
          end
      | CmdGetUnsatCore =>
          let
            val command_state = dest_typecheck_state "get-unsat-core" state
            val _ = query_warning "get-unsat-core"
              "unsat-core extraction is not implemented"
          in
            finish (add_typechecked_query QueryGetUnsatCore command_state)
          end
      | CmdGetModel =>
          let
            val command_state = dest_typecheck_state "get-model" state
            val _ = query_warning "get-model" "models are not produced by Z3_TAC"
          in
            finish (add_typechecked_query QueryGetModel command_state)
          end
      | CmdGetValue terms =>
          let
            val command_state = dest_typecheck_state "get-value" state
            val terms = List.map (checked_term o
              typecheck_term (context "get-value")
                (current_typecheck_dicts command_state)) terms
            val _ = query_warning "get-value"
              "term values are not produced by Z3_TAC"
          in
            finish (add_typechecked_query (QueryGetValue terms) command_state)
          end
      | CmdGetAssignment =>
          let
            val command_state = dest_typecheck_state "get-assignment" state
            val _ = query_warning "get-assignment"
              "assignments are not produced by Z3_TAC"
          in
            finish (add_typechecked_query QueryGetAssignment command_state)
          end
      | CmdGetAssertions =>
          let
            val command_state = dest_typecheck_state "get-assertions" state
            val _ = query_warning "get-assertions"
              "assertion output is not produced by Z3_TAC"
          in
            finish (add_typechecked_query QueryGetAssertions command_state)
          end
      | CmdEcho _ => state
      | CmdExit => state
      | CmdUnknown (name, _) =>
          raise ERR "typecheck_script"
            ("unknown command '" ^ located_string_node name ^ "'")
    end

  fun typecheck_script script : checked_script =
    let
      fun loop [] state = finalize_typecheck_state "(end-of-stream)" state
        | loop (command :: rest) state =
            (case node_of command of
               CmdExit => finalize_typecheck_state "exit" state
             | _ => loop rest (typecheck_command command state))
    in
      loop script NONE
    end

  fun typecheck_script_string text =
    typecheck_script (parse_script_string text)

in

  val loc_of = loc_of
  val node_of = node_of
  val source_pos_to_string = source_pos_to_string
  val source_span_to_string = source_span_to_string
  val parse_script_string = parse_script_string
  val parse_script_file = parse_script_file
  val typecheck_script = typecheck_script
  val typecheck_script_string = typecheck_script_string

  val smtlib_mk_let_bindings = smtlib_mk_let_bindings
  val smtlib_mk_let = smtlib_mk_let

  val parse_declare_fun = parse_declare_fun

  val parse_type = parse_type
  val parse_type_list = parse_type_list

  val parse_term_with_cfg = parse_term_with_cfg
  val parse_term = parse_term
  val parse_term_list = parse_term_list

  (* 'parse_file' parses an SMT-LIB 2 benchmark, returning the
     benchmark's logic, two dictionaries containing all types and
     terms, respectively, declared in the benchmark, and a list of
     "assert"ed formulae *)

  (* This parser handles a restricted subset of SMT-LIB 2.  Recognised
     commands: set-info and set-option (content discarded), set-logic,
     get-info, get-option, declare-sort, define-sort (content checked
     and discarded), declare-const, declare-fun, define-const,
     define-fun, assert, push, pop, reset, reset-assertions, check-sat,
     check-sat-assuming, get-proof, get-unsat-assumptions, get-unsat-core,
     get-model, get-value, get-assignment, get-assertions, echo, and exit.
     Solver query commands update parser state, but model/value/core output
     is not produced by this parser or by proof reconstruction mode.
     Recursive definitions and datatype commands are represented by the
     script AST but rejected here with explicit unsupported-command
     diagnostics.  Any other command is rejected with "unknown command". *)

  fun parse_file_state (path : string) : command_state_snapshot =
  let
    (* parse the file contents *)
    val _ = if !Library.trace > 1 then
        Feedback.HOL_MESG
          ("HolSmtLib: parsing SMT-LIB 2 benchmark file '" ^ path ^ "'")
      else ()
    val instream = TextIO.openIn path
    val text = TextIO.inputAll instream
    val _ = TextIO.closeIn instream
    val result = typecheck_script_string text
  in
    result
  end

  fun parse_file (path : string)
    : string * Type.hol_type dict * Term.term dict * Term.term list =
    legacy_result_of_state (parse_file_state path)

end  (* local *)

end
