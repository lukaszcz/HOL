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
    | TermString of string
    | TermIndexed of string located * term_ast located list
    | TermApply of term_ast located * term_ast located list
    | TermApplyOperator of string located * term_ast located *
        term_ast located list
    | TermAscribed of term_ast located * sort_ast located
    | TermLet of (string located * term_ast located) list * term_ast located
    | TermMatch of term_ast located * match_case_ast located list
    | TermForall of sorted_var_ast located list * term_ast located
    | TermExists of sorted_var_ast located list * term_ast located
    | TermLambda of sorted_var_ast located list * term_ast located
    | TermAnnotated of term_ast located * sexp_ast located list
  and match_pattern_ast =
      MatchPatternAtom of string located
    | MatchPatternConstructor of string located * string located list
  and match_case_ast =
      MatchCase of match_pattern_ast located * term_ast located
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

  type typecheck_options = {
    dict_logic : string option,
    solver : string option,
    elaborate_datatypes : bool
  }

  type datatype_type_entry = {
    smt_name : string,
    hol_type : Type.hol_type
  }

  type datatype_constructor_entry = {
    smt_name : string,
    hol_name : string,
    term : Term.term
  }

  type datatype_selector_entry = {
    smt_name : string,
    constructor : string,
    domain : Type.hol_type,
    range : Type.hol_type
  }

  type datatype_elaboration_result = {
    types : datatype_type_entry list,
    constructors : datatype_constructor_entry list,
    selectors : datatype_selector_entry list,
    mk_selector_case : {
      selector : string,
      constructor : string,
      scrutinee : Term.term
    } -> Term.term,
    mk_tester_case : {
      constructor : string,
      scrutinee : Term.term
    } -> Term.term
  }

  type datatype_elaborator = {
    define_datatype : string located * datatype_decl_ast located ->
      datatype_elaboration_result,
    define_datatypes : datatype_binding_ast located list *
      datatype_decl_ast located list -> datatype_elaboration_result
  }

  type parser_cfg = {
    mk_let_bindings: dicts * bindings -> Term.term dict,
    mk_let: bindings * Term.term -> Term.term,
    parse_choice: bool,
    parse_lambda: bool
  }

  datatype query_command =
      QueryCheckSat of {
        assumptions: Term.term list,
        assertions: Term.term list,
        local_definitions: Term.term list,
        transfer_hypotheses: Term.term list
      }
    | QueryGetProof
    | QueryGetUnsatAssumptions
    | QueryGetUnsatCore
    | QueryGetModel
    | QueryGetValue of Term.term list
    | QueryGetAssignment
    | QueryGetAssertions
    | QueryGetInfo of string
    | QueryGetOption of string

  type surface_flags = SmtLib_Logics.surface_flags

  type command_state_snapshot = {
    logic: string,
    tydict: Type.hol_type dict,
    tmdict: Term.term dict,
    assertions: Term.term list,
    named_assertions: (string * Term.term) list,
    local_definitions: Term.term list,
    queries: query_command list,
    surface_flags: surface_flags
  }

  type checked_script = command_state_snapshot

local

  val ERR = Feedback.mk_HOL_ERR "SmtLib_Parser"
  val WARNING = Feedback.HOL_WARNING "SmtLib_Parser"

  val datatype_elaborator : datatype_elaborator option ref = ref NONE

  fun install_datatype_elaborator hooks =
    datatype_elaborator := SOME hooks

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

  datatype token_kind = AtomToken | QuotedSymbolToken | StringToken

  datatype located_token = Token of {
    text: string,
    kind: token_kind,
    loc: source_span
  }

  fun token_text (Token {text, ...}) = text
  fun token_kind (Token {kind, ...}) = kind
  fun token_loc (Token {loc, ...}) = loc

  fun syntax_error fn_name loc msg =
    raise ERR fn_name (msg ^ " at " ^ source_span_to_string loc)

  fun mk_point_span pos = SourceSpan {start = pos, stop = pos}

  val unlocated_pos : source_pos = {line = 1, column = 1, offset = 0}
  val unlocated_span = mk_point_span unlocated_pos

  fun make_tokenizer_from_input track_locations
      (input: unit -> char option) : unit -> located_token option =
  let
    datatype lookahead = NeedChar | NextChar of char | EndOfInput

    val lookahead = ref NeedChar
    val index = ref 0
    val line = ref 1
    val column = ref 1

    fun pos () = {line = !line, column = !column, offset = !index}

    (* A span costs two position records and the span itself, per token.
       Proof streams run to hundreds of megabytes and never report a span,
       so they are tokenized with 'track_locations' false; 'pos' itself
       stays exact, so the syntax errors below remain located either way. *)
    fun token_start () = if track_locations then pos () else unlocated_pos
    fun token_span start =
      if track_locations then SourceSpan {start = start, stop = pos ()}
      else unlocated_span

    fun peek () =
      case !lookahead of
        NextChar c => SOME c
      | EndOfInput => NONE
      | NeedChar =>
          (case input () of
             SOME c => (lookahead := NextChar c; SOME c)
           | NONE => (lookahead := EndOfInput; NONE))

    fun advance () =
      case peek () of
        NONE => NONE
      | SOME c =>
          (lookahead := NeedChar;
           index := !index + 1;
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

    fun token kind start chars =
      Token {text = String.implode (List.rev chars),
             kind = kind,
             loc = token_span start}

    fun atom start chars =
      case peek () of
        NONE => token AtomToken start chars
      | SOME c =>
          if c = #" " orelse c = #"\t" orelse c = #"\n" orelse
             c = #"\r" orelse c = #"(" orelse c = #")" orelse c = #";"
          then token AtomToken start chars
          else (ignore (advance ()); atom start (c :: chars))

    fun quoted_symbol start chars =
      case advance () of
        NONE => syntax_error "get_token" (mk_point_span (pos ()))
          "unterminated quoted symbol"
      | SOME #"|" => token QuotedSymbolToken start chars
      | SOME c => quoted_symbol start (c :: chars)

    fun string_lit start chars =
      case advance () of
        NONE => syntax_error "get_token" (mk_point_span (pos ()))
          "unterminated string literal"
      | SOME #"\"" =>
          (case peek () of
             SOME #"\"" =>
               (ignore (advance ()); string_lit start (#"\"" :: chars))
           | _ => token StringToken start chars)
      (* SMT-LIB 2.6 string literals have no backslash escapes; the only
         in-string escape is a doubled quote ("") handled above, so every
         other character (backslash included) is taken literally. *)
      | SOME c => string_lit start (c :: chars)
  in
    fn () =>
      (skip_space_and_comments ();
       case peek () of
         NONE => NONE
       | SOME #"(" =>
           let val start = token_start ()
               val _ = advance ()
           in SOME (token AtomToken start [#"("]) end
       | SOME #")" =>
           let val start = token_start ()
               val _ = advance ()
           in SOME (token AtomToken start [#")"]) end
       | SOME #"|" =>
           let val start = token_start ()
               val _ = advance ()
           in SOME (quoted_symbol start []) end
       | SOME #"\"" =>
           let val start = token_start ()
               val _ = advance ()
           in SOME (string_lit start []) end
       | SOME c =>
           let val start = token_start ()
               val _ = advance ()
           in SOME (atom start [c]) end)
  end

  fun make_located_tokenizer (text: string) : unit -> located_token option =
  let
    val len = String.size text
    val index = ref 0

    fun input () =
      if !index >= len then NONE
      else
        let val c = String.sub (text, !index)
        in index := !index + 1; SOME c end
  in
    make_tokenizer_from_input true input
  end

  (* Proof tokens reach the dictionaries as plain strings, so a String token
     is marked with a prefix that no SMT-LIB symbol can carry: control
     characters are excluded from simple symbols by the grammar and from
     quoted symbols by the printable-character requirement.  A token that
     carries the marker anyway is therefore rejected, rather than silently
     taken for a string literal. *)
  val proof_string_token_prefix = "\001HolSmtString:"

  fun make_proof_tokenizer_from_input input =
    let
      val next_token = make_tokenizer_from_input false input
    in
      fn () =>
        case next_token () of
          SOME tok =>
            if token_kind tok = StringToken then
              proof_string_token_prefix ^ token_text tok
            else if String.isPrefix proof_string_token_prefix
                (token_text tok) then
              raise ERR "make_proof_tokenizer_from_input"
                ("symbol '" ^ token_text tok ^
                 "' collides with the string literal marker")
            else
              token_text tok
        | NONE =>
            raise ERR "make_proof_tokenizer_from_input" "end of stream"
    end

  fun make_proof_stream_tokenizer instream =
  let
    val chunk = ref ""
    val index = ref 0

    fun input () =
      if !index < String.size (!chunk) then
        let val c = String.sub (!chunk, !index)
        in index := !index + 1; SOME c end
      else
        let val next = TextIO.inputN (instream, 65536)
        in
          if String.size next = 0 then NONE
          else
            (chunk := next;
             index := 1;
             SOME (String.sub (next, 0)))
        end
  in
    make_proof_tokenizer_from_input input
  end

  fun proof_string_token token =
    if String.isPrefix proof_string_token_prefix token then
      SOME (String.extract
        (token, String.size proof_string_token_prefix, NONE))
    else
      NONE

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

    fun parse_qualified_identifier_from_first tok =
      if token_text tok = "(" then
        let
          val underscore = need_token "parse_term" "'_'"
          val _ = expect_token "parse_term" "_" underscore
          val name_tok = need_token "parse_term" "indexed identifier name"
          val _ =
            if token_kind name_tok = StringToken then
              syntax_error "parse_term" (token_loc name_tok)
                "expected indexed identifier name"
            else
              ()
          fun parse_index index_tok =
            if token_text index_tok = "(" orelse
               token_kind index_tok = StringToken then
              syntax_error "parse_term" (token_loc index_tok)
                "expected identifier index"
            else
              located (token_loc index_tok)
                (TermIdentifier (token_text index_tok))
          val (indices, close_tok) =
            parse_until_rparen "parse_term" parse_index []
          val _ =
            if List.null indices then
              syntax_error "parse_term" (token_loc close_tok)
                "indexed identifier requires at least one index"
            else
              ()
          val loc = combine_span (token_loc tok) (token_loc close_tok)
        in
          located loc
            (TermIndexed
              (parse_atom_name "parse_term" name_tok, indices))
        end
      else if token_text tok = ")" orelse token_kind tok = StringToken then
        syntax_error "parse_term" (token_loc tok)
          "expected qualified identifier"
      else
        located (token_loc tok) (TermIdentifier (token_text tok))

    fun parse_term_from_first tok =
      if token_text tok = "(" then
        parse_term_list tok
      else if token_text tok = ")" then
        syntax_error "parse_term" (token_loc tok) "unexpected ')'"
      else if token_kind tok = StringToken then
        located (token_loc tok) (TermString (token_text tok))
      else
        located (token_loc tok) (TermIdentifier (token_text tok))

    and parse_term_list open_tok =
      let
        val head_tok = need_token "parse_term" "term head"
        val head_text = token_text head_tok
        val reserved_head = token_kind head_tok = AtomToken
      in
        if reserved_head andalso head_text = "_" then
          let
            val first_tok = need_token "parse_term"
              "indexed term name or apply head"
            val first_text = token_text first_tok
            val atom_constant =
              token_kind first_tok = AtomToken andalso
              (SmtLib_Theories.is_numeral first_text orelse
               Lib.can SmtLib_Theories.real_of_decimal first_text orelse
               String.isPrefix "#b" first_text orelse
               String.isPrefix "#x" first_text)
            (* A quoted symbol is an ordinary term even when its text is the
               name of an indexed family (for example, |_|). *)
            val symbol_first =
              token_kind first_tok = AtomToken andalso
              first_text <> "(" andalso first_text <> ")" andalso
              not atom_constant
          in
            if symbol_first then
              let
                val (indices, close_tok) =
                  parse_until_rparen "parse_term" parse_term_from_first []
                val loc = combine_span
                  (token_loc open_tok) (token_loc close_tok)
              in
                located loc
                  (TermIndexed
                    (parse_atom_name "parse_term" first_tok, indices))
              end
            else
              let
                val rator = parse_term_from_first first_tok
                val (args, close_tok) =
                  parse_until_rparen "parse_term" parse_term_from_first []
                val loc = combine_span
                  (token_loc open_tok) (token_loc close_tok)
              in
                located loc
                  (TermApplyOperator
                    (located (token_loc head_tok) head_text, rator, args))
              end
          end
        else if reserved_head andalso head_text = "@" then
          let
            val rator = parse_term_from_first
              (need_token "parse_term" "apply head")
            val (args, close_tok) =
              parse_until_rparen "parse_term" parse_term_from_first []
            val loc = combine_span (token_loc open_tok) (token_loc close_tok)
          in
            located loc
              (TermApplyOperator
                (located (token_loc head_tok) head_text, rator, args))
          end
        else if reserved_head andalso head_text = "as" then
          let
            val term = parse_qualified_identifier_from_first
              (need_token "parse_term" "ascribed identifier")
            val sort = parse_sort ()
            val close_tok = need_token "parse_term" "')'"
            val _ = expect_token "parse_term" ")" close_tok
            val loc = combine_span (token_loc open_tok) (token_loc close_tok)
          in
            located loc (TermAscribed (term, sort))
          end
        else if reserved_head andalso head_text = "set.comprehension" then
          let
            val vars = parse_sorted_var_list ()
            val predicate = parse_term_from_first
              (need_token "parse_term" "set comprehension predicate")
            val value = parse_term_from_first
              (need_token "parse_term" "set comprehension value")
            val close_tok = need_token "parse_term" "')'"
            val _ = expect_token "parse_term" ")" close_tok
            val loc = combine_span (token_loc open_tok) (token_loc close_tok)
            val head = located (token_loc head_tok)
              (TermIdentifier "set.comprehension")
            val predicate = located (loc_of predicate)
              (TermLambda (vars, predicate))
            val value = located (loc_of value) (TermLambda (vars, value))
          in
            located loc (TermApply (head, [predicate, value]))
          end
        else if reserved_head andalso head_text = "let" then
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
        else if reserved_head andalso head_text = "match" then
          let
            fun parse_pattern_from_first tok =
              if token_text tok = "(" then
                let
                  val ctor = parse_atom_name "parse_match_pattern"
                    (need_token "parse_match_pattern" "constructor name")
                  fun parse_binder tok =
                    if token_text tok = "(" orelse token_text tok = ")" then
                      syntax_error "parse_match_pattern" (token_loc tok)
                        ("expected flat pattern binder, found '" ^
                         token_text tok ^ "'")
                    else
                      parse_atom_name "parse_match_pattern" tok
                  val (binders, close_tok) =
                    parse_until_rparen "parse_match_pattern" parse_binder []
                  val loc = combine_span (token_loc tok) (token_loc close_tok)
                in
                  located loc (MatchPatternConstructor (ctor, binders))
                end
              else if token_text tok = ")" then
                syntax_error "parse_match_pattern" (token_loc tok)
                  "unexpected ')'"
              else
                located (token_loc tok)
                  (MatchPatternAtom
                    (located (token_loc tok) (token_text tok)))

            fun parse_branch tok =
              let
                val _ = expect_token "parse_match_branch" "(" tok
                val pattern = parse_pattern_from_first
                  (need_token "parse_match_branch" "match pattern")
                val body = parse_term_from_first
                  (need_token "parse_match_branch" "match branch body")
                val close_tok = need_token "parse_match_branch" "')'"
                val _ = expect_token "parse_match_branch" ")" close_tok
                val loc = combine_span (token_loc tok) (token_loc close_tok)
              in
                located loc (MatchCase (pattern, body))
              end

            val scrutinee = parse_term_from_first
              (need_token "parse_term" "match scrutinee")
            val branches_open = need_token "parse_term" "match branch list"
            val _ = expect_token "parse_term" "(" branches_open
            val (branches, _) =
              parse_until_rparen "parse_term" parse_branch []
            val close_tok = need_token "parse_term" "')'"
            val _ = expect_token "parse_term" ")" close_tok
            val loc = combine_span (token_loc open_tok) (token_loc close_tok)
          in
            located loc (TermMatch (scrutinee, branches))
          end
        else if reserved_head andalso
                (head_text = "forall" orelse head_text = "exists" orelse
                 head_text = "lambda") then
          let
            val vars = parse_sorted_var_list ()
            val _ =
              if head_text = "lambda" andalso List.null vars then
                syntax_error "parse_term" (token_loc head_tok)
                  "lambda requires at least one sorted variable"
              else ()
            val body = parse_term_from_first
              (need_token "parse_term" "binder body")
            val close_tok = need_token "parse_term" "')'"
            val _ = expect_token "parse_term" ")" close_tok
            val loc = combine_span (token_loc open_tok) (token_loc close_tok)
          in
            if head_text = "forall" then
              located loc (TermForall (vars, body))
            else if head_text = "exists" then
              located loc (TermExists (vars, body))
            else
              located loc (TermLambda (vars, body))
          end
        else if reserved_head andalso head_text = "!" then
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
  let
    fun try_fns [] last_err = (NONE, last_err)
      | try_fns (f :: fs) last_err =
          (SOME (f token indices args), last_err)
          handle Interrupt => raise Interrupt
               | Feedback.HOL_ERR holerr => try_fns fs (SOME holerr)
               | _ => try_fns fs last_err
    val primary_fns = Redblackmap.find (dict, token)
      handle Redblackmap.NotFound => []
    val catch_all_fns = Redblackmap.find (dict, "_")
      handle Redblackmap.NotFound => []
    fun generic_msg detail =
      "failed to parse '" ^ token ^ "' (with indices [" ^
      String.concatWith ", " (List.map Hol_pp.term_to_string indices) ^
      "] and " ^ Int.toString (List.length args) ^ " argument(s))" ^
      detail
  in
    case try_fns primary_fns NONE of
      (SOME result, _) => result
    | (NONE, primary_err) =>
        (case try_fns catch_all_fns NONE of
           (SOME result, _) => result
         | (NONE, catch_all_err) =>
             (* The entry registered under this very name knows why it
                rejected the input; the '_' catch-all only knows that the
                token is not one of its own literals.  Report the specific
                reason, so an enumerated diagnostic is not masked by a
                generic one. *)
             (case (primary_err, catch_all_err) of
                (SOME holerr, _) =>
                  raise ERR "t_with_args"
                    (generic_msg (": " ^ Feedback.message_of holerr))
              | (NONE, SOME holerr) =>
                  raise ERR "t_with_args"
                    (generic_msg (": " ^ Feedback.message_of holerr))
              | (NONE, NONE) => raise ERR "t_with_args" (generic_msg "")))
  end

  fun declared_sort_parsefn sort_name arity =
  let
    val nullary_ty = Type.mk_vartype ("'" ^ sort_name)
    val cache = ref ([] : (Type.hol_type list * Type.hol_type) list)
    fun same_args (args1, args2) =
      Lib.list_compare Type.compare (args1, args2) = EQUAL
    fun cached_ty args =
      case List.find (fn (cached_args, _) => same_args (cached_args, args)) (!cache) of
        SOME (_, ty) => ty
      | NONE =>
          let
            val ty = Type.gen_tyvar ()
          in
            cache := (args, ty) :: !cache;
            ty
          end
    fun arity_mismatch actual =
      raise ERR ("<" ^ sort_name ^ ">")
        ("declare-sort arity mismatch for '" ^ sort_name ^ "': expected " ^
         Int.toString arity ^ ", actual " ^ Int.toString actual)
  in
    fn token => fn indices => fn args =>
      if not (List.null indices) then
        raise ERR ("<" ^ sort_name ^ ">")
          ("declare-sort arity mismatch for '" ^ sort_name ^
           "': expected no indices, actual " ^
           Int.toString (List.length indices))
      else if List.length args = arity then
        if arity = 0 then nullary_ty else cached_ty args
      else
        arity_mismatch (List.length args)
  end

  fun same_sort ty1 ty2 = Type.compare (ty1, ty2) = EQUAL

  fun int_to_real_expected expected actual =
    same_sort expected realSyntax.real_ty andalso same_sort actual intSyntax.int_ty

  fun coerce_int_arg_to_real arg =
    if same_sort (Term.type_of arg) intSyntax.int_ty then
      (intrealSyntax.mk_real_of_int arg, true)
    else
      (arg, false)

  fun coerce_int_args_to_real args =
    let
      val coerced = List.map coerce_int_arg_to_real args
    in
      (List.map Lib.fst coerced, List.exists Lib.snd coerced)
    end

  fun coerce_arg_to_expected expected arg =
    if int_to_real_expected expected (Term.type_of arg) then
      intrealSyntax.mk_real_of_int arg
    else
      arg

  fun coerce_args_to_expected domain args =
    ListPair.map (fn (expected, arg) => coerce_arg_to_expected expected arg)
      (domain, args)

  fun list_mk_comb_coerce_int_to_real tm domain args =
    Term.list_mk_comb (tm, coerce_args_to_expected domain args)

  fun t_with_term_args dict token indices args =
    t_with_args dict token indices args
    handle original as Feedback.HOL_ERR _ =>
      let
        val (coerced_args, changed) = coerce_int_args_to_real args
      in
        if changed then
          t_with_args dict token indices coerced_args
          handle Feedback.HOL_ERR _ => raise original
        else
          raise original
      end

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

  (* Indices are numerals, except that the Unicode strings theory writes
     character indices as hexadecimal literals, as in '(_ char #x2A)'.
     Both forms are turned into a numeral here, so that no consumer of an
     index has to recover one from the token text. *)
  fun index_numeral_term token =
  let
    fun radix from_string =
      let
        fun bad () =
          raise ERR "index_numeral_term"
            ("index numeral expected, but '" ^ token ^ "' found")
      in
        from_string (String.extract (token, 2, NONE))
        (* Moscow ML's Arbnum implementation throws Option.Option on error,
           while Poly/ML's throws the Fail exception *)
        handle Option.Option => bad ()
             | Fail _ => bad ()
      end
    val value =
      if String.isPrefix "#x" token then radix Arbnum.fromHexString
      else if String.isPrefix "#b" token then radix Arbnum.fromBinString
      else Library.parse_arbnum token
  in
    intSyntax.term_of_int (Arbint.fromNat value)
  end

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
        index_numeral_term token
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
    t_with_term_args tmdict head (get_indices [])
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
    (* CVC's CPC printer represents a binder list as ``(@list @t1 ...)``.
       This is deliberately accepted only for the explicit marker; ordinary
       SMT-LIB binders continue through [parse_sorted_vars].  The referenced
       entries must already be terms in the current dictionary and, crucially,
       must be HOL variables. *)
    val binder_open = get_token ()
    val binder_head = get_token ()
    val (vars, cpc_binders, get_token) =
      if binder_open = "(" andalso binder_head = "@list" then
        let
          fun parse_vars acc =
            let val token = get_token () in
              if token = ")" then List.rev acc
              else
                let
                  val tm = parse_term_aux cfg get_token (tydict, tmdict)
                    token []
                  val _ = Term.is_var tm orelse
                    raise ERR "parse_binder_term"
                      "CPC @list binder contains a non-variable term"
                in parse_vars ((Lib.fst (Term.dest_var tm), tm) :: acc) end
            end
        in
          (parse_vars [], true, get_token)
        end
      else
        let
          val get_token = Library.undo_look_ahead
            [binder_open, binder_head] get_token
          val sorted_vars = parse_sorted_vars get_token tydict
        in
          (List.map (fn vT => (Lib.fst vT, Term.mk_var vT)) sorted_vars,
           false, get_token)
        end
    (* variables don't take arguments *)
    fun parsefn var token indices args =
      if List.null indices andalso List.null args then
        var
      else
        raise ERR ("<" ^ Hol_pp.term_to_string var ^ ">")
          "wrong number of arguments"
    val tmdict = if cpc_binders then tmdict else
      List.foldl Library.extend_dict tmdict
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

  (* Z3 proofs use the ArraysEx constant-array spelling
       [((as const (Array I E)) e)].  Unlike a benchmark command, proof
     parsing does not run through the located AST typechecker, so recognize
     its qualified head directly and make the curried constant-array function
     which the enclosing application supplies with [e]. *)
  and parse_ascribed_term cfg get_token (tydict, tmdict) : Term.term =
  let
    val name = get_token ()
  in
    if name = "const" then
      let
        val array_ty = parse_type get_token tydict
        val (domain, range) = Type.dom_rng array_ty
          handle Feedback.HOL_ERR _ =>
            raise ERR "parse_ascribed_term"
              "Z3 const expects an Array sort"
        val payload = Term.mk_var ("array_const_value", range)
        val index = Term.variant [payload]
          (Term.mk_var ("array_const_index", domain))
        val _ = Library.expect_token ")" (get_token ())
      in
        Term.mk_abs (payload, Term.mk_abs (index, payload))
      end
    else if name = "union" then
      let
        val array_ty = parse_type get_token tydict
        val (_, range) = Type.dom_rng array_ty
          handle Feedback.HOL_ERR _ =>
            raise ERR "parse_ascribed_term"
              "Z3 union expects an Array sort"
        val _ = if range = Type.bool then () else
          raise ERR "parse_ascribed_term"
            "Z3 union expects an Array with Bool range"
        val left = Term.mk_var ("array_union_left", array_ty)
        val right = Term.mk_var ("array_union_right", array_ty)
        val _ = Library.expect_token ")" (get_token ())
      in
        Term.mk_abs (left, Term.mk_abs (right,
          pred_setSyntax.mk_union (left, right)))
      end
    else
      (* Preserve proof-dialect qualified identifiers already supplied by
         the Z3 dictionary, notably [(as seq.empty (Seq A))]. *)
      parse_compound_term cfg (Library.undo_look_ahead [name] get_token)
        (tydict, tmdict) "as"
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
    else if token = "as" then
      let
        val t = parse_ascribed_term cfg get_token (tydict, tmdict)
        fun apply_const_array payload =
          let
            val (variable, body) = Term.dest_abs t
            val (index, _) = Term.dest_abs body
            val domain = Term.type_of index
            val range = Term.type_of variable
          in
            if range = Type.bool andalso Term.aconv payload boolSyntax.F then
              pred_setSyntax.mk_empty domain
            else if range = Type.bool andalso
                    Term.aconv payload boolSyntax.T then
              pred_setSyntax.mk_univ domain
            else Term.subst [{redex = variable, residue = payload}] body
          end
        fun apply_one (argument, function) =
          case Lib.total Term.dest_abs function of
            SOME (variable, body) =>
              Term.subst [{redex = variable, residue = argument}] body
          | NONE => Term.mk_comb (function, argument)
      in
        fn [payload] => apply_const_array payload
          | args => List.foldl apply_one t args
      end
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
          else if token = "choice" andalso #parse_choice cfg then
            parse_binder_term cfg get_token (tydict, tmdict)
              (fn (vars, body) =>
                List.foldr (fn (v, acc) => boolSyntax.mk_select (v, acc))
                  body vars)
          (* Lambda parsing is enabled only for proof-certificate dialects;
             benchmark lambdas use the located AST typechecker.  Preserve the
             binder as a genuine HOL abstraction so bound variables cannot
             escape as free variables. *)
          else if token = "lambda" andalso #parse_lambda cfg then
            parse_binder_term cfg get_token (tydict, tmdict)
              (fn (vars, body) => Term.list_mk_abs (vars, body))
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
      t_with_term_args tmdict token []

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
    parse_choice = false,
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
      val keyword = get_token ()
      val _ = Library.expect_token ")" (get_token ())
    in
      keyword
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
  fun parse_declare_sort get_token tydict =
  let
    val name = get_token ()
    val arity_text = get_token ()
    val arity =
      case Int.fromString arity_text of
        SOME n =>
          if n < 0 then raise ERR "parse_declare_sort"
            ("declare-sort arity for '" ^ name ^ "' must be non-negative")
          else n
      | NONE => raise ERR "parse_declare_sort"
          ("declare-sort arity for '" ^ name ^
           "' must be a numeral, got '" ^ arity_text ^ "'")
    val _ = Library.expect_token ")" (get_token ())
    val parsefn = declared_sort_parsefn name arity
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
        list_mk_comb_coerce_int_to_real tm domain_types args
      else
        raise ERR ("<" ^ name ^ ">") "wrong number of arguments"
  in
    (tm, Library.extend_dict ((name, parsefn), tmdict))
  end

  val parse_declare_const = parse_declare_const_fun false
  val parse_declare_fun = parse_declare_const_fun true

  fun legacy_datatype_type name =
    Type.mk_vartype ("'smtlib_dt_" ^ name)

  fun legacy_extend_datatype_sort command name arity_text tydict =
  let
    val arity =
      case Int.fromString arity_text of
        SOME n => n
      | NONE => raise ERR command
          ("declare-datatypes arity for '" ^ name ^
           "' must be a numeral, got '" ^ arity_text ^ "'")
    val _ =
      if arity = 0 then ()
      else raise ERR command
        ("declare-datatypes arity for '" ^ name ^
         "': unsupported legacy parser arity " ^ arity_text)
    val datatype_ty = legacy_datatype_type name
    fun parse_ty token indices args =
      if List.null indices andalso List.null args then
        datatype_ty
      else
        raise ERR ("<" ^ name ^ ">") "wrong number of arguments"
  in
    Library.extend_dict ((name, parse_ty), tydict)
  end

  fun parse_datatype_decl_body get_token command name datatype_ty tydict tmdict =
  let
    fun add_constructor (ctor_name, selectors, tmdict) =
      let
        val arg_tys = List.map Lib.snd selectors
        val ctor_tm = Term.mk_var (ctor_name,
          boolSyntax.list_mk_fun (arg_tys, datatype_ty))
        val args_count = List.length arg_tys
        fun ctor_parse token indices args =
          if List.null indices andalso List.length args = args_count then
            list_mk_comb_coerce_int_to_real ctor_tm arg_tys args
          else
            raise ERR ("<" ^ ctor_name ^ ">") "wrong number of arguments"
        fun selector_entry ((selector_name, selector_ty), tmdict) =
          let
            val selector_tm = Term.mk_var (selector_name,
              Type.--> (datatype_ty, selector_ty))
            fun selector_parse token indices args =
              if List.null indices andalso List.length args = 1 then
                list_mk_comb_coerce_int_to_real selector_tm [datatype_ty] args
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
        raise ERR command
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
  in
    tmdict
  end

  fun parse_declare_datatype get_token (tydict, tmdict) =
  let
    val name = get_token ()
    val datatype_ty = legacy_datatype_type name
    val tydict = legacy_extend_datatype_sort "declare-datatype" name "0" tydict
    val tmdict = parse_datatype_decl_body get_token "declare-datatype"
      name datatype_ty tydict tmdict
    val _ = Library.expect_token ")" (get_token ())
  in
    (tydict, tmdict)
  end

  fun parse_declare_datatypes get_token (tydict, tmdict) =
  let
    fun parse_binding acc =
      let
        val token = get_token ()
      in
        if token = ")" then
          List.rev acc
        else
          let
            val _ = Library.expect_token "(" token
            val name = get_token ()
            val arity = get_token ()
            val _ = Library.expect_token ")" (get_token ())
          in
            parse_binding ((name, arity) :: acc)
          end
      end

    val _ = Library.expect_token "(" (get_token ())
    val bindings = parse_binding []
    val _ =
      if List.null bindings then
        raise ERR "declare-datatypes" "empty declare-datatypes command"
      else ()
    val tydict =
      List.foldl
        (fn ((name, arity), tydict) =>
          legacy_extend_datatype_sort "declare-datatypes" name arity tydict)
        tydict bindings

    fun parse_decls [] tmdict =
      let val token = get_token ()
      in
        Library.expect_token ")" token;
        tmdict
      end
      | parse_decls ((name, _) :: rest) tmdict =
        let
          val datatype_ty = legacy_datatype_type name
          val tmdict = parse_datatype_decl_body get_token "declare-datatypes"
            name datatype_ty tydict tmdict
        in
          parse_decls rest tmdict
        end

    val _ = Library.expect_token "(" (get_token ())
    val tmdict = parse_decls bindings tmdict
    val _ = Library.expect_token ")" (get_token ())
  in
    (tydict, tmdict)
  end

  fun define_fun_signature name vars range_type tmdict =
  let
    val domain_types = List.map (Term.type_of o Lib.snd) vars
    val tm = Term.mk_var (name,
      boolSyntax.list_mk_fun (domain_types, range_type))
    val args_count = List.length domain_types
    fun parsefn token indices args =
      if List.null indices andalso List.length args = args_count then
        list_mk_comb_coerce_int_to_real tm domain_types args
      else
        raise ERR ("<" ^ name ^ ">") "wrong number of arguments"
    val tmdict = Library.extend_dict ((name, parsefn), tmdict)
  in
    (tm, tmdict)
  end

  fun define_fun_equation tm vars definiens =
  let
    val vars = List.map Lib.snd vars
  in
    boolSyntax.list_mk_forall (vars,
      boolSyntax.mk_eq (Term.list_mk_comb (tm, vars), definiens))
  end

  fun define_fun_term name vars range_type definiens tmdict =
  let
    val (tm, tmdict) = define_fun_signature name vars range_type tmdict
    val definition = define_fun_equation tm vars definiens
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

  fun add_sorted_vars_to_legacy_tmdict vars tmdict =
  let
    fun var_parsefn var token indices args =
      if List.null indices andalso List.null args then
        var
      else
        raise ERR ("<" ^ Hol_pp.term_to_string var ^ ">")
          "wrong number of arguments"
  in
    List.foldl Library.extend_dict tmdict
      (List.map (Lib.apsnd var_parsefn) vars)
  end

  fun parse_legacy_fun_signature get_token tydict =
  let
    val _ = Library.expect_token "(" (get_token ())
    val name = get_token ()
    val vars = parse_sorted_vars get_token tydict
    val range_type = parse_type get_token tydict
    val _ = Library.expect_token ")" (get_token ())
    val vars = List.map (fn vT => (Lib.fst vT, Term.mk_var vT)) vars
  in
    (name, vars, range_type)
  end

  fun parse_define_fun_rec get_token (tydict, tmdict) =
  let
    val name = get_token ()
    val vars = parse_sorted_vars get_token tydict
    val range_type = parse_type get_token tydict
    val vars = List.map (fn vT => (Lib.fst vT, Term.mk_var vT)) vars
    val (tm, tmdict) = define_fun_signature name vars range_type tmdict
    val definiens_tmdict = add_sorted_vars_to_legacy_tmdict vars tmdict
    val definiens = parse_term get_token (tydict, definiens_tmdict)
    val _ = Library.expect_token ")" (get_token ())
  in
    (tmdict, define_fun_equation tm vars definiens)
  end

  fun parse_define_funs_rec get_token (tydict, tmdict) =
  let
    fun parse_signatures tmdict specs =
      let val token = get_token ()
      in
        if token = ")" then
          (tmdict, List.rev specs)
        else
          let
            val get_token' = Library.undo_look_ahead [token] get_token
            val (name, vars, range_type) =
              parse_legacy_fun_signature get_token' tydict
            val (tm, tmdict) =
              define_fun_signature name vars range_type tmdict
          in
            parse_signatures tmdict ((tm, vars) :: specs)
          end
      end

    fun malformed_count () =
      raise ERR "define-funs-rec"
        "malformed recursive definition block: function signature count does not match body count"

    fun parse_bodies tmdict [] definitions =
      let val token = get_token ()
      in
        if token = ")" then List.rev definitions else malformed_count ()
      end
      | parse_bodies tmdict ((tm, vars) :: specs) definitions =
        let val token = get_token ()
        in
          if token = ")" then
            malformed_count ()
          else
            let
              val get_token' = Library.undo_look_ahead [token] get_token
              val body_tmdict = add_sorted_vars_to_legacy_tmdict vars tmdict
              val definiens = parse_term get_token' (tydict, body_tmdict)
              val definition = define_fun_equation tm vars definiens
            in
              parse_bodies tmdict specs (definition :: definitions)
            end
        end

    val _ = Library.expect_token "(" (get_token ())
    val (tmdict, specs) = parse_signatures tmdict []
    val _ = Library.expect_token "(" (get_token ())
    val definitions = parse_bodies tmdict specs []
    val _ = Library.expect_token ")" (get_token ())
  in
    (tmdict, definitions)
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
        assertions = frame_assertions frame,
        named_assertions = frame_named_assertions frame,
        local_definitions = assertion :: frame_local_definitions frame
      }) state

  fun add_assertions assertions state =
    List.foldl
      (fn (assertion, state) => add_assertion assertion NONE state)
      state assertions

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

  fun check_sat_query state assumptions =
    QueryCheckSat {
      assumptions = assumptions,
      assertions = active_assertions state,
      local_definitions = active_local_definitions state,
      transfer_hypotheses = []
    }

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

  fun empty_surface_flags () = SmtLib_Logics.empty_surface_flags

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
     queries = List.rev queries,
     surface_flags = empty_surface_flags ()}
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
        val option = parse_get_info get_token
        val command_state = dest_state "get-info" state
      in
        parse_commands get_token
          (SOME (add_query (QueryGetInfo option) command_state))
      end
    | "get-option" =>
      let
        val option = parse_get_option get_token
        val command_state = dest_state "get-option" state
      in
        parse_commands get_token
          (SOME (add_query (QueryGetOption option) command_state))
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
      let
        val command_state = dest_state "define-fun-rec" state
        val (tydict, tmdict) = current_dicts command_state
        val (tmdict, def) = parse_define_fun_rec get_token (tydict, tmdict)
        val command_state = update_current_dicts (tydict, tmdict) command_state
      in
        parse_commands get_token (SOME (add_assertion def NONE command_state))
      end
    | "define-funs-rec" =>
      let
        val command_state = dest_state "define-funs-rec" state
        val (tydict, tmdict) = current_dicts command_state
        val (tmdict, defs) = parse_define_funs_rec get_token (tydict, tmdict)
        val command_state = update_current_dicts (tydict, tmdict) command_state
      in
        parse_commands get_token (SOME (add_assertions defs command_state))
      end
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
      let
        val command_state = dest_state "declare-datatypes" state
        val (tydict, tmdict) = current_dicts command_state
        val (tydict, tmdict) = parse_declare_datatypes get_token
          (tydict, tmdict)
      in
        parse_commands get_token
          (SOME (update_current_dicts (tydict, tmdict) command_state))
      end
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
          (SOME (add_query (check_sat_query command_state []) command_state))
      end
    | "check-sat-assuming" =>
      let
        val command_state = dest_state "check-sat-assuming" state
        val assumptions = parse_term_list get_token (current_dicts command_state)
        val _ = Library.expect_token ")" (get_token ())
      in
        parse_commands get_token
          (SOME (add_query (check_sat_query command_state assumptions)
            command_state))
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
      in
        parse_commands get_token
          (SOME (add_query QueryGetUnsatAssumptions command_state))
      end
    | "get-unsat-core" =>
      let
        val command_state = dest_state "get-unsat-core" state
        val _ = Library.expect_token ")" (get_token ())
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

  datatype surface_sort =
      RigidSort of Type.hol_type
    | PolySort of Type.hol_type
    | ConstructorSort of Type.hol_type * surface_sort list
    | ArraySort of surface_sort * surface_sort
    | MapSort of surface_sort * surface_sort

  fun is_set_surface surface =
    case surface of
      ConstructorSort (ty, _) => pred_setSyntax.is_set_type ty
    | _ => false

  type function_signature = {
    tm: Term.term,
    domain: Type.hol_type list,
    domain_surface: surface_sort list,
    range: Type.hol_type,
    range_surface: surface_sort
  }

  type function_signature_dict =
    (string, function_signature list) Redblackmap.dict

  type typecheck_frame = {
    tydict: Type.hol_type dict,
    tmdict: Term.term dict,
    sigdict: function_signature_dict,
    finite_sets: Term.term list,
    assertions: Term.term list,
    named_assertions: (string * Term.term) list,
    local_definitions: Term.term list
  }

  type typecheck_state = {
    logic: string,
    frames: typecheck_frame list,
    queries: query_command list,
    surface_flags: surface_flags ref
  }

  type metadata_index =
    (string, SmtLib_Theories.symbol_metadata list) Redblackmap.dict

  type typecheck_context = {
    description: string,
    solver: string option,
    surface_flags: surface_flags ref,
    metadata_index: metadata_index
  }

  datatype surface_event =
      ArrowSortUsed
    | LambdaUsed
    | ApplyOperatorUsed
    | PartialApplicationUsed

  datatype checked_term =
    CheckedTerm of {
      term: Term.term,
      sort: Type.hol_type,
      surface_sort: surface_sort
    }

  datatype checked_match_branch =
      CheckedMatchConstructor of {
        smt_name: string,
        hol_name: string,
        constructor: Term.term,
        pattern: Term.term,
        body: checked_term,
        loc: source_span
      }
    | CheckedMatchDefault of {
        var: Term.term,
        body: checked_term,
        loc: source_span
      }

  fun checked_term_with_surface_sort surface_sort t =
    CheckedTerm {term = t, sort = Term.type_of t, surface_sort = surface_sort}
  fun checked_term_of t =
    checked_term_with_surface_sort (RigidSort (Term.type_of t)) t
  fun checked_term (CheckedTerm {term, ...}) = term
  fun checked_sort (CheckedTerm {sort, ...}) = sort
  fun checked_surface_sort (CheckedTerm {surface_sort, ...}) = surface_sort

  fun surface_bindings (expected, actual) =
    case (expected, actual) of
      (PolySort ty, _) => [(ty, actual)]
    | (ConstructorSort (_, expected_args),
       ConstructorSort (_, actual_args)) =>
        List.concat
          (ListPair.map surface_bindings (expected_args, actual_args))
    | (MapSort (expected_domain, expected_range),
       MapSort (actual_domain, actual_range)) =>
        surface_bindings (expected_domain, actual_domain) @
        surface_bindings (expected_range, actual_range)
    | (ArraySort (expected_index, expected_element),
       ArraySort (actual_index, actual_element)) =>
        surface_bindings (expected_index, actual_index) @
        surface_bindings (expected_element, actual_element)
    | _ => []

  fun instantiate_surface_sort_with bindings subst surface_sort =
    case surface_sort of
      PolySort ty =>
        (* An unbound polymorphic position stays polymorphic: it never
           claimed a surface structure, so collapsing it to 'RigidSort'
           would assert that it is atomic and reject a structured term of
           the very same sort. *)
        (case List.find (fn (template, _) => same_sort template ty) bindings of
           SOME (_, actual) => actual
         | NONE => PolySort (Type.type_subst subst ty))
    | ConstructorSort (ty, args) =>
        ConstructorSort (Type.type_subst subst ty,
          List.map (instantiate_surface_sort_with bindings subst) args)
    | MapSort (domain, range) =>
        MapSort (instantiate_surface_sort_with bindings subst domain,
          instantiate_surface_sort_with bindings subst range)
    | ArraySort (index, element) =>
        ArraySort (instantiate_surface_sort_with bindings subst index,
          instantiate_surface_sort_with bindings subst element)
    | RigidSort ty => RigidSort ty

  fun instantiate_surface_sort subst surface_sort =
    instantiate_surface_sort_with [] subst surface_sort

  fun surface_sort_compatible expected actual =
    case (expected, actual) of
      (PolySort _, _) => true
    | (RigidSort expected_ty, RigidSort actual_ty) =>
        same_sort expected_ty actual_ty orelse
        int_to_real_expected expected_ty actual_ty
    | (ConstructorSort (expected_ty, expected_args),
       ConstructorSort (actual_ty, actual_args)) =>
        Lib.can (Type.match_type expected_ty) actual_ty andalso
        ListPair.allEq
          (fn (expected_arg, actual_arg) =>
            surface_sort_compatible expected_arg actual_arg)
          (expected_args, actual_args)
    | (MapSort (expected_domain, expected_range),
       MapSort (actual_domain, actual_range)) =>
        surface_sort_compatible expected_domain actual_domain andalso
        surface_sort_compatible expected_range actual_range
    | (ArraySort (expected_index, expected_element),
       ArraySort (actual_index, actual_element)) =>
        surface_sort_compatible expected_index actual_index andalso
        surface_sort_compatible expected_element actual_element
    | _ => false

  fun surface_sorts_equivalent left right =
    surface_sort_compatible left right orelse
    surface_sort_compatible right left

  fun surface_sort_type surface_sort =
    case surface_sort of
      RigidSort ty => ty
    | PolySort ty => ty
    | ConstructorSort (ty, _) => ty
    | MapSort (domain, range) =>
        Type.--> (surface_sort_type domain, surface_sort_type range)
    | ArraySort (index, element) =>
        Type.--> (surface_sort_type index, surface_sort_type element)

  fun surface_component_of_type ty surface_sort =
    if same_sort ty (surface_sort_type surface_sort) then SOME surface_sort
    else
      case surface_sort of
        ConstructorSort (_, args) =>
          Lib.get_first (surface_component_of_type ty) args
      | MapSort (domain, range) =>
          Lib.get_first (surface_component_of_type ty) [domain, range]
      | ArraySort (index, element) =>
          Lib.get_first (surface_component_of_type ty) [index, element]
      | _ => NONE

  fun type_to_string ty = Hol_pp.type_to_string ty

  fun sort_list_to_string tys =
    "[" ^ String.concatWith ", " (List.map type_to_string tys) ^ "]"

  (* Index the term-kind symbol metadata by name.  This depends only on the
     logic's dictionary, so a caller handling one command builds it once and
     reuses it across the several `command_context` values it needs (see the
     memoized `context` in `typecheck_command`). *)
  fun build_metadata_index dictionary_metadata =
    List.foldl
      (fn (metadata as {kind, name, ...}
             : SmtLib_Theories.symbol_metadata, index) =>
        if kind = "term" then
          Redblackmap.insert
            (index, name,
             metadata ::
               Option.getOpt (Redblackmap.peek (index, name), []))
        else
          index)
      (Redblackmap.mkDict String.compare)
      dictionary_metadata

  fun command_context solver surface_flags metadata_index command =
    {
      description = "command '" ^ command ^ "'",
      solver = solver,
      surface_flags = surface_flags,
      metadata_index = metadata_index
    } : typecheck_context

  fun metadata_has_term
      ({metadata_index, ...}: typecheck_context) predicate name =
    case Redblackmap.peek (metadata_index, name) of
      NONE => false
    | SOME entries =>
        List.exists (fn {attributes, ...} => predicate attributes) entries

  fun indexed_term_family context name =
    metadata_has_term context (fn attributes => #indexed attributes) name

  fun apply_operator_available
      ({metadata_index, ...}: typecheck_context) operator =
    case Redblackmap.peek (metadata_index, operator) of
      NONE => false
    | SOME entries =>
        List.exists (fn {theory, ...} => theory = "HO-Core") entries

  (* Each surface flag is a monotone (false -> true) marker.  OR the current
     value with whether this event targets the flag, so the record is rebuilt
     once with no field copied verbatim across branches. *)
  fun note_surface_event
      ({surface_flags, ...}: typecheck_context) event =
    let
      val {arrow_sort_used, lambda_used, apply_operator_used,
        partial_application_used} = !surface_flags
    in
      surface_flags := {
        arrow_sort_used = arrow_sort_used orelse event = ArrowSortUsed,
        lambda_used = lambda_used orelse event = LambdaUsed,
        apply_operator_used =
          apply_operator_used orelse event = ApplyOperatorUsed,
        partial_application_used =
          partial_application_used orelse event = PartialApplicationUsed
      }
    end

  fun note_arrow_sort_used context =
    note_surface_event context ArrowSortUsed

  fun type_error fn_name ({description, ...}: typecheck_context) loc expected
      actual detail =
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
         " in " ^ description ^ expected_s ^ actual_s ^ ": " ^ detail)
    end

  fun expect_checked_sort fn_name context loc expected checked =
    if checked_sort checked = expected then
      checked_term checked
    else
      type_error fn_name context loc (SOME expected) (SOME (checked_sort checked))
        "sort mismatch"

  fun expect_checked_surface_sort fn_name context loc expected_ty
      expected_surface checked =
    if checked_sort checked = expected_ty andalso
       surface_sort_compatible expected_surface
         (checked_surface_sort checked) then
      checked_term checked
    else
      type_error fn_name context loc (SOME expected_ty)
        (SOME (checked_sort checked)) "surface sort mismatch"

  fun located_string_node x = node_of x

  fun typecheck_frame_tydict ({tydict, ...}: typecheck_frame) = tydict
  fun typecheck_frame_tmdict ({tmdict, ...}: typecheck_frame) = tmdict
  fun typecheck_frame_sigdict ({sigdict, ...}: typecheck_frame) = sigdict
  fun typecheck_frame_finite_sets ({finite_sets, ...}: typecheck_frame) =
    finite_sets
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
    finite_sets = [],
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
      ({logic, frames, queries, surface_flags}: typecheck_state) =
    case frames of
      frame :: rest =>
        {logic = logic, frames = f frame :: rest, queries = queries,
         surface_flags = surface_flags}
    | [] => raise ERR "update_current_typecheck_frame" "empty assertion stack"

  fun update_current_typecheck_dicts (tydict, tmdict, sigdict) state =
    update_current_typecheck_frame
      (fn frame => {
        tydict = tydict,
        tmdict = tmdict,
        sigdict = sigdict,
        finite_sets = typecheck_frame_finite_sets frame,
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
        finite_sets = typecheck_frame_finite_sets frame,
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
        finite_sets = typecheck_frame_finite_sets frame,
        assertions = typecheck_frame_assertions frame,
        named_assertions = typecheck_frame_named_assertions frame,
        local_definitions = assertion :: typecheck_frame_local_definitions frame
      }) state

  fun add_typechecked_query query
      ({logic, frames, queries, surface_flags}: typecheck_state) =
    {logic = logic, frames = frames, queries = query :: queries,
     surface_flags = surface_flags}

  (* A cvc5 declaration returning a Set promises a finite result at every
     argument tuple, not only when it happens to be a nullary declaration. *)
  fun add_typechecked_finite_set set_tm domain state =
    let
      fun mk_vars _ [] = []
        | mk_vars index (ty :: tys) =
            Term.mk_var ("finite_set_arg" ^ Int.toString index, ty) ::
            mk_vars (index + 1) tys
      val vars = mk_vars 0 domain
      val finite = boolSyntax.list_mk_forall
        (vars, pred_setSyntax.mk_finite (Term.list_mk_comb (set_tm, vars)))
    in
      update_current_typecheck_frame
        (fn frame => {
          tydict = typecheck_frame_tydict frame,
          tmdict = typecheck_frame_tmdict frame,
          sigdict = typecheck_frame_sigdict frame,
          finite_sets = finite :: typecheck_frame_finite_sets frame,
          assertions = typecheck_frame_assertions frame,
          named_assertions = typecheck_frame_named_assertions frame,
          local_definitions = typecheck_frame_local_definitions frame
        }) state
    end

  fun finite_bag_term bag_tm =
    Term.mk_comb
      (Term.mk_thy_const {Thy = "bag", Name = "FINITE_BAG",
        Ty = Type.--> (Term.type_of bag_tm, Type.bool)}, bag_tm)

  (* A cvc5 declaration returning a Bag promises a finite result at every
     argument tuple, not only when it happens to be a nullary declaration. *)
  fun add_typechecked_finite_bag bag_tm domain state =
    let
      fun mk_vars _ [] = []
        | mk_vars index (ty :: tys) =
            Term.mk_var ("finite_bag_arg" ^ Int.toString index, ty) ::
            mk_vars (index + 1) tys
      val vars = mk_vars 0 domain
      val finite = boolSyntax.list_mk_forall
        (vars, finite_bag_term (Term.list_mk_comb (bag_tm, vars)))
    in
      update_current_typecheck_frame
        (fn frame => {
          tydict = typecheck_frame_tydict frame,
          tmdict = typecheck_frame_tmdict frame,
          sigdict = typecheck_frame_sigdict frame,
          finite_sets = finite :: typecheck_frame_finite_sets frame,
          assertions = typecheck_frame_assertions frame,
          named_assertions = typecheck_frame_named_assertions frame,
          local_definitions = typecheck_frame_local_definitions frame
        }) state
    end

  fun active_typechecked_assertions ({frames, ...}: typecheck_state) =
    List.concat
      (List.map
        (List.rev o typecheck_frame_assertions)
        (List.rev frames))

  fun active_typechecked_named_assertions ({frames, ...}: typecheck_state) =
    List.concat
      (List.map (List.rev o typecheck_frame_named_assertions) (List.rev frames))

  fun active_typechecked_finite_sets ({frames, ...}: typecheck_state) =
    List.concat
      (List.map (List.rev o typecheck_frame_finite_sets) (List.rev frames))

  fun active_typechecked_local_definitions ({frames, ...}: typecheck_state) =
    List.concat
      (List.map (List.rev o typecheck_frame_local_definitions) (List.rev frames))

  fun typechecked_check_sat_query state assumptions =
    QueryCheckSat {
      assumptions = assumptions,
      assertions = active_typechecked_assertions state,
      local_definitions = active_typechecked_local_definitions state,
      transfer_hypotheses = active_typechecked_finite_sets state
    }

  val reset_logic_prefix = "__HOLSMT_RESET__:"

  fun reset_logic logic = reset_logic_prefix ^ logic

  fun is_reset_logic logic = String.isPrefix reset_logic_prefix logic

  fun visible_logic logic =
    if is_reset_logic logic then
      String.extract (logic, String.size reset_logic_prefix, NONE)
    else logic

  fun has_active_typecheck_state state =
    case state of
      SOME {logic, ...} => not (is_reset_logic logic)
    | NONE => false

  fun new_typecheck_state logic tydict tmdict =
    {logic = logic,
     frames = [mk_typecheck_frame tydict tmdict (empty_sigdict ())],
     queries = [],
     surface_flags = ref (empty_surface_flags ())}

  fun dest_typecheck_state cmd (SOME (x as {logic, ...})) =
        if is_reset_logic logic then
          raise ERR "typecheck_script"
            ("received " ^ cmd ^ " before set-logic")
        else x
    | dest_typecheck_state cmd NONE =
        raise ERR "typecheck_script" ("received " ^ cmd ^ " before set-logic")

  fun finalize_typecheck_state cmd state : command_state_snapshot =
  let
    val command_state as {logic, queries, surface_flags, ...} =
      (case state of
         SOME x => x
       | NONE =>
           raise ERR "typecheck_script"
             ("received " ^ cmd ^ " before set-logic"))
    val (tydict, tmdict, _) = current_typecheck_dicts command_state
  in
    {logic = visible_logic logic,
     tydict = tydict,
     tmdict = tmdict,
     assertions = active_typechecked_assertions command_state,
     named_assertions = active_typechecked_named_assertions command_state,
     local_definitions = active_typechecked_local_definitions command_state,
     queries = List.rev queries,
     surface_flags = !surface_flags}
  end

  fun push_typecheck_frames 0 state = state
    | push_typecheck_frames n
        ({logic, frames, queries, surface_flags}: typecheck_state) =
        let
          val top = current_typecheck_frame
            {logic = logic, frames = frames, queries = queries,
             surface_flags = surface_flags}
          val frame = mk_typecheck_frame
            (typecheck_frame_tydict top)
            (typecheck_frame_tmdict top)
            (typecheck_frame_sigdict top)
        in
          push_typecheck_frames (n - 1)
            {logic = logic, frames = frame :: frames, queries = queries,
             surface_flags = surface_flags}
        end

  fun pop_typecheck_frames 0 state = state
    | pop_typecheck_frames n
        ({logic, frames, queries, surface_flags}: typecheck_state) =
        (case frames of
           _ :: rest =>
             if List.null rest then
               raise ERR "pop" "pop scope underflow: cannot pop the base assertion scope"
             else
               pop_typecheck_frames (n - 1)
                 {logic = logic, frames = rest, queries = queries,
                  surface_flags = surface_flags}
         | [] => raise ERR "pop" "empty assertion stack")

  fun reset_typecheck_assertions
      (state as
        {logic, frames, queries, surface_flags}: typecheck_state) =
    let
      val frame = current_typecheck_frame
        {logic = logic, frames = frames, queries = queries,
         surface_flags = surface_flags}
      val reset_frame = {
        tydict = typecheck_frame_tydict frame,
        tmdict = typecheck_frame_tmdict frame,
        sigdict = typecheck_frame_sigdict frame,
        finite_sets = typecheck_frame_finite_sets frame,
        assertions = [],
        named_assertions = [],
        local_definitions = []
      }
    in
      {logic = logic,
       frames = [reset_frame],
       queries = queries,
       surface_flags = surface_flags}
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

  fun reject_duplicate_definition context loc name sigdict =
    case peek_signatures (sigdict, name) of
      NONE => ()
    | SOME _ =>
        type_error "reject_duplicate_definition" context loc NONE NONE
          ("duplicate define-const/define-fun declaration for symbol '" ^
           name ^ "'")

  fun make_decl_parsefn name tm args_count token indices args =
    if List.null indices andalso List.length args = args_count then
      Term.list_mk_comb (tm, args)
    else
      raise ERR ("<" ^ name ^ ">") "wrong number of arguments"

  fun add_value_signature_with_surface name domain domain_surface range
      range_surface (tmdict, sigdict) =
    let
      val tm = Term.mk_var (name, boolSyntax.list_mk_fun (domain, range))
      val parsefn = make_decl_parsefn name tm (List.length domain)
      val tmdict = Library.extend_dict ((name, parsefn), tmdict)
      val sigdict = add_signature name
        {tm = tm, domain = domain, domain_surface = domain_surface,
         range = range, range_surface = range_surface} sigdict
    in
      (tm, tmdict, sigdict)
    end

  fun add_value_signature name domain range env =
    add_value_signature_with_surface name domain (List.map RigidSort domain)
      range (RigidSort range) env

  fun add_value_term_signature_with_surface name tm domain domain_surface range
      range_surface (tmdict, sigdict) =
    let
      val parsefn = make_decl_parsefn name tm (List.length domain)
      val tmdict = Library.extend_dict ((name, parsefn), tmdict)
      val sigdict = add_signature name
        {tm = tm, domain = domain, domain_surface = domain_surface,
         range = range, range_surface = range_surface} sigdict
    in
      (tmdict, sigdict)
    end

  fun index_term_from_ast_with_options elaborate_datatypes context
      (tydict, tmdict, sigdict) term_ast =
    case node_of term_ast of
      TermIdentifier token =>
        (index_numeral_term token
         handle Feedback.HOL_ERR _ =>
           ((checked_term o
               typecheck_term_with_options elaborate_datatypes context
                 (tydict, tmdict, sigdict)) term_ast
            handle Feedback.HOL_ERR _ =>
              Term.mk_var (token, Type.mk_vartype "'smtlib_index")))
    | _ =>
        checked_term
          (typecheck_term_with_options elaborate_datatypes context
            (tydict, tmdict, sigdict) term_ast)

  and index_term_from_ast context env term_ast =
    index_term_from_ast_with_options false context env term_ast

  and typecheck_sort context tydict sort_ast =
    let
      fun arg_sorts args = List.map (typecheck_sort context tydict) args
      fun array_sort_arity loc actual =
        type_error "typecheck_sort" context loc NONE NONE
          ("ArraysEx Array sort arity mismatch: expected exactly two " ^
           "sort arguments (Index and Element), actual sort argument " ^
           "count " ^ Int.toString actual)
      fun function_sort loc args =
        let
          val sorts = arg_sorts args
          val function_ty =
            SmtLib_Theories.function_ty sorts
            handle Feedback.HOL_ERR holerr =>
              type_error "typecheck_sort" context loc NONE NONE
                (Feedback.message_of holerr)
          val _ = note_arrow_sort_used context
        in
          function_ty
        end
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
          if name = "Array" then
            array_sort_arity (loc_of sort_ast) 0
          else
            (t_with_args tydict name [] []
             handle Feedback.HOL_ERR holerr =>
               type_error "typecheck_sort" context (loc_of sort_ast) NONE NONE
                 (Feedback.message_of holerr))
      | SortIndexed (name, indices) =>
          parse_index name indices []
      | SortApply (head, args) =>
          if located_string_node head = "->" then
            function_sort (loc_of sort_ast) args
          else if located_string_node head = "Array" andalso
                  List.length args <> 2 then
            array_sort_arity (loc_of sort_ast) (List.length args)
          else
            (t_with_args tydict (located_string_node head) []
               (arg_sorts args)
             handle Feedback.HOL_ERR holerr =>
               type_error "typecheck_sort" context (loc_of sort_ast) NONE NONE
                 (Feedback.message_of holerr))
    end

  and surface_sort_of_ast context tydict sort_ast =
    case node_of sort_ast of
      SortApply (head, args) =>
        if located_string_node head = "->" andalso List.length args >= 2 then
          let
            val (domains, range) =
              Lib.front_last
                (List.map (surface_sort_of_ast context tydict) args)
          in
            List.foldr MapSort range domains
          end
        else if located_string_node head = "Array" andalso
                List.length args = 2 then
          case List.map (surface_sort_of_ast context tydict) args of
            [index, element] => ArraySort (index, element)
          | _ => raise ERR "surface_sort_of_ast" "impossible Array arity"
        else
          ConstructorSort (typecheck_sort context tydict sort_ast,
            List.map (surface_sort_of_ast context tydict) args)
    | _ => RigidSort (typecheck_sort context tydict sort_ast)

  and typecheck_sorted_var context tydict sorted_var =
    case node_of sorted_var of
      SortedVar (name, sort) =>
        (located_string_node name, typecheck_sort context tydict sort)

  (* Typecheck a `SortedVar` into its bound HOL variable together with the
     surface sort of its declared type; used by binders, lambdas, and the
     define-fun family. *)
  and checked_sorted_var context tydict sorted_var =
    let
      val (name, ty) = typecheck_sorted_var context tydict sorted_var
      val surface_sort =
        case node_of sorted_var of
          SortedVar (_, sort) => surface_sort_of_ast context tydict sort
    in
      (name, Term.mk_var (name, ty), surface_sort)
    end

  and instantiate_signature arg_sorts arg_surface
      ({tm, domain, domain_surface, range, range_surface}
         : function_signature) =
    let
      val _ = ListPair.allEq
        (fn (expected, actual) =>
          surface_sort_compatible expected actual)
        (domain_surface, arg_surface) orelse raise Match
      val surface_subst = List.concat
        (ListPair.map surface_bindings (domain_surface, arg_surface))
      fun match_one ((expected, actual), subst) =
        let
          val expected = Type.type_subst subst expected
          val actual =
            if int_to_real_expected expected actual then realSyntax.real_ty
            else actual
          val more = Type.match_type expected actual
        in
          more @ subst
        end
      val subst = List.foldl match_one [] (ListPair.zip (domain, arg_sorts))
    in
      SOME {tm = Term.inst subst tm,
        domain = List.map (Type.type_subst subst) domain,
        domain_surface = List.map
          (instantiate_surface_sort_with surface_subst subst) domain_surface,
        range = Type.type_subst subst range,
        range_surface =
          instantiate_surface_sort_with surface_subst subst range_surface}
    end
    handle Feedback.HOL_ERR _ => NONE
         | Match => NONE

  and apply_checked_args fn_name context loc detail head args =
    let
      fun apply_one position rator arg =
        let
          val rator_sort = checked_sort rator
          val (domain_surface, range_surface) =
            case checked_surface_sort rator of
              MapSort pair => pair
            | _ =>
                type_error fn_name context loc NONE (SOME rator_sort)
                  (detail ^ " expected a map-sorted term before argument " ^
                   Int.toString position)
          val (domain, _) = Type.dom_rng rator_sort
          val arg_sort = checked_sort arg
          val match_sort =
            if int_to_real_expected domain arg_sort then domain else arg_sort
          val subst =
            Type.match_type domain match_sort
            handle Feedback.HOL_ERR _ =>
              type_error fn_name context loc (SOME domain) (SOME arg_sort)
                (detail ^ " argument " ^ Int.toString position ^
                 " sort mismatch")
          val _ =
            if surface_sort_compatible domain_surface
                (checked_surface_sort arg) then ()
            else
              type_error fn_name context loc (SOME domain) (SOME arg_sort)
                (detail ^ " argument " ^ Int.toString position ^
                 " sort mismatch")
          val rator_term = Term.inst subst (checked_term rator)
          val (inst_domain, _) = Type.dom_rng (Term.type_of rator_term)
          val arg_term = coerce_arg_to_expected inst_domain (checked_term arg)
        in
          checked_term_with_surface_sort
            (instantiate_surface_sort subst range_surface)
            (Term.mk_comb (rator_term, arg_term))
        end
      fun loop _ rator [] = rator
        | loop position rator (arg :: rest) =
            loop (position + 1) (apply_one position rator arg) rest
      val result = loop 1 head args
      val _ =
        if not (List.null args) andalso
           (case checked_surface_sort result of MapSort _ => true | _ => false)
        then note_surface_event context PartialApplicationUsed
        else ()
    in
      result
    end

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

  and apply_user_signature fn_name context loc name args signatures =
    let
      val arg_terms = List.map checked_term args
      val arg_sorts = List.map checked_sort args
      val arg_surface = List.map checked_surface_sort args
      val arity_matches =
        List.filter
          (fn {domain, ...}: function_signature =>
            List.length domain = List.length arg_sorts)
          signatures
      val exact = Lib.get_first
        (instantiate_signature arg_sorts arg_surface) arity_matches
      fun map_signature ({domain, range_surface, ...}: function_signature) =
        List.null domain andalso
        (case range_surface of MapSort _ => true | _ => false)
      fun ranked_underapplication ({domain, ...}: function_signature) =
        List.length arg_sorts < List.length domain
      fun mismatch () =
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
    in
      case exact of
        SOME {tm, domain, range, range_surface, ...} =>
          CheckedTerm {
            term = list_mk_comb_coerce_int_to_real tm domain arg_terms,
            sort = range,
            surface_sort = range_surface
          }
      | NONE =>
          if not (List.null arity_matches) then mismatch ()
          else
            (case List.find map_signature signatures of
               SOME {tm, range, range_surface, ...} =>
                 apply_checked_args fn_name context loc
                   ("map-sorted symbol '" ^ name ^ "'")
                   (CheckedTerm {
                     term = tm,
                     sort = range,
                     surface_sort = range_surface
                   }) args
             | NONE =>
                 (case List.find ranked_underapplication signatures of
                    SOME {domain, ...} =>
                      type_error fn_name context loc NONE NONE
                        ("function symbol '" ^ name ^ "' of rank " ^
                         Int.toString (List.length domain) ^
                         " cannot be partially applied; wrap it in a " ^
                         "lambda (SMT-LIB 2.7 §3.9)")
                  | NONE => mismatch ()))
    end

  and apply_symbol fn_name context loc (tydict, tmdict, sigdict)
      name indices args =
    let
      fun arity_mismatch symbol expected actual =
        type_error fn_name context loc NONE NONE
          ("ArraysEx " ^ symbol ^ " arity mismatch: expected " ^
           Int.toString expected ^ " arguments, actual argument count " ^
           Int.toString actual)
      fun array_dom_rng symbol array_sort =
        SOME (Type.dom_rng array_sort)
        handle Feedback.HOL_ERR _ =>
          type_error fn_name context loc NONE (SOME array_sort)
            ("ArraysEx " ^ symbol ^ " array sort mismatch: expected " ^
             "Array Index Element")
      fun check_array_builtin arg_sorts =
        if not (List.null indices) then ()
        else
          case (name, arg_sorts) of
            ("select", [array_sort, index_sort]) =>
              let val (expected_index, _) =
                    valOf (array_dom_rng "select" array_sort)
              in
                if index_sort = expected_index orelse
                   int_to_real_expected expected_index index_sort then ()
                else
                  type_error fn_name context loc (SOME expected_index)
                    (SOME index_sort)
                    "ArraysEx select index sort mismatch"
              end
          | ("select", _) =>
              arity_mismatch "select" 2 (List.length arg_sorts)
          | ("store", [array_sort, index_sort, value_sort]) =>
              let val (expected_index, expected_value) =
                    valOf (array_dom_rng "store" array_sort)
              in
                if index_sort <> expected_index andalso
                   not (int_to_real_expected expected_index index_sort) then
                  type_error fn_name context loc (SOME expected_index)
                    (SOME index_sort)
                    "ArraysEx store index sort mismatch"
                else if value_sort <> expected_value andalso
                        not (int_to_real_expected expected_value value_sort) then
                  type_error fn_name context loc (SOME expected_value)
                    (SOME value_sort)
                    "ArraysEx store value sort mismatch"
                else ()
              end
          | ("store", _) =>
              arity_mismatch "store" 3 (List.length arg_sorts)
          | _ => ()
      fun check_surface_builtin () =
        if not (List.null indices) then ()
        else
          case (name, List.map checked_surface_sort args) of
            ("select", [set_surface, actual_index]) =>
              if is_set_surface set_surface then
                if #solver context = SOME "cvc5" then
                  type_error fn_name context loc NONE NONE
                    "Z3 Set select is unavailable in the cvc5 dialect"
                else ()
              else
                (case set_surface of
                   ArraySort (index, _) =>
                     if surface_sort_compatible index actual_index then ()
                     else type_error fn_name context loc NONE NONE
                       "ArraysEx select surface sort mismatch"
                 | _ => ())
          | ("store", [ArraySort (index, element), actual_index,
                        actual_element]) =>
              if surface_sort_compatible index actual_index andalso
                 surface_sort_compatible element actual_element then ()
              else type_error fn_name context loc NONE NONE
                "ArraysEx store surface sort mismatch"
          | ("ite", _ :: then_sort :: else_sort :: _) =>
              if surface_sorts_equivalent then_sort else_sort then ()
              else type_error fn_name context loc NONE NONE
                "ite branch surface sort mismatch"
          | _ => ()
      fun result_surface_sort t =
        case (name, args) of
          ("select", array :: _) =>
            (case checked_surface_sort array of
               ArraySort (_, element) => element
             | _ => RigidSort (Term.type_of t))
        | ("store", array :: _) => checked_surface_sort array
        | ("ite", _ :: then_term :: else_term :: _) =>
            let
              val then_surface = checked_surface_sort then_term
              val else_surface = checked_surface_sort else_term
            in
              if surface_sort_compatible then_surface else_surface then
                else_surface
              else then_surface
            end
        | (_, [arg]) =>
            (case surface_component_of_type (Term.type_of t)
                (checked_surface_sort arg) of
               SOME surface_sort => surface_sort
             | NONE => RigidSort (Term.type_of t))
        | _ => RigidSort (Term.type_of t)
    in
      if List.null indices andalso name = "@bbterm" then
        let
          val arg_terms = List.map checked_term args
          val arg_sorts = List.map checked_sort args
          val t =
            t_with_term_args tmdict name [] arg_terms
            handle Feedback.HOL_ERR holerr =>
              type_error fn_name context loc NONE NONE
                ("could not resolve symbol '" ^ name ^ "' for actual sorts " ^
                 sort_list_to_string arg_sorts ^ ": " ^
                 Feedback.message_of holerr)
        in
          checked_term_of t
        end
      else if List.null indices then
        (case peek_signatures (sigdict, name) of
           SOME signatures =>
             apply_user_signature fn_name context loc name args signatures
         | NONE =>
             let
               val arg_terms = List.map checked_term args
               val arg_sorts = List.map checked_sort args
               val _ = check_array_builtin arg_sorts
               val _ = check_surface_builtin ()
               val t =
                 (case (name, args) of
                    ("select", [set_tm, element]) =>
                      if is_set_surface (checked_surface_sort set_tm) andalso
                         #solver context <> SOME "cvc5" then
                        pred_setSyntax.mk_in
                          (checked_term element, checked_term set_tm)
                      else
                        t_with_term_args tmdict name [] arg_terms
                  | ("store", [set_tm, element, value]) =>
                      if is_set_surface (checked_surface_sort set_tm) andalso
                         #solver context <> SOME "cvc5" andalso
                         Term.aconv (checked_term value) boolSyntax.T then
                        pred_setSyntax.mk_insert
                          (checked_term element, checked_term set_tm)
                      else if is_set_surface (checked_surface_sort set_tm) andalso
                              #solver context <> SOME "cvc5" andalso
                              Term.aconv (checked_term value) boolSyntax.F then
                        pred_setSyntax.mk_delete
                          (checked_term set_tm, checked_term element)
                      else
                        t_with_term_args tmdict name [] arg_terms
                  | _ => t_with_term_args tmdict name [] arg_terms)
                 handle Feedback.HOL_ERR holerr =>
                   type_error fn_name context loc NONE NONE
                     ("could not resolve symbol '" ^ name ^
                      "' for actual sorts " ^ sort_list_to_string arg_sorts ^
                      ": " ^ Feedback.message_of holerr)
             in
               checked_term_with_surface_sort (result_surface_sort t) t
             end)
      else
        let
          val arg_terms = List.map checked_term args
          val arg_sorts = List.map checked_sort args
          val t =
            t_with_term_args tmdict name indices arg_terms
            handle Feedback.HOL_ERR holerr =>
              type_error fn_name context loc NONE NONE
                ("could not resolve indexed symbol '" ^ name ^
                 "' for actual sorts " ^ sort_list_to_string arg_sorts ^
                 ": " ^ Feedback.message_of holerr)
        in
          checked_term_of t
        end
    end

  and constructor_arg_types ty =
    case Lib.total Type.dom_rng ty of
      NONE => []
    | SOME (domain, range) => domain :: constructor_arg_types range

  and const_name tm =
    #Name (Term.dest_thy_const tm)
    handle Feedback.HOL_ERR _ => Lib.fst (Term.dest_const tm)

  and constructors_for_match context loc scrutinee_sort =
    let
      val constructors =
        List.map (TypeBasePure.cinst scrutinee_sort)
          (TypeBase.constructors_of scrutinee_sort)
        handle Feedback.HOL_ERR _ =>
          type_error "typecheck_match" context loc NONE
            (SOME scrutinee_sort)
            "match scrutinee sort is not an elaborated datatype"
    in
      if List.null constructors then
        type_error "typecheck_match" context loc NONE (SOME scrutinee_sort)
          "match scrutinee sort has no datatype constructors"
      else constructors
    end

  and constructor_pattern_with_names ctor names =
    let
      val arg_tys = constructor_arg_types (Term.type_of ctor)
      val _ =
        if List.length names = List.length arg_tys then ()
        else raise ERR "constructor_pattern_with_names"
          "binder count does not match constructor arity"
      val vars = ListPair.map Term.mk_var (names, arg_tys)
    in
      (Term.list_mk_comb (ctor, vars), vars)
    end

  and generated_constructor_pattern ctor =
    let
      val arg_tys = constructor_arg_types (Term.type_of ctor)
      val names = List.tabulate (List.length arg_tys,
        fn i => "match" ^ Int.toString i)
    in
      constructor_pattern_with_names ctor names
    end

  and constructor_for_pattern context loc sigdict scrutinee_sort constructors
      smt_name =
    let
      fun same_constructor tm ctor =
        const_name tm = const_name ctor
        handle Feedback.HOL_ERR _ => false

      fun instantiate
          ({tm, domain, domain_surface, range, ...}: function_signature) =
        let
          val subst = Type.match_type range scrutinee_sort
          val tm = Term.inst subst tm
          val domain = List.map (Type.type_subst subst) domain
          val domain_surface =
            List.map (instantiate_surface_sort subst) domain_surface
        in
          case List.find (same_constructor tm) constructors of
            SOME ctor =>
              SOME {smt_name = smt_name, hol_name = const_name ctor,
                constructor = ctor, domain = domain,
                domain_surface = domain_surface}
          | NONE => NONE
        end
        handle Feedback.HOL_ERR _ => NONE
    in
      case peek_signatures (sigdict, smt_name) of
        SOME signatures =>
          (case Lib.get_first instantiate signatures of
             SOME result => result
           | NONE =>
               type_error "typecheck_match" context loc NONE
                 (SOME scrutinee_sort)
                 ("unknown match constructor '" ^ smt_name ^
                  "' for scrutinee sort " ^ type_to_string scrutinee_sort))
      | NONE =>
          type_error "typecheck_match" context loc NONE (SOME scrutinee_sort)
            ("unknown match constructor '" ^ smt_name ^
             "' for scrutinee sort " ^ type_to_string scrutinee_sort)
    end

  (* Pattern binders keep the surface sort the pattern gives them: a binder
     for a '(Pair Int)' field must be usable wherever a '(Pair Int)' term is,
     which a plain rigid sort would not be. *)
  and add_pattern_bindings bindings (tmdict, sigdict) =
    List.foldl
      (fn ((var, surface_sort), (tmdict, sigdict)) =>
        let val name = Lib.fst (Term.dest_var var)
        in
          add_value_term_signature_with_surface name var [] []
            (Term.type_of var) surface_sort (tmdict, sigdict)
        end)
      (tmdict, sigdict) bindings

  and reject_duplicate_pattern_binders context loc names =
    let
      fun seen _ [] = false
        | seen name (x :: xs) = name = x orelse seen name xs
      fun loop [] = ()
        | loop (name :: rest) =
            if seen name rest then
              type_error "typecheck_match" context loc NONE NONE
                ("duplicate match pattern binder '" ^ name ^ "'")
            else loop rest
    in
      loop names
    end

  and typecheck_match elaborate_datatypes context
      (env as (tydict, tmdict, sigdict)) loc scrutinee branches =
    let
      val _ =
        if elaborate_datatypes then ()
        else
          type_error "typecheck_match" context loc NONE NONE
            ("SMT-LIB match requires datatype elaboration; placeholder " ^
             "datatype mode cannot support binding patterns soundly")
      val _ =
        if List.null branches then
          type_error "typecheck_match" context loc NONE NONE
            "match expression must have at least one branch"
        else ()
      val scrutinee_checked =
        typecheck_term_with_options elaborate_datatypes context env scrutinee
      val scrutinee_term = checked_term scrutinee_checked
      val scrutinee_sort = checked_sort scrutinee_checked
      val constructors =
        constructors_for_match context (loc_of scrutinee) scrutinee_sort

      fun check_body local_tmdict local_sigdict body =
        typecheck_term_with_options elaborate_datatypes context
          (tydict, local_tmdict, local_sigdict) body

      fun check_constructor_branch branch_loc pattern_loc ctor_name binder_names
          body =
        let
          val ctor_s = located_string_node ctor_name
          val binders = List.map located_string_node binder_names
          val _ = reject_duplicate_pattern_binders context pattern_loc binders
          val {hol_name, constructor, domain, domain_surface, ...} =
            constructor_for_pattern context (loc_of ctor_name) sigdict
              scrutinee_sort constructors ctor_s
          val _ =
            if List.length binders = List.length domain then ()
            else
              type_error "typecheck_match" context pattern_loc NONE NONE
                ("constructor pattern '" ^ ctor_s ^ "' arity mismatch: " ^
                 "expected " ^ Int.toString (List.length domain) ^
                 " binders, actual " ^ Int.toString (List.length binders))
          val vars = ListPair.map Term.mk_var (binders, domain)
          val (local_tmdict, local_sigdict) =
            add_pattern_bindings (ListPair.zip (vars, domain_surface))
              (tmdict, sigdict)
          val body_checked = check_body local_tmdict local_sigdict body
          val pattern = Term.list_mk_comb (constructor, vars)
        in
          CheckedMatchConstructor {
            smt_name = ctor_s,
            hol_name = hol_name,
            constructor = constructor,
            pattern = pattern,
            body = body_checked,
            loc = branch_loc
          }
        end

      fun check_default_branch branch_loc name body =
        let
          val var = Term.mk_var (located_string_node name, scrutinee_sort)
          val (local_tmdict, local_sigdict) =
            add_pattern_bindings
              [(var, checked_surface_sort scrutinee_checked)]
              (tmdict, sigdict)
          val body_checked = check_body local_tmdict local_sigdict body
        in
          CheckedMatchDefault {var = var, body = body_checked, loc = branch_loc}
        end

      fun check_branch branch =
        case node_of branch of
          MatchCase (pattern, body) =>
            (case node_of pattern of
               MatchPatternConstructor (ctor_name, binders) =>
                 check_constructor_branch (loc_of branch) (loc_of pattern)
                   ctor_name binders body
             | MatchPatternAtom name =>
                 (case Lib.total
                    (constructor_for_pattern context (loc_of name) sigdict
                      scrutinee_sort constructors) (located_string_node name) of
                    SOME {constructor, domain = [], hol_name, ...} =>
                      let
                        val body_checked = check_body tmdict sigdict body
                      in
                        CheckedMatchConstructor {
                          smt_name = located_string_node name,
                          hol_name = hol_name,
                          constructor = constructor,
                          pattern = constructor,
                          body = body_checked,
                          loc = loc_of branch
                        }
                      end
                  | SOME {domain, ...} =>
                      type_error "typecheck_match" context (loc_of pattern)
                        NONE NONE
                        ("constructor pattern '" ^ located_string_node name ^
                         "' arity mismatch: expected " ^
                         Int.toString (List.length domain) ^
                         " binders, actual 0")
                  | NONE => check_default_branch (loc_of branch) name body))

      val checked_branches = List.map check_branch branches

      fun body_sort branch =
        case branch of
          CheckedMatchConstructor {body, ...} => checked_sort body
        | CheckedMatchDefault {body, ...} => checked_sort body
      fun body_loc branch =
        case branch of
          CheckedMatchConstructor {loc, ...} => loc
        | CheckedMatchDefault {loc, ...} => loc
      val result_sort = body_sort (hd checked_branches)
      val result_surface_sort =
        (case hd checked_branches of
           CheckedMatchConstructor {body, ...} => checked_surface_sort body
         | CheckedMatchDefault {body, ...} => checked_surface_sort body)
      fun branch_surface_sort branch =
        case branch of
          CheckedMatchConstructor {body, ...} => checked_surface_sort body
        | CheckedMatchDefault {body, ...} => checked_surface_sort body
      val _ =
        List.app
          (fn branch =>
            if body_sort branch = result_sort andalso
               surface_sorts_equivalent (branch_surface_sort branch)
                 result_surface_sort then ()
            else type_error "typecheck_match" context (body_loc branch)
              (SOME result_sort) (SOME (body_sort branch))
              "match branch result sort mismatch")
          checked_branches

      fun duplicate name [] = false
        | duplicate name (x :: xs) = name = x orelse duplicate name xs
      fun scan [] seen default = (List.rev seen, default)
        | scan (branch :: rest) seen default =
            (case branch of
               CheckedMatchConstructor {smt_name, hol_name, loc, ...} =>
                 if duplicate hol_name seen then
                   type_error "typecheck_match" context loc NONE NONE
                     ("duplicate match constructor pattern '" ^ smt_name ^ "'")
                 else scan rest (hol_name :: seen) default
             | CheckedMatchDefault {loc, ...} =>
                 (case default of
                    NONE => scan rest seen (SOME branch)
                  | SOME _ =>
                      type_error "typecheck_match" context loc NONE NONE
                        "duplicate match default pattern"))
      val (covered, default) = scan checked_branches [] NONE
      val missing =
        List.filter (fn ctor => not (duplicate (const_name ctor) covered))
          constructors
      val _ =
        if List.null missing orelse Option.isSome default then ()
        else
          type_error "typecheck_match" context loc NONE NONE
            ("non-exhaustive match: missing constructor pattern '" ^
             const_name (hd missing) ^ "'")

      fun branch_for_constructor ctor =
        let val cname = const_name ctor
        in
          case List.find
              (fn branch =>
                case branch of
                  CheckedMatchConstructor {hol_name, ...} => hol_name = cname
                | CheckedMatchDefault _ => true)
              checked_branches of
            SOME (CheckedMatchConstructor {pattern, body, ...}) =>
              (pattern, checked_term body)
          | SOME (CheckedMatchDefault {var, body, ...}) =>
              let
                val (pattern, _) = generated_constructor_pattern ctor
                val rhs = Term.subst
                  [{redex = var, residue = pattern}]
                  (checked_term body)
              in
                (pattern, rhs)
              end
          | NONE =>
              raise ERR "typecheck_match"
                "missing constructor without a matching branch"
        end
      val case_term =
        TypeBase.mk_case (scrutinee_term,
          List.map branch_for_constructor constructors)
        handle Feedback.HOL_ERR holerr =>
          type_error "typecheck_match" context loc NONE NONE
            ("could not construct datatype match case: " ^
             Feedback.message_of holerr)
    in
      CheckedTerm {
        term = case_term,
        sort = result_sort,
        surface_sort = result_surface_sort
      }
    end

  and typecheck_term context env term_ast =
    typecheck_term_with_options false context env term_ast

  and typecheck_term_with_options elaborate_datatypes context env term_ast =
    let
      val (tydict, tmdict, sigdict) = env
      fun check t = typecheck_term_with_options elaborate_datatypes context env t
      fun check_index t =
        index_term_from_ast_with_options elaborate_datatypes context env t
      fun apply_operator loc operator head args =
        if not (apply_operator_available context operator) then
          type_error "typecheck_term" context loc NONE NONE
            ("apply operator '" ^ operator ^
             "' is unavailable in the selected theory")
        else if List.null args then
          type_error "typecheck_term" context loc NONE
            (SOME (checked_sort head))
            ("apply operator '" ^ operator ^
             "' expects a map term and at least one argument")
        else
          let
            val detail = "apply operator '" ^ operator ^ "'"
            val checked = apply_checked_args "typecheck_term" context loc
              detail head args
            val dictionary_term = t_with_term_args tmdict operator []
              (checked_term head :: List.map checked_term args)
              handle Feedback.HOL_ERR holerr =>
                type_error "typecheck_term" context loc NONE NONE
                  (detail ^ " dictionary resolution failed: " ^
                   Feedback.message_of holerr)
            val _ =
              if Term.aconv dictionary_term (checked_term checked) then ()
              else
                type_error "typecheck_term" context loc NONE NONE
                  (detail ^ " dictionary resolution disagreed with " ^
                   "curried application")
            val _ = note_surface_event context ApplyOperatorUsed
          in
            checked_term_with_surface_sort
              (checked_surface_sort checked) dictionary_term
          end

      fun indexed_or_apply loc name indices outer_args =
        let
          val indexed_result =
            if List.null indices then
              raise ERR "typecheck_term"
                "indexed identifier requires at least one index"
            else
              apply_symbol "typecheck_term" context loc env
                (located_string_node name) (List.map check_index indices)
                (List.map check outer_args)
        in
          indexed_result
        end
        handle original as Feedback.HOL_ERR _ =>
          if indexed_term_family context (located_string_node name) orelse
             located_string_node name = "is" then
            raise original
          else
            (case Lib.total
                (fn () =>
                  apply_symbol "typecheck_term" context (loc_of name) env
                    (located_string_node name) [] []) () of
             SOME head =>
               if (case checked_surface_sort head of MapSort _ => true
                   | _ => false) then
                 let
                   val explicit = apply_operator loc "_" head
                     (List.map check indices)
                 in
                   apply_checked_args "typecheck_term" context loc
                     "higher-order application" explicit
                     (List.map check outer_args)
                 end
               else raise original
           | NONE => raise original)

      fun z3_or_neutral () =
        case #solver context of SOME "cvc5" => false | _ => true
      fun cvc5_or_neutral () =
        case #solver context of SOME "Z3" => false | _ => true
      fun as_const_array_or_set sort payload =
        let
          val expected = typecheck_sort context tydict sort
          val expected_surface = surface_sort_of_ast context tydict sort
          val payload = check payload
          val (domain, range) = Type.dom_rng expected
            handle Feedback.HOL_ERR _ =>
              type_error "typecheck_term" context (loc_of term_ast)
                NONE (SOME expected) "Z3 const result must have Array or Set sort"
          val _ =
            if range = Type.bool then ()
            else type_error "typecheck_term" context (loc_of term_ast)
              (SOME Type.bool) (SOME range)
              "Z3 Bool-array const payload must have Bool range"
          val _ =
            if checked_sort payload = Type.bool then ()
            else type_error "typecheck_term" context (loc_of term_ast)
              (SOME Type.bool) (SOME (checked_sort payload))
              "Z3 Array/Set const payload must be Boolean"
          val result =
            if is_set_surface expected_surface then
              if Term.aconv (checked_term payload) boolSyntax.F then
                pred_setSyntax.mk_empty domain
              else if Term.aconv (checked_term payload) boolSyntax.T then
                pred_setSyntax.mk_univ domain
              else type_error "typecheck_term" context (loc_of term_ast)
                (SOME Type.bool) (SOME (checked_sort payload))
                "Z3 Set const payload must be true or false"
            else
              Term.mk_abs (Term.mk_var ("array_const_x", domain),
                checked_term payload)
        in
          checked_term_with_surface_sort expected_surface result
        end
      fun as_cvc5_set_constant name sort =
        let
          val expected = typecheck_sort context tydict sort
          val expected_surface = surface_sort_of_ast context tydict sort
          val _ =
            if pred_setSyntax.is_set_type expected then ()
            else type_error "typecheck_term" context (loc_of term_ast)
              NONE (SOME expected)
              (name ^ " result must have Set sort")
          val element = pred_setSyntax.dest_set_type expected
          val set_tm =
            if name = "set.empty" then pred_setSyntax.mk_empty element
            else pred_setSyntax.mk_univ element
        in
          checked_term_with_surface_sort expected_surface set_tm
        end
      fun as_seq_empty sort =
        let
          val expected = typecheck_sort context tydict sort
          val expected_surface = surface_sort_of_ast context tydict sort
          val smtstr_ty =
            Type.mk_thy_type {Thy = "smtstring", Tyop = "smtstr", Args = []}
          val empty =
            if listSyntax.is_list_type expected then
              listSyntax.mk_nil (listSyntax.dest_list_type expected)
            else if Type.compare (expected, smtstr_ty) = EQUAL then
              SmtLib_String_Literal.mk_string_term ""
            else
              type_error "typecheck_term" context (loc_of term_ast)
                NONE (SOME expected) "seq.empty result must have Seq sort"
        in
          checked_term_with_surface_sort expected_surface empty
        end
      fun as_cvc5_bag_empty sort =
        let
          val expected = typecheck_sort context tydict sort
          val expected_surface = surface_sort_of_ast context tydict sort
          val _ =
            if bagSyntax.is_bag_ty expected then ()
            else type_error "typecheck_term" context (loc_of term_ast)
              NONE (SOME expected) "bag.empty result must have Bag sort"
          val (element, _) = Type.dom_rng expected
          val bag_tm = Term.inst [{redex = Type.alpha, residue = element}]
            bagSyntax.EMPTY_BAG_tm
        in
          checked_term_with_surface_sort expected_surface bag_tm
        end
      fun apply_head loc head args =
        case node_of head of
          TermIdentifier name =>
            apply_symbol "typecheck_term" context loc env name []
              (List.map check args)
        | TermIndexed (name, indices) =>
            indexed_or_apply loc name indices args
        | _ =>
            let
              val head_checked = check head
              val checked_args = List.map check args
              val result =
                case checked_surface_sort head_checked of
                  MapSort _ =>
                    apply_checked_args "typecheck_term" context loc
                      "higher-order application" head_checked checked_args
                | _ =>
                    let
                      val arg_terms = List.map checked_term checked_args
                      val t =
                        Term.list_mk_comb
                          (checked_term head_checked, arg_terms)
                        handle Feedback.HOL_ERR holerr =>
                          type_error "typecheck_term" context loc NONE
                            (SOME (checked_sort head_checked))
                            ("invalid higher-order application: " ^
                             Feedback.message_of holerr)
                    in
                      checked_term_of t
                    end
              val _ = note_surface_event context PartialApplicationUsed
            in
              result
            end
    in
      case node_of term_ast of
        TermIdentifier name =>
          apply_symbol "typecheck_term" context (loc_of term_ast) env name [] []
      | TermString value =>
          (checked_term_of (SmtLib_String_Literal.mk_string_term value)
           handle SmtLib_String_Literal.InvalidStringLiteral detail =>
             type_error "typecheck_term" context (loc_of term_ast)
               NONE NONE detail)
      | TermIndexed (name, indices) =>
          indexed_or_apply (loc_of term_ast) name indices []
      | TermApply
          (Located {node = TermAscribed
             (Located {node = TermIdentifier "const", ...}, sort), ...}, [payload]) =>
          if z3_or_neutral () then
            as_const_array_or_set sort payload
          else type_error "typecheck_term" context (loc_of term_ast) NONE NONE
            "Z3 const Set syntax is unavailable in the cvc5 dialect"
      | TermApply (head, args) =>
          apply_head (loc_of term_ast) head args
      | TermApplyOperator (operator, head, args) =>
          apply_operator (loc_of term_ast) (located_string_node operator)
            (check head) (List.map check args)
      | TermAscribed
          (ascribed as Located {node = TermIdentifier name, ...}, sort) =>
          if (name = "set.empty" orelse name = "set.universe") andalso
             cvc5_or_neutral () then
            as_cvc5_set_constant name sort
          else if name = "seq.empty" then
            as_seq_empty sort
          else if name = "bag.empty" andalso cvc5_or_neutral () then
            as_cvc5_bag_empty sort
          else
          let
            val checked = check ascribed
            val expected = typecheck_sort context tydict sort
            val expected_surface = surface_sort_of_ast context tydict sort
            val _ =
              if checked_sort checked = expected then ()
              else
                type_error "typecheck_term" context (loc_of term_ast)
                  (SOME expected) (SOME (checked_sort checked))
                  "qualified identifier sort ascription mismatch"
          in
            checked_term_with_surface_sort expected_surface
              (checked_term checked)
          end
      | TermAscribed (term, sort) =>
          let
            val checked = check term
            val expected = typecheck_sort context tydict sort
            val expected_surface = surface_sort_of_ast context tydict sort
            val _ =
              if checked_sort checked = expected then ()
              else
                type_error "typecheck_term" context (loc_of term_ast)
                  (SOME expected) (SOME (checked_sort checked))
                  "qualified identifier sort ascription mismatch"
          in
            checked_term_with_surface_sort expected_surface
              (checked_term checked)
          end
      | TermLet (bindings, body) =>
          let
            val checked_bindings =
              List.map (fn (name, body) =>
                let val checked = check body
                in
                  (located_string_node name,
                   Term.mk_var (located_string_node name, checked_sort checked),
                   checked_term checked, checked_surface_sort checked)
                end) bindings
            val (tmdict, sigdict) =
              List.foldl
                (fn ((name, var, _, surface_sort), (tmdict, sigdict)) =>
                  add_value_term_signature_with_surface name var [] []
                    (Term.type_of var) surface_sort (tmdict, sigdict))
                (tmdict, sigdict) checked_bindings
            val body_checked =
              typecheck_term_with_options elaborate_datatypes context
                (tydict, tmdict, sigdict) body
            val term_bindings = List.map
              (fn (name, var, value, _) => (name, var, value))
              checked_bindings
            val t = (#mk_let smtlib_cfg) (term_bindings,
              checked_term body_checked)
          in
            checked_term_with_surface_sort
              (checked_surface_sort body_checked) t
          end
      | TermMatch (scrutinee, branches) =>
          typecheck_match elaborate_datatypes context env (loc_of term_ast)
            scrutinee branches
      | TermForall (vars, body) =>
          typecheck_binder_with_options elaborate_datatypes context env
            term_ast vars body boolSyntax.list_mk_forall
      | TermExists (vars, body) =>
          typecheck_binder_with_options elaborate_datatypes context env
            term_ast vars body boolSyntax.list_mk_exists
      | TermLambda (vars, body) =>
          let
            val _ = note_surface_event context LambdaUsed
          in
            typecheck_lambda_with_options elaborate_datatypes context env
              vars body
          end
      | TermAnnotated (term, _) =>
          check term
    end

  and typecheck_binder_with_options elaborate_datatypes context
      (tydict, tmdict, sigdict) term_ast vars body mk_binder =
    let
      val vars = List.map (checked_sorted_var context tydict) vars
      val (tmdict, sigdict) =
        List.foldl
          (fn ((name, var, surface_sort), (tmdict, sigdict)) =>
            add_value_term_signature_with_surface name var [] []
              (Term.type_of var) surface_sort (tmdict, sigdict))
          (tmdict, sigdict) vars
      val body_checked =
        typecheck_term_with_options elaborate_datatypes context
          (tydict, tmdict, sigdict) body
      val body = expect_checked_sort "typecheck_binder" context (loc_of body)
        Type.bool body_checked
    in
      checked_term_of
        (mk_binder (List.map (fn (_, var, _) => var) vars, body))
    end

  and typecheck_lambda_with_options elaborate_datatypes context
      (tydict, tmdict, sigdict) vars body =
    let
      fun reject_duplicates _ [] = ()
        | reject_duplicates seen (sorted_var :: rest) =
            (case node_of sorted_var of
               SortedVar (name, _) =>
                 let val name_text = located_string_node name
                 in
                   if List.exists (fn prior => prior = name_text) seen then
                     type_error "typecheck_lambda" context (loc_of name)
                       NONE NONE
                       ("duplicate lambda binder '" ^ name_text ^ "'")
                   else reject_duplicates (name_text :: seen) rest
                 end)
      val _ = reject_duplicates [] vars
      val vars = List.map (checked_sorted_var context tydict) vars
      val (tmdict, sigdict) =
        List.foldl
          (fn ((name, var, surface_sort), (tmdict, sigdict)) =>
            add_value_term_signature_with_surface name var [] []
              (Term.type_of var) surface_sort (tmdict, sigdict))
          (tmdict, sigdict) vars
      val body_checked =
        typecheck_term_with_options elaborate_datatypes context
          (tydict, tmdict, sigdict) body
    in
      checked_term_with_surface_sort
        (List.foldr
          (fn ((_, _, domain), range) => MapSort (domain, range))
          (checked_surface_sort body_checked) vars)
        (Term.list_mk_abs
          (List.map (fn (_, var, _) => var) vars,
           checked_term body_checked))
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
      val arity =
        case Int.fromString arity_text of
          SOME n =>
            if n < 0 then type_error "typecheck_declare_sort" context
              (loc_of arity) NONE NONE
              ("declare-sort arity for '" ^ sort_name ^ "' must be non-negative")
            else n
        | NONE => type_error "typecheck_declare_sort" context (loc_of arity)
            NONE NONE
            ("declare-sort arity for '" ^ sort_name ^
             "' must be a numeral, got '" ^ arity_text ^ "'")
      val parsefn = declared_sort_parsefn sort_name arity
    in
      Library.extend_dict ((sort_name, parsefn), tydict)
    end

  fun datatype_type datatype_name args =
    let
      val tag_ty = Type.mk_vartype ("'smtlib_dt_" ^ datatype_name)
    in
      case args of
        [] => tag_ty
      | _ => List.foldl
          (fn (arg, acc) => Type.mk_type ("prod", [acc, arg]))
          tag_ty args
    end

  fun datatype_arity context loc datatype_name arity_text =
    case Int.fromString arity_text of
      SOME n =>
        if n < 0 then
          type_error "typecheck_declare_datatype" context loc NONE NONE
            ("declare-datatypes arity for '" ^ datatype_name ^
             "' must be non-negative")
        else n
    | NONE =>
        type_error "typecheck_declare_datatype" context loc NONE NONE
          ("declare-datatypes arity for '" ^ datatype_name ^
           "' must be a numeral, got '" ^ arity_text ^ "'")

  fun extend_datatype_sort context name arity tydict =
    let
      val datatype_name = located_string_node name
      fun parse_ty token indices args =
        if List.null indices andalso List.length args = arity then
          datatype_type datatype_name args
        else raise ERR ("<" ^ datatype_name ^ ">") "wrong number of arguments"
    in
      Library.extend_dict ((datatype_name, parse_ty), tydict)
    end

  fun add_datatype_params params tydict =
    List.foldl
      (fn (param, tydict) =>
        let
          val pname = located_string_node param
          val ty = Type.mk_vartype ("'" ^ pname)
          fun parsefn token indices args =
            if List.null indices andalso List.null args then ty
            else raise ERR ("<" ^ pname ^ ">") "wrong number of arguments"
        in
          Library.extend_dict ((pname, parsefn), tydict)
        end)
      tydict params

  fun typecheck_datatype_body context datatype_name decl
      (tydict, tmdict, sigdict) =
    let
      val datatype_name_s = located_string_node datatype_name
      fun param_type param =
        Type.mk_vartype ("'" ^ located_string_node param)

      fun add_constructor tydict (ctor, (tmdict, sigdict)) =
        case node_of ctor of
          DatatypeConstructor (ctor_name, _, selectors) =>
            let
              val datatype_ty =
                case node_of decl of
                  DatatypeDecl (params, _) =>
                    datatype_type datatype_name_s (List.map param_type params)
              val ctor_name_s = located_string_node ctor_name
              val param_tys =
                case node_of decl of
                  DatatypeDecl (params, _) => List.map param_type params
              fun polymorphic_surface surface_sort =
                case surface_sort of
                  RigidSort ty =>
                    if List.exists (fn param => same_sort param ty) param_tys then
                      PolySort ty
                    else RigidSort ty
                | ConstructorSort (ty, args) =>
                    ConstructorSort (ty, List.map polymorphic_surface args)
                | MapSort (domain, range) =>
                    MapSort (polymorphic_surface domain,
                      polymorphic_surface range)
                | ArraySort (index, element) =>
                    ArraySort (polymorphic_surface index,
                      polymorphic_surface element)
                | PolySort ty => PolySort ty
              fun selector_info selector =
                case node_of selector of
                  DatatypeSelector (selector_name, selector_sort) =>
                    let
                      val selector_ty =
                        typecheck_sort context tydict selector_sort
                      val selector_surface = polymorphic_surface
                        (surface_sort_of_ast context tydict selector_sort)
                    in
                      (located_string_node selector_name, selector_ty,
                       selector_surface)
                    end
              val selectors = List.map selector_info selectors
              val arg_tys = List.map #2 selectors
              val arg_surface = List.map #3 selectors
              val datatype_surface =
                if List.null param_tys then RigidSort datatype_ty
                else ConstructorSort (datatype_ty, List.map PolySort param_tys)
              val ctor_tm = Term.mk_var (ctor_name_s,
                boolSyntax.list_mk_fun (arg_tys, datatype_ty))
              val (tmdict, sigdict) =
                add_value_term_signature_with_surface ctor_name_s ctor_tm
                  arg_tys arg_surface datatype_ty datatype_surface
                  (tmdict, sigdict)

              fun add_selector
                  ((selector_name, selector_ty, selector_surface),
                   (tmdict, sigdict)) =
                let
                  val selector_tm = Term.mk_var (selector_name,
                    Type.--> (datatype_ty, selector_ty))
                in
                  add_value_term_signature_with_surface selector_name
                    selector_tm [datatype_ty] [datatype_surface]
                    selector_ty selector_surface (tmdict, sigdict)
                end

              fun tester_parse token indices args =
                case (indices, args) of
                  ([index], [arg]) =>
                    let
                      val index_name = Lib.fst (Term.dest_var index)
                      val subst = Type.match_type datatype_ty (Term.type_of arg)
                    in
                      if index_name = ctor_name_s then
                        Term.list_mk_comb
                          (Term.mk_var ("is_" ^ ctor_name_s,
                             Type.--> (Type.type_subst subst datatype_ty,
                               Type.bool)),
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
        DatatypeDecl (params, constructors) =>
          let
            val constructor_tydict = add_datatype_params params tydict
            val (tmdict, sigdict) =
              List.foldl (add_constructor constructor_tydict)
                (tmdict, sigdict) constructors
          in
            (tydict, tmdict, sigdict)
          end
    end

  fun real_datatype_sort_parsefn smt_name base_ty token indices args =
    let
      val {Thy, Tyop, Args} = Type.dest_thy_type base_ty
      val arity = List.length Args
      fun arity_error actual =
        raise ERR ("<" ^ smt_name ^ ">")
          ("datatype arity mismatch for '" ^ smt_name ^ "': expected " ^
           Int.toString arity ^ ", actual " ^ Int.toString actual)
    in
      if not (List.null indices) then
        raise ERR ("<" ^ smt_name ^ ">")
          ("datatype sort '" ^ smt_name ^ "' does not take indices")
      else if List.length args = arity then
        if arity = 0 then base_ty
        else Type.mk_thy_type {Thy = Thy, Tyop = Tyop, Args = args}
      else
        arity_error (List.length args)
    end

  fun add_real_datatype_type ({smt_name, hol_type}: datatype_type_entry,
      tydict) =
    Library.extend_dict
      ((smt_name, real_datatype_sort_parsefn smt_name hol_type), tydict)

  fun add_real_datatype_constructor
      ({smt_name, term, ...}: datatype_constructor_entry,
       (tmdict, sigdict)) =
    let
      val (domain, range) = boolSyntax.strip_fun (Term.type_of term)
    in
      add_value_term_signature_with_surface smt_name term domain
        (List.map PolySort domain) range (PolySort range) (tmdict, sigdict)
    end

  fun add_real_datatype_selector mk_selector_case
      ({smt_name, constructor, domain, range}: datatype_selector_entry,
       tmdict) =
    let
      fun parsefn token indices args =
        case (indices, args) of
          ([], [arg]) =>
            let
              val _ = Type.match_type domain (Term.type_of arg)
            in
              mk_selector_case {
                selector = smt_name,
                constructor = constructor,
                scrutinee = arg
              }
            end
        | _ => raise ERR ("<" ^ smt_name ^ ">")
            "one datatype selector argument expected"
    in
      Library.extend_dict ((smt_name, parsefn), tmdict)
    end

  fun add_real_datatype_tester mk_tester_case tmdict =
    let
      fun constructor_index_name index =
        Lib.fst (Term.dest_var index)
        handle Feedback.HOL_ERR _ => Lib.fst (Term.dest_const index)
      fun parsefn token indices args =
        case (indices, args) of
          ([index], [arg]) =>
            mk_tester_case {
              constructor = constructor_index_name index,
              scrutinee = arg
            }
        | _ => raise ERR "<is>"
            "one constructor index and one datatype tester argument expected"
    in
      Library.extend_dict (("is", parsefn), tmdict)
    end

  fun install_real_datatype_elaboration
      ({types, constructors, selectors, mk_selector_case, mk_tester_case}:
         datatype_elaboration_result)
      (tydict, tmdict, sigdict) =
    let
      val tydict = List.foldl add_real_datatype_type tydict types
      val (tmdict, sigdict) =
        List.foldl add_real_datatype_constructor
          (tmdict, sigdict) constructors
      val tmdict =
        List.foldl (add_real_datatype_selector mk_selector_case)
          tmdict selectors
      val tmdict = add_real_datatype_tester mk_tester_case tmdict
    in
      (tydict, tmdict, sigdict)
    end

  fun require_datatype_elaborator context loc =
    case !datatype_elaborator of
      SOME hooks => hooks
    | NONE =>
        type_error "typecheck_declare_datatype" context loc NONE NONE
          "datatype elaboration requested before SmtLib_Datatypes was loaded"

  fun check_elaborated_datatype_surface context decl =
    let
      fun check_sort sort =
        case node_of sort of
          SortApply (head, args) =>
            let
              val _ =
                if located_string_node head <> "->" then ()
                else if List.length args >= 2 then
                  note_arrow_sort_used context
                else
                  type_error "typecheck_sort" context (loc_of sort) NONE NONE
                    ("function sort '->' expects at least one domain sort " ^
                     "and one range sort")
            in
              List.app check_sort args
            end
        | _ => ()
      fun check_selector selector =
        case node_of selector of DatatypeSelector (_, sort) => check_sort sort
      fun check_constructor constructor =
        case node_of constructor of
          DatatypeConstructor (_, _, selectors) =>
            List.app check_selector selectors
    in
      case node_of decl of
        DatatypeDecl (_, constructors) =>
          List.app check_constructor constructors
    end

  fun typecheck_declare_datatype elaborate_datatypes context name decl
      (tydict, tmdict, sigdict) =
    let
      val arity =
        case node_of decl of
          DatatypeDecl (params, _) => List.length params
      val result =
        if elaborate_datatypes then
          let
            val _ = check_elaborated_datatype_surface context decl
          in
            SOME (#define_datatype
              (require_datatype_elaborator context (loc_of name)) (name, decl))
          end
        else NONE
      val tydict =
        if elaborate_datatypes then tydict
        else extend_datatype_sort context name arity tydict
    in
      case result of
        SOME elaboration =>
          install_real_datatype_elaboration elaboration
            (tydict, tmdict, sigdict)
      | NONE =>
          typecheck_datatype_body context name decl (tydict, tmdict, sigdict)
    end

  fun typecheck_declare_datatypes elaborate_datatypes context bindings decls
      (tydict, tmdict, sigdict) =
    let
      val _ =
        if List.length bindings = List.length decls then ()
        else type_error "typecheck_declare_datatypes" context
          (case bindings of b :: _ => loc_of b
           | [] => (case decls of d :: _ => loc_of d
                    | [] => raise ERR "typecheck_declare_datatypes"
                        "empty declare-datatypes command"))
          NONE NONE
          "datatype binding count does not match datatype declaration count"

      fun binding_info binding =
        case node_of binding of
          DatatypeBinding (name, arity) =>
            (name, datatype_arity context (loc_of arity)
               (located_string_node name) (located_string_node arity))

      val infos = List.map binding_info bindings

      fun check_decl_arity ((name, arity), decl) =
        case node_of decl of
          DatatypeDecl (params, _) =>
            if arity = List.length params then ()
            else type_error "typecheck_declare_datatypes" context (loc_of decl)
              NONE NONE
              ("declare-datatypes arity for '" ^ located_string_node name ^
               "': expected " ^ Int.toString arity ^ ", actual " ^
               Int.toString (List.length params))

      val _ = List.app check_decl_arity (ListPair.zip (infos, decls))

      val tydict =
        if elaborate_datatypes then tydict
        else
          List.foldl
            (fn ((name, arity), tydict) =>
              extend_datatype_sort context name arity tydict)
            tydict infos
      fun add_one ((name, _), decl, (tydict, tmdict, sigdict)) =
        typecheck_datatype_body context name decl (tydict, tmdict, sigdict)
    in
      if elaborate_datatypes then
        let
          val _ = List.app (check_elaborated_datatype_surface context) decls
          val hooks =
            require_datatype_elaborator context
              (case bindings of b :: _ => loc_of b
               | [] => (case decls of d :: _ => loc_of d
                        | [] => raise ERR "typecheck_declare_datatypes"
                            "empty declare-datatypes command"))
          val result = #define_datatypes hooks (bindings, decls)
        in
          install_real_datatype_elaboration result (tydict, tmdict, sigdict)
        end
      else
        ListPair.foldl add_one (tydict, tmdict, sigdict) (infos, decls)
    end

  fun mk_definition tm vars definiens =
    let
      val vars = List.map #2 vars
      val equation =
        boolSyntax.mk_eq (Term.list_mk_comb (tm, vars), definiens)
    in
      boolSyntax.list_mk_forall (vars, equation)
    end

  fun define_typechecked_fun context loc name vars range_type range_surface
      definiens (tmdict, sigdict) =
    let
      val _ = reject_duplicate_definition context loc name sigdict
      val domain_types = List.map (Term.type_of o #2) vars
      val domain_surface = List.map #3 vars
      val (tm, tmdict, sigdict) =
        add_value_signature_with_surface name domain_types domain_surface
          range_type range_surface (tmdict, sigdict)
      val definition = mk_definition tm vars definiens
    in
      (tmdict, sigdict, definition)
    end

  fun add_sorted_vars_to_env vars (tmdict, sigdict) =
    List.foldl
      (fn ((vname, var, surface_sort), (tmdict, sigdict)) =>
        add_value_term_signature_with_surface vname var [] []
          (Term.type_of var) surface_sort (tmdict, sigdict))
      (tmdict, sigdict) vars

  fun typecheck_definition_body elaborate_datatypes context loc body
      (tydict, tmdict, sigdict) vars range_type range_surface =
    let
      val (body_tmdict, body_sigdict) =
        add_sorted_vars_to_env vars (tmdict, sigdict)
      val body_checked =
        typecheck_term_with_options elaborate_datatypes context
          (tydict, body_tmdict, body_sigdict) body
    in
      expect_checked_surface_sort "typecheck_definition_body" context loc
        range_type range_surface body_checked
    end

  fun typecheck_define_const elaborate_datatypes context name sort body
      (tydict, tmdict, sigdict) =
    let
      val name_loc = loc_of name
      val name = located_string_node name
      val _ = reject_duplicate_definition context name_loc name sigdict
      val range_type = typecheck_sort context tydict sort
      val range_surface = surface_sort_of_ast context tydict sort
      val body_checked =
        typecheck_term_with_options elaborate_datatypes context
          (tydict, tmdict, sigdict) body
      val body_term = expect_checked_surface_sort "typecheck_define_const"
        context (loc_of body) range_type range_surface body_checked
      val (tmdict, sigdict, definition) =
        define_typechecked_fun context name_loc name [] range_type
          range_surface body_term
          (tmdict, sigdict)
    in
      (tmdict, sigdict, definition)
    end

  fun typecheck_define_fun elaborate_datatypes context name sorted_vars range body
      (tydict, tmdict, sigdict) =
    let
      val name_loc = loc_of name
      val name = located_string_node name
      val _ = reject_duplicate_definition context name_loc name sigdict
      fun term_mentions_name term =
        case node_of term of
          TermIdentifier n => n = name
        | TermString _ => false
        | TermIndexed (head, indices) =>
            located_string_node head = name orelse
            List.exists term_mentions_name indices
        | TermApply (head, args) =>
            term_mentions_name head orelse List.exists term_mentions_name args
        | TermApplyOperator (_, head, args) =>
            term_mentions_name head orelse List.exists term_mentions_name args
        | TermAscribed (term, _) => term_mentions_name term
        | TermLet (bindings, body) =>
            List.exists (term_mentions_name o Lib.snd) bindings orelse
            term_mentions_name body
        | TermMatch (scrutinee, branches) =>
            let
              fun branch_mentions branch =
                case node_of branch of
                  MatchCase (_, body) => term_mentions_name body
            in
              term_mentions_name scrutinee orelse
              List.exists branch_mentions branches
            end
        | TermForall (_, body) => term_mentions_name body
        | TermExists (_, body) => term_mentions_name body
        | TermLambda (_, body) => term_mentions_name body
        | TermAnnotated (term, _) => term_mentions_name term
      val _ =
        if term_mentions_name body then
          type_error "typecheck_define_fun" context (loc_of body) NONE NONE
            "recursive self-reference"
        else ()
      val range_type = typecheck_sort context tydict range
      val range_surface = surface_sort_of_ast context tydict range
      val vars = List.map (checked_sorted_var context tydict) sorted_vars
      val body_term =
        typecheck_definition_body elaborate_datatypes context (loc_of body)
          body (tydict, tmdict, sigdict) vars range_type range_surface
      val (tmdict, sigdict, definition) =
        define_typechecked_fun context name_loc name vars range_type
          range_surface body_term
          (tmdict, sigdict)
    in
      (tmdict, sigdict, definition)
    end

  fun typecheck_define_fun_rec elaborate_datatypes context name sorted_vars
      range body
      (tydict, tmdict, sigdict) =
    let
      val name_loc = loc_of name
      val name = located_string_node name
      val _ = reject_duplicate_definition context name_loc name sigdict
      val range_type = typecheck_sort context tydict range
      val range_surface = surface_sort_of_ast context tydict range
      val vars = List.map (checked_sorted_var context tydict) sorted_vars
      val domain_types = List.map (Term.type_of o #2) vars
      val domain_surface = List.map #3 vars
      val (tm, tmdict, sigdict) =
        add_value_signature_with_surface name domain_types domain_surface
          range_type range_surface (tmdict, sigdict)
      val body_term =
        typecheck_definition_body elaborate_datatypes context (loc_of body)
          body (tydict, tmdict, sigdict) vars range_type range_surface
      val definition = mk_definition tm vars body_term
    in
      (tmdict, sigdict, definition)
    end

  fun typecheck_define_funs_rec elaborate_datatypes context sigs bodies
      (tydict, tmdict, sigdict) =
    let
      val _ =
        if List.length sigs = List.length bodies then ()
        else raise ERR "typecheck_script"
          "malformed recursive definition block: function signature count does not match body count"

      fun add_signature_from_ast (sig_ast, (tmdict, sigdict, specs)) =
        case node_of sig_ast of
          FunctionSignature (name, sorted_vars, range) =>
            let
              val name_loc = loc_of name
              val name = located_string_node name
              val _ = reject_duplicate_definition context name_loc name sigdict
              val range_type = typecheck_sort context tydict range
              val range_surface = surface_sort_of_ast context tydict range
              val vars =
                List.map (checked_sorted_var context tydict) sorted_vars
              val domain_types = List.map (Term.type_of o #2) vars
              val domain_surface = List.map #3 vars
              val (tm, tmdict, sigdict) =
                add_value_signature_with_surface name domain_types
                  domain_surface range_type range_surface
                  (tmdict, sigdict)
            in
              (tmdict, sigdict,
               {tm = tm, vars = vars, range = range_type,
                range_surface = range_surface} :: specs)
            end

      val (tmdict, sigdict, specs) =
        List.foldl add_signature_from_ast (tmdict, sigdict, []) sigs
      val specs = List.rev specs

      fun make_def ({tm, vars, range, range_surface}, body) =
        let
          val body_term =
            typecheck_definition_body elaborate_datatypes context (loc_of body)
              body (tydict, tmdict, sigdict) vars range range_surface
        in
          mk_definition tm vars body_term
        end

      val definitions = ListPair.map make_def (specs, bodies)
    in
      (tmdict, sigdict, definitions)
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

  fun typecheck_bool_terms elaborate_datatypes context env fn_name terms =
    List.map (fn term =>
      let
        val checked =
          typecheck_term_with_options elaborate_datatypes context env term
      in
        if checked_sort checked = Type.bool then checked_term checked
        else
          type_error fn_name context (loc_of term) (SOME Type.bool)
            (SOME (checked_sort checked))
            "assumption literal must have Bool sort"
      end) terms

  fun typecheck_command
      ({dict_logic, solver, elaborate_datatypes}: typecheck_options) command state =
    let
      fun dictionary_logic logic =
        case dict_logic of SOME broad_logic => broad_logic | NONE => logic
      fun parsedicts_for_solver logic =
        case solver of
          SOME target => SmtLib_Logics.parsedicts_of_solver_logic target logic
        | NONE => SmtLib_Logics.parsedicts_of_any_solver_logic logic
      (* A command handler asks for several `context` values (one per phase
         that reports errors), all sharing the same logic.  The metadata index
         depends only on that logic, so derive it once and reuse it; only the
         command description varies between the returned contexts. *)
      val context_shared = ref NONE
      fun context command =
        let
          val (surface_flags, metadata_index) =
            case !context_shared of
              SOME shared => shared
            | NONE =>
                let
                  val {logic, surface_flags, ...} =
                    dest_typecheck_state command state
                  val metadata = SmtLib_Logics.metadata_of_logic
                    (dictionary_logic (visible_logic logic))
                  val shared = (surface_flags, build_metadata_index metadata)
                in
                  context_shared := SOME shared; shared
                end
        in
          command_context solver surface_flags metadata_index command
        end
      fun finish state = SOME state
      (* Sort aliases have already been expanded when this is called.  Test
         the resulting HOL types so a declared alias for [Set A] or [Bag A]
         cannot lose its cvc5 finiteness invariant. *)
      fun cvc5_set_type ty =
        #solver (context "set declaration") = SOME "cvc5" andalso
        pred_setSyntax.is_set_type ty
      fun cvc5_bag_type ty =
        #solver (context "bag declaration") = SOME "cvc5" andalso
        bagSyntax.is_bag_ty ty
      fun parsedicts_for logic =
        parsedicts_for_solver (dictionary_logic logic)
      fun typecheck_define_fun_command command_name name vars range body state =
        let
          val command_state = dest_typecheck_state command_name state
          val (tydict, tmdict, sigdict) =
            current_typecheck_dicts command_state
          val (tmdict, sigdict, def) =
            typecheck_define_fun elaborate_datatypes (context command_name)
              name vars range body (tydict, tmdict, sigdict)
          val command_state = update_current_typecheck_dicts
            (tydict, tmdict, sigdict) command_state
        in
          finish (add_typechecked_definition def command_state)
        end
      fun add_definitions definitions command_state =
        List.foldl
          (fn (def, state) => add_typechecked_definition def state)
          command_state definitions
    in
      case node_of command of
      CmdSetInfo _ => state
    | CmdSetOption _ =>
          if has_active_typecheck_state state then
            raise ERR "typecheck_script"
              "set-option after logic or assertions"
          else state
      | CmdSetLogic logic =>
          let
            val _ = not (has_active_typecheck_state state) orelse
              raise ERR "typecheck_script"
                "duplicate set-logic: set-logic issued more than once"
            val logic_name = located_string_node logic
            val (tydict, tmdict) = parsedicts_for logic_name
          in
            finish (new_typecheck_state logic_name tydict tmdict)
          end
      | CmdGetInfo option =>
          let
            val command_state = dest_typecheck_state "get-info" state
          in
            finish (add_typechecked_query
              (QueryGetInfo (located_string_node option)) command_state)
          end
      | CmdGetOption option =>
          let
            val command_state = dest_typecheck_state "get-option" state
          in
            finish (add_typechecked_query
              (QueryGetOption (located_string_node option)) command_state)
          end
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
            val (set_tm, tmdict, sigdict) =
              add_value_signature_with_surface name_text [] [] range
                (surface_sort_of_ast (context "declare-const") tydict sort)
                (tmdict, sigdict)
            val command_state = update_current_typecheck_dicts
              (tydict, tmdict, sigdict) command_state
            val command_state =
              if cvc5_set_type range then
                add_typechecked_finite_set set_tm [] command_state
              else if cvc5_bag_type range then
                add_typechecked_finite_bag set_tm [] command_state
              else command_state
          in
            finish command_state
          end
      | CmdDeclareFun (name, domain, range) =>
          let
            val command_state =
              dest_typecheck_state "declare-fun" state
            val (tydict, tmdict, sigdict) =
              current_typecheck_dicts command_state
            val domain_surface = List.map
              (surface_sort_of_ast (context "declare-fun") tydict) domain
            val domain = List.map
              (typecheck_sort (context "declare-fun") tydict) domain
            val range_surface =
              surface_sort_of_ast (context "declare-fun") tydict range
            val range_ty =
              typecheck_sort (context "declare-fun") tydict range
            val name_text = located_string_node name
            val _ = reject_duplicate_signature (context "declare-fun")
              (loc_of name) name_text domain range_ty sigdict
            val (set_tm, tmdict, sigdict) =
              add_value_signature_with_surface name_text domain domain_surface
                range_ty range_surface (tmdict, sigdict)
            val command_state = update_current_typecheck_dicts
              (tydict, tmdict, sigdict) command_state
            val command_state =
              if cvc5_set_type range_ty then
                add_typechecked_finite_set set_tm domain command_state
              else if cvc5_bag_type range_ty then
                add_typechecked_finite_bag set_tm domain command_state
              else command_state
          in
            finish command_state
          end
      | CmdDefineConst (name, sort, body) =>
          let
            val command_state =
              dest_typecheck_state "define-const" state
            val (tydict, tmdict, sigdict) =
              current_typecheck_dicts command_state
            val (tmdict, sigdict, def) =
              typecheck_define_const elaborate_datatypes
                (context "define-const") name sort body
                (tydict, tmdict, sigdict)
            val command_state = update_current_typecheck_dicts
              (tydict, tmdict, sigdict) command_state
          in
            finish (add_typechecked_definition def command_state)
          end
      | CmdDefineFun (name, vars, range, body) =>
          typecheck_define_fun_command "define-fun" name vars range body state
      | CmdDefineFunRec (name, vars, range, body) =>
          let
            val command_state = dest_typecheck_state "define-fun-rec" state
            val (tydict, tmdict, sigdict) =
              current_typecheck_dicts command_state
            val (tmdict, sigdict, def) =
              typecheck_define_fun_rec elaborate_datatypes
                (context "define-fun-rec")
                name vars range body (tydict, tmdict, sigdict)
            val command_state = update_current_typecheck_dicts
              (tydict, tmdict, sigdict) command_state
          in
            finish (add_typechecked_definition def command_state)
          end
      | CmdDefineFunsRec (sigs, bodies) =>
          let
            val command_state = dest_typecheck_state "define-funs-rec" state
            val (tydict, tmdict, sigdict) =
              current_typecheck_dicts command_state
            val (tmdict, sigdict, definitions) =
              typecheck_define_funs_rec elaborate_datatypes
                (context "define-funs-rec")
                sigs bodies (tydict, tmdict, sigdict)
            val command_state = update_current_typecheck_dicts
              (tydict, tmdict, sigdict) command_state
          in
            finish (add_definitions definitions command_state)
          end
      | CmdDeclareDatatype (name, decl) =>
          let
            val command_state =
              dest_typecheck_state "declare-datatype" state
            val (tydict, tmdict, sigdict) =
              current_typecheck_dicts command_state
            val (tydict, tmdict, sigdict) =
              typecheck_declare_datatype elaborate_datatypes
                (context "declare-datatype") name decl
                (tydict, tmdict, sigdict)
          in
            finish (update_current_typecheck_dicts
              (tydict, tmdict, sigdict) command_state)
          end
      | CmdDeclareDatatypes (bindings, decls) =>
          let
            val command_state =
              dest_typecheck_state "declare-datatypes" state
            val (tydict, tmdict, sigdict) =
              current_typecheck_dicts command_state
            val (tydict, tmdict, sigdict) =
              typecheck_declare_datatypes elaborate_datatypes
                (context "declare-datatypes")
                bindings decls (tydict, tmdict, sigdict)
          in
            finish (update_current_typecheck_dicts
              (tydict, tmdict, sigdict) command_state)
          end
      | CmdAssert term =>
          let
            val command_state = dest_typecheck_state "assert" state
            val env = current_typecheck_dicts command_state
            val (term, name) = split_assertion_term term
            val checked =
              typecheck_term_with_options elaborate_datatypes
                (context "assert") env term
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
            val logic = visible_logic (#logic command_state)
            val (tydict, tmdict) = parsedicts_for logic
          in
            finish (new_typecheck_state (reset_logic logic) tydict tmdict)
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
          in
            finish (add_typechecked_query
              (typechecked_check_sat_query command_state []) command_state)
          end
      | CmdCheckSatAssuming assumptions =>
          let
            val command_state =
              dest_typecheck_state "check-sat-assuming" state
            val assumptions = typecheck_bool_terms elaborate_datatypes
              (context "check-sat-assuming")
              (current_typecheck_dicts command_state)
              "typecheck_check_sat_assuming" assumptions
          in
            finish (add_typechecked_query
              (typechecked_check_sat_query command_state assumptions)
              command_state)
          end
      | CmdGetProof =>
          let val command_state = dest_typecheck_state "get-proof" state
          in finish (add_typechecked_query QueryGetProof command_state) end
      | CmdGetUnsatAssumptions =>
          let
            val command_state =
              dest_typecheck_state "get-unsat-assumptions" state
          in
            finish (add_typechecked_query QueryGetUnsatAssumptions command_state)
          end
      | CmdGetUnsatCore =>
          let
            val command_state = dest_typecheck_state "get-unsat-core" state
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
              typecheck_term_with_options elaborate_datatypes
                (context "get-value")
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

  val default_typecheck_options = {
    dict_logic = NONE,
    solver = NONE,
    elaborate_datatypes = false
  }

  fun typecheck_script_with_options options script : checked_script =
    let
      fun loop [] state = finalize_typecheck_state "(end-of-stream)" state
        | loop (command :: rest) state =
            (case node_of command of
               CmdExit => finalize_typecheck_state "exit" state
             | _ => loop rest (typecheck_command options command state))
    in
      loop script NONE
    end

  fun typecheck_script_with_dict_logic dict_logic script =
    typecheck_script_with_options
      {dict_logic = dict_logic, solver = NONE, elaborate_datatypes = false} script

  fun typecheck_script script =
    typecheck_script_with_options default_typecheck_options script

  fun typecheck_script_string text =
    typecheck_script (parse_script_string text)

  fun typecheck_script_string_with_dict_logic dict_logic text =
    typecheck_script_with_dict_logic (SOME dict_logic) (parse_script_string text)

  fun typecheck_script_string_with_options options text =
    typecheck_script_with_options options (parse_script_string text)

in

  val loc_of = loc_of
  val node_of = node_of
  val source_pos_to_string = source_pos_to_string
  val source_span_to_string = source_span_to_string
  val parse_script_string = parse_script_string
  val parse_script_file = parse_script_file
  val install_datatype_elaborator = install_datatype_elaborator
  val default_typecheck_options = default_typecheck_options
  val typecheck_script = typecheck_script
  val typecheck_script_with_options = typecheck_script_with_options
  val typecheck_script_with_dict_logic = typecheck_script_with_dict_logic
  val typecheck_script_string = typecheck_script_string
  val typecheck_script_string_with_options =
    typecheck_script_string_with_options
  val typecheck_script_string_with_dict_logic =
    typecheck_script_string_with_dict_logic

  val smtlib_mk_let_bindings = smtlib_mk_let_bindings
  val smtlib_mk_let = smtlib_mk_let

  val parse_declare_fun = parse_declare_fun

  val parse_type = parse_type
  val parse_type_list = parse_type_list

  val parse_term_with_cfg = parse_term_with_cfg
  val parse_term = parse_term
  val parse_term_list = parse_term_list
  val make_proof_stream_tokenizer = make_proof_stream_tokenizer
  val proof_string_token = proof_string_token
  val parse_benchmark_state = parse_benchmark_state
  val parse_benchmark = parse_benchmark

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
     Recursive definition commands predeclare their recursive signatures and
     add their equations to the assertion context.  Datatype commands install
     uninterpreted datatype sorts plus constructor, selector, and tester symbols
     for bounded command-state checking.  Any other command is rejected with
     "unknown command". *)

  fun parse_file_state_with_options
      (options as {dict_logic, ...}: typecheck_options) (path : string)
      : command_state_snapshot =
  let
    (* parse the file contents *)
    val _ = if !Library.trace > 1 then
        Feedback.HOL_MESG
          ("HolSmtLib: parsing SMT-LIB 2 benchmark file '" ^ path ^ "'" ^
           (case dict_logic of
              NONE => ""
            | SOME logic => " with " ^ logic ^ " dictionaries"))
      else ()
    val instream = TextIO.openIn path
    val text = TextIO.inputAll instream
    val _ = TextIO.closeIn instream
    val result = typecheck_script_string_with_options options text
  in
    result
  end

  fun parse_file_state (path : string) : command_state_snapshot =
    parse_file_state_with_options default_typecheck_options path

  fun parse_file_state_with_dict_logic dict_logic (path : string)
      : command_state_snapshot =
    parse_file_state_with_options
      {dict_logic = SOME dict_logic, solver = NONE,
       elaborate_datatypes = false} path

  fun parse_file (path : string)
      : string * Type.hol_type dict * Term.term dict * Term.term list =
    legacy_result_of_state (parse_file_state path)

end  (* local *)

end
