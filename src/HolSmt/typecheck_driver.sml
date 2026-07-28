(* Command-line typecheck driver for SMT-LIB conformance tests. *)

fun typecheck_usage () =
  "Usage: " ^ CommandLine.name () ^
  " <input.smt2> <logic> [--placeholder-datatypes]\n"

fun typecheck_die msg =
  (TextIO.output (TextIO.stdErr, msg ^ "\n");
   OS.Process.exit OS.Process.failure)

fun typecheck_extra_args () =
  case !BuildHeap_CLINE.buildheap_extra_data of
    SOME payload => String.fields (fn c => c = #"\n") payload
  | NONE => []

fun typecheck_args () =
  case CommandLine.arguments () of
    args as [_, _] => args
  | args as [_, _, "--placeholder-datatypes"] => args
  | _ => typecheck_extra_args ()

val _ = SmtLib_Datatypes.empty_name_map

fun typecheck_datatype_options elaborate =
  {dict_logic = NONE, elaborate_datatypes = elaborate}

fun typecheck_datatype_options_with_logic elaborate logic =
  {dict_logic = SOME logic, elaborate_datatypes = elaborate}

fun typecheck_count_assertions
    (state: SmtLib_Parser.command_state_snapshot) =
  List.length (#assertions state)

fun typecheck_count_queries
    (state: SmtLib_Parser.command_state_snapshot) =
  List.length (#queries state)

(* 'define-fun' bodies are part of the checked query, so the fragment gate
   has to see them too, or a quantifier or nonlinear product buried in a
   macro escapes the check.  Only the definiens and the parameters are
   benchmark constructs: the universal closure and the definiendum
   application are artefacts of the equational encoding, and handing those
   to the gate would report every parameterised macro as a quantified
   formula and as an uninterpreted application. *)
fun typecheck_definition_terms definition =
  let
    val (vars, body) = boolSyntax.strip_forall definition
    val definiens =
      Lib.snd (boolSyntax.dest_eq body)
        handle Feedback.HOL_ERR _ => body
  in
    definiens :: vars
  end

fun typecheck_query_fragment_terms queries =
  List.concat (List.map (fn query =>
    case query of
      SmtLib_Parser.QueryCheckSat
        {assumptions, assertions, local_definitions} =>
          List.concat
            (List.map typecheck_definition_terms local_definitions) @
          assertions @ assumptions
    | _ => []) queries)

fun typecheck_ok path expected_logic elaborate_datatypes =
let
  val _ = Library.trace := 0
  val (state: SmtLib_Parser.command_state_snapshot, scoped_parse_error) =
    (SmtLib_Parser.parse_file_state_with_options
       (typecheck_datatype_options elaborate_datatypes) path, NONE)
    handle Feedback.HOL_ERR holerr =>
      (SmtLib_Parser.parse_file_state_with_options
         (typecheck_datatype_options_with_logic elaborate_datatypes "ALL") path,
       SOME holerr)
  val observed_logic = #logic state
  val fragment_diagnostic =
    SmtLib_Logics.fragment_violation_diagnostic observed_logic
      (#surface_flags state)
      (typecheck_query_fragment_terms (#queries state))
in
  if observed_logic <> expected_logic then
    typecheck_die
      ("TYPECHECK_FAIL\n" ^
       "logic=" ^ expected_logic ^ "\n" ^
       "diagnostic=set-logic " ^ observed_logic ^
       " does not match requested logic " ^ expected_logic)
  else if Option.isSome fragment_diagnostic then
    typecheck_die
      ("TYPECHECK_FAIL\n" ^
       "logic=" ^ observed_logic ^ "\n" ^
       "diagnostic=logic fragment restrictions are not completely enforced: " ^
       valOf fragment_diagnostic)
  else if Option.isSome scoped_parse_error then
    raise Feedback.HOL_ERR (valOf scoped_parse_error)
  else
    (print
       ("TYPECHECK_PASS\n" ^
        "logic=" ^ observed_logic ^ "\n" ^
        "assertions=" ^ Int.toString (typecheck_count_assertions state) ^ "\n" ^
        "queries=" ^ Int.toString (typecheck_count_queries state) ^ "\n");
     OS.Process.exit OS.Process.success)
end
handle Feedback.HOL_ERR holerr =>
  typecheck_die
    ("TYPECHECK_FAIL\n" ^
     "logic=" ^ expected_logic ^ "\n" ^
     "diagnostic=" ^ Feedback.message_of holerr)
     | IO.Io {name, function, cause} =>
  typecheck_die
    ("TYPECHECK_FAIL\n" ^
     "logic=" ^ expected_logic ^ "\n" ^
     "diagnostic=I/O error in " ^ function ^ " for " ^ name ^
     ": " ^ General.exnMessage cause)
     | exn =>
  typecheck_die
    ("TYPECHECK_FAIL\n" ^
     "logic=" ^ expected_logic ^ "\n" ^
     "diagnostic=" ^ General.exnMessage exn)

val () =
  case typecheck_args () of
    [path, logic] => typecheck_ok path logic true
  | [path, logic, "--placeholder-datatypes"] => typecheck_ok path logic false
  | _ => typecheck_die (typecheck_usage ())
