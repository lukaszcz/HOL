(* Command-line checked Z3_TAC driver for SMT-LIB conformance tests. *)

fun z3_tac_usage () =
  "Usage: " ^ CommandLine.name () ^ " <input.smt2> <logic>\n"

fun z3_tac_emit status fields =
  print (String.concatWith "\n" (status :: fields) ^ "\n")

fun z3_tac_die status fields =
  (z3_tac_emit status fields;
   OS.Process.exit OS.Process.failure)

fun z3_tac_extra_args () =
  case !BuildHeap_CLINE.buildheap_extra_data of
    SOME payload => String.fields (fn c => c = #"\n") payload
  | NONE => []

fun z3_tac_args () =
  case CommandLine.arguments () of
    args as [_, _] => args
  | _ => z3_tac_extra_args ()

fun z3_tac_query_name query =
  case query of
    SmtLib_Parser.QueryCheckSat {assumptions = [], ...} => "check-sat"
  | SmtLib_Parser.QueryCheckSat _ => "check-sat-assuming"
  | SmtLib_Parser.QueryGetProof => "get-proof"
  | SmtLib_Parser.QueryGetUnsatAssumptions => "get-unsat-assumptions"
  | SmtLib_Parser.QueryGetUnsatCore => "get-unsat-core"
  | SmtLib_Parser.QueryGetModel => "get-model"
  | SmtLib_Parser.QueryGetValue _ => "get-value"
  | SmtLib_Parser.QueryGetAssignment => "get-assignment"
  | SmtLib_Parser.QueryGetAssertions => "get-assertions"
  | SmtLib_Parser.QueryGetInfo _ => "get-info"
  | SmtLib_Parser.QueryGetOption _ => "get-option"

fun z3_tac_query_diagnostic queries =
  case queries of
    [SmtLib_Parser.QueryCheckSat {assumptions = [], ...}] => NONE
  | [SmtLib_Parser.QueryCheckSat {assumptions = [], ...},
     SmtLib_Parser.QueryGetProof] => NONE
  | [SmtLib_Parser.QueryCheckSat {assumptions = _ :: _, ...}] =>
      SOME "check-sat-assuming is outside checked Z3_TAC command-line entry point"
  | [SmtLib_Parser.QueryCheckSat {assumptions = _ :: _, ...},
     SmtLib_Parser.QueryGetProof] =>
      SOME "check-sat-assuming is outside checked Z3_TAC command-line entry point"
  | [] =>
      SOME "no check-sat query in raw SMT-LIB script for checked Z3_TAC"
  | SmtLib_Parser.QueryCheckSat _ :: query :: _ =>
      SOME ("raw SMT-LIB query " ^ z3_tac_query_name query ^
            " is outside checked Z3_TAC command-line entry point")
  | query :: _ =>
      SOME ("raw SMT-LIB query " ^ z3_tac_query_name query ^
            " is outside checked Z3_TAC command-line entry point")

fun z3_tac_query_assertions queries =
  case queries of
    SmtLib_Parser.QueryCheckSat
      {assumptions, assertions, local_definitions} :: _ =>
        local_definitions @ assertions @ assumptions
  | _ => []

fun z3_tac_conjunction [] = boolSyntax.T
  | z3_tac_conjunction (tm :: tms) =
      List.foldl (fn (next, acc) => boolSyntax.mk_conj (acc, next)) tm tms

fun z3_tac_goal assertions =
  boolSyntax.mk_neg (z3_tac_conjunction assertions)

fun z3_tac_unsupported_command_diagnostic command =
  case SmtLib_Parser.node_of command of
    SmtLib_Parser.CmdCheckSatAssuming _ =>
      SOME "check-sat-assuming is outside checked Z3_TAC command-line entry point"
  | SmtLib_Parser.CmdDefineFunRec _ =>
      SOME "recursive definition command define-fun-rec is outside checked Z3_TAC command-line entry point"
  | SmtLib_Parser.CmdDefineFunsRec _ =>
      SOME "recursive definition command define-funs-rec is outside checked Z3_TAC command-line entry point"
  | SmtLib_Parser.CmdDeclareDatatype _ =>
      SOME "datatype declaration command declare-datatype is outside checked Z3_TAC command-line entry point"
  | SmtLib_Parser.CmdDeclareDatatypes _ =>
      SOME "datatype declaration command declare-datatypes is outside checked Z3_TAC command-line entry point"
  | _ => NONE

fun z3_tac_script_diagnostic path =
  let
    val script = SmtLib_Parser.parse_script_file path
    val diagnostics = List.map z3_tac_unsupported_command_diagnostic script
  in
    case List.find Option.isSome diagnostics of
      SOME (SOME diagnostic) => SOME diagnostic
    | _ => NONE
  end

fun z3_tac_checked_prove goal =
  case Z3.Z3_SMT_Prover ([], goal) of
    SolverSpec.UNSAT (SOME thm) =>
      let val () = Library.check_oracle_tags "Z3_TAC conformance driver" thm
      in thm end
  | SolverSpec.UNSAT NONE =>
      raise Feedback.mk_HOL_ERR "Z3_TAC_Driver" "z3_tac_checked_prove"
        "Z3_TAC prover returned UNSAT without a checked theorem"
  | SolverSpec.SAT NONE =>
      raise Feedback.mk_HOL_ERR "Z3_TAC_Driver" "z3_tac_checked_prove"
        "solver reports negated term to be satisfiable"
  | SolverSpec.SAT (SOME _) =>
      raise Feedback.mk_HOL_ERR "Z3_TAC_Driver" "z3_tac_checked_prove"
        "solver reports negated term to be satisfiable with a model"
  | SolverSpec.UNKNOWN NONE =>
      raise Feedback.mk_HOL_ERR "Z3_TAC_Driver" "z3_tac_checked_prove"
        "solver reports unknown"
  | SolverSpec.UNKNOWN (SOME message) =>
      raise Feedback.mk_HOL_ERR "Z3_TAC_Driver" "z3_tac_checked_prove"
        ("solver reports unknown: " ^ message)

fun z3_tac_ok path expected_logic =
let
  val _ = Library.trace := 0
  val script_diagnostic = z3_tac_script_diagnostic path
  val _ =
    case script_diagnostic of
      SOME diagnostic =>
        z3_tac_die "Z3_TAC_UNSUPPORTED"
          ["logic=" ^ expected_logic,
           "diagnostic=" ^ diagnostic]
    | NONE => ()
  val state: SmtLib_Parser.command_state_snapshot =
    SmtLib_Parser.parse_file_state path
  val observed_logic = #logic state
  val queries = #queries state
  val assertions = z3_tac_query_assertions queries
in
  if observed_logic <> expected_logic then
    z3_tac_die "Z3_TAC_FAIL"
      ["logic=" ^ expected_logic,
       "diagnostic=set-logic " ^ observed_logic ^
       " does not match requested logic " ^ expected_logic]
  else
    case z3_tac_query_diagnostic queries of
      SOME diagnostic =>
        z3_tac_die "Z3_TAC_UNSUPPORTED"
          ["logic=" ^ observed_logic,
           "diagnostic=" ^ diagnostic,
           "queries=" ^ Int.toString (List.length queries)]
    | NONE =>
      let
        val goal = z3_tac_goal assertions
        val thm = z3_tac_checked_prove goal
      in
        z3_tac_emit "Z3_TAC_PASS"
          ["logic=" ^ observed_logic,
           "assertions=" ^ Int.toString (List.length (#assertions state)),
           "local_definitions=" ^ Int.toString (List.length (#local_definitions state)),
           "queries=" ^ Int.toString (List.length queries),
           "z3_version=" ^ Z3.version_string (),
           "theorem=" ^ Library.thm_to_string thm];
        OS.Process.exit OS.Process.success
      end
end
handle Feedback.HOL_ERR holerr =>
  z3_tac_die "Z3_TAC_FAIL"
    ["logic=" ^ expected_logic,
     "diagnostic=" ^ Feedback.message_of holerr]
     | IO.Io {name, function, cause} =>
  z3_tac_die "Z3_TAC_FAIL"
    ["logic=" ^ expected_logic,
     "diagnostic=I/O error in " ^ function ^ " for " ^ name ^
     ": " ^ General.exnMessage cause]
     | exn =>
  z3_tac_die "Z3_TAC_FAIL"
    ["logic=" ^ expected_logic,
     "diagnostic=" ^ General.exnMessage exn]

val () =
  case z3_tac_args () of
    [path, logic] => z3_tac_ok path logic
  | _ => z3_tac_die "Z3_TAC_FAIL" ["diagnostic=" ^ z3_tac_usage ()]
