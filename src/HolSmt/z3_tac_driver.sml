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

(* A build heap has no active theory.  Native SMT datatypes create HOL
   types, so establish an ephemeral theory before a driver elaborates them. *)
val _ =
  case Thm.getCT () of
    NONE => Theory.new_theory "HolSmtDriver"
  | SOME _ => ()

val _ = SmtLib_Datatypes.empty_name_map

val z3_tac_datatype_options =
  {dict_logic = NONE, solver = SOME "Z3", elaborate_datatypes = true}

fun z3_tac_datatype_options_with_logic logic =
  {dict_logic = SOME logic, solver = SOME "Z3", elaborate_datatypes = true}

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
    [SmtLib_Parser.QueryCheckSat _] => NONE
  | [SmtLib_Parser.QueryCheckSat _, SmtLib_Parser.QueryGetProof] => NONE
  | [SmtLib_Parser.QueryCheckSat _,
     SmtLib_Parser.QueryGetUnsatAssumptions] => NONE
  | [SmtLib_Parser.QueryCheckSat _, SmtLib_Parser.QueryGetUnsatCore] => NONE
  | [SmtLib_Parser.QueryCheckSat _, SmtLib_Parser.QueryGetUnsatCore,
     SmtLib_Parser.QueryGetUnsatAssumptions] => NONE
  | [SmtLib_Parser.QueryCheckSat _,
     SmtLib_Parser.QueryGetUnsatAssumptions,
     SmtLib_Parser.QueryGetUnsatCore] => NONE
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
      {assumptions, assertions, local_definitions, ...} :: _ =>
        local_definitions @ assertions @ assumptions
  | _ => []

fun z3_tac_query_assumptions queries =
  case queries of
    SmtLib_Parser.QueryCheckSat {assumptions, ...} :: _ => assumptions
  | _ => []

fun z3_tac_query_transfer_hypotheses queries =
  case queries of
    SmtLib_Parser.QueryCheckSat {transfer_hypotheses, ...} :: _ =>
      transfer_hypotheses
  | _ => []

(* 'define-fun' bodies reach the solver through 'local_definitions' (see
   'z3_tac_query_assertions'), so the fragment gate has to see them too, or
   a quantifier or nonlinear product buried in a macro escapes the check.
   Only the definiens and the parameters are benchmark constructs: the
   universal closure and the definiendum application are artefacts of the
   equational encoding, and handing those to the gate would report every
   parameterised macro as a quantified formula and as an uninterpreted
   application. *)
fun z3_tac_definition_terms definition =
  let
    val (vars, body) = boolSyntax.strip_forall definition
    val definiens =
      Lib.snd (boolSyntax.dest_eq body)
        handle Feedback.HOL_ERR _ => body
  in
    definiens :: vars
  end

fun z3_tac_query_fragment_terms queries =
  case queries of
    SmtLib_Parser.QueryCheckSat
      {assumptions, assertions, local_definitions, ...} :: _ =>
        List.concat (List.map z3_tac_definition_terms local_definitions) @
        assertions @ assumptions
  | _ => []

fun z3_tac_conjunction [] = boolSyntax.T
  | z3_tac_conjunction (tm :: tms) =
      List.foldl (fn (next, acc) => boolSyntax.mk_conj (acc, next)) tm tms

fun z3_tac_hypothesis_goal_required queries =
  case queries of
    SmtLib_Parser.QueryCheckSat {assumptions = _ :: _, ...} :: _ => true
  | SmtLib_Parser.QueryGetUnsatAssumptions :: _ => true
  | SmtLib_Parser.QueryGetUnsatCore :: _ => true
  | _ :: rest => z3_tac_hypothesis_goal_required rest
  | [] => false

fun z3_tac_goal queries assertions transfer_hypotheses =
  if z3_tac_hypothesis_goal_required queries then
    (transfer_hypotheses @ assertions, boolSyntax.F)
  else
    (transfer_hypotheses, boolSyntax.mk_neg (z3_tac_conjunction assertions))

(* The smallest symbolic-add commutativity proof in the Phase-5 corpus is
   already over 25 MB.  Keep this pre-solver check on the shared, unit-tested
   D12 contract rather than allocating Z3's proof text. *)
fun z3_tac_preflight_resource_gate terms =
  SmtFpProve.preflight_resource_gate terms

fun z3_tac_parenthesized_list items =
  "(" ^ String.concatWith " " items ^ ")"

fun z3_tac_term_member tm terms =
  List.exists (fn candidate => Term.aconv candidate tm) terms

fun z3_tac_unsat_assumption_terms thm assumptions =
  let val hyps = Thm.hyp thm
  in List.filter (fn assumption => z3_tac_term_member assumption hyps) assumptions end

fun z3_tac_unsat_core_names thm named_assertions =
  let val hyps = Thm.hyp thm
  in
    List.map Lib.fst
      (List.filter
        (fn (_, assertion) => z3_tac_term_member assertion hyps)
        named_assertions)
  end

fun z3_tac_unsat_response_fields thm queries assumptions named_assertions =
let
  val assumption_list =
    z3_tac_parenthesized_list
      (List.map Library.term_to_string
        (z3_tac_unsat_assumption_terms thm assumptions))
  val core_list =
    z3_tac_parenthesized_list
      (z3_tac_unsat_core_names thm named_assertions)
  fun add_fields [] fields = List.rev fields
    | add_fields (SmtLib_Parser.QueryGetUnsatAssumptions :: rest) fields =
        add_fields rest ("unsat_assumptions=" ^ assumption_list :: fields)
    | add_fields (SmtLib_Parser.QueryGetUnsatCore :: rest) fields =
        add_fields rest ("unsat_core=" ^ core_list :: fields)
    | add_fields (_ :: rest) fields = add_fields rest fields
in
  add_fields queries []
end

fun z3_tac_unsupported_command_diagnostic command =
  case SmtLib_Parser.node_of command of
    _ => NONE

fun z3_tac_command_query_name command =
  case SmtLib_Parser.node_of command of
    SmtLib_Parser.CmdCheckSat => SOME "check-sat"
  | SmtLib_Parser.CmdCheckSatAssuming _ => SOME "check-sat-assuming"
  | SmtLib_Parser.CmdGetProof => SOME "get-proof"
  | SmtLib_Parser.CmdGetUnsatAssumptions => SOME "get-unsat-assumptions"
  | SmtLib_Parser.CmdGetUnsatCore => SOME "get-unsat-core"
  | SmtLib_Parser.CmdGetModel => SOME "get-model"
  | SmtLib_Parser.CmdGetValue _ => SOME "get-value"
  | SmtLib_Parser.CmdGetAssignment => SOME "get-assignment"
  | SmtLib_Parser.CmdGetAssertions => SOME "get-assertions"
  | SmtLib_Parser.CmdGetInfo _ => SOME "get-info"
  | SmtLib_Parser.CmdGetOption _ => SOME "get-option"
  | _ => NONE

fun z3_tac_script_query_diagnostic query_names =
  case query_names of
    ["check-sat"] => NONE
  | ["check-sat", "get-proof"] => NONE
  | ["check-sat-assuming"] => NONE
  | ["check-sat-assuming", "get-proof"] => NONE
  | ["check-sat", "get-unsat-assumptions"] => NONE
  | ["check-sat-assuming", "get-unsat-assumptions"] => NONE
  | ["check-sat", "get-unsat-core"] => NONE
  | ["check-sat-assuming", "get-unsat-core"] => NONE
  | ["check-sat", "get-unsat-core", "get-unsat-assumptions"] => NONE
  | ["check-sat-assuming", "get-unsat-core", "get-unsat-assumptions"] => NONE
  | ["check-sat", "get-unsat-assumptions", "get-unsat-core"] => NONE
  | ["check-sat-assuming", "get-unsat-assumptions", "get-unsat-core"] => NONE
  | [] =>
      SOME "no check-sat query in raw SMT-LIB script for checked Z3_TAC"
  | "check-sat" :: query :: _ =>
      SOME ("raw SMT-LIB query " ^ query ^
            " is outside checked Z3_TAC command-line entry point")
  | query :: _ =>
      SOME ("raw SMT-LIB query " ^ query ^
            " is outside checked Z3_TAC command-line entry point")

fun z3_tac_term_uses_fold_left term =
  let
    fun any terms = List.exists scan terms
    and scan term =
      case SmtLib_Parser.node_of term of
        SmtLib_Parser.TermIdentifier "seq.fold_left" => true
      | SmtLib_Parser.TermIdentifier _ => false
      | SmtLib_Parser.TermString _ => false
      | SmtLib_Parser.TermIndexed (_, args) => any args
      | SmtLib_Parser.TermApply (head, args) => scan head orelse any args
      | SmtLib_Parser.TermApplyOperator (_, head, args) =>
          scan head orelse any args
      | SmtLib_Parser.TermAscribed (body, _) => scan body
      | SmtLib_Parser.TermLet (bindings, body) =>
          List.exists (fn (_, value) => scan value) bindings orelse scan body
      | SmtLib_Parser.TermMatch (scrutinee, cases) =>
          scan scrutinee orelse List.exists (fn case_ast =>
            case SmtLib_Parser.node_of case_ast of
              SmtLib_Parser.MatchCase (_, body) => scan body) cases
      | SmtLib_Parser.TermForall (_, body) => scan body
      | SmtLib_Parser.TermExists (_, body) => scan body
      | SmtLib_Parser.TermLambda (_, body) => scan body
      | SmtLib_Parser.TermAnnotated (body, _) => scan body
  in
    scan term
  end

fun z3_tac_command_uses_fold_left command =
  let
    fun any terms = List.exists z3_tac_term_uses_fold_left terms
  in
    case SmtLib_Parser.node_of command of
      SmtLib_Parser.CmdDefineConst (_, _, body) => z3_tac_term_uses_fold_left body
    | SmtLib_Parser.CmdDefineFun (_, _, _, body) => z3_tac_term_uses_fold_left body
    | SmtLib_Parser.CmdDefineFunRec (_, _, _, body) =>
        z3_tac_term_uses_fold_left body
    | SmtLib_Parser.CmdDefineFunsRec (_, bodies) => any bodies
    | SmtLib_Parser.CmdAssert body => z3_tac_term_uses_fold_left body
    | SmtLib_Parser.CmdCheckSatAssuming terms => any terms
    | SmtLib_Parser.CmdGetValue terms => any terms
    | _ => false
  end

fun z3_tac_script_diagnostic path =
  let
    val script = SmtLib_Parser.parse_script_file path
    val unsupported_fold_left =
      Z3.configured_version () = SOME "4.11.2" andalso
      List.exists z3_tac_command_uses_fold_left script
    fun scan [] query_names =
          z3_tac_script_query_diagnostic (List.rev query_names)
      | scan (command :: rest) query_names =
          (case SmtLib_Parser.node_of command of
             SmtLib_Parser.CmdExit => NONE
           | _ =>
             case z3_tac_unsupported_command_diagnostic command of
               SOME diagnostic => SOME diagnostic
             | NONE =>
                 scan rest
                   (case z3_tac_command_query_name command of
                      SOME name => name :: query_names
                    | NONE => query_names))
  in
    if unsupported_fold_left then
      SOME "seq.fold_left requires Z3 4.12.4 or later"
    else scan script []
  end

datatype z3_tac_checked_result =
    Z3_TAC_UNSAT of Thm.thm
  | Z3_TAC_SAT
  | Z3_TAC_UNKNOWN of string option

fun z3_tac_raw_result path =
  let
    val output = OS.FileSys.tmpName ()
    val executable =
      case Z3.configured_executable () of
        SOME executable => executable
      | NONE => raise Feedback.mk_HOL_ERR "Z3_TAC_Driver" "z3_tac_raw_result"
          Z3.error_msg
    fun quote path =
      "'" ^ String.translate
        (fn #"'" => "'\\''" | character => str character) path ^ "'"
    fun work () =
      (ignore (OS.Process.system
         (quote executable ^ " -smt2 -file:" ^ quote path ^ " > " ^ quote output));
       Z3.is_sat_file output)
    fun cleanup () = OS.FileSys.remove output handle OS.SysErr _ => ()
  in
    Portable.finally cleanup work ()
  end

fun z3_tac_checked_result goal =
  case Z3.Z3_SMT_Prover goal of
    SolverSpec.UNSAT (SOME thm) =>
      let val () = Library.check_oracle_tags "Z3_TAC conformance driver" thm
      in Z3_TAC_UNSAT thm end
  | SolverSpec.UNSAT NONE =>
      raise Feedback.mk_HOL_ERR "Z3_TAC_Driver" "z3_tac_checked_prove"
        "Z3_TAC prover returned UNSAT without a checked theorem"
  | SolverSpec.SAT NONE => Z3_TAC_SAT
  | SolverSpec.SAT (SOME _) => Z3_TAC_SAT
  | SolverSpec.UNKNOWN message => Z3_TAC_UNKNOWN message

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
  val (state: SmtLib_Parser.command_state_snapshot, scoped_parse_error) =
    (SmtLib_Parser.parse_file_state_with_options
       z3_tac_datatype_options path, NONE)
    handle Feedback.HOL_ERR holerr =>
      (SmtLib_Parser.parse_file_state_with_options
         (z3_tac_datatype_options_with_logic "ALL") path,
       SOME holerr)
  val observed_logic = #logic state
  val queries = #queries state
  val assertions = z3_tac_query_assertions queries
  val assumptions = z3_tac_query_assumptions queries
  val fragment_diagnostic =
    SmtLib_Logics.fragment_violation_diagnostic observed_logic
      (#surface_flags state) (z3_tac_query_fragment_terms queries)
in
  if observed_logic <> expected_logic then
    z3_tac_die "Z3_TAC_FAIL"
      ["logic=" ^ expected_logic,
       "diagnostic=set-logic " ^ observed_logic ^
       " does not match requested logic " ^ expected_logic]
  else if Option.isSome fragment_diagnostic then
    z3_tac_die "Z3_TAC_FAIL"
      ["logic=" ^ observed_logic,
       "diagnostic=checked mode must reject logic fragment violations before reconstruction: " ^
         valOf fragment_diagnostic]
  else if Option.isSome scoped_parse_error then
    raise Feedback.HOL_ERR (valOf scoped_parse_error)
  else
    case z3_tac_query_diagnostic queries of
      SOME diagnostic =>
        z3_tac_die "Z3_TAC_UNSUPPORTED"
          ["logic=" ^ observed_logic,
           "diagnostic=" ^ diagnostic,
           "queries=" ^ Int.toString (List.length queries)]
    | NONE =>
      let
        val transfer_hypotheses =
          z3_tac_query_transfer_hypotheses queries
        val goal = z3_tac_goal queries assertions transfer_hypotheses
        val expected_result = z3_tac_raw_result path
        val result =
          (z3_tac_preflight_resource_gate assertions;
           z3_tac_checked_result goal)
          handle Feedback.HOL_ERR holerr =>
            if SmtResource.is_resource_gate holerr then
              z3_tac_die "Z3_TAC_RESOURCE_GATED"
                ["logic=" ^ observed_logic,
                 "diagnostic=" ^ Feedback.message_of holerr]
            else
              raise Feedback.HOL_ERR holerr
        val common_fields =
          ["logic=" ^ observed_logic,
           "assertions=" ^ Int.toString (List.length (#assertions state)),
           "local_definitions=" ^ Int.toString (List.length (#local_definitions state)),
           "queries=" ^ Int.toString (List.length queries),
           "z3_version=" ^ Z3.version_string ()]
      in
        case (expected_result, result) of
          (SolverSpec.UNSAT _, Z3_TAC_UNSAT thm) =>
            z3_tac_emit "Z3_TAC_PASS"
              (common_fields @
               ["result=unsat",
                "theorem=" ^ Library.thm_to_string thm] @
               z3_tac_unsat_response_fields thm queries assumptions
                 (#named_assertions state))
        | (SolverSpec.SAT _, Z3_TAC_SAT) =>
            z3_tac_emit "Z3_TAC_PASS" (common_fields @ ["result=sat"])
        | (SolverSpec.UNKNOWN NONE, _) =>
            z3_tac_die "Z3_TAC_UNSUPPORTED"
              (common_fields @
               ["expected=unknown",
                "diagnostic=raw Z3 result is UNKNOWN"])
        | (SolverSpec.UNKNOWN (SOME message), _) =>
            z3_tac_die "Z3_TAC_UNSUPPORTED"
              (common_fields @
               ["expected=unknown", "diagnostic=raw Z3 result is UNKNOWN: " ^
                 message])
        | (SolverSpec.UNSAT _, Z3_TAC_SAT) =>
            z3_tac_die "Z3_TAC_FAIL"
              (common_fields @
               ["expected=unsat", "result=sat",
                "diagnostic=translated query lost native Z3 unsatisfiability"])
        | (SolverSpec.SAT _, Z3_TAC_UNSAT _) =>
            z3_tac_die "Z3_TAC_FAIL"
              (common_fields @
               ["expected=sat", "result=unsat",
                "diagnostic=translated query changed the native Z3 result"])
        | (SolverSpec.UNSAT _, Z3_TAC_UNKNOWN NONE) =>
            z3_tac_die "Z3_TAC_UNSUPPORTED"
              (common_fields @
               ["expected=unsat", "result=unknown",
                "diagnostic=UNSAT result has no HOL theorem to reconstruct"])
        | (SolverSpec.UNSAT _, Z3_TAC_UNKNOWN (SOME message)) =>
            z3_tac_die "Z3_TAC_UNSUPPORTED"
              (common_fields @
               ["expected=unsat", "result=unknown",
                "diagnostic=UNSAT result has no HOL theorem to reconstruct: " ^
                  message])
        | (SolverSpec.SAT _, Z3_TAC_UNKNOWN NONE) =>
            z3_tac_die "Z3_TAC_UNSUPPORTED"
              (common_fields @
               ["expected=sat", "result=unknown",
                "diagnostic=SAT result was not reproduced"])
        | (SolverSpec.SAT _, Z3_TAC_UNKNOWN (SOME message)) =>
            z3_tac_die "Z3_TAC_UNSUPPORTED"
              (common_fields @
               ["expected=sat", "result=unknown",
                "diagnostic=SAT result was not reproduced: " ^ message]);
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
