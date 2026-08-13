(* Command-line checked cvc5/CPC driver for SMT-LIB replay matrices. *)

fun cvc_cpc_emit status fields =
  print (String.concatWith "\n" (status :: fields) ^ "\n")

fun cvc_cpc_die status fields =
  (cvc_cpc_emit status fields; OS.Process.exit OS.Process.failure)

fun cvc_cpc_args () =
  case CommandLine.arguments () of
    args as [_, _] => args
  | _ =>
      (case !BuildHeap_CLINE.buildheap_extra_data of
         SOME payload => String.fields (fn c => c = #"\n") payload
       | NONE => [])

val _ = SmtLib_Datatypes.empty_name_map

val _ =
  case Thm.getCT () of
    NONE => Feedback.quiet_messages Theory.new_theory "HolSmtDriver"
  | SOME _ => ()

fun cvc_cpc_conjunction [] = boolSyntax.T
  | cvc_cpc_conjunction (tm :: tms) =
      List.foldl (fn (next, acc) => boolSyntax.mk_conj (acc, next)) tm tms

(* 'define-fun' bodies reach the solver through 'local_definitions', so the
   fragment gate has to see them too, or a quantifier or nonlinear product
   buried in a macro escapes the check.  Only the definiens and the
   parameters are benchmark constructs: the universal closure and the
   definiendum application are artefacts of the equational encoding, and
   handing those to the gate would report every parameterised macro as a
   quantified formula and as an uninterpreted application. *)
fun cvc_cpc_definition_terms definition =
  let
    val (vars, body) = boolSyntax.strip_forall definition
    val definiens =
      Lib.snd (boolSyntax.dest_eq body)
        handle Feedback.HOL_ERR _ => body
  in
    definiens :: vars
  end

fun cvc_cpc_query_fragment_terms queries =
  List.concat (List.map (fn query =>
    case query of
      SmtLib_Parser.QueryCheckSat
        {assumptions, assertions, local_definitions, ...} =>
          List.concat (List.map cvc_cpc_definition_terms local_definitions) @
          assertions @ assumptions
    | _ => []) queries)

fun cvc_cpc_goal queries =
  let
    val check_sat =
      case queries of
        SmtLib_Parser.QueryCheckSat query :: [] => query
      | SmtLib_Parser.QueryCheckSat query :: [SmtLib_Parser.QueryGetProof] =>
          query
      | _ => raise Feedback.mk_HOL_ERR "CVC_CPC_TAC_Driver" "cvc_cpc_goal"
        "only check-sat followed optionally by get-proof is supported"
  in
    case check_sat of
      {assumptions = [], assertions, local_definitions, transfer_hypotheses} =>
      (transfer_hypotheses, boolSyntax.mk_neg
        (cvc_cpc_conjunction (local_definitions @ assertions)))
    | {assertions, assumptions, local_definitions, transfer_hypotheses, ...} =>
      (transfer_hypotheses @ local_definitions @ assertions @ assumptions,
       boolSyntax.F)
  end
  (*** Removed obsolete direct query matching. ***)
  (***
    [SmtLib_Parser.QueryCheckSat
       {assumptions = [], assertions, local_definitions}] =>
      ([], boolSyntax.mk_neg
        (cvc_cpc_conjunction (local_definitions @ assertions)))
  | [SmtLib_Parser.QueryCheckSat {assertions, assumptions, local_definitions}] =>
      (local_definitions @ assertions @ assumptions, boolSyntax.F)
  | _ => raise Feedback.mk_HOL_ERR "CVC_CPC_TAC_Driver" "cvc_cpc_goal"
    "only a single check-sat command is supported by the CPC matrix driver"
  ***)

fun cvc_cpc_run path expected_logic =
  let
    val _ = Library.trace := 0
    val (state, scoped_parse_error) =
      (SmtLib_Parser.parse_file_state_with_options
         {dict_logic = NONE, solver = SOME "cvc5",
          elaborate_datatypes = true} path, NONE)
      handle Feedback.HOL_ERR holerr =>
        (SmtLib_Parser.parse_file_state_with_options
           {dict_logic = SOME "ALL", solver = SOME "cvc5",
            elaborate_datatypes = true} path,
         SOME holerr)
    val observed_logic = #logic state
    val fragment_diagnostic =
      SmtLib_Logics.fragment_violation_diagnostic observed_logic
        (#surface_flags state)
        (cvc_cpc_query_fragment_terms (#queries state))
    val _ =
      if observed_logic <> expected_logic then
        raise Feedback.mk_HOL_ERR "CVC_CPC_TAC_Driver" "cvc_cpc_run"
          ("set-logic " ^ observed_logic ^ " does not match requested logic " ^
           expected_logic)
      else
        case fragment_diagnostic of
          SOME diagnostic =>
            raise Feedback.mk_HOL_ERR "CVC_CPC_TAC_Driver" "cvc_cpc_run"
              ("checked mode must reject logic fragment violations before " ^
               "reconstruction: " ^ diagnostic)
        | NONE =>
            (case scoped_parse_error of
               SOME holerr => raise Feedback.HOL_ERR holerr
             | NONE => ())
    val result = CVC.CVC_SMT_CPC_Prover (cvc_cpc_goal (#queries state))
    val fields = ["logic=" ^ observed_logic,
                  "cvc5_version=" ^ CVC.version_string ()]
  in
    case result of
      SolverSpec.UNSAT (SOME thm) =>
        let val () = Library.check_oracle_tags "HolSmtLib" "CPC conformance driver" thm
        in cvc_cpc_emit "CVC_CPC_TAC_PASS"
             (fields @ ["result=unsat", "theorem=" ^ Library.thm_to_string thm]);
           OS.Process.exit OS.Process.success
        end
    | SolverSpec.SAT _ =>
        cvc_cpc_die "CVC_CPC_TAC_FAIL"
          (fields @ ["result=sat", "diagnostic=expected unsat"])
    | SolverSpec.UNKNOWN message =>
        cvc_cpc_die "CVC_CPC_TAC_UNSUPPORTED"
          (fields @ ["result=unknown", "diagnostic=" ^
             Option.getOpt (message, "cvc5 returned unknown")])
    | SolverSpec.UNSAT NONE =>
        cvc_cpc_die "CVC_CPC_TAC_FAIL"
          (fields @ ["diagnostic=UNSAT result omitted checked theorem"])
  end
  handle Feedback.HOL_ERR holerr =>
    if SmtResource.is_resource_gate holerr then
      (cvc_cpc_emit "CVC_CPC_TAC_RESOURCE_GATED"
         ["logic=" ^ expected_logic,
          "diagnostic=" ^ Feedback.message_of holerr];
       OS.Process.exit OS.Process.success)
    else
      cvc_cpc_die "CVC_CPC_TAC_FAIL"
        ["logic=" ^ expected_logic,
         "diagnostic=" ^ Feedback.message_of holerr]
    | exn => cvc_cpc_die "CVC_CPC_TAC_FAIL"
      ["logic=" ^ expected_logic, "diagnostic=" ^ General.exnMessage exn]

val () =
  case cvc_cpc_args () of
    [path, logic] => cvc_cpc_run path logic
  | _ => cvc_cpc_die "CVC_CPC_TAC_FAIL"
      ["diagnostic=Usage: <input.smt2> <logic>"]
