(* Functions to invoke the cvc5 SMT solver *)

structure CVC = struct

  (* returns SAT if cvc5 reported "sat", UNSAT if cvc5 reported "unsat" *)
  fun is_sat_stream instream =
    case Option.map (String.tokens Char.isSpace) (TextIO.inputLine instream) of
      NONE => SolverSpec.UNKNOWN NONE
    | SOME ["sat"] => SolverSpec.SAT NONE
    | SOME ["unsat"] => SolverSpec.UNSAT NONE
    | _ => is_sat_stream instream

  fun is_sat_file path =
    let
      val instream = TextIO.openIn path
    in
      is_sat_stream instream
        before TextIO.closeIn instream
    end

  fun get_nonempty_env name =
    case OS.Process.getEnv name of
      SOME file => if file = "" then NONE else SOME file
    | NONE => NONE

  fun command_available name =
    OS.Process.isSuccess
      (OS.Process.system ("command -v " ^ name ^ " >/dev/null 2>&1"))
    handle _ => false

  fun configured_executable () =
    case get_nonempty_env "HOL4_CVC_EXECUTABLE" of
      SOME file => SOME file
    | NONE =>
        (case get_nonempty_env "CVC5" of
          SOME file => SOME file
        | NONE =>
            if command_available "cvc5" then SOME "cvc5" else NONE)

  fun is_configured () = Option.isSome (configured_executable ());

  val error_msg = "CVC not configured: set the HOL4_CVC_EXECUTABLE environment variable to point to the cvc5 executable file.";

  fun mk_CVC_fun name pre cmd_stem post goal =
    case configured_executable () of
      SOME file =>
        SolverSpec.make_solver pre (file ^ cmd_stem) post goal
    | NONE =>
        raise Feedback.mk_HOL_ERR "CVC" name error_msg

  (* cvc5, SMT-LIB file format, no proofs *)
  val CVC_SMT_Oracle =
    mk_CVC_fun "CVC_SMT_Oracle"
      (fn goal =>
        let
          val (goal, _) = SolverSpec.simplify (SmtLib.SIMP_TAC false) goal
          val (_, strings) = SmtLib.goal_to_SmtLib NONE goal
        in
          ((), strings)
        end)
      (* Some options were added due to:
         https://github.com/cvc5/cvc5/issues/10293 *)
      " --macros-quant --macros-quant-mode=all --lang smt "
      (Lib.K is_sat_file)

  (* cvc5, SMT-LIB file format, with Alethe proofs *)
  val CVC_SMT_Prover =
    mk_CVC_fun "CVC_SMT_Prover"
      (fn goal =>
        let
          val (goal, validation) = SolverSpec.simplify (SmtLib.SIMP_TAC true) goal
          val (translation, strings) =
            SmtLib.goal_to_SmtLib_with_get_proof_translation NONE goal
        in
          (((goal, validation), translation), strings)
        end)
      " --produce-proofs --dump-proofs --proof-format-mode=alethe --lang smt "
      (fn ((goal, validation), translation) =>
        fn outfile =>
          let
            val instream = TextIO.openIn outfile
            val result = is_sat_stream instream
          in
            case result of
              SolverSpec.UNSAT NONE =>
              let
                val (ty_dict, tm_dict) =
                  SmtLib.parser_dicts_for_translation translation
                (* parse the Alethe proof *)
                val proof = Alethe_ProofParser.parse_stream
                  (ty_dict, tm_dict) instream
                val _ = TextIO.closeIn instream
                val _ = if List.null proof then
                          raise Feedback.mk_HOL_ERR "CVC" "CVC_SMT_Prover"
                            "cvc5 returned empty proof (may be unsupported)"
                        else ()
                val (As, g) = goal
                val thm =
                  Feedback.quiet_messages Alethe_ProofReplay.check_proof
                    (As, g, proof)
                val thm = Thm.CCONTR g thm
                val thm = validation [thm]
              in
                SolverSpec.UNSAT (SOME thm)
              end
            | _ => (result before TextIO.closeIn instream)
          end)

end
