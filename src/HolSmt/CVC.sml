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

  fun executable_string () =
    case configured_executable () of
      SOME file => file
    | NONE => "<unconfigured>"

  val error_msg = "CVC not configured: set the HOL4_CVC_EXECUTABLE environment variable to point to the cvc5 executable file.";

  fun parse_cvc_version fname =
    let
      val instrm = TextIO.openIn fname
      val text = TextIO.inputAll instrm before TextIO.closeIn instrm
      val tokens = String.tokens Char.isSpace text
    in
      case tokens of
        "cvc5" :: version :: _ => version
      | _ => CPC_Proof.unknown_cvc_version
    end
    handle _ => CPC_Proof.unknown_cvc_version

  val CVCversion =
    case configured_executable () of
      NONE => CPC_Proof.unknown_cvc_version
    | SOME executable =>
        let
          val outfile = OS.FileSys.tmpName ()
          fun work () =
            let val _ = OS.Process.system (executable ^ " --version > " ^ outfile)
            in parse_cvc_version outfile end
          fun finish () = OS.FileSys.remove outfile handle SysErr _ => ()
        in
          Portable.finally finish work ()
        end

  fun version_string () = CVCversion

  fun mk_CVC_fun name pre cmd_stem post goal =
    case configured_executable () of
      SOME file =>
        SolverSpec.make_solver pre (file ^ cmd_stem) post goal
    | NONE =>
      raise Feedback.mk_HOL_ERR "CVC" name error_msg

  fun copy_file source target =
    let
      val input = TextIO.openIn source
      fun work () = Library.write_strings_to_file target [TextIO.inputAll input]
      fun finish () = TextIO.closeIn input
    in
      Portable.finally finish work ()
    end

  (* Keeping these exact temporary artifacts is deliberately opt-in.  It lets
     the CPC corpus runner consume precisely the post-preprocessing SMT-LIB
     query and its corresponding native proof without changing normal solver
     operation. *)
  fun cpc_capture cmd_stem key stage source =
    case get_nonempty_env "HOL4_CVC_CPC_CAPTURE_DIR" of
      NONE => ()
    | SOME directory =>
        let
          val _ = OS.FileSys.mkDir directory handle SysErr _ => ()
          val stem = "cpc-" ^ OS.Path.file key
          val extension = if stage = "input" then ".smt2" else ".out"
          val target = OS.Path.concat (directory, stem ^ extension)
          val metadata = OS.Path.concat (directory, stem ^ ".meta")
          val _ = copy_file source target
          val _ = Library.write_strings_to_file metadata
            ["cvc5_version=", version_string (), "\n",
             "command=", executable_string (), cmd_stem, "<input-file>\n"]
        in () end

  fun mk_CVC_CPC_fun name pre cmd_stem post goal =
    case configured_executable () of
      SOME file =>
        SolverSpec.make_solver_with_capture
          (SOME (cpc_capture cmd_stem)) pre (file ^ cmd_stem) post goal
    | NONE =>
      raise Feedback.mk_HOL_ERR "CVC" name error_msg

  fun hol_err_string holerr =
    Feedback.top_structure_of holerr ^ "." ^
    Feedback.top_function_of holerr ^ ": " ^
    Feedback.message_of holerr
    handle Feedback.HOL_ERR _ => Feedback.message_of holerr

  fun raise_with_context function phase cmd_stem holerr =
    raise Feedback.mk_HOL_ERR "CVC" function
      ("cvc5 " ^ phase ^ " failed\n" ^
       "cvc5 version: " ^ version_string () ^ "\n" ^
       "cvc5 command: " ^ executable_string () ^ cmd_stem ^
       "<input-file> > <output-file>\n" ^
       "underlying HOL_ERR: " ^ hol_err_string holerr)

  fun check_reconstructed_theorem name ((As, g), thm) =
    let
      val allowed_hyps = HOLset.fromList Term.compare As
      val extra_hyps = HOLset.difference (Thm.hypset thm, allowed_hyps)
      val _ = HOLset.isEmpty extra_hyps orelse
        raise Feedback.mk_HOL_ERR "CVC" "check_reconstructed_theorem"
          ("solver '" ^ name ^ "' produced theorem with extra hypotheses")
      val _ = Term.aconv (Thm.concl thm) g orelse
        raise Feedback.mk_HOL_ERR "CVC" "check_reconstructed_theorem"
          ("solver '" ^ name ^ "' produced theorem with an unexpected conclusion")
      val _ = Library.check_oracle_tags name thm
    in thm end

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

  fun proof_pre goal =
    let
      val original_goal = goal
      val (goal, validation) = SolverSpec.simplify (SmtLib.SIMP_TAC true) goal
      val (translation, strings) =
        SmtLib.goal_to_SmtLib_with_get_proof_translation NONE goal
    in
      (((original_goal, goal, validation), translation), strings)
    end

  fun checked_post proof_name cmd_stem parse replay
      ((original_goal, goal, validation), translation) outfile =
    let
      val instream = TextIO.openIn outfile
      val result = is_sat_stream instream
    in
      case result of
        SolverSpec.UNSAT NONE =>
        let
          val (ty_dict, tm_dict) = SmtLib.parser_dicts_for_translation translation
          val proof = parse (ty_dict, tm_dict) instream
            handle Feedback.HOL_ERR holerr =>
              (TextIO.closeIn instream;
               raise_with_context proof_name "proof parse" cmd_stem holerr)
          val _ = TextIO.closeIn instream
          val (As, g) = goal
          val thm = replay (As, g, proof)
            handle Feedback.HOL_ERR holerr =>
              raise_with_context proof_name "proof replay" cmd_stem holerr
          val thm = Thm.CCONTR g thm
          val thm = validation [thm]
          val thm = check_reconstructed_theorem proof_name (original_goal, thm)
        in SolverSpec.UNSAT (SOME thm) end
      | _ => (result before TextIO.closeIn instream)
    end

  (* CPC is the sole checked cvc5 proof format. *)
  val cpc_proof_cmd =
    " --produce-proofs --dump-proofs --proof-format-mode=cpc " ^
    "--proof-granularity=dsl-rewrite --lang smt "

  val CVC_SMT_CPC_Prover =
    mk_CVC_CPC_fun "CVC_SMT_CPC_Prover" proof_pre cpc_proof_cmd
      (checked_post "CVC_SMT_CPC_Prover" cpc_proof_cmd
        (fn dicts => CPC_ProofParser.parse_stream_with_version dicts
          (version_string ()))
        CPC_ProofReplay.check_proof)

  (* cvc5, SMT-LIB file format, checked proofs. *)
  val CVC_SMT_Prover = CVC_SMT_CPC_Prover
end
