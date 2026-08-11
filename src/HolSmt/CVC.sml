(* Functions to invoke the cvc5 SMT solver *)

structure CVC = struct

  (* returns SAT if cvc5 reported "sat", UNSAT if cvc5 reported "unsat" *)
  (* cvc5 diagnoses some errors without giving up -- an unsupported command is
     reported and the verdict still follows -- so an `(error ...)` line must
     not abort the scan the way it does for Z3.  Remember the first one and
     use it as the reason when the stream ends with no verdict at all, rather
     than returning a bare UNKNOWN that discards what cvc5 said. *)
  fun is_sat_stream_with_error_and_consumed first_error consumed instream =
    case TextIO.inputLine instream of
      NONE => (SolverSpec.UNKNOWN first_error, consumed)
    | SOME line =>
        let
          val consumed = consumed + String.size line
          val trimmed = Substring.string
            (Substring.dropl Char.isSpace (Substring.full line))
        in
          if String.isPrefix "(error" trimmed then
            is_sat_stream_with_error_and_consumed
              (case first_error of NONE => SOME line | _ => first_error)
              consumed instream
          else
            case String.tokens Char.isSpace line of
              ["sat"] => (SolverSpec.SAT NONE, consumed)
            | ["unsat"] => (SolverSpec.UNSAT NONE, consumed)
            | _ => is_sat_stream_with_error_and_consumed first_error
                consumed instream
        end

  fun is_sat_stream_with_consumed instream =
    is_sat_stream_with_error_and_consumed NONE 0 instream

  fun is_sat_stream instream = Lib.fst (is_sat_stream_with_consumed instream)

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

  fun is_version_token token =
    token <> "" andalso Char.isDigit (String.sub (token, 0))

  (* cvc5 announces itself either as `cvc5 1.3.4 [git ...]` or, in older
     releases, as `This is cvc5 version 1.1.2`.  Anchoring at the first token
     recognizes only the former and reports every other build as
     `unknown_cvc_version`, which costs the version its say in which measured
     dialect `CPC_Proof.resolve_version` replays it under.  Look for the
     `cvc5` marker anywhere instead, and take the version-shaped token that
     follows it. *)
  fun parse_cvc_version fname =
    let
      val instrm = TextIO.openIn fname
      val text = TextIO.inputAll instrm before TextIO.closeIn instrm
      fun version_after ("version" :: rest) = version_after rest
        | version_after (token :: _) =
            if is_version_token token then SOME token else NONE
        | version_after [] = NONE
      fun scan [] = NONE
        | scan ("cvc5" :: rest) =
            (case version_after rest of
               SOME version => SOME version
             | NONE => scan rest)
        | scan (_ :: rest) = scan rest
    in
      case scan (String.tokens Char.isSpace text) of
        SOME version => version
      | NONE => CPC_Proof.unknown_cvc_version
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

  (* Ask cvc5 to limit itself, so that `SolverSpec`'s wall timeout stays a
     backstop rather than the only mechanism.  `--tlimit-per` bounds each
     query and still reports `unknown`; `--tlimit` aborts without printing a
     verdict, which is indistinguishable from a crash. *)
  fun timeout_option () =
    " --tlimit-per=" ^
    Int.toString (SolverSpec.configured_timeout_milliseconds ())

  fun with_timeout_option cmd_stem = timeout_option () ^ cmd_stem

  fun mk_CVC_fun name pre cmd_stem post goal =
    case configured_executable () of
      SOME file =>
        SolverSpec.make_solver pre (file ^ with_timeout_option cmd_stem) post
          goal
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
             "command=", cmd_stem, "<input-file>\n"]
        in () end

  fun mk_CVC_CPC_fun name pre command_stem post goal =
    case configured_executable () of
      SOME file =>
        SolverSpec.make_solver_with_capture_and_command
          (SOME cpc_capture) pre
          (fn data => file ^ with_timeout_option (command_stem data)) post goal
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

  (* cvc5 1.3.4 treats a lambda binder as a quantifier for logic checking,
     even though SMT-LIB's QF classification only excludes quantified terms.
     Keep the compatibility widening at the cvc5 boundary: the shared logic
     inference and every other solver continue to receive the precise
     HO_QF_* logic. *)
  fun cvc_logic_policy
      ({features = SmtLib.LogicFeatures {higher_order, ...}, inferred_logic,
        reason} : {features : SmtLib.logic_features,
                   inferred_logic : string, reason : string}) =
    if higher_order andalso String.isPrefix "HO_QF_" inferred_logic then
      SOME {logic = "HO_" ^
          String.extract (inferred_logic, String.size "HO_QF_", NONE),
        reason = reason ^
          "; cvc5 lambda/HO_QF compatibility widening"}
    else NONE

  fun cvc_translation get_proof goal =
    SmtLib.goal_to_SmtLib_translation_for_solver
      {policy = cvc_logic_policy, dialect = SmtLib.Standard27,
       apply_operator = SmtLib.ApplyAt, get_proof = get_proof,
       target = SOME {solver = "cvc5", version = SOME (version_string ())}}
      goal

  fun goal_to_SmtLib_translation goal = cvc_translation false goal

  fun goal_to_SmtLib_with_get_proof_translation goal =
    cvc_translation true goal

  (* cvc5, SMT-LIB file format, no proofs *)
  val CVC_SMT_Oracle =
    mk_CVC_fun "CVC_SMT_Oracle"
      (fn goal =>
        let
          val (goal, _) = SolverSpec.simplify (SmtLib.SIMP_TAC false) goal
          val (_, strings) = goal_to_SmtLib_translation goal
        in
          ((), strings)
        end)
      (* Some options were added due to:
         https://github.com/cvc5/cvc5/issues/10293 *)
      (" --macros-quant --macros-quant-mode=all --fp-exp --sets-exp " ^
       "--arrays-exp --lang smt ")
      (Lib.K is_sat_file)

  fun proof_pre goal =
    let
      val original_goal = goal
      val (goal, validation) = SolverSpec.simplify (SmtLib.SIMP_TAC true) goal
      val (translation, strings) =
        goal_to_SmtLib_with_get_proof_translation goal
      val arrays_exp = List.exists
        (fn text => String.isSubstring "(as const (Array" text) strings
    in
      (((original_goal, goal, validation), (translation, arrays_exp)), strings)
    end

  fun checked_post proof_name command_stem parse replay
      (data as ((original_goal, goal, validation), (translation, _))) outfile =
    let
      val instream = TextIO.openIn outfile
      val (result, proof_start) = is_sat_stream_with_consumed instream
    in
      case result of
        SolverSpec.UNSAT NONE =>
        let
          val (ty_dict, tm_dict) = SmtLib.parser_dicts_for_translation translation
          val proof =
            SmtResource.with_proof_size_gate "cvc5-cpc-proof-text"
              outfile proof_start instream (parse (ty_dict, tm_dict))
            handle Feedback.HOL_ERR holerr =>
              (TextIO.closeIn instream;
               if SmtResource.is_resource_gate holerr then
                 raise Feedback.HOL_ERR holerr
               else
                 raise_with_context proof_name "proof parse" (command_stem data) holerr)
          val _ = TextIO.closeIn instream
          val (As, g) = goal
          val thm = replay (As, g, proof)
            handle Feedback.HOL_ERR holerr =>
              if SmtResource.is_resource_gate holerr then
                raise Feedback.HOL_ERR holerr
              else
                raise_with_context proof_name "proof replay" (command_stem data) holerr
          val thm = Thm.CCONTR g thm
          val thm = validation [thm]
          val thm = check_reconstructed_theorem proof_name (original_goal, thm)
        in SolverSpec.UNSAT (SOME thm) end
      | _ => (result before TextIO.closeIn instream)
    end

  (* CPC is the sole checked cvc5 proof format. *)
  val cpc_proof_cmd =
    " --produce-proofs --dump-proofs --proof-format-mode=cpc " ^
    "--proof-granularity=dsl-rewrite --fp-exp --lang smt "

  fun cpc_command (_, (_, arrays_exp)) =
    if arrays_exp then
      cpc_proof_cmd ^ "--arrays-exp "
    else
      cpc_proof_cmd

  val CVC_SMT_CPC_Prover =
    mk_CVC_CPC_fun "CVC_SMT_CPC_Prover" proof_pre cpc_command
      (checked_post "CVC_SMT_CPC_Prover" cpc_command
        (fn dicts => CPC_ProofParser.parse_stream_with_version dicts
          (version_string ()))
        CPC_ProofReplay.check_proof)

  (* cvc5, SMT-LIB file format, checked proofs. *)
  val CVC_SMT_Prover = CVC_SMT_CPC_Prover
end
