(* Copyright (c) 2009-2012 Tjark Weber. All rights reserved. *)

(* Functions to invoke the Z3 SMT solver *)

structure Z3 = struct

  (* Returns Z3's result and the number of bytes consumed before proof text.
     Z3's status lines are ASCII, so String.size is also their byte count. *)
  fun is_sat_stream_with_consumed instream =
    let
      fun scan consumed =
        case TextIO.inputLine instream of
          NONE => (SolverSpec.UNKNOWN NONE, consumed)
        | SOME line =>
            let
              val consumed = consumed + String.size line
              val trimmed = Substring.string
                (Substring.dropl Char.isSpace (Substring.full line))
            in
              if String.isPrefix "(error" trimmed then
                (SolverSpec.UNKNOWN (SOME line), consumed)
              else
                case String.tokens Char.isSpace line of
                  ["sat"] => (SolverSpec.SAT NONE, consumed)
                | ["unsat"] => (SolverSpec.UNSAT NONE, consumed)
                | ["unknown"] => (SolverSpec.UNKNOWN NONE, consumed)
                | _ => scan consumed
            end
    in
      scan 0
    end

  (* returns SAT if Z3 reported "sat", UNSAT if Z3 reported "unsat" *)
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
    case get_nonempty_env "HOL4_Z3_EXECUTABLE" of
      SOME file => SOME file
    | NONE =>
        (case get_nonempty_env "Z3" of
          SOME file => SOME file
        | NONE => if command_available "z3" then SOME "z3" else NONE)

  fun is_configured () = Option.isSome (configured_executable ());

  val error_msg =
    "Z3 not configured: install z3 on PATH or set the " ^
    "HOL4_Z3_EXECUTABLE environment variable to point to the Z3 executable.";

  fun executable_string () =
    case configured_executable () of
      SOME file => file
    | NONE => "<unconfigured>"

  fun timeout_option () =
    " -t:" ^ Int.toString (SolverSpec.configured_timeout_milliseconds ())

  fun with_timeout_option cmd_stem =
    timeout_option () ^ cmd_stem

  val max_capture_file_bytes = 64 * 1024 * 1024
  val max_capture_invocation_bytes = 96 * 1024 * 1024
  val max_capture_time = Time.fromSeconds 15

  fun capture_file_bytes source =
    Position.toInt (OS.FileSys.fileSize source)
    handle Overflow => max_capture_file_bytes + 1

  fun copy_file_bounded_memory source target =
    let
      val input = TextIO.openIn source
      val output = TextIO.openOut target
      fun copy () =
        case TextIO.inputN (input, 65536) of
          "" => ()
        | chunk => (TextIO.output (output, chunk); copy ())
      fun finish () =
        let
          val input_exception =
            (TextIO.closeIn input; NONE) handle exn => SOME exn
          fun close_output () = TextIO.closeOut output
        in
          case input_exception of
            NONE =>
              (close_output () handle exn =>
                SmtResource.resolve_diagnostic_exception exn
                  (fn () => ()) (fn _ => ()))
          | SOME exn =>
              SmtResource.resolve_diagnostic_exception exn close_output
                (fn _ => ())
        end
    in
      case Exn.capture copy () of
        Exn.Res result => (finish (); result)
      | Exn.Exn exn =>
          SmtResource.resolve_diagnostic_exception exn finish
            (fn original => raise original)
    end

  (* Exact solver artifacts are retained only when this E0 hook is enabled.
     Streaming the copy avoids allocating a proof-sized ML string.  A single
     invocation-local closure selects unique, non-overwriting targets and
     bounds file bytes, aggregate bytes, and copy time.  Refused or failed
     observation is diagnostic only and cannot replace a solver result. *)
  fun z3_capture_for_directory directory =
    let
      val targets = ref ([] : (string * string) list)
      val captured_bytes = ref 0
      fun path stem extension =
        OS.Path.concat (directory, stem ^ extension)
      fun occupied stem = List.exists
        (fn extension => OS.FileSys.access (path stem extension, []))
        [".smt2", ".out", ".meta"]
      fun unique_stem base =
        let
          fun choose 0 =
                if occupied base then choose 1 else base
            | choose suffix =
                let val candidate = base ^ "-" ^ Int.toString suffix
                in
                  if occupied candidate then choose (suffix + 1)
                  else candidate
                end
        in
          choose 0
        end
      fun target_for key =
        case List.find (fn (saved_key, _) => saved_key = key) (!targets) of
          SOME (_, stem) => stem
        | NONE =>
            let
              val stem = unique_stem ("z3-" ^ OS.Path.file key)
              val _ = targets := (key, stem) :: !targets
            in
              stem
            end
      fun refuse message = SmtResource.emit_e0
        ("capture=refused reason=" ^ SmtResource.bounded_text 240 message)
      fun capture cmd_stem key stage source =
        let
          val _ = OS.FileSys.mkDir directory
            handle SysErr _ =>
              if OS.FileSys.isDir directory then ()
              else raise Fail "capture directory is unavailable"
          val stem = target_for key
          val extension = if stage = "input" then ".smt2" else ".out"
          val target = path stem extension
          val metadata = path stem ".meta"
          val bytes = capture_file_bytes source
          val _ =
            if bytes > max_capture_file_bytes then
              raise Fail ("file exceeds " ^
                Int.toString max_capture_file_bytes ^ " bytes")
            else if !captured_bytes > max_capture_invocation_bytes - bytes then
              raise Fail ("invocation exceeds " ^
                Int.toString max_capture_invocation_bytes ^ " bytes")
            else if OS.FileSys.access (target, []) then
              raise Fail "capture target already exists"
            else ()
          fun remove_partial () =
            OS.FileSys.remove target handle SysErr _ => ()
          val _ =
            (Timeout.apply max_capture_time
               (fn () => copy_file_bounded_memory source target) ()
             handle exn =>
               SmtResource.resolve_diagnostic_exception exn remove_partial
                 (fn original => raise original))
          val _ = captured_bytes := !captured_bytes + bytes
          val _ =
            if stage <> "input" orelse OS.FileSys.access (metadata, []) then ()
            else
              Library.write_strings_to_file metadata
                ["command=", cmd_stem, "<input-file> > <output-file>\n",
                 "capture_key=", key, "\n",
                 "max_file_bytes=", Int.toString max_capture_file_bytes,
                 "\nmax_invocation_bytes=",
                 Int.toString max_capture_invocation_bytes,
                 "\nmax_copy_seconds=",
                 LargeInt.toString (Time.toSeconds max_capture_time), "\n"]
        in
          ()
        end handle exn =>
          SmtResource.resolve_diagnostic_exception exn
            (fn () =>
              (SmtResource.invoke_e0_diagnostic_hook "z3-capture-refusal";
               refuse (General.exnMessage exn))) (fn _ => ())
    in
      capture
    end

  fun z3_capture_for_invocation () =
    case get_nonempty_env "HOL4_Z3_PROOF_CAPTURE_DIR" of
      NONE => NONE
    | SOME directory => SOME (z3_capture_for_directory directory)

  fun mk_Z3_fun name pre cmd_stem post goal =
    case configured_executable () of
      SOME file =>
        SolverSpec.make_solver_with_capture_and_command
          (z3_capture_for_invocation ()) pre
          (fn _ => file ^ with_timeout_option cmd_stem) post goal
    | NONE =>
        raise Feedback.mk_HOL_ERR "Z3" name error_msg

  (* e.g. "Z3 version 4.5.0 - 64 bit" *)
  fun parse_Z3_version fname =
    let
      val instrm = TextIO.openIn fname
      val s = TextIO.inputAll instrm before TextIO.closeIn instrm
      val tokens = String.tokens Char.isSpace s
    in
      case tokens of
        "Z3" :: "version" :: version :: _ => version
      | _ => "0"
    end
    handle _ => "0"

  val Z3version =
      case configured_executable () of
          NONE => "0"
        | SOME p =>
          let
            val outfile = OS.FileSys.tmpName()
            fun work () = let
              val _ = OS.Process.system (p ^ " -version > " ^ outfile)
            in
              parse_Z3_version outfile
            end
            fun finish () =
                OS.FileSys.remove outfile handle SysErr _ => ()
          in
            Portable.finally finish work ()
          end

  fun configured_version () =
    if Z3version = "0" then NONE else SOME Z3version

  fun version_string () =
    case configured_version () of
      SOME version => version
    | NONE => "<undiscoverable>"

  fun major_version version =
    case String.tokens (fn c => c = #".") version of
      major :: _ => SOME major
    | [] => NONE

  val z3_414_affected_array_logics = [
    "ALIRA", "ANIA", "ANIRA",
    "AUFDTLIA", "AUFDTLIRA", "AUFDTNIRA", "AUFBVDT"
  ]

  fun decimal_component s =
    s <> "" andalso List.all Char.isDigit (String.explode s)

  fun is_z3_414_version version =
    case String.tokens (fn c => c = #".") version of
      [major, minor, patch] =>
        major = "4" andalso minor = "14" andalso decimal_component patch
    | _ => false

  (* Z3 4.14.1 rejects Array under these seven non-QF logic names with
     "unknown sort 'Array'".  ALL is a sound superset and the unchanged
     queries passed direct probes on every supported Z3 anchor.  This policy
     belongs at the Z3 boundary: the inferred logics remain valid SMT-LIB and
     are accepted by the other supported solvers and Z3 minor versions. *)
  fun z3_414_logic_policy version
      ({features = SmtLib.LogicFeatures {arrays, ...}, inferred_logic,
        reason} : {features : SmtLib.logic_features,
                   inferred_logic : string, reason : string}) =
    if (case version of SOME v => is_z3_414_version v | NONE => false) andalso
       arrays andalso
       List.exists (fn logic => logic = inferred_logic)
         z3_414_affected_array_logics
    then
      SOME {logic = "ALL",
        reason = reason ^
          "; Z3 4.14.x array-logic compatibility widening to ALL"}
    else
      NONE

  fun z3_translation get_proof version =
    SmtLib.goal_to_SmtLib_translation_for_solver
      {policy = z3_414_logic_policy version, dialect = SmtLib.Z3LambdaArray,
       apply_operator = SmtLib.ApplyUnderscore, get_proof = get_proof,
       target = SOME {solver = "Z3", version = version}}

  fun goal_to_SmtLib_translation_for_version version =
    z3_translation false version

  val plain_check_sat_command = "(check-sat)\n"
  val quantified_proof_check_sat_command = "(check-sat-using smt)\n"

  (* This policy is intentionally a function of translation metadata, not of
     rendered SMT-LIB text.  LogicFeatures combines a structural scan of the
     translated HOL terms with exact provenance from generated-forall emitters,
     without inspecting comments, symbols, or String literals. *)
  fun checked_check_sat_command translation =
    if SmtLib.translation_has_quantifiers translation then
      quantified_proof_check_sat_command
    else
      plain_check_sat_command

  fun goal_to_SmtLib_with_get_proof_translation_for_version version goal =
    let
      val (translation, strings) = z3_translation true version goal
      val selected_check_sat = checked_check_sat_command translation
      fun select_check_sat command =
        if command = plain_check_sat_command then selected_check_sat
        else command
    in
      (translation, List.map select_check_sat strings)
    end

  (* Z3 (Linux/Unix), SMT-LIB file format, no proofs *)
  val Z3_SMT_Oracle =
    mk_Z3_fun "Z3_SMT_Oracle"
      (fn goal =>
        let
          val (goal, _) = SolverSpec.simplify (SmtLib.Z3_SIMP_TAC false) goal
          val (_, strings) =
            goal_to_SmtLib_translation_for_version (configured_version ()) goal
        in
          ((), strings)
        end)
      " -smt2 -file:"
      (Lib.K is_sat_file)

  (* Only Z3 4.x is supported: legacy 2.x/3.x proof support (PROOF_MODE) has
     been removed, and those binaries reject the 4.x command line outright.
     Callers use this to skip tests rather than fail them, so a version that
     cannot be discovered counts as unsupported. *)
  fun is_v4 () =
    case configured_version () of
      SOME version => major_version version = SOME "4"
    | NONE => false

  fun is_v4_configured () = is_configured () andalso is_v4 ()

  (* disable `pp.simplify_implies` so that Z3's AST pretty-printer doesn't
     mangle `asserted` proof rules, which would cause a mismatch against the
     goal's assumption list *)
  val proof_option = " proof=true pp.simplify_implies=false"

  val proof_cmd_stem = proof_option ^ " -smt2 -file:"

  fun current_proof_cmd_stem () = with_timeout_option proof_cmd_stem

  fun command_string cmd_stem =
    executable_string () ^ cmd_stem ^ "<input-file> > <output-file>"

  fun hol_err_string holerr =
    Feedback.top_structure_of holerr ^ "." ^
    Feedback.top_function_of holerr ^ ": " ^
    Feedback.message_of holerr
    handle Feedback.HOL_ERR _ => Feedback.message_of holerr

  fun raise_with_context function phase cmd_stem holerr =
    raise Feedback.mk_HOL_ERR "Z3" function
      ("Z3 " ^ phase ^ " failed\n" ^
       "Z3 version: " ^ version_string () ^ "\n" ^
       "Z3 command: " ^ command_string cmd_stem ^ "\n" ^
       "underlying HOL_ERR: " ^ hol_err_string holerr)

  val unsupported_proof_symbol_diagnostic =
    "Z3_PROOF_SYMBOL_UNSUPPORTED"

  fun is_unknown_proof_symbol_error holerr =
    Feedback.top_structure_of holerr = "SmtLib_Parser" andalso
    Feedback.top_function_of holerr =
      SmtLib_Parser.unknown_symbol_origin
    handle Feedback.HOL_ERR _ => false

  (* Classify only the parser's exact no-dictionary-entry boundary.  Builder
     errors for registered proof symbols, resource gates, and every other
     parser failure retain their original classification and context. *)
  fun classify_proof_parse_error holerr =
    if is_unknown_proof_symbol_error holerr then
      raise Feedback.mk_HOL_ERR "Z3" "classify_proof_parse_error"
        (unsupported_proof_symbol_diagnostic ^ ": " ^
         Feedback.message_of holerr)
    else
      raise Feedback.HOL_ERR holerr

  fun classify_proof_parse_error_for_test parse =
    parse ()
    handle Feedback.HOL_ERR holerr => classify_proof_parse_error holerr

  fun capture_diagnostic_precedence_for_test original =
    SmtResource.resolve_diagnostic_exception original
      (fn () => SmtResource.invoke_e0_diagnostic_hook
        "z3-capture-refusal") (fn _ => ())

  fun close_diagnostic_precedence_for_test original =
    SmtResource.resolve_diagnostic_exception original
      (fn () => ()) (fn _ => ())

  fun check_reconstructed_theorem name ((As, g), thm) =
    let
      fun terms_to_string terms =
        "[" ^ String.concatWith ", " (List.map Library.term_to_string terms) ^
        "]"
      val allowed_hyps = HOLset.fromList Term.compare As
      val extra_hyps = HOLset.difference (Thm.hypset thm, allowed_hyps)
      val () =
        if HOLset.isEmpty extra_hyps then
          ()
        else
          raise Feedback.mk_HOL_ERR "Z3" "check_reconstructed_theorem"
            ("solver '" ^ name ^ "' produced theorem with extra hypotheses; " ^
             "unexpected hypotheses: " ^
             terms_to_string (HOLset.listItems extra_hyps) ^
             "; allowed hypotheses: " ^
             terms_to_string (HOLset.listItems allowed_hyps) ^
             "; theorem: " ^
             Library.thm_to_string thm)
      val () =
        if Term.aconv (Thm.concl thm) g then
          ()
        else
          raise Feedback.mk_HOL_ERR "Z3" "check_reconstructed_theorem"
            ("solver '" ^ name ^ "' produced theorem with conclusion " ^
             Library.term_to_string (Thm.concl thm) ^
             ", expected parsed assertion-negation goal " ^
             Library.term_to_string g)
      val () = Library.check_oracle_tags "HolSmtLib" name thm
    in
      thm
    end

  (* Z3 (Linux/Unix), SMT-LIB file format, with proofs *)
  val Z3_SMT_Prover =
    mk_Z3_fun "Z3_SMT_Prover"
      (SmtResource.profile_phase "z3/input-generation" (fn goal =>
        let
          val original_goal = goal
          val (goal, validation) = SolverSpec.simplify
            (SmtLib.Z3_SIMP_TAC true) goal
          val (translation, strings) =
            goal_to_SmtLib_with_get_proof_translation_for_version
              (configured_version ()) goal
        in
          (((original_goal, goal, validation), translation), strings)
        end))
      proof_cmd_stem
      (fn ((original_goal, goal, validation), translation) =>
        fn outfile =>
          let
            val instream = TextIO.openIn outfile
            fun close () =
              TextIO.closeIn instream
              handle exn =>
                SmtResource.resolve_diagnostic_exception exn
                  (fn () => ()) (fn _ => ())
            fun contextualize_parse exn =
              if SmtResource.terminal_diagnostic_exception exn then raise exn
              else
                case exn of
                  Feedback.HOL_ERR holerr =>
                    (classify_proof_parse_error holerr
                     handle Feedback.HOL_ERR classified =>
                       raise_with_context "Z3_SMT_Prover" "proof parse"
                         (current_proof_cmd_stem ()) classified)
                | _ =>
                    raise Feedback.mk_HOL_ERR "Z3" "Z3_SMT_Prover"
                      ("Z3 proof parse failed\n" ^
                       "Z3 version: " ^ version_string () ^ "\n" ^
                       "Z3 command: " ^
                       command_string (current_proof_cmd_stem ()) ^ "\n" ^
                       "underlying exception: " ^ General.exnMessage exn)
            fun parse_proof proof_start =
              (let
                 (* Reject oversized proof text before the untrusted proof
                    parser reads even its first token. *)
                 val proof_bytes = SmtResource.remaining_file_bytes
                   outfile proof_start
                 val _ = SmtResource.profile_phase "z3/byte-admission"
                   (SmtResource.check_proof_size "z3-proof-text")
                   proof_bytes
                 val _ = SmtResource.emit_e0
                   ("proof bytes=" ^ Int.toString proof_bytes)
                 val proof =
                   SmtResource.profile_phase "z3/parse+graph-construction"
                     (Z3_ProofParser.parse_stream_with_version
                       (SmtLib.parser_dicts_for_solver_translation
                         "Z3" translation) (version_string ())) instream
                 (* Graph metrics are observation only.  Keep their traversal
                    entirely out of the ordinary checked path. *)
                 val _ =
                   if not (SmtResource.e0_enabled ()) then ()
                   else
                     ((let val graph = Z3_Proof.proof_graph_metrics proof
                       in
                         SmtResource.emit_e0
                          ("proof_graph outer_nodes=" ^
                            Int.toString (#nodes graph) ^
                            " outer_direct_edges=" ^
                            Int.toString (#edges graph) ^ " variables=" ^
                            Int.toString (#variables graph) ^
                            " bit_decompositions=" ^
                            Int.toString (#bit_decompositions graph))
                       end) handle exn =>
                         SmtResource.resolve_diagnostic_exception exn
                           (fn () => ()) (fn _ => ()))
               in
                 proof
               end handle exn => contextualize_parse exn)
            fun work () =
              let
                val (result, proof_start) =
                  is_sat_stream_with_consumed instream
              in
                case result of
                  SolverSpec.UNSAT NONE =>
                  let
                    val (As, g) = goal
                    val proof = parse_proof proof_start
                    val thm = SmtResource.profile_phase "z3/replay"
                      (Z3_ProofReplay.check_proof_with_definitions
                        (SmtLib.translation_definitions translation))
                      (As, g, proof)
                      handle Feedback.HOL_ERR holerr =>
                        if SmtResource.is_resource_gate holerr then
                          raise Feedback.HOL_ERR holerr
                        else
                          raise_with_context "Z3_SMT_Prover" "proof replay"
                            (current_proof_cmd_stem ()) holerr
                    val thm = SmtResource.profile_phase "z3/final-ccontr"
                      (fn thm => Thm.CCONTR g thm) thm
                    val thm = SmtResource.profile_phase "z3/final-validation"
                      validation [thm]
                    val thm = SmtResource.profile_phase "z3/final-checks"
                      (check_reconstructed_theorem "Z3_SMT_Prover")
                      (original_goal, thm)
                  in
                    SolverSpec.UNSAT (SOME thm)
                  end
                | _ => result
              end
            val outcome = Exn.capture work ()
          in
            case outcome of
              Exn.Res result => (close (); result)
            | Exn.Exn exn =>
                SmtResource.resolve_diagnostic_exception exn close
                  (fn original => raise original)
          end)

end
