(* Functions to invoke the cvc5 SMT solver *)

structure CVC = struct


  (* Nonselected caller seam: children enter before any SolverSpec pre.
     Selection needs a reviewed application GP callback and cursor path. *)
  fun CVC_Children_First_Begin request children =
    SmtCheckedGraph.begin_children_first_boolean_application
      request children
  fun CVC_Children_First_Prepare handoff discover exact_goal =
    SmtCheckedGraph.prepare_children_first_with_policy
      handoff discover exact_goal
  val CVC_Children_First_Close =
    SmtCheckedGraph.close_children_first_handoff
  (* CVC initiates the one A/I birth before any SolverSpec pre. I issues
     an opaque one-use Ready token; CheckedGraph consumes its exact Source,
     OriginalPortfolio and A-born goal on the same Work meter. *)
  fun CVC_Children_First_Adopt_Caller request children =
    let
      (* Fixed identity GP over this exact A OriginalPortfolio. No
         caller-supplied theorem, conversion, Source or Work enters. *)
      fun discover work native sources =
        SmtReplayInvocationWork.with_step work (fn () =>
          let
            val held = SmtReplayInvocationWork.original_sources work
            val _ = if Portable.pointer_eq (held,sources) then () else
              raise Feedback.mk_HOL_ERR "CVC" "discover_identity"
                "foreign A original Source"
            val _ = SmtReplayNativeContract.validate_for work native
            val {assumptions,denied} =
              SmtLib_GraphSourcePortfolio.originals_with_policy work
            val portfolio =
              SmtLib_GraphSourcePortfolio.validate_portfolio_with_policy work
                {assumptions=assumptions,
                 goal= #node (SmtReplaySource.goal_source sources),
                 denied=denied}
            val checked =
              SmtLib_GraphPreprocess.from_portfolio_with_policy work portfolio
            val _ = SmtReplayNativeContract.validate_for work native
          in checked end)
      val _ = SmtCheckedGraph.validate_caller_owned_children_first_request
        request
      val token =
        SmtReplayInvocationWork.begin_ready_checked_owned_boolean_application
          (#owned request) children
      fun prepare () =
        let
          val {goal,handoff} =
            SmtCheckedGraph.adopt_caller_owned_children_first
              (#native request) token
          val {work,invocation} =
            SmtCheckedGraph.prepare_children_first_with_policy
              handoff discover goal
          val closed = ref false
          fun close () =
            if !closed then () else
              (closed := true;
               SmtCheckedGraph.close_original_with_policy
                 work invocation)
        in {goal=goal,work=work,invocation=invocation,
            close=close} end
    in prepare () handle primary =>
      ((SmtReplayInvocationWork.close_ready_checked_owned_boolean_application
          token handle _ => ());
       raise primary) end
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

  val error_msg =
    "CVC not configured: install cvc5 on PATH or set the " ^
    "HOL4_CVC_EXECUTABLE environment variable to point to the cvc5 " ^
    "executable.";

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
       "cvc5 command: " ^ executable_string () ^ with_timeout_option cmd_stem ^
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
      val _ = Library.check_oracle_tags "HolSmtLib" name thm
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
          val (goal, _) = SolverSpec.simplify (SmtLib.CVC_SIMP_TAC false) goal
          val (_, strings) = goal_to_SmtLib_translation goal
        in
          ((), strings)
        end)
      (* Some options were added due to:
         https://github.com/cvc5/cvc5/issues/10293 *)
      (" --quiet --macros-quant --macros-quant-mode=all " ^
       "--fp-exp --sets-exp " ^
       "--arrays-exp --lang smt ")
      (Lib.K is_sat_file)

  fun proof_pre goal =
    let
      val original_goal = goal
      (* CVC_SIMP_TAC removes these transfer assumptions before translation,
         but CPC's symbolic cardinality rules need them during reconstruction.
         They remain assumptions of the original goal, so retain them only as
         replay context. *)
      val finite_hyps = List.mapPartial (fn hyp =>
        if Lib.can pred_setSyntax.dest_finite hyp then SOME hyp else NONE)
        (Lib.fst original_goal)
      val (goal, validation) = SolverSpec.simplify (SmtLib.CVC_SIMP_TAC true) goal
      val (translation, strings) =
        goal_to_SmtLib_with_get_proof_translation goal
      val arrays_exp = List.exists
        (fn text => String.isSubstring "(as const (Array" text) strings
    in
      (((original_goal, goal, validation, finite_hyps),
        (translation, arrays_exp)), strings)
    end

  (* CPC replay calls Metis and Grobner internally.  Their default interactive
     output is useful when those tools are invoked directly, but it makes a
     routine CVC_TAC proof unnecessarily noisy.  Keep all backend chatter
     suppressed inside the checked solver boundary. *)
  fun quiet_replay replay input =
    Lib.with_flag (Grobner.verbose, false)
      (Feedback.trace ("metis", 0) replay) input

  fun quiet f =
    Feedback.trace ("metis", 0)
      (fn () =>
        Feedback.quiet_messages
          (fn () => Feedback.quiet_warnings (fn () => f ()) ()) ()) ()

  fun checked_post proof_name command_stem parse replay
      (data as ((original_goal, goal, validation, finite_hyps),
        (translation, _))) outfile =
    let
      val instream = TextIO.openIn outfile
      val (result, proof_start) = is_sat_stream_with_consumed instream
    in
      case result of
        SolverSpec.UNSAT NONE =>
        let
          val (ty_dict, tm_dict) = quiet (fn () =>
            SmtLib.parser_dicts_for_solver_translation "cvc5" translation)
          val _ = if !Library.trace > 1 then
              Feedback.HOL_MESG "HolSmtLib: parsing CVC proof"
            else ()
          val proof = quiet (fn () =>
            SmtResource.with_proof_size_gate "cvc5-cpc-proof-text"
              outfile proof_start instream
              (SmtResource.profile_phase "cvc/cpc-parse"
                (parse (ty_dict, tm_dict))))
            handle Feedback.HOL_ERR holerr =>
              (TextIO.closeIn instream;
               if SmtResource.is_resource_gate holerr then
                 raise Feedback.HOL_ERR holerr
               else
                 raise_with_context proof_name "proof parse"
                   (command_stem data) holerr)
          val _ = TextIO.closeIn instream
          val (As, g) = goal
          val _ = if !Library.trace > 1 then
              Feedback.HOL_MESG "HolSmtLib: checking CVC proof"
            else ()
          val replay_checked = fn () =>
            SmtResource.profile_phase "cvc/cpc-replay"
              (quiet_replay
                (replay (SmtLib.translation_definitions translation)))
              (finite_hyps @ As, g, proof)
          val trace_replay =
            OS.Process.getEnv "HOL4_CPC_REPLAY_TRACE" = SOME "1" orelse
            OS.Process.getEnv "HOL4_CPC_REPLAY_TRACE" = SOME "full"
          val thm =
            if trace_replay then replay_checked ()
            else quiet replay_checked
            handle Feedback.HOL_ERR holerr =>
              if SmtResource.is_resource_gate holerr then
                raise Feedback.HOL_ERR holerr
              else
                raise_with_context proof_name "proof replay"
                  (command_stem data) holerr
          val thm = quiet (fn () => Thm.CCONTR g thm)
          val thm = quiet (fn () => validation [thm])
          val thm = quiet (fn () =>
            check_reconstructed_theorem proof_name (original_goal, thm))
        in SolverSpec.UNSAT (SOME thm) end
      | _ => (result before TextIO.closeIn instream)
    end

  (* CPC is the sole checked cvc5 proof format. *)
  val cpc_proof_cmd =
    " --quiet --produce-proofs --proof-format-mode=cpc " ^
    "--proof-granularity=dsl-rewrite --fp-exp --sets-exp --lang smt "

  fun cpc_command (_, (_, arrays_exp)) =
    cpc_proof_cmd ^
    (if arrays_exp then "--arrays-exp " else "")

  val CVC_SMT_CPC_Prover =
    mk_CVC_CPC_fun "CVC_SMT_CPC_Prover" proof_pre cpc_command
      (checked_post "CVC_SMT_CPC_Prover" cpc_command
        (fn dicts => CPC_ProofParser.parse_stream_with_version dicts
          (version_string ()))
        CPC_ProofReplay.check_proof_with_definitions)

  (* cvc5, SMT-LIB file format, checked proofs. *)
  val CVC_SMT_Prover = CVC_SMT_CPC_Prover
  (* Explicit finite graph path; legacy CVC_SMT_Prover above is unchanged. *)
  fun checked_graph_post limits
      ((original_goal,(As,g),validation,finite_hyps),
       (translation,arrays_exp)) outfile =
    let
      val input = TextIO.openIn outfile
      fun close () = TextIO.closeIn input
      fun classify phase error =
        if SmtResource.terminal_diagnostic_exception error then raise error
        else case error of Feedback.HOL_ERR holerr =>
          if SmtResource.is_resource_gate holerr then raise error else
            raise_with_context "CVC_SMT_Graph_Prover" phase
              (cpc_proof_cmd ^ (if arrays_exp then "--arrays-exp " else ""))
              holerr
        | _ => raise error
      fun work () =
        let val (status,start) = is_sat_stream_with_consumed input
        in case status of SolverSpec.UNSAT NONE =>
          let
            val trace = OS.Process.getEnv "HOL4_CPC_REPLAY_TRACE"
            fun replay () =
              SmtResource.with_proof_size_gate "cvc5-cpc-proof-text"
                outfile start input (fn stream =>
                  quiet_replay (fn () => SmtCheckedGraph.cvc limits translation
                    (version_string ()) (finite_hyps @ As,g) stream) ())
            val theorem =
              (if trace = SOME "1" orelse trace = SOME "full"
               then replay () else quiet replay)
              handle SmtCheckedGraph.ParseFailure error =>
                  classify "proof parse" error
                | SmtCheckedGraph.ReplayFailure error =>
                  classify "proof replay" error
            (* prove_graph_proof already closed the denied goal exactly once. *)
            val theorem = quiet (fn () => validation [theorem])
            val theorem = quiet (fn () => check_reconstructed_theorem
              "CVC_SMT_Graph_Prover" (original_goal,theorem))
          in SolverSpec.UNSAT (SOME theorem) end
        | _ => status end
      val outcome = Exn.capture work ()
    in case outcome of Exn.Res result => (close ();result)
      | Exn.Exn error =>
              SmtResource.resolve_diagnostic_exception error close
          (fn original => raise original)
    end
  fun CVC_SMT_Graph_Prover limits =
    (SmtCheckedGraph.validate limits;
     mk_CVC_CPC_fun "CVC_SMT_Graph_Prover" proof_pre cpc_command
       (checked_graph_post limits))


  (* Optional original Source path; no post-expanded tactic substitution. *)
  fun CVC_SMT_Original_Source_Prover
      {limits,discover,ordinary_limit,worker,force_worker} original =
    case configured_executable () of
      NONE => raise Feedback.mk_HOL_ERR "CVC"
        "CVC_SMT_Original_Source_Prover" error_msg
    | SOME file =>
      let
        fun pre original =
          let
            val invocation = SmtCheckedGraph.prepare_original
              limits discover original
            fun translate () =
              let
                val version = version_string ()
                val query = SmtCheckedGraph.processed_goal invocation
                val (translation,strings) =
                  SmtLib.goal_to_SmtLib_translation_for_solver
                    {policy = cvc_logic_policy,dialect = SmtLib.Standard27,
                     apply_operator = SmtLib.ApplyAt,get_proof = true,
                     target = SOME {solver = "cvc5",version = SOME version}}
                    query
                val _ = SmtCheckedGraph.admit_translation invocation translation
                val arrays_exp = List.exists
                  (fn text => String.isSubstring "(as const (Array" text) strings
              in ((invocation,translation,version,arrays_exp),strings) end
          in translate () handle primary =>
            ((SmtCheckedGraph.close_original invocation handle _ => ());
             raise primary) end
        fun post (invocation,translation,version,_) outfile =
          let
            val input = TextIO.openIn outfile
            fun work () =
              let val (status,start) = is_sat_stream_with_consumed input
              in case status of SolverSpec.UNSAT NONE =>
                let
                  val theorem = quiet (fn () =>
                    SmtResource.with_proof_size_gate "cvc5-cpc-proof-text"
                      outfile start input
                      (fn stream => SmtCheckedGraph.cvc_original invocation
                        translation version {ordinary_limit = ordinary_limit,
                          worker = worker,force_worker = force_worker} stream))
                in SolverSpec.UNSAT (SOME theorem) end
              | _ => status end
            val outcome = Exn.capture work ()
            val cleanup = Exn.capture TextIO.closeIn input
          in case outcome of Exn.Exn primary => raise primary
            | Exn.Res result => (Exn.release cleanup;result) end
        fun validate (invocation,_,_,_) goal theorem =
          SmtCheckedGraph.audit_original invocation goal theorem
        fun complete (invocation,_,_,_) =
          SmtCheckedGraph.close_original invocation
      in SolverSpec.make_solver_with_capture_command_and_completion
        validate complete (SOME cpc_capture) pre
        (fn (_,_,_,arrays_exp) => file ^ with_timeout_option
          (cpc_proof_cmd ^ (if arrays_exp then "--arrays-exp " else "")))
        post original end

  (* Additive SAME original Work path; legacy wrapper remains above. *)
  fun CVC_SMT_Owned_Original_Source_Prover
      {limits,discover,ordinary_limit,worker,force_worker} original =
    case configured_executable () of
      NONE => raise Feedback.mk_HOL_ERR "CVC"
        "CVC_SMT_Owned_Original_Source_Prover" error_msg
    | SOME file =>
      let
        fun pre original =
          let
            val invocation = SmtCheckedGraph.prepare_original_with_work
              limits discover original
            fun translate () =
              let
                val version = version_string ()
                val query = SmtCheckedGraph.processed_goal_with_work invocation
                val (translation,strings) =
                  SmtLib.goal_to_SmtLib_translation_for_solver
                    {policy = cvc_logic_policy,dialect = SmtLib.Standard27,
                     apply_operator = SmtLib.ApplyAt,get_proof = true,
                     target = SOME {solver = "cvc5",version = SOME version}}
                    query
                val _ = SmtCheckedGraph.admit_translation_with_work
                  invocation translation
                val arrays_exp = List.exists
                  (fn text => String.isSubstring "(as const (Array" text) strings
              in ((invocation,translation,version,arrays_exp),strings) end
          in translate () handle primary =>
            ((SmtCheckedGraph.close_original_with_work invocation
                handle _ => ());
             raise primary) end
        fun post (invocation,translation,version,_) outfile =
          let
            val input = TextIO.openIn outfile
            fun work () =
              let val (status,start) = is_sat_stream_with_consumed input
              in case status of SolverSpec.UNSAT NONE =>
                let
                  val theorem = quiet (fn () =>
                    SmtResource.with_proof_size_gate "cvc5-cpc-proof-text"
                      outfile start input
                      (fn stream => SmtCheckedGraph.cvc_original_with_work
                        invocation
                        translation version {ordinary_limit = ordinary_limit,
                          worker = worker,force_worker = force_worker} stream))
                in SolverSpec.UNSAT (SOME theorem) end
              | _ => status end
            val outcome = Exn.capture work ()
            val cleanup = Exn.capture TextIO.closeIn input
          in case outcome of Exn.Exn primary => raise primary
            | Exn.Res result => (Exn.release cleanup;result) end
        fun validate (invocation,_,_,_) goal theorem =
          SmtCheckedGraph.audit_original_with_work invocation goal theorem
        fun complete (invocation,_,_,_) =
          SmtCheckedGraph.close_original_with_work invocation
      in SolverSpec.make_solver_with_capture_command_and_completion
        validate complete (SOME cpc_capture) pre
        (fn (_,_,_,arrays_exp) => file ^ with_timeout_option
          (cpc_proof_cmd ^ (if arrays_exp then "--arrays-exp " else "")))
        post original end

  (* Additive SAME original Work path; legacy wrapper remains above. *)
  fun CVC_SMT_Owned_Original_Source_Prover_With_Emissions
      {limits,discover,ordinary_limit} original =
    case configured_executable () of
      NONE => raise Feedback.mk_HOL_ERR "CVC"
        "CVC_SMT_Owned_Original_Source_Prover_With_Emissions" error_msg
    | SOME file =>
      let
        fun pre original =
          let
            val invocation = SmtResource.profile_phase
              "cvc/emitted-source-admission"
              (SmtCheckedGraph.prepare_original_with_work limits discover)
              original
            fun translate () =
              let
                val version = version_string ()
                val {receipt,translation,strings} =
                  SmtResource.profile_phase "cvc/emitted-translation"
                    (SmtCheckedGraph.emit_translation_with_work invocation)
                    {policy = cvc_logic_policy,dialect = SmtLib.Standard27,
                     apply_operator = SmtLib.ApplyAt,get_proof = true,
                     target = SOME {solver = "cvc5",version = SOME version}}
                val _ = SmtCheckedGraph.admit_emitted_translation_with_work
                  invocation receipt
                val arrays_exp = List.exists
                  (fn text => String.isSubstring "(as const (Array" text)
                  strings
              in ((invocation,receipt,version,arrays_exp),strings) end
          in translate () handle primary =>
            ((SmtCheckedGraph.close_original_with_work invocation
                handle _ => ());
             raise primary) end
        fun post (invocation,receipt,version,_) outfile =
          let
            val input = TextIO.openIn outfile
            fun work () =
              let val (status,start) = is_sat_stream_with_consumed input
              in case status of SolverSpec.UNSAT NONE =>
                let
                  val theorem = quiet (fn () =>
                    SmtResource.with_proof_size_gate "cvc5-cpc-proof-text"
                      outfile start input
                      (fn stream =>
                        SmtCheckedGraph.cvc_original_emitted_with_work
                          invocation receipt version ordinary_limit stream))
                in SolverSpec.UNSAT (SOME theorem) end
              | _ => status end
            val outcome = Exn.capture work ()
            val cleanup = Exn.capture TextIO.closeIn input
          in case outcome of Exn.Exn primary => raise primary
            | Exn.Res result => (Exn.release cleanup;result) end
        fun validate (invocation,_,_,_) goal theorem =
          SmtResource.profile_phase "cvc/emitted-final-audit"
            (SmtCheckedGraph.audit_original_with_work invocation goal) theorem
        fun complete (invocation,_,_,_) =
          SmtCheckedGraph.close_original_with_work invocation
      in SolverSpec.make_solver_with_capture_command_and_completion
        validate complete (SOME cpc_capture) pre
        (fn (_,_,_,arrays_exp) => file ^ with_timeout_option
          (cpc_proof_cmd ^ (if arrays_exp then "--arrays-exp " else "")))
        post original end

  (* Opt-in output preflight. It is not a proof Reader or theorem route. *)
  val bounded_cpc_status_line_limit = 65536
  val bounded_cpc_status_prefix_limit = 1048576

  fun bounded_cpc_status input =
    let
      val consumed = ref 0
      fun refuse limit observed =
        SmtResource.raise_gate "cvc_status"
          ("resource-gated: cvc5-status; limit=" ^ limit ^
           "; observed=" ^ Int.toString observed ^ " bytes")
      fun next_line () =
        let
          fun collect length chars =
            case TextIO.input1 input of
              NONE => if length = 0 then NONE else
                SOME (String.implode (List.rev chars))
            | SOME ch =>
                let
                  (* The one extra SOME is never retained or classified. *)
                  val _ = if length < bounded_cpc_status_line_limit
                    then () else refuse "line-bytes" (length + 1)
                  val _ = if !consumed < bounded_cpc_status_prefix_limit
                    then () else refuse "prefix-bytes" (!consumed + 1)
                  val _ = consumed := !consumed + 1
                  val next = ch :: chars
                in if ch = #"\n" then SOME (String.implode
                     (List.rev next)) else collect (length + 1) next end
        in collect 0 [] end
      fun scan first_error =
        case next_line () of
          NONE => (SolverSpec.UNKNOWN first_error,!consumed)
        | SOME line =>
            let val trimmed = Substring.string
                  (Substring.dropl Char.isSpace (Substring.full line))
            in if String.isPrefix "(error" trimmed then
                 scan (case first_error of NONE => SOME line
                   | _ => first_error)
               else case String.tokens Char.isSpace line of
                   ["sat"] => (SolverSpec.SAT NONE,!consumed)
                 | ["unsat"] => (SolverSpec.UNSAT NONE,!consumed)
                 | _ => scan first_error
            end
    in scan NONE end

  fun bounded_cpc_status_file path =
    let
      val input = TextIO.openIn path
      val result = Exn.capture bounded_cpc_status input
      val cleanup = Exn.capture TextIO.closeIn input
    in case result of Exn.Exn primary => raise primary
      | Exn.Res status => (Exn.release cleanup;status) end

  (* Subtract in Position.int. The older Int overflow sentinel could become
     under-cap after subtracting a nonzero status prefix. *)
  fun bounded_cpc_proof_gate path proof_start =
    let
      val size = OS.FileSys.fileSize path
      val start = Position.fromInt proof_start
      val maximum = Position.fromInt SmtResource.max_proof_bytes
      val _ = if Position.compare (size,start) = LESS then
          raise Feedback.mk_HOL_ERR "CVC" "bounded_cpc_proof_gate"
            "proof start exceeds output size" else ()
      val remaining = Position.- (size,start)
      val _ = if Position.compare (remaining,maximum) = GREATER then
          SmtResource.raise_gate "check_proof_size"
            (SmtResource.resource_diagnostic_prefix "FloatingPoint" ^
             "limit=proof-size; observed=" ^
             Position.toString remaining ^ " bytes; maximum=" ^
             Int.toString SmtResource.max_proof_bytes ^
             " bytes; feature=" ^ SmtResource.resource_feature
               "FloatingPoint" "cvc5-cpc-proof-text")
        else SmtResource.check_proof_size "cvc5-cpc-proof-text"
          (Position.toInt remaining)
    in size end

  fun bounded_cpc_preflight path =
    let
      val (status,start) = bounded_cpc_status_file path
      val size = case status of SolverSpec.UNSAT NONE =>
          bounded_cpc_proof_gate path start
        | _ => OS.FileSys.fileSize path
    in (status,start,size) end

  fun bounded_cpc_copy source target =
    let
      val output = TextIO.openOut target
      fun work () =
        let
          val input = TextIO.openIn source
          fun loop () =
            let val chunk = TextIO.inputN (input,4096)
            in if chunk = "" then () else
                 (TextIO.output (output,chunk);loop ()) end
          val outcome = Exn.capture loop ()
          val close_input = Exn.capture TextIO.closeIn input
        in case outcome of Exn.Exn primary => raise primary
          | Exn.Res () => Exn.release close_input end
      val outcome = Exn.capture work ()
      val close_output = Exn.capture TextIO.closeOut output
    in case outcome of Exn.Exn primary => raise primary
      | Exn.Res () => Exn.release close_output end

  (* The optional output diagnostic is independently bounded, even if
     the solver file grows after a successful status preflight. Input
     diagnostics retain their existing copy behavior. *)
  fun bounded_cpc_copy_output source target =
    let
      val ceiling = IntInf.fromInt SmtResource.max_proof_bytes +
        IntInf.fromInt bounded_cpc_status_prefix_limit
      val output = TextIO.openOut target
      fun work () =
        let
          val input = TextIO.openIn source
          fun loop (copied : IntInf.int) =
            let
              val remaining = ceiling - copied
              val take = if remaining > 4096 then 4096 else
                if remaining > 0 then IntInf.toInt remaining else 1
              val chunk = TextIO.inputN (input,take)
              val next = copied + IntInf.fromInt (String.size chunk)
            in if chunk = "" then () else
                 if next > ceiling then
                   SmtResource.raise_gate "cvc_capture"
                     ("resource-gated: cvc5-output-diagnostic; limit=" ^
                      IntInf.toString ceiling ^ " bytes")
                 else (TextIO.output (output,chunk);loop next) end
          val outcome = Exn.capture loop (0 : IntInf.int)
          val close_input = Exn.capture TextIO.closeIn input
        in case outcome of Exn.Exn primary => raise primary
          | Exn.Res () => Exn.release close_input end
      val outcome = Exn.capture work ()
      val close_output = Exn.capture TextIO.closeOut output
      fun finish () = case outcome of Exn.Exn primary => raise primary
        | Exn.Res () => Exn.release close_output
    in finish () handle primary =>
         ((OS.FileSys.remove target handle _ => ());raise primary) end

  fun bounded_cpc_capture cmd_stem key stage source =
    case get_nonempty_env "HOL4_CVC_CPC_CAPTURE_DIR" of
      NONE => ()
    | SOME directory =>
        let
          val _ = OS.FileSys.mkDir directory handle SysErr _ => ()
          val stem = "cpc-" ^ OS.Path.file key
          val extension = if stage = "input" then ".smt2" else ".out"
          val target = OS.Path.concat (directory,stem ^ extension)
          val metadata = OS.Path.concat (directory,stem ^ ".meta")
          val _ = if stage = "input" then bounded_cpc_copy source target
            else bounded_cpc_copy_output source target
          val _ = Library.write_strings_to_file metadata
            ["cvc5_version=",version_string (),"\n",
             "command=",cmd_stem,"<input-file>\n"]
        in () end

  fun same_bounded_status (SolverSpec.SAT left,SolverSpec.SAT right) =
        left = right
    | same_bounded_status (SolverSpec.UNSAT NONE,SolverSpec.UNSAT NONE) =
        true
    | same_bounded_status
        (SolverSpec.UNKNOWN left,SolverSpec.UNKNOWN right) = left = right
    | same_bounded_status _ = false

  (* Opt-in status-only solver bracket. The A-born goal and same Work are
     created before SolverSpec pre; no proof Reader is selected here. *)
  fun CVC_SMT_Caller_Owned_Bool_App_Status_Bracket
      {request,children} =
    case configured_executable () of
      NONE => raise Feedback.mk_HOL_ERR "CVC"
        "CVC_SMT_Caller_Owned_Bool_App_Status_Bracket" error_msg
    | SOME file =>
      let
        val {goal,work,invocation,close} =
          CVC_Children_First_Adopt_Caller request children
        fun same_goal ((lefts,left),(rights,right)) =
          List.null lefts andalso List.null rights andalso
          Portable.pointer_eq (left,right)
        fun pre supplied =
          let
            val _ = if same_goal (goal,supplied) then () else
              raise Feedback.mk_HOL_ERR "CVC"
                "CVC_SMT_Caller_Owned_Bool_App_Status_Bracket"
                "SolverSpec supplied a different A-born goal"
            val version = version_string ()
            val query = SmtCheckedGraph.processed_goal_with_policy
              work invocation
            val (translation,strings) =
              SmtLib.goal_to_SmtLib_translation_for_solver
                {policy = cvc_logic_policy,dialect = SmtLib.Standard27,
                 apply_operator = SmtLib.ApplyAt,get_proof = true,
                 target = SOME {solver = "cvc5",version = SOME version}}
                query
            val _ = SmtCheckedGraph.admit_translation_with_policy
              work invocation translation
            val arrays_exp = List.exists
              (fn text => String.isSubstring "(as const (Array" text)
              strings
          in ((translation,arrays_exp),strings) end
        val output_receipt = ref NONE
        fun capture cmd key stage source =
          if stage <> "output" then
            bounded_cpc_capture cmd key stage source
          else
            let
              val result = case !output_receipt of
                  NONE => Exn.capture bounded_cpc_preflight source
                | SOME _ => Exn.Exn (Feedback.mk_HOL_ERR "CVC"
                    "capture" "duplicate output preflight")
              val _ = output_receipt := SOME (source,result)
            in case result of
                Exn.Exn (primary as Interrupt) => raise primary
              | Exn.Exn (primary as Timeout.TIMEOUT _) => raise primary
              | Exn.Exn _ => ()
              | Exn.Res _ => bounded_cpc_capture cmd key stage source end
        fun post _ outfile =
          let
            val preflight = case !output_receipt of
                NONE => raise Feedback.mk_HOL_ERR "CVC" "post"
                  "missing output preflight"
              | SOME (source,result) =>
                  (output_receipt := NONE;
                   if source = outfile then Exn.release result else
                     raise Feedback.mk_HOL_ERR "CVC" "post"
                       "foreign output preflight path")
            val (prior,prior_start,prior_size) = preflight
            val input = TextIO.openIn outfile
            fun work () =
              let
                val (status,start) = bounded_cpc_status input
                val size = OS.FileSys.fileSize outfile
                val _ = if same_bounded_status (prior,status) andalso
                    start = prior_start andalso
                    Position.compare (size,prior_size) = EQUAL
                  then () else raise Feedback.mk_HOL_ERR "CVC" "post"
                    "output changed after preflight"
                val _ = case status of SolverSpec.UNSAT NONE =>
                    ignore (bounded_cpc_proof_gate outfile start)
                  | _ => ()
              in status end
            val outcome = Exn.capture work ()
            val cleanup = Exn.capture TextIO.closeIn input
          in case outcome of Exn.Exn primary => raise primary
            | Exn.Res status => (Exn.release cleanup;status) end
        fun validate _ _ _ =
          raise Feedback.mk_HOL_ERR "CVC"
            "CVC_SMT_Caller_Owned_Bool_App_Status_Bracket"
            "status-only post cannot return a checked theorem"
        fun complete _ = close ()
        fun command (_,arrays_exp) =
          file ^ with_timeout_option
            (cpc_proof_cmd ^ (if arrays_exp then "--arrays-exp " else ""))
        fun run () =
          SolverSpec.make_solver_with_capture_command_and_completion_strict
            validate complete (SOME capture) pre command post goal
      in run () handle primary =>
        ((close () handle _ => ());raise primary) end


  (* Guarded paid full-CPC continuation of the caller-owned bracket.
     The fixed replay policy below intentionally refuses selection. *)
  fun CVC_SMT_Caller_Owned_Bool_App_Checked_Bracket
      {request,children} =
    case configured_executable () of
      NONE => raise Feedback.mk_HOL_ERR "CVC"
        "CVC_SMT_Caller_Owned_Bool_App_Checked_Bracket" error_msg
    | SOME file =>
      let
        (* Refuse an unbounded original Work before A/I birth. This
           restriction belongs to the checked fixture only. *)
        val _ = case #work_limit (#owned request) of
            SmtReplayResourcePolicy.AtMost n =>
              if n > 0 then () else
                raise Feedback.mk_HOL_ERR "CVC" "fixed_work_limit"
                  "checked route requires positive finite original Work"
          | SmtReplayResourcePolicy.Uncapped =>
              raise Feedback.mk_HOL_ERR "CVC" "fixed_work_limit"
                "checked route requires positive finite original Work"
        val {goal,work,invocation,close} =
          CVC_Children_First_Adopt_Caller request children
        (* Restricted fixed replay policy. The native Type cap is per
           callback; all Type debits accumulate on the retained Work. *)
        fun fixed_policy_replay_options () :
            SmtCheckedGraph.policy_replay_options =
          let
            val contract = SmtCheckedGraph.native_contract_with_policy_for
              work invocation
            val limits = SmtReplayNativeContract.for_work work contract
            val ceiling = IntInf.fromInt (#type_work_limit limits)
            val epoch = Type.type_epoch ()
            val symbols = Term.term_epoch ()
            val entered = ref false
            val ERR = Feedback.mk_HOL_ERR "CVC" "fixed_type_policy"
            fun epochs () =
              if Type.type_epoch () = epoch andalso
                  Term.term_epoch () = symbols then () else
                raise ERR "Type or Term epoch changed"
            fun valid () =
              (SmtReplayNativeContract.validate_for work contract;
               epochs ())
            fun native_unit used n =
              (epochs ();
               if n >= 0 andalso !used + n <= ceiling then () else
                 raise ERR "retained native Type work exhausted";
               SmtReplayInvocationWork.spend_policy work n;
               used := !used + n;
               epochs ())
            fun inspect root =
              let
                val used = ref (0 : IntInf.int)
                fun walk [] = ()
                  | walk ([] :: more) = walk more
                  | walk ((ty :: rest) :: more) =
                      (native_unit used 1;
                       if Type.is_vartype ty then
                         let
                           val name = Type.dest_vartype ty
                           val _ = native_unit used
                             (IntInf.fromInt (String.size name))
                         in walk (rest :: more) end
                       else
                         let val (_,args) = Type.dest_type ty
                         in walk (args :: rest :: more) end)
              in walk [[root]] end
            fun check ty =
              ((valid ();
                if !entered then raise ERR "reentrant Type callback"
                  else ();
                entered := true;
                inspect ty;
                valid ();
                entered := false)
               handle primary =>
                 ((SmtReplayInvocationWork.close work handle _ => ());
                  raise primary))
          in {profiles=[],check_type=check,ordinal=0} end
        fun same_goal ((lefts,left),(rights,right)) =
          List.null lefts andalso List.null rights andalso
          Portable.pointer_eq (left,right)
        fun pre supplied =
          let
            val _ = if same_goal (goal,supplied) then () else
              raise Feedback.mk_HOL_ERR "CVC"
                "CVC_SMT_Caller_Owned_Bool_App_Checked_Bracket"
                "SolverSpec supplied a different A-born goal"
            val version = version_string ()
            val query = SmtCheckedGraph.processed_goal_with_policy
              work invocation
            val (translation,strings) =
              SmtLib.goal_to_SmtLib_translation_for_solver
                {policy = cvc_logic_policy,dialect = SmtLib.Standard27,
                 apply_operator = SmtLib.ApplyAt,get_proof = true,
                 target = SOME {solver = "cvc5",version = SOME version}}
                query
            val _ = SmtCheckedGraph.admit_translation_with_policy
              work invocation translation
            val arrays_exp = List.exists
              (fn text => String.isSubstring "(as const (Array" text)
              strings
          in ((translation,version,arrays_exp),strings) end
        val output_receipt = ref NONE
        fun capture cmd key stage source =
          if stage <> "output" then
            bounded_cpc_capture cmd key stage source
          else
            let
              val result = case !output_receipt of
                  NONE => Exn.capture bounded_cpc_preflight source
                | SOME _ => Exn.Exn (Feedback.mk_HOL_ERR "CVC"
                    "capture" "duplicate output preflight")
              val _ = output_receipt := SOME (source,result)
            in case result of
                Exn.Exn (primary as Interrupt) => raise primary
              | Exn.Exn (primary as Timeout.TIMEOUT _) => raise primary
              | Exn.Exn _ => ()
              | Exn.Res _ => bounded_cpc_capture cmd key stage source end
        fun post (translation,version,_) outfile =
          let
            val preflight = case !output_receipt of
                NONE => raise Feedback.mk_HOL_ERR "CVC" "post"
                  "missing output preflight"
              | SOME (source,result) =>
                  (output_receipt := NONE;
                   if source = outfile then Exn.release result else
                     raise Feedback.mk_HOL_ERR "CVC" "post"
                       "foreign output preflight path")
            val (prior,prior_start,prior_size) = preflight
            val input = TextIO.openIn outfile
            fun scan_and_replay () =
              let
                val (status,start) = bounded_cpc_status input
                val size = OS.FileSys.fileSize outfile
                val _ = if same_bounded_status (prior,status) andalso
                    start = prior_start andalso
                    Position.compare (size,prior_size) = EQUAL
                  then () else raise Feedback.mk_HOL_ERR "CVC" "post"
                    "output changed after preflight"
                (* A matching post scan pays its bounded prefix before
                   status dispatch. The scan and the earlier preflight
                   are still not prepaid. *)
                val _ = SmtReplayInvocationWork.with_step work
                  (fn () => SmtReplayInvocationWork.spend_policy work
                    (IntInf.fromInt start))
                val result = case status of SolverSpec.UNSAT NONE =>
                    let
                      val _ = ignore (bounded_cpc_proof_gate outfile start)
                      (* Capture from the status-positioned descriptor. The
                         opaque receipt owns the paid immutable proof bytes;
                         this file-size gate grants no parser authority. *)
                      val certificate =
                        SmtReplayInvocationWork.capture_cpc_certificate
                          work input
                      val theorem =
                        SmtCheckedGraph.cvc_original_with_policy_paid
                          work invocation translation version
                          (fixed_policy_replay_options ()) certificate
                    in SolverSpec.UNSAT (SOME theorem) end
                  | _ => status
              in result end
            val outcome = Exn.capture scan_and_replay ()
            val cleanup = Exn.capture TextIO.closeIn input
          in case outcome of Exn.Exn primary => raise primary
            | Exn.Res status => (Exn.release cleanup;status) end
        fun validate _ supplied theorem =
          SmtCheckedGraph.audit_original_with_policy
            work invocation supplied theorem
        fun complete _ = close ()
        fun command (_,_,arrays_exp) =
          file ^ with_timeout_option
            (cpc_proof_cmd ^ (if arrays_exp then "--arrays-exp " else ""))
        fun run () =
          SolverSpec.make_solver_with_capture_command_and_completion_strict
            validate complete (SOME capture) pre command post goal
      in run () handle primary =>
        ((close () handle _ => ());raise primary) end

end
