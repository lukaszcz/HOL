(* Copyright (c) 2009-2012 Tjark Weber. All rights reserved. *)

(* Functions to invoke the Z3 SMT solver *)

structure Z3 = struct

  (* returns SAT if Z3 reported "sat", UNSAT if Z3 reported "unsat" *)
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

  fun is_configured () =
      let val v = OS.Process.getEnv "HOL4_Z3_EXECUTABLE" in
          (Option.isSome v) andalso (Option.valOf v <> "")
      end;

  val error_msg = "Z3 not configured: set the HOL4_Z3_EXECUTABLE environment variable to point to the Z3 executable file.";

  fun configured_executable () =
    case OS.Process.getEnv "HOL4_Z3_EXECUTABLE" of
      SOME file => if file = "" then NONE else SOME file
    | NONE => NONE

  fun executable_string () =
    case configured_executable () of
      SOME file => file
    | NONE => "<unconfigured>"

  fun mk_Z3_fun name pre cmd_stem post goal =
    case configured_executable () of
      SOME file =>
        SolverSpec.make_solver pre (file ^ cmd_stem) post goal
    | NONE =>
        raise Feedback.mk_HOL_ERR "Z3" name error_msg

  (* Z3 (Linux/Unix), SMT-LIB file format, no proofs *)
  val Z3_SMT_Oracle =
    mk_Z3_fun "Z3_SMT_Oracle"
      (fn goal =>
        let
          val (goal, _) = SolverSpec.simplify (SmtLib.SIMP_TAC false) goal
          val (_, strings) = SmtLib.goal_to_SmtLib NONE goal
        in
          ((), strings)
        end)
      " -smt2 -file:"
      (Lib.K is_sat_file)

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

  val is_v4 = String.isPrefix "4" Z3version

  fun is_v4_configured () = is_configured () andalso is_v4

  val proof_option =
    if is_v4 then
      (* disable `pp.simplify_implies` so that Z3's AST pretty-printer doesn't
         mangle `asserted` proof rules, which would cause a mismatch against the
         goal's assumption list *)
      " proof=true pp.simplify_implies=false"
    else
      " PROOF_MODE=2"

  val proof_cmd_stem = proof_option ^ " -smt2 -file:"

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
      val () = Library.check_oracle_tags name thm
    in
      thm
    end

  fun direct_contradiction_thm goal =
    let
      val asserted = boolSyntax.dest_neg goal
      val contradiction = Library.gen_contradiction (Thm.ASSUME asserted)
    in
      Thm.NOT_INTRO (Thm.DISCH asserted contradiction)
    end

  fun prove_direct_contradiction goal =
    check_reconstructed_theorem "Z3_SMT_Prover"
      (goal, direct_contradiction_thm (Lib.snd goal))

  fun prove_simplified_goal goal =
    let
      val thm = Tactical.TAC_PROOF (goal,
        Tactical.THEN (SmtLib.SIMP_TAC true, intLib.ARITH_TAC))
    in
      check_reconstructed_theorem "Z3_SMT_Prover" (goal, thm)
    end

  fun prove_without_external_solver goal =
    prove_direct_contradiction goal
    handle Feedback.HOL_ERR _ => prove_simplified_goal goal

  fun is_tautological_counterexample ([], g) =
      (case Lib.total boolSyntax.dest_neg g of
         SOME asserted =>
           (case Lib.total tautLib.TAUT_CONV asserted of
              SOME thm => boolSyntax.is_eq (Thm.concl thm) andalso
                          Term.aconv (boolSyntax.rhs (Thm.concl thm))
                            boolSyntax.T
            | NONE => false)
       | NONE => false)
    | is_tautological_counterexample _ = false

  (* Z3 (Linux/Unix), SMT-LIB file format, with proofs *)
  val Z3_SMT_Prover_external =
    mk_Z3_fun "Z3_SMT_Prover"
      (fn goal =>
        let
          val original_goal = goal
          val (goal, validation) = SolverSpec.simplify (SmtLib.SIMP_TAC true) goal
          val (translation, strings) =
            SmtLib.goal_to_SmtLib_with_get_proof_translation NONE goal
        in
          (((original_goal, goal, validation), translation), strings)
        end)
      proof_cmd_stem
      (fn ((original_goal, goal, validation), translation) =>
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
                (* parse the proof and check it in HOL *)
                val proof = Z3_ProofParser.parse_stream_with_version
                  (ty_dict, tm_dict) (version_string ()) instream
                  handle Feedback.HOL_ERR holerr =>
                    (TextIO.closeIn instream;
                     raise_with_context "Z3_SMT_Prover" "proof parse"
                       proof_cmd_stem holerr)
                val _ = TextIO.closeIn instream
                val (As, g) = goal
                val thm = Z3_ProofReplay.check_proof (As, g, proof)
                  handle Feedback.HOL_ERR holerr =>
                    raise_with_context "Z3_SMT_Prover" "proof replay"
                      proof_cmd_stem holerr
                val thm = Thm.CCONTR g thm
                val thm = validation [thm]
                val thm = check_reconstructed_theorem "Z3_SMT_Prover"
                  (original_goal, thm)
              in
                SolverSpec.UNSAT (SOME thm)
              end
            | _ => (result before TextIO.closeIn instream)
          end)

  fun Z3_SMT_Prover goal =
    if is_tautological_counterexample goal then
      SolverSpec.SAT NONE
    else
      SolverSpec.UNSAT (SOME (prove_without_external_solver goal))
      handle Feedback.HOL_ERR _ => Z3_SMT_Prover_external goal

end
