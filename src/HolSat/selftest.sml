open HolKernel Parse boolLib testutils HolSatLib

val _ = set_trace "Unicode" 0

(* These callbacks never run a SAT executable.  In particular, failures in
   command construction must get the same cleanup as solver/replay failures. *)
local
  open satConfig SatSolvers
  exception CleanupSentinel of unit ref
  val token = ref ()
  val primary = CleanupSentinel token
  val secondary = Fail "secondary cleanup failure"
  val duration = Time.fromSeconds 7
  fun same (CleanupSentinel x) (CleanupSentinel y) = x = y
    | same Interrupt Interrupt = true
    | same (Timeout.TIMEOUT x) (Timeout.TIMEOUT y) = x = y
    | same (Fail x) (Fail y) = x = y
    | same _ _ = false
  fun raised expected (Exn.Exn actual) = same expected actual
    | raised _ _ = false
  fun control name action =
    (tprint name; require_msg (check_result I) Bool.toString action ())
  fun put path text =
    let val out = TextIO.openOut path
    in dimacsTools.with_cleanup (fn () => TextIO.closeOut out)
         (fn () => TextIO.output (out,text)) () end
  fun exists path = OS.FileSys.access (path,[])
  fun named_solver name run post =
    let val SatSolver fields = minisatp
    in SatSolver
      {name = name, URL = #URL fields,
       (* Access is checked, but this executable is never launched. *)
       executable = OS.Path.concat (Globals.HOLDIR,"bin/hol"),
       post_exe = Option.map (fn _ => "unused") post,
       notime_run = run, time_run = #time_run fields,
       post_run = (case post of SOME f => f | NONE => #post_run fields),
       only_true = false, failure_string = "UNSAT",
       start_string = "SAT", end_string = " 0"}
    end
  fun solver run post = named_solver "cleanup-sentinel" run post

  (* A backend name does not establish ownership.  Check the fixed trace
     separately from the generated per-call names, before any child launch. *)
  fun fixed_trace_case present create input post error prove =
    let
      val trace = "resolve_trace"
      val text = "caller owned before command construction\n"
      val occupied = (ignore (OS.FileSys.isLink trace); true)
                     handle OS.SysErr _ => false
      val _ = if occupied then
                raise Fail "resolve_trace already exists in test directory"
              else ()
      val paths = ref (case input of NONE => [] | SOME p => [p])
      val calls = ref 0
      fun run _ (cnf,outfile) =
        (calls := !calls + 1;
         paths := [cnf,outfile,outfile^".proof",outfile^".stats"] @
           (case input of NONE => [!dimacsTools.tmp_name] | SOME _ => []);
         put outfile "UNSAT\n";
         put (outfile^".proof") "sentinel proof";
         put (outfile^".stats") "sentinel stats";
         if create then put trace "invocation owned\n" else ();
         if post then "exit 0" else raise error)
      val backend = named_solver "zchaff" run
        (if post then SOME (fn _ => fn _ => raise error) else NONE)
      val conf = set_solver backend (set_term ``~(p /\ q)`` base_config)
      val conf = case input of NONE => conf | SOME p => set_infile p conf
      fun same_text () =
        let val stream = TextIO.openIn trace
        in dimacsTools.with_cleanup (fn () => TextIO.closeIn stream)
             TextIO.inputAll stream = text end
    in dimacsTools.with_cleanup
      (fn () => dimacsTools.clean_files (trace :: !paths))
      (fn () =>
        let val _ = if present then put trace text else ()
            val result = Exn.capture prove conf
        in !calls = 1 andalso raised error result andalso
           (if present then exists trace andalso same_text ()
            else exists trace = (create andalso Option.isSome input)) andalso
           List.all (fn p => exists p = Option.isSome input) (!paths)
        end) ()
    end
  val failures = [primary, Interrupt, Timeout.TIMEOUT duration]
  val _ = control "ZChaff pre-launch failures preserve caller trace bytes"
    (fn () => List.all (fn prove => List.all (fn error =>
      fixed_trace_case true false NONE false error prove) failures)
      [GEN_SAT, GEN_SAT_PROVE_ONLY,
       fn conf => GEN_SAT (set_flag_is_proved false conf)])
  val _ = control "ZChaff newly created trace drains on every failure"
    (fn () => List.all (fn post => List.all (fn error =>
      fixed_trace_case false true NONE post error GEN_SAT) failures)
      [false,true])
  val _ = control "ZChaff postprocessor failure preserves caller trace"
    (fn () => List.all (fn error =>
      fixed_trace_case true false NONE true error GEN_SAT) failures)
  val _ = control "ZChaff explicit input retains invocation files"
    (fn () => List.all (fn present =>
      let val input = OS.FileSys.tmpName ()
      in dimacsTools.with_cleanup (fn () => dimacsTools.clean_files [input])
        (fn () => (put input "p cnf 1 1\n1 0\n";
          fixed_trace_case present (not present) (SOME input) false
            primary GEN_SAT)) () end) [false,true])
  val _ = control "ZChaff pre-launch failure preserves dangling caller link"
    (fn () =>
      let val target = OS.FileSys.tmpName ()
          val trace = "resolve_trace"
          val _ = OS.FileSys.remove target
      in dimacsTools.with_cleanup (fn () => dimacsTools.clean_files [trace])
        (fn () =>
          (Posix.FileSys.symlink {old = target, new = trace};
           raised primary (Exn.capture GEN_SAT
             (set_solver (named_solver "zchaff"
               (fn _ => fn _ => raise primary) NONE)
               (set_term ``~(p /\ q)`` base_config))) andalso
           OS.FileSys.isLink trace andalso
           OS.FileSys.readLink trace = target)) () end)

  val _ = control "SAT resource scopes preserve the first exception"
    (fn () => List.all (fn error =>
      List.all (fn cleanup_error =>
        let val closed = ref false
            val result = Exn.capture
              (dimacsTools.with_cleanup
                (fn () => (closed := true; raise cleanup_error))
                (fn () => raise error)) ()
        in !closed andalso raised error result end)
        [secondary, Interrupt, Timeout.TIMEOUT duration])
      [primary, Interrupt, Timeout.TIMEOUT duration] andalso
      raised secondary (Exn.capture
        (dimacsTools.with_cleanup (fn () => raise secondary) (fn () => 1))
        ()) andalso
      dimacsTools.with_cleanup (fn () => ()) (fn () => 17) () = 17)

  (* Verify sidecars as well as the CNF and the tmpName placeholder.  The
     outer scope also cleans broken-test leftovers before reporting failure. *)
  fun callback_case input answer run_error post_error prove accept =
    let
      val paths = ref (case input of NONE => [] | SOME path => [path])
      val calls = ref 0
      val ready = ref false
      fun run _ (cnf,outfile) =
        (calls := !calls + 1;
         paths := [cnf,outfile,outfile^".proof",outfile^".stats"] @
           (case input of NONE => [!dimacsTools.tmp_name] | SOME _ => []);
         ready := exists cnf;
         put outfile answer;
         put (outfile^".proof") "sentinel proof";
         put (outfile^".stats") "sentinel stats";
         case run_error of SOME error => raise error | NONE => "exit 0")
      val post = Option.map (fn error => fn _ => fn _ => raise error)
                            post_error
      val conf = set_solver (solver run post)
        (set_term ``~(p /\ q)`` base_config)
      val conf = case input of NONE => conf | SOME path => set_infile path conf
    in dimacsTools.with_cleanup (fn () => dimacsTools.clean_files (!paths))
         (fn () =>
           let val result = Exn.capture prove conf
           in !calls = 1 andalso !ready andalso accept result andalso
              List.all (fn path => exists path = Option.isSome input) (!paths)
           end) ()
    end
  fun failed error =
    callback_case NONE "UNSAT\n" (SOME error) NONE GEN_SAT (raised error)
  val _ = control "SAT callback failures remove all owned solver files"
    (fn () => List.all failed [primary, Interrupt, Timeout.TIMEOUT duration])
  val _ = control "SAT postprocessor failures remove all owned solver files"
    (fn () => List.all (fn error =>
      callback_case NONE "UNSAT\n" NONE (SOME error) GEN_SAT (raised error))
      [primary, Interrupt, Timeout.TIMEOUT duration])
  val _ = control "MiniSat failure preserves unrelated fixed trace files"
    (fn () =>
      let val path = "resolve_trace"
          val existed = exists path
          val _ = if existed then () else put path "caller owned\n"
      in dimacsTools.with_cleanup
           (fn () => if existed then () else dimacsTools.clean_files [path])
           (fn () => failed primary andalso exists path) ()
      end)
  val _ = control "SAT callback cleanup preserves caller-owned files"
    (fn () =>
      let val input = OS.FileSys.tmpName ()
      in dimacsTools.with_cleanup (fn () => dimacsTools.clean_files [input])
           (fn () =>
             (put input "p cnf 1 1\n1 0\n";
              callback_case (SOME input) "UNSAT\n" (SOME primary) NONE
                GEN_SAT (fn result => raised primary result andalso
                  dimacsTools.readDimacs input ~~ ``v1:bool``))) ()
      end)
  val _ = control "SAT result/failure paths remove owned solver files"
    (fn () =>
      callback_case NONE "SAT 1 2 0\n" NONE NONE GEN_SAT_PROVE_ONLY
        (fn Exn.Exn (SAT_satisfiable _) => true | _ => false) andalso
      callback_case NONE "SAT 1 2 0\n" NONE NONE
        (fn conf => GEN_SAT (set_flag_is_proved false conf))
        (fn Exn.Exn (SAT_cex _) => true | _ => false) andalso
      callback_case NONE "UNSAT\n" NONE NONE
        (fn conf => GEN_SAT (set_flag_is_proved false conf))
        (fn Exn.Res th => concl th ~~ ``~(p /\ q)`` | _ => false) andalso
      callback_case NONE "SAT not-an-integer 0\n" NONE NONE GEN_SAT
        (fn Exn.Exn (HOL_ERR _) => true | _ => false) andalso
      callback_case NONE "SAT 1 2 0\n" NONE NONE GEN_SAT
        (fn Exn.Exn (SAT_cex _) => true | _ => false) andalso
      callback_case NONE "SAT -1 -2 0\n" NONE NONE GEN_SAT
        (fn Exn.Exn satTools.satCheckError => true | _ => false))

  val _ = control "SAT observation scopes retire on failure and reject reentry"
    (fn () =>
      let fun reset error =
            let val failed = Exn.capture satTools.with_solver_statistics
                  (fn () => raise error)
                val (value,stats) = satTools.with_solver_statistics
                  (fn () => 17)
            in raised error failed andalso value = 17 andalso
               #external_calls stats = 0 andalso #internal_calls stats = 0
            end
          val ((rejected,_),_) = satTools.with_solver_statistics (fn () =>
            let val denied =
                  ((satTools.with_solver_statistics (fn () => ()); false)
                   handle HOL_ERR e =>
                     Feedback.top_structure_of e = "satTools" andalso
                     Feedback.top_function_of e = "with_solver_statistics"
                     andalso Feedback.message_of e = "observation reentry")
            in (denied,()) end)
      in rejected andalso List.all reset
           [primary,Interrupt,Timeout.TIMEOUT duration] end)

  (* Keep the legacy ordinary-I/O classification; only terminal I/O causes
     must escape rather than being classified as an UNSAT response. *)
  fun invoke error = satTools.invokeSat
    (solver (fn _ => fn _ => raise error) NONE) T NONE NONE
    (1,Redblackmap.mkDict Term.compare) (Array.fromList [T]) "unused"
  val ordinary_io = IO.Io
    {name = "sentinel", function = "callback", cause = Fail "ordinary"}
  fun terminal_io error = IO.Io
    {name = "sentinel", function = "callback", cause = error}
  val _ = control "SAT callback ordinary I/O classification is unchanged"
    (fn () => not (Option.isSome (invoke ordinary_io)) andalso
      raised primary (Exn.capture invoke primary) andalso
      List.all (fn error =>
        case Exn.capture invoke (terminal_io error) of
          Exn.Exn (IO.Io {cause,...}) => same error cause | _ => false)
        [Interrupt, Timeout.TIMEOUT duration])
in
  val _ = ()
end

(* #1170: SAT_ORACLE used to fabricate a bogus theorem on inputs whose
   negated form has a top-level conjunct that boolean-simplifies to F.
   For ``b ==> T`` the negation is ``b /\ ~T``; presimp turns ``~T`` into
   ``F``, but the F conjunct was silently dropped from the CNF passed to
   MiniSAT, which then declared satisfiability. SAT_ORACLE skipped the
   model-check that SAT_PROVE relies on and returned a bogus
   |- b ==> ~(b ==> T). The fix short-circuits in to_cnf when a conjunct
   reduces to F, so MiniSAT is never invoked for this case (and so the
   test does not depend on a working MiniSAT installation). *)
val _ = tprint "SAT_ORACLE proves `b ==> T` (#1170)"
val _ = require_msg
          (check_result (fn th => concl th ~~ ``b ==> T``))
          thm_to_string
          SAT_ORACLE
          ``b ==> T``

(* Definitional CNF uses a shared root assumption while replaying the
   resolution trace; the returned proof must still discharge that root. *)
val _ = tprint "SAT_PROVE discharges definitional CNF roots"
val _ = require_msg
          (check_result (fn th => null (hyp th) andalso
            concl th ~~ ``(p /\ q) ==> (q /\ p)``))
          thm_to_string
          SAT_PROVE
          ``(p /\ q) ==> (q /\ p)``

(* Proof-only mode checks UNSAT certificates but never reconstructs a model
   theorem for a satisfying assignment that the caller will discard. *)
val _ = tprint "SAT_PROVE_ONLY checks UNSAT proofs"
val _ = require_msg
          (check_result (fn th => null (hyp th) andalso
            concl th ~~ ``(p /\ q) ==> (q /\ p)``))
          thm_to_string
          SAT_PROVE_ONLY
          ``(p /\ q) ==> (q /\ p)``

val _ = tprint "SAT_PROVE_ONLY rejects SAT instances"
val _ = require_msg
          (check_result (fn rejected => rejected))
          Bool.toString
          (fn tm => (ignore (SAT_PROVE_ONLY tm); false)
             handle SAT_satisfiable _ => true)
          ``p \/ q``

(* Explicit CNF counts propositional atoms, which need not be HOL
   variables.  Here P is the only free variable but P T and P F are
   distinct DIMACS atoms.  Proof-only mode must also override an oracle
   flag supplied in the configuration. *)
val _ = tprint "explicit CNF counts compound Boolean atoms"
val _ = require_msg
          (check_result (fn th =>
            let val (oracles, axioms) = Tag.dest_tag (tag th)
            in null (hyp th) andalso
               concl th ~~ ``~((P:bool->bool) T /\ ~P T /\ P F /\ ~P F)``
               andalso List.all (fn name => name = "DISK_THM") oracles
               andalso null axioms
            end))
          thm_to_string
          (fn tm => GEN_SAT_PROVE_ONLY
            (satConfig.set_flag_is_proved false
              (satConfig.set_flag_is_cnf true
                (satConfig.set_term tm satConfig.base_config))))
          ``(P:bool->bool) T /\ ~P T /\ P F /\ ~P F``

val _ = tprint "proof-only explicit CNF rejects SAT without model checking"
val _ = require_msg
          (check_result (fn rejected => rejected))
          Bool.toString
          (fn tm =>
            (ignore (GEN_SAT_PROVE_ONLY
              (satConfig.set_flag_is_cnf true
                (satConfig.set_term tm satConfig.base_config)));
             false)
            handle SAT_satisfiable _ => true)
          ``(P:bool->bool) T /\ ~P F``

(* These controls force the boundary rather than letting a missing external
   solver silently turn a certificate test into an internal DPLL test. *)
local
  open satConfig SatSolvers
  fun checked expected th =
    let val (oracles, axioms) = Tag.dest_tag (tag th)
    in null (hyp th) andalso concl th ~~ expected andalso null axioms
       andalso List.all (fn s => s = "DISK_THM") oracles end
  fun control name action =
    (tprint name;
     require_msg (check_result I) Bool.toString action ())
  fun config cnf = set_flag_is_cnf true (set_term cnf base_config)
  val valid = ``(p /\ q) ==> (q /\ p)``
  val invalid = ``p \/ q``
  val cnf = ``p /\ ~p``
  val compound = ``(P:bool->bool) T /\ ~P F``
  fun sat_only conf =
    (GEN_SAT_PROVE_ONLY conf; false) handle SAT_satisfiable _ => true
  fun model conf goal =
    (GEN_SAT conf; false) handle SAT_cex th =>
      let val (assignment, denied) = dest_imp (concl th)
          val verified = satTools.satCheck (strip_conj assignment) denied
      in checked (concl th) th andalso checked (concl th) verified
         andalso denied ~~ mk_neg goal end
  fun named_solver_at name path =
    let val SatSolver fields = minisatp
    in SatSolver
      {name = name, URL = #URL fields, executable = path,
       post_exe = NONE, notime_run = #notime_run fields,
       time_run = #time_run fields, post_run = #post_run fields,
       only_true = #only_true fields, failure_string = #failure_string fields,
       start_string = #start_string fields, end_string = #end_string fields}
    end
  fun solver_at path = named_solver_at (getSolverName minisatp) path
  val missing = OS.FileSys.tmpName ()
  val _ = OS.FileSys.remove missing
  fun internal conf = set_solver (solver_at missing) conf
  fun measured conf prove =
    let val (result, stats) = satTools.with_solver_statistics
          (fn () => prove conf)
    in result andalso #external_calls stats = 0
       andalso #internal_calls stats = 1 end
  val _ = control "ordinary missing-solver checked UNSAT/model contracts"
    (fn () => measured (internal (set_term valid base_config))
        (fn conf => checked valid (GEN_SAT conf)) andalso
      measured (internal (set_term invalid base_config))
        (fn conf => model conf invalid))
  val _ = control "proof-only missing-solver CNF and compound SAT contracts"
    (fn () => measured (internal (config cnf))
        (fn conf => checked (mk_neg cnf) (GEN_SAT_PROVE_ONLY conf)) andalso
      measured (internal (config compound)) sat_only andalso
      measured (internal (set_term invalid base_config)) sat_only andalso
      sat_only (set_term F base_config))
  val _ = control "proof-only missing-proof fallback preserves explicit CNF"
    (fn () => measured (set_proof missing (config cnf))
        (fn conf => checked (mk_neg cnf) (GEN_SAT_PROVE_ONLY conf)) andalso
      measured (set_proof missing (config compound)) sat_only)
  val _ = control "ordinary missing-proof checked UNSAT/model contracts"
    (fn () => measured
        (set_flag_is_cnf false (set_proof missing
          (set_term valid base_config)))
        (fn conf => checked valid (GEN_SAT conf)) andalso
      measured (set_flag_is_cnf false (set_proof missing
        (set_term invalid base_config))) (fn conf => model conf invalid))

  val trace = OS.FileSys.tmpName ()
  fun with_trace bytes action =
    let val out = BinIO.openOut trace
        val _ = BinIO.output (out, Word8Vector.fromList
          (List.map Word8.fromInt bytes))
        val _ = BinIO.closeOut out
        val result = Exn.capture action (set_proof trace (config cnf))
        val _ = OS.FileSys.remove trace
    in Exn.release result end
  val _ = control "ZChaff fallback and malformed replay preserve caller trace"
    (fn () =>
      let val path = "resolve_trace"
          val text = "caller owned during fallback/replay\n"
          val backend = named_solver_at "zchaff" missing
          fun zconf conf = set_solver backend conf
          fun preserved () =
            let val stream = TextIO.openIn path
            in dimacsTools.with_cleanup (fn () => TextIO.closeIn stream)
                 TextIO.inputAll stream = text end
          fun fallback prove conf =
            checked valid (prove (zconf conf)) andalso preserved ()
      in dimacsTools.with_cleanup (fn () => dimacsTools.clean_files [path])
        (fn () =>
          let val out = TextIO.openOut path
              val _ = TextIO.output (out,text)
              val _ = TextIO.closeOut out
              val conf = set_term valid base_config
              val proof = set_flag_is_cnf false (set_proof missing conf)
          in List.all (fn prove => fallback prove conf andalso
               fallback prove proof) [GEN_SAT,GEN_SAT_PROVE_ONLY] andalso
             with_trace [] (fn conf =>
               ((GEN_SAT (zconf conf); false)
                 handle Domain => preserved () | Subscript => preserved ()
                      | HOL_ERR _ => preserved ()))
          end) ()
      end)
  val roots = [2,0,0,4,1,0]
  val forward = [5,2,1,0]
  val backward = [3,1,2,0]
  fun trace_proves bytes problem = with_trace bytes (fn conf =>
    let val (th, stats) = satTools.with_solver_statistics (fn () =>
          GEN_SAT_PROVE_ONLY (set_term problem conf))
    in checked (mk_neg problem) th andalso #internal_calls stats = 0
       andalso #external_calls stats = 0 end)
  fun bad_trace bytes problem = with_trace bytes (fn conf =>
    ((GEN_SAT_PROVE_ONLY (set_term problem conf); false)
     handle HOL_ERR _ => true | Domain => true | Subscript => true))
  val _ = control "binary resolution: both pivots, factoring and deletion"
    (fn () => trace_proves (roots @ forward) cnf andalso
      trace_proves (roots @ backward) cnf andalso
      trace_proves (roots @ forward) ``(p \/ p) /\ ~p`` andalso
      trace_proves (roots @ [3,0] @ forward) cnf)
  val _ = control "binary resolution: malformed/incomplete traces reject"
    (fn () => List.all (fn bytes => bad_trace bytes cnf)
      [[], [128], [2,0], [2,0,0], [0,0,0], [6,0,0],
       roots @ [1,2,1,0], roots @ [5,2,0,0], roots @ [5,1,1,0]]
      andalso bad_trace (roots @ forward) ``p /\ q``)

  val _ = control "ordinary malformed traces retain checked failures"
    (fn () => List.all (fn bytes => with_trace bytes (fn conf =>
      ((GEN_SAT conf; false) handle HOL_ERR _ => true
        | Domain => true | Subscript => true)))
      [[], [128], [2,0], [0,0,0], [6,0,0]])

  (* A deterministic compact replay with a nonempty definition map.  The
     source atom is compound, but resolution must use its schematic name
     until the shared root context has been discharged. *)
  val _ = control "compact resolution discharges roots before expansion"
    (fn () => with_trace (roots @ forward) (fn _ =>
      let
        val x = mk_var ("sat_compact", bool)
        val atom = ``(p:bool) /\ q``
        val source = mk_conj (atom, mk_neg atom)
        val premise = ASSUME source
        val clauses = Array.fromList
          [(x, CONJUNCT1 premise), (mk_neg x, CONJUNCT2 premise)]
        val lfn = Redblackmap.insert
          (Redblackmap.mkDict Term.var_compare, x, atom)
        val sva = Array.fromList [T, x]
        val result = minisatParse.replayProof sva 2 "unused" minisatp 1
          clauses lfn (SOME trace)
      in case result of
          NONE => false
        | SOME th => checked (mk_neg source) (NOT_INTRO (DISCH source th))
      end))
  val _ = control "proof-only file input checks the file endpoint"
    (fn () =>
      let
        val input = OS.FileSys.tmpName ()
        fun put text =
          let val out = TextIO.openOut input
          in TextIO.output (out, text); TextIO.closeOut out end
        val result = Exn.capture (fn () =>
          let
            val _ = put "p cnf 1 2\n1 0\n-1 0\n"
            val problem = dimacsTools.readDimacs input
            val conf = set_infile input (internal base_config)
            val _ = checked (mk_neg problem) (GEN_SAT_PROVE_ONLY conf)
              orelse raise Fail "DIMACS endpoint"
            val _ = put "p cnf 1 1\n1 0\n"
          in sat_only conf end) ()
        val _ = OS.FileSys.remove input
      in Exn.release result end)

  val _ = control "ordinary DIMACS endpoints and caller-owned files"
    (fn () =>
      let val input = OS.FileSys.tmpName ()
          val output = input ^ "." ^ getSolverName minisatp
          fun put text =
            let val out = TextIO.openOut input
            in dimacsTools.with_cleanup (fn () => TextIO.closeOut out)
                 (fn () => TextIO.output (out,text)) () end
          fun exists () = OS.FileSys.access (input,[])
      in dimacsTools.with_cleanup
        (fn () => dimacsTools.clean_files
          [input,output,output^".proof",output^".stats"])
        (fn () =>
          let val _ = put "p cnf 1 2\n1 0\n-1 0\n"
              val problem = dimacsTools.readDimacs input
              val conf = set_infile input base_config
              val external =
                if OS.FileSys.access (getSolverExe minisatp,
                                      [OS.FileSys.A_EXEC]) then
                  checked (mk_neg problem) (GEN_SAT conf) andalso exists ()
                else true
              val fallback = model (internal conf) problem andalso exists ()
              val _ = put "p cnf 1 1\n1 0\n"
              val sat = dimacsTools.readDimacs input
          in external andalso fallback andalso
             model (internal conf) sat andalso exists () end) ()
      end)

  (* Ordinary entries deliberately retain the historical explicit-CNF
     polarity/model contract; the proof-only entry is not a replacement. *)
  val _ = control "ordinary constant CNF keeps the zero-variable shortcut"
    (fn () => List.all (fn oracle =>
      let fun conf tm = set_flag_is_proved (not oracle) (config tm)
          fun falsity tm =
            (GEN_SAT (conf tm); false) handle SAT_cex th =>
              checked (mk_neg tm) th
      in checked T (GEN_SAT (conf T)) andalso falsity F andalso
         checked ``T /\ T`` (GEN_SAT (conf ``T /\ T``)) andalso
         falsity ``T /\ F`` end) [false,true])

  val _ = control "ordinary compound CNF external and fallback contracts"
    (fn () =>
      let val unsat = ``(P:bool->bool) T /\ ~P T /\ P F /\ ~P F``
          val sat = ``(P:bool->bool) T /\ ~P F``
          val atom_goal = ``((P:bool->bool) T /\ P F) ==> P F``
          val atom_bad = ``(P:bool->bool) T \/ P F``
          fun legacy_compound tm =
            ((GEN_SAT (internal (set_term tm base_config)); false)
             handle HOL_ERR e =>
               Feedback.top_structure_of e = "Term" andalso
               Feedback.top_function_of e = "dest_const" andalso
               Feedback.message_of e = "not a const")
      in (if OS.FileSys.access (getSolverExe minisatp,
                                 [OS.FileSys.A_EXEC]) then
            checked (mk_neg unsat) (GEN_SAT (config unsat)) andalso
            ((GEN_SAT (config sat); false) handle UNCHANGED => true)
          else true) andalso
         legacy_compound atom_goal andalso legacy_compound atom_bad andalso
         (* Legacy fallback proves the positive CNF, hence a refutable CNF
            raises a checked counterexample, not a refutation theorem. *)
         measured (internal (config cnf)) (fn conf => model conf cnf) andalso
         measured (internal (set_flag_is_proved false
                     (set_term valid base_config)))
           (fn conf => checked valid (GEN_SAT conf))
      end)

  val _ = control "compact malformed pivot preserves the old diagnostic"
    (fn () => with_trace (roots @ [5,20,1,0]) (fn _ =>
      let val x = mk_var ("sat_diagnostic", bool)
          val atom = ``p /\ q``
          val source = mk_conj (atom, mk_neg atom)
          val premise = ASSUME source
          val clauses = Array.fromList
            [(x, CONJUNCT1 premise), (mk_neg x, CONJUNCT2 premise)]
          val lfn = Redblackmap.insert
            (Redblackmap.mkDict Term.var_compare, x, atom)
      in (minisatParse.replayProof (Array.fromList [T,x]) 2 "unused"
            minisatp 1 clauses lfn (SOME trace); false)
         handle HOL_ERR e => Feedback.message_of e = "mk_sat_var10\n"
      end))

  val _ = control "ordinary false obligations are never certified"
    (fn () => List.all (fn bytes => with_trace bytes (fn conf =>
      let val th = GEN_SAT (set_term ``p /\ q`` conf)
      in not (concl th ~~ ``~(p /\ q)``) andalso null (hyp th) end
      handle HOL_ERR _ => true | Domain => true | Subscript => true
           | SAT_cex _ => true))
      [[2,0,0], roots, roots @ forward, roots @ backward])
  val _ = if not (OS.FileSys.access (getSolverExe minisatp,
                                     [OS.FileSys.A_EXEC])) then () else
    let
      val _ = control "external checked SAT/UNSAT and proof-only SAT"
        (fn () =>
          let val (_, stats) = satTools.with_solver_statistics (fn () =>
                if checked valid (SAT_PROVE valid) andalso
                   model (set_term invalid base_config) invalid andalso
                   sat_only (config compound) then () else raise Fail "SAT")
          in #external_calls stats = 3 andalso #internal_calls stats = 0 end)
      val _ = control "external oracle SAT/UNSAT stays distinct from checked"
        (fn () =>
          let fun oracle th =
                let val (names, axioms) = Tag.dest_tag (tag th)
                in null (hyp th) andalso null axioms andalso
                   List.exists (fn s => s = "HolSatLib") names end
              val th = SAT_ORACLE valid
              val sat = (SAT_ORACLE invalid; false) handle SAT_cex th =>
                oracle th andalso snd (dest_imp (concl th)) ~~ mk_neg invalid
          in concl th ~~ valid andalso oracle th andalso sat end)
    in () end
in
  val _ = ()
end
