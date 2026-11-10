(* Copyright (c) 2026 The HOL4 contributors.
   No top-level jobs: register run with the HolSmt selftest postludes. *)
structure SmtSolverCleanupTests =
struct
  exception Primary of unit ref
  exception Cleanup

  fun require text yes = if yes then () else raise Fail text
  fun test label action =
    (testutils.tprint label; action (); testutils.OK ())
  fun remove path = OS.FileSys.remove path handle OS.SysErr _ => ()
  fun temporary action =
    let val path = OS.FileSys.tmpName ()
    in SolverSpec.complete_owned (fn () => remove path) action path end
  fun put path text = SolverSpec.with_output_file path
    (fn stream => TextIO.output (stream,text))

  fun same_primary (Primary expected) (Primary actual) = expected=actual
    | same_primary (Fail expected) (Fail actual) = expected=actual
    | same_primary Interrupt Interrupt = true
    | same_primary (Timeout.TIMEOUT expected) (Timeout.TIMEOUT actual) =
        Time.compare (expected,actual)=EQUAL
    | same_primary (Feedback.HOL_ERR expected) (Feedback.HOL_ERR actual) =
        Feedback.top_structure_of expected=Feedback.top_structure_of actual
        andalso
        Feedback.top_function_of expected=Feedback.top_function_of actual
        andalso Feedback.message_of expected=Feedback.message_of actual
    | same_primary _ _ = false
  fun primaries () =
    [Primary (ref ()), Fail "injected parser failure", Interrupt,
     Timeout.TIMEOUT (Time.fromSeconds 7),
     Feedback.mk_HOL_ERR "SmtResource" "cleanup_test"
       "resource-gated: injected parser failure"]
  fun expect_primary expected action =
    case Exn.capture action () of
      Exn.Exn actual => require "primary exception replaced"
        (same_primary expected actual)
    | Exn.Res _ => raise Fail "expected primary exception"

  fun precedence () =
    List.app (fn primary =>
      let val calls = ref 0
          fun close () = (calls := !calls+1; raise Cleanup)
          val _ = expect_primary primary (fn () =>
            SolverSpec.complete_owned close (fn () => raise primary) ())
      in require "cleanup skipped or repeated" (!calls=1) end)
      (primaries ())

  (* Poly/ML may retain buffered suffixes even after closeIn. Descriptor
     counts below test release; do not mistake buffered text for a leak. *)
  fun acquisition () = temporary (fn path =>
    let
      val _ = put path "unread suffix"
      val saved = ref NONE
      val primary = Primary (ref ())
      val _ = expect_primary primary (fn () =>
        SolverSpec.with_input_file path (fn input =>
          (saved := SOME input; raise primary)))
      (* A regular input file cannot be an output directory. The second
         acquisition fails while the outer input descriptor is owned. *)
      val outcome = Exn.capture (fn () =>
        SolverSpec.with_input_file path (fn input =>
          (saved := SOME input;
           SolverSpec.with_output_file
             (OS.Path.concat (path,"missing")) (fn _ => ())))) ()
      val _ = require "second acquisition unexpectedly succeeded"
        (case outcome of Exn.Exn (IO.Io _) => true | _ => false)
    in () end)

  (* Optional Linux observation; all stream-invariant checks above and below
     are portable. Counting the directory's own descriptor is symmetric. *)
  fun fd_count () =
    if not (OS.FileSys.isDir "/proc/self/fd" handle OS.SysErr _ => false)
    then NONE
    else
      let val dir = OS.FileSys.openDir "/proc/self/fd"
          fun count n = case OS.FileSys.readDir dir of
              NONE => n | SOME _ => count (n+1)
      in SOME (SolverSpec.complete_owned
        (fn () => OS.FileSys.closeDir dir) count 0) end

  fun copy_acquisition () = temporary (fn source =>
    let
      val _ = put source "copy source"
      val target = OS.Path.concat (source,"missing")
      fun fails copy = case Exn.capture (fn () => copy source target) () of
          Exn.Exn (IO.Io _) => ()
        | _ => raise Fail "copy did not report output acquisition failure"
      val initial = fd_count ()
      val _ = List.app (fn _ =>
        (fails Z3.copy_file_bounded_memory; fails CVC.copy_file))
        (List.tabulate (32,fn n => n))
    in require "copy acquisition leaked descriptors"
      (fd_count ()=initial) end)

  fun legacy_post () = temporary (fn path =>
    let
      val goal = ([],boolSyntax.T)
      val (translation,_) = CVC.goal_to_SmtLib_with_get_proof_translation goal
      fun validation [theorem] = theorem
        | validation _ = raise Fail "unexpected validation input"
      val data = ((goal,goal,validation,[]),(translation,false))
      val saved = ref NONE
      val replays = ref 0
      fun replay _ _ =
        (replays := !replays+1;
         Thm.MP (Thm.NOT_ELIM
           (Thm.ASSUME (boolSyntax.mk_neg boolSyntax.T))) boolTheory.TRUTH)
      fun post parse = CVC.checked_post "cleanup_test" (fn _ => " test ")
        parse replay data path
      fun failing primary _ input =
        (saved := SOME input;
         require "fixture has no unread proof"
           (not (TextIO.endOfStream input));
         raise primary)
      val _ = put path "unsat\nunread proof suffix\n"
      val initial = fd_count ()
      val _ = List.app (fn primary =>
        List.app (fn _ =>
          expect_primary primary (fn () => post (failing primary)))
          (List.tabulate (16,fn n => n)))
        (primaries ())
      val ordinary = Feedback.mk_HOL_ERR "InjectedParser" "parse" "bad proof"
      val diagnostic = Exn.capture (fn () => post (failing ordinary)) ()
      val _ = require "ordinary parser context changed"
        (case diagnostic of Exn.Exn (Feedback.HOL_ERR detail) =>
           Feedback.top_structure_of detail="CVC" andalso
           Feedback.top_function_of detail="cleanup_test" andalso
           String.isSubstring "cvc5 proof parse failed\n"
             (Feedback.message_of detail) andalso
           String.isSubstring
             "underlying HOL_ERR: InjectedParser.parse: bad proof"
             (Feedback.message_of detail)
         | _ => false)
      val _ = require "failed parser reached replay" (!replays=0)
      val _ = require "failed parser leaked descriptors" (fd_count ()=initial)
      (* Exercise recovery on the very same existing callback boundary. *)
      val result = post (fn _ => fn input => (saved := SOME input; ()))
      val _ = require "checked post did not recover"
        (case result of SolverSpec.UNSAT (SOME theorem) =>
           null (Thm.hyp theorem) andalso
           Term.aconv (Thm.concl theorem) boolSyntax.T
         | _ => false)
      val _ = require "recovery replay count changed" (!replays=1)
      val _ = put path "sat\nunread suffix\n"
    in require "status-only post did not recover"
      (case post (fn _ => fn _ => raise Fail "unexpected parse") of
         SolverSpec.SAT NONE => !replays=1 | _ => false) end)

  (* Linux directory reads exercise the otherwise-uncovered scan/read
     failure AFTER openIn, for both status and version readers. Do not
     assume other platforms reject directory reads the same way. *)
  fun failed_reads () = if not (Option.isSome (fd_count ())) then () else
    temporary (fn path =>
    let
      val _ = remove path
      val _ = OS.FileSys.mkDir path
      fun work () =
        let
          val initial = fd_count ()
          fun fail scan = case Exn.capture scan path of
              Exn.Exn (IO.Io _) => ()
            | Exn.Exn (OS.SysErr _) => ()
            | Exn.Res (SolverSpec.UNKNOWN _) => ()
            | Exn.Exn error => raise error
            | _ => raise Fail "directory read produced a solver verdict"
          val _ = List.app (fn _ =>
            (fail Z3.is_sat_file; fail CVC.is_sat_file;
             require "directory version fallback changed"
               (Z3.parse_Z3_version path="0" andalso
                CVC.parse_cvc_version path=CPC_Proof.unknown_cvc_version)))
            (List.tabulate (32,fn n => n))
        in require "failed status/version read leaked descriptors"
          (fd_count ()=initial) end
    in SolverSpec.complete_owned (fn () => OS.FileSys.rmDir path) work () end)

  fun ordinary_diagnostics () = temporary (fn path =>
    let
      val _ = put path "not a version\n"
      val _ = require "malformed version fallback changed"
        (Z3.parse_Z3_version path="0" andalso
         CVC.parse_cvc_version path=CPC_Proof.unknown_cvc_version)
      val _ = remove path
    in require "missing version fallback changed"
      (Z3.parse_Z3_version path="0" andalso
       CVC.parse_cvc_version path=CPC_Proof.unknown_cvc_version) end)

  fun draining () = List.app (fn primary =>
    let val calls = ref ([]:int list)
        fun close n error () =
          (calls := !calls @ [n];case error of NONE => ()
           | SOME error => raise error)
        fun cleanup () = SolverSpec.cleanup_all
          [close 1 (SOME primary),close 2 (SOME Cleanup),close 3 NONE]
        val _ = expect_primary primary cleanup
    in require "independent cleanup skipped or changed order" (!calls=[1,2,3])
    end) (primaries ())

  (* Exercise the actual list/writer wrappers, not just the precedence
     combinator. The completion callback fails as well, after observing both
     temporary paths removed. Ordinary observers remain best-effort. *)
  fun wrapper_failures () =
    let
      val goal = ([],boolSyntax.T)
      fun one strict stage primary =
        let
          val paths = ref ([]:string list)
          val completed = ref 0
          val observations = ref ([]:string list)
          val posts = ref 0
          fun finish () =
            (completed := !completed+1;
             require "completion preceded temporary cleanup"
               (List.all (fn path => not (OS.FileSys.access (path,[])))
                 (!paths));
             raise Cleanup)
          fun pre _ = ((),fn output =>
            (output "query";if stage="writer" then raise primary else ()))
          fun capture _ key at source =
            (paths := key::source:: !paths;
             observations := !observations @ [at];
             if stage=at then raise primary else ())
          fun post _ _ =
            (posts := !posts+1;
             if stage="post" then raise primary else
               SolverSpec.UNSAT (SOME boolTheory.TRUTH))
          fun validate _ _ _ = if stage="validate" then raise primary else ()
          val call =
            SolverSpec.make_solver_with_capture_command_and_completion_writer_internal
              strict validate (fn _ => finish ()) (SOME capture) pre
              (fn _ => "true ") post
          val outcome = Exn.capture call goal
          val observing = stage="input" orelse stage="output"
          val propagates = not observing orelse
            (strict andalso SolverSpec.terminal_capture_exception primary)
          val _ = if propagates then
              (case outcome of Exn.Exn actual =>
                 require "wrapper replaced first exception"
                   (same_primary primary actual)
               | _ => raise Fail "wrapper suppressed primary")
            else require "ordinary observer changed result/cleanup policy"
              (case outcome of Exn.Exn Cleanup => true | _ => false)
          val _ = require "completion skipped or repeated" (!completed=1)
          val _ = require "temporary file leaked"
            (List.all (fn path => not (OS.FileSys.access (path,[]))) (!paths))
        in require "callback ordering changed"
          (if stage="writer" then null (!observations) andalso !posts=0
           else if stage="input" andalso propagates then
             !observations=["input"] andalso !posts=0
           else if stage="output" andalso propagates then
             !observations=["input","output"] andalso !posts=0
           else !observations=["input","output"] andalso !posts=1) end
    in Lib.with_flag (Library.trace,0) (fn () =>
      List.app (fn strict => List.app (fn stage =>
        List.app (one strict stage) (primaries ()))
        ["writer","input","output","post","validate"]) [false,true]) () end

  fun run () =
    (test "Solver cleanup preserves first exception" precedence;
     test "Solver stream ownership covers second acquisition" acquisition;
     test "Solver capture copy acquisition releases input" copy_acquisition;
     test "Solver failed status/version reads release input" failed_reads;
     test "Legacy checked_post parser failures close and recover" legacy_post;
     test "Solver version ordinary fallbacks unchanged" ordinary_diagnostics;
     test "Independent solver cleanup drains all actions" draining;
     test "Actual solver callbacks preserve first failure and remove files"
       wrapper_failures)
end
