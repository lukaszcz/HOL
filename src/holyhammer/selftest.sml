open testutils

fun join a b = OS.Path.concat (a, b)

fun write_file path contents =
  let
    val output = TextIO.openOut path
    val _ = TextIO.output (output, contents)
  in
    TextIO.closeOut output
  end

fun is_dir path = OS.FileSys.isDir path handle OS.SysErr _ => false

val mkdir = hhConfig.ensure_dir
val mkdirs = hhConfig.ensure_dir

fun remove_tree path =
  if is_dir path then
    let
      val stream = OS.FileSys.openDir path
      fun loop () =
        case OS.FileSys.readDir stream of
            NONE => OS.FileSys.closeDir stream
          | SOME name => (remove_tree (join path name); loop ())
      val _ = loop ()
    in
      OS.FileSys.rmDir path
    end
  else OS.FileSys.remove path
  handle OS.SysErr _ => ()

fun make_executable path =
  let
    val _ = write_file path "#!/bin/sh\nexit 0\n"
    val status = OS.Process.system ("/bin/chmod 700 " ^ path)
  in
    if OS.Process.isSuccess status then ()
    else raise Fail ("could not make executable " ^ path)
  end

fun expect message truth =
  (tprint message; if truth then OK () else die ("FAILED: " ^ message))

fun is_some expected actual = actual = SOME expected

fun has_parameter key value source =
  List.exists (fn (key', value', source') =>
    key = key' andalso value = value' andalso source = source')
    (hhConfig.hh_params ())

fun option_error fragments thunk =
  ((thunk (); false)
   handle Feedback.HOL_ERR error =>
     let val message = Feedback.message_of error
     in List.all (fn fragment => String.isSubstring fragment message) fragments
     end
        | _ => false)

fun test_child root =
  let
    val home = join root "home"
    val holdir = join root "holdir"
    val hammer = join (join home ".hol4") "hammer"
    val config = join hammer "config"
    val config_exec = join root "config-exec"
    val env_exec = join root "env-exec"
    val path_dir = join root "path"
    val path_exec = join path_dir "path-exec"
    val platform = hhConfig.platform ()
    val system_provers = join (join (join holdir "src") "holyhammer")
                              "provers"
    val user_provers = join hammer "provers"
    val state_provers = join (hhConfig.state_dir ()) "provers"
    fun install root version =
      let
        val dir = join (join root ("installprover-" ^ version)) platform
        val _ = mkdirs dir
        val file = join dir "install-exec"
      in
        make_executable file; file
      end
    val system_old = install system_provers "1.0"
    val system_new = install system_provers "2.0"
    val user_new = install user_provers "9.0"
    val state_exec =
      let
        val dir = join (join state_provers "stateprover-3.0") platform
        val _ = mkdirs dir
        val file = join dir "state-exec"
      in
        make_executable file; file
      end
    (* Pre-download-provers installations put the binary straight into
       provers/, with no version or platform directory. *)
    val flat_exec =
      let val file = join system_provers "flat-exec" in
        mkdirs system_provers; make_executable file; file
      end
    val _ = make_executable config_exec
    val _ = make_executable env_exec
    val _ = mkdirs path_dir
    val _ = make_executable path_exec
    val config_contents =
      ("# user configuration\n\
       \priority = user # comments are ignored\n\
       \integer = 42\n\
       \enabled = YeS\n\
       \path.value = ~/.fixture\n\
       \plain = key = value\n\
       \timeout = 21\n\
       \cores = 3\n\
       \prover.e.executable = " ^ config_exec ^ "\n")
    val _ = write_file config config_contents
    val _ = expect "state directory" (OS.FileSys.isDir (hhConfig.state_dir ()))
    val _ = expect "comment and assignment parsing"
      (is_some "key = value" (hhConfig.get "plain"))
    val _ = expect "user config overrides system config and environment"
      (is_some "user" (hhConfig.get "priority"))
    val _ = expect "environment key mangling"
      (is_some "environment" (hhConfig.get "mangled.key"))
    val expected_eval =
      case OS.Process.getEnv "HHEVAL_INTEGRATION_TEST" of
          SOME path =>
            (case OS.Process.getEnv "HOL4_HAMMER_EVAL_DIR" of
                 SOME directory => directory
               | NONE => path)
        | NONE => join (join (join holdir "src") "holyhammer") "eval"
    val _ = expect "built-in default"
      (is_some expected_eval (hhConfig.get "eval.dir"))
    val _ = expect "system configuration"
      (is_some "system only" (hhConfig.get "system.only"))
    val _ = expect "integer configuration"
      (hhConfig.get_int "integer" = SOME 42)
    val _ = expect "Boolean configuration"
      (hhConfig.get_bool "enabled" = SOME true)
    val _ = expect "path configuration"
      (is_some (join home ".fixture") (hhConfig.get_path "path.value"))
    val _ = expect "option config overrides option environment"
      (hhConfig.hh_get "timeout" = "21" andalso
       is_some "21" (hhConfig.get "timeout"))
    val _ = hhConfig.hh_set ("timeout", "23")
    val _ = expect "runtime option overrides config"
      (hhConfig.hh_get "timeout" = "23" andalso
       is_some "23" (hhConfig.get "timeout"))
    val _ = expect "unknown option is a descriptive HOL_ERR"
      (option_error ["unknown", "valid keys", "timeout"]
        (fn () => hhConfig.hh_set ("not_an_option", "1")))
    val _ = expect "unparsable option is a descriptive HOL_ERR"
      (option_error ["timeout", "positive integer", "valid keys"]
        (fn () => hhConfig.hh_set ("timeout", "not-an-integer")))
    val _ = expect "failed validation preserves the runtime value"
      (hhConfig.hh_get "timeout" = "23")
    val _ = expect "provers are registry-validated at set time"
      (option_error ["provers", "registered prover names"]
        (fn () => hhConfig.hh_set
          ("provers", "not-a-holyhammer-prover")))
    val _ = expect "unknown unset option is a HOL_ERR"
      (option_error ["unknown", "valid keys"]
        (fn () => hhConfig.hh_unset "not_an_option"))
    val _ = hhConfig.hh_set ("preplay_timeout", "2.5")
    val _ = hhConfig.hh_set ("minimize_timeout", "3.5")
    val _ = hhConfig.hh_set ("max_facts", "17")
    val _ = hhConfig.hh_set ("minimize", "off")
    val _ = hhConfig.hh_set ("cache", "yes")
    val _ = hhConfig.hh_set ("debug_dir", join root "debug")
    val options : hhConfig.hh_options = hhConfig.snapshot ()
    val _ = expect "snapshot parses values and computes slices"
      (#timeout options = 23 andalso #max_proofs options = 4 andalso
       #provers options = ["e", "vampire", "zipperposition"] andalso
       #cores options = 3 andalso #slices options = 72 andalso
       #filter options = "none" andalso #max_facts options = SOME 17 andalso
       not (#minimize options) andalso #cache options andalso
       #cache_dir options = join (hhConfig.state_dir ()) "cache" andalso
       #cache_max_entries options = 100000 andalso
       #debug_dir options = SOME (join root "debug"))
    val _ = expect "snapshot assigns reconstruction timeouts"
      (Real.abs (!hhReconstruct.reconstruction_timeout - 2.5) < 0.000001
       andalso
       Real.abs (!hhReconstruct.minimization_timeout - 3.5) < 0.000001)
    val _ = expect "hh_params reports all four provenance layers"
      (has_parameter "timeout" "23" "set" andalso
       has_parameter "cores" "3" "config" andalso
       has_parameter "filter" "none" "env" andalso
       has_parameter "max_proofs" "4" "default")
    val _ = hhConfig.print_params ()
    val _ = holyHammer.set_timeout 19
    val _ = expect "set_timeout updates the runtime option"
      (hhConfig.hh_get "timeout" = "19")
    val _ = hhConfig.hh_unset "timeout"
    val _ = expect "hh_unset restores config precedence"
      (hhConfig.hh_get "timeout" = "21")
    val _ = write_file config
      ("provers = not-a-holyhammer-prover\n" ^ config_contents)
    val _ = expect "provers are registry-validated at snapshot time"
      (option_error ["provers", "registered prover names"]
        (fn () => ignore (hhConfig.snapshot ())))
    val _ = write_file config config_contents
    val _ = hhConfig.hh_set ("provers", "e vampire")
    val _ = expect "registered prover lists round-trip"
      (#provers (hhConfig.snapshot ()) = ["e", "vampire"])
    val _ = hhConfig.hh_unset "provers"
    val _ = expect "configuration executable discovery"
      (is_some config_exec (hhConfig.find_exec "e" ["path-exec"]))
    val _ = write_file config
      ("priority = user # comments are ignored\n\
       \integer = 42\n\
       \enabled = YeS\n\
       \path.value = ~/.fixture\n\
       \plain = key = value\n\
       \eval.dir = config-eval\n")
    val _ = expect "configuration overrides the built-in default"
      (is_some "config-eval" (hhConfig.get "eval.dir"))
    val _ = expect "environment is effective after config removal"
      (hhConfig.hh_get "timeout" = "22" andalso
       has_parameter "timeout" "22" "env")
    val _ = expect "prover environment executable discovery"
      (is_some env_exec (hhConfig.find_exec "e" ["path-exec"]))
    val _ = expect "PATH executable discovery"
      (is_some path_exec (hhConfig.find_exec "pathprover" ["path-exec"]))
    val _ = expect "state-directory installation discovery"
      (is_some state_exec
       (hhConfig.find_exec "stateprover" ["state-exec"]))
    val _ = expect "newest system installation is preferred"
      (is_some system_new
       (hhConfig.find_exec "installprover" ["install-exec"]))
    val _ = expect "install search precedes user installation"
      (hhConfig.find_exec "installprover" ["install-exec"] <> SOME user_new)
    val _ = expect "older installation is not selected"
      (hhConfig.find_exec "installprover" ["install-exec"] <> SOME system_old)
    val _ = expect "legacy flat installation discovery"
      (is_some flat_exec (hhConfig.find_exec "flatprover" ["flat-exec"]))
    val _ = expect "versioned installation precedes the legacy layout"
      (is_some system_new
       (hhConfig.find_exec "installprover" ["install-exec"]))
    val _ = expect "dump reports provenance"
      (List.exists (fn (key, value) =>
         key = "priority" andalso String.isPrefix "config: " value)
       (hhConfig.dump ()))
  in
    ()
  end

fun make_fixture root =
  let
    val home = join root "home"
    val holdir = join root "holdir"
    val hammer = join (join home ".hol4") "hammer"
    val _ = mkdirs hammer
    val _ = mkdirs (join holdir "etc")
    val _ = write_file (join (join holdir "etc") "hammer-config")
      "priority = system\nplain = system value\nsystem.only = system only\n"
  in
    (home, holdir, join root "path", join root "env-exec")
  end

fun run_parent () =
  let
    val root = OS.FileSys.tmpName ()
    val _ = OS.FileSys.remove root handle OS.SysErr _ => ()
    val _ = OS.FileSys.mkDir root
    val (home, holdir, path, env_exec) = make_fixture root
    val command =
      "/usr/bin/env HOL4_HAMMER_PRIORITY=environment" ^
      " HOL4_HAMMER_MANGLED_KEY=environment" ^
      " HOL4_HAMMER_TIMEOUT=22" ^
      " HOL4_HAMMER_FILTER=none" ^
      " HOL4_EPROVER_EXECUTABLE=" ^ env_exec ^
      " HOL4_HAMMER_DIR=" ^ join root "state" ^
      " HHCONFIG_TEST_ROOT=" ^ root ^
      " HOLDIR=" ^ holdir ^
      " PATH=" ^ path ^
      " ./selftest.exe"
    val env_command =
      "/usr/bin/env HOL4_HAMMER_EVAL_DIR=environment-eval" ^
      " HHCONFIG_ENV_DEFAULT_TEST=environment-eval" ^
      " HHCONFIG_TEST_ROOT=" ^ root ^
      " HOLDIR=" ^ holdir ^
      " PATH=" ^ path ^
      " ./selftest.exe"
    val _ = tprint "hhConfig hermetic selftests"
    val first = OS.Process.system command
    val _ = write_file (join (join (join home ".hol4") "hammer")
                            "config") "# no eval.dir here\n"
    val second = OS.Process.system env_command
    val _ = remove_tree root
  in
    if OS.Process.isSuccess first andalso OS.Process.isSuccess second then OK ()
    else die "FAILED: hhConfig child selftest"
  end

fun test_environment_default value =
  let
    val options : hhConfig.hh_options = hhConfig.snapshot ()
    val _ = expect "environment overrides the built-in default"
      (is_some value (hhConfig.get "eval.dir"))
    val _ = expect "effective timeout default is 30"
      (#timeout options = 30 andalso hhConfig.hh_get "timeout" = "30" andalso
       has_parameter "timeout" "30" "default")
    val _ = expect "default cores and slices are computed"
      (#cores options > 0 andalso #slices options = 24 * #cores options)
    val _ = expect "empty option defaults map to NONE"
      (#max_facts options = NONE andalso #debug_dir options = NONE)
  in
    ()
  end

val _ =
  case OS.Process.getEnv "HHCONFIG_TEST_ROOT" of
      NONE => run_parent ()
    | SOME root =>
      (case OS.Process.getEnv "HHCONFIG_ENV_DEFAULT_TEST" of
           SOME value => test_environment_default value
         | NONE => test_child root)

fun read_lines path =
  let
    val input = TextIO.openIn path
    fun loop lines =
      case TextIO.inputLine input of
          NONE => List.rev lines
        | SOME line => loop (line :: lines)
    val lines = loop []
    val _ = TextIO.closeIn input
  in
    lines
  end

fun expect_equal message expected actual =
  expect message (expected = actual)

fun prover name =
  case hhProver.lookup name of
      SOME config => config
    | NONE => raise Fail ("missing prover " ^ name)

val sample_request : hhProver.run_request =
  {timeout = 7, problem = "problem.p", extra = ["--extra"],
   debug_dir = NONE}

fun test_recording file parser expected_szs expected_axioms =
  let
    val (szs, axioms) = parser (read_lines (join "test-data" file))
    val _ = expect_equal ("recording status " ^ file) expected_szs szs
  in
    expect_equal ("recording axioms " ^ file) expected_axioms axioms
  end

fun test_szs_status_words () =
  let
    val words =
      ["Theorem", "Unsatisfiable", "CounterSatisfiable", "Satisfiable",
       "GaveUp", "Unknown", "Incomplete", "Timeout", "ResourceOut",
       "MemoryOut", "Forced", "User", "Inappropriate", "NewStatus"]
    val expected =
      [hhProver.SzsTheorem, hhProver.SzsTheorem,
       hhProver.SzsCounterSat, hhProver.SzsSatisfiable,
       hhProver.SzsGaveUp, hhProver.SzsGaveUp, hhProver.SzsGaveUp,
       hhProver.SzsTimeout, hhProver.SzsResourceOut,
       hhProver.SzsResourceOut, hhProver.SzsGaveUp, hhProver.SzsGaveUp,
       hhProver.SzsInappropriate, hhProver.SzsUnknown "NewStatus"]
    val actual = map (fn word =>
      hhProver.szs_of_line ("% SZS status " ^ word ^ " for problem"))
      words
  in
    expect_equal "SZS status words" (map SOME expected) actual
  end

fun test_hhProver () =
  let
    val e = prover "e"
    val vampire = prover "vampire"
    val zipperposition = prover "zipperposition"
    val z3 = prover "z3"
    val e_legacy = prover "e-legacy"
    val vampire_legacy = prover "vampire-legacy"
    val names = map #name (hhProver.all ())
    val _ = expect "all built-in provers"
      (names = ["e", "vampire", "zipperposition", "z3", "e-legacy",
                "vampire-legacy"])
    val _ = expect "default provers are found and non-legacy"
      (List.all (fn name => not (#legacy (prover name)))
       (hhProver.default_provers ()))
    val _ = expect "legacy entries reuse modern executable discovery"
      (hhProver.find_exec e_legacy = hhProver.find_exec e andalso
       hhProver.find_exec vampire_legacy = hhProver.find_exec vampire)
    val _ = expect "duplicate prover names are rejected"
      ((hhProver.register e; false) handle Fail _ => true)
    val _ = test_recording "e-theorem-chatter.out" (#parse_output e)
      hhProver.SzsTheorem (SOME ["keep_name"])
    val _ = test_recording "e-counter-sat.out" (#parse_output e)
      hhProver.SzsCounterSat NONE
    val _ = test_recording "e-gave-up.out" (#parse_output e)
      hhProver.SzsGaveUp NONE
    val _ = test_recording "vampire-theorem.out" (#parse_output vampire)
      hhProver.SzsTheorem (SOME ["keep_name"])
    val _ = test_recording "vampire-counter-sat.out" (#parse_output vampire)
      hhProver.SzsCounterSat NONE
    val _ = test_recording "vampire-timeout.out" (#parse_output vampire)
      hhProver.SzsTimeout NONE
    val _ = test_recording "vampire-legacy-timeout.out"
      (#parse_output vampire_legacy) hhProver.SzsTimeout NONE
    val _ = test_recording "z3-tptp-theorem.out" (#parse_output z3)
      hhProver.SzsTheorem (SOME ["keep_name"])
    val _ = test_recording "zipperposition-theorem.out"
      (#parse_output zipperposition) hhProver.SzsTheorem
      (SOME ["keep_name"])
    val _ = test_recording "zipperposition-counter-sat.out"
      (#parse_output zipperposition) hhProver.SzsCounterSat NONE
    val _ = test_recording "zipperposition-gave-up.out"
      (#parse_output zipperposition) hhProver.SzsGaveUp NONE
    val _ = test_recording "zipperposition-timeout.out"
      (#parse_output zipperposition) hhProver.SzsResourceOut NONE
    val _ = expect_equal "E version parser" (SOME "3.2.5-ho")
      (#parse_version e (String.concat (read_lines "test-data/e-version.out")))
    val _ = expect_equal "Vampire version parser" (SOME "5.0.1")
      (#parse_version vampire
       (String.concat (read_lines "test-data/vampire-version.out")))
    val _ = expect_equal "Zipperposition version parser" (SOME "2.1")
      (#parse_version zipperposition
       (String.concat (read_lines "test-data/zipperposition-version.out")))
    val _ = expect_equal "Z3 TPTP version parser" (SOME "4.11.2.0")
      (#parse_version z3 "Z3tptp [4.11.2.0] (c) Microsoft Corp.")
    val _ = expect_equal "E command"
      ("e", ["--auto-schedule", "--tstp-in", "--tstp-out", "-s",
             "--cpu-limit=7", "--proof-object=1", "--extra", "problem.p"])
      (#mk_command e "e" sample_request)
    val _ = expect_equal "Vampire command"
      ("vampire", ["--mode", "portfolio", "--schedule", "casc",
        "--input_syntax", "tptp", "--proof", "tptp",
        "--output_axiom_names", "on", "-t", "7", "--input_file",
        "--extra", "problem.p"])
      (#mk_command vampire "vampire" sample_request)
    val _ = expect_equal "Zipperposition command"
      ("zipperposition", ["--input", "tptp", "--output", "tptp",
        "--timeout", "7", "--extra", "problem.p"])
      (#mk_command zipperposition "zipperposition" sample_request)
    val _ = expect_equal "Z3 legacy command"
      ("z3", ["-tptp", "DISPLAY_UNSAT_CORE=true",
        "ELIM_QUANTIFIERS=true", "PULL_NESTED_QUANTIFIERS=true", "-T:7",
        "--extra", "problem.p"])
      (#mk_command z3 "z3" sample_request)
    val _ = expect_equal "Z3 standalone TPTP command"
      ("z3_tptp", ["-c", "-smt.pull_nested_quantifiers:true", "-t:7",
        "--extra", "-file:problem.p"])
      (#mk_command z3 "z3_tptp" sample_request)
    val _ = expect_equal "E legacy command"
      ("e", ["-s", "--cpu-limit=7", "--auto-schedule", "--tstp-in",
        "-R", "--print-statistics", "-p", "--tstp-format", "--extra",
        "problem.p"])
      (#mk_command e_legacy "e" sample_request)
    val _ = expect_equal "Vampire legacy command"
      ("vampire", ["--time_limit", "7", "--proof", "tptp",
        "--output_axiom_names", "on", "--extra", "problem.p"])
      (#mk_command vampire_legacy "vampire" sample_request)
  in
    ()
  end

fun slice_options provers slices cores timeout filter max_facts
    : hhConfig.hh_options =
  {timeout = timeout, max_proofs = 4, provers = provers, slices = slices,
   cores = cores, filter = filter, max_facts = max_facts, minimize = true,
   preplay_timeout = 1.0, minimize_timeout = 1.0, cache = false,
   cache_dir = "", cache_max_entries = 100000, debug_dir = NONE}

fun slice_summary (slice : hhProver.slice) =
  (#prover slice, #format slice, #type_enc slice, #lam_trans slice,
   #nfacts slice, #filter slice, #extra_opts slice, #slice_size slice)

fun schedule_summary
    (schedule : (hhProver.prover_config * hhProver.slice) list) =
  map (fn ((config : hhProver.prover_config),
           (slice : hhProver.slice)) =>
    (#name config, #nfacts slice, #filter slice, #extra_opts slice)) schedule

fun test_hhSlice () =
  let
    val vampire_options = ["--mode", "portfolio", "--schedule", "casc"]
    fun expected prover nfacts extra =
      (prover, "fof", "", "", nfacts, "knn", extra, 1)
    val e_slices = map slice_summary (#slices (prover "e") ())
    val vampire_slices = map slice_summary (#slices (prover "vampire") ())
    val zipperposition_slices =
      map slice_summary (#slices (prover "zipperposition") ())
    val _ = expect_equal "E slice table"
      [expected "e" 128 ["--auto-schedule"],
       expected "e" 512 ["--auto-schedule"],
       expected "e" 32 ["--auto"],
       expected "e" 1024 ["--auto-schedule"]] e_slices
    val _ = expect_equal "Vampire slice table"
      [expected "vampire" 96 vampire_options,
       expected "vampire" 512 vampire_options,
       expected "vampire" 32 vampire_options,
       expected "vampire" 1024 vampire_options] vampire_slices
    val _ = expect_equal "Zipperposition slice table"
      [expected "zipperposition" 128 [],
       expected "zipperposition" 512 [],
       expected "zipperposition" 32 []] zipperposition_slices
    val _ = expect "legacy one-shot provers have no slices"
      (List.all (null o (fn config => #slices config ()))
       (map prover ["z3", "e-legacy", "vampire-legacy"]))
    val _ = expect_equal "rotation truncates to requested slice count"
      ["vampire", "e", "zipperposition", "vampire", "e"]
      (hhSlice.schedule_of_provers
        ["e", "vampire", "zipperposition"] 5)
    val _ = expect_equal "rotation filters and extends in requested order"
      ["e", "zipperposition", "e", "zipperposition", "e",
       "zipperposition", "e"]
      (hhSlice.schedule_of_provers ["zipperposition", "e"] 7)
    val defaults = slice_options ["e", "vampire", "zipperposition"]
      (24 * 32) 32 30 "knn" NONE
    val default_schedule = hhSlice.mk_schedule defaults
    val expected_default =
      [("vampire", 96, "knn", vampire_options),
       ("e", 128, "knn", ["--auto-schedule"]),
       ("zipperposition", 128, "knn", []),
       ("vampire", 512, "knn", vampire_options),
       ("e", 512, "knn", ["--auto-schedule"]),
       ("vampire", 32, "knn", vampire_options),
       ("zipperposition", 512, "knn", []),
       ("vampire", 1024, "knn", vampire_options),
       ("e", 32, "knn", ["--auto"]),
       ("e", 1024, "knn", ["--auto-schedule"]),
       ("zipperposition", 32, "knn", [])]
    val _ = expect_equal "default options produce all eleven slices"
      expected_default (schedule_summary default_schedule)
    val small = hhSlice.mk_schedule
      (slice_options ["e", "vampire", "zipperposition"] 5 2 30 "knn"
        NONE)
    val _ = expect_equal "small schedule follows the golden rotation"
      (List.take (expected_default, 5)) (schedule_summary small)
    val subset = hhSlice.mk_schedule
      (slice_options ["zipperposition", "e"] 7 4 30 "knn" NONE)
    val _ = expect_equal "prover subset consumes each table head-first"
      [("e", 128, "knn", ["--auto-schedule"]),
       ("zipperposition", 128, "knn", []),
       ("e", 512, "knn", ["--auto-schedule"]),
       ("zipperposition", 512, "knn", []),
       ("e", 32, "knn", ["--auto"]),
       ("zipperposition", 32, "knn", []),
       ("e", 1024, "knn", ["--auto-schedule"])]
      (schedule_summary subset)
    val overridden = hhSlice.mk_schedule
      (slice_options ["e"] 20 2 30 "none" (SOME 40))
    val _ = expect_equal "fact and filter overrides precede deduplication"
      [("e", 40, "none", ["--auto-schedule"]),
       ("e", 32, "none", ["--auto"])]
      (schedule_summary overridden)
    val exhausted = hhSlice.mk_schedule
      (slice_options ["e", "vampire", "zipperposition"] 100 8 30 "knn"
        NONE)
    val _ = expect "rotation exhaustion stops at eleven unique slices"
      (length exhausted = 11)
    val _ = expect "Z3 remains outside the slice scheduler"
      (null (hhSlice.mk_schedule
        (slice_options ["z3"] 100 8 30 "knn" NONE)))
    val first_slice = #2 (hd default_schedule)
    val large_slice : hhProver.slice =
      {prover = #prover first_slice, format = #format first_slice,
       type_enc = #type_enc first_slice, lam_trans = #lam_trans first_slice,
       nfacts = #nfacts first_slice, filter = #filter first_slice,
       extra_opts = #extra_opts first_slice, slice_size = 3}
    fun close expected actual = Real.abs (expected - actual) < 0.000001
    val _ = expect "budget uses full timeout when slices fit on cores"
      (close 30.0 (hhSlice.slice_budget (length default_schedule) defaults
        first_slice))
    val budget_options = slice_options ["e"] 999 32 30 "knn" NONE
    val _ = expect "budget arithmetic uses ceiling batches"
      (close 15.0 (hhSlice.slice_budget 33 budget_options first_slice) andalso
       close 15.0 (hhSlice.slice_budget 64 budget_options first_slice) andalso
       close 10.0 (hhSlice.slice_budget 65 budget_options first_slice) andalso
       close 30.0 (hhSlice.slice_budget 65 budget_options large_slice) andalso
       close 0.0 (hhSlice.slice_budget 0 budget_options first_slice))
  in
    ()
  end

fun contains needle haystack =
  String.isSubstring needle haystack

fun main_hh_error names =
  let
    val saved = !holyHammer.all_atps
    fun restore result = (holyHammer.all_atps := saved; result)
    fun call () =
      ignore (holyHammer.main_hh "" mlThmData.empty_thmdata
        ([], boolSyntax.T))
  in
    holyHammer.all_atps := names;
    ((call (); restore NONE)
     handle Feedback.HOL_ERR error =>
       restore (SOME (Feedback.message_of error))
          | exn => (holyHammer.all_atps := saved; raise exn))
  end

fun test_holyHammer_validation () =
  let
    val unknown = "not-a-holyhammer-prover"
    val _ = holyHammer.lemmas_glob := SOME ["stale-result"]
    val message = main_hh_error [unknown]
    val _ = expect "failed calls clear saved HolyHammer lemmas"
      (not (Option.isSome (!holyHammer.lemmas_glob)))
    val _ = expect "all_atps rejects unknown registry names"
      (case message of
           SOME text =>
             contains unknown text andalso
             contains
               ("known provers: e, vampire, zipperposition, z3, " ^
                "e-legacy, vampire-legacy") text
         | NONE => false)
  in
    case OS.Process.getEnv "HHCONFIG_TEST_ROOT" of
        NONE => ()
      | SOME _ =>
          let
            val output = OS.FileSys.tmpName ()
            val message = smlRedirect.hide_in_file output
              (fn () => main_hh_error ["zipperposition"]) ()
            val printed = String.concat (read_lines output)
            val _ = OS.FileSys.remove output
          in
            expect "no-prover path prints downloader hint"
              (contains "tools/download-provers" printed andalso
               case message of
                   SOME text => contains "tools/download-provers" text
                 | NONE => false)
          end
  end

fun fake_config name exec_name args parser : hhProver.prover_config =
  {name = name, exec_names = [exec_name], env_var = "",
   version_args = ["--version"], parse_version = fn _ => SOME "test",
   tested_versions = ["test"],
   mk_command = fn executable => fn _ => (executable, args),
   parse_output = parser, default_nfacts = 0, slices = fn () => [],
   legacy = false}

fun wait_until deadline predicate =
  if predicate () then true
  else if Time.> (Time.now (), deadline) then false
  else
    (OS.Process.sleep (Time.fromMilliseconds 20);
     wait_until deadline predicate)

fun pid_from_output output =
  case String.tokens Char.isSpace output of
      word :: _ =>
        (case Int.fromString word of
             SOME number =>
               Posix.Process.wordToPid (SysWord.fromInt number)
           | NONE => raise Fail "fixture printed a non-numeric pid")
    | [] => raise Fail "fixture did not print its child pid"

fun process_is_gone pid =
  let
    val signal_zero = Posix.Signal.fromWord 0w0
  in
    ((Posix.Process.kill (Posix.Process.K_PROC pid, signal_zero); false)
     handle OS.SysErr (_, SOME error) => OS.errorName error = "ESRCH")
  end

fun test_runner_load parser =
  let
    val workers = 24
    val config = fake_config "runner-load" "/bin/echo"
      ["% SZS status Theorem"] parser
    val request : hhProver.run_request =
      {timeout = 2, problem = "unused", extra = [], debug_dir = NONE}
    val _ = ignore (hhProver.probe config)
    val _ = hhProver.reset_spawn_count ()
    val result_mutex = Mutex.mutex ()
    val finished = ref 0
    val passed = ref 0
    fun note success =
      let
        val _ = Mutex.lock result_mutex
        val _ = finished := !finished + 1
        val _ = if success then passed := !passed + 1 else ()
      in
        Mutex.unlock result_mutex
      end
    fun worker () =
      let
        val running = hhProver.run_async config request
        val result = #wait running ()
      in
        note (#szs result = hhProver.SzsTheorem)
      end
      handle _ => note false
    val _ = List.tabulate (workers, fn _ => Thread.fork (worker, []))
    fun all_finished () =
      let
        val _ = Mutex.lock result_mutex
        val done = !finished = workers
        val _ = Mutex.unlock result_mutex
      in
        done
      end
    val completed = wait_until
      (Time.+ (Time.now (), Time.fromSeconds 15)) all_finished
    val _ = Mutex.lock result_mutex
    val successes = !passed
    val _ = Mutex.unlock result_mutex
    val _ = expect "runner concurrent load completes"
      (completed andalso successes = workers)
    val _ = expect "runner spawn counter counts concurrent forks"
      (hhProver.spawn_count () = workers)
  in
    ()
  end

fun test_runner () =
  case OS.Process.getEnv "HHCONFIG_TEST_ROOT" of
      SOME _ => ()
    | NONE =>
  let
    val e = prover "e"
    val good = fake_config "runner-good" "/bin/echo"
      ["% SZS status Theorem"] (#parse_output e)
    val debug_dir = OS.FileSys.tmpName ()
    val _ = remove_tree debug_dir
    val good_request : hhProver.run_request =
      {timeout = 1, problem = "unused", extra = [], debug_dir = SOME debug_dir}
    val good_result = hhProver.run good good_request
    val _ = expect "runner parses stdout"
      (#szs good_result = hhProver.SzsTheorem)
    val _ = expect "runner saves debug output"
      (OS.FileSys.access (#output_file good_result, [OS.FileSys.A_READ]))
    val _ = remove_tree debug_dir
    val timeout = fake_config "runner-timeout" "/bin/sleep" ["30"]
      (#parse_output e)
    val timeout_request : hhProver.run_request =
      {timeout = 0, problem = "unused", extra = [], debug_dir = NONE}
    val timeout_result = hhProver.run timeout timeout_request
    val _ = expect "runner watchdog timeout"
      (#szs timeout_result = hhProver.SzsTimeout orelse
       #szs timeout_result = hhProver.SzsResourceOut)
    val killed = fake_config "runner-killed" "/bin/sleep" ["30"]
      (#parse_output e)
    val kill_request : hhProver.run_request =
      {timeout = 30, problem = "unused", extra = [], debug_dir = NONE}
    val running_sleep = hhProver.run_async killed kill_request
    val _ = #kill running_sleep ()
    val _ = #kill running_sleep ()
    val killed_result = #wait running_sleep ()
    val killed_result_again = #wait running_sleep ()
    val _ = expect "runner kill returns before child exit"
      (#szs killed_result = hhProver.SzsTimeout andalso
       #szs killed_result_again = hhProver.SzsTimeout andalso
       Real.== (#time killed_result, #time killed_result_again) andalso
       #time killed_result < 5.0)
    val fixture_dir = "test-data"
    val printer_path = join fixture_dir "runner-print-e.sh"
    val printer = fake_config "runner-printer" printer_path []
      (#parse_output e)
    val printer_dir = OS.FileSys.tmpName ()
    val _ = remove_tree printer_dir
    val printer_request : hhProver.run_request =
      {timeout = 2, problem = "unused", extra = [],
       debug_dir = SOME printer_dir}
    val printer_result = hhProver.run printer printer_request
    val printed = String.concat (read_lines (#output_file printer_result))
    val recorded = String.concat
      (read_lines (join fixture_dir "e-theorem-chatter.out"))
    val _ = expect "runner captures stdout intact"
      (#szs printer_result = hhProver.SzsTheorem andalso
       printed = recorded)
    val _ = remove_tree printer_dir
    val forking_path = join fixture_dir "runner-forking-sleeper.sh"
    val forking = fake_config "runner-forking" forking_path []
      (#parse_output e)
    val forking_dir = OS.FileSys.tmpName ()
    val _ = remove_tree forking_dir
    val forking_request : hhProver.run_request =
      {timeout = 30, problem = "unused", extra = [],
       debug_dir = SOME forking_dir}
    val running_fork = hhProver.run_async forking forking_request
    val _ = OS.Process.sleep (Time.fromMilliseconds 200)
    val _ = #kill running_fork ()
    val forking_result = #wait running_fork ()
    val grandchild = pid_from_output
      (String.concat (read_lines (#output_file forking_result)))
    val grandchild_gone = wait_until
      (Time.+ (Time.now (), Time.fromSeconds 5))
      (fn () => process_is_gone grandchild)
    val _ = expect "runner group kill reaps grandchild" grandchild_gone
    val _ = remove_tree forking_dir
    val exec_failure : hhProver.prover_config =
      {name = "runner-exec-failure", exec_names = ["/bin/true"],
       env_var = "", version_args = [], parse_version = fn _ => SOME "test",
       tested_versions = ["test"],
       mk_command = fn _ => fn _ =>
         ("/definitely/missing/holyhammer-prover", []),
       parse_output = #parse_output e, default_nfacts = 0,
       slices = fn () => [], legacy = false}
    val exec_result = hhProver.run exec_failure timeout_request
    val _ = expect "runner exec failure returns RunFailure"
      (case #szs exec_result of hhProver.RunFailure _ => true | _ => false)
    val missing : hhProver.prover_config =
      {name = "runner-missing", exec_names = ["missing-hh-prover"],
       env_var = "", version_args = [], parse_version = fn _ => NONE,
       tested_versions = [],
       mk_command = fn executable => fn _ => (executable, []),
       parse_output = #parse_output e, default_nfacts = 0,
       slices = fn () => [], legacy = false}
    val missing_result = hhProver.run missing timeout_request
    val _ = expect "missing prover names downloader"
      (case #szs missing_result of
           hhProver.RunFailure message =>
             contains "tools/download-provers" message
         | _ => false)
    val _ = test_runner_load (#parse_output e)
  in
    ()
  end

fun write_tiny_problem () =
  let
    val path = OS.FileSys.tmpName ()
    val _ = write_file path
      "fof(thm_2Ekeep__name, axiom, p).\nfof(conjecture, conjecture, p).\n"
  in
    path
  end

fun test_installed_prover problem config =
  case hhProver.probe config of
      NONE => (tprint ("runner smoke " ^ #name config ^ " (skipped: absent)");
               OK ())
    | SOME _ =>
        let
          val request : hhProver.run_request =
            {timeout = 5, problem = problem, extra = [], debug_dir = NONE}
          val result = hhProver.run config request
        in
          expect ("runner smoke " ^ #name config)
            (#szs result = hhProver.SzsTheorem)
        end

fun test_installed_provers () =
  case OS.Process.getEnv "HHCONFIG_TEST_ROOT" of
      SOME _ => ()
    | NONE =>
        let
          val problem = write_tiny_problem ()
          val _ = List.app (test_installed_prover problem)
            (map prover ["e", "vampire", "zipperposition", "z3"])
          val _ = OS.FileSys.remove problem handle OS.SysErr _ => ()
        in
          ()
        end

fun same_real left right = Real.== (left, right)

fun same_real_option NONE NONE = true
  | same_real_option (SOME left) (SOME right) = same_real left right
  | same_real_option _ _ = false

fun same_journal_entry (expected : hhEval.journal_entry)
    (actual : hhEval.journal_entry) =
  #run expected = #run actual andalso #thy expected = #thy actual andalso
  #thm expected = #thm actual andalso
  #goal_id expected = #goal_id actual andalso
  #cond expected = #cond actual andalso
  hhEval.string_of_regime (#regime expected) =
    hhEval.string_of_regime (#regime actual) andalso
  hhEval.string_of_selector (#selector expected) =
    hhEval.string_of_selector (#selector actual) andalso
  #prover expected = #prover actual andalso
  #prover_version expected = #prover_version actual andalso
  #nfacts expected = #nfacts actual andalso
  #timeout expected = #timeout actual andalso
  #szs expected = #szs actual andalso
  same_real (#t_prover expected) (#t_prover actual) andalso
  #axioms_used expected = #axioms_used actual andalso
  #recon_ok expected = #recon_ok actual andalso
  #recon_method expected = #recon_method actual andalso
  same_real_option (#t_recon expected) (#t_recon actual) andalso
  #stac expected = #stac actual andalso #error expected = #error actual

fun test_hhEval root =
  let
    val holdir = join root "holdir"
    val sigobj = join holdir "sigobj"
    val src = join holdir "src"
    val _ = mkdirs sigobj
    val _ = mkdirs (join (join (join src "one") ".hol") "objs")
    val _ = mkdirs (join (join (join src "two") ".hol") "objs")
    val _ = write_file (join sigobj "SRCFILES")
      (join src "one/listTheory" ^ "\n" ^
       join src "two/arithmeticTheory" ^ "\n")
    val _ = write_file (join (join (join (join src "one") ".hol") "objs")
      "listTheory.dat") ""
    val _ = write_file (join (join (join (join src "two") ".hol") "objs")
      "arithmeticTheory.dat") ""
    val _ = write_file (join (join (join (join src "two") ".hol") "objs")
      "missingTheory.dat") ""
    val coverage = hhEval.stdlib_coverage ()
    val _ = expect_equal "SRCFILES corpus parser"
      ["arithmetic", "list"] (#srcfiles coverage)
    val _ = expect_equal "coverage check records discrepancy" ["missing"]
      (#added_from_dat coverage)
    val _ = expect_equal "stdlib corpus explicitly adds discrepancy"
      ["arithmetic", "list", "missing"] (hhEval.stdlib_theories ())
    val expdir = join root "hheval"
    val _ = remove_tree expdir
    val journal = hhEval.journal_path expdir "list"
    val null_entry : hhEval.journal_entry =
      {run = "fixture", thy = "list", thm = "nil", goal_id = "list.nil",
       cond = "deps-e", regime = hhEval.Bushy, selector = hhEval.Deps,
       prover = "e", prover_version = NONE, nfacts = 0, timeout = 5,
       szs = "BrokenDeps", t_prover = 0.0, axioms_used = NONE,
       recon_ok = NONE, recon_method = NONE, t_recon = NONE, stac = NONE,
       error = NONE}
    val full_entry : hhEval.journal_entry =
      {run = "fixture", thy = "list", thm = "cons", goal_id = "list.cons",
       cond = "knn-e", regime = hhEval.Chainy, selector = hhEval.Knn 128,
       prover = "e", prover_version = SOME "3.2.5", nfacts = 128,
       timeout = 10, szs = "Theorem", t_prover = 1.25,
       axioms_used = SOME ["list.nil", "arithmetic.add"], recon_ok = SOME true,
       recon_method = SOME "metis", t_recon = SOME 0.5,
       stac = SOME "metis_tac [list_nil]", error = SOME "fixture"}
    val _ = expect "journal null-field round trip"
      (same_journal_entry null_entry
       (hhEval.parse_journal_line (hhEval.encode_journal_line null_entry)))
    val _ = expect "journal populated-field round trip"
      (same_journal_entry full_entry
       (hhEval.parse_journal_line (hhEval.encode_journal_line full_entry)))
    val _ = hhEval.append_journal journal null_entry
    val _ = hhEval.append_journal journal full_entry
    val entries = hhEval.read_journal journal
    val _ = expect "journal append flushes both lines"
      (length entries = 2 andalso same_journal_entry null_entry (hd entries))
    val complete = [("list.nil", "deps-e"), ("list.cons", "knn-e")]
    val _ = expect "resume complete journal"
      (hhEval.journal_complete journal complete)
    val corrupt = TextIO.openAppend journal
    val _ = TextIO.output (corrupt, "{interrupted-write")
    val _ = TextIO.closeOut corrupt
    val _ = expect "resume ignores a truncated final journal record"
      (hhEval.journal_complete journal complete andalso
       length (hhEval.read_journal journal) = 2)
    val partial = hhEval.journal_path expdir "partial"
    val _ = hhEval.append_journal partial null_entry
    val _ = expect "resume partial journal"
      (not (hhEval.journal_complete partial complete))
    val empty = hhEval.journal_path expdir "empty"
    val _ = expect "resume empty journal"
      (not (hhEval.journal_complete empty complete))
    val retry = hhEval.journal_path expdir "retry"
    val retry_entry : hhEval.journal_entry =
      {run = "fixture", thy = "list", thm = "nil", goal_id = "list.nil",
       cond = "deps-e", regime = hhEval.Bushy, selector = hhEval.Deps,
       prover = "e", prover_version = NONE, nfacts = 0, timeout = 5,
       szs = "Error", t_prover = 0.0, axioms_used = NONE,
       recon_ok = NONE, recon_method = NONE, t_recon = NONE, stac = NONE,
       error = SOME "transient harness failure"}
    val _ = hhEval.append_journal retry retry_entry
    val _ = expect "resume retries harness errors"
      (not (hhEval.cell_completed (hhEval.read_completed retry)
        ("list.nil", "deps-e")))
    val run_failure = hhEval.journal_path expdir "runfailure"
    val _ = hhEval.append_journal run_failure
      {run = #run retry_entry, thy = #thy retry_entry,
       thm = #thm retry_entry, goal_id = #goal_id retry_entry,
       cond = #cond retry_entry, regime = #regime retry_entry,
       selector = #selector retry_entry, prover = #prover retry_entry,
       prover_version = NONE, nfacts = 0, timeout = 5,
       szs = "RunFailure", t_prover = 0.0, axioms_used = NONE,
       recon_ok = NONE, recon_method = NONE, t_recon = NONE, stac = NONE,
       error = SOME "prover binary was missing"}
    val _ = expect "resume retries cells whose prover never ran"
      (not (hhEval.cell_completed (hhEval.read_completed run_failure)
        ("list.nil", "deps-e")))
    (* A resume appends past the torn record an interrupted worker left,
       so the malformed line ends up in the middle of the journal. *)
    val torn = hhEval.journal_path expdir "torn"
    val _ = hhEval.append_journal torn null_entry
    val torn_out = TextIO.openAppend torn
    val _ = TextIO.output (torn_out, "{interrupted-write\n")
    val _ = TextIO.closeOut torn_out
    val _ = hhEval.append_journal torn full_entry
    val _ = expect "resume ignores a truncated journal record mid-file"
      (hhEval.journal_complete torn complete andalso
       length (hhEval.read_journal torn) = 2)
    val condition : hhEval.condition =
      {cond_id = "knn-e", regime = hhEval.Chainy, selector = hhEval.Knn 128,
       prover = "e", timeout = 10, reconstruct = true}
    val parsed_condition =
      hhEval.parse_condition (hhEval.encode_condition condition)
    val _ = expect "condition serialization"
      (#cond_id parsed_condition = #cond_id condition andalso
       hhEval.string_of_regime (#regime parsed_condition) = "chainy" andalso
       hhEval.string_of_selector (#selector parsed_condition) = "knn128" andalso
       #prover parsed_condition = "e" andalso
       #timeout parsed_condition = 10 andalso #reconstruct parsed_condition)
    val header : hhEval.run_header =
      {expname = "fixture", date = "today", host = "host", hol_commit = "abc",
       provers = [{name = "e", path = SOME "/e", version = SOME "3.2.5",
                   sha256 = SOME "123"}],
       corpus = [{thy = "list", theorem_count = 2, dep_stamp = "stamp"}],
       added_from_dat = ["missing"], conditions = [condition], sample = 1}
    val _ = hhEval.write_run_header expdir header
    val header_json = JSONParser.parseFile (join expdir "run.json")
    val _ = expect "run header writer"
      (JSONUtil.asString (JSONUtil.lookupField header_json "expname") =
       "fixture")
    val _ = expect "sample one selects every goal"
      (hhEval.sample_goal 1 "list.nil")
    val _ = expect "sample selection is deterministic"
      (hhEval.sample_goal 7 "list.nil" = hhEval.sample_goal 7 "list.nil")
    val _ = expect "invalid sample factor is rejected"
      ((hhEval.sample_goal 0 "list.nil"; false) handle Fail _ => true)
    val script = hhEval.write_evalscript expdir "list" [condition] 7
    val script_text = String.concat (read_lines script)
    val _ = expect "worker script is beside its theory"
      (OS.Path.dir script = join src "one")
    val _ = expect "worker script loads hhEval"
      (String.isSubstring "load \"hhEval\";" script_text)
    val _ = expect "worker script loads its theory"
      (String.isSubstring "load \"listTheory\";" script_text)
    val _ = expect "worker script reflects condition settings"
      (String.isSubstring "hhEval.set_worker_settings" script_text andalso
       String.isSubstring "knn-e" script_text andalso
       String.isSubstring "sample = 7" script_text)
    val _ = expect "worker script calls eval_thy"
      (String.isSubstring "hhEval.eval_thy" script_text)
    val reportdir = join root "hheval-report"
    val report_journal = join reportdir "journal"
    val fixture_journal = join "test-data" "hheval-report/journal"
    fun copy_fixture name =
      write_file (join report_journal name)
        (String.concat (read_lines (join fixture_journal name)))
    val _ = remove_tree reportdir
    val _ = mkdirs report_journal
    val _ = copy_fixture "list.jsonl"
    val _ = copy_fixture "arithmetic.jsonl"
    val report_corrupt = TextIO.openAppend (join report_journal "list.jsonl")
    val _ = TextIO.output (report_corrupt, "{in-progress")
    val _ = TextIO.closeOut report_corrupt
    val _ = hhEval.report reportdir
    val summary = JSONParser.parseFile (join reportdir "summary.json")
    fun array_field name value =
      JSONUtil.arrayMap (fn item => item) (JSONUtil.lookupField value name)
    fun named name wanted values =
      case List.find (fn value =>
        JSONUtil.asString (JSONUtil.lookupField value name) = wanted) values of
          SOME value => value
        | NONE => raise Fail ("missing report item: " ^ wanted)
    fun metric name value =
      JSONUtil.asInt (JSONUtil.lookupField
        (JSONUtil.lookupField value "metrics") name)
    val conditions = array_field "conditions" summary
    val e_condition = named "cond" "deps-e" conditions
    val vampire_condition = named "cond" "deps-vampire" conditions
    val portfolios = array_field "portfolios" summary
    val portfolio = named "key" "bushy/5s" portfolios
    val prover_rows = array_field "provers" portfolio
    val e_prover = named "prover" "e" prover_rows
    val vampire_prover = named "prover" "vampire" prover_rows
    val report_text = String.concat (read_lines (join reportdir "report.md"))
    val _ = expect "report writes both output files"
      (OS.FileSys.access (join reportdir "summary.json", [OS.FileSys.A_READ])
       andalso
       OS.FileSys.access (join reportdir "report.md", [OS.FileSys.A_READ]))
    val _ = expect "report condition counts and quantiles"
      (metric "goals" e_condition = 5 andalso
       metric "attempted" e_condition = 4 andalso
       metric "proved" e_condition = 2 andalso
       metric "reconstructed" e_condition = 1 andalso
       same_real (JSONUtil.asNumber (JSONUtil.lookupField
         (JSONUtil.lookupField e_condition "metrics") "t_prover_p50"))
         0.2 andalso
       same_real (JSONUtil.asNumber (JSONUtil.lookupField
         (JSONUtil.lookupField e_condition "metrics") "t_prover_p90"))
         1.0 andalso
       same_real (JSONUtil.asNumber (JSONUtil.lookupField
         (JSONUtil.lookupField e_condition "metrics") "t_prover_max"))
         1.0 andalso
       same_real (JSONUtil.asNumber (JSONUtil.lookupField
         (JSONUtil.lookupField e_condition "metrics") "proved_pct"))
         50.0 andalso
       same_real (JSONUtil.asNumber (JSONUtil.lookupField
         (JSONUtil.lookupField e_condition "metrics") "reconstructed_pct"))
         25.0)
    val _ = expect "report second prover counts"
      (metric "goals" vampire_condition = 5 andalso
       metric "attempted" vampire_condition = 4 andalso
       metric "proved" vampire_condition = 3 andalso
       metric "reconstructed" vampire_condition = 2)
    val _ = expect "report portfolio union and unique solves"
      (metric "goals" portfolio = 6 andalso
       metric "attempted" portfolio = 5 andalso
       metric "proved" portfolio = 4 andalso
       metric "reconstructed" portfolio = 2 andalso
       JSONUtil.asInt (JSONUtil.lookupField e_prover "unique_proved") =
         1 andalso
       JSONUtil.asInt (JSONUtil.lookupField vampire_prover "unique_proved") =
         2 andalso
       JSONUtil.asInt (JSONUtil.lookupField e_prover
         "unique_reconstructed") = 0 andalso
       JSONUtil.asInt (JSONUtil.lookupField vampire_prover
         "unique_reconstructed") = 1)
    val _ = expect "report includes per-theory markdown table"
      (String.isSubstring "## Theories" report_text andalso
       String.isSubstring "| arithmetic | deps-e" report_text andalso
       String.isSubstring "| list | deps-vampire" report_text)
  in
    ()
  end

val _ =
  case OS.Process.getEnv "HHCONFIG_TEST_ROOT" of
      NONE => ()
    | SOME root => test_hhEval root

fun test_actual_hhEval_corpus () =
  let
    val theories = hhEval.stdlib_theories ()
    val coverage = hhEval.stdlib_coverage ()
    val _ = expect "stdlib corpus contains list and arithmetic"
      (List.exists (fn theory => theory = "list") theories andalso
       List.exists (fn theory => theory = "arithmetic") theories)
    val _ = expect "stdlib coverage discrepancies are recorded"
      (List.all (fn theory => List.exists (fn item => item = theory) theories)
       (#added_from_dat coverage))
  in
    ()
  end

val _ =
  case OS.Process.getEnv "HHCONFIG_TEST_ROOT" of
      NONE => test_actual_hhEval_corpus ()
    | SOME _ => ()

fun test_holyHammer_e () =
  case OS.Process.getEnv "HHCONFIG_TEST_ROOT" of
      SOME _ => ()
    | NONE =>
        case hhProver.probe (prover "e") of
            NONE =>
              (tprint "holyHammer end-to-end e (skipped: absent)"; OK ())
          | SOME _ =>
              let
                val saved = !holyHammer.all_atps
                val root = OS.FileSys.tmpName ()
                val _ = remove_tree root
                val _ = mkdir root
                val add1 = DB.fetch "arithmetic" "ADD1"
                val success =
                  ((holyHammer.all_atps := ["e"];
                    holyHammer.set_timeout 10;
                    ignore (holyHammer.hh ([], boolSyntax.T));
                    ignore (holyHammer.hh_pb root ["e"]
                      ["arithmeticTheory.ADD1"] (Thm.dest_thm add1));
                    case !holyHammer.lemmas_glob of
                        SOME (_ :: _) => true
                      | _ => false)
                   handle Interrupt =>
                     (holyHammer.all_atps := saved; raise Interrupt)
                        | Feedback.HOL_ERR error =>
                     (print (Feedback.message_of error ^ "\n"); false)
                        | exn =>
                     (print (General.exnMessage exn ^ "\n"); false))
                val _ = holyHammer.all_atps := saved
                val _ = remove_tree root
              in
                expect "holyHammer end-to-end e with used axioms" success
              end

val _ = test_szs_status_words ()
val _ = test_hhProver ()
val _ = test_hhSlice ()
val _ = test_holyHammer_validation ()
val _ = test_runner ()
val _ = test_installed_provers ()
val _ = test_holyHammer_e ()

fun test_hhEval_integration () =
  case OS.Process.getEnv "HHCONFIG_TEST_ROOT" of
      SOME _ => ()
    | NONE =>
  case OS.Process.getEnv "HHEVAL_INTEGRATION_TEST" of
      SOME _ =>
        let
          val root =
            case OS.Process.getEnv "HOL4_HAMMER_EVAL_DIR" of
                SOME path => path
              | NONE => raise Fail "integration test has no evaluation dir"
          val condition : hhEval.condition =
            {cond_id = "bushy-deps-e", regime = hhEval.Bushy,
             selector = hhEval.Deps, prover = "e", timeout = 1,
             reconstruct = false}
          val _ = hhEval.run_eval
            {expname = "smoke", ncore = 1, thyl = ["pair", "option"],
             conditions = [condition]}
          val expdir = join root "smoke"
          val pair_journal = hhEval.journal_path expdir "pair"
          val option_journal = hhEval.journal_path expdir "option"
          val journal_before = String.concat (read_lines pair_journal) ^
            String.concat (read_lines option_journal)
          val _ = expect "hhEval integration journals are valid"
            (not (null (hhEval.read_journal pair_journal)) andalso
             not (null (hhEval.read_journal option_journal)) andalso
             OS.FileSys.access (join expdir "run.json", [OS.FileSys.A_READ]))
          val _ = hhEval.run_eval
            {expname = "smoke", ncore = 1, thyl = ["pair", "option"],
             conditions = [condition]}
          val journal_after = String.concat (read_lines pair_journal) ^
            String.concat (read_lines option_journal)
          val _ = expect "hhEval integration resume is a no-op"
            (journal_before = journal_after)
        in
          ()
        end
    | NONE =>
        (case hhProver.probe (prover "e") of
             NONE => (tprint "hhEval integration (skipped: e absent)"; OK ())
           | SOME _ =>
               (tprint
                  "hhEval integration (skipped: set HHEVAL_INTEGRATION_TEST)";
                OK ()))

val _ = test_hhEval_integration ()

val _ = expect "hhEval smoke has twelve fixed goals"
  (length hhEval.smoke_goals = 12)

val _ = expect "hhEval smoke covers every pinned prover four times"
  (List.all (fn prover =>
     length (List.filter (fn (_, _, item) => item = prover)
       hhEval.smoke_goals) = 4)
   ["e", "vampire", "zipperposition"])

local open hhReconstruct hhTranslate holyHammer hhExportLib hhExportFof
  hhExportTf0 hhExportTh0 hhExportTf1 hhExportTh1 hhConfig hhProver hhSlice
in end
