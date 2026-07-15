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

fun mkdir path =
  if is_dir path then () else OS.FileSys.mkDir path

fun mkdirs path =
  if is_dir path then ()
  else
    let
      val parent = OS.Path.dir path
      val _ = if parent = "" orelse parent = path then () else mkdirs parent
    in
      mkdir path
    end

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
    val _ = make_executable config_exec
    val _ = make_executable env_exec
    val _ = mkdirs path_dir
    val _ = make_executable path_exec
    val _ = write_file config
      ("# user configuration\n\
       \priority = user # comments are ignored\n\
       \integer = 42\n\
       \enabled = YeS\n\
       \path.value = ~/.fixture\n\
       \plain = key = value\n\
       \prover.e.executable = " ^ config_exec ^ "\n")
    val _ = expect "state directory" (OS.FileSys.isDir (hhConfig.state_dir ()))
    val _ = expect "comment and assignment parsing"
      (is_some "key = value" (hhConfig.get "plain"))
    val _ = expect "user config overrides system config and environment"
      (is_some "user" (hhConfig.get "priority"))
    val _ = expect "environment key mangling"
      (is_some "environment" (hhConfig.get "mangled.key"))
    val _ = expect "built-in default"
      (is_some (join (hhConfig.state_dir ()) "eval")
               (hhConfig.get "eval.dir"))
    val _ = expect "system configuration"
      (is_some "system only" (hhConfig.get "system.only"))
    val _ = expect "integer configuration"
      (hhConfig.get_int "integer" = SOME 42)
    val _ = expect "Boolean configuration"
      (hhConfig.get_bool "enabled" = SOME true)
    val _ = expect "path configuration"
      (is_some (join home ".fixture") (hhConfig.get_path "path.value"))
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
    val _ = expect "prover environment executable discovery"
      (is_some env_exec (hhConfig.find_exec "e" ["path-exec"]))
    val _ = expect "PATH executable discovery"
      (is_some path_exec (hhConfig.find_exec "pathprover" ["path-exec"]))
    val _ = expect "newest system installation is preferred"
      (is_some system_new
       (hhConfig.find_exec "installprover" ["install-exec"]))
    val _ = expect "install search precedes user installation"
      (hhConfig.find_exec "installprover" ["install-exec"] <> SOME user_new)
    val _ = expect "older installation is not selected"
      (hhConfig.find_exec "installprover" ["install-exec"] <> SOME system_old)
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
      " HOL4_EPROVER_EXECUTABLE=" ^ env_exec ^
      " HHCONFIG_TEST_ROOT=" ^ root ^
      " PATH=" ^ path ^
      " ./selftest.exe"
    val env_command =
      "/usr/bin/env HOL4_HAMMER_EVAL_DIR=environment-eval" ^
      " HHCONFIG_ENV_DEFAULT_TEST=environment-eval" ^
      " HHCONFIG_TEST_ROOT=" ^ root ^
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
  expect "environment overrides the built-in default"
    (is_some value (hhConfig.get "eval.dir"))

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
    val _ = test_recording "zipperposition-theorem.out"
      (#parse_output zipperposition) hhProver.SzsTheorem
      (SOME ["keep_name"])
    val _ = test_recording "zipperposition-counter-sat.out"
      (#parse_output zipperposition) hhProver.SzsCounterSat NONE
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

val _ = test_hhProver ()

local open hhReconstruct hhTranslate holyHammer hhExportLib hhExportFof
  hhExportTf0 hhExportTh0 hhExportTf1 hhExportTh1 hhConfig hhProver in end
