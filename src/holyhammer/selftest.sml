open testutils

(* This quotation is deliberately compiled after hhLamTrans is linked.  A
   compile-time combin-theory dependency used to install its surface grammar
   in HolyHammer sessions (b7fca5c48); this ordinary source fixture must
   retain the ambient grammar. *)
val grammar_pollution_fixture : Term.term = ``(\x : 'a. x) y = y``
val _ =
  (tprint "hhLamTrans does not pollute the term grammar";
   if boolSyntax.is_eq grammar_pollution_fixture then OK ()
   else die "FAILED: hhLamTrans grammar fixture")

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
    val _ = expect "format vocabulary is validated at set time"
      (option_error ["format", "supported TPTP format"]
        (fn () => hhConfig.hh_set ("format", "bad-format")))
    val _ = expect "type encoding vocabulary is validated at set time"
      (option_error ["type_enc", "supported type encoding"]
        (fn () => hhConfig.hh_set ("type_enc", "bad-encoding")))
    val _ = expect "lambda vocabulary is validated at set time"
      (option_error ["lam_trans", "supported lambda translation"]
        (fn () => hhConfig.hh_set ("lam_trans", "bad-lambda")))
    val _ = hhConfig.hh_set ("format", "tf0")
    val _ = hhConfig.hh_set ("type_enc", "mono_native")
    val _ = hhConfig.hh_set ("lam_trans", "lifting")
    val _ = hhConfig.hh_set ("mono_iters", "4")
    val _ = hhConfig.hh_set ("mono_instances", "77")
    val _ = hhConfig.hh_set ("minimize", "off")
    val _ = hhConfig.hh_set ("cache", "yes")
    val _ = hhConfig.hh_set ("debug_dir", join root "debug")
    val options : hhConfig.hh_options = hhConfig.snapshot ()
    val _ = expect "snapshot parses values and computes slices"
      (#timeout options = 23 andalso #max_proofs options = 4 andalso
       #provers options = ["e", "vampire", "zipperposition"] andalso
       #cores options = 3 andalso #slices options = 72 andalso
       #filter options = "none" andalso #max_facts options = SOME 17 andalso
       #format options = "tf0" andalso #type_enc options = "mono_native" andalso
       #lam_trans options = "lifting" andalso #mono_iters options = 4 andalso
       #mono_instances options = SOME 77 andalso not (#minimize options) andalso
       #cache options andalso
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
       has_parameter "format" "tf0" "set" andalso
       has_parameter "type_enc" "mono_native" "set" andalso
       has_parameter "lam_trans" "lifting" "set" andalso
       has_parameter "mono_iters" "4" "set" andalso
       has_parameter "mono_instances" "77" "set" andalso
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
    val _ = List.app hhConfig.hh_unset
      ["format", "type_enc", "lam_trans", "mono_iters", "mono_instances"]
    val default_options : hhConfig.hh_options = hhConfig.snapshot ()
    val _ = expect "new option defaults preserve per-slice values"
      (#format default_options = "" andalso #type_enc default_options = "" andalso
       #lam_trans default_options = "" andalso #mono_iters default_options = 3 andalso
       #mono_instances default_options = NONE andalso
       hhConfig.hh_get "mono_instances" = "100")
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

fun test_hhTptpProblem () =
  let
    open hhTptpProblem
    val ind = TyCon ("$i", [])
    val bool = TyCon ("$o", [])
    val x = Tm (("X", []), [])
    val a = Tm (("a", []), [])
    val f_x_a = Tm (("f", []), [x, a])
    val predicate =
      Quant (true, [("X", SOME ind)],
        Atom (Tm (("p", []), [f_x_a])))
    val fof : problem =
      [("Facts", [FormLine ("fact", Axiom, predicate)]),
       ("Conjecture", [FormLine ("conjecture", Conjecture,
         Atom (Tm (("p", []), [a])))])]
    val decls =
      [TypeDecl ("ty.i", "i", 0),
       SymDecl ("sy.f", "f", TyFun (ind, TyFun (ind, ind))),
       SymDecl ("sy.p", "p", TyFun (ind, bool))]
    fun typed formula : problem =
      [("Declarations", decls),
       ("Facts", [FormLine ("fact", Axiom, formula)]),
       ("Conjecture", [FormLine ("conjecture", Conjecture,
         Atom (Tm (("p", []), [a])))])]
    val tf0 = TFF {poly = false, fool = NoFool}
    val tx0 = TFF {poly = false,
                   fool = Fool {with_ite = true, with_let = true}}
    val tf1 = TFF {poly = true, fool = NoFool}
    val th0 = THF {poly = false,
                   syntax = {with_ite = false, with_let = false},
                   choice = false}
    val th1 = THF {poly = true,
                   syntax = {with_ite = true, with_let = false},
                   choice = false}
    val ite = Tm (("$ite", []),
      [Tm (("c", []), [x]), f_x_a, a])
    val tx0_formula =
      Quant (true, [("X", SOME ind)], Atom (Tm (("p", []), [ite])))
    val tf1_formula =
      TyQuant (true, ["A"],
        Quant (true, [("X", SOME (TyVar "A"))],
          Atom (Tm (("p", [TyVar "A"]), [x]))))
    val th0_formula =
      Atom (Tm (("p", []), [TmAbs (("Y", ind), Tm (("f", []), [x, a]))]))
    val th1_formula =
      TyQuant (true, ["A"],
        Atom (Tm (("p", [TyVar "A"]), [ite])))
    fun golden name format problem =
      expect_equal ("TPTP golden " ^ name)
        (String.concat (read_lines (join "test-data/problems" name)))
        (string_of_problem format ("hhTptpProblem " ^ name) problem)
    fun raises thunk = (thunk (); false) handle Fail _ => true
    val _ = golden "fof.p" FOF fof
    val _ = golden "tf0.p" tf0 (typed predicate)
    val _ = golden "tx0.p" tx0 (typed tx0_formula)
    val _ = golden "tf1.p" tf1 (typed tf1_formula)
    val _ = golden "th0.p" th0 (typed th0_formula)
    val _ = golden "th1.p" th1 (typed th1_formula)
    val uncurry_expected = String.concat
      ["% uncurry\n", "% Declarations (1)\n", "tff(sy.f, type,\n",
       "    f : ($i * $i) > $i).\n"]
    val _ = expect_equal "TFF types are uncurried" uncurry_expected
      (string_of_problem tf0 "uncurry"
        [("Declarations", [SymDecl ("sy.f", "f",
          TyFun (ind, TyFun (ind, ind)))])])
    val _ = expect_equal "type arguments precede TFF term arguments"
      "% args\n%  (1)\ntff(fact, axiom,\n    (f($i,X))).\n"
      (string_of_problem tf0 "args"
        [("", [FormLine ("fact", Axiom,
          Atom (Tm (("f", [ind]), [x])))])])
    val _ = expect_equal "type arguments precede THF term arguments"
      "% args\n%  (1)\nthf(fact, axiom,\n    ((f @ ($i) @ X))).\n"
      (string_of_problem th0 "args"
        [("", [FormLine ("fact", Axiom,
          Atom (Tm (("f", [ind]), [x])))])])
    val _ = expect "$ite prints when enabled"
      (String.isSubstring "$ite(c(X),f(X,a),a)"
        (string_of_problem tx0 "ite"
          [("Facts", [FormLine ("fact", Axiom, Atom ite)])]))
    val _ = expect "$ite rejects disabled syntax"
      (raises (fn () => string_of_problem tf0 "ite"
        [("Facts", [FormLine ("fact", Axiom, Atom ite)])]))
    val let_term = Tm (("$let", []),
      [a, TmAbs (("Y", ind), Tm (("f", []), [x, a]))])
    val _ = expect "$let prints when enabled"
      (String.isSubstring "$let(Y : $i, Y := a, f(X,a))"
        (string_of_problem tx0 "let"
          [("Facts", [FormLine ("fact", Axiom, Atom let_term)])]))
    val _ = expect "$let rejects disabled syntax"
      (raises (fn () => string_of_problem th1 "let"
        [("Facts", [FormLine ("fact", Axiom, Atom let_term)])]))
    val choice = Tm (("@+", []), [TmAbs (("Y", ind), x)])
    val _ = expect "choice printing is rejected"
      (raises (fn () => string_of_problem th0 "choice"
        [("Facts", [FormLine ("fact", Axiom, Atom choice)])]))
    val sections = string_of_problem FOF "sections"
      [("First", [FormLine ("one", Axiom, Atom a)]),
       ("Second", [FormLine ("two", Hypothesis, Atom x),
                   FormLine ("three", Conjecture, Atom a)])]
    val _ = expect "sections preserve order and print counts"
      (String.isSubstring "% First (1)\nfof(one" sections andalso
       String.isSubstring "% Second (2)\nfof(two" sections andalso
       String.isSubstring "fof(three" sections andalso
       String.isSubstring "% First (1)" sections andalso
       String.isSubstring "% Second (2)" sections)
  in
    ()
  end

val _ = test_hhTptpProblem ()

fun test_hhTypeEnc () =
  let
    open hhTptpProblem hhTypeEnc
    fun raises fragment thunk =
      (thunk (); false)
      handle Fail message => String.isSubstring fragment message
           | _ => false
    val encodings =
      ["mono_native", "mono_native_fool", "mono_native_higher",
       "mono_native_higher_fool", "poly_native", "mono_guards",
       "mono_guards??", ""]
    val rejected = ["native", "mono_guards?", "poly_guards", " ",
                    "mono_native??"]
    val fof = FOF
    val tf0 = TFF {poly = false, fool = NoFool}
    val tx0 = TFF {poly = false,
                   fool = Fool {with_ite = true, with_let = true}}
    val tf1 = TFF {poly = true, fool = NoFool}
    val th0 = THF {poly = false,
                   syntax = {with_ite = false, with_let = false},
                   choice = false}
    val th1 = THF {poly = true,
                   syntax = {with_ite = true, with_let = false},
                   choice = false}
    fun adjusted format encoding =
      to_string (adjust_type_enc format (of_string encoding))
    fun matrix format expected =
      ListPair.allEq (fn (encoding, result) =>
        case result of
            SOME expected => adjusted format encoding = expected
          | NONE => raises "valid only" (fn () =>
              ignore (adjust_type_enc format (of_string encoding))))
        (encodings, expected)
    val mono = "mono_native"
    val mono_fool = "mono_native_fool"
    val _ = expect "type-encoding grammar round-trips"
      (List.all (fn encoding => to_string (of_string encoding) = encoding)
       encodings)
    val _ = expect "type-encoding grammar rejects all other strings"
      (List.all (fn encoding => raises "unknown type encoding" (fn () =>
         ignore (of_string encoding))) rejected)
    val _ = expect "type encoding adjustment matrix: FOF"
      (matrix fof [SOME "mono_guards", SOME "mono_guards",
                   SOME "mono_guards", SOME "mono_guards",
                   SOME "mono_guards", SOME "mono_guards",
                   SOME "mono_guards??", SOME ""])
    val _ = expect "type encoding adjustment matrix: TF0"
      (matrix tf0 [SOME mono, SOME mono, SOME mono, SOME mono,
                   SOME mono, NONE, NONE, NONE])
    val _ = expect "type encoding adjustment matrix: TX0"
      (matrix tx0 [SOME mono, SOME mono_fool, SOME mono, SOME mono_fool,
                   SOME mono, NONE, NONE, NONE])
    val _ = expect "type encoding adjustment matrix: TF1"
      (matrix tf1 [SOME mono, SOME mono, SOME mono, SOME mono,
                   SOME "poly_native", NONE, NONE, NONE])
    val _ = expect "type encoding adjustment matrix: TH0"
      (matrix th0 [SOME mono, SOME mono, SOME "mono_native_higher",
                   SOME "mono_native_higher", SOME mono, NONE, NONE,
                   NONE])
    val _ = expect "type encoding adjustment matrix: TH1"
      (matrix th1 [SOME mono, SOME mono_fool, SOME "mono_native_higher",
                   SOME "mono_native_higher_fool", SOME "poly_native",
                   NONE, NONE, NONE])
    val _ = bossLib.Hol_datatype
      `hh_typeenc_enum = HHRed | HHBlue | HHGreen`
    val _ = bossLib.Hol_datatype
      `hh_typeenc_recursive = HHStop | HHNext of hh_typeenc_recursive`
    val num_ty = Term.type_of ``0 : num``
    val list_num_ty = Term.type_of ``[] : num list``
    val list_var_ty = Term.type_of ``[] : 'a list``
    val one_ty = Type.mk_type ("one", [])
    val enum_ty = Type.mk_type ("hh_typeenc_enum", [])
    val rec_ty = Type.mk_type ("hh_typeenc_recursive", [])
    val bool_fun_ty = Type.mk_type ("fun", [Type.bool, Type.bool])
    val bool_bool_fun_ty = Type.mk_type ("fun", [Type.bool, bool_fun_ty])
    val num_bool_fun_ty = Type.mk_type ("fun", [num_ty, Type.bool])
    val _ = expect "infinity oracle recognises hardwired types"
      (surely_infinite num_ty)
    val _ = expect "infinity oracle recognises recursive list instances"
      (surely_infinite list_num_ty andalso surely_infinite list_var_ty)
    val _ = expect "infinity oracle keeps finite functions finite"
      (not (surely_infinite bool_fun_ty) andalso
       not (surely_infinite bool_bool_fun_ty))
    val _ = expect "infinity oracle composes infinite function domains"
      (surely_infinite num_bool_fun_ty)
    val _ = expect "infinity oracle treats unknown finite types conservatively"
      (not (surely_infinite Type.bool) andalso not (surely_infinite one_ty)
       andalso not (surely_infinite enum_ty))
    val _ = expect "infinity oracle detects recursive datatypes"
      (surely_infinite rec_ty)
    fun same_types expected actual = expected = actual
    val x = Term.mk_var ("X", one_ty)
    val n = Term.mk_var ("N", num_ty)
    val p = Term.mk_var ("P", Type.mk_type ("fun", [one_ty, Type.bool]))
    val fequal = Term.mk_var ("fequal",
      Type.mk_type ("fun", [one_ty,
        Type.mk_type ("fun", [one_ty, Type.bool])]))
    val naked = boolSyntax.mk_forall (x, boolSyntax.mk_eq (x, x))
    val guarded = boolSyntax.mk_forall (x, Term.mk_comb (p, x))
    val negative = boolSyntax.mk_forall (x,
      boolSyntax.mk_neg (boolSyntax.mk_eq (x, x)))
    val fequal_formula = boolSyntax.mk_forall (x,
      Term.list_mk_comb (fequal, [x, x]))
    val infinite_naked = boolSyntax.mk_forall (n, boolSyntax.mk_eq (n, n))
    val _ = expect "monotonicity calculus finds naked variables"
      (same_types [Type.bool, one_ty] (types_needing_encoding [naked]))
    val _ = expect "monotonicity calculus ignores guarded and negative variables"
      (same_types [Type.bool]
        (types_needing_encoding [guarded, negative, infinite_naked]))
    val _ = expect "monotonicity calculus finds fequal variables"
      (same_types [Type.bool, one_ty]
        (types_needing_encoding [fequal_formula]))
  in
    ()
  end

val _ = test_hhTypeEnc ()

fun test_hhLamTrans () =
  let
    open boolSyntax
    val num = Term.type_of ``0 : num``
    val unary = Type.mk_type ("fun", [num, num])
    val binary = Type.mk_type ("fun", [num, unary])
    val x = Term.mk_var ("X", num)
    val y = Term.mk_var ("Y", num)
    val f = Term.mk_var ("F", binary)
    val g = Term.mk_var ("G", unary)
    val h = Term.mk_var ("H", unary)
    val nested_lam = Term.list_mk_abs ([x, y],
      Term.list_mk_comb (f, [Term.mk_comb (g, x), y]))
    val nested = mk_eq (Term.list_mk_comb (nested_lam, [x, y]),
      Term.list_mk_comb (f, [Term.mk_comb (g, x), y]))
    val under_quantifier = mk_forall (h,
      mk_eq (Term.mk_comb (Term.mk_abs (x, Term.mk_comb (h, x)), x),
        Term.mk_comb (h, x)))
    val alpha = Type.mk_vartype "'a"
    val poly_predicate = Type.mk_type ("fun", [alpha, Type.bool])
    val poly_x = Term.mk_var ("PX", alpha)
    val poly_p = Term.mk_var ("PP", poly_predicate)
    val polymorphic_lam =
      Term.mk_abs (poly_x, Term.mk_comb (poly_p, poly_x))
    val polymorphic = mk_eq (Term.mk_comb (polymorphic_lam, poly_x),
      Term.mk_comb (poly_p, poly_x))
    val bool_consumer = Term.mk_var ("BC", Type.mk_type
      ("fun", [Type.bool, Type.bool]))
    val quantified_argument = Term.mk_comb (bool_consumer,
      mk_forall (poly_x, Term.mk_comb (poly_p, poly_x)))
    val t = Term.mk_var ("T0", Type.bool)
    val t1 = Term.mk_var ("T1", Type.bool)
    val t2 = Term.mk_var ("T2", Type.bool)
    val implication_lam = Term.mk_abs (t,
      mk_imp (mk_imp (t1, t), mk_imp (mk_imp (t2, t), t)))
    val function_consumer = Term.mk_var ("FC", Type.mk_type
      ("fun", [Term.type_of implication_lam, Type.bool]))
    val implication_argument =
      Term.mk_comb (function_consumer, implication_lam)
    val nested_quantifier_lam = Term.mk_abs (x,
      mk_forall (y, mk_imp (mk_conj
        (mk_eq (x, x), mk_eq (y, y)), mk_eq (x, y))))
    val nested_function_consumer = Term.mk_var ("NFC", Type.mk_type
      ("fun", [Term.type_of nested_quantifier_lam, Type.bool]))
    val nested_quantifier_argument =
      Term.mk_comb (nested_function_consumer, nested_quantifier_lam)
    val beta_fixtures = [nested, under_quantifier, polymorphic]
    val fixtures =
      beta_fixtures @
      [quantified_argument, implication_argument, nested_quantifier_argument]
    fun formula_abs tm =
      if is_forall tm then formula_abs (#2 (dest_forall tm))
      else if is_exists tm then formula_abs (#2 (dest_exists tm))
      else if is_neg tm then formula_abs (dest_neg tm)
      else if is_conj tm orelse is_disj tm orelse is_imp_only tm then
        formula_abs (lhand tm) orelse formula_abs (rand tm)
      else if is_eq tm andalso Term.type_of (lhand tm) = Type.bool then
        formula_abs (lhand tm) orelse formula_abs (rand tm)
      else term_abs tm
    and term_abs tm =
      if Term.is_abs tm then true
      else if Term.is_comb tm then
        term_abs (Term.rator tm) orelse term_abs (Term.rand tm)
      else false
    fun generated_symbol tm =
      List.all (fn variable =>
        String.isPrefix "lam." (#1 (Term.dest_var variable)))
        (Term.free_vars_lr tm)
    fun normalise tm =
      (rhs (Thm.concl (simpLib.SIMP_CONV boolSimps.bool_ss
        [DB.fetch "combin" "I_THM", DB.fetch "combin" "K_THM",
         DB.fetch "combin" "S_THM", DB.fetch "combin" "C_THM",
         DB.fetch "combin" "o_THM"] tm)) handle UNCHANGED => tm)
    fun has_name stem definitions =
      List.exists (fn (name, _) => name = stem) definitions
    val (lifted, lift_defs) = hhLamTrans.translate "lifting" fixtures
    val (combs, comb_defs) = hhLamTrans.translate "combs" fixtures
    val (both, both_defs) =
      hhLamTrans.translate "combs_and_lifting" fixtures
    val (kept, kept_defs) = hhLamTrans.translate "keep_lams" fixtures
    val _ = expect "lambda lifting has deterministic names"
      (map #1 lift_defs = List.tabulate (length lift_defs,
       fn index => "lam." ^ Int.toString index))
    val _ = expect "lifting removes fixture abstractions"
      (List.all (not o formula_abs) lifted andalso
       List.all (fn (_, definition) =>
         not (formula_abs definition)) lift_defs)
    val _ = expect "lifting definitions bind their captured variables"
      (List.all (generated_symbol o #2) lift_defs andalso
       List.exists (fn (_, definition) =>
         List.exists (fn ty => ty = alpha) (Term.type_vars_in_term definition))
         lift_defs)
    val _ = expect "combs removes fixture abstractions"
      (null comb_defs andalso List.all (not o formula_abs) combs)
    val _ = expect "combs beta-normalise to the closed input"
      (ListPair.allEq (fn (actual, fixture) =>
         Term.aconv (normalise actual)
           (normalise (list_mk_forall (Term.free_vars_lr fixture, fixture))))
       (List.take (combs, length beta_fixtures), beta_fixtures))
    val _ = expect "combs_and_lifting retains both definition forms"
      (ListPair.allEq (fn (left, right) => Term.aconv left right)
         (both, lifted) andalso
       length both_defs = 2 * length lift_defs andalso
       List.all (fn (name, _) =>
         has_name (name ^ ".combs") both_defs) lift_defs andalso
       List.all (not o formula_abs o #2) both_defs)
    val _ = expect "keep_lams only eta-contracts"
      (null kept_defs andalso List.exists formula_abs kept andalso
       length kept = length fixtures)
    val _ = expect "empty lambda mode is rejected outside the legacy path"
      ((ignore (hhLamTrans.translate "" fixtures); false) handle Fail _ => true)
  in
    ()
  end

val _ = test_hhLamTrans ()

fun test_hhMonomorph () =
  let
    open boolSyntax
    val alpha = Type.alpha
    val beta = Type.beta
    val num = Term.type_of ``0 : num``
    fun list_ty ty = Type.mk_type ("list", [ty])
    fun pair_ty left right = Type.mk_type ("prod", [left, right])
    fun nil_tm ty = Term.inst [{redex = alpha, residue = ty}] ``[]``
    fun eq_nil ty = mk_eq (nil_tm ty, nil_tm ty)
    fun conjs [] = boolSyntax.T
      | conjs (first :: rest) = List.foldl (fn (tm, result) =>
          mk_conj (result, tm)) first rest
    fun named name facts =
      List.filter (fn (other, _) => other = name) facts
    fun same_output left right =
      ListPair.allEq (fn ((left_name, left_tm), (right_name, right_tm)) =>
        left_name = right_name andalso Term.aconv left_tm right_tm)
        (left, right)
    val goal = eq_nil (list_ty num)
    val schematic = eq_nil (list_ty alpha)
    val expected = Term.inst [{redex = alpha, residue = num}] schematic
    val basic = hhMonomorph.monomorph
      {max_iters = 3, max_new_instances = 100} goal
      [("ground", goal), ("schematic", schematic)]
    val predicate = Term.mk_var ("P", Type.mk_type ("fun", [alpha,
      Type.bool]))
    val x = Term.mk_var ("X", alpha)
    val ignored = Term.mk_comb (predicate, x)
    val with_ignored = hhMonomorph.monomorph
      {max_iters = 3, max_new_instances = 100} goal
      [("ground", goal), ("ignored", ignored), ("schematic", schematic)]
    val global_cap = hhMonomorph.monomorph
      {max_iters = 3, max_new_instances = 1} goal
      [("first", schematic), ("second", schematic)]
    fun nested 0 = num
      | nested count = list_ty (nested (count - 1))
    val cap_goal = conjs (map (fn index =>
      eq_nil (list_ty (nested index))) (List.tabulate (11, fn index => index)))
    val per_fact = hhMonomorph.monomorph
      {max_iters = 3, max_new_instances = 100} cap_goal
      [("many", schematic)]
    val smallest_ten = map (fn index =>
      Term.inst [{redex = alpha, residue = nested index}] schematic)
      (List.tabulate (10, fn index => index))
    val too_many_predicate = Term.mk_var ("Q",
      List.foldr (fn (_, ty) => Type.mk_type ("fun", [list_ty alpha, ty]))
        Type.bool (List.tabulate (21, fn index => index)))
    val too_many = Term.list_mk_comb (too_many_predicate,
      List.tabulate (21, fn _ => nil_tm alpha))
    val schematic_cap = hhMonomorph.monomorph
      {max_iters = 3, max_new_instances = 100} goal
      [("too-many", too_many)]
    val pair_alpha_num = pair_ty alpha num
    val pair_beta_num = pair_ty beta num
    val chain = conjs [eq_nil (list_ty alpha),
      eq_nil (list_ty pair_alpha_num)]
    val downstream = eq_nil (list_ty pair_beta_num)
    val one_round = hhMonomorph.monomorph
      {max_iters = 1, max_new_instances = 100} goal
      [("chain", chain), ("downstream", downstream)]
    val privileged = hhMonomorph.monomorph
      {max_iters = 2, max_new_instances = 100} goal
      [("chain", chain), ("downstream", downstream)]
    val filler = List.tabulate (10, fn index =>
      ("filler" ^ Int.toString index, goal))
    val ordinary = hhMonomorph.monomorph
      {max_iters = 2, max_new_instances = 100} goal
      (filler @ [("chain", chain), ("downstream", downstream)])
    val again = hhMonomorph.monomorph
      {max_iters = 3, max_new_instances = 100} cap_goal
      [("many", schematic)]
    val _ = expect "monomorphization closes the list/num fixture"
      (length (named "ground" basic) = 1 andalso
       List.exists (fn (_, tm) => Term.aconv tm expected)
         (named "schematic" basic))
    val _ = expect "monomorphization drops ignored facts"
      (null (named "ignored" with_ignored) andalso
       ListPair.allEq (fn ((_, actual), (_, expected)) =>
         Term.aconv actual expected) (named "ground" with_ignored,
         [("ground", goal)]))
    val _ = expect "monomorphization enforces its global instance cap"
      (length global_cap = 1)
    val _ = expect "monomorphization enforces ten instances per fact"
      (ListPair.allEq (fn ((_, actual), expected) => Term.aconv actual expected)
        (named "many" per_fact, smallest_ten))
    val _ = expect "monomorphization skips facts with over twenty schematics"
      (null (named "too-many" schematic_cap))
    val _ = expect "monomorphization enforces its round cap"
      (null (named "downstream" one_round))
    val _ = expect "privileged facts advance pair/list chains by one round"
      (not (null (named "downstream" privileged)) andalso
       null (named "downstream" ordinary))
    val _ = expect "monomorphization output order is deterministic"
      (same_output per_fact again)
  in
    ()
  end

val _ = test_hhMonomorph ()

fun test_hhProblemGen () =
  let
    open boolSyntax hhTptpProblem hhProblemGen
    val num = Term.type_of ``0 : num``
    val unary_num = Type.mk_type ("fun", [num, num])
    val bool_to_bool = Type.mk_type ("fun", [Type.bool, Type.bool])
    val x = Term.mk_var ("X", num)
    val y = Term.mk_var ("Y", num)
    val f = Term.mk_var ("F", unary_num)
    val p = Term.mk_var ("P", Type.bool)
    val use = Term.mk_var ("use", Type.mk_type
      ("fun", [bool_to_bool, Type.bool]))
    val use_bool = Term.mk_var ("use_bool", bool_to_bool)
    val use_num = Term.mk_var ("use_num", Type.mk_type
      ("fun", [num, Type.bool]))
    val alpha = Type.alpha
    fun list_ty ty = Type.mk_type ("list", [ty])
    fun nil_tm ty = Term.inst [{redex = alpha, residue = ty}] ``[]``
    fun eq_nil ty = mk_eq (nil_tm ty, nil_tm ty)
    val fof = FOF
    val tf0 = TFF {poly = false, fool = NoFool}
    val tx0 = TFF {poly = false,
                   fool = Fool {with_ite = true, with_let = true}}
    val th0 = THF {poly = false,
                   syntax = {with_ite = false, with_let = false},
                   choice = false}
    val th1 = THF {poly = true,
                   syntax = {with_ite = true, with_let = false},
                   choice = false}
    fun input conjecture : named_terms = {conjecture = conjecture, facts = []}
    fun head_name tm =
      let
        fun head body = if Term.is_comb body then head (Term.rator body)
                        else body
        val head = head tm
      in
        if Term.is_var head then #1 (Term.dest_var head)
        else #1 (Term.dest_const head)
      end
    fun proxied_atom format tm =
      let
        val ir = formula_skeleton (input tm)
      in
        case #conjecture (introduce_proxies format ir) of
            HAtom result => result
          | _ => raise Fail "expected atom"
      end
    val beta = Term.mk_comb (Term.mk_abs (x, x), y)
    val eta = Term.mk_abs (x, Term.mk_comb (f, x))
    val let_tm = mk_let (Term.mk_abs (x, Term.mk_comb (f, x)), y)
    val cond_tm = mk_cond (p, x, y)
    val beta_result = #conjecture (presimp fof (input beta))
    val eta_result = #conjecture (presimp fof (input eta))
    val let_fof = #conjecture (presimp fof (input let_tm))
    val let_tx0 = #conjecture (presimp tx0 (input let_tm))
    val cond_tf0 = #conjecture (presimp tf0 (input cond_tm))
    val cond_tx0 = #conjecture (presimp tx0 (input cond_tm))
    val lambda = mk_eq (Term.mk_abs (x, x), Term.mk_abs (x, x))
    val downgraded = pass_lambda tf0 "keep_lams" (input lambda)
    val kept = pass_lambda th0 "keep_lams" (input lambda)
    val goal = eq_nil (list_ty num)
    val schematic = eq_nil (list_ty alpha)
    val mono = pass_monomorph (hhTypeEnc.of_string "mono_native")
      {max_iters = 3, max_new_instances = 100}
      {conjecture = goal, facts = [("schematic", schematic)]}
    val poly = pass_monomorph (hhTypeEnc.of_string "poly_native")
      {max_iters = 3, max_new_instances = 100}
      {conjecture = goal, facts = [("schematic", schematic)]}
    val iff = formula_skeleton (input (mk_eq (mk_neg p, p)))
    val logical_argument = Term.mk_comb (use, negation)
    val applied_not = Term.mk_comb (use_bool, mk_neg p)
    val applied_eq = Term.mk_comb (use_bool, mk_eq (x, y))
    val ite_atom = Term.mk_comb (use_num, cond_tm)
    val _ = expect "hhProblemGen presimp beta-contracts"
      (Term.aconv beta_result y)
    val _ = expect "hhProblemGen presimp eta-contracts"
      (Term.aconv eta_result f)
    val _ = expect "hhProblemGen presimp gates LET on $let"
      (Term.aconv let_fof (Term.mk_comb (f, y)) andalso is_let let_tx0)
    val _ = expect "hhProblemGen presimp retains COND for helper routing"
      (is_cond cond_tf0 andalso is_cond cond_tx0)
    val _ = expect "hhProblemGen downgrades keep_lams outside THF"
      (not (null (#facts downgraded)) andalso null (#facts kept))
    val _ = expect "hhProblemGen dispatches monomorphization by encoding"
      (List.exists (fn (_, tm) => not (Term.aconv tm schematic)) (#facts mono)
       andalso ListPair.allEq (fn ((left_name, left), (right_name, right)) =>
         left_name = right_name andalso Term.aconv left right)
         (#facts poly, [("schematic", schematic)]))
    val _ = expect "hhProblemGen skeleton maps boolean equality to iff"
      (case iff of
           {conjecture = HConn (Iff, [HConn (Not, _), HAtom _]), ...} => true
         | _ => false)
    val _ = expect "hhProblemGen uses proxies in FOF and TF0 term positions"
      (head_name (rand (proxied_atom fof logical_argument)) = "pxy.not" andalso
       head_name (rand (proxied_atom tf0 logical_argument)) = "pxy.not")
    val _ = expect "hhProblemGen uses logical proxies in term positions"
      (head_name (rand (proxied_atom tx0 applied_not)) = "pxy.not" andalso
       head_name (rand (proxied_atom tx0 applied_eq)) = "pxy.eq" andalso
       head_name (rand (proxied_atom th0 logical_argument)) = "pxy.not")
    val _ = expect "hhProblemGen gates $ite on the format syntax"
      (head_name (rand (proxied_atom tx0 ite_atom)) = "$ite" andalso
       is_cond (rand (proxied_atom tf0 ite_atom)))
    val proxy_ir = introduce_proxies fof
      (formula_skeleton (input logical_argument))
    val _ = expect "hhProblemGen records used proxies"
      (#proxies proxy_ir = ["not"])
    val _ = expect "hhProblemGen composes its front-end passes"
      (#proxies (translate_front
        {format = fof, type_enc = hhTypeEnc.of_string "mono_guards",
         lam_trans = "lifting", mono_iters = 3, mono_instances = 100}
        (input logical_argument)) = ["not"])
    fun problem format encoding terms =
      string_of_problem format "hhProblemGen pass 6--8"
        (generate_problem
          {format = format, type_enc = hhTypeEnc.of_string encoding,
           lam_trans = "lifting", mono_iters = 3, mono_instances = 100}
          terms)
    fun occurrences needle text =
      let
        fun loop haystack count =
          case Substring.position needle haystack of
              (_, rest) =>
                if Substring.isEmpty rest then count
                else loop (Substring.triml (size needle) rest) (count + 1)
      in
        loop (Substring.full text) 0
      end
    val binary_num = Type.mk_type ("fun", [num, unary_num])
    val pxy_f = Term.mk_var ("pxy.f", binary_num)
    val number_pred = Term.mk_var ("NPred", Type.mk_type
      ("fun", [num, Type.bool]))
    val function_var = Term.mk_var ("H", unary_num)
    val function_pred = Term.mk_var ("FPred", Type.mk_type
      ("fun", [unary_num, Type.bool]))
    val full_f = Term.list_mk_comb (pxy_f, [x, y])
    val full_formula = Term.mk_comb (number_pred, full_f)
    val no_function_variable =
      problem fof "mono_guards" {conjecture = full_formula, facts = []}
    val with_function_variable = problem fof "mono_guards"
      {conjecture = mk_forall (function_var, full_formula), facts = []}
    val bool_term = problem fof "mono_guards" (input applied_not)
    val fool_bool_term = problem tx0 "mono_native_fool" (input applied_not)
    val tf1 = TFF {poly = true, fool = NoFool}
    val poly_goal = eq_nil (list_ty alpha)
    val poly_native = problem tf1 "poly_native" (input poly_goal)
    val mono_native = problem tf0 "mono_native" (input poly_goal)
    val higher_native = problem th0 "mono_native_higher" (input poly_goal)
    val higher_fool = problem th0 "mono_native_higher_fool" (input poly_goal)
    val one_ty = Type.mk_type ("one", [])
    val one_x = Term.mk_var ("OX", one_ty)
    val one_y = Term.mk_var ("OY", one_ty)
    val one_naked = mk_forall (one_x,
      mk_forall (one_y, mk_eq (one_x, one_x)))
    val guards_all = problem fof "mono_guards" (input one_naked)
    val guards_query = problem fof "mono_guards??" (input one_naked)
    val one_only = mk_forall (one_x, mk_eq (one_x, one_x))
    val one_all = problem fof "mono_guards" (input one_only)
    val one_query = problem fof "mono_guards??" (input one_only)
    val forty_four = problem tf1 "poly_native"
      {conjecture = full_formula,
       facts = List.tabulate (44, fn index =>
         ("f" ^ Int.toString index,
          Term.mk_comb (function_pred, Term.mk_comb (pxy_f, x))))}
    val forty_five = problem tf1 "poly_native"
      {conjecture = full_formula,
       facts = List.tabulate (45, fn index =>
         ("f" ^ Int.toString index,
          Term.mk_comb (function_pred, Term.mk_comb (pxy_f, x))))}
    val _ = expect "hhProblemGen respects final application arities"
      (String.isSubstring "pxy_2Ef(" no_function_variable andalso
       not (String.isSubstring "app_2E(pxy_2Ef" no_function_variable) andalso
       String.isSubstring "app_2E(pxy_2Ef" with_function_variable)
    val _ = expect "hhProblemGen switches to Min_App_Op at forty-five facts"
      (occurrences "app_2E(pxy_2Ef" forty_four = 44 andalso
       occurrences "app_2E(pxy_2Ef" forty_five = 45)
    val _ = expect "hhProblemGen inserts pp for non-FOOL boolean terms"
      (String.isSubstring "pp_2E(app_2E" bool_term andalso
       not (String.isSubstring "pp_2E(app_2E" fool_bool_term))
    val _ = expect "hhProblemGen mangles mono symbols, sorts, and type variables"
      (String.isSubstring "c_2Elist_2ENIL" mono_native andalso
       String.isSubstring "ty_2E" mono_native andalso
       String.isSubstring "var_2E_27a" mono_native)
    val _ = expect "hhProblemGen binds TF1 type variables and emits declarations"
      (String.isSubstring "!>[A" poly_native andalso
       String.isSubstring "tff(ty_" poly_native andalso
       String.isSubstring "tff(sy_" poly_native)
    val _ = expect "all native encoding paths produce TPTP structures"
      (String.isSubstring "tff(conjecture" mono_native andalso
       String.isSubstring "tff(conjecture" fool_bool_term andalso
       String.isSubstring "thf(conjecture" higher_native andalso
       String.isSubstring "thf(conjecture" higher_fool)
    val _ = expect "monomorphic THF flattens applied types to ground sorts"
      (String.isSubstring
         "ty_2Elist_2Elist_28var_2E_27a_29 : $tType" higher_native)
    val _ = expect "mono_guards?? guards fewer naked variables"
      (occurrences "gd_2E" guards_query < occurrences "gd_2E" guards_all)
    val _ = expect "mono_guards?? agrees on possibly-finite naked types"
      (String.isSubstring "![OX]: (gd_2E" one_query andalso
       String.isSubstring "![OX]: (gd_2E" one_all)
    val _ = expect "hhProblemGen emits result guards and witnesses"
      (String.isSubstring "gsy_2E" guards_all andalso
       String.isSubstring "wit_2E" guards_all)
    val cond_helpers = problem tf0 "mono_native"
      (input (mk_eq (cond_tm, x)))
    val app_helpers = with_function_variable
    val pp_helpers = bool_term
    val no_helpers = problem fof "mono_guards" (input (mk_eq (x, x)))
    val _ = expect "hhProblemGen injects all COND helpers iff COND occurs"
      (String.isSubstring "help_2Eif__True" cond_helpers andalso
       String.isSubstring "help_2Eif__False" cond_helpers andalso
       String.isSubstring "help_2Ebool__cases" cond_helpers andalso
       not (String.isSubstring "help_2Eif__True" no_helpers) andalso
       not (String.isSubstring "help_2Eif__False" no_helpers))
    val _ = expect "hhProblemGen injects EQ_EXT iff app occurs"
      (String.isSubstring "help_2Eeq__ext" app_helpers andalso
       not (String.isSubstring "help_2Eeq__ext" no_helpers))
    val _ = expect "hhProblemGen injects pp laws iff pp occurs"
      (String.isSubstring "help_2Epp_2Etrue" pp_helpers andalso
       String.isSubstring "help_2Epp_2Efalse" pp_helpers andalso
       not (String.isSubstring "help_2Epp_2Etrue" no_helpers) andalso
       not (String.isSubstring "help_2Epp_2Efalse" no_helpers))
    val quantifier_use = Term.mk_var ("quantifier_use", Type.mk_type
      ("fun", [Term.type_of universal, Type.bool]))
    val all_helpers = problem fof "mono_guards"
      (input (Term.mk_comb (quantifier_use, universal)))
    val ex_helpers = problem fof "mono_guards"
      (input (Term.mk_comb (quantifier_use, existential)))
    val true_helpers = problem fof "mono_guards"
      (input (Term.mk_comb (use_bool, T)))
    val false_helpers = problem fof "mono_guards"
      (input (Term.mk_comb (use_bool, F)))
    fun logical_helper constant =
      let val use = Term.mk_var ("logical_helper",
        Type.mk_type ("fun", [Term.type_of constant, Type.bool])) in
        problem fof "mono_guards" (input (Term.mk_comb (use, constant)))
      end
    val conj_helpers = logical_helper conjunction
    val disj_helpers = logical_helper disjunction
    val imp_helpers = logical_helper implication
    val _ = expect "hhProblemGen injects proxy laws iff their proxies occur"
      (String.isSubstring "help_2Epxy_2Eeq" no_helpers andalso
       String.isSubstring "help_2Epxy_2Enot" pp_helpers andalso
       String.isSubstring "help_2Epxy_2Econj" conj_helpers andalso
       String.isSubstring "help_2Epxy_2Edisj" disj_helpers andalso
       String.isSubstring "help_2Epxy_2Eimp" imp_helpers andalso
       String.isSubstring "help_2Epxy_2Eall" all_helpers andalso
       String.isSubstring "help_2Epxy_2Eex" ex_helpers andalso
       String.isSubstring "help_2Epxy_2Etrue" true_helpers andalso
       String.isSubstring "help_2Epxy_2Efalse" false_helpers andalso
       not (String.isSubstring "help_2Epxy_2Eall" no_helpers) andalso
       not (String.isSubstring "help_2Epxy_2Eex" no_helpers))
    val memo = new_export_memo ()
    val output1 = OS.FileSys.tmpName ()
    val output2 = OS.FileSys.tmpName ()
    val export_options =
      {format = tf0, type_enc = hhTypeEnc.of_string "mono_native",
       lam_trans = "lifting", mono_iters = 3, mono_instances = 100}
    val theorem = DB.fetch "bool" "TRUTH"
    val exported = (``T`` : Term.term, [("truth", theorem)])
    val _ = export_pb_in memo export_options output1 exported
    val _ = export_pb_in memo export_options output2 exported
    val first_export = String.concat (read_lines output1)
    val second_export = String.concat (read_lines output2)
    val _ = OS.FileSys.remove output1
    val _ = OS.FileSys.remove output2
    val _ = expect "hhProblemGen export is stable and memoizes lambda handling"
      (first_export = second_export andalso memo_lambda_runs memo = 1 andalso
       String.isSubstring "% generated by hhProblemGen; format=tff" first_export andalso
       String.isSubstring "% Declarations" first_export andalso
       String.isSubstring "% Helpers" first_export andalso
       String.isSubstring "% Facts" first_export andalso
       String.isSubstring "% Conjecture" first_export)
    val comb_problem = string_of_problem tf0 "combin helpers"
      (generate_problem
        {format = tf0, type_enc = hhTypeEnc.of_string "mono_native",
         lam_trans = "combs", mono_iters = 3, mono_instances = 100}
        (input lambda))
    val _ = expect "hhProblemGen fetches combinator helpers only for combs"
      (String.isSubstring "help_2Ecombin_2EI" comb_problem andalso
       not (String.isSubstring "help_2Ecombin_2EI" mono_native))
    (* This exporter fixture has a polymorphic premise and puts lambdas,
       COND, a Boolean term in term position, and naked equality in its
       conjecture.  It is deliberately proof-independent. *)
    val golden_goal = mk_conj (mk_eq (cond_tm, x),
      mk_conj (lambda, mk_conj (applied_not, mk_eq (x, x))))
    val golden_exported = (golden_goal, [("poly", Thm.REFL schematic)])
    val golden_specs =
      [("hhproblemgen-tx0-lifting.p", tx0, "mono_native_fool", "lifting"),
       ("hhproblemgen-tx0minus-lifting.p",
        TFF {poly = false, fool = Fool {with_ite = false, with_let = false}},
        "mono_native_fool", "lifting"),
       ("hhproblemgen-th1-keep-lams.p", th1, "mono_native_higher_fool",
        "keep_lams"),
       ("hhproblemgen-th0-keep-lams.p", th0, "mono_native_higher",
        "keep_lams"),
       ("hhproblemgen-tf1-lifting.p", tf1, "poly_native", "lifting"),
       ("hhproblemgen-tf0-combs-lifting.p", tf0, "mono_native",
        "combs_and_lifting"),
       ("hhproblemgen-tx0-combs.p", tx0, "mono_native_fool", "combs"),
       ("hhproblemgen-fof-guards-query.p", fof, "mono_guards??", "lifting")]
    fun golden_problem (name, format, encoding, mode) =
      let
        val options =
          {format = format, type_enc = hhTypeEnc.of_string encoding,
           lam_trans = mode, mono_iters = 3, mono_instances = 100}
        val temporary = OS.FileSys.tmpName ()
        val _ = export_pb options temporary golden_exported
        val actual = String.concat (read_lines temporary)
        val _ = OS.FileSys.remove temporary
        val path = join "test-data/problems" name
      in
        expect_equal ("hhProblemGen golden " ^ name)
          (String.concat (read_lines path)) actual
      end
    val _ = List.app golden_problem golden_specs
    (* This is export-linked: the fake proof names are the exact escaped
       identifiers the fixture just emitted, including a mono copy. *)
    val roundtrip_name = "fixtureTheory.roundtrip"
    val roundtrip_file = OS.FileSys.tmpName ()
    val roundtrip_theorem = DB.fetch "bool" "TRUTH"
    val roundtrip_input = (mk_conj (mk_eq (cond_tm, x), lambda),
      [(roundtrip_name, roundtrip_theorem),
       (roundtrip_name, roundtrip_theorem)])
    val _ = export_pb export_options roundtrip_file roundtrip_input
    val roundtrip_problem = String.concat (read_lines roundtrip_file)
    val _ = OS.FileSys.remove roundtrip_file
    val escaped_roundtrip = aiLib.escape ("thm." ^ roundtrip_name)
    val escaped_copy = aiLib.escape ("thm2." ^ roundtrip_name)
    val _ = expect "hhProblemGen export-linked parse-back fixture emits all names"
      (String.isSubstring escaped_roundtrip roundtrip_problem andalso
       String.isSubstring escaped_copy roundtrip_problem andalso
       String.isSubstring "lam_2E" roundtrip_problem andalso
       String.isSubstring "help_2Eif__True" roundtrip_problem)
    val _ = expect_equal "hhProblemGen export-linked TSTP round trip"
      [roundtrip_name]
      (hhProver.axioms_from_tstp
        ["fof(" ^ escaped_roundtrip ^ ", axiom, p).",
         "fof(" ^ escaped_copy ^ ", axiom, p).",
         "fof(lam_2E0, axiom, p).",
         "fof(help_2Eif__True, axiom, p).",
         "fof(ty_2Efixture, axiom, p).",
         "fof(sy_2Efixture, axiom, p).",
         "fof(gsy_2Efixture, axiom, p).",
         "fof(wit_2Efixture, axiom, p)."])
  in
    ()
  end

val _ = test_hhProblemGen ()

fun prover name =
  case hhProver.lookup name of
      SOME config => config
    | NONE => raise Fail ("missing prover " ^ name)

val sample_request : hhProver.run_request =
  {timeout = 7, format = "fof", problem = "problem.p", extra = ["--extra"],
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
    val names = map #name (hhProver.all ())
    val _ = expect "all built-in provers"
      (names = ["e", "vampire", "zipperposition", "z3"])
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
    val _ = test_recording "vampire-5.0.1-tx0-lifting.out"
      (#parse_output vampire) hhProver.SzsTheorem
      (SOME ["arithmeticTheory.ADD1"])
    val _ = test_recording "e-3.2.5-ho-tx0minus-lifting.out"
      (#parse_output e) hhProver.SzsTheorem (SOME ["arithmeticTheory.ADD1"])
    val _ = test_recording "zipperposition-2.1-th1-keep-lams.out"
      (#parse_output zipperposition) hhProver.SzsTheorem
      (SOME ["arithmeticTheory.ADD1"])
    val _ = test_recording "e-3.2.5-ho-th0-keep-lams.out"
      (#parse_output e) hhProver.SzsTheorem (SOME ["arithmeticTheory.ADD1"])
    val _ = test_recording "vampire-5.0.1-th0-substitute.out"
      (#parse_output vampire) hhProver.SzsTheorem
      (SOME ["arithmeticTheory.ADD1"])
    val _ = test_recording "e-3.2.5-ho-tx0minus-combs-lifting.out"
      (#parse_output e) hhProver.SzsTheorem (SOME ["arithmeticTheory.ADD1"])
    val _ = test_recording "vampire-5.0.1-tx0-combs.out"
      (#parse_output vampire) hhProver.SzsTheorem
      (SOME ["arithmeticTheory.ADD1"])
    val _ = test_recording "zipperposition-2.1-fof-substitute.out"
      (#parse_output zipperposition) hhProver.SzsTheorem
      (SOME ["arithmeticTheory.ADD1"])
    val _ = expect_equal "TSTP parse-back drops generated names and dedups copies"
      ["alpha", "beta"]
      (hhProver.axioms_from_tstp
        (read_lines "test-data/hhproblemgen-roundtrip.out"))
    val _ = expect_equal "TSTP parse-back accepts thm copies and dedups"
      ["alpha"]
      (hhProver.axioms_from_tstp
        ["fof(thm_2Ealpha, axiom, p).",
         "fof(thm2_2Ealpha, axiom, p).",
         "fof(thm10_2Ealpha, axiom, p)."])
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
  in
    ()
  end

fun slice_options provers slices cores timeout filter max_facts
    : hhConfig.hh_options =
  {timeout = timeout, max_proofs = 4, provers = provers, slices = slices,
   cores = cores, filter = filter, max_facts = max_facts,
   format = "", type_enc = "", lam_trans = "", mono_iters = 3,
   mono_instances = NONE, minimize = true,
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
    fun expected prover format type_enc lam_trans nfacts =
      (prover, format, type_enc, lam_trans, nfacts, "knn", [], 1)
    val phase1 =
      [expected "vampire" "fof" "" "" 96,
       expected "e" "fof" "" "" 128,
       expected "zipperposition" "fof" "" "" 128,
       expected "vampire" "fof" "" "" 512,
       expected "e" "fof" "" "" 512,
       expected "vampire" "fof" "" "" 32,
       expected "zipperposition" "fof" "" "" 512,
       expected "vampire" "fof" "" "" 1024]
    val phase2 =
      [expected "vampire" "tx0" "mono_native_fool" "lifting" 96,
       expected "e" "tx0-" "mono_native_fool" "lifting" 128,
       expected "zipperposition" "th1" "mono_native_higher_fool"
         "keep_lams" 128,
       expected "e" "th0" "mono_native_higher" "keep_lams" 512,
       expected "vampire" "th0" "mono_native_higher" "keep_lams" 512,
       expected "e" "tx0-" "mono_native_fool" "combs_and_lifting" 1024,
       expected "vampire" "tx0" "mono_native_fool" "combs" 512,
       expected "zipperposition" "fof" "" "" 32]
    val expected_default = phase1 @ phase2
    val e_slices = map slice_summary (#slices (prover "e") ())
    val vampire_slices = map slice_summary (#slices (prover "vampire") ())
    val zipperposition_slices =
      map slice_summary (#slices (prover "zipperposition") ())
    val _ = expect_equal "E slice table"
      [List.nth (phase1, 1), List.nth (phase1, 4),
       List.nth (phase2, 1), List.nth (phase2, 3),
       List.nth (phase2, 5)] e_slices
    val _ = expect_equal "Vampire slice table"
      [List.nth (phase1, 0), List.nth (phase1, 3),
       List.nth (phase1, 5), List.nth (phase1, 7),
       List.nth (phase2, 0), List.nth (phase2, 4),
       List.nth (phase2, 6)] vampire_slices
    val _ = expect_equal "Zipperposition slice table"
      [List.nth (phase1, 2), List.nth (phase1, 6),
       List.nth (phase2, 2), List.nth (phase2, 7)] zipperposition_slices
    val _ = expect "Z3 stays callable without scheduler slices"
      (List.all (null o (fn config => #slices config ()))
       (map prover ["z3"]))
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
    val _ = expect_equal "golden 16-slice Phase 2 schedule"
      expected_default (map (slice_summary o #2) default_schedule)
    val _ = expect_equal "Phase 1 eight-slice prefix is frozen verbatim"
      phase1 (List.take (map (slice_summary o #2) default_schedule, 8))
    val gate30 = slice_options ["e", "vampire", "zipperposition"]
      8 8 30 "knn" NONE
    val gate10 = slice_options ["e", "vampire", "zipperposition"]
      8 8 10 "knn" NONE
    val gate30_schedule = hhSlice.mk_schedule gate30
    val gate10_schedule = hhSlice.mk_schedule gate10
    val expected_gate = List.take (phase1, 8)
    val _ = expect_equal "gate freezes the first eight schedule slices"
      expected_gate (map (slice_summary o #2) gate30_schedule)
    val _ = expect_equal "S30 and S10 use the same frozen schedule"
      (schedule_summary gate30_schedule) (schedule_summary gate10_schedule)
    fun close expected actual = Real.abs (expected - actual) < 0.000001
    val _ = expect "eight-core gate gives every S30 slice 30 seconds"
      (List.all (fn (_, slice) =>
         close 30.0 (hhSlice.slice_budget 8 gate30 slice)) gate30_schedule)
    val _ = expect "eight-core gate gives every S10 slice 10 seconds"
      (List.all (fn (_, slice) =>
         close 10.0 (hhSlice.slice_budget 8 gate10 slice)) gate10_schedule)
    val anchors = gate30_schedule
    fun anchor_command_equal (config, slice) =
      let
        val baseline : hhProver.run_request =
          {timeout = 30, format = "fof", problem = "anchor.p", extra = [],
           debug_dir = NONE}
        val scheduled : hhProver.run_request =
          {timeout = 30, format = #format slice, problem = "anchor.p",
           extra = #extra_opts slice, debug_dir = NONE}
      in
        #mk_command config "anchor-prover" baseline =
        #mk_command config "anchor-prover" scheduled
      end
    val _ = expect "gate anchors are command-equivalent to one-shot B"
      (List.all anchor_command_equal anchors)
    val small = hhSlice.mk_schedule
      (slice_options ["e", "vampire", "zipperposition"] 5 2 30 "knn"
        NONE)
    val _ = expect_equal "small schedule follows the golden rotation"
      (List.take (schedule_summary default_schedule, 5))
      (schedule_summary small)
    val subset = hhSlice.mk_schedule
      (slice_options ["zipperposition", "e"] 7 4 30 "knn" NONE)
    val _ = expect_equal "prover subset consumes each table head-first"
      [("e", 128, "knn", []),
       ("zipperposition", 128, "knn", []),
       ("e", 512, "knn", []),
       ("zipperposition", 512, "knn", []),
       ("e", 128, "knn", []),
       ("zipperposition", 128, "knn", []),
       ("e", 512, "knn", [])]
      (schedule_summary subset)
    val overridden = hhSlice.mk_schedule
      (slice_options ["e"] 20 2 30 "none" (SOME 40))
    val _ = expect_equal "fact and filter overrides precede deduplication"
      [("e", 40, "none", []),
       ("e", 40, "none", []),
       ("e", 40, "none", []),
       ("e", 40, "none", [])]
      (schedule_summary overridden)
    val exhausted = hhSlice.mk_schedule
      (slice_options ["e", "vampire", "zipperposition"] 100 8 30 "knn"
        NONE)
    val _ = expect "rotation exhaustion stops at sixteen unique slices"
      (length exhausted = 16)
    val _ = expect "Z3 remains outside the slice scheduler"
      (null (hhSlice.mk_schedule
        (slice_options ["z3"] 100 8 30 "knn" NONE)))
    val first_slice = #2 (hd default_schedule)
    val large_slice : hhProver.slice =
      {prover = #prover first_slice, format = #format first_slice,
       type_enc = #type_enc first_slice, lam_trans = #lam_trans first_slice,
       nfacts = #nfacts first_slice, filter = #filter first_slice,
       extra_opts = #extra_opts first_slice, slice_size = 3}
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
    val triple_options : hhConfig.hh_options =
      {timeout = 30, max_proofs = 4, provers = ["e"], slices = 1, cores = 1,
       filter = "knn", max_facts = NONE, format = "tf0",
       type_enc = "mono_native", lam_trans = "lifting", mono_iters = 3,
       mono_instances = NONE, minimize = true, preplay_timeout = 1.0,
       minimize_timeout = 1.0, cache = false, cache_dir = "",
       cache_max_entries = 100000, debug_dir = NONE}
    val triple_schedule = hhSlice.mk_schedule triple_options
    val _ = expect "slice construction accepts a supported full triple"
      (case triple_schedule of
           [(_, slice)] => #format slice = "tf0" andalso
                         #type_enc slice = "mono_native" andalso
                         #lam_trans slice = "lifting"
         | _ => false)
    fun invalid_triple format type_enc lam_trans =
      let
        val options : hhConfig.hh_options =
          {timeout = 30, max_proofs = 4, provers = ["e"], slices = 1,
           cores = 1, filter = "knn", max_facts = NONE, format = format,
           type_enc = type_enc, lam_trans = lam_trans, mono_iters = 3,
           mono_instances = NONE, minimize = true, preplay_timeout = 1.0,
           minimize_timeout = 1.0, cache = false, cache_dir = "",
           cache_max_entries = 100000, debug_dir = NONE}
      in
        ((ignore (hhSlice.mk_schedule options); false) handle Fail _ => true)
      end
    val _ = expect "slice construction rejects incoherent triples"
      (invalid_triple "tf0" "" "lifting" andalso
       invalid_triple "th1" "mono_native_higher" "keep_lams" andalso
       invalid_triple "tf0" "mono_native" "")
  in
    ()
  end

fun cache_options directory maximum enabled : hhConfig.hh_options =
  {timeout = 30, max_proofs = 4, provers = ["e"], slices = 1,
   cores = 1, filter = "knn", max_facts = NONE,
   format = "", type_enc = "", lam_trans = "", mono_iters = 3,
   mono_instances = NONE, minimize = true,
   preplay_timeout = 1.0, minimize_timeout = 1.0, cache = enabled,
   cache_dir = directory, cache_max_entries = maximum, debug_dir = NONE}

fun test_hhCache () =
  let
    val root = OS.FileSys.tmpName ()
    val _ = remove_tree root
    val _ = mkdir root
    val moved = join root "moved"
    val cache = join root "cache"
    val lru_cache = join root "lru"
    val _ = mkdir moved
    val problem1 = join root "problem.p"
    val problem2 = join moved "renamed.p"
    val problem3 = join root "changed.p"
    val contents = "fof(cache_fixture, conjecture, $true).\n"
    val _ = write_file problem1 contents
    val _ = write_file problem2 contents
    val _ = write_file problem3 (contents ^ "% changed\n")
    val first : hhCache.key_parts =
      {prover = "e", version = SOME "3.2.5",
       argv = ["--cpu-limit=10", problem1], problem = problem1}
    val relocated : hhCache.key_parts =
      {prover = "e", version = SOME "3.2.5",
       argv = ["--cpu-limit=10", problem2], problem = problem2}
    val longer : hhCache.key_parts =
      {prover = "e", version = SOME "3.2.5",
       argv = ["--cpu-limit=20", problem1], problem = problem1}
    val upgraded : hhCache.key_parts =
      {prover = "e", version = SOME "3.3",
       argv = ["--cpu-limit=10", problem1], problem = problem1}
    val changed : hhCache.key_parts =
      {prover = "e", version = SOME "3.2.5",
       argv = ["--cpu-limit=10", problem3], problem = problem3}
    val first_key = hhCache.key_of first
    val _ = expect "cache key is a SHA-1 digest"
      (String.size first_key = 40 andalso
       List.all Char.isHexDigit (String.explode first_key))
    val _ = expect "cache key ignores the problem path"
      (first_key = hhCache.key_of relocated)
    val _ = expect "cache key includes timeout and options"
      (first_key <> hhCache.key_of longer)
    val _ = expect "cache key includes the probed prover version"
      (first_key <> hhCache.key_of upgraded)
    val _ = expect "cache key includes problem contents"
      (first_key <> hhCache.key_of changed)
    val boundary1 : hhCache.key_parts =
      {prover = "ab", version = NONE, argv = ["c", problem1],
       problem = problem1}
    val boundary2 : hhCache.key_parts =
      {prover = "a", version = NONE, argv = ["bc", problem1],
       problem = problem1}
    val _ = expect "cache key fields have unambiguous boundaries"
      (hhCache.key_of boundary1 <> hhCache.key_of boundary2)
    val options = cache_options cache 100 true
    val stored : hhProver.run_result =
      {szs = hhProver.SzsTheorem, used_axioms = SOME ["a", "b"],
       time = 1.25, version = SOME "3.2.5", output_file = "ignored.out"}
    val _ = hhCache.store options first stored
    val round_trip = hhCache.lookup options relocated
    val _ = expect "cache store and relocated lookup round-trip"
      (case round_trip of
           SOME result =>
             #szs result = hhProver.SzsTheorem andalso
             #used_axioms result = SOME ["a", "b"] andalso
             Real.abs (#time result - 1.25) < 0.000001 andalso
             #version result = SOME "3.2.5" andalso
             #output_file result = ""
         | NONE => false)
    val _ = expect "a longer timeout is a cache miss"
      (not (Option.isSome (hhCache.lookup options longer)))
    val timeout_result : hhProver.run_result =
      {szs = hhProver.SzsTimeout, used_axioms = NONE, time = 10.0,
       version = SOME "3.2.5", output_file = "timeout.out"}
    val _ = hhCache.store options longer timeout_result
    val _ = expect "timeout results are cached"
      (case hhCache.lookup options longer of
           SOME result => #szs result = hhProver.SzsTimeout
         | NONE => false)
    val corrupt : hhCache.key_parts =
      {prover = "e", version = NONE, argv = ["--corrupt", problem1],
       problem = problem1}
    val corrupt_path = join cache (hhCache.key_of corrupt)
    val _ = write_file corrupt_path "this is not JSON"
    val _ = expect "corrupt cache entries are misses"
      (not (Option.isSome (hhCache.lookup options corrupt)))
    val _ = expect "corrupt cache entries are deleted"
      (not (OS.FileSys.access (corrupt_path, [])))
      handle OS.SysErr _ => OK ()
    val disabled : hhCache.key_parts =
      {prover = "e", version = NONE, argv = ["--disabled", problem1],
       problem = problem1}
    val _ = hhCache.store (cache_options cache 100 false) disabled stored
    val _ = expect "disabled cache does not store entries"
      (not (OS.FileSys.access (join cache (hhCache.key_of disabled), [])))
      handle OS.SysErr _ => OK ()
    fun lru_parts number : hhCache.key_parts =
      {prover = "e", version = SOME "3.2.5",
       argv = ["--slice=" ^ Int.toString number, problem1],
       problem = problem1}
    val lru_parts_list = List.tabulate (6, lru_parts)
    val lru_options = cache_options lru_cache 5 true
    val _ = List.app (fn parts => hhCache.store lru_options parts stored)
      lru_parts_list
    fun path_of parts = join lru_cache (hhCache.key_of parts)
    fun set_times ([], _) = ()
      | set_times (parts :: rest, seconds) =
          (OS.FileSys.setTime
             (path_of parts, SOME (Time.fromSeconds
               (LargeInt.fromInt seconds)));
           set_times (rest, seconds + 10))
    val _ = set_times (lru_parts_list, 10)
    val oldest = hd lru_parts_list
    val before_touch = OS.FileSys.modTime (path_of oldest)
    val _ = ignore (hhCache.lookup lru_options oldest)
    val after_touch = OS.FileSys.modTime (path_of oldest)
    val _ = expect "cache lookup refreshes the LRU mtime"
      (Time.compare (after_touch, before_touch) = GREATER)
    val _ = hhCache.prune lru_options
    fun exists parts = OS.FileSys.access (path_of parts, [])
      handle OS.SysErr _ => false
    val _ = expect "cache prune removes oldest entries after a touch"
      (exists (List.nth (lru_parts_list, 0)) andalso
       not (exists (List.nth (lru_parts_list, 1))) andalso
       not (exists (List.nth (lru_parts_list, 2))) andalso
       List.all exists (List.drop (lru_parts_list, 3)))
    val _ = expect "cache prune enforces the ninety-percent bound"
      (length (hhConfig.directory_names lru_cache) = 4)
    val _ = remove_tree root
  in
    ()
  end

fun contains needle haystack =
  String.isSubstring needle haystack

fun hh_error call =
  ((call (); NONE)
   handle Feedback.HOL_ERR error => SOME (Feedback.message_of error))

fun test_holyHammer_validation () =
  let
    val unknown = "not-a-holyhammer-prover"
    val _ = expect "prover option rejects unknown registry names"
      (option_error [unknown, "registered prover names"]
        (fn () => hhConfig.hh_set ("provers", unknown)))
  in
    case OS.Process.getEnv "HHCONFIG_TEST_ROOT" of
        NONE => ()
      | SOME _ =>
          let
            val output = OS.FileSys.tmpName ()
            val message = smlRedirect.hide_in_file output
              (fn () => hh_error (fn () =>
                ignore (holyHammer.hh_pb "" ["zipperposition"] []
                  ([], boolSyntax.T)))) ()
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
   tested_versions = ["test"], supported_formats = ["fof"],
   mk_command = fn executable => fn _ => (executable, args),
   parse_output = parser, mono_instances = NONE,
   slices = fn () => [],
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
      {timeout = 2, format = "fof", problem = "unused", extra = [],
       debug_dir = NONE}
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
      {timeout = 1, format = "fof", problem = "unused", extra = [],
       debug_dir = SOME debug_dir}
    val good_result = hhProver.run good good_request
    val _ = expect "runner parses stdout"
      (#szs good_result = hhProver.SzsTheorem)
    val _ = expect "runner saves debug output"
      (OS.FileSys.access (#output_file good_result, [OS.FileSys.A_READ]))
    val _ = remove_tree debug_dir
    val timeout = fake_config "runner-timeout" "/bin/sleep" ["30"]
      (#parse_output e)
    val timeout_request : hhProver.run_request =
      {timeout = 0, format = "fof", problem = "unused", extra = [],
       debug_dir = NONE}
    val timeout_result = hhProver.run timeout timeout_request
    val _ = expect "runner watchdog timeout"
      (#szs timeout_result = hhProver.SzsTimeout orelse
       #szs timeout_result = hhProver.SzsResourceOut)
    val killed = fake_config "runner-killed" "/bin/sleep" ["30"]
      (#parse_output e)
    val kill_request : hhProver.run_request =
      {timeout = 30, format = "fof", problem = "unused", extra = [],
       debug_dir = NONE}
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
      {timeout = 2, format = "fof", problem = "unused", extra = [],
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
      {timeout = 30, format = "fof", problem = "unused", extra = [],
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
       tested_versions = ["test"], supported_formats = ["fof"],
       mk_command = fn _ => fn _ =>
         ("/definitely/missing/holyhammer-prover", []),
       parse_output = #parse_output e,
       mono_instances = NONE, slices = fn () => [], legacy = false}
    val exec_result = hhProver.run exec_failure timeout_request
    val _ = expect "runner exec failure returns RunFailure"
      (case #szs exec_result of hhProver.RunFailure _ => true | _ => false)
    val missing : hhProver.prover_config =
      {name = "runner-missing", exec_names = ["missing-hh-prover"],
       env_var = "", version_args = [], parse_version = fn _ => NONE,
       tested_versions = [], supported_formats = ["fof"],
       mk_command = fn executable => fn _ => (executable, []),
       parse_output = #parse_output e,
       mono_instances = NONE, slices = fn () => [], legacy = false}
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
            {timeout = 5, format = "fof", problem = problem, extra = [],
             debug_dir = NONE}
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

fun same_engine (hhEval.Prover left) (hhEval.Prover right) = left = right
  | same_engine
      (hhEval.Sched {provers = left_provers, slices = left_slices,
                     cores = left_cores, max_proofs = left_max_proofs})
      (hhEval.Sched {provers = right_provers, slices = right_slices,
                     cores = right_cores, max_proofs = right_max_proofs}) =
      left_provers = right_provers andalso left_slices = right_slices andalso
      left_cores = right_cores andalso left_max_proofs = right_max_proofs
  | same_engine _ _ = false

val same_slice = hhProver.same_slice

fun same_journal_slice (expected : hhEval.journal_slice)
    (actual : hhEval.journal_slice) =
  same_slice (#slice expected) (#slice actual) andalso
  #szs expected = #szs actual andalso
  same_real (#time expected) (#time actual) andalso
  #cached expected = #cached actual

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
  same_engine (#engine expected) (#engine actual) andalso
  #ho expected = #ho actual andalso #prover expected = #prover actual andalso
  #prover_version expected = #prover_version actual andalso
  #nfacts expected = #nfacts actual andalso
  #timeout expected = #timeout actual andalso
  #szs expected = #szs actual andalso
  same_real (#t_prover expected) (#t_prover actual) andalso
  #axioms_used expected = #axioms_used actual andalso
  #recon_ok expected = #recon_ok actual andalso
  #recon_method expected = #recon_method actual andalso
  same_real_option (#t_recon expected) (#t_recon actual) andalso
  #stac expected = #stac actual andalso #error expected = #error actual andalso
  #stop expected = #stop actual andalso
  same_real_option (#t_total expected) (#t_total actual) andalso
  (case (#winner expected, #winner actual) of
       (NONE, NONE) => true
     | (SOME left, SOME right) => same_slice left right
     | _ => false) andalso
  ListPair.allEq (fn (left, right) => same_journal_slice left right)
    (#slices expected, #slices actual)

fun test_hhEval root =
  let
    val num_ty = Type.mk_type ("num", [])
    val num_fun_ty = Type.mk_type ("fun", [num_ty, num_ty])
    val bool_predicate_ty = Type.mk_type ("fun", [Type.bool, Type.bool])
    val x = Term.mk_var ("x", num_ty)
    val f = Term.mk_var ("f", num_fun_ty)
    val bool_predicate = Term.mk_var ("P", bool_predicate_ty)
    val residual_lambda : Term.term = ``(\x : num. x) = (\x. x)``
    val applied_bound_function : Term.term = ``!f : num -> num. f 0 = f 0``
    val connective_in_term = Term.mk_comb (bool_predicate, ``T /\ T``)
    val quantifier_in_term = Term.mk_comb (bool_predicate, ``!x : num. x = x``)
    val plain_first_order : Term.term = ``(1 : num) = 1``
    val binder_only : Term.term = ``!x : num. x = x``
    val beta_redex = Term.mk_comb (Term.mk_abs (x, x), ``0 : num``)
    val eta_redex = Term.mk_abs (x, Term.mk_comb (f, x))
    val _ = expect "HO classifier hand-labelled fixtures"
      (List.all (fn (tm, expected) => hhEval.is_higher_order_goal tm = expected)
       [(residual_lambda, true), (applied_bound_function, true),
        (connective_in_term, true), (quantifier_in_term, true),
        (plain_first_order, false), (binder_only, false)])
    val _ = expect "HO classifier beta-eta invariant"
      (hhEval.is_higher_order_goal beta_redex =
         hhEval.is_higher_order_goal ``0 : num`` andalso
       hhEval.is_higher_order_goal eta_redex =
         hhEval.is_higher_order_goal f)
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
       engine = hhEval.Prover "e", ho = SOME false, prover = "e",
       prover_version = NONE,
       nfacts = 0, timeout = 5,
       szs = "BrokenDeps", t_prover = 0.0, axioms_used = NONE,
       recon_ok = NONE, recon_method = NONE, t_recon = NONE, stac = NONE,
       error = NONE, stop = NONE, t_total = NONE, winner = NONE, slices = []}
    val full_entry : hhEval.journal_entry =
      {run = "fixture", thy = "list", thm = "cons", goal_id = "list.cons",
       cond = "knn-e", regime = hhEval.Chainy, selector = hhEval.Knn 128,
       engine = hhEval.Prover "e", ho = SOME true, prover = "e",
       prover_version = SOME "3.2.5", nfacts = 128,
       timeout = 10, szs = "Theorem", t_prover = 1.25,
       axioms_used = SOME ["list.nil", "arithmetic.add"], recon_ok = SOME true,
       recon_method = SOME "metis", t_recon = SOME 0.5,
       stac = SOME "metis_tac [list_nil]", error = SOME "fixture",
       stop = NONE, t_total = NONE, winner = NONE, slices = []}
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
       engine = hhEval.Prover "e", ho = SOME false, prover = "e",
       prover_version = NONE, nfacts = 0, timeout = 5,
       szs = "Error", t_prover = 0.0, axioms_used = NONE,
       recon_ok = NONE, recon_method = NONE, t_recon = NONE, stac = NONE,
       error = SOME "transient harness failure", stop = NONE,
       t_total = NONE, winner = NONE, slices = []}
    val _ = hhEval.append_journal retry retry_entry
    val _ = expect "resume retries harness errors"
      (not (hhEval.cell_completed (hhEval.read_completed retry)
        ("list.nil", "deps-e")))
    val run_failure = hhEval.journal_path expdir "runfailure"
    val _ = hhEval.append_journal run_failure
      {run = #run retry_entry, thy = #thy retry_entry,
       thm = #thm retry_entry, goal_id = #goal_id retry_entry,
       cond = #cond retry_entry, regime = #regime retry_entry,
       selector = #selector retry_entry, engine = #engine retry_entry,
       ho = #ho retry_entry, prover = #prover retry_entry,
       prover_version = NONE, nfacts = 0, timeout = 5,
       szs = "RunFailure", t_prover = 0.0, axioms_used = NONE,
       recon_ok = NONE, recon_method = NONE, t_recon = NONE, stac = NONE,
       error = SOME "prover binary was missing", stop = NONE,
       t_total = NONE, winner = NONE, slices = []}
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
       engine = hhEval.Prover "e", timeout = 10, reconstruct = true}
    val parsed_condition =
      hhEval.parse_condition (hhEval.encode_condition condition)
    val _ = expect "condition serialization"
      (#cond_id parsed_condition = #cond_id condition andalso
       hhEval.string_of_regime (#regime parsed_condition) = "chainy" andalso
       hhEval.string_of_selector (#selector parsed_condition) = "knn128" andalso
       same_engine (#engine parsed_condition) (hhEval.Prover "e") andalso
       #timeout parsed_condition = 10 andalso #reconstruct parsed_condition)
    val sched_condition : hhEval.condition =
      {cond_id = "sched", regime = hhEval.Chainy,
       selector = hhEval.Knn 256,
       engine = hhEval.Sched
         {provers = ["e", "vampire"], slices = 6, cores = 2,
          max_proofs = 3},
       timeout = 30, reconstruct = true}
    val parsed_sched_condition =
      hhEval.parse_condition (hhEval.encode_condition sched_condition)
    val _ = expect "Sched condition serialization"
      (#cond_id parsed_sched_condition = "sched" andalso
       same_engine (#engine parsed_sched_condition)
         (#engine sched_condition) andalso
       #timeout parsed_sched_condition = 30 andalso
       #reconstruct parsed_sched_condition)
    val invalid_sched : hhEval.condition =
      {cond_id = "invalid-sched", regime = hhEval.Bushy,
       selector = hhEval.Deps,
       engine = hhEval.Sched
         {provers = ["e"], slices = 1, cores = 1, max_proofs = 1},
       timeout = 5, reconstruct = false}
    val _ = expect "Sched condition requires reconstruction"
      ((hhEval.validate_condition invalid_sched; false)
       handle Fail message =>
         String.isSubstring "Sched" message andalso
         String.isSubstring "reconstruct must be true" message)
    val schedule_slice : hhEval.journal_slice =
      {slice =
         {prover = "e", format = "fof", type_enc = "",
          lam_trans = "", nfacts = 256, filter = "mepo",
          extra_opts = ["--auto"], slice_size = 15},
       szs = "Theorem", time = 1.75, cached = true}
    val competing_schedule_slice : hhEval.journal_slice =
      {slice =
         {prover = "e", format = "tx0-", type_enc = "mono_native_fool",
          lam_trans = "lifting", nfacts = 256, filter = "mepo",
          extra_opts = ["--auto"], slice_size = 15},
       szs = "Theorem", time = 1.5, cached = false}
    val sched_entry : hhEval.journal_entry =
      {run = "fixture", thy = "list", thm = "scheduled",
       goal_id = "list.scheduled", cond = "sched",
       regime = hhEval.Chainy, selector = hhEval.Knn 256,
       engine = #engine sched_condition, ho = SOME true, prover = "e",
       prover_version = SOME "3.2.5", nfacts = 256, timeout = 30,
       szs = "Theorem", t_prover = 1.75,
       axioms_used = SOME ["list.one"], recon_ok = SOME true,
       recon_method = SOME "metis", t_recon = SOME 0.25,
       stac = SOME "metis_tac [list_one]", error = NONE,
       stop = SOME "MaxProofs", t_total = SOME 2.0,
       winner = SOME (#slice schedule_slice),
       slices = [competing_schedule_slice, schedule_slice]}
    val sched_line = hhEval.encode_journal_line sched_entry
    val _ = expect "Sched journal round trip"
      (same_journal_entry sched_entry (hhEval.parse_journal_line sched_line))
    val sched_json = JSONParser.parseFile
      (let
         val path = join expdir "sched-line.json"
         val _ = write_file path sched_line
       in
         path
       end)
    val _ = expect "Sched journal emits engine, HO, and exact winner fields"
      (JSONUtil.asString (JSONUtil.lookupField sched_json "engine") =
         "sched" andalso
       JSONUtil.asBool (JSONUtil.lookupField sched_json "ho") andalso
       JSONUtil.asString (JSONUtil.lookupField
         (JSONUtil.lookupField sched_json "winner") "format") = "fof" andalso
       JSONUtil.asString (JSONUtil.lookupField
         (hd (JSONUtil.arrayMap (fn item => item)
           (JSONUtil.lookupField sched_json "slices"))) "szs") = "Theorem")
    val v1_fixture = join "test-data/hheval-report/journal" "list.jsonl"
    val v1_line = hd (read_lines v1_fixture)
    val v1_entry = hhEval.parse_journal_line v1_line
    val _ = expect "checked-in v1 journal remains readable"
      (#goal_id v1_entry = "list.one" andalso #ho v1_entry = NONE andalso
       same_engine (#engine v1_entry) (hhEval.Prover "e") andalso
       #szs v1_entry = "Theorem" andalso null (#slices v1_entry))
    val v2_fixture = join "test-data" "hheval-journal-v2.jsonl"
    val v2_line = hd (read_lines v2_fixture)
    val v2_entry = hhEval.parse_journal_line v2_line
    val _ = expect "real Phase 1 v2 journal excerpt remains readable"
      (#goal_id v2_entry = "arithmetic.ZERO_LESS_EQ" andalso
       #prover v2_entry = "e" andalso #ho v2_entry = NONE andalso
       #nfacts v2_entry = 128)
    val mixed = hhEval.journal_path expdir "mixed"
    val _ = write_file mixed (v1_line ^ "\n" ^ v2_line ^ "\n")
    val _ = hhEval.append_journal mixed sched_entry
    val _ = expect "resume accepts mixed v1/v2/v3 journals"
      (hhEval.journal_complete mixed
         [("list.one", "deps-e"), ("arithmetic.ZERO_LESS_EQ", "b30-current-e"),
          ("list.scheduled", "sched")])
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
       "fixture" andalso
       JSONUtil.asInt (JSONUtil.lookupField header_json "schema") = 3)
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
    val _ = copy_fixture "sched.jsonl"
    fun subset_entry thm ho szs recon : hhEval.journal_entry =
      {run = #run full_entry, thy = "subset", thm = thm,
       goal_id = "subset." ^ thm, cond = "subset-fixture",
       regime = hhEval.Bushy, selector = hhEval.Deps,
       engine = hhEval.Prover "e", ho = SOME ho, prover = "e",
       prover_version = #prover_version full_entry, nfacts = 3, timeout = 6,
       szs = szs, t_prover = 0.1, axioms_used = NONE,
       recon_ok = recon, recon_method = NONE, t_recon = NONE, stac = NONE,
       error = NONE, stop = NONE, t_total = NONE, winner = NONE, slices = []}
    val subset_journal = join report_journal "subset.jsonl"
    val _ = hhEval.append_journal subset_journal
      (subset_entry "ho" true "Theorem" (SOME true))
    val _ = hhEval.append_journal subset_journal
      (subset_entry "first_order" false "Theorem" (SOME false))
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
    val sched_condition = named "cond" "sched-main" conditions
    val subset_condition = named "cond" "subset-fixture" conditions
    val subset_rows = array_field "subsets" subset_condition
    val ho_subset = named "subset" "HO" subset_rows
    val non_ho_subset = named "subset" "non-HO" subset_rows
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
    val _ = expect "report schedule counts and total-time quantiles"
      (metric "goals" sched_condition = 4 andalso
       metric "attempted" sched_condition = 4 andalso
       metric "proved" sched_condition = 3 andalso
       metric "reconstructed" sched_condition = 2 andalso
       same_real (JSONUtil.asNumber (JSONUtil.lookupField
         (JSONUtil.lookupField sched_condition "metrics") "t_prover_p50"))
         0.8 andalso
       same_real (JSONUtil.asNumber (JSONUtil.lookupField
         (JSONUtil.lookupField sched_condition "metrics") "t_prover_p90"))
         1.2)
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
    val distributions = array_field "schedule_distributions" summary
    val sched_distribution = named "cond" "sched-main" distributions
    val stop_rows = array_field "stop_reasons" sched_distribution
    val max_proofs = named "value" "MaxProofs" stop_rows
    val comparisons = array_field "schedule_vs_union" summary
    val comparison = named "condition" "sched-main" comparisons
    val contributions = array_field "slice_contributions" summary
    val _ = expect "report HO subset arithmetic and slice contributions"
      (metric "goals" ho_subset = 1 andalso
       metric "proved" ho_subset = 1 andalso
       metric "reconstructed" ho_subset = 1 andalso
       metric "goals" non_ho_subset = 1 andalso
       metric "proved" non_ho_subset = 1 andalso
       metric "reconstructed" non_ho_subset = 0 andalso
       List.exists (fn row =>
         JSONUtil.asString (JSONUtil.lookupField row "format") = "fof" andalso
         JSONUtil.asInt (JSONUtil.lookupField row "wins") >= 1)
         contributions andalso
       String.isSubstring "## HO subsets" report_text andalso
       String.isSubstring "| deps-e | HO | n/a |" report_text andalso
       String.isSubstring "## Slice contributions" report_text)
    val _ = expect "report schedule distributions"
      (JSONUtil.asInt (JSONUtil.lookupField max_proofs "count") = 2 andalso
       length (array_field "slices_run" sched_distribution) = 2 andalso
       String.isSubstring "2:1, 3:3" report_text andalso
       String.isSubstring "MaxProofs:2" report_text)
    val _ = expect "report schedule versus union comparison"
      (JSONUtil.asInt (JSONUtil.lookupField comparison "proved_delta") = ~1
       andalso JSONUtil.asInt
         (JSONUtil.lookupField comparison "reconstructed_delta") = 0 andalso
       String.isSubstring "## Schedule vs portfolio union" report_text andalso
       String.isSubstring "| sched-main | bushy/5s | 3 | 4 | -1 | 2 | 2 | 0 |"
         report_text)
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
                val root = OS.FileSys.tmpName ()
                val _ = remove_tree root
                val _ = mkdir root
                val add1 = DB.fetch "arithmetic" "ADD1"
                val success =
                  ((holyHammer.set_timeout 10;
                    ignore (holyHammer.hh_pb root ["e"]
                      ["arithmeticTheory.ADD1"] (Thm.dest_thm add1));
                    true)
                   handle Interrupt =>
                     raise Interrupt
                        | Feedback.HOL_ERR error =>
                     (print (Feedback.message_of error ^ "\n"); false)
                        | exn =>
                     (print (General.exnMessage exn ^ "\n"); false))
                val _ = hhConfig.hh_unset "timeout"
                val _ = remove_tree root
              in
                expect "holyHammer hh_pb end-to-end e" success
              end

val _ = test_szs_status_words ()
val _ = test_hhProver ()
val _ = test_hhSlice ()
val _ = test_hhCache ()
val _ = test_holyHammer_validation ()
val _ = test_runner ()
val _ = test_installed_provers ()
val _ = test_holyHammer_e ()

val schedule_fixture_dir = "test-data"
val schedule_printer = join schedule_fixture_dir "runner-print-e.sh"
val schedule_sleeper =
  join schedule_fixture_dir "runner-forking-sleeper.sh"

fun fixture_slice name extra size : hhProver.slice =
  {prover = name, format = "fof", type_enc = "", lam_trans = "",
   nfacts = 0, filter = "none", extra_opts = extra, slice_size = size}

fun printer_config name slices note parser : hhProver.prover_config =
  {name = name, exec_names = [schedule_printer], env_var = "",
   version_args = ["--version"], parse_version = fn _ => SOME "test",
   tested_versions = ["test"], supported_formats = ["fof"],
   mk_command = fn executable => fn request =>
     (note request; (executable, #extra request)),
   parse_output = parser, mono_instances = NONE,
   slices = fn () => slices, legacy = false}

fun sleeper_config name parser : hhProver.prover_config =
  let val slice = fixture_slice name [] 1 in
    {name = name, exec_names = [schedule_sleeper], env_var = "",
     version_args = ["--version"], parse_version = fn _ => SOME "test",
     tested_versions = ["test"], supported_formats = ["fof"],
     mk_command = fn executable => fn _ => (executable, []),
     parse_output = parser, mono_instances = NONE,
     slices = fn () => [slice], legacy = false}
  end

fun fixture_options provers slices cores timeout max_proofs cache cache_dir
    debug_dir : hhConfig.hh_options =
  {timeout = timeout, max_proofs = max_proofs, provers = provers,
   slices = slices, cores = cores, filter = "none", max_facts = NONE,
   format = "", type_enc = "", lam_trans = "", mono_iters = 3,
   mono_instances = NONE, minimize = true, preplay_timeout = 1.0,
   minimize_timeout = 1.0,
   cache = cache, cache_dir = cache_dir, cache_max_entries = 100,
   debug_dir = debug_dir}

fun without_minimization (options : hhConfig.hh_options)
    : hhConfig.hh_options =
  {timeout = #timeout options, max_proofs = #max_proofs options,
   provers = #provers options, slices = #slices options,
   cores = #cores options, filter = #filter options,
   max_facts = #max_facts options, format = #format options,
   type_enc = #type_enc options, lam_trans = #lam_trans options,
   mono_iters = #mono_iters options, mono_instances = #mono_instances options,
   minimize = false, preplay_timeout = #preplay_timeout options,
   minimize_timeout = #minimize_timeout options, cache = #cache options,
   cache_dir = #cache_dir options,
   cache_max_entries = #cache_max_entries options,
   debug_dir = #debug_dir options}

fun slice_event_tag (slice : hhProver.slice) =
  #prover slice ^ ":" ^ String.concatWith "," (#extra_opts slice)

fun stop_event_name hhSchedule.MaxProofs = "max-proofs"
  | stop_event_name hhSchedule.Timeout = "timeout"
  | stop_event_name hhSchedule.Exhausted = "exhausted"
  | stop_event_name hhSchedule.Interrupted = "interrupted"

fun szs_event_name hhProver.SzsTheorem = "theorem"
  | szs_event_name hhProver.SzsCounterSat = "counter-sat"
  | szs_event_name hhProver.SzsSatisfiable = "satisfiable"
  | szs_event_name hhProver.SzsGaveUp = "gave-up"
  | szs_event_name hhProver.SzsTimeout = "timeout"
  | szs_event_name hhProver.SzsResourceOut = "resource-out"
  | szs_event_name hhProver.SzsInappropriate = "inappropriate"
  | szs_event_name (hhProver.SzsUnknown status) = status
  | szs_event_name (hhProver.RunFailure message) = "failure:" ^ message

fun observe_schedule_event (hhSchedule.SliceStarted slice) =
      "started|" ^ slice_event_tag slice
  | observe_schedule_event (hhSchedule.SliceDone (slice, _, _)) =
      "done|" ^ slice_event_tag slice
  | observe_schedule_event (hhSchedule.ProofFound (slice, _)) =
      "found|" ^ slice_event_tag slice
  | observe_schedule_event (hhSchedule.Verified suggestion) =
      "verified|" ^ slice_event_tag (#slice suggestion)
  | observe_schedule_event (hhSchedule.ScheduleDone reason) =
      "schedule-done|" ^ stop_event_name reason

fun run_schedule_on goal options =
  let
    val events = ref ([] : string list)
    val result = hhSchedule.run
      {options = options, goal = goal, premises = [],
       progress = SOME (fn event =>
         events := observe_schedule_event event :: !events)}
  in
    (result, List.rev (!events))
  end

fun run_schedule options = run_schedule_on ([], boolSyntax.T) options

fun event_position wanted events =
  let
    fun seek _ [] = NONE
      | seek index (event :: rest) =
          if event = wanted then SOME index else seek (index + 1) rest
  in
    seek 0 events
  end

fun event_before left right events =
  case (event_position left events, event_position right events) of
      (SOME left_index, SOME right_index) => left_index < right_index
    | _ => false

fun event_suffix prefix event =
  String.extract (event, String.size prefix, NONE)

fun schedule_events_sane events =
  let
    fun with_prefix prefix = List.filter (String.isPrefix prefix) events
    fun follows earlier prefix event =
      event_before (earlier ^ event_suffix prefix event) event events
    val done = with_prefix "done|"
    val found = with_prefix "found|"
    val verified = with_prefix "verified|"
    val finished = with_prefix "schedule-done|"
  in
    not (null events) andalso length finished = 1 andalso
    hd (List.rev events) = hd finished andalso
    List.all (follows "started|" "done|") done andalso
    List.all (follows "done|" "found|") found andalso
    List.all (follows "found|" "verified|") verified
  end

fun output_files directory name =
  map (join directory)
    (List.filter (String.isPrefix (name ^ "-"))
      (hhConfig.directory_names directory))

fun fixture_child_gone directory name =
  case output_files directory name of
      [path] =>
        let
          val pid = pid_from_output (String.concat (read_lines path))
        in
          wait_until (Time.+ (Time.now (), Time.fromSeconds 5))
            (fn () => process_is_gone pid)
        end
    | _ => false

fun test_schedule_max_proofs parser =
  let
    val name = "hh-schedule-max-proofs"
    val slices =
      [fixture_slice name ["0", "schedule-truth.out"] 1,
       fixture_slice name ["0", "schedule-t-def.out"] 1]
    val config = printer_config name slices (fn _ => ()) parser
    val _ = hhProver.register config
    val options1 = fixture_options [name] 2 2 5 1 false "" NONE
    val options2 = fixture_options [name] 2 2 5 2 false "" NONE
    val (result1, _) = run_schedule options1
    val (result2, events2) = run_schedule options2
    val lemma_sets = map (#lemmas : hhSchedule.suggestion -> string list)
      (#suggestions result2)
    val _ = expect "scheduler max_proofs one stops after one verification"
      (#stopped result1 = hhSchedule.MaxProofs andalso
       length (#suggestions result1) = 1)
    val _ = expect "scheduler max_proofs two verifies two suggestions"
      (#stopped result2 = hhSchedule.MaxProofs andalso
       length (#suggestions result2) = 2 andalso
       List.exists (fn lemmas => lemmas = ["boolTheory.TRUTH"])
         lemma_sets andalso
       List.exists (fn lemmas => lemmas = ["boolTheory.T_DEF"])
         lemma_sets)
    val _ = expect "scheduler event ordering is sane"
      (schedule_events_sane events2)
    val _ = expect "scheduler exports the zero-fact prefix"
      (OS.FileSys.access
        (hhSchedule.problem_path (fixture_slice name [] 1),
         [OS.FileSys.A_READ]))
  in
    ()
  end

fun test_schedule_reconstruction_failure parser =
  let
    val name = "hh-schedule-reconstruction-failure"
    val bad_recording = "schedule-unreconstructable.out"
    val slices =
      [fixture_slice name ["0", bad_recording] 1,
       fixture_slice name ["0", "schedule-add1.out"] 1]
    val config = printer_config name slices (fn _ => ()) parser
    val (bad_status, bad_axioms) =
      parser (read_lines (join schedule_fixture_dir bad_recording))
    val (good_status, good_axioms) =
      parser
        (read_lines (join schedule_fixture_dir "schedule-add1.out"))
    val _ = hhProver.register config
    val options = fixture_options [name] 2 1 5 1 false "" NONE
    val goal = ([], Thm.concl (DB.fetch "arithmetic" "ADD1"))
    val (result, events) = run_schedule_on goal options
    val found = List.filter (String.isPrefix "found|") events
    val verified = List.filter (String.isPrefix "verified|") events
    val _ = expect "unreconstructable scheduler recording parses as theorem"
      (bad_status = hhProver.SzsTheorem andalso
       bad_axioms = SOME ["fixtureTheory.unreconstructable"])
    val _ = expect "replayable scheduler recording parses as theorem"
      (good_status = hhProver.SzsTheorem andalso
       good_axioms = SOME ["arithmeticTheory.ADD1"])
    val _ = expect "both reconstruction results are discovered"
      (length found = 2)
    val _ = expect "only the replayable reconstruction verifies"
      (length verified = 1)
    val _ = expect "failed reconstruction does not stop the schedule"
      (#stopped result = hhSchedule.MaxProofs andalso
       case #suggestions result of
           [suggestion] =>
             #lemmas suggestion = ["arithmeticTheory.ADD1"]
         | _ => false)
  in
    ()
  end

fun test_schedule_without_minimization () =
  let
    val name = "hh-schedule-no-minimize"
    val lemmas = ["boolTheory.TRUTH", "boolTheory.T_DEF"]
    val slice = fixture_slice name ["0", "schedule-truth.out"] 1
    val config = printer_config name [slice] (fn _ => ())
      (fn _ => (hhProver.SzsTheorem, SOME lemmas))
    val _ = hhProver.register config
    val options = without_minimization
      (fixture_options [name] 1 1 5 1 false "" NONE)
    val (result, _) = run_schedule options
    val _ = expect "scheduler minimize=false preserves the ATP lemma list"
      (case #suggestions result of
           [suggestion] => #stac suggestion = mlThmData.mk_metis_call lemmas
         | _ => false)
  in
    ()
  end

fun test_schedule_early_stop parser =
  let
    val slow1 = "hh-schedule-slow-one"
    val fast = "hh-schedule-fast"
    val slow2 = "hh-schedule-slow-two"
    val fast_slices =
      [fixture_slice fast ["2", "schedule-truth.out"] 1]
    val debug = OS.FileSys.tmpName ()
    val _ = remove_tree debug
    val _ = hhProver.register (sleeper_config slow1 parser)
    val _ = hhProver.register
      (printer_config fast fast_slices (fn _ => ()) parser)
    val _ = hhProver.register (sleeper_config slow2 parser)
    val options = fixture_options [slow1, fast, slow2] 3 3 12 1 false ""
      (SOME debug)
    val (result, events) = run_schedule options
    val children_gone =
      fixture_child_gone debug slow1 andalso fixture_child_gone debug slow2
    val early_stop_ok =
      #stopped result = hhSchedule.MaxProofs andalso
      length (#suggestions result) = 1
    val _ =
      if early_stop_ok then ()
      else
        print ("early-stop diagnostic: stopped=" ^
          stop_event_name (#stopped result) ^ ", suggestions=" ^
          Int.toString (length (#suggestions result)) ^ ", slices=" ^
          Int.toString (length (#slices_run result)) ^ ", total=" ^
          Real.toString (#t_total result) ^ ", events=" ^
          String.concatWith ";" events ^ ", results=" ^
          String.concatWith ";"
            (map (fn (slice, status, elapsed, _) =>
              slice_event_tag slice ^ ":" ^ szs_event_name status ^ ":" ^
              Real.toString elapsed) (#slices_run result)) ^ "\n")
    val _ = expect "scheduler early stop follows a verified proof"
      early_stop_ok
    val _ = expect "scheduler early stop returns below the slice budget"
      (#t_total result < 8.0)
    val _ = expect "scheduler early stop kills laggard process groups"
      children_gone
    val _ = remove_tree debug
  in
    ()
  end

fun test_schedule_budget_truncation parser =
  let
    val name = "hh-schedule-budget"
    val first = fixture_slice name ["2", "e-gave-up.out"] 1
    val second = fixture_slice name ["0", "e-gave-up.out"] 4
    val budgets = ref ([] : int list)
    fun note (request : hhProver.run_request) =
      budgets := !budgets @ [#timeout request]
    val config = printer_config name [first, second] note parser
    val _ = hhProver.register config
    val options = fixture_options [name] 2 1 4 1 false "" NONE
    val (result, _) = run_schedule options
    val wanted = Real.ceil (hhSlice.slice_budget 2 options second)
    val _ = expect "late scheduler slice receives a truncated budget"
      (#stopped result = hhSchedule.Exhausted andalso
       case !budgets of
           [first_budget, second_budget] =>
             first_budget = 2 andalso second_budget < wanted
         | _ => false)
  in
    ()
  end

fun test_schedule_cache parser =
  let
    val name = "hh-schedule-cache"
    val slice = fixture_slice name ["0", "schedule-truth.out"] 1
    val config = printer_config name [slice] (fn _ => ()) parser
    val root = OS.FileSys.tmpName ()
    val cache = join root "cache"
    val _ = remove_tree root
    val _ = mkdir root
    val _ = hhProver.register config
    val options = fixture_options [name] 1 1 5 1 true cache NONE
    val _ = hhProver.reset_spawn_count ()
    val (first, _) = run_schedule options
    val first_spawns = hhProver.spawn_count ()
    val _ = hhProver.reset_spawn_count ()
    val (second, _) = run_schedule options
    val second_spawns = hhProver.spawn_count ()
    val first_cached = map #4 (#slices_run first)
    val second_cached = map #4 (#slices_run second)
    val _ = expect "scheduler cache hit spawns no processes"
      (#stopped first = hhSchedule.MaxProofs andalso first_spawns > 0 andalso
       List.all not first_cached andalso
       #stopped second = hhSchedule.MaxProofs andalso
       length (#suggestions second) = 1 andalso
       List.all (fn cached => cached) second_cached andalso
       second_spawns = 0)
    val _ = remove_tree root
  in
    ()
  end

fun test_schedule_timeout parser =
  let
    val name = "hh-schedule-timeout"
    val debug = OS.FileSys.tmpName ()
    val _ = remove_tree debug
    val _ = hhProver.register (sleeper_config name parser)
    val options = fixture_options [name] 1 1 1 1 false "" (SOME debug)
    val (result, events) = run_schedule options
    val child_gone = fixture_child_gone debug name
    val _ = expect "scheduler timeout stop reason is reachable"
      (#stopped result = hhSchedule.Timeout andalso
       null (#suggestions result) andalso #t_total result < 7.0 andalso
       child_gone andalso schedule_events_sane events)
    val _ = remove_tree debug
  in
    ()
  end

fun test_schedule_export_wiring () =
  let
    val e = prover "e"
    val vampire = prover "vampire"
    fun options mono_instances : hhConfig.hh_options =
      {timeout = 30, max_proofs = 1, provers = ["e"], slices = 1, cores = 1,
       filter = "none", max_facts = NONE, format = "", type_enc = "",
       lam_trans = "", mono_iters = 3, mono_instances = mono_instances,
       minimize = true, preplay_timeout = 1.0, minimize_timeout = 1.0,
       cache = false, cache_dir = "", cache_max_entries = 100,
       debug_dir = NONE}
    fun slice type_enc lam_trans : hhProver.slice =
      {prover = "e", format = "fof", type_enc = type_enc,
       lam_trans = lam_trans, nfacts = 0, filter = "none",
       extra_opts = [], slice_size = 1}
    val legacy = slice "" ""
    val lifting = slice "mono_guards" "lifting"
    val combs = slice "mono_guards" "combs"
    val goal = ([], boolSyntax.T)
    val legacy_path = hhSchedule.problem_path legacy
    val lifting_path = hhSchedule.problem_path lifting
    val combs_path = hhSchedule.problem_path combs
    val _ = List.app (remove_tree o OS.Path.dir)
      [legacy_path, lifting_path, combs_path]
    val expected_dir = OS.FileSys.tmpName ()
    val _ = OS.FileSys.remove expected_dir
    val _ = mkdir expected_dir
    val _ = hhExportFof.fof_export_pb expected_dir (boolSyntax.T, [])
    val _ = hhSchedule.export_problems (options NONE) goal [] [(e, legacy)]
    val legacy_empty_text = String.concat (read_lines legacy_path)
    val _ = expect "legacy scheduler dispatch is byte-identical"
      (legacy_empty_text =
       String.concat (read_lines (join expected_dir "atp_in")))
    val _ = hhSchedule.export_problems (options NONE) goal
      ["boolTheory.TRUTH"] [(e, legacy)]
    val _ = expect "filter=none exports premises beyond the slice fact count"
      (legacy_empty_text <> String.concat (read_lines legacy_path))
    val _ = hhSchedule.export_problems (options NONE) goal []
      [(e, lifting), (e, combs), (e, lifting)]
    val lifting_text = String.concat (read_lines lifting_path)
    val _ = expect "problem exports re-key full triples"
      (lifting_path <> combs_path andalso OS.FileSys.access (lifting_path, [])
       andalso OS.FileSys.access (combs_path, []))
    val _ = expect "nonlegacy triple dispatches to hhProblemGen"
      (contains "generated by hhProblemGen" lifting_text)
    val _ = expect "registry mono-instance override wins over default"
      (contains "mono_instances=128" lifting_text)
    val _ = hhSchedule.export_problems (options (SOME 77)) goal [] [(e, lifting)]
    val _ = expect "explicit mono-instance option beats registry override"
      (contains "mono_instances=77" (String.concat (read_lines lifting_path)))
    fun mono_slice prover : hhProver.slice =
      {prover = prover, format = "th0", type_enc = "mono_native_higher",
       lam_trans = "keep_lams", nfacts = 0, filter = "none",
       extra_opts = [], slice_size = 1}
    val e_mono = mono_slice "e"
    val vampire_mono = mono_slice "vampire"
    val _ = hhSchedule.export_problems (options NONE) goal []
      [(e, e_mono), (vampire, vampire_mono)]
    val e_mono_path = hhSchedule.problem_path e_mono
    val vampire_mono_path = hhSchedule.problem_path vampire_mono
    val _ = expect "prover-specific monomorphization exports stay distinct"
      (e_mono_path <> vampire_mono_path andalso
       contains "mono_instances=128"
         (String.concat (read_lines e_mono_path)) andalso
       contains "mono_instances=256"
         (String.concat (read_lines vampire_mono_path)))
    val _ = remove_tree expected_dir
  in
    ()
  end

fun test_hhSchedule () =
  case OS.Process.getEnv "HHCONFIG_TEST_ROOT" of
      SOME _ => ()
    | NONE =>
        let
          val parser = #parse_output (prover "e")
          val started = Time.now ()
          val _ = test_schedule_max_proofs parser
          val _ = test_schedule_reconstruction_failure parser
          val _ = test_schedule_without_minimization ()
          val _ = test_schedule_early_stop parser
          val _ = test_schedule_budget_truncation parser
          val _ = test_schedule_cache parser
          val _ = test_schedule_timeout parser
        in
          expect "scheduler hermetic suite stays within its wall-time bound"
            (Time.toReal (Time.- (Time.now (), started)) < 60.0)
        end

val _ = test_schedule_export_wiring ()
val _ = test_hhSchedule ()

fun with_hh_options settings action =
  let
    fun clear () = List.app (hhConfig.hh_unset o #1) settings
    val _ = List.app hhConfig.hh_set settings
  in
    (action () before clear ())
    handle exn => (clear (); raise exn)
  end

fun test_main_hh_lemmas_hook parser =
  let
    val name = "hh-main-lemmas-hook"
    val launches = ref 0
    val slices =
      [fixture_slice name ["0", "schedule-truth.out"] 1,
       fixture_slice name ["5", "schedule-t-def.out"] 1,
       fixture_slice name ["0", "schedule-add1.out"] 1]
    fun note _ = launches := !launches + 1
    val _ = hhProver.register (printer_config name slices note parser)
    val settings =
      [("provers", name), ("slices", "3"), ("cores", "1"),
       ("timeout", "5"), ("filter", "none"), ("debug_dir", "")]
    val lemmas = with_hh_options settings (fn () =>
      holyHammer.main_hh_lemmas "/ignored" mlThmData.empty_thmdata
        ([], boolSyntax.T))
    val _ = expect "main_hh_lemmas returns scheduler suggestion lemmas"
      (lemmas = SOME ["boolTheory.TRUTH"])
    val _ = expect "interactive HolyHammer stops after one verified proof"
      (!launches < length slices)
  in
    ()
  end

fun test_holyHammer_unverified_failure parser =
  let
    val name = "hh-main-unverified"
    val slice = fixture_slice name
      ["0", "schedule-unreconstructable.out"] 1
    val debug = OS.FileSys.tmpName ()
    val _ = remove_tree debug
    val _ = hhProver.register
      (printer_config name [slice] (fn _ => ()) parser)
    val settings =
      [("provers", name), ("slices", "1"), ("cores", "1"),
       ("timeout", "5"), ("filter", "none"), ("debug_dir", debug)]
    val goal = ([], Thm.concl (DB.fetch "arithmetic" "ADD1"))
    val message = with_hh_options settings (fn () =>
      hh_error (fn () => ignore
        (holyHammer.main_hh "/ignored" mlThmData.empty_thmdata
          goal)))
    val problem = hhSchedule.problem_path (fixture_slice name [] 1)
    val _ = expect "unverified ATP proofs are reported with diagnostics"
      (case message of
           SOME text =>
             contains name text andalso
             contains "fixtureTheory.unreconstructable" text andalso
             contains problem text andalso contains debug text andalso
             contains "output:" text
         | NONE => false)
    val _ = remove_tree debug
  in
    ()
  end

fun test_holyHammer_scheduler_api () =
  case OS.Process.getEnv "HHCONFIG_TEST_ROOT" of
      SOME _ => ()
    | NONE =>
        let val parser = #parse_output (prover "e") in
          test_main_hh_lemmas_hook parser;
          test_holyHammer_unverified_failure parser
        end

val _ = test_holyHammer_scheduler_api ()

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
             selector = hhEval.Deps, engine = hhEval.Prover "e", timeout = 1,
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

val _ = expect "hhEval legacy smoke has twelve prover goals and one schedule goal"
  (length hhEval.smoke_goals = 13 andalso
   length (List.filter (fn (_, _, engine) => engine = "sched")
     hhEval.smoke_goals) = 1)

val _ = expect "hhEval smoke covers every pinned prover four times"
  (List.all (fn prover =>
     length (List.filter (fn (_, _, item) => item = prover)
       hhEval.smoke_goals) = 4)
   ["e", "vampire", "zipperposition"])

local open hhReconstruct hhTranslate holyHammer hhExportLib hhExportFof
  hhExportTf0 hhExportTh0 hhExportTf1 hhExportTh1 hhConfig hhProver hhSlice
  hhCache hhSchedule
in end
