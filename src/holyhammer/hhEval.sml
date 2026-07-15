(* ========================================================================= *)
(* FILE          : hhEval.sml                                                *)
(* DESCRIPTION   : HolyHammer evaluation corpus and durable journal          *)
(* ========================================================================= *)

structure hhEval :> hhEval =
struct

open HolKernel boolLib aiLib

datatype regime = Bushy | Chainy
datatype selector = Deps | Knn of int

type condition =
  {cond_id : string, regime : regime, selector : selector,
   prover : string, timeout : int, reconstruct : bool}

type journal_entry =
  {run : string, thy : string, thm : string, goal_id : string,
   cond : string, regime : regime, selector : selector,
   prover : string, prover_version : string option, nfacts : int,
   timeout : int, szs : string, t_prover : real,
   axioms_used : string list option, recon_ok : bool option,
   recon_method : string option, t_recon : real option,
   stac : string option, error : string option}

type corpus_coverage =
  {srcfiles : string list, dat_theories : string list,
   added_from_dat : string list}

type corpus_entry =
  {thy : string, theorem_count : int, dep_stamp : string}

type prover_identity =
  {name : string, path : string option, version : string option,
   sha256 : string option}

type run_header =
  {expname : string, date : string, host : string, hol_commit : string,
   provers : prover_identity list, corpus : corpus_entry list,
   added_from_dat : string list, conditions : condition list, sample : int}

type completed = (string * string) list

fun join left right = OS.Path.concat (left, right)

fun is_dir path = OS.FileSys.isDir path handle OS.SysErr _ => false

fun ensure_dir path =
  if path = "" orelse is_dir path then ()
  else
    let
      val parent = OS.Path.dir path
      val _ = if parent = path then () else ensure_dir parent
    in
      OS.FileSys.mkDir path
      handle OS.SysErr _ =>
        if is_dir path then () else raise Fail ("cannot create " ^ path)
    end

fun trim_left text =
  let
    fun loop index =
      if index < String.size text andalso
         Char.isSpace (String.sub (text, index)) then loop (index + 1)
      else index
  in
    String.extract (text, loop 0, NONE)
  end

fun trim_right text =
  let
    fun loop index =
      if index > 0 andalso Char.isSpace (String.sub (text, index - 1)) then
        loop (index - 1)
      else index
  in
    String.substring (text, 0, loop (String.size text))
  end

fun trim text = trim_right (trim_left text)

fun ends_with suffix text =
  let val start = String.size text - String.size suffix in
    start >= 0 andalso String.extract (text, start, NONE) = suffix
  end

fun insert item [] = [item]
  | insert item (head :: tail) =
      if String.compare (item, head) = LESS then item :: head :: tail
      else head :: insert item tail

fun sort [] = []
  | sort (head :: tail) = insert head (sort tail)

fun unique [] = []
  | unique [item] = [item]
  | unique (first :: second :: rest) =
      if first = second then unique (second :: rest)
      else first :: unique (second :: rest)

fun sorted_unique items = unique (sort items)

fun string_of_regime Bushy = "bushy"
  | string_of_regime Chainy = "chainy"

fun string_of_selector Deps = "deps"
  | string_of_selector (Knn count) = "knn" ^ Int.toString count

fun regime_of_string "bushy" = Bushy
  | regime_of_string "chainy" = Chainy
  | regime_of_string text = raise Fail ("unknown evaluation regime: " ^ text)

fun selector_of_string "deps" = Deps
  | selector_of_string text =
      if String.isPrefix "knn" text then
        (case Int.fromString (String.extract (text, 3, NONE)) of
             SOME count => Knn count
           | NONE => raise Fail ("bad evaluation selector: " ^ text))
      else raise Fail ("unknown evaluation selector: " ^ text)

fun json_condition {cond_id, regime, selector, prover, timeout, reconstruct} =
  JSON.OBJECT
    [("cond_id", JSON.STRING cond_id),
     ("regime", JSON.STRING (string_of_regime regime)),
     ("selector", JSON.STRING (string_of_selector selector)),
     ("prover", JSON.STRING prover),
     ("timeout", JSON.INT (IntInf.fromInt timeout)),
     ("reconstruct", JSON.BOOL reconstruct)]

fun parse_json text =
  let
    val source = JSONParser.openString text
    val value = JSONParser.parse source
    val _ = JSONParser.close source
  in
    value
  end

fun field name value = JSONUtil.lookupField value name

fun string_field name value = JSONUtil.asString (field name value)
fun int_field name value = JSONUtil.asInt (field name value)
fun real_field name value = JSONUtil.asNumber (field name value)
fun bool_field name value = JSONUtil.asBool (field name value)

fun option_field decoder name value =
  case field name value of JSON.NULL => NONE | item => SOME (decoder item)

fun parse_condition_value value : condition =
  {cond_id = string_field "cond_id" value,
   regime = regime_of_string (string_field "regime" value),
   selector = selector_of_string (string_field "selector" value),
   prover = string_field "prover" value,
   timeout = int_field "timeout" value,
   reconstruct = bool_field "reconstruct" value}

fun encode_condition condition =
  JSONPrinter.valueToString (json_condition condition)

fun parse_condition text = parse_condition_value (parse_json text)

fun theory_of_srcfile line =
  let
    val path = trim line
    val file = OS.Path.file path
    val name = String.substring (file, 0, String.size file - 6)
  in
    if String.isSubstring "/src/" path andalso ends_with "Theory" file andalso
       name <> "" then SOME name else NONE
  end
  handle Subscript => NONE

fun theories_from_srcfile_lines lines =
  sorted_unique (List.mapPartial theory_of_srcfile lines)

fun read_lines path =
  let
    val input = TextIO.openIn path
    fun loop lines =
      case TextIO.inputLine input of
          NONE => List.rev lines
        | SOME line => loop (line :: lines)
    val result = loop []
    val _ = TextIO.closeIn input
  in
    result
  end

fun theories_from_srcfiles path = theories_from_srcfile_lines (read_lines path)

fun directory_names path =
  let
    val stream = OS.FileSys.openDir path
    fun loop names =
      case OS.FileSys.readDir stream of
          NONE => List.rev names
        | SOME name => loop (name :: names)
    val result = loop []
    val _ = OS.FileSys.closeDir stream
  in
    result
  end
  handle OS.SysErr _ => []

fun dat_theories_under root =
  let
    fun walk directory =
      List.concat (map (fn name =>
        let val path = join directory name in
          if is_dir path then walk path
          else if ends_with "Theory.dat" name then
            [String.substring (name, 0, String.size name - 10)]
          else []
        end) (directory_names directory))
  in
    sorted_unique (walk root)
  end

val theory_dat_theories = dat_theories_under

fun coverage_check {srcfiles, dat_theories} =
  List.filter (fn theory => not (List.exists (fn name => name = theory)
                                  srcfiles)) dat_theories

fun holdir () =
  case OS.Process.getEnv "HOLDIR" of
      SOME directory => directory
    | NONE => raise Fail "HOLDIR is not set"

fun stdlib_coverage () =
  let
    val root = holdir ()
    val srcfiles = theories_from_srcfiles (join (join root "sigobj") "SRCFILES")
    val dat_theories = dat_theories_under (join root "src")
    val added_from_dat = coverage_check
      {srcfiles = srcfiles, dat_theories = dat_theories}
  in
    {srcfiles = srcfiles, dat_theories = dat_theories,
     added_from_dat = added_from_dat}
  end

fun stdlib_theories () =
  let
    val {srcfiles, added_from_dat, ...} = stdlib_coverage ()
    val _ =
      if null added_from_dat then ()
      else TextIO.output (TextIO.stdErr,
        "hhEval: adding " ^ Int.toString (length added_from_dat) ^
        " theories absent from sigobj/SRCFILES\n")
  in
    sorted_unique (srcfiles @ added_from_dat)
  end

fun eval_dir () =
  case hhConfig.get_path "eval.dir" of
      SOME directory => directory
    | NONE => join (join (join (holdir ()) "src") "holyhammer") "eval"

fun experiment_dir expname = join (eval_dir ()) expname
fun journal_path expdir theory =
  join (join expdir "journal") (theory ^ ".jsonl")

fun json_string_option NONE = JSON.NULL
  | json_string_option (SOME text) = JSON.STRING text

fun json_real_option NONE = JSON.NULL
  | json_real_option (SOME number) = JSON.FLOAT number

fun json_bool_option NONE = JSON.NULL
  | json_bool_option (SOME truth) = JSON.BOOL truth

fun json_string_list_option NONE = JSON.NULL
  | json_string_list_option (SOME items) = JSON.ARRAY (map JSON.STRING items)

fun journal_json
    {run, thy, thm, goal_id, cond, regime, selector, prover,
     prover_version, nfacts, timeout, szs, t_prover, axioms_used,
     recon_ok, recon_method, t_recon, stac, error} =
  JSON.OBJECT
    [("run", JSON.STRING run), ("thy", JSON.STRING thy),
     ("thm", JSON.STRING thm), ("goal_id", JSON.STRING goal_id),
     ("cond", JSON.STRING cond),
     ("regime", JSON.STRING (string_of_regime regime)),
     ("selector", JSON.STRING (string_of_selector selector)),
     ("prover", JSON.STRING prover),
     ("prover_version", json_string_option prover_version),
     ("nfacts", JSON.INT (IntInf.fromInt nfacts)),
     ("timeout", JSON.INT (IntInf.fromInt timeout)),
     ("szs", JSON.STRING szs), ("t_prover", JSON.FLOAT t_prover),
     ("axioms_used", json_string_list_option axioms_used),
     ("recon_ok", json_bool_option recon_ok),
     ("recon_method", json_string_option recon_method),
     ("t_recon", json_real_option t_recon),
     ("stac", json_string_option stac), ("error", json_string_option error)]

fun string_list value = JSONUtil.arrayMap JSONUtil.asString value

fun parse_journal_value value : journal_entry =
  {run = string_field "run" value, thy = string_field "thy" value,
   thm = string_field "thm" value, goal_id = string_field "goal_id" value,
   cond = string_field "cond" value,
   regime = regime_of_string (string_field "regime" value),
   selector = selector_of_string (string_field "selector" value),
   prover = string_field "prover" value,
   prover_version = option_field JSONUtil.asString "prover_version" value,
   nfacts = int_field "nfacts" value, timeout = int_field "timeout" value,
   szs = string_field "szs" value, t_prover = real_field "t_prover" value,
   axioms_used = option_field string_list "axioms_used" value,
   recon_ok = option_field JSONUtil.asBool "recon_ok" value,
   recon_method = option_field JSONUtil.asString "recon_method" value,
   t_recon = option_field JSONUtil.asNumber "t_recon" value,
   stac = option_field JSONUtil.asString "stac" value,
   error = option_field JSONUtil.asString "error" value}

fun encode_journal_line entry = JSONPrinter.valueToString (journal_json entry)
fun parse_journal_line text = parse_journal_value (parse_json text)

fun append_journal path entry =
  let
    val _ = ensure_dir (OS.Path.dir path)
    val output = TextIO.openAppend path
    val _ = TextIO.output (output, encode_journal_line entry ^ "\n")
    val _ = TextIO.flushOut output
    val _ = TextIO.closeOut output
  in
    ()
  end

fun read_journal path =
  if OS.FileSys.access (path, [OS.FileSys.A_READ]) then
    List.map parse_journal_line
      (List.filter (fn line => trim line <> "") (read_lines path))
  else []
  handle OS.SysErr _ => []

fun add_completed entry pairs =
  let val pair = (#goal_id entry, #cond entry) in
    if List.exists (fn item => item = pair) pairs then pairs else pair :: pairs
  end

fun read_completed path =
  List.foldl (fn (entry, pairs) => add_completed entry pairs) []
    (read_journal path)

fun cell_completed pairs pair = List.exists (fn item => item = pair) pairs

fun journal_complete path cells =
  let val pairs = read_completed path in
    List.all (cell_completed pairs) cells
  end

fun read_command path arguments =
  let
    val process = Unix.execute (path, arguments)
    val (input, output) = Unix.streamsOf process
    val _ = TextIO.closeOut output
    val text = TextIO.inputAll input
    val _ = TextIO.closeIn input
    val _ = Unix.reap process
  in
    SOME text
  end
  handle OS.SysErr _ => NONE | IO.Io _ => NONE

fun first_word text =
  case String.tokens Char.isSpace text of [] => NONE | word :: _ => SOME word

fun sha256 path =
  let
    fun digest executable arguments =
      case read_command executable arguments of
          NONE => NONE
        | SOME output => first_word output
  in
    if OS.FileSys.access (path, [OS.FileSys.A_READ]) then
      case digest "/usr/bin/sha256sum" [path] of
          SOME hash => SOME hash
        | NONE => digest "/usr/bin/shasum" ["-a", "256", path]
    else NONE
  end
  handle OS.SysErr _ => NONE

fun distinct_names names =
  let
    fun loop seen [] = List.rev seen
      | loop seen (name :: rest) =
          if List.exists (fn old => old = name) seen then loop seen rest
          else loop (name :: seen) rest
  in
    loop [] names
  end

fun prover_identity name =
  case hhProver.lookup name of
      NONE => {name = name, path = NONE, version = NONE, sha256 = NONE}
    | SOME config =>
        (case hhProver.probe config of
             NONE => {name = name, path = NONE, version = NONE, sha256 = NONE}
           | SOME {path, version, ...} =>
               {name = name, path = SOME path, version = version,
                sha256 = sha256 path})

fun current_prover_identities conditions =
  map prover_identity (distinct_names (map #prover conditions))

fun host_name () =
  case List.find (fn (name, _) => name = "nodename")
                 (Posix.ProcEnv.uname ()) of
      SOME (_, host) => host
    | NONE => "unknown"

fun hol_commit () =
  case read_command "/usr/bin/git" ["rev-parse", "HEAD"] of
      SOME output =>
        (case first_word output of SOME hash => hash | NONE => "unknown")
    | NONE => "unknown"

fun loaded_corpus_entry thy =
  {thy = thy, theorem_count = length (DB.theorems thy),
   dep_stamp = Theory.hash thy}

fun new_run_header
    {expname, corpus, added_from_dat, conditions, sample} =
  {expname = expname, date = Date.toString (Date.fromTimeLocal (Time.now ())),
   host = host_name (), hol_commit = hol_commit (),
   provers = current_prover_identities conditions, corpus = corpus,
   added_from_dat = added_from_dat, conditions = conditions, sample = sample}

fun json_prover {name, path, version, sha256} =
  JSON.OBJECT
    [("name", JSON.STRING name), ("path", json_string_option path),
     ("version", json_string_option version),
     ("sha256", json_string_option sha256)]

fun json_corpus_entry {thy, theorem_count, dep_stamp} =
  JSON.OBJECT
    [("thy", JSON.STRING thy),
     ("theorem_count", JSON.INT (IntInf.fromInt theorem_count)),
     ("dep_stamp", JSON.STRING dep_stamp)]

fun header_json
    {expname, date, host, hol_commit, provers, corpus, added_from_dat,
     conditions, sample} =
  JSON.OBJECT
    [("expname", JSON.STRING expname), ("date", JSON.STRING date),
     ("host", JSON.STRING host), ("hol_commit", JSON.STRING hol_commit),
     ("provers", JSON.ARRAY (map json_prover provers)),
     ("corpus", JSON.ARRAY (map json_corpus_entry corpus)),
     ("added_from_dat", JSON.ARRAY (map JSON.STRING added_from_dat)),
     ("conditions", JSON.ARRAY (map json_condition conditions)),
     ("sample", JSON.INT (IntInf.fromInt sample))]

fun write_run_header expdir header =
  let
    val _ = ensure_dir expdir
    val output = TextIO.openOut (join expdir "run.json")
    val _ = JSONPrinter.printFmt (output, header_json header)
    val _ = TextIO.output (output, "\n")
    val _ = TextIO.flushOut output
    val _ = TextIO.closeOut output
  in
    ()
  end

fun sample_hash text =
  let
    val modulus = IntInf.fromInt 2147483647
    fun step (character, value) =
      IntInf.mod (value * 65599 + IntInf.fromInt (Char.ord character), modulus)
  in
    List.foldl step 0 (String.explode text)
  end

fun sample_goal factor goal_id =
  if factor < 1 then raise Fail "--sample must be a positive integer"
  else IntInf.mod (sample_hash goal_id, IntInf.fromInt factor) = 0

(* -------------------------------------------------------------------------
   Evaluation driver and per-theory workers
   ------------------------------------------------------------------------- *)

val worker_conditions = ref ([] : condition list)
val worker_sample = ref 1

fun set_worker_settings {conditions, sample} =
  if sample < 1 then raise Fail "eval.sample must be a positive integer"
  else (worker_conditions := conditions; worker_sample := sample)

fun run_name expdir = OS.Path.file expdir

fun safe_component text =
  String.map (fn character =>
    if Char.isAlphaNum character orelse character = #"_" orelse
       character = #"-" then character else #"_") text

fun goal_id thy name = thy ^ "." ^ name

fun szs_name hhProver.SzsTheorem = "Theorem"
  | szs_name hhProver.SzsCounterSat = "CounterSatisfiable"
  | szs_name hhProver.SzsSatisfiable = "Satisfiable"
  | szs_name hhProver.SzsGaveUp = "GaveUp"
  | szs_name hhProver.SzsTimeout = "Timeout"
  | szs_name hhProver.SzsResourceOut = "ResourceOut"
  | szs_name hhProver.SzsInappropriate = "Inappropriate"
  | szs_name (hhProver.SzsUnknown name) = name
  | szs_name (hhProver.RunFailure _) = "RunFailure"

fun run_failure_error (hhProver.RunFailure message) = SOME message
  | run_failure_error _ = NONE

fun base_entry expdir thy name condition nfacts szs t_prover axioms version =
  {run = run_name expdir, thy = thy, thm = name, goal_id = goal_id thy name,
   cond = #cond_id condition, regime = #regime condition,
   selector = #selector condition, prover = #prover condition,
   prover_version = version, nfacts = nfacts, timeout = #timeout condition,
   szs = szs, t_prover = t_prover, axioms_used = axioms,
   recon_ok = NONE, recon_method = NONE, t_recon = NONE, stac = NONE,
   error = NONE} : journal_entry

fun journal_theory_error expdir thy message =
  let
    val condition : condition =
      {cond_id = "__load__", regime = Bushy, selector = Deps,
       prover = "", timeout = 0, reconstruct = false}
    val entry = base_entry expdir thy "__load__" condition 0 "LoadFailure"
      0.0 NONE NONE
    val entry =
      {run = #run entry, thy = #thy entry, thm = #thm entry,
       goal_id = #goal_id entry, cond = #cond entry, regime = #regime entry,
       selector = #selector entry, prover = #prover entry,
       prover_version = #prover_version entry, nfacts = #nfacts entry,
       timeout = #timeout entry, szs = #szs entry, t_prover = #t_prover entry,
       axioms_used = #axioms_used entry, recon_ok = #recon_ok entry,
       recon_method = #recon_method entry, t_recon = #t_recon entry,
       stac = #stac entry, error = SOME message}
  in
    append_journal (journal_path expdir thy) entry
  end

fun pool_ids (thyl, thmidl) =
  map (fn (theory, name) => theory ^ "Theory." ^ name)
    (List.concat (map hhExportLib.thmidl_in_thy thyl) @ thmidl)

fun chainy_pools thy =
  let
    val order = hhExportLib.sorted_ancestry [thy]
    fun one ((_, name), pool) = (name, pool_ids pool)
  in
    map one (hhExportLib.chainy_dep order thy (DB.theorems thy))
  end

fun lookup_pool name pools =
  case List.find (fn (other, _) => other = name) pools of
      SOME (_, pool) => pool
    | NONE => []

fun select_knn pool count goal =
  let
    val (weights, features) = mlThmData.create_thmdata ()
    val permitted = List.filter (fn (name, _) =>
      List.exists (fn allowed => allowed = name) pool) features
  in
    mlNearestNeighbor.thmknn_wdep (weights, permitted) count
      (mlFeature.fea_of_goal true goal)
  end

fun selected_premises condition pool thm goal =
  case #selector condition of
      Deps =>
        let val dependencies = #2 (mlThmData.intactdep_of_thm thm) in
          case #regime condition of
              Bushy => dependencies
            | Chainy => List.filter (fn name =>
                List.exists (fn allowed => allowed = name) pool) dependencies
        end
    | Knn count => select_knn pool count goal

fun reconstruct condition result goal =
  if not (#reconstruct condition) orelse
     #szs result <> hhProver.SzsTheorem then
    (NONE, NONE, NONE, NONE)
  else
    case #used_axioms result of
        NONE => (NONE, NONE, NONE, NONE)
      | SOME axioms =>
          ((let
              val ((stac, _), elapsed) =
                add_time (hhReconstruct.hh_reconstruct axioms) goal
            in
              (SOME true, SOME "metis", SOME elapsed, SOME stac)
            end)
           handle Interrupt => raise Interrupt
                | error =>
                    (SOME false, SOME "metis", NONE,
                     SOME (General.exnMessage error)))

fun run_cell expdir thy (name, thm) pool condition =
  let
    val goal = dest_thm thm
    val premises = selected_premises condition pool thm goal
    val named_premises = mlThmData.thml_of_namel premises
    val nfacts = length named_premises
    val directory = join (join (join expdir "pb") (safe_component thy))
      (safe_component (name ^ "-" ^ #cond_id condition))
    val _ = ensure_dir directory
    val _ = hhExportFof.fof_export_pb directory
      (list_mk_imp goal, named_premises)
  in
    case hhProver.lookup (#prover condition) of
        NONE =>
          let
            val entry = base_entry expdir thy name condition nfacts
              "RunFailure" 0.0 NONE NONE
            val entry =
              {run = #run entry, thy = #thy entry, thm = #thm entry,
               goal_id = #goal_id entry, cond = #cond entry,
               regime = #regime entry, selector = #selector entry,
               prover = #prover entry, prover_version = #prover_version entry,
               nfacts = #nfacts entry, timeout = #timeout entry,
               szs = #szs entry, t_prover = #t_prover entry,
               axioms_used = #axioms_used entry, recon_ok = #recon_ok entry,
               recon_method = #recon_method entry, t_recon = #t_recon entry,
               stac = #stac entry,
               error = SOME ("unknown HolyHammer prover: " ^ #prover condition)}
          in
            append_journal (journal_path expdir thy) entry
          end
      | SOME prover =>
          let
            val result = hhProver.run prover
              {timeout = #timeout condition,
               problem = join directory "atp_in", extra = [],
               debug_dir = SOME (join expdir "out")}
            val (recon_ok, recon_method, t_recon, stac_or_error) =
              reconstruct condition result goal
            val entry = base_entry expdir thy name condition nfacts
              (szs_name (#szs result)) (#time result) (#used_axioms result)
              (#version result)
            val (stac, recon_error) =
              case recon_ok of
                  SOME false => (NONE, stac_or_error)
                | _ => (stac_or_error, NONE)
            val entry =
              {run = #run entry, thy = #thy entry, thm = #thm entry,
               goal_id = #goal_id entry, cond = #cond entry,
               regime = #regime entry, selector = #selector entry,
               prover = #prover entry, prover_version = #prover_version entry,
               nfacts = #nfacts entry, timeout = #timeout entry,
               szs = #szs entry, t_prover = #t_prover entry,
               axioms_used = #axioms_used entry, recon_ok = recon_ok,
               recon_method = recon_method, t_recon = t_recon, stac = stac,
               error = case recon_error of
                           SOME message => SOME message
                         | NONE => run_failure_error (#szs result)}
          in
            append_journal (journal_path expdir thy) entry
          end
  end
  handle Interrupt => raise Interrupt
       | error =>
           let
             val entry = base_entry expdir thy name condition 0 "Error" 0.0
               NONE NONE
             val entry =
               {run = #run entry, thy = #thy entry, thm = #thm entry,
                goal_id = #goal_id entry, cond = #cond entry,
                regime = #regime entry, selector = #selector entry,
                prover = #prover entry, prover_version = #prover_version entry,
                nfacts = #nfacts entry, timeout = #timeout entry,
                szs = #szs entry, t_prover = #t_prover entry,
                axioms_used = #axioms_used entry, recon_ok = #recon_ok entry,
                recon_method = #recon_method entry, t_recon = #t_recon entry,
                stac = #stac entry, error = SOME (General.exnMessage error)}
           in
             append_journal (journal_path expdir thy) entry
           end

fun broken_deps_cell expdir thy name condition =
  let
    val entry = base_entry expdir thy name condition 0 "BrokenDeps" 0.0
      NONE NONE
  in
    append_journal (journal_path expdir thy) entry
  end

fun eval_loaded_theory expdir thy =
  let
    val completed = read_completed (journal_path expdir thy)
    val pools = chainy_pools thy
    fun evaluate (name, thm) =
      let
        val id = goal_id thy name
        val (dependencies_ok, intact_deps) =
          mlThmData.intactdep_of_thm thm
        val pool = lookup_pool name pools
        fun one condition =
          if cell_completed completed (id, #cond_id condition) then ()
          else if #regime condition = Bushy andalso not dependencies_ok then
            broken_deps_cell expdir thy name condition
          else
            run_cell expdir thy (name, thm)
              (case #regime condition of
                   Bushy => intact_deps
                 | Chainy => pool)
              condition
      in
        if sample_goal (!worker_sample) id then app one (!worker_conditions)
        else ()
      end
  in
    app evaluate (DB.theorems thy)
  end

fun eval_thy expdir thy =
  (eval_loaded_theory expdir thy
   handle Interrupt => raise Interrupt
        | error => journal_theory_error expdir thy (General.exnMessage error))

fun condition_text condition =
  "hhEval.parse_condition " ^ Portable.mlquote (encode_condition condition)

fun write_evalscript expdir thy conditions sample =
  let
    val scripts = join expdir "scripts"
    val _ = ensure_dir scripts
    val path = join scripts (safe_component thy ^ "_hheval.sml")
    val conditions_text = String.concatWith ", " (map condition_text conditions)
    val settings =
      "val _ = hhEval.set_worker_settings {conditions = [" ^
      conditions_text ^ "], sample = " ^ Int.toString sample ^ "};"
    val action = "val _ = hhEval.eval_thy " ^ Portable.mlquote expdir ^
      " " ^ Portable.mlquote thy ^ ";"
    val output = TextIO.openOut path
    val _ = TextIO.output (output,
      "load " ^ Portable.mlquote (thy ^ "Theory") ^ ";\n" ^
      "load \"hhEval\";\n" ^ settings ^ "\n" ^ action ^ "\n")
    val _ = TextIO.closeOut output
  in
    path
  end

fun configured_sample () =
  case hhConfig.get_int "eval.sample" of
      NONE => 1
    | SOME sample =>
        if sample < 1 then raise Fail "eval.sample must be a positive integer"
        else sample

fun theory_cells thy conditions sample =
  let
    val _ = load (thy ^ "Theory")
    fun cells (name, _) =
      let val id = goal_id thy name in
        if sample_goal sample id then map (fn condition =>
          (id, #cond_id condition)) conditions
        else []
      end
  in
    SOME (List.concat (map cells (DB.theorems thy)))
  end
  handle Interrupt => raise Interrupt | _ => NONE

fun file_exists path =
  OS.FileSys.access (path, [OS.FileSys.A_READ]) handle OS.SysErr _ => false

fun run_eval {expname, ncore, thyl, conditions} =
  if ncore < 1 then raise Fail "run_eval requires at least one worker"
  else
    let
      val sample = configured_sample ()
      val expdir = experiment_dir expname
      val _ = ensure_dir expdir
      val _ = ensure_dir (join expdir "journal")
      val _ = ensure_dir (join expdir "out")
      val _ = ensure_dir (join expdir "pb")
      val _ = ensure_dir (join expdir "scripts")
      fun corpus_entry thy =
        ((load (thy ^ "Theory"); loaded_corpus_entry thy)
         handle Interrupt => raise Interrupt
              | _ => {thy = thy, theorem_count = 0, dep_stamp = ""})
      val _ =
        if file_exists (join expdir "run.json") then ()
        else write_run_header expdir
          (new_run_header {expname = expname, corpus = map corpus_entry thyl,
            added_from_dat = [], conditions = conditions, sample = sample})
      val states = map (fn thy =>
        (thy, theory_cells thy conditions sample)) thyl
      fun pending (thy, NONE) =
            (journal_theory_error expdir thy
               "theory could not be loaded by the evaluation driver";
             false)
        | pending (thy, SOME cells) =
            not (journal_complete (journal_path expdir thy) cells)
      val queued_names = map #1 (List.filter pending states)
      val scripts = map (fn thy =>
        (thy, write_evalscript expdir thy conditions sample)) thyl
      val queued = List.filter (fn (thy, _) =>
        List.exists (fn name => name = thy) queued_names) scripts
      val _ = smlExecScripts.buildheap_dir := join expdir "out"
      val _ = smlParallel.parapp_queue ncore
        (fn (_, script) => smlExecScripts.exec_script script) queued
      fun note_unfinished (thy, NONE) = ()
        | note_unfinished (thy, SOME cells) =
            if journal_complete (journal_path expdir thy) cells then ()
            else journal_theory_error expdir thy
              "evaluation worker ended before completing its journal"
      val _ = app note_unfinished (List.filter pending states)
    in
      ()
    end

end
