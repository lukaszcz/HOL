(* Generate an immutable Phase 2-complete anchor manifest.

   Run this file only in a detached worktree at [behavior_source_commit],
   after loading the target theory and hhEval from that worktree.  Two older
   evidence layers remain separate: the gate journal supplies the accepted
   goal inventory and profile multiset, while the uncommitted Task13 audit
   supplies premise/command checks and internally paired keys.  Manifest
   cache keys come only from the reproducible Phase 2-complete source. *)

open HolKernel boolLib aiLib

val gate_run_source_commit =
  "f25871c404016d4368a0927ba0a868860fc82c70"

fun required_env name =
  case OS.Process.getEnv name of
      SOME value => value
    | NONE => raise Fail (name ^ " is not set")

val behavior_source_commit =
  required_env "HHEVAL_ANCHOR_BEHAVIOR_COMMIT"

fun optional_words name =
  case OS.Process.getEnv name of
      NONE => []
    | SOME value => String.tokens Char.isSpace value

fun optional_int name default =
  case OS.Process.getEnv name of
      NONE => default
    | SOME value =>
        (case Int.fromString value of
             SOME number => number
           | NONE => raise Fail (name ^ " is not an integer"))

fun trace text =
  case OS.Process.getEnv "HHEVAL_ANCHOR_TRACE" of
      SOME "1" => print ("HHEVAL_ANCHOR_TRACE=" ^ text ^ "\n")
    | _ => ()

val target_theory = required_env "HHEVAL_ANCHOR_THEORY"
val actual_source_commit = required_env "HHEVAL_ANCHOR_SOURCE_COMMIT"
val _ = if actual_source_commit = behavior_source_commit then () else
  raise Fail "anchor driver is not running at the Phase 2-complete commit"
val output_path = required_env "HHEVAL_ANCHOR_OUTPUT"
val journal_path = required_env "HHEVAL_ANCHOR_JOURNAL"
val legacy_rows_path = required_env "HHEVAL_ANCHOR_LEGACY_ROWS"
val command_rows_path = required_env "HHEVAL_ANCHOR_COMMAND_ROWS"
val accepted_run_header = required_env "HHEVAL_ANCHOR_ACCEPTED_RUN_HEADER"
val accepted_run_header_sha =
  required_env "HHEVAL_ANCHOR_ACCEPTED_RUN_HEADER_SHA256"
val accepted_journal = required_env "HHEVAL_ANCHOR_ACCEPTED_JOURNAL"
val accepted_journal_sha =
  required_env "HHEVAL_ANCHOR_ACCEPTED_JOURNAL_SHA256"
val input_run_header_sha =
  required_env "HHEVAL_ANCHOR_INPUT_RUN_HEADER_SHA256"
val input_journal = required_env "HHEVAL_ANCHOR_INPUT_JOURNAL"
val input_journal_sha =
  required_env "HHEVAL_ANCHOR_INPUT_JOURNAL_SHA256"
val paired_rows_sha = required_env "HHEVAL_ANCHOR_PAIRED_ROWS_SHA256"
val command_rows_sha = required_env "HHEVAL_ANCHOR_COMMAND_ROWS_SHA256"
val baseline_provenance_sha =
  required_env "HHEVAL_ANCHOR_BASELINE_PROVENANCE_SHA256"
val invocation_provenance_sha =
  required_env "HHEVAL_ANCHOR_INVOCATION_PROVENANCE_SHA256"
val success_marker = required_env "HHEVAL_ANCHOR_SUCCESS_MARKER"

fun write_success_marker () =
  let val output = TextIO.openOut success_marker in
    TextIO.output (output, "success\n");
    TextIO.closeOut output
  end

fun make_options slices cores : hhConfig.hh_options =
  let val base = hhConfig.snapshot () in
    {timeout = 30, max_proofs = 4,
     provers = ["e", "vampire", "zipperposition"],
     slices = slices, cores = cores, filter = "knn", max_facts = NONE,
     format = "", type_enc = "", lam_trans = "", mono_iters = 3,
     mono_instances = NONE, minimize = true, preplay_timeout = 1.0,
     minimize_timeout = 1.0, cache = false, cache_dir = #cache_dir base,
     cache_max_entries = 100000, debug_dir = NONE}
  end

fun pool_ids (theories, current) =
  map (fn (theory, name) => theory ^ "Theory." ^ name)
    (List.concat (map hhExportLib.thmidl_in_thy theories) @ current)

fun chainy_pools theory =
  let
    val order = hhExportLib.sorted_ancestry [theory]
    val earlier =
      if List.exists (fn name => name = theory) order then
        hhExportLib.before_elem theory order
      else order
    fun one (name, theorem) =
      let
        val older = List.filter (hhExportLib.older_than theorem)
          (DB.thms theory)
        val current = map (fn (other, _) => (theory, other)) older
      in
        (name, pool_ids (earlier, current))
      end
  in
    map one (DB.theorems theory)
  end

fun lookup_pool name pools =
  case List.find (fn (other, _) => other = name) pools of
      SOME (_, pool) => pool
    | NONE => []

val model_current_theory = Theory.current_theory ()
val model_ancestry = Theory.ancestry model_current_theory
val model_namespace_count = length (mlThmData.unsafe_namespace_thms ())
val _ = trace ("current-theory:" ^ model_current_theory)
val (knn_weights, knn_features) = mlThmData.create_thmdata ()

fun select_knn pool count goal =
  let
    val permitted = List.filter (fn (name, _) =>
      List.exists (fn allowed => allowed = name) pool) knn_features
  in
    mlNearestNeighbor.thmknn_wdep (knn_weights, permitted) count
      (mlFeature.fea_of_goal true goal)
  end

fun sha1_text text =
  let
    val bytes = Byte.stringToBytes text
    val size = Word8Vector.length bytes
    fun read (offset, wanted) =
      let
        val count = Int.min (wanted, size - offset)
        val chunk = Word8Vector.tabulate
          (count, fn index => Word8Vector.sub (bytes, offset + index))
      in
        (chunk, offset + count)
      end
  in
    SHA1.sha1String read 0
  end

fun frame text = Int.toString (String.size text) ^ ":" ^ text

fun take_up_to count items =
  if count <= 0 then []
  else
    case items of
        [] => []
      | item :: rest => item :: take_up_to (count - 1) rest

fun premise_digest count premises =
  sha1_text (String.concat (map frame (take_up_to count premises)))

fun sequence_digest values = sha1_text (String.concat (map frame values))

fun feature_text (name, symbols) =
  name ^ "\001" ^ String.concatWith "," (map Int.toString symbols)

fun weight_text (symbol, weight) =
  Int.toString symbol ^ "\001" ^ Real.toString weight

val native_model_inventory_sha1 = sequence_digest (map #1 knn_features)
val native_model_features_sha1 =
  sequence_digest (map feature_text knn_features)
val native_model_weights_sha1 = sequence_digest
  (map weight_text (Redblackmap.listItems knn_weights))

fun ranking_model_digest name fallback =
  case OS.Process.getEnv name of
      SOME value =>
        if String.size value = 40 andalso
           List.all (fn character => Char.isDigit character orelse
             (#"a" <= character andalso character <= #"f"))
             (String.explode value)
        then value
        else raise Fail ("invalid " ^ name)
    | NONE => fallback

val model_override_names =
  ["HHEVAL_ANCHOR_MODEL_INVENTORY_SHA1",
   "HHEVAL_ANCHOR_MODEL_FEATURES_SHA1",
   "HHEVAL_ANCHOR_MODEL_WEIGHTS_SHA1",
   "HHEVAL_ANCHOR_MODEL_FEATURE_ROWS"]
val model_override_values = map OS.Process.getEnv model_override_names
val _ =
  if List.all Option.isSome model_override_values orelse
     List.all (not o Option.isSome) model_override_values
  then ()
  else raise Fail "incomplete anchor ranking-model provenance"
val model_inventory_sha1 = ranking_model_digest
  "HHEVAL_ANCHOR_MODEL_INVENTORY_SHA1" native_model_inventory_sha1
val model_features_sha1 = ranking_model_digest
  "HHEVAL_ANCHOR_MODEL_FEATURES_SHA1" native_model_features_sha1
val model_weights_sha1 = ranking_model_digest
  "HHEVAL_ANCHOR_MODEL_WEIGHTS_SHA1" native_model_weights_sha1
val model_feature_rows = optional_int "HHEVAL_ANCHOR_MODEL_FEATURE_ROWS"
  (length knn_features)
val _ = if model_feature_rows > 0 then () else
  raise Fail "invalid anchor ranking-model feature count"

fun canonical_sequence tag values =
  frame tag ^ frame (Int.toString (length values)) ^
  String.concat (map frame values)

val anchor_goal_digest_schema = "hh-goal-struct-v1"

fun sorted_distinct_strings values =
  let
    fun distinct [] = []
      | distinct [value] = [value]
      | distinct (first :: (rest as second :: _)) =
          if first = second then distinct rest
          else first :: distinct rest
  in
    distinct (Listsort.sort String.compare values)
  end

fun canonical_type ty =
  if Type.is_vartype ty then
    canonical_sequence "type-variable" [Type.dest_vartype ty]
  else
    let
      val {Thy, Tyop, Args} = Type.dest_thy_type ty
    in
      canonical_sequence "type-operator"
        (Thy :: Tyop :: map canonical_type Args)
    end

fun canonical_term tm =
  let
    fun bound_index _ [] = NONE
      | bound_index variable (binder :: rest) =
          if Term.term_eq variable binder then SOME 0
          else
            case bound_index variable rest of
                SOME index => SOME (index + 1)
              | NONE => NONE
    fun encode bound current =
      if Term.is_var current then
        let
          val (name, ty) = Term.dest_var current
          val index = bound_index current bound
          val fields =
            case index of
                SOME position => [Int.toString position, canonical_type ty]
              | NONE => [name, canonical_type ty]
          val tag =
            if Option.isSome index then "bound-variable"
            else "free-variable"
        in
          canonical_sequence tag fields
        end
      else if Term.is_const current then
        let val {Thy, Name, Ty} = Term.dest_thy_const current in
          canonical_sequence "constant" [Thy, Name, canonical_type Ty]
        end
      else if Term.is_comb current then
        let val (operator, operand) = Term.dest_comb current in
          canonical_sequence "combination"
            [encode bound operator, encode bound operand]
        end
      else
        let val (binder, body) = Term.dest_abs current in
          canonical_sequence "abstraction"
            [canonical_type (Term.type_of binder),
             encode (binder :: bound) body]
        end
  in
    encode [] tm
  end

fun anchor_goal_sha1 (assumptions, conclusion) =
  sha1_text (canonical_sequence anchor_goal_digest_schema
    [canonical_sequence "assumption-set"
       (sorted_distinct_strings (map canonical_term assumptions)),
     canonical_sequence "conclusion" [canonical_term conclusion]])

fun goal_binding goal_id (assumptions, conclusion) pool premises = JSON.OBJECT
  [("goal_id", JSON.STRING goal_id),
   ("goal_sha1", JSON.STRING
     (anchor_goal_sha1 (assumptions, conclusion))),
   ("ancestry_sha1", JSON.STRING
     (sequence_digest (hhExportLib.sorted_ancestry [target_theory]))),
   ("fact_inventory_sha1", JSON.STRING (sequence_digest pool)),
   ("selected_premises_sha1", JSON.STRING
     (premise_digest (length premises) premises)),
   ("selected_premise_count", JSON.INT
     (IntInf.fromInt (length premises)))]

fun normalized_argument problem argument =
  if argument = problem then "<problem>"
  else
    let val prefix = "-file:" in
      if String.isPrefix prefix argument andalso
         String.extract (argument, String.size prefix, NONE) = problem
      then prefix ^ "<problem>"
      else argument
    end

fun json_strings values =
  JSONPrinter.valueToString (JSON.ARRAY (map JSON.STRING values))

fun indexed items =
  let
    fun loop _ [] = []
      | loop index (item :: rest) =
          (index, item) :: loop (index + 1) rest
  in
    loop 1 items
  end

fun version_of "e" = SOME "3.2.5-ho"
  | version_of "vampire" = SOME "5.0.1"
  | version_of "zipperposition" = SOME "2.1"
  | version_of name = raise Fail ("unknown Phase 2 prover " ^ name)

fun profile_equal (left : hhProver.slice, right : hhProver.slice) =
  #prover left = #prover right andalso #format left = #format right andalso
  #type_enc left = #type_enc right andalso
  #lam_trans left = #lam_trans right andalso
  #nfacts left = #nfacts right andalso #filter left = #filter right andalso
  #extra_opts left = #extra_opts right andalso
  #slice_size left = #slice_size right

fun profile_member profile profiles =
  List.exists (fn other => profile_equal (profile, other)) profiles

fun distinct_profiles [] = []
  | distinct_profiles (profile :: rest) =
      if profile_member profile rest then distinct_profiles rest
      else profile :: distinct_profiles rest

fun remove_profile profile [] = NONE
  | remove_profile profile (item :: rest) =
      if profile_equal (profile, item) then SOME rest
      else
        case remove_profile profile rest of
            NONE => NONE
          | SOME remaining => SOME (item :: remaining)

fun same_profile_multiset [] actual = null actual
  | same_profile_multiset (profile :: rest) actual =
      case remove_profile profile actual of
          NONE => false
        | SOME remaining => same_profile_multiset rest remaining

fun fields line =
  String.fields (fn character => character = #"\t") (hhConfig.trim line)

fun lines path =
  List.filter (fn line => hhConfig.trim line <> "") (bare_readl path)

fun app_lines path action =
  let
    val input = TextIO.openIn path
    fun close_and_raise error = (TextIO.closeIn input; raise error)
    fun loop line_number =
      case TextIO.inputLine input of
          NONE => TextIO.closeIn input
        | SOME line =>
            ((if hhConfig.trim line = "" then ()
              else action (line_number, line));
             loop (line_number + 1))
            handle error => close_and_raise error
  in
    loop 1
  end

fun parse_json text =
  let
    val source = JSONParser.openString text
    val value = JSONParser.parse source
    val _ = JSONParser.close source
  in
    value
  end

fun json_field name value = JSONUtil.lookupField value name
fun json_string name value = JSONUtil.asString (json_field name value)
fun json_int name value = JSONUtil.asInt (json_field name value)
fun json_strings_field name value =
  JSONUtil.arrayMap JSONUtil.asString (json_field name value)

fun journal_slice value : hhProver.slice =
  {prover = json_string "prover" value,
   format = json_string "format" value,
   type_enc = json_string "type_enc" value,
   lam_trans = json_string "lam_trans" value,
   nfacts = json_int "nfacts" value,
   filter = json_string "filter" value,
   extra_opts = json_strings_field "extra_opts" value,
   slice_size = json_int "slice_size" value}

type journal_entry =
  {thy : string, goal_id : string, slices : hhProver.slice list}

fun journal_entry line : journal_entry =
  let val value = parse_json line in
    {thy = json_string "thy" value, goal_id = json_string "goal_id" value,
     slices = JSONUtil.arrayMap
       (journal_slice o json_field "slice") (json_field "slices" value)}
  end

fun read_journal path = map journal_entry (lines path)

fun hex_digest size text =
  String.size text = size andalso List.all (fn character =>
    Char.isDigit character orelse
    (#"a" <= character andalso character <= #"f")) (String.explode text)

fun positive_int field text =
  case Int.fromString text of
      SOME value =>
        if value > 0 andalso Int.toString value = text then value
        else raise Fail ("invalid historical " ^ field ^ ": " ^ text)
    | NONE => raise Fail ("invalid historical " ^ field ^ ": " ^ text)

fun known_prover prover =
  List.exists (fn name => name = prover)
    ["e", "vampire", "zipperposition"]

fun valid_goal goal =
  goal <> "" andalso String.isSubstring "." goal

fun target_goal goal = String.isPrefix (target_theory ^ ".") goal

fun legacy_key goal index = goal ^ "\t" ^ Int.toString index

fun command_key goal prover filter nfacts format type_enc lam_trans extra =
  String.concatWith "\001"
    [goal, prover, filter, Int.toString nfacts, format, type_enc, lam_trans,
     json_strings extra]

fun insert_unique label dictionary key value =
  case Redblackmap.peek (!dictionary, key) of
      SOME _ => raise Fail ("duplicate historical " ^ label ^ ": " ^ key)
    | NONE => dictionary := Redblackmap.insert (!dictionary, key, value)

fun load_legacy_index path =
  let
    val dictionary = ref (Redblackmap.mkDict String.compare)
    fun one (line_number, line) =
      case fields line of
          [goal, index_text, prover, format, _, _, nfacts_text,
           premise, baseline_key, gate_key] =>
            let
              val index = positive_int "slice index" index_text
              val _ = if index <= 8 then () else raise Fail
                ("historical slice index exceeds eight at line " ^
                 Int.toString line_number)
              val _ = ignore (positive_int "nfacts" nfacts_text)
              val _ = if valid_goal goal andalso known_prover prover andalso
                  (format = "fof" orelse format = "tff") andalso
                  hex_digest 40 premise andalso
                  hex_digest 40 baseline_key andalso
                  hex_digest 40 gate_key andalso
                  baseline_key = gate_key
                then ()
                else raise Fail ("malformed historical premise row at line " ^
                  Int.toString line_number)
            in
              if target_goal goal then
                insert_unique "premise key" dictionary
                  (legacy_key goal index) (premise, baseline_key)
              else ()
            end
        | _ => raise Fail ("invalid historical premise schema at line " ^
            Int.toString line_number)
    val _ = app_lines path one
  in
    !dictionary
  end

fun load_command_index path =
  let
    val dictionary = ref (Redblackmap.mkDict String.compare)
    fun one (line_number, line) =
      case fields line of
          [goal, prover, filter, nfacts_text, format, type_enc, lam_trans,
           extra_text, command_text] =>
            let
              val nfacts = positive_int "nfacts" nfacts_text
              val extra = JSONUtil.arrayMap JSONUtil.asString
                (parse_json extra_text)
              val command = JSONUtil.arrayMap JSONUtil.asString
                (parse_json command_text)
              val _ =
                if valid_goal goal andalso known_prover prover andalso
                   filter = "knn" andalso
                   (format = "fof" orelse format = "tff") andalso
                   (case command of "anchor-prover" :: _ => true | _ => false)
                then ()
                else raise Fail ("malformed historical command row at line " ^
                  Int.toString line_number)
              val key = command_key goal prover filter nfacts format type_enc
                lam_trans extra
            in
              if target_goal goal then
                insert_unique "command profile" dictionary key command
              else ()
            end
        | _ => raise Fail ("invalid historical command schema at line " ^
            Int.toString line_number)
    val _ = app_lines path one
  in
    !dictionary
  end

val legacy_index = load_legacy_index legacy_rows_path
val command_index = load_command_index command_rows_path

fun lookup_legacy goal index =
  Redblackmap.peek (legacy_index, legacy_key goal index)

fun lookup_command goal (slice : hhProver.slice) =
  Redblackmap.peek (command_index,
    command_key goal (#prover slice) (#filter slice) (#nfacts slice)
      (#format slice) (#type_enc slice) (#lam_trans slice)
      (#extra_opts slice))

val historical_rows_checked = ref 0
val historical_premise_mismatches = ref 0
val historical_request_key_mismatches = ref 0

fun cross_certify goal index premise key command slice =
  if index > 8 then ()
  else
    let
      val legacy =
        case lookup_legacy goal index of
            SOME value => value
          | NONE => raise Fail ("missing historical premise row " ^ goal)
      val _ =
        case legacy of
            (old_premise, old_key) =>
              (historical_rows_checked := !historical_rows_checked + 1;
               if old_premise = premise then () else
                 raise Fail ("historical premise mismatch for " ^ goal);
               if old_key = key then () else
                 raise Fail ("historical request-key mismatch for " ^ goal ^
                   ": accepted=" ^ old_key ^ " derived=" ^ key))
      val old_command =
        case lookup_command goal slice of
            SOME value => value
          | NONE => raise Fail ("missing historical command row " ^ goal)
      val _ =
        if json_strings old_command = command then () else raise Fail
          ("historical normalized command mismatch for " ^ goal)
    in
      ()
    end

fun row_of goal premises timeout
    (index, (config : hhProver.prover_config, slice : hhProver.slice)) =
  let
    val problem = hhSchedule.problem_path slice
    val request : hhProver.run_request =
      {timeout = timeout, format = #format slice, problem = problem,
       extra = #extra_opts slice, debug_dir = NONE}
    val (_, raw_argv) = #mk_command config "anchor-prover"
      (#format request) request
    val command = json_strings
      ("anchor-prover" :: map (normalized_argument problem) raw_argv)
    val key = hhCache.key_of
      {prover = #name config, version = version_of (#name config),
       argv = raw_argv, problem = problem}
    val digest = premise_digest (#nfacts slice) premises
    val _ = cross_certify goal index digest key command slice
  in
    String.concatWith "\t"
      [goal, Int.toString index, #prover slice, #filter slice,
       #format slice, #type_enc slice, #lam_trans slice,
       Int.toString (#nfacts slice), Int.toString (#slice_size slice),
       json_strings (#extra_opts slice), digest, command, key]
  end

fun goal_set (entries : journal_entry list) =
  mk_string_set (map #goal_id entries)

fun requested_names () =
  case optional_words "HHEVAL_ANCHOR_THEOREMS" of
      [] => map #1 (DB.theorems target_theory)
    | names => names

fun header row_count goal_count execution_goal_count profile_start
    profile_length profile_sha bindings =
  JSONPrinter.valueToString (JSON.OBJECT
    [("schema", JSON.STRING "hh-anchor-manifest-v2"),
     ("behavior_source_commit", JSON.STRING behavior_source_commit),
     ("gate_run_source_commit", JSON.STRING gate_run_source_commit),
     ("task13_key_source", JSON.STRING
       "uncommitted-phase2-task13-artifact-state"),
     ("accepted_run_header", JSON.STRING accepted_run_header),
     ("accepted_run_header_sha256", JSON.STRING accepted_run_header_sha),
     ("accepted_journal", JSON.STRING accepted_journal),
     ("accepted_journal_sha256", JSON.STRING accepted_journal_sha),
     ("input_run_header_sha256", JSON.STRING input_run_header_sha),
     ("input_journal", JSON.STRING input_journal),
     ("input_journal_sha256", JSON.STRING input_journal_sha),
     ("task13_paired_rows_sha256", JSON.STRING paired_rows_sha),
     ("task13_command_rows_sha256", JSON.STRING command_rows_sha),
     ("baseline_provenance_sha256", JSON.STRING baseline_provenance_sha),
     ("invocation_provenance_sha256",
       JSON.STRING invocation_provenance_sha),
     ("task13_paired_driver_sha256", JSON.STRING
       "2fd0a344574906d38a59774f5e293fc673cb1fca28bcab07664dcb52779bf430"),
     ("task13_paired_controller_sha256", JSON.STRING
       "fb98abd78825ca7e4e15c64bfe6d7ffcc3cee34dca8c6e59fe78828552968141"),
     ("task13_rows_checked", JSON.INT
       (IntInf.fromInt (!historical_rows_checked))),
     ("task13_internal_key_pair_mismatches", JSON.INT 0),
     ("task13_premise_mismatches", JSON.INT
       (IntInf.fromInt (!historical_premise_mismatches))),
     ("task13_request_key_mismatches", JSON.INT
       (IntInf.fromInt (!historical_request_key_mismatches))),
     ("model_current_theory", JSON.STRING model_current_theory),
     ("model_ancestry", JSON.ARRAY (map JSON.STRING model_ancestry)),
     ("model_feature_rows", JSON.INT
       (IntInf.fromInt model_feature_rows)),
     ("model_inventory_sha1", JSON.STRING model_inventory_sha1),
     ("model_features_sha1", JSON.STRING model_features_sha1),
     ("model_weights_sha1", JSON.STRING model_weights_sha1),
     ("export_model_inventory_sha1",
       JSON.STRING native_model_inventory_sha1),
     ("export_model_features_sha1", JSON.STRING native_model_features_sha1),
     ("export_model_weights_sha1", JSON.STRING native_model_weights_sha1),
     ("export_model_feature_rows", JSON.INT
       (IntInf.fromInt (length knn_features))),
     ("model_namespace_count", JSON.INT
       (IntInf.fromInt model_namespace_count)),
     ("task13_execution_goals", JSON.INT
       (IntInf.fromInt execution_goal_count)),
     ("goals", JSON.INT (IntInf.fromInt goal_count)),
     ("profiles", JSON.INT 16),
     ("profile_start", JSON.INT (IntInf.fromInt profile_start)),
     ("profile_length", JSON.INT (IntInf.fromInt profile_length)),
     ("profile_set_sha1", JSON.STRING profile_sha),
     ("goal_digest_schema", JSON.STRING anchor_goal_digest_schema),
     ("goal_bindings", JSON.ARRAY bindings),
     ("row_count", JSON.INT (IntInf.fromInt row_count)),
     ("prover_spawns", JSON.INT 0)])

fun generate () =
  let
    val options = make_options 16 16
    val full_schedule = hhSlice.mk_schedule options
    val _ = if length full_schedule = 16 then ()
      else raise Fail "Phase 2 anchor schedule does not contain 16 slices"
    val profile_start = optional_int "HHEVAL_ANCHOR_PROFILE_START" 0
    val profile_length = optional_int "HHEVAL_ANCHOR_PROFILE_LENGTH" 16
    val _ =
      if profile_start >= 0 andalso profile_length > 0 andalso
         profile_start + profile_length <= 16
      then ()
      else raise Fail "invalid Phase 2 anchor profile batch"
    val indexed_schedule = List.drop (indexed full_schedule, profile_start)
    val selected = List.take (indexed_schedule, profile_length)
    val schedule = map #2 selected
    val profile_batches =
      if profile_start = 0 andalso profile_length = 16 then
        [List.take (selected, 8), List.drop (selected, 8)]
      else if profile_start = 0 andalso profile_length = 8 then [selected]
      else if profile_start >= 8 then [selected]
      else raise Fail
        "historical first-eight profiles must export as one frozen batch"
    fun profile_text (index, (_, slice : hhProver.slice)) =
      String.concatWith "\001"
        [Int.toString index, #prover slice, #filter slice, #format slice,
         #type_enc slice, #lam_trans slice, Int.toString (#nfacts slice),
         Int.toString (#slice_size slice), json_strings (#extra_opts slice)]
    val profile_sha = sequence_digest (map profile_text selected)
    val all_names = map #1 (DB.theorems target_theory)
    val names = requested_names ()
    val wanted_goals = mk_string_set
      (map (fn name => target_theory ^ "." ^ name) names)
    val all_journal = read_journal journal_path
    val all_journal_goals = goal_set all_journal
    val _ =
      if not (null all_journal) andalso
         List.all (fn entry => #thy entry = target_theory andalso
           length (#slices entry) = 16) all_journal andalso
         length all_journal = length all_journal_goals
      then ()
      else raise Fail "canonical journal member has invalid target inventory"
    fun complete_history (entry : journal_entry) =
      let
        val goal = #goal_id entry
        val legacy_ok = List.all (fn index =>
          Option.isSome (lookup_legacy goal index))
          (List.tabulate (8, fn index => index + 1))
      in
        legacy_ok
      end
    val command_rows = Redblackmap.listItems command_index
    fun command_count goal =
      length (List.filter (fn (key, _) =>
        String.isPrefix (goal ^ "\001") key) command_rows)
    val expected_history_rows = 8 * length all_journal
    val _ =
      if Redblackmap.numItems legacy_index = expected_history_rows andalso
         Redblackmap.numItems command_index = expected_history_rows andalso
         List.all complete_history all_journal andalso
         List.all (fn entry => command_count (#goal_id entry) = 8)
           all_journal
      then ()
      else raise Fail
        "historical target rows differ from canonical journal inventory"
    val journal = List.filter (fn entry =>
      #thy entry = target_theory andalso
      List.exists (fn goal => goal = #goal_id entry) wanted_goals)
      all_journal
    val journal_goals = goal_set journal
    val _ = if journal_goals = wanted_goals then ()
      else raise Fail "Phase 2 journal and requested goal inventories differ"
    val schedule_profiles = distinct_profiles (map #2 full_schedule)
    fun journal_profiles (entry : journal_entry) = #slices entry
    val _ =
      if length schedule_profiles = 16 andalso
         List.all (fn entry => same_profile_multiset
           (map #2 full_schedule) (journal_profiles entry)) journal
      then ()
      else raise Fail "Phase 2 journal profile multisets differ"
    val maximum = foldl Int.max 0 (map (#nfacts o #2) full_schedule)
    val pools = chainy_pools target_theory
    val premise_path = OS.Process.getEnv "HHEVAL_ANCHOR_PREMISES_PATH"
    val premise_directory =
      OS.Process.getEnv "HHEVAL_ANCHOR_PREMISES_DIRECTORY"
    val premise_read_only =
      OS.Process.getEnv "HHEVAL_ANCHOR_PREMISES_READ_ONLY" = SOME "1"
    val premise_provenance_sha =
      case OS.Process.getEnv "HHEVAL_ANCHOR_PREMISES_PROVENANCE_SHA256" of
          SOME value => value
        | NONE => baseline_provenance_sha
    val _ = if hex_digest 64 premise_provenance_sha then () else
      raise Fail "invalid premise producer provenance SHA-256"
    val _ =
      case (premise_path, premise_directory) of
          (NONE, _) => ()
        | (SOME _, NONE) =>
            if length names = 1 then ()
            else raise Fail "premise journal requires exactly one goal"
        | (SOME _, SOME _) =>
            raise Fail "premise path and directory are mutually exclusive"
    val _ =
      if premise_read_only andalso not (Option.isSome premise_path) andalso
         not (Option.isSome premise_directory)
      then raise Fail "read-only premises require a path or directory"
      else ()
    fun premise_file goal_id =
      case (premise_path, premise_directory) of
          (SOME path, NONE) => SOME path
        | (NONE, SOME directory) =>
            SOME (OS.Path.concat (directory, sha1_text goal_id ^ ".premises"))
        | (NONE, NONE) => NONE
        | (SOME _, SOME _) => raise Fail "unreachable premise configuration"
    fun premise_header goal_id goal pool values =
      "#hh-anchor-premises-v2\t" ^ JSONPrinter.valueToString (JSON.OBJECT
        [("schema", JSON.STRING "hh-anchor-premises-v2"),
         ("invocation_provenance_sha256",
           JSON.STRING invocation_provenance_sha),
         ("producer_provenance_sha256",
           JSON.STRING premise_provenance_sha),
         ("canonical_journal_member_sha256",
           JSON.STRING input_journal_sha),
         ("model_inventory_sha1", JSON.STRING model_inventory_sha1),
         ("model_features_sha1", JSON.STRING model_features_sha1),
         ("model_weights_sha1", JSON.STRING model_weights_sha1),
         ("model_feature_rows", JSON.INT
           (IntInf.fromInt model_feature_rows)),
         ("maximum", JSON.INT (IntInf.fromInt maximum)),
         ("count", JSON.INT (IntInf.fromInt (length values))),
         ("goal", goal_binding goal_id goal pool values)])
    fun read_premises path goal_id goal pool =
      let
        val input = TextIO.openIn path
        fun line () =
          case TextIO.inputLine input of
              NONE => NONE
            | SOME text =>
                SOME (if String.isSuffix "\n" text then
                        String.substring (text, 0, String.size text - 1)
                      else text)
        val header =
          case line () of
              SOME text => text
            | NONE => raise Fail "empty anchor premise journal"
        fun loop values =
          case line () of
              NONE => List.rev values
            | SOME value => loop (value :: values)
        val values = loop []
        val _ = TextIO.closeIn input
        val expected = premise_header goal_id goal pool values
        val _ =
          if header = expected andalso length values <= maximum andalso
             length values = length (mk_string_set values)
          then ()
          else raise Fail "invalid anchor premise journal"
      in
        values
      end
    fun write_premises path goal_id goal pool values =
      let
        val _ = if premise_read_only then
          raise Fail "missing read-only anchor premise journal" else ()
        val partial = path ^ ".partial"
        val output = TextIO.openOut partial
        val header = premise_header goal_id goal pool values
        val _ = TextIO.output (output, header ^ "\n")
        val _ = List.app
          (fn value => TextIO.output (output, value ^ "\n")) values
        val _ = TextIO.closeOut output
        val _ = OS.FileSys.rename {old = partial, new = path}
      in
        values
      end
    fun premises_for name goal =
      let
        val goal_id = target_theory ^ "." ^ name
        val pool = lookup_pool name pools
      in
        case (premise_file goal_id,
              List.exists (fn requested => requested = name) names) of
            (SOME path, true) =>
              if OS.FileSys.access (path, []) then
                read_premises path goal_id goal pool
              else
                write_premises path goal_id goal pool
                  (select_knn pool maximum goal)
          | _ => select_knn pool maximum goal
      end
    val chunks = ref ([] : string list list)
    val bindings = ref ([] : JSON.value list)
    fun one name =
      let
        val _ = trace ("select:" ^ name)
        val theorem = DB.fetch target_theory name
        val goal = dest_thm theorem
        val pool = lookup_pool name pools
        val premises = premises_for name goal
        val goal_id = target_theory ^ "." ^ name
        val wanted = List.exists (fn requested => requested = name) names
        val _ = if wanted then
          bindings := goal_binding goal_id goal pool premises :: !bindings
          else ()
        val _ = trace ("export:" ^ name)
        val _ = trace ("state:" ^ hhConfig.state_dir ())
        val _ = trace ("problem:" ^ hhSchedule.problem_path (#2 (hd schedule)))
        fun batch_rows batch =
          let
            val batch_schedule = map #2 batch
            val _ = hhSchedule.export_problems options goal premises
              batch_schedule
          in
            map (row_of goal_id premises 30) batch
          end
        val _ = trace ("rows:" ^ name)
        val rows = List.concat (map batch_rows profile_batches)
      in
        if wanted then chunks := rows :: !chunks else ()
      end
    val _ = hhProver.reset_spawn_count ()
    (* Legacy FOF translation has a deliberate process-global memo.  Task13
       traversed every theorem in DB creation order, so a requested subset
       must replay the complete prefix/state sequence rather than starting
       at the requested theorem.  Typed-only batches do not cross-certify
       Task13 and may retain the bounded single-goal resume path. *)
    val execution_names = if profile_start < 8 then all_names else names
    val _ = List.app one execution_names
    val spawns = hhProver.spawn_count ()
    val _ = if spawns = 0 then ()
      else raise Fail "Phase 2 manifest generation spawned a prover"
    val rows = List.concat (List.rev (!chunks))
    val _ = if length rows = profile_length * length names then ()
      else raise Fail "Phase 2 manifest row count differs from profile batch"
    val output = TextIO.openOut output_path
    val _ = TextIO.output (output,
      "#hh-anchor-manifest-v2\t" ^
      header (length rows) (length names) (length execution_names)
        profile_start profile_length profile_sha (List.rev (!bindings)) ^
      "\n")
    val _ = List.app (fn row => TextIO.output (output, row ^ "\n")) rows
    val _ = TextIO.closeOut output
  in
    print ("HHEVAL_PHASE2_ANCHOR_ROWS=" ^
      Int.toString (profile_length * length names) ^
      "\nHHEVAL_ANCHOR_PROVER_SPAWNS=0\n")
  end

val status =
  (generate (); write_success_marker (); OS.Process.success)
  handle Interrupt => raise Interrupt
       | error =>
           (TextIO.output (TextIO.stdErr,
              "anchor manifest worker failed: " ^
              General.exnMessage error ^ "\n");
            OS.Process.failure)

val _ = OS.Process.exit status
