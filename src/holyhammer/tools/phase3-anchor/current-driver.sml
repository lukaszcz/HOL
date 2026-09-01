fun required_env name =
  case OS.Process.getEnv name of
      SOME value => value
    | NONE => raise Fail (name ^ " is not set");

fun hheval_run_current () =
let
val theory = required_env "HHEVAL_THEORY";
val theory_dir = required_env "HHEVAL_THEORY_DIR";
val baseline = required_env "HHEVAL_ANCHOR_BASELINE";
val output = required_env "HHEVAL_ANCHOR_OUTPUT";
val mismatches = required_env "HHEVAL_ANCHOR_MISMATCHES";
val scratch = required_env "HHEVAL_ANCHOR_SCRATCH";
val invocation_sha =
  required_env "HHEVAL_CURRENT_INVOCATION_PROVENANCE_SHA256";
val baseline_sha = required_env "HHEVAL_CURRENT_BASELINE_SHA256";
val run_header_sha = required_env "HHEVAL_CURRENT_RUN_HEADER_SHA256";
val canonical_member_sha =
  required_env "HHEVAL_CURRENT_CANONICAL_MEMBER_SHA256";
val producer_sources_sha =
  required_env "HHEVAL_CURRENT_PRODUCER_SOURCES_SHA256";
val producer_objects_sha =
  required_env "HHEVAL_CURRENT_PRODUCER_OBJECTS_SHA256";
val rankings_directory = required_env "HHEVAL_CURRENT_RANKINGS_DIRECTORY";
val progress_path = required_env "HHEVAL_CURRENT_PROGRESS_PATH";
val goal_range_start =
  valOf (Int.fromString (required_env "HHEVAL_CURRENT_GOAL_RANGE_START"));
val goal_range_length =
  valOf (Int.fromString (required_env "HHEVAL_CURRENT_GOAL_RANGE_LENGTH"));
val goal_chunk_policy_version =
  required_env "HHEVAL_CURRENT_GOAL_CHUNK_POLICY_VERSION";
val profile_start =
  valOf (Int.fromString (required_env "HHEVAL_ANCHOR_PROFILE_START"));
val profile_length =
  valOf (Int.fromString (required_env "HHEVAL_ANCHOR_PROFILE_LENGTH"));
val replay_theory =
  required_env "HHEVAL_ANCHOR_REPLAY_THEORY" = "1";
val checkpoint_mode =
  OS.Process.getEnv "HHEVAL_CURRENT_CHECKPOINT_MODE" = SOME "atom";
val checkpoint_soft_seconds =
  case OS.Process.getEnv "HHEVAL_CURRENT_CHECKPOINT_SOFT_SECONDS" of
      SOME text => valOf (Int.fromString text)
    | NONE => 420;
val _ = OS.FileSys.chDir theory_dir;
val _ = if checkpoint_mode then () else load (theory ^ "Theory");
val _ = if checkpoint_mode then () else load "hhEval";
val _ = aiLib.scratch_dir := scratch;
val _ = print ("HHEVAL_CURRENT_THEORY=" ^ Theory.current_theory () ^ "\n");
(* The controller captures the legacy ambient model after loading the certified
   target and before creating the synthetic replay theory.  Keeping that
   boundary explicit prevents replay-only theory state from changing ranking. *)
val legacy_model_probe = hheval_legacy_model_probe;
val target_model_probe = hheval_target_model_probe;
val legacy_model_binding = hhEval.anchor_model_binding legacy_model_probe;
val model_environment =
  ["HHEVAL_CURRENT_MODEL_INVENTORY_SHA1",
   "HHEVAL_CURRENT_MODEL_FEATURES_SHA1",
   "HHEVAL_CURRENT_MODEL_WEIGHTS_SHA1",
   "HHEVAL_CURRENT_MODEL_FEATURE_ROWS",
   "HHEVAL_CURRENT_MODEL_CURRENT_THEORY",
   "HHEVAL_CURRENT_MODEL_ANCESTRY",
   "HHEVAL_CURRENT_MODEL_NAMESPACE_COUNT",
   "HHEVAL_CURRENT_TARGET_MODEL_FEATURES_SHA1"];
val _ =
  if profile_start <> 0 then ()
  else List.app (fn name =>
    case OS.Process.getEnv name of
        NONE => ()
      | SOME _ => raise Fail
          "current first8 rejects a supplied model binding")
    model_environment;
fun expected_model_binding () : hhEval.anchor_model_binding =
  {inventory_sha1 =
     required_env "HHEVAL_CURRENT_MODEL_INVENTORY_SHA1",
   features_sha1 =
     required_env "HHEVAL_CURRENT_MODEL_FEATURES_SHA1",
   weights_sha1 =
     required_env "HHEVAL_CURRENT_MODEL_WEIGHTS_SHA1",
   feature_rows = valOf (Int.fromString
     (required_env "HHEVAL_CURRENT_MODEL_FEATURE_ROWS"))};
val ranking_model_binding =
  if profile_start = 0 then legacy_model_binding
  else expected_model_binding ();
val ranking_model_current_theory =
  if profile_start = 0 then hheval_legacy_model_current_theory
  else required_env "HHEVAL_CURRENT_MODEL_CURRENT_THEORY";
val ranking_model_ancestry =
  if profile_start = 0 then hheval_legacy_model_ancestry
  else String.tokens (fn character => character = #",")
    (required_env "HHEVAL_CURRENT_MODEL_ANCESTRY");
val ranking_model_namespace_count =
  if profile_start = 0 then hheval_legacy_model_namespace_count
  else valOf (Int.fromString
    (required_env "HHEVAL_CURRENT_MODEL_NAMESPACE_COUNT"));
fun sha1_text text =
  let
    val bytes = Byte.stringToBytes text;
    val size = Word8Vector.length bytes;
    fun read (offset, wanted) =
      let
        val count = Int.min (wanted, size - offset);
        val chunk = Word8Vector.tabulate
          (count, fn index => Word8Vector.sub (bytes, offset + index));
      in
        (chunk, offset + count)
      end;
  in
    SHA1.sha1String read 0
  end;
fun frame text = Int.toString (String.size text) ^ ":" ^ text;
fun sequence_digest values = sha1_text (String.concat (map frame values));
fun feature_text (name, features) =
  name ^ "\001" ^ String.concatWith "," (map Int.toString features);
val target_model_digest = sequence_digest
  (map feature_text (#2 target_model_probe));
val ranking_target_model_digest =
  if profile_start = 0 then target_model_digest
  else required_env "HHEVAL_CURRENT_TARGET_MODEL_FEATURES_SHA1";
fun lower_hex character =
  Char.isDigit character orelse
  (#"a" <= character andalso character <= #"f");
fun valid_sha1 digest =
  String.size digest = 40 andalso List.all lower_hex (String.explode digest);
val _ =
  if ranking_model_current_theory <> "" andalso
     not (null ranking_model_ancestry) andalso
     ranking_model_namespace_count >= 0 andalso
     valid_sha1 ranking_target_model_digest
  then ()
  else raise Fail "invalid carried current ranking-model provenance";
val _ = print ("HHEVAL_CURRENT_ANCESTRY=" ^
  String.concatWith "," (Theory.ancestry theory @ [theory]) ^
  "\nHHEVAL_CURRENT_LEGACY_FEATURE_ROWS=" ^
  Int.toString (length (#2 legacy_model_probe)) ^
  "\nHHEVAL_CURRENT_TARGET_FEATURE_ROWS=" ^
  Int.toString (length (#2 target_model_probe)) ^
  "\nHHEVAL_CURRENT_NAMESPACE_COUNT=" ^
  Int.toString (length (mlThmData.unsafe_namespace_thms ())) ^ "\n");

fun read_lines path =
  let
    val input = TextIO.openIn path;
    fun loop result =
      case TextIO.inputLine input of
          NONE => (TextIO.closeIn input; List.rev result)
        | SOME line =>
            loop ((if String.isSuffix "\n" line then
                     String.substring (line, 0, String.size line - 1)
                   else line) :: result);
  in
    loop []
  end;
fun parse_json text =
  let
    val source = JSONParser.openString text;
    val value = JSONParser.parse source;
    val _ = JSONParser.close source;
  in
    value
  end;
fun json_field name value = JSONUtil.lookupField value name;
fun json_string name value = JSONUtil.asString (json_field name value);
fun json_int name value = JSONUtil.asInt (json_field name value);
fun ranking_path goal_id = OS.Path.concat
  (rankings_directory, sha1_text goal_id ^ ".ranking");
fun ranking_header (ranking : hhEval.anchor_ranking) =
  JSONPrinter.valueToString (JSON.OBJECT
    [("schema", JSON.STRING "hh-anchor-current-ranking-v1"),
     ("producer_role", JSON.STRING "current"),
     ("goal_digest_schema", JSON.STRING hhEval.anchor_goal_digest_schema),
     ("invocation_provenance_sha256", JSON.STRING invocation_sha),
     ("run_header_sha256", JSON.STRING run_header_sha),
     ("canonical_journal_member_sha256",
       JSON.STRING canonical_member_sha),
     ("producer_sources_sha256", JSON.STRING producer_sources_sha),
     ("producer_objects_sha256", JSON.STRING producer_objects_sha),
     ("model_inventory_sha1",
       JSON.STRING (#inventory_sha1 ranking_model_binding)),
     ("model_features_sha1",
       JSON.STRING (#features_sha1 ranking_model_binding)),
     ("model_weights_sha1",
       JSON.STRING (#weights_sha1 ranking_model_binding)),
     ("model_feature_rows", JSON.INT
       (IntInf.fromInt (#feature_rows ranking_model_binding))),
     ("goal_id", JSON.STRING (#goal_id ranking)),
     ("goal_sha1", JSON.STRING (#goal_sha1 ranking)),
     ("ancestry_sha1", JSON.STRING (#ancestry_sha1 ranking)),
     ("pool_inventory_sha1",
       JSON.STRING (#fact_inventory_sha1 ranking)),
     ("pool_count", JSON.INT (IntInf.fromInt (#pool_count ranking))),
     ("maximum", JSON.INT (IntInf.fromInt (#maximum ranking))),
     ("selected_premises_sha1",
       JSON.STRING (#selected_premises_sha1 ranking)),
     ("selected_premise_count", JSON.INT
       (IntInf.fromInt (length (#selected_premises ranking))))]);
fun ranking_lines ranking =
  ("#hh-anchor-current-ranking-v1\t" ^ ranking_header ranking) ::
  #selected_premises ranking;
fun write_ranking ranking =
  let
    val path = ranking_path (#goal_id ranking);
    val lines = ranking_lines ranking;
  in
    if OS.FileSys.access (path, []) then
      if read_lines path = lines then ()
      else raise Fail "existing current ranking journal is stale"
    else
      let
        val partial = path ^ ".partial";
        val output = TextIO.openOut partial;
        val _ = List.app (fn line =>
          TextIO.output (output, line ^ "\n")) lines;
        val _ = TextIO.closeOut output;
      in
        OS.FileSys.rename {old = partial, new = path}
      end
  end;
fun read_ranking goal_id : hhEval.anchor_ranking =
  let
    val lines = read_lines (ranking_path goal_id);
    val (first, premises) =
      case lines of [] => raise Fail "empty current ranking journal"
        | first :: rest => (first, rest);
    val prefix = "#hh-anchor-current-ranking-v1\t";
    val _ = if String.isPrefix prefix first then () else
      raise Fail "cross-fed or malformed current ranking journal";
    val value = parse_json
      (String.extract (first, String.size prefix, NONE));
    val _ =
      if json_string "schema" value = "hh-anchor-current-ranking-v1" andalso
         json_string "producer_role" value = "current" andalso
         json_string "goal_digest_schema" value =
           hhEval.anchor_goal_digest_schema andalso
         json_string "invocation_provenance_sha256" value =
           invocation_sha andalso
         json_string "run_header_sha256" value = run_header_sha andalso
         json_string "canonical_journal_member_sha256" value =
           canonical_member_sha andalso
         json_string "producer_sources_sha256" value =
           producer_sources_sha andalso
         json_string "producer_objects_sha256" value =
           producer_objects_sha andalso
         json_string "model_inventory_sha1" value =
           #inventory_sha1 ranking_model_binding andalso
         json_string "model_features_sha1" value =
           #features_sha1 ranking_model_binding andalso
         json_string "model_weights_sha1" value =
           #weights_sha1 ranking_model_binding andalso
         json_int "model_feature_rows" value =
           #feature_rows ranking_model_binding andalso
         json_string "goal_id" value = goal_id andalso
         json_int "selected_premise_count" value = length premises
      then ()
      else raise Fail "current ranking journal provenance is stale";
  in
    {goal_id = goal_id, goal_sha1 = json_string "goal_sha1" value,
     ancestry_sha1 = json_string "ancestry_sha1" value,
     fact_inventory_sha1 = json_string "pool_inventory_sha1" value,
     pool_count = json_int "pool_count" value,
     selected_premises_sha1 =
       json_string "selected_premises_sha1" value,
     selected_premises = premises, maximum = json_int "maximum" value}
  end;

fun manifest_theorem_names path =
  let
    val prefix = theory ^ ".";
    val input = TextIO.openIn path;
    fun lines result =
      case TextIO.inputLine input of
          NONE => (TextIO.closeIn input; List.rev result)
        | SOME line => lines (line :: result);
    fun name_of line =
      case String.fields (fn character => character = #"\t") line of
          goal :: _ =>
            if String.isPrefix prefix goal then
              SOME (String.extract (goal, String.size prefix, NONE))
            else NONE
        | [] => NONE;
    fun add (name, names) =
      if List.exists (fn old => old = name) names then names
      else names @ [name];
  in
    foldl add [] (List.mapPartial name_of (lines []))
  end;

val requested_theorem_names =
  case OS.Process.getEnv "HHEVAL_ANCHOR_THEOREMS" of
      SOME words => String.tokens Char.isSpace words
    | NONE => manifest_theorem_names baseline;

val manifest = hhEval.read_anchor_manifest baseline;
fun in_profile index =
  profile_start < index andalso index <= profile_start + profile_length;
fun write_marker path value =
  let
    val stream = TextIO.openOut path;
    val _ = TextIO.output
      (stream, JSONPrinter.valueToString value ^ "\n");
  in
    TextIO.closeOut stream
  end;
val _ =
  if goal_range_start >= 0 andalso
     goal_range_length = length requested_theorem_names andalso
     (goal_chunk_policy_version = "hh-current-goal-bisect-v1" orelse
      goal_chunk_policy_version = hheval_checkpoint_policy)
  then ()
  else raise Fail "invalid current goal-range binding";
val _ = write_marker progress_path (JSON.OBJECT
  [("schema", JSON.STRING "hh-current-computation-progress-v1"),
   ("theory", JSON.STRING theory),
   ("profile_start", JSON.INT (IntInf.fromInt profile_start)),
   ("profile_length", JSON.INT (IntInf.fromInt profile_length)),
   ("goal_range_start", JSON.INT (IntInf.fromInt goal_range_start)),
   ("goal_range_length", JSON.INT (IntInf.fromInt goal_range_length)),
   ("goal_chunk_policy_version", JSON.STRING goal_chunk_policy_version),
   ("invocation_provenance_sha256", JSON.STRING invocation_sha),
   ("run_header_sha256", JSON.STRING run_header_sha),
   ("baseline_manifest_sha256", JSON.STRING baseline_sha),
   ("canonical_journal_member_sha256",
     JSON.STRING canonical_member_sha),
   ("model_inventory_sha1",
     JSON.STRING (#inventory_sha1 ranking_model_binding)),
   ("model_features_sha1",
     JSON.STRING (#features_sha1 ranking_model_binding)),
   ("model_weights_sha1",
     JSON.STRING (#weights_sha1 ranking_model_binding))]);
val prover_versions =
  [("e", SOME "3.2.5-ho"), ("vampire", SOME "5.0.1"),
   ("zipperposition", SOME "2.1")];
fun derive names =
  if profile_start = 0 then
    hhEval.derive_anchor_rows_part_with_model
      {thy = theory, theorem_names = names, timeout = 30,
       prover_versions = prover_versions, profile_start = profile_start,
       profile_length = profile_length, replay_theory = replay_theory,
       model_thmdata = legacy_model_probe,
       model_binding = legacy_model_binding}
  else
    hhEval.derive_anchor_rows_part_with_rankings
      {thy = theory, theorem_names = names, timeout = 30,
       prover_versions = prover_versions, profile_start = profile_start,
       profile_length = profile_length,
       rankings = map (fn name => read_ranking (theory ^ "." ^ name))
         names,
       model_binding = ranking_model_binding};
fun same_strings ([], []) = true
  | same_strings (left :: lefts, right :: rights) =
      left = right andalso same_strings (lefts, rights)
  | same_strings _ = false;
fun db_range start count =
  List.take (List.drop (hheval_checkpoint_db_order, start), count);
val _ =
  if not checkpoint_mode then ()
  else if profile_start = 0 andalso not replay_theory andalso
          hheval_checkpoint_schema = "hh-current-db-checkpoint-chain-v1" andalso
          hheval_checkpoint_policy = goal_chunk_policy_version andalso
          hheval_checkpoint_theory = theory andalso
          !hheval_checkpoint_index = goal_range_start andalso
          same_strings (requested_theorem_names,
            db_range goal_range_start goal_range_length)
  then ()
  else raise Fail "current checkpoint atom has stale or non-DB-order state";
val checkpoint_start_time = Time.now ();
fun checkpoint_elapsed () =
  Time.toReal (Time.- (Time.now (), checkpoint_start_time));
fun write_checkpoint_stage text =
  if checkpoint_mode then
    let
      val stream = TextIO.openOut
        (required_env "HHEVAL_CURRENT_CHECKPOINT_STAGE_PATH")
    in
      TextIO.output (stream, text ^ "\n");
      TextIO.closeOut stream
    end
  else ();
val _ = write_checkpoint_stage "deriving";
fun combine_derivations (derivations : hhEval.anchor_derivation list) :
    hhEval.anchor_derivation =
  {current = List.concat (map #current derivations),
   goal_bindings = List.concat (map #goal_bindings derivations),
   rankings = List.concat (map #rankings derivations),
   model_binding = ranking_model_binding,
   prover_spawns = foldl (fn (item, total) =>
     #prover_spawns item + total) 0 derivations};
fun checkpoint_loop ([], completed, results) =
      (List.rev completed, List.rev results)
  | checkpoint_loop (name :: names, completed, results) =
      let
        val result = derive [name]
        val _ = hheval_checkpoint_index := !hheval_checkpoint_index + 1
        val completed' = name :: completed
        val results' = result :: results
      in
        if checkpoint_elapsed () >= Real.fromInt checkpoint_soft_seconds
        then (List.rev completed', List.rev results')
        else checkpoint_loop (names, completed', results')
      end;
val (theorem_names, derivation) =
  if checkpoint_mode then
    let
      val (completed, results) =
        checkpoint_loop (requested_theorem_names, [], [])
    in
      (completed, combine_derivations results)
    end
  else (requested_theorem_names, derive requested_theorem_names);
val requested_goals = map (fn name => theory ^ "." ^ name) theorem_names;
fun requested goal = List.exists (fn wanted => wanted = goal) requested_goals;
val expected = List.filter (fn row =>
  requested (#goal_id row) andalso in_profile (#slice_index row))
  (#rows manifest);
val _ = if profile_start = 0 then
  List.app write_ranking (#rankings derivation) else ();
val differences = hhEval.compare_anchor_rows expected (#current derivation);

fun same_binding ((left : hhEval.anchor_goal_binding),
    (right : hhEval.anchor_goal_binding)) =
  #goal_id left = #goal_id right andalso
  #goal_sha1 left = #goal_sha1 right andalso
  #ancestry_sha1 left = #ancestry_sha1 right andalso
  #fact_inventory_sha1 left = #fact_inventory_sha1 right andalso
  #selected_premises_sha1 left = #selected_premises_sha1 right andalso
  #selected_premise_count left = #selected_premise_count right;
fun expected_binding goal = List.find (fn binding =>
  #goal_id binding = goal) (#goal_bindings (#header manifest));
val binding_mismatches = List.filter (fn binding =>
  case expected_binding (#goal_id binding) of
      SOME old => not (same_binding (old, binding))
    | NONE => true) (#goal_bindings derivation);

fun binding_json (binding : hhEval.anchor_goal_binding) = JSON.OBJECT
  [("goal_id", JSON.STRING (#goal_id binding)),
   ("goal_sha1", JSON.STRING (#goal_sha1 binding)),
   ("ancestry_sha1", JSON.STRING (#ancestry_sha1 binding)),
   ("fact_inventory_sha1",
     JSON.STRING (#fact_inventory_sha1 binding)),
   ("selected_premises_sha1",
     JSON.STRING (#selected_premises_sha1 binding)),
   ("selected_premise_count",
     JSON.INT (IntInf.fromInt (#selected_premise_count binding)))];
fun profile_text (row : hhEval.anchor_row) = String.concatWith "\001"
  [Int.toString (#slice_index row), #prover row, #filter row, #format row,
   #type_enc row, #lam_trans row, Int.toString (#nfacts row),
   Int.toString (#slice_size row),
   JSONPrinter.valueToString
     (JSON.ARRAY (map JSON.STRING (#extra_opts row)))];
fun first_goal_profiles [] = []
  | first_goal_profiles ((first : hhEval.anchor_row) :: rows) =
      first :: List.filter (fn (row : hhEval.anchor_row) =>
        #goal_id row = #goal_id first) rows;
val profile_set_sha1 = sequence_digest
  (map profile_text (first_goal_profiles (#current derivation)));
val row_set_sha1 = sequence_digest
  (map hhEval.encode_anchor_row (#current derivation));

fun write_lines path lines =
  let
    val stream = TextIO.openOut path;
    val _ = List.app (fn line => TextIO.output (stream, line ^ "\n")) lines;
  in
    TextIO.closeOut stream
  end;

fun mismatch_json (row : hhEval.anchor_mismatch) =
  JSONPrinter.valueToString (JSON.OBJECT
    [("goal_id", JSON.STRING (#goal_id row)),
     ("slice", JSON.INT (IntInf.fromInt (#slice_index row))),
     ("field", JSON.STRING (#field row)),
     ("expected", JSON.STRING (#expected row)),
     ("actual", JSON.STRING (#actual row))]);

val header = JSONPrinter.valueToString (JSON.OBJECT
  [("schema", JSON.STRING "hh-anchor-current-v1"),
   ("goal_digest_schema", JSON.STRING hhEval.anchor_goal_digest_schema),
   ("invocation_provenance_sha256", JSON.STRING invocation_sha),
   ("baseline_manifest_sha256", JSON.STRING baseline_sha),
   ("theory", JSON.STRING theory),
   ("goals", JSON.INT (IntInf.fromInt (length theorem_names))),
   ("profile_start", JSON.INT (IntInf.fromInt profile_start)),
   ("profile_length", JSON.INT (IntInf.fromInt profile_length)),
   ("goal_range_start", JSON.INT (IntInf.fromInt goal_range_start)),
   ("goal_range_length", JSON.INT (IntInf.fromInt goal_range_length)),
   ("completed_goal_range_start",
     JSON.INT (IntInf.fromInt goal_range_start)),
   ("completed_goal_range_length",
     JSON.INT (IntInf.fromInt (length theorem_names))),
   ("goal_chunk_policy_version", JSON.STRING goal_chunk_policy_version),
   ("replay_theory", JSON.BOOL replay_theory),
   ("model_current_theory", JSON.STRING ranking_model_current_theory),
   ("model_ancestry", JSON.ARRAY
      (map JSON.STRING ranking_model_ancestry)),
   ("model_feature_rows",
     JSON.INT (IntInf.fromInt (#feature_rows ranking_model_binding))),
   ("model_inventory_sha1",
     JSON.STRING (#inventory_sha1 ranking_model_binding)),
   ("model_features_sha1",
     JSON.STRING (#features_sha1 ranking_model_binding)),
   ("model_weights_sha1",
     JSON.STRING (#weights_sha1 ranking_model_binding)),
   ("export_model_feature_rows",
     JSON.INT (IntInf.fromInt (#feature_rows legacy_model_binding))),
   ("export_model_inventory_sha1",
     JSON.STRING (#inventory_sha1 legacy_model_binding)),
   ("export_model_features_sha1",
     JSON.STRING (#features_sha1 legacy_model_binding)),
   ("export_model_weights_sha1",
     JSON.STRING (#weights_sha1 legacy_model_binding)),
   ("target_model_features_sha1", JSON.STRING ranking_target_model_digest),
   ("model_namespace_count", JSON.INT
      (IntInf.fromInt ranking_model_namespace_count)),
   ("export_model_current_theory",
     JSON.STRING hheval_legacy_model_current_theory),
   ("export_model_ancestry", JSON.ARRAY
      (map JSON.STRING hheval_legacy_model_ancestry)),
   ("export_model_namespace_count", JSON.INT
      (IntInf.fromInt hheval_legacy_model_namespace_count)),
   ("export_target_model_features_sha1", JSON.STRING target_model_digest),
   ("profile_set_sha1", JSON.STRING profile_set_sha1),
   ("row_set_sha1", JSON.STRING row_set_sha1),
   ("goal_bindings", JSON.ARRAY
      (map binding_json (#goal_bindings derivation))),
   ("row_count", JSON.INT (IntInf.fromInt (length (#current derivation)))),
   ("mismatches", JSON.INT (IntInf.fromInt (length differences))),
   ("binding_mismatches",
     JSON.INT (IntInf.fromInt (length binding_mismatches))),
   ("prover_spawns", JSON.INT
      (IntInf.fromInt (#prover_spawns derivation)))]);
val _ = write_lines output
  (("#hh-anchor-current-v1\t" ^ header) ::
   map hhEval.encode_anchor_row (#current derivation));
val _ = write_lines mismatches (map mismatch_json differences);
val result =
  {rows = length (#current derivation), mismatches = length differences,
   prover_spawns = #prover_spawns derivation};

val _ = print
  ("HHEVAL_PHASE3_ANCHOR_ROWS=" ^ Int.toString (#rows result) ^
   "\nHHEVAL_PHASE3_ANCHOR_MISMATCHES=" ^
   Int.toString (#mismatches result) ^
   "\nHHEVAL_PHASE3_ANCHOR_PROVER_SPAWNS=" ^
   Int.toString (#prover_spawns result) ^ "\n");

val successful =
  if #mismatches result = 0 andalso null binding_mismatches andalso
     #prover_spawns result = 0 then true else false;
val status = if successful then OS.Process.success else OS.Process.failure;
in
  (status, successful, checkpoint_mode, theorem_names)
end;

val (hheval_status, hheval_successful, hheval_checkpoint_mode,
     hheval_completed_names) = hheval_run_current ();

fun hheval_write_completed_names names =
  let
    val stream = TextIO.openOut
      (required_env "HHEVAL_CURRENT_CHECKPOINT_COMPLETED_NAMES")
  in
    List.app (fn name => TextIO.output (stream, name ^ "\n")) names;
    TextIO.closeOut stream
  end;

fun hheval_write_checkpoint_stage text =
  let
    val stream = TextIO.openOut
      (required_env "HHEVAL_CURRENT_CHECKPOINT_STAGE_PATH")
  in
    TextIO.output (stream, text ^ "\n");
    TextIO.closeOut stream
  end;

val _ =
  if hheval_successful andalso hheval_checkpoint_mode then
    (hheval_write_completed_names hheval_completed_names;
     hheval_write_checkpoint_stage "saving";
     PolyML.fullGC ();
     PolyML.SaveState.saveState
       (required_env "HHEVAL_CURRENT_CHECKPOINT_NEXT_HEAP");
     hheval_write_checkpoint_stage "saved")
  else ();
val _ = OS.Process.exit hheval_status;
