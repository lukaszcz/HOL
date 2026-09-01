fun checkpoint_required_env name =
  case OS.Process.getEnv name of
      SOME value => value
    | NONE => raise Fail (name ^ " is not set");

val hheval_checkpoint_schema = "hh-current-db-checkpoint-chain-v1";
val hheval_checkpoint_policy = "hh-current-db-soft420-hard600-prune-v2";
val hheval_checkpoint_theory = checkpoint_required_env "HHEVAL_THEORY";
val hheval_checkpoint_heap =
  checkpoint_required_env "HHEVAL_CURRENT_CHECKPOINT_HEAP";
val hheval_checkpoint_db_order =
  map #1 (DB.theorems hheval_checkpoint_theory);
val hheval_checkpoint_index = ref 0;
val hheval_checkpoint_model = hheval_legacy_model_probe;
val hheval_checkpoint_model_binding =
  hhEval.anchor_model_binding hheval_checkpoint_model;
val hheval_checkpoint_target_model = hheval_target_model_probe;
val _ = smlRedirect.hide_flag := false;

val checkpoint_forbidden_environment =
  ["HHEVAL_ANCHOR_BASELINE", "HHEVAL_CURRENT_BASELINE_SHA256",
   "HHEVAL_ANCHOR_PREMISES_DIRECTORY",
   "HHEVAL_ANCHOR_PREMISES_PROVENANCE_SHA256",
   "HHEVAL_CURRENT_RANKINGS_DIRECTORY",
   "HHEVAL_CURRENT_MODEL_INVENTORY_SHA1",
   "HHEVAL_CURRENT_MODEL_FEATURES_SHA1",
   "HHEVAL_CURRENT_MODEL_WEIGHTS_SHA1"];
val _ = List.app (fn name =>
  case OS.Process.getEnv name of
      NONE => ()
    | SOME _ => raise Fail
        ("checkpoint base rejects baseline/carried input " ^ name))
  checkpoint_forbidden_environment;

fun checkpoint_write_lines path lines =
  let
    val output = TextIO.openOut path
    val _ = List.app (fn line => TextIO.output (output, line ^ "\n")) lines
  in
    TextIO.closeOut output
  end;

fun checkpoint_sha1_text text =
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
  end;
fun checkpoint_frame text = Int.toString (String.size text) ^ ":" ^ text;
fun checkpoint_sequence_digest values =
  checkpoint_sha1_text (String.concat (map checkpoint_frame values));
fun checkpoint_feature_text (name, features) =
  name ^ "\001" ^ String.concatWith "," (map Int.toString features);
val hheval_checkpoint_db_order_sha1 =
  checkpoint_sequence_digest hheval_checkpoint_db_order;
val hheval_checkpoint_target_model_sha1 = checkpoint_sequence_digest
  (map checkpoint_feature_text (#2 hheval_checkpoint_target_model));
val checkpoint_metadata = JSONPrinter.valueToString (JSON.OBJECT
  [("schema", JSON.STRING hheval_checkpoint_schema),
   ("policy_version", JSON.STRING hheval_checkpoint_policy),
   ("theory", JSON.STRING hheval_checkpoint_theory),
   ("db_goal_count", JSON.INT
      (IntInf.fromInt (length hheval_checkpoint_db_order))),
   ("db_order_sha1", JSON.STRING hheval_checkpoint_db_order_sha1),
   ("model_current_theory",
      JSON.STRING hheval_legacy_model_current_theory),
   ("model_ancestry", JSON.ARRAY
      (map JSON.STRING hheval_legacy_model_ancestry)),
   ("model_namespace_count", JSON.INT
      (IntInf.fromInt hheval_legacy_model_namespace_count)),
   ("model_inventory_sha1", JSON.STRING
      (#inventory_sha1 hheval_checkpoint_model_binding)),
   ("model_features_sha1", JSON.STRING
      (#features_sha1 hheval_checkpoint_model_binding)),
   ("model_weights_sha1", JSON.STRING
      (#weights_sha1 hheval_checkpoint_model_binding)),
   ("model_feature_rows", JSON.INT
      (IntInf.fromInt (#feature_rows hheval_checkpoint_model_binding))),
   ("target_model_features_sha1",
      JSON.STRING hheval_checkpoint_target_model_sha1)]);

val _ = checkpoint_write_lines
  (checkpoint_required_env "HHEVAL_CURRENT_CHECKPOINT_DB_ORDER")
  hheval_checkpoint_db_order;
val _ = checkpoint_write_lines
  (checkpoint_required_env "HHEVAL_CURRENT_CHECKPOINT_BASE_METADATA")
  [checkpoint_metadata];
val _ = print
  ("HHEVAL_CURRENT_CHECKPOINT_BASE=saving\n" ^
   "HHEVAL_CURRENT_CHECKPOINT_DB_GOALS=" ^
   Int.toString (length hheval_checkpoint_db_order) ^ "\n");
val _ = PolyML.fullGC ();
val _ = PolyML.SaveState.saveState hheval_checkpoint_heap;
