(* This file is loaded only by the generated, nested theory worker.  Its
   wrapper has already loaded the target theory followed by hhEval, exactly as
   the S30-v2 worker did. *)
open HolKernel;

fun required_env name =
  case OS.Process.getEnv name of
      SOME value => value
    | NONE => raise Fail (name ^ " is not set");

val anchor_theory = required_env "HHEVAL_THEORY";
val anchor_output = required_env "HHEVAL_ANCHOR_OUTPUT";
val anchor_witness = required_env "HHEVAL_ANCHOR_WITNESS";

fun make_options slices cores : hhConfig.hh_options =
  let val base = hhConfig.snapshot () in
    {timeout = 30, max_proofs = 4,
     provers = ["e", "vampire", "zipperposition"],
     slices = slices, cores = cores, filter = "knn", max_facts = NONE,
     format = "", type_enc = "", lam_trans = "", mono_iters = 3,
     mono_instances = NONE, minimize = true, preplay_timeout = 1.0,
     minimize_timeout = 1.0, cache = false, cache_dir = #cache_dir base,
     cache_max_entries = 100000, debug_dir = NONE}
  end;

val baseline_options = make_options 8 8;
val gate_options = make_options 16 16;
val baseline_schedule = hhSlice.mk_schedule baseline_options;
val gate_schedule = hhSlice.mk_schedule gate_options;
val gate_anchor_schedule = List.take (gate_schedule, 8);

fun maximum_facts
    (schedule : (hhProver.prover_config * hhProver.slice) list) =
  foldl Int.max 0 (map (#nfacts o #2) schedule);

fun same_slice (left : hhProver.slice, right : hhProver.slice) =
  #prover left = #prover right andalso #format left = #format right andalso
  #type_enc left = #type_enc right andalso
  #lam_trans left = #lam_trans right andalso
  #nfacts left = #nfacts right andalso #filter left = #filter right andalso
  #extra_opts left = #extra_opts right andalso
  #slice_size left = #slice_size right;

fun same_profile ((_, left) : hhProver.prover_config * hhProver.slice,
                  (_, right) : hhProver.prover_config * hhProver.slice) =
  same_slice (left, right);

val _ =
  if length baseline_schedule = 8 andalso
     ListPair.allEq same_profile (baseline_schedule, gate_anchor_schedule)
  then ()
  else raise Fail "baseline and gate anchor profiles differ";

val baseline_maximum = maximum_facts baseline_schedule;
val gate_maximum = maximum_facts gate_schedule;
val _ = if baseline_maximum = gate_maximum then ()
  else raise Fail "baseline and gate anchor selectors have different maxima";

fun pool_ids (theories, current) =
  map (fn (theory, name) => theory ^ "Theory." ^ name)
    (List.concat (map hhExportLib.thmidl_in_thy theories) @ current);

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
  end;

fun lookup_pool name pools =
  case List.find (fn (other, _) => other = name) pools of
      SOME (_, pool) => pool
    | NONE => [];

fun select_knn pool count goal =
  let
    val (weights, features) = mlThmData.create_thmdata ()
    val permitted = List.filter (fn (name, _) =>
      List.exists (fn allowed => allowed = name) pool) features
  in
    mlNearestNeighbor.thmknn_wdep (weights, permitted) count
      (mlFeature.fea_of_goal true goal)
  end;

fun version_of "e" = SOME "3.2.5-ho"
  | version_of "vampire" = SOME "5.0.1"
  | version_of "zipperposition" = SOME "2.1"
  | version_of name = raise Fail ("unknown anchor prover " ^ name);

fun path_of "e" = required_env "HOL4_EPROVER_EXECUTABLE"
  | path_of "vampire" = required_env "HOL4_VAMPIRE_EXECUTABLE"
  | path_of "zipperposition" =
      required_env "HOL4_ZIPPERPOSITION_EXECUTABLE"
  | path_of name = raise Fail ("unknown anchor prover " ^ name);

fun indexed items =
  let
    fun loop _ [] = []
      | loop index (item :: rest) =
          (index, item) :: loop (index + 1) rest
  in
    loop 1 items
  end;

fun take_up_to 0 _ = []
  | take_up_to _ [] = []
  | take_up_to count (item :: rest) =
      item :: take_up_to (count - 1) rest;

fun sha1_text text =
  let
    val bytes = Byte.stringToBytes text
    val length = Word8Vector.length bytes
    fun read (offset, requested) =
      let
        val count = Int.min (requested, length - offset)
        val chunk = Word8Vector.tabulate
          (count, fn index => Word8Vector.sub (bytes, offset + index))
      in
        (chunk, offset + count)
      end
  in
    SHA1.sha1String read 0
  end;

fun frame text = Int.toString (String.size text) ^ ":" ^ text;

fun premise_digest count premises =
  sha1_text (String.concat (map frame (take_up_to count premises)));

fun request_key (config : hhProver.prover_config,
                 slice : hhProver.slice) =
  let
    val request : hhProver.run_request =
      {timeout = 30, format = #format slice,
       problem = hhSchedule.problem_path slice,
       extra = #extra_opts slice, debug_dir = NONE}
    val path = path_of (#name config)
    val (_, argv) = #mk_command config path (#format request) request
  in
    hhCache.key_of
      {prover = #name config, version = version_of (#name config),
       argv = argv, problem = #problem request}
  end;

fun indexed_keys schedule =
  map (fn (index, (config, slice)) =>
    (index, config, slice, request_key (config, slice)))
    (indexed schedule);

fun derive () =
  let
    val _ = hhProver.reset_spawn_count ()
    val pools = chainy_pools anchor_theory
    val output = TextIO.openOut anchor_output
    fun emit theorem_name premises
        ((baseline_index, _, baseline_slice, baseline_key),
         (gate_index, _, gate_slice, gate_key)) =
      let
        val _ = if baseline_index = gate_index andalso
          same_slice (baseline_slice, gate_slice)
          then () else raise Fail "paired anchor profile mismatch"
        val _ = if baseline_key = gate_key then ()
          else raise Fail "paired anchor request keys differ"
        val fields =
          [anchor_theory ^ "." ^ theorem_name,
           Int.toString baseline_index, #prover baseline_slice,
           #format baseline_slice, #type_enc baseline_slice,
           #lam_trans baseline_slice, Int.toString (#nfacts baseline_slice),
           premise_digest (#nfacts baseline_slice) premises,
           baseline_key, gate_key]
      in
        TextIO.output (output, String.concatWith "\t" fields ^ "\n")
      end
    fun emit_pairs _ _ [] [] = ()
      | emit_pairs theorem_name premises (baseline :: baselines)
          (gate :: gates) =
          (emit theorem_name premises (baseline, gate);
           emit_pairs theorem_name premises baselines gates)
      | emit_pairs _ _ _ _ = raise Fail "paired anchor key count differs"
    fun one (name, theorem) =
      let
        val goal = dest_thm theorem
        val pool = lookup_pool name pools
        val baseline_premises = select_knn pool baseline_maximum goal
        val gate_premises = select_knn pool gate_maximum goal
        val _ = if baseline_premises = gate_premises then ()
          else raise Fail "baseline and gate selected premises differ"
        val _ = hhSchedule.export_problems baseline_options goal
          baseline_premises baseline_schedule
        val baseline_keys = indexed_keys baseline_schedule
        val _ = hhSchedule.export_problems gate_options goal gate_premises
          gate_anchor_schedule
        val gate_keys = indexed_keys gate_anchor_schedule
      in
        emit_pairs name baseline_premises baseline_keys gate_keys
      end
    val _ = app one (DB.theorems anchor_theory)
    val _ = TextIO.closeOut output
    val spawns = hhProver.spawn_count ()
    val _ = if spawns = 0 then ()
      else raise Fail "anchor key derivation spawned a prover"
    val witness = TextIO.openOut anchor_witness
    val _ = TextIO.output (witness, "TASK13_ANCHOR_PROVER_SPAWNS=" ^
      Int.toString spawns ^ "\n")
    val _ = TextIO.closeOut witness
  in
    print ("TASK13_ANCHOR_PROVER_SPAWNS=" ^
      Int.toString spawns ^ "\n")
  end;

val _ = derive ();
