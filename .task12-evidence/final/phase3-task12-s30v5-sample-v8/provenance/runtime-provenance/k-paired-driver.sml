val _ = (load "BasicProvers"; load "hhEval");

fun required name =
  case OS.Process.getEnv name of
      SOME value => value
    | NONE => raise Fail (name ^ " is not set");

fun trim line =
  if size line > 0 andalso String.sub (line, size line - 1) = #"\n" then
    String.substring (line, 0, size line - 1)
  else line;

fun goal_ids path theory =
  let
    val input = TextIO.openIn path
    fun loop acc =
      case TextIO.inputLine input of
          NONE => rev acc
        | SOME line =>
            (case String.fields (fn c => c = #"\t") (trim line) of
                 [row_theory, goal] =>
                   loop (if row_theory = theory then goal :: acc else acc)
               | _ => raise Fail "invalid K goal inventory")
    val result = loop []
    val _ = TextIO.closeIn input
  in
    if null result then raise Fail "empty K theory subset" else result
  end;

fun write_count path count =
  let val output = TextIO.openOut path in
    TextIO.output (output, Int.toString count ^ "\n");
    TextIO.closeOut output
  end;

fun require_prover name =
  case hhProver.lookup name of
      NONE => raise Fail ("unknown K prover: " ^ name)
    | SOME config =>
        (case hhProver.probe config of
             NONE => raise Fail ("unavailable K prover: " ^ name)
           | SOME {path, version = NONE, ...} =>
               raise Fail ("unresolved K prover version: " ^ name)
           | SOME {path, version = SOME version, tested} =>
               (name, path, version, tested));

fun write_versions path rows =
  let
    val output = TextIO.openOut path
    fun write (name, executable, version, tested) =
      TextIO.output (output,
        String.concatWith "\t"
          [name, executable, version, Bool.toString tested] ^ "\n")
  in
    List.app write rows;
    TextIO.closeOut output
  end;

val condition : hhEval.condition =
  {cond_id = "s30-v5", regime = hhEval.Chainy,
   selector = hhEval.PerSlice,
   engine = hhEval.Sched
     {provers = ["e", "vampire", "zipperposition"],
      slices = 24, cores = 24, max_proofs = 4},
   timeout = 30, reconstruct = true};

val theory = required "HHEVAL_THEORY";
val theory_dir = required "HHEVAL_THEORY_DIR";
val inventory = required "HHEVAL_GOAL_INVENTORY";
val prime_dir = required "HHEVAL_PRIME_EXPDIR";
val replay_dir = required "HHEVAL_REPLAY_EXPDIR";
val selected = goal_ids inventory theory;
val _ = OS.FileSys.chDir theory_dir;
val _ = load (theory ^ "Theory");
val _ = Feedback.quiet_messages Theory.new_theory
  ("hheval_task12_k_" ^ theory);
val _ = hhEval.set_worker_settings {conditions = [condition], sample = 1};
val _ = hhEval.set_worker_goal_ids selected;
val resolved = map require_prover ["e", "vampire", "zipperposition"];
val version_spawns = hhProver.spawn_count ();
val _ = if version_spawns = 3 then ()
        else raise Fail "K prover version resolution did not spawn exactly 3";
val _ = write_versions (required "HHEVAL_RESOLVED_VERSIONS") resolved;
val _ = write_count (required "HHEVAL_VERSION_SPAWNS") version_spawns;
val _ = hhProver.reset_spawn_count ();
val _ = hhEval.eval_thy prime_dir theory;
val prime_spawns = hhProver.spawn_count ();
val _ = if hhEval.worker_theory_complete prime_dir theory then ()
        else raise Fail "K prime journal incomplete";
val _ = hhProver.reset_spawn_count ();
val _ = hhEval.eval_thy replay_dir theory;
val replay_spawns = hhProver.spawn_count ();
val _ = if hhEval.worker_theory_complete replay_dir theory then ()
        else raise Fail "K replay journal incomplete";
val _ = write_count (required "HHEVAL_PRIME_SPAWNS") prime_spawns;
val _ = write_count (required "HHEVAL_REPLAY_SPAWNS") replay_spawns;
val _ = if prime_spawns = 0 andalso replay_spawns = 0 then ()
        else raise Fail "K cache witness spawned a post-reset prover";
