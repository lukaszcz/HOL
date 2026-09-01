load "BasicProvers";
load "hhEval";

open HolKernel;

fun required_env name =
  case OS.Process.getEnv name of
      SOME value => value
    | NONE => raise Fail (name ^ " is not set");

fun seconds timer = Time.toReal (Timer.checkRealTimer timer);

fun output_line output values =
  TextIO.output (output, String.concatWith "\t" values ^ "\n");

fun pool_ids (theories, current) =
  map (fn (theory, name) => theory ^ "Theory." ^ name)
    (List.concat (map hhExportLib.thmidl_in_thy theories) @ current);

fun chainy_pools theory =
  let
    val order = hhExportLib.sorted_ancestry [theory];
    val earlier =
      if List.exists (fn name => name = theory) order then
        hhExportLib.before_elem theory order
      else order;
    fun one (name, theorem) =
      let
        val older = List.filter (hhExportLib.older_than theorem)
          (DB.thms theory);
        val current = map (fn (other, _) => (theory, other)) older;
      in
        (name, pool_ids (earlier, current))
      end;
  in
    map one (DB.theorems theory)
  end;

fun lookup_pool name pools =
  case List.find (fn (other, _) => other = name) pools of
      SOME (_, pool) => pool
    | NONE => [];

fun maximum_by_filter schedule filter =
  foldl Int.max 0
    (map (fn (_, slice : hhProver.slice) => #nfacts slice)
      (List.filter (fn (_, slice : hhProver.slice) =>
        #filter slice = filter) schedule));

fun run () =
  let
    val theory = required_env "HHEVAL_THEORY";
    val theory_dir = required_env "HHEVAL_THEORY_DIR";
    val output_path = required_env "HHEVAL_PROBE_OUTPUT";
    val load_timer = Timer.startRealTimer ();
    val _ = OS.FileSys.chDir theory_dir;
    val _ = load (theory ^ "Theory");
    val _ = Feedback.quiet_messages Theory.new_theory
      ("hheval_probe_" ^ theory);
    val load_seconds = seconds load_timer;
    val options = hhConfig.snapshot ();
    val schedule = hhSlice.mk_schedule
      {timeout = 30, max_proofs = 4,
       provers = ["e", "vampire", "zipperposition"],
       slices = 24, cores = 24, filter = "", max_facts = NONE,
       format = "", type_enc = "", lam_trans = "", mono_iters = 3,
       mono_instances = NONE, minimize = true,
       preplay_timeout = #preplay_timeout options,
       minimize_timeout = #minimize_timeout options,
       cache = false, cache_dir = #cache_dir options,
       cache_max_entries = #cache_max_entries options,
       debug_dir = NONE};
    val filters = ["knn", "mepo", "mash", "mesh"];
    val maxima = map (fn filter =>
      (filter, maximum_by_filter schedule filter)) filters;
    val pools = chainy_pools theory;
    val thmdata_timer = Timer.startRealTimer ();
    val thmdata = hhLearn.create_thmdata_for theory;
    val thmdata_seconds = seconds thmdata_timer;
    val _ = hhLearn.clean_context_cache ();
    val context_timer = Timer.startRealTimer ();
    val context = hhLearn.create_context_for theory thmdata;
    val context_seconds = seconds context_timer;
    val output = TextIO.openOut output_path;
    val _ = output_line output
      ["context", theory, Real.toString load_seconds,
       Real.toString thmdata_seconds, Real.toString context_seconds,
       Int.toString (length (hhLearn.context_thmids context))];
    fun rank_one (name, theorem) =
      let
        val goal_id = theory ^ "." ^ name;
      in
        if hhEval.sample_goal 500 goal_id then
          let
            val goal = dest_thm theorem;
            val pool = lookup_pool name pools;
            fun one (filter, maximum) =
              let
                val timer = Timer.startRealTimer ();
                val ranking = hhLearn.rank context
                  {filter = filter, pool = SOME pool,
                   goal = goal, n = maximum};
                val elapsed = seconds timer;
              in
                output_line output
                  ["rank", goal_id, filter, Int.toString maximum,
                   Real.toString elapsed, Int.toString (length ranking),
                   Int.toString (length pool)]
              end;
          in
            List.app one maxima
          end
        else ()
      end;
    val _ = List.app rank_one (DB.theorems theory);
    val cleanup_timer = Timer.startRealTimer ();
    val _ = hhLearn.clean_context_cache ();
    val cleanup_seconds = seconds cleanup_timer;
    val _ = output_line output
      ["cleanup", theory, Real.toString cleanup_seconds];
    val _ = TextIO.closeOut output;
  in
    print ("HHEVAL_PHASE3_PROBE=" ^ theory ^ "\n")
  end;

val _ = run ();
