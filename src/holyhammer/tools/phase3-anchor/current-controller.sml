load "hhEval";

fun required_env name =
  case OS.Process.getEnv name of
      SOME value => value
    | NONE => raise Fail (name ^ " is not set");

val theory = required_env "HHEVAL_THEORY";
val worker_root = required_env "HHEVAL_CURRENT_WORKER_ROOT";
val inner = required_env "HHEVAL_CURRENT_INNER";
val launch_dir = required_env "HHEVAL_CURRENT_LAUNCH_DIR";

fun write_text path text =
  let
    val output = TextIO.openOut path;
    val _ = TextIO.output (output, text);
  in
    TextIO.closeOut output
  end;

fun run_nested_worker () =
  let
    val script = OS.Path.concat
      (launch_dir, ".hheval_anchor_current_" ^ theory ^ ".sml");
    val kill_text =
      case OS.Process.getEnv "HHEVAL_CURRENT_TEST_SIGKILL_MARKER" of
          SOME path =>
            if path = "" then ""
            else String.concat
              ["val hheval_kill_out = TextIO.openOut ",
               Portable.mlquote path, ";\n",
               "val _ = TextIO.output (hheval_kill_out, \"nested-hol\n\");\n",
               "val _ = TextIO.closeOut hheval_kill_out;\n",
               "val _ = Posix.Process.kill (Posix.Process.K_PROC ",
               "(Posix.ProcEnv.getpid ()), Posix.Signal.kill);\n"]
        | NONE => "";
    val worker_text =
      if OS.Process.getEnv "HHEVAL_CURRENT_CHECKPOINT_LAUNCH" = SOME "atom"
      then String.concat
        ["PolyML.SaveState.loadState ",
         Portable.mlquote (required_env
           "HHEVAL_CURRENT_CHECKPOINT_PRIOR_HEAP"), ";\n",
         kill_text,
         "use ", Portable.mlquote inner, ";\n"]
      else String.concat
      ["load ", Portable.mlquote (theory ^ "Theory"), ";\n",
       "val hheval_legacy_model_current_theory = Theory.current_theory ();\n",
       "val hheval_legacy_model_ancestry = Theory.ancestry ",
       "hheval_legacy_model_current_theory;\n",
       "val hheval_legacy_model_namespace_count = length ",
       "(mlThmData.unsafe_namespace_thms ());\n",
       "val hheval_legacy_model_probe = mlThmData.create_thmdata ();\n",
       "val hheval_target_model_probe = hhLearn.create_thmdata_for ",
       Portable.mlquote theory, ";\n",
       "val hheval_checkpoint_schema = \"disabled\";\n",
       "val hheval_checkpoint_policy = \"disabled\";\n",
       "val hheval_checkpoint_theory = ", Portable.mlquote theory, ";\n",
       "val hheval_checkpoint_db_order = ([] : string list);\n",
       "val hheval_checkpoint_index = ref 0;\n",
       "val _ = Feedback.quiet_messages Theory.new_theory ",
       Portable.mlquote ("hheval_anchor_" ^ theory), ";\n",
       "load \"hhEval\";\n",
       "use ", Portable.mlquote inner, ";\n"];
    val _ = write_text script worker_text;
    val _ = aiLib.scratch_dir := worker_root;
    fun cleanup () = OS.FileSys.remove script handle OS.SysErr _ => ();
  in
    (smlExecScripts.exec_script script before cleanup ())
    handle error => (cleanup (); raise error)
  end;

fun validate_checkpoint_heap () =
  case OS.Process.getEnv "HHEVAL_CURRENT_CHECKPOINT_LAUNCH" of
      SOME launch =>
        if launch = "base" orelse launch = "atom" then
          let
            val environment =
              if launch = "base" then "HHEVAL_CURRENT_CHECKPOINT_HEAP"
              else "HHEVAL_CURRENT_CHECKPOINT_NEXT_HEAP";
            val heap = required_env environment;
            val script = OS.Path.concat
              (launch_dir, ".hheval_anchor_verify_" ^ theory ^ ".sml");
            val text = String.concat
              ["PolyML.SaveState.loadState ", Portable.mlquote heap, ";\n",
               "print \"HHEVAL_CURRENT_CHECKPOINT_HEAP_LOAD=success\\n\";\n"];
            val _ = write_text script text;
            fun cleanup () =
              OS.FileSys.remove script handle OS.SysErr _ => ();
          in
            (smlExecScripts.exec_script script before cleanup ())
            handle error => (cleanup (); raise error)
          end
        else ()
    | NONE => ();

fun main () =
  (run_nested_worker ();
   validate_checkpoint_heap ();
   print "HHEVAL_CURRENT_CHECKPOINT_HEAP_LOAD=success\n";
   print "HHEVAL_CURRENT_CONTROLLER=success\n";
   OS.Process.success);

val status =
  main ()
  handle Interrupt => raise Interrupt
       | error =>
           (TextIO.output (TextIO.stdErr,
              "current anchor derivation failed: " ^
              General.exnMessage error ^ "\n");
            OS.Process.failure);

val _ = OS.Process.exit status;
