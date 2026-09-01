load "hhEval";

fun required_env name =
  case OS.Process.getEnv name of
      SOME value => value
    | NONE => raise Fail (name ^ " is not set");

val anchor_theory = required_env "HHEVAL_ANCHOR_THEORY";
val anchor_driver = required_env "HHEVAL_ANCHOR_DRIVER";
val anchor_worker_root = required_env "HHEVAL_ANCHOR_WORKER_ROOT";
val anchor_objects = required_env "HHEVAL_ANCHOR_OBJECTS";
val anchor_worktree = required_env "HHEVAL_ANCHOR_WORKTREE";
val anchor_schedule_source =
  case OS.Process.getEnv "HHEVAL_ANCHOR_SCHEDULE_SOURCE" of
      SOME path => if path = "" then OS.Path.concat
        (anchor_worktree, "src/holyhammer/hhSchedule.sml") else path
    | NONE => OS.Path.concat
        (anchor_worktree, "src/holyhammer/hhSchedule.sml");
val anchor_theory_dir = required_env "HHEVAL_ANCHOR_THEORY_DIR";
val success_marker = required_env "HHEVAL_ANCHOR_SUCCESS_MARKER";

fun write_text path text =
  let
    val output = TextIO.openOut path
    val _ = TextIO.output (output, text)
  in
    TextIO.closeOut output
  end;

fun run_nested_worker () =
  let
    val _ = OS.FileSys.remove success_marker handle OS.SysErr _ => ()
    (* The controller replaces the entire worker script, so the only
       service formerly provided by [write_evalscript] was choosing the
       theory source directory.  Use the invocation-pinned launch directory
       explicitly; this also covers certified test theories outside the
       historical source tree. *)
    val script = OS.Path.concat
      (anchor_theory_dir, ".hheval_task10_anchor_" ^ anchor_theory ^ ".sml")
    val worker_text = String.concat
      ["load ", Portable.mlquote (anchor_theory ^ "Theory"), ";\n",
       "load \"hhEval\";\n",
       "val task10_anchor_hhEval_dependency = hhEval.eval_thy;\n",
       "loadPath := ", Portable.mlquote anchor_objects,
       " :: !loadPath;\n",
       "use ", Portable.mlquote (OS.Path.concat
         (anchor_worktree, "src/holyhammer/hhMonomorph.sml")), ";\n",
       "use ", Portable.mlquote (OS.Path.concat
         (anchor_worktree, "src/holyhammer/hhProblemGen.sml")), ";\n",
       "use ", Portable.mlquote anchor_schedule_source, ";\n",
       "use ", Portable.mlquote anchor_driver, ";\n"]
    val _ = write_text script worker_text
    val _ = smlExecScripts.buildheap_dir :=
      OS.Path.concat (anchor_worker_root, "worker-out")
    fun cleanup () = OS.FileSys.remove script handle OS.SysErr _ => ()
  in
    (smlExecScripts.exec_script script;
     if OS.FileSys.access (success_marker, []) then cleanup ()
     else (cleanup (); raise Fail "anchor worker did not certify success"))
    handle error => (cleanup (); raise error)
  end;

fun main () =
  (run_nested_worker ();
   print "HHEVAL_ANCHOR_CONTROLLER=success\n";
   OS.Process.success);

val status =
  main ()
  handle Interrupt => raise Interrupt
       | error =>
           (TextIO.output (TextIO.stdErr,
              "anchor manifest generation failed: " ^
              General.exnMessage error ^ "\n");
            OS.Process.failure);

val _ = OS.Process.exit status;
