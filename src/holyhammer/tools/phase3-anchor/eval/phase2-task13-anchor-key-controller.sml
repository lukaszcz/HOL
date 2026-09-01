load "hhEval";

fun required_env name =
  case OS.Process.getEnv name of
      SOME value => value
    | NONE => raise Fail (name ^ " is not set");

fun write_text path text =
  let
    val output = TextIO.openOut path
    val _ = TextIO.output (output, text)
  in
    TextIO.closeOut output
  end;

val anchor_theory = required_env "HHEVAL_THEORY";
val anchor_driver = required_env "HHEVAL_ANCHOR_DRIVER";
val anchor_witness = required_env "HHEVAL_ANCHOR_WITNESS";

fun run_nested_worker () =
  let
    val expdir = "/tmp/phase2-task13-anchor-key-derive-" ^ anchor_theory
    val script = hhEval.write_evalscript expdir anchor_theory [] 1
    val worker_text = String.concat
      ["load ", Portable.mlquote (anchor_theory ^ "Theory"), ";\n",
       "load \"hhEval\";\n",
       "val task13_anchor_hhEval_dependency = hhEval.eval_thy;\n",
       "use ", Portable.mlquote anchor_driver, ";\n"]
    val _ = write_text script worker_text
    val _ = smlExecScripts.buildheap_dir :=
      OS.Path.concat (OS.Path.dir anchor_witness, "worker-out")
    fun cleanup () = OS.FileSys.remove script handle OS.SysErr _ => ()
  in
    (smlExecScripts.exec_script script before cleanup ())
    handle error => (cleanup (); raise error)
  end;

val _ = run_nested_worker ();
