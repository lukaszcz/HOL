fun required_env name =
  case OS.Process.getEnv name of
      SOME value => value
    | NONE => raise Fail (name ^ " is not set");

val anchor_theory = required_env "HHEVAL_ANCHOR_THEORY";
val anchor_driver = required_env "HHEVAL_ANCHOR_DRIVER";
val anchor_worker_root = required_env "HHEVAL_ANCHOR_WORKER_ROOT";

val _ = load (anchor_theory ^ "Theory");
val _ = load "mlNearestNeighbor";
val _ = load "mlFeature";
val _ = load "mlThmData";
val _ = load "hhSchedule";
val _ = aiLib.scratch_dir := anchor_worker_root;

fun main () =
  (use anchor_driver;
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
