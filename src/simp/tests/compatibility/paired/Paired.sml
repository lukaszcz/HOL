(* Harness-only protocol. No production simplifier instrumentation. *)
structure Paired =
struct
  fun env name =
    case OS.Process.getEnv name of
        SOME s => s
      | NONE => raise Fail ("missing environment variable: " ^ name)
  val sequence = ref 0
  fun emit fields =
    (print ("@@PAIR\t" ^ Int.toString (!sequence) ^ "\t" ^
            String.concatWith "\t" fields ^ "\n");
     sequence := !sequence + 1;
     TextIO.flushOut TextIO.stdOut)
  fun observe key value =
    if env "PAIR_CONTROL" = "missing" andalso key = "second.printers" then ()
    else emit ["observation", key, value]
  val checks = ref 0
  fun check name b =
    (testutils.tprint name;
     if b then testutils.OK () else testutils.die name;
     checks := !checks + 1;
     emit ["check", name, "pass"])
end
