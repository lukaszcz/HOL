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
  (* Installed after private-first paths and tracing are active. Keeping the
     bootstrap independent of testutils permits a genuinely fresh min heap. *)
  val report : (string * bool -> unit) ref =
    ref (fn (_ : string, _ : bool) =>
                     raise Fail "check reporter not initialized")
  val checks = ref 0
  fun check name b =
    (!report (name, b);
     checks := !checks + 1;
     emit ["check", name, "pass"])
end
