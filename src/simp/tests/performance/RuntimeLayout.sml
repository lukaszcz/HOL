(* Loaded only AFTER the unmodified Performance target has returned. No
   compiler printing, forced collection, casts or unchecked memory reads.
   showSize traverses actual reachable objects; it does not trace execution.
   These snapshots are NOT measurement-boundary layouts or timing evidence. *)
val _ = let
  val _ = if PolyML.architecture () = "Arm64" then ()
          else raise Fail "runtime layout requires full-64 Arm64"
  val _ = TextIO.print
    "@@RUNTIME_LAYOUT\tbegin\tArm64\trun,step,measured,experiment\n"
  val _ = TextIO.flushOut TextIO.stdOut
  val words = PolyML.showSize (run,step,measured,experiment)
in
  TextIO.print ("@@RUNTIME_LAYOUT\tend\t" ^ Int.toString words ^ "\n");
  TextIO.flushOut TextIO.stdOut
end
