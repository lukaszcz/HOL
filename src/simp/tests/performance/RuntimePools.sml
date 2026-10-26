(* Diagnostic only: loaded after the unchanged Performance target returns.
   The native interposer is preloaded; its extent is enabled only here.
   FFI setup and this traversal are NOT measurement-boundary snapshots. *)
val _ = let
  val _ = if PolyML.architecture () = "Arm64" then ()
          else raise Fail "runtime pools require full-64 Arm64"
  val library = Foreign.loadLibrary
    (valOf (OS.Process.getEnv "RUNTIME_POOLS_LIBRARY"))
  val beginPools = Foreign.buildCall0
    (Foreign.getSymbol library "runtime_pools_begin", (), Foreign.cVoid)
  val endPools = Foreign.buildCall0
    (Foreign.getSymbol library "runtime_pools_end", (), Foreign.cVoid)
  val _ = TextIO.print
    "@@RUNTIME_LAYOUT\tbegin\tArm64\trun,step,measured,experiment\n"
  val _ = TextIO.flushOut TextIO.stdOut
  val _ = beginPools ()
  val words = PolyML.showSize (run,step,measured,experiment)
  val _ = endPools ()
in
  TextIO.print ("@@RUNTIME_LAYOUT\tend\t" ^ Int.toString words ^ "\n");
  TextIO.flushOut TextIO.stdOut
end
