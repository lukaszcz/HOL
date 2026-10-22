(* Reuse the exact campaign proof/name/persistence/callback fixture. *)
local
  open ExclusionInputs
  fun exercise n = let
    fun one ({build,verify,makers,collectors,...}:workload) = let
      val m = !makerCalls
      val c = !collectorCalls
      val result = build ()
      val _ = required (!makerCalls-m = makers andalso
                        !collectorCalls-c = collectors)
    in verify result end
  in List.app one (workloads n); true end
in
  val _ = Paired.check "assembly reset"
    (not (!PolyML.Compiler.assemblyCode) andalso
     not (!PolyML.Compiler.codetreeAfterOpt) andalso
     not (!PolyML.Compiler.icode))
  val _ = Paired.check "delete/replay 0" (exercise 0)
  val _ = Paired.check "delete/replay 10" (exercise 10)
  val _ = Paired.observe "complete" "TASK17-exclusion-assembly-v1"
end
