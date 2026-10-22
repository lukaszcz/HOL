(* Exact campaign workloads, one construction/application per stage. *)
local
  open TacticInputs
  fun exercise n =
    (List.app (fn ({run,verify,...}:workload) => (run (); verify ()))
      (workloads n); true)
in
  val _ = Paired.check "assembly reset"
    (not (!PolyML.Compiler.assemblyCode) andalso
     not (!PolyML.Compiler.codetreeAfterOpt) andalso
     not (!PolyML.Compiler.icode))
  val _ = Paired.check "ordinary 0" (exercise 0)
  val _ = Paired.check "ordinary 8" (exercise 8)
  val _ = Paired.observe "complete" "TASK18-tactic-assembly-v1"
end
