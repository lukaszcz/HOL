(* Diagnostic compiler printing only; never install in acceptance launchers.
   The paired runner calls this instead of Meta.qquse. All other runner and
   workload source bytes remain unchanged. Printing changes process layout:
   observations from this launcher are NOT acceptance timing evidence. *)
val codegenTargets =
  ["Cond_rewr.sml", "Traverse.sml", "simpLib.sml", "MatrixSupport.sml",
   "Performance.sml"]
fun codegenSwitch enabled =
  (PolyML.Compiler.assemblyCode := enabled;
   PolyML.Compiler.codetreeAfterOpt := enabled;
   PolyML.Compiler.icode := enabled)
val _ = codegenSwitch false
fun codegenUse path = let
  val private = Paired.env "PAIR_PRIVATE"
  val name = OS.Path.file path
  val selected = Paired.env "PAIR_FIXTURE" = "performance" andalso
                 OS.Path.dir path = private andalso
                 List.exists (fn n => n = name) codegenTargets
  fun mark stage = print ("@@CALLER_CODEGEN\t" ^ stage ^ "\t" ^
                          path ^ "\n")
in
  if !PolyML.Compiler.assemblyCode orelse
     !PolyML.Compiler.codetreeAfterOpt orelse !PolyML.Compiler.icode
  then raise Fail "compiler printing unexpectedly enabled" else ();
  if selected then
    (mark "begin"; codegenSwitch true;
     (Meta.qquse path handle e =>
       (codegenSwitch false; mark "aborted"; raise e));
     codegenSwitch false; mark "end")
  else Meta.qquse path
end
