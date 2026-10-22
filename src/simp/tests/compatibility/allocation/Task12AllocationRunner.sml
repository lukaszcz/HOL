(* Same audited protocol as paired/runner.sml; additionally request compiler
   assembly for the selected private implementation, never alter its source. *)
open Paired
val _ = Paired.emit ["begin", Paired.env "PAIR_SELECTION",
                     Paired.env "PAIR_FIXTURE", Paired.env "PAIR_CONTROL"]
val _ = Paired.emit ["cwd", OS.FileSys.getDir ()]
val _ = Paired.emit ["holdir", Paired.env "HOLDIR", Systeml.HOLDIR]
val _ = Paired.emit ["preloaded", String.concatWith "," (Meta.loaded ())]
val _ = List.app (fn (file,dir) =>
  Paired.emit ["heapfile", OS.Path.concat (dir,file)])
  (Binarymap.listItems (Meta.fileDirMap ()))
val _ = Meta.loadPath := [Paired.env "PAIR_PRIVATE",
                         OS.Path.concat (Paired.env "HOLDIR", "sigobj")]
val _ = List.app (fn s => Paired.emit ["search",s]) (!Meta.loadPath)
fun tracedUse path = let
  val path = holpathdb.subst_pathvars path
  val path = OS.Path.mkAbsolute
    {path=path,relativeTo=OS.FileSys.getDir ()}
  val assembly = OS.Path.file path = "Cond_rewr.sml" orelse
                 OS.Path.file path = "SimpTracking.sml"
  val previous = !PolyML.Compiler.assemblyCode
  fun reset () = PolyML.Compiler.assemblyCode := previous
in
  Paired.emit ["use",path];
  PolyML.Compiler.assemblyCode := assembly;
  (Meta.qquse path handle e => (reset (); raise e));
  reset ();
  Paired.emit ["used",path]
end
fun files () = List.app (fn (file,dir) =>
  Paired.emit ["loaded",OS.Path.concat (dir,file)])
  (Binarymap.listItems (Meta.fileDirMap ()))
val result =
  (Meta.loadPlan tracedUse "CheckSupport";
   Meta.loadPlan tracedUse (Paired.env "PAIR_TARGET"); "pass")
  handle e => (Paired.emit ["exception",General.exnName e,
                            String.toString (General.exnMessage e)]; "error")
val _ = files ()
val _ = Paired.emit ["end",result,Int.toString (!Paired.checks)]
val _ = OS.Process.exit
  (if result = "pass" then OS.Process.success else OS.Process.failure)
