(* The launcher imports no simplifier module. Dependencies are loaded only
   after recording the initial heap and setting the exact search path. *)
open Paired
val _ = PolyML.Compiler.assemblyCode := false
val _ = PolyML.Compiler.codetreeAfterOpt := false
val _ = PolyML.Compiler.icode := false
val optimizedTree =
  case Paired.env "PAIR_OPTIMIZED_TREE" of
    "true" => true
  | "false" => false
  | _ => raise Fail "invalid PAIR_OPTIMIZED_TREE"
val _ = Paired.emit ["begin", Paired.env "PAIR_SELECTION",
                     Paired.env "PAIR_FIXTURE", Paired.env "PAIR_CONTROL"]
val _ = Paired.emit ["cwd", OS.FileSys.getDir ()]
val _ = Paired.emit ["holdir", Paired.env "HOLDIR", Systeml.HOLDIR]
val _ = Paired.emit ["preloaded", String.concatWith "," (Meta.loaded ())]
val _ = List.app (fn (file, dir) =>
  Paired.emit ["heapfile", OS.Path.concat (dir, file)])
  (Binarymap.listItems (Meta.fileDirMap ()))
val _ = Meta.loadPath := [Paired.env "PAIR_PRIVATE",
                         OS.Path.concat (Paired.env "HOLDIR", "sigobj")]
val _ = List.app (fn s => Paired.emit ["search", s]) (!Meta.loadPath)
fun tracedUse path =
  let val path = holpathdb.subst_pathvars path
      val path = OS.Path.mkAbsolute
        {path=path, relativeTo=OS.FileSys.getDir ()}
  in
    Paired.emit ["use", path];
    if path = OS.Path.concat (Paired.env "PAIR_PRIVATE", "simpLib.sml")
    then
      let
        fun switches enabled =
          (PolyML.Compiler.assemblyCode := enabled;
           PolyML.Compiler.codetreeAfterOpt := (enabled andalso optimizedTree);
           PolyML.Compiler.icode := (enabled andalso optimizedTree))
      in
        if !PolyML.Compiler.assemblyCode orelse
           !PolyML.Compiler.codetreeAfterOpt orelse !PolyML.Compiler.icode
        then raise Fail "compiler printing unexpectedly enabled"
        else ();
        switches true;
        (Meta.qquse path handle e => (switches false; raise e));
        switches false
      end
    else Meta.qquse path;
    Paired.emit ["used", path]
  end
fun files () =
  List.app (fn (file, dir) =>
    Paired.emit ["loaded", OS.Path.concat (dir, file)])
    (Binarymap.listItems (Meta.fileDirMap ()))
val result =
  (Meta.loadPlan tracedUse "CheckSupport";
   Meta.loadPlan tracedUse (Paired.env "PAIR_TARGET"); "pass")
  handle e => (Paired.emit ["exception", General.exnName e,
                            String.toString (General.exnMessage e)];
               "error")
val _ = files ()
val _ = if Paired.env "PAIR_CONTROL" = "truncated" then ()
        else Paired.emit ["end", result, Int.toString (!Paired.checks)]
val _ = OS.Process.exit
  (if result = "pass" andalso Paired.env "PAIR_CONTROL" <> "failed"
   then OS.Process.success else OS.Process.failure)
