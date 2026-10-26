(* The launcher imports no simplifier module. Dependencies are loaded only
   after recording the initial heap and setting the exact search path. *)
open Paired
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
    Meta.qquse path;
    Paired.emit ["used", path]
  end
(* Layout randomization (performance runs only): compile PERF_LAYOUT
   padding functions before any dependency, shifting every later code
   address. Both sides draw independent counts; no events are emitted. *)
fun layoutPadding () =
  case OS.Process.getEnv "PERF_LAYOUT" of
      NONE => ()
    | SOME s =>
      let
        val units = case Int.fromString s of
                        SOME n => if n >= 0 andalso Int.toString n = s then n
                                  else raise Fail ("bad PERF_LAYOUT: " ^ s)
                      | NONE => raise Fail ("bad PERF_LAYOUT: " ^ s)
        fun unit i = "fun layout_pad" ^ Int.toString i ^ " (x : int) = x + " ^
                     Int.toString i ^ ";\n"
        val rest = ref (String.explode
                          (String.concat (List.tabulate (units, unit))))
        fun next () = case !rest of
                          [] => NONE
                        | c :: cs => (rest := cs; SOME c)
        fun loop () =
          if null (!rest) then ()
          else (PolyML.compiler (next, [PolyML.Compiler.CPOutStream ignore])
                  ();
                loop ())
      in
        loop ()
      end
fun files () =
  List.app (fn (file, dir) =>
    Paired.emit ["loaded", OS.Path.concat (dir, file)])
    (Binarymap.listItems (Meta.fileDirMap ()))
val result =
  (layoutPadding ();
   Meta.loadPlan tracedUse "CheckSupport";
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
