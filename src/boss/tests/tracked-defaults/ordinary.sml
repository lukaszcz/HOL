(* Fresh hol.state0 process: prerequisites are not imports. *)
open HolKernel testutils
fun check label ok = (tprint label; if ok then OK () else die label)
val extensions =
  ["TraverseExt","Cond_rewrExt","OpeningExt","TravrulesExt",
   "simpExtLib","congExtLib","pureSimpsExt","boolSimpsExt",
   "combinSimpsExt","numSimpsExt","listSimpsExt","pred_setSimpsExt",
   "trackedSimpDefaults","simpMarkerLib","SplitData","splitLib",
   "splitPersistLib"]
fun absent () = List.app (fn name => check ("ordinary load excludes " ^ name)
  (not (List.exists (equal name) (Meta.loaded ())) andalso
   not (Option.isSome (#lookupStruct PolyML.globalNameSpace name)))) extensions
val _ = absent ()
val root = Systeml.HOLDIR
val _ = List.app (fn path =>
  (Meta.load (OS.Path.concat (root,path)); absent ()))
  ["src/basicProof/BasicProvers","src/num/arith/src/numSimps",
   "src/list/src/listSimps","src/pred_set/src/pred_setSimps",
   "src/boss/bossLib"]
val _ = Meta.qquse "ordinary-proofs.ML"
val _ = absent ()
val _ = print "ORDINARY_DEFAULT_LOAD_COMPLETE imports=5 proofs=3\n"
val _ = OS.Process.exit OS.Process.success
