(* Each frozen client executes in its own ordinary-only process. *)
open HolKernel testutils
fun env name = valOf (OS.Process.getEnv name)
val target = env "SIMP_LEGACY_TARGET"
val expected = valOf (Int.fromString (env "SIMP_LEGACY_CHECKS"))
val _ = load target
val _ = if !Paired.checks = expected then ()
        else raise Fail "incomplete legacy assertions"
val forbidden =
  ["TraverseExt", "Cond_rewrExt", "OpeningExt", "TravrulesExt",
   "simpExtLib", "congExtLib", "pureSimpsExt", "boolSimpsExt",
   "combinSimpsExt", "numSimpsExt", "pred_setSimpsExt", "listSimpsExt",
   "intReduceExt", "integer_wordLibExt", "realSimpsExt", "SimpTracking",
   "simpMarkerTheory", "simpMarkerSyntax",
   "simpMarkerLib", "splitLib", "SplitData", "splitPersistLib"]
val _ = List.app (fn name =>
  if List.exists (equal name) (Meta.loaded ()) orelse
     Option.isSome (#lookupStruct PolyML.globalNameSpace name)
  then raise Fail ("ordinary test loaded extension: " ^ name)
  else ()) forbidden
val _ = List.app (fn (file,dir) =>
  print ("OBS legacy.path=" ^ OS.Path.concat (dir,file) ^ "\n"))
  (Binarymap.listItems (Meta.fileDirMap ()))
val _ = print ("OBS legacy.complete=" ^ target ^ ":" ^
               Int.toString (!Paired.checks) ^ "\n")
val _ = OS.Process.exit OS.Process.success
