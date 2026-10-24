(* Harness-only falsification of a proposed profiler-sum allocation counter.
   The C shim injects SYNTHETIC requests: these are NOT allocated HOL words.
   Never load without the driver's exact linked-libpolyml fingerprint guard. *)
open testutils
val library = Foreign.loadLibrary
  (valOf (OS.Process.getEnv "TASK29_PROFILER_SHIM"))
val inject = Foreign.buildCall2
  (Foreign.getSymbol library "task29_unknown_pc",
   (Foreign.cUint64Large,Foreign.cUint64Large),Foreign.cVoid)
val rows = ref ([] : (string * int * int) list)
fun probe (label,words,events,collect) = let
  val entries = ref ([] : (int * string) list)
  val _ = PolyML.Profiling.profileStream (fn xs => entries := xs)
    PolyML.Profiling.ProfileAllocations
    (fn () => (inject (words,events);
               if collect then PolyML.fullGC () else ())) ()
  val unknown = List.foldl (fn ((n,name),acc) =>
    if name = "UNKNOWN" then acc+n else acc) 0 (!entries)
  val total = List.foldl (fn ((n,_),acc) => acc+n) 0 (!entries)
  val _ = rows := (label,unknown,total) :: !rows
  val _ = print ("@@TASK29_PROFILER\t" ^ label ^ "\t" ^
    Int.toString unknown ^ "\t" ^ Int.toString total ^ "\n")
in unknown end
val empty = probe ("empty",0,0,false)
val small = probe ("one-word",1,1,false)
val large = probe ("million-words",1048576,1,false)
val seven = probe ("seven-events",1048576,7,false)
val collected = probe ("collected",1048576,7,true)
val reset = probe ("reset",0,0,false)
fun check label yes = (tprint label; if yes then OK () else die label)
val _ = check "empty/reset unknown counts" (empty = 0 andalso reset = 0)
val _ = check "unknown PC loses requested word count"
  (small = 1 andalso large = 1)
val _ = check "unknown PC counts events, not words" (seven = 7)
val _ = check "explicit GC does not recover lost words" (collected = 7)
val _ = check "all diagnostic cases executed" (length (!rows) = 6)
val _ = print "@@TASK29_PROFILER_COMPLETE\t6\n"
