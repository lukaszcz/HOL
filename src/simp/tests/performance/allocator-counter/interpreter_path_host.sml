(* Load Natively, AFTER RootInterpreted.ML, table initialisation and the
 * interpreted body. TASK29_PATH_HOST is supplied/sealed by the driver.
 * Never useIntoEnv here. Typed API audit as in interpreter_host.sml:
 * compiler(namespace, reader, params) returns (_, SOME code); code () is
 * run and its declaration record ignored. Entries (including preparation and
 * result printing) are all compiled before the first bracket; only the
 * native Foreign wrappers call the shim.
 *)
structure Task29PathHost =
struct
fun check label yes = if yes then () else raise Fail label
val namespace : CompilerBody.nameSpace =
  Make.gEnvAsNameSpace Task29InterpreterTable
val params : Universal.universal list =
  [Universal.tagInject Debug.maxInlineSizeTag 0]
fun entry expression = let
  val input = TextIO.openString ("val _ = " ^ expression ^ ";")
  fun reader () = TextIO.input1 input
  val code =
    (case CompilerBody.compiler (namespace, reader, params) of
         (_, SOME code) => code
       | (_, NONE) => raise Fail ("entry compilation failed: " ^ expression))
    handle ex => (TextIO.closeIn input; raise ex)
  val _ = TextIO.closeIn input
in code end
fun quoted s = "\"" ^ String.toString s ^ "\""
val shimPath = case OS.Process.getEnv "TASK29_ALLOC_SHIM" of
    SOME p => p | NONE => raise Fail "set TASK29_ALLOC_SHIM"
val library = Foreign.loadLibrary shimPath
fun sym name = Foreign.getSymbol library name
val runtimePath = Foreign.buildCall0 (sym "task29_alloc_runtime", (),
                                      Foreign.cString)
val abiCheck = Foreign.buildCall0 (sym "task29_alloc_abi_check", (),
                                   Foreign.cInt)
val startBracket = Foreign.buildCall0 (sym "task29_alloc_start", (),
                                       Foreign.cVoid)
val endBracket = Foreign.buildCall0 (sym "task29_alloc_end", (),
                                     Foreign.cVoid)
val getCall = Foreign.buildCall1 (sym "task29_alloc_get", Foreign.cInt,
                                  Foreign.cUint64Large)
val getPath = Foreign.buildCall1 (sym "task29_alloc_path_get", Foreign.cInt,
                                  Foreign.cUint64Large)
val getBranch = Foreign.buildCall1 (sym "task29_alloc_interpreter_get",
                                    Foreign.cInt, Foreign.cUint64Large)
val limitAddressSpace = Foreign.buildCall0 (sym "task29_failure_limit", (),
                                            Foreign.cInt)
val getLimit = Foreign.buildCall1 (sym "task29_failure_limit_get",
                                   Foreign.cInt, Foreign.cUint64Large)
fun at xs i = List.nth (xs, i) : LargeInt.int
fun sum xs = List.foldl (op +) (0 : LargeInt.int) xs
fun fields xs = map LargeInt.toString xs
fun emit kind values =
  print ("@@TASK29_PATH_" ^ kind ^ "_V1\t" ^
         String.concatWith "\t" values ^ "\n")
val noopE = entry "Task29Path.noop ()"
val clearE = entry "Task29Path.clear ()"
val workE = entry "Task29Path.work ()"
val attemptE = entry "Task29Path.attempt ()"
fun prepareE k s = entry ("Task29Path.prepare " ^ Int.toString k ^ " " ^
                          Int.toString s)
fun reportE label = entry ("Task29Path.report " ^ quoted label)

val labels = ref ([] : string list)
val previous = ref (NONE : LargeInt.int list option)
val previousPath = ref (NONE : LargeInt.int list option)
val previousBranch = ref (NONE : LargeInt.int list option)
fun ordered idx (a, b) = List.all (fn i => at a i <= at b i) idx
val rawIndexes = [3, 4, 5, 6, 7]
val pathIndexes = List.tabulate (28, fn i => i + 3)
val branchIndexes = [3, 4, 5, 6]
fun valid s = at s 0 = 1 andalso at s 1 = 8 andalso at s 2 = 0 andalso
              at s 3 = sum (List.drop (s, 4))
fun pathValid s = at s 0 = 1 andalso at s 1 = 8 andalso at s 2 = 0 andalso
                  at s 30 = 0 andalso at s 31 = 0
fun branchValid s = at s 0 = 1 andalso at s 1 = 8 andalso at s 2 = 0
                    andalso at s 7 = 0
fun track r v idx (a, b) what label = let
  val _ = check (label ^ " " ^ what ^ " ordered") (ordered idx (a, b))
  val _ = case !r of NONE => () | SOME p =>
    check (label ^ " " ^ what ^ " process monotonicity") (ordered idx (p, a))
in r := SOME b end

(* label, kind, a, b, unmeasured preparation, measured entry *)
fun measure (label, kind, a, b, prepare, code) = let
  val _ = check (label ^ " unique")
    (not (List.exists (fn s => s = label) (!labels)))
  val _ = labels := label :: !labels
  val _ = ignore (prepare ())
  val _ = emit "REQUEST" [label, kind, Int.toString a, Int.toString b]
  val _ = TextIO.flushOut TextIO.stdOut
  val _ = startBracket ()
  val _ = ignore (code ())
  val _ = endBracket ()
  val s = List.tabulate (8, getCall)
  val e = List.tabulate (8, fn i => getCall (8 + i))
  val ps = List.tabulate (32, getPath)
  val pe = List.tabulate (32, fn i => getPath (32 + i))
  val bs = List.tabulate (8, getBranch)
  val be = List.tabulate (8, fn i => getBranch (8 + i))
  val _ = emit "ENDPOINT" (label :: "start" :: fields s)
  val _ = emit "ENDPOINT" (label :: "end" :: fields e)
  val _ = emit "PENDPOINT" (label :: "start" :: fields ps)
  val _ = emit "PENDPOINT" (label :: "end" :: fields pe)
  val _ = emit "BENDPOINT" (label :: "start" :: fields bs)
  val _ = emit "BENDPOINT" (label :: "end" :: fields be)
  val _ = check (label ^ " valid endpoints")
    (valid s andalso valid e andalso pathValid ps andalso pathValid pe andalso
     branchValid bs andalso branchValid be)
  val _ = track previous () rawIndexes (s, e) "raw" label
  val _ = track previousPath () pathIndexes (ps, pe) "path" label
  val _ = track previousBranch () branchIndexes (bs, be) "branch" label
  val d = map (fn i => at e i - at s i) rawIndexes
  val _ = emit "RAW" (label :: fields d)
  val _ = emit "PATH" (label ::
    fields (map (fn i => at pe i - at ps i) pathIndexes))
  val _ = emit "BRANCH" (label ::
    fields (map (fn i => at be i - at bs i) branchIndexes))
  val _ = TextIO.flushOut TextIO.stdOut
  val _ = ignore ((reportE label) ())
in () end

fun noopRow label = (label, "noop", 0, 0, clearE, noopE)
fun loopRow label k s = (label, "loop", k, s, prepareE k s, workE)
fun attemptNoopRow label = (label, "attempt-noop", 0, 0, clearE, attemptE)
fun attemptRow kind label k s = (label, kind, k, s, prepareE k s, attemptE)
fun lbl xs = String.concatWith "-" xs
val loops = [(4096, 0), (4096, 1000), (32768, 1000), (1, 100000),
             (1, 200000), (64, 2097152)]
val failSizes = [16777216, 25165824]
val okSize = 1000

(* Every entry of both phases is compiled here, before any OS limit. *)
val phaseA =
  map noopRow ["noop-warmup-1", "noop-warmup-2", "noop-before-1",
               "noop-before-2"] @
  List.concat (map (fn r => map (fn (k, s) =>
    loopRow (lbl ["loop", Int.toString k, Int.toString s, Int.toString r])
            k s) loops) [1, 2])
val phaseB =
  map noopRow ["noop-limited-1", "noop-limited-2"] @
  map attemptNoopRow ["attempt-noop-1", "attempt-noop-2"] @
  map (fn r => attemptRow "ok" (lbl ["ok-before", Int.toString r])
                          1 okSize) [1, 2] @
  List.concat (map (fn r => List.concat (map (fn n =>
    [attemptRow "fail" (lbl ["fail", Int.toString n, Int.toString r]) 1 n,
     attemptRow "ok" (lbl ["recover", Int.toString n, Int.toString r])
                1 okSize]) failSizes)) [1, 2]) @
  map noopRow ["noop-final-1", "noop-final-2"] @
  [attemptNoopRow "attempt-noop-final"]

fun run () = let
  val _ = emit "SCOPE"
    ["hybrid-bytecode-path-controls-only; not full runtime validation"]
  val _ = emit "PROFILE" ["interpreter"]
  val _ = emit "RUNTIME" [runtimePath ()]
  val maps = TextIO.openIn "/proc/self/maps"
  fun emitMaps () = case TextIO.inputLine maps of NONE => () | SOME line =>
    (print ("@@TASK29_PATH_MAP_V1\t" ^ line); emitMaps ())
  val _ = emitMaps ()
  val _ = TextIO.closeIn maps
  val _ = emit "THREADS" ("start" :: PathThreads.threads ())
  val abi = abiCheck ()
  val _ = emit "ABI" [Int.toString abi]
  val _ = check "native C ABI controls for interpreted path entries"
    (abi = 15)
  (* bytes/word, repeats, two failed sizes (words), recovery size *)
  val _ = emit "CONFIG" ["8", "2", "16777216", "25165824", "1000"]
  val _ = List.app measure phaseA
  (* Warm full GC, then the one-shot verified OS bound (all closures exist). *)
  val _ = PolyML.fullGC ()
  val status = limitAddressSpace ()
  val limit = List.tabulate (4, getLimit)
  val _ = emit "LIMIT" (fields (Int.toLarge status :: limit))
  val _ = check "OS address-space limit applied and verified" (status = 1)
  val _ = List.app measure phaseB
  val _ = emit "THREADS" ("end" :: PathThreads.threads ())
  val _ = emit "UNCLAIMED"
    ["compact32; foreign-created-thread callbacks; pure-interpreter runtime; "
     ^ "code-space failures here; image lineage; TASK29B matrix"]
  val _ = emit "COMPLETE" [Int.toString (length (!labels))]
  val _ = TextIO.flushOut TextIO.stdOut
in () end
end;
val _ = Task29PathHost.run ();
