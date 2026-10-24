(* Load Natively, AFTER RootInterpreted.ML, table initialisation and body.
 * TASK29_ALLOC_HOST is supplied/sealed by the driver. Never useIntoEnv here.
 *
 * Typed API audit: MLCompiler/COMPILERBODYSIG.sml and MAKE_.ML,
 * compileIntoEnv: compiler(namespace, reader, params) returns (_, SOME code);
 * code() returns {fixes, values, structures, signatures, functors, types}.
 * We ignore that record, with NO declaration installation and NO casts.
 * The native executeCode/pass4Structs successful-result packaging is a fixed
 * part of each raw bracket, not subtracted or called interpreted allocation.
 * ALL entries (including preparation/verification) are compiled before run.
 * Only native Foreign wrappers call the shim; the body is pure bytecode SML.
 *)
structure Task29InterpreterHost =
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
val noopEntry = entry "Task29Interpreter.noop ()"
val workEntry = entry "Task29Interpreter.work ()"
val gcEntry = entry "Task29Interpreter.gcWork ()"
fun quoted s = "\"" ^ String.toString s ^ "\""
fun plan kind label n = let
  val suffix = if kind = "refs" then "Refs" else "Words"
  val prepare = entry ("Task29Interpreter.prepare" ^ suffix ^ " " ^
                       Int.toString n)
  val verify = entry ("Task29Interpreter.verify" ^ suffix ^ " " ^
                      quoted label ^ " " ^ Int.toString n)
in (label, n, prepare, verify) end
fun plans kind = let
  val warmup = map (fn repeat =>
    plan kind (kind ^ "-warmup-" ^ repeat) 0) ["1", "2"]
  fun round repeat = map (fn n =>
    plan kind (kind ^ "-" ^ Int.toString n ^ "-" ^ repeat) n) [0, 1, 16, 32]
in (warmup, round "1", round "2") end
val refsPlans = plans "refs"
val wordsPlans = plans "words"
val verifyLiveRefs =
  entry "Task29Interpreter.verifyRefs \"after-live-gc\" 32"
val verifyLiveWords =
  entry "Task29Interpreter.verifyWords \"after-live-gc\" 32"

val shimPath = case OS.Process.getEnv "TASK29_ALLOC_SHIM" of
    SOME p => p | NONE => raise Fail "set TASK29_ALLOC_SHIM"
val library = Foreign.loadLibrary shimPath
val runtimePath = Foreign.buildCall0
  (Foreign.getSymbol library "task29_alloc_runtime", (), Foreign.cString)
val abiCheck = Foreign.buildCall0
  (Foreign.getSymbol library "task29_alloc_abi_check", (), Foreign.cInt)
val startBracket = Foreign.buildCall0
  (Foreign.getSymbol library "task29_alloc_start", (), Foreign.cVoid)
val endBracket = Foreign.buildCall0
  (Foreign.getSymbol library "task29_alloc_end", (), Foreign.cVoid)
val getCall = Foreign.buildCall1
  (Foreign.getSymbol library "task29_alloc_get",
   Foreign.cInt, Foreign.cUint64Large)
val labels = ref ([] : string list)
val previous = ref (NONE : LargeInt.int list option)
val indexes = [3, 4, 5, 6, 7]
fun at xs i = List.nth (xs, i) : LargeInt.int
fun sum xs = List.foldl (op +) (0 : LargeInt.int) xs
fun fields xs = String.concatWith "\t" (map LargeInt.toString xs)
fun emit kind values =
  print ("@@TASK29_INTERPRETER_" ^ kind ^ "_V1\t" ^
         String.concatWith "\t" values ^ "\n")
fun ordered (a, b) = List.all (fn i => at a i <= at b i) indexes
fun valid s = at s 0 = 1 andalso at s 1 = 8 andalso at s 2 = 0 andalso
              at s 3 = sum (List.drop (s, 4))
fun endpoint label side s = emit "ENDPOINT" [label, side, fields s]
fun measure label code = let
  val _ = check (label ^ " unique")
    (not (List.exists (fn s => s = label) (!labels)))
  val _ = labels := label :: !labels
  (* Native endpoints around the PRECOMPILED declaration-entry call only.
   * Keep the native successful-result record packaging in the raw counts.
   * No compiler, environment entry, preparation, inspection or formatting.
   *)
  val _ = startBracket ()
  val _ = ignore (code ())
  val _ = endBracket ()
  val a = List.tabulate (8, getCall)
  val b = List.tabulate (8, fn i => getCall (8 + i))
  val d = map (fn i => at b i - at a i) indexes
  val _ = endpoint label "start" a
  val _ = endpoint label "end" b
  val _ = emit "RAW" [label, fields d]
  val _ = check (label ^ " ABI/sum/monotonicity")
    (valid a andalso valid b andalso ordered (a, b) andalso
     hd d = sum (tl d))
  val _ = case !previous of NONE => () | SOME p =>
    check (label ^ " process monotonicity") (ordered (p, a))
  val _ = previous := SOME b
in d end
fun workRound kind (label, n, prepare, verify) = let
  val _ = ignore (prepare ())
  val d = measure label workEntry
  val physical = if kind = "refs" then 5 * n else 1 + n
  val _ = check (label ^ " covers physical interpreted storage")
    (at d 3 >= Int.toLarge physical)
  val _ = ignore (verify ())
in d end
fun exact label zero d (words : LargeInt.int) =
  check label (ListPair.mapEq (op -) (d, zero) =
               [words, 0, 0, words, 0])
fun series kind (warmup, firstPlans, secondPlans) = let
  val _ = List.app (fn p => ignore (workRound kind p)) warmup
  val first = map (workRound kind) firstPlans
  val second = map (workRound kind) secondPlans
  val zero = hd first
  val factor = if kind = "refs" then 5 else 1
  val _ = List.app (fn (n, d) =>
    exact (kind ^ " exact INTERPRETER slope " ^ Int.toString n)
      zero d (Int.toLarge (factor * n)))
    (ListPair.zip ([0, 1, 16, 32], first))
  val _ = exact (kind ^ " exact doubling slope")
    (List.nth (first, 2)) (List.nth (first, 3))
    (Int.toLarge (factor * 16))
  (* Full vectors include native packaging: total AND native overhead must
   * repeat, as must RTS/interpreter/code. Never subtract a no-op baseline.
   *)
  val _ = check (kind ^ " all categories repeat exactly") (first = second)
in () end
fun run () = let
  val _ = emit "SCOPE"
    ["hybrid-bytecode-controls-only; not full runtime validation"]
  val _ = emit "BOOTSTRAP" ["RootInterpreted.ML", "Make.makeGEnv",
    "Initialise.initGlobalEnv:false", "mlsource/BuildBasis.sml"]
  val _ = emit "RUNTIME" [runtimePath ()]
  val maps = TextIO.openIn "/proc/self/maps"
  fun emitMaps () = case TextIO.inputLine maps of NONE => () | SOME line =>
    (print ("@@TASK29_INTERPRETER_MAP_V1\t" ^ line); emitMaps ())
  val _ = emitMaps ()
  val _ = TextIO.closeIn maps
  val abi = abiCheck ()
  val _ = emit "ABI" [Int.toString abi]
  val _ = check "native C ABI controls for interpreted entries" (abi = 15)
  (* bytes/word, repetitions, sizes, words/ref+cons, array header words *)
  val _ = emit "CONFIG" ["8", "2", "0", "1", "16", "32", "5", "1"]
  val _ = measure "noop-warmup-1" noopEntry
  val _ = measure "noop-warmup-2" noopEntry
  val idle = measure "noop-before-1" noopEntry
  val idle2 = measure "noop-before-2" noopEntry
  val _ = check "entry no-op total/native/category costs repeat" (idle = idle2)
  val _ = measure "gc-warmup" gcEntry
  val gc = measure "gc-empty-1" gcEntry
  val gc2 = measure "gc-empty-2" gcEntry
  val _ = check "interpreted GC entry costs repeat" (gc = gc2)
  val _ = series "refs" refsPlans
  val _ = series "words" wordsPlans
  val live1 = measure "gc-live-1" gcEntry
  val live2 = measure "gc-live-2" gcEntry
  val _ = ignore (verifyLiveRefs ())
  val _ = ignore (verifyLiveWords ())
  val _ = check "GC never recounts retained interpreted objects"
    (gc = live1 andalso gc = live2)
  val final1 = measure "noop-final-1" noopEntry
  val final2 = measure "noop-final-2" noopEntry
  val _ = check "entry no-op total/native costs stable after work/GC"
    (idle = final1 andalso idle = final2)
  val _ = emit "UNCLAIMED"
    ["compact32; pure-interpreter runtime; threads; failed allocations; " ^
     "overflow injection; image lineage; full runtime completeness; " ^
     "TASK29B matrix"]
  val _ = emit "COMPLETE" [Int.toString (length (!labels))]
in () end
end;
val _ = Task29InterpreterHost.run ();
