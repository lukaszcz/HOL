(* Lower-level SUCCESS path controls for native and RTS reservations. Dedicated
 * Holmake/testutils launcher, not the main controls process:
 *   path-controls.exe --gcthreads=1
 * Use the sealed patched runtime and TASK29_ALLOC_SHIM=absolute/bracket.so.
 * The driver merges stderr into stdout, keeps the whole receipt and imposes a
 * finite process-group timeout.
 *
 * Loops of known-size allocations are far larger than one heap segment and
 * than the minor-GC threshold, so the segment-refill and success-after-GC
 * branches of Processes::FindAllocationSpace execute many times. The path
 * diagnostic ABI observes which branch actually ran; request sizes are never
 * used to infer that. Exact word counts must not depend on the branch
 * schedule, which legitimately differs between rounds.
 * Native: Array.array of s words reserves exactly s+1 words.
 * RTS: IntInf.<< (1, 64*m) is PolyShiftLeftArbitrary, which reserves exactly
 * m+2 words through alloc. Results are retained and consumed after brackets.
 * No unsafe casts, counter writes or synthetic allocations.
 *)
open testutils

fun check label yes = (tprint label; if yes then OK () else die label)
val shimPath =
  case OS.Process.getEnv "TASK29_ALLOC_SHIM" of
      SOME p => if OS.Path.isAbsolute p then p
                else raise Fail "TASK29_ALLOC_SHIM must be absolute"
    | NONE => raise Fail "set TASK29_ALLOC_SHIM"
val library = Foreign.loadLibrary shimPath
fun sym name = Foreign.getSymbol library name
val runtimePath = Foreign.buildCall0
  (sym "task29_alloc_runtime", (), Foreign.cString)
val abiCheck = Foreign.buildCall0
  (sym "task29_alloc_abi_check", (), Foreign.cInt)
val startBracket = Foreign.buildCall0
  (sym "task29_alloc_start", (), Foreign.cVoid)
val endBracket = Foreign.buildCall0
  (sym "task29_alloc_end", (), Foreign.cVoid)
val getCall = Foreign.buildCall1
  (sym "task29_alloc_get", Foreign.cInt, Foreign.cUint64Large)
val getPath = Foreign.buildCall1
  (sym "task29_alloc_path_get", Foreign.cInt, Foreign.cUint64Large)
fun emit kind values =
  print ("@@TASK29_PATH_" ^ kind ^ "_V1\t" ^
         String.concatWith "\t" values ^ "\n")
val _ = emit "SCOPE"
  ["lower-level-success-paths-only; not full runtime validation"]
val _ = emit "PROFILE" ["native-rts"]
val _ = emit "RUNTIME" [runtimePath ()]
val maps = TextIO.openIn "/proc/self/maps"
fun emitMaps () = case TextIO.inputLine maps of
    NONE => ()
  | SOME line => (print ("@@TASK29_PATH_MAP_V1\t" ^ line); emitMaps ())
val _ = emitMaps ()
val _ = TextIO.closeIn maps
val _ = emit "THREADS" ("start" :: PathThreads.threads ())
val abi = abiCheck ()
val _ = emit "ABI" [Int.toString abi]
val _ = check "original, interpreter and path C ABI controls" (abi = 15)
(* word bytes; native iterations small/large, native words; RTS iterations,
 * small/large limbs; large-object iterations small/large, large limbs.
 *)
val _ = emit "CONFIG"
  ["8", "4096", "32768", "1024", "262144", "1", "101", "8", "64", "1048576"]

(* Every root, closure and exception value exists BEFORE measurement. *)
val sentinel = Array.array (1024, 0w90 : Word.word)
val count = ref 0
val size = ref 0
val shift = ref (0w0 : Word.word)
val arr = ref sentinel
val big = ref (0 : IntInf.int)
val noopWork = fn () => ()
val nativeWork = fn () => let
  fun go i = if i = 0 then ()
             else (arr := Array.array (!size, 0wx25); go (i - 1))
in go (!count) end
val rtsWork = fn () => let
  fun go i = if i = 0 then ()
             else (big := IntInf.<< (1, !shift); go (i - 1))
in go (!count) end
val action = ref noopWork
val noWork = ref true

fun at xs i = List.nth (xs, i) : LargeInt.int
fun fields xs = map LargeInt.toString xs
fun sum xs = List.foldl (op +) (0 : LargeInt.int) xs
val indexes = [3, 4, 5, 6, 7]
val previous = ref (NONE : LargeInt.int list option)
val previousPath = ref (NONE : LargeInt.int list option)
val labels = ref ([] : string list)
fun ordered idx (a, b) = List.all (fn i => at a i <= at b i) idx
fun valid xs =
  at xs 0 = 1 andalso at xs 1 = 8 andalso at xs 2 = 0 andalso
  at xs 3 = sum (List.drop (xs, 4))
fun pathValid xs = at xs 0 = 1 andalso at xs 1 = 8 andalso at xs 2 = 0 andalso
  List.all (fn i => at xs i = 0) [30, 31]
val pathIndexes = List.tabulate (28, fn i => i + 3)
fun bit b = if b then "1" else "0"

fun measure label kind k s work = let
  val _ = check (label ^ " unique label")
    (not (List.exists (fn x => x = label) (!labels)))
  val _ = labels := label :: !labels
  val _ = action := work
  val _ = count := k
  val _ = size := s
  val _ = shift := Word.fromInt (64 * s)
  val _ = arr := sentinel
  val _ = big := 0
  val _ = emit "REQUEST" [label, kind, Int.toString k, Int.toString s]
  val _ = TextIO.flushOut TextIO.stdOut
  val _ = startBracket ()
  val _ = (!action) ()
  val _ = endBracket ()
  val a = List.tabulate (8, getCall)
  val b = List.tabulate (8, fn i => getCall (8 + i))
  val pa = List.tabulate (32, getPath)
  val pb = List.tabulate (32, fn i => getPath (32 + i))
  val _ = emit "ENDPOINT" (label :: "start" :: fields a)
  val _ = emit "ENDPOINT" (label :: "end" :: fields b)
  val _ = emit "PENDPOINT" (label :: "start" :: fields pa)
  val _ = emit "PENDPOINT" (label :: "end" :: fields pb)
  val _ = check (label ^ " valid monotonic endpoints")
    (valid a andalso valid b andalso ordered indexes (a, b) andalso
     pathValid pa andalso pathValid pb andalso
     ordered pathIndexes (pa, pb))
  val _ = case !previous of NONE => () | SOME p =>
    check (label ^ " process monotonicity") (ordered indexes (p, a))
  val _ = case !previousPath of NONE => () | SOME p =>
    check (label ^ " process path monotonicity") (ordered pathIndexes (p, pa))
  val _ = previous := SOME b
  val _ = previousPath := SOME pb
  val _ = emit "RAW" (label :: fields (map (fn i => at b i - at a i) indexes))
  val _ = emit "PATH"
    (label :: fields (map (fn i => at pb i - at pa i) pathIndexes))
  (* Retained results are consumed only now, outside the bracket. *)
  val (x, y) =
    if kind = "native" then
      (Array.length (!arr),
       bit (Array.all (fn w => w = 0wx25) (!arr)))
    else if kind = "rts" orelse kind = "large" then
      (IntInf.log2 (!big), bit (!big = IntInf.<< (1, !shift)))
    else (0, "1")
  val intact = Array.length sentinel = 1024 andalso
               Array.all (fn w => w = 0w90) sentinel
  val _ = emit "RESULT" [label, "1", Int.toString x, y, bit intact]
in () end

fun series kind first second =
  List.app (fn (label, k, s) => measure label kind k s
    (if kind = "native" then nativeWork else rtsWork)) (first @ second)

val _ = measure "noop-warmup-1" "noop" 0 0 noopWork
val _ = measure "noop-warmup-2" "noop" 0 0 noopWork
val _ = measure "noop-before-1" "noop" 0 0 noopWork
val _ = measure "noop-before-2" "noop" 0 0 noopWork
fun round kind name sizes ks r = map (fn (k, s) =>
  (kind ^ "-" ^ Int.toString k ^ "-" ^ Int.toString s ^ "-" ^ r, k, s))
  (List.concat (map (fn k => map (fn s => (k, s)) sizes) ks))
val _ = List.app (fn r => series "native" (round "native" "" [0, 1024]
  [4096, 32768] r) []) ["1", "2"]
val _ = List.app (fn r => series "rts" (round "rts" "" [1, 101]
  [262144] r) []) ["1", "2"]
val _ = List.app (fn r => series "large" (round "large" "" [1048576]
  [8, 64] r) []) ["1", "2"]
val _ = measure "noop-final-1" "noop" 0 0 noopWork
val _ = measure "noop-final-2" "noop" 0 0 noopWork
val _ = emit "THREADS" ("end" :: PathThreads.threads ())
val _ = emit "UNCLAIMED"
  ["compact32; foreign-created-thread callbacks; image lineage; " ^
   "failure paths; code-space reuse; TASK29B matrix"]
val _ = emit "COMPLETE" [Int.toString (length (!labels))]
val _ = TextIO.flushOut TextIO.stdOut
