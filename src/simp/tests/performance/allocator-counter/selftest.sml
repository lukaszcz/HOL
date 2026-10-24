(* Executed-control fixture for the EXPERIMENTAL managed allocator counter.
 * This is not a completeness/provenance test or TASK29B acceptance.  Run only
 * with the sealed patched Linux/aarch64 runtime also linked by bracket.so.
 * This fixture deliberately requires 8-byte PolyWords; compact32 is untested.
 * Use the Holmake-built launcher, not input piped into bin/hol.
 *)
open testutils

fun check label yes = (tprint label; if yes then OK () else die label)
val shimPath =
  case OS.Process.getEnv "TASK29_ALLOC_SHIM" of
      SOME p => p
    | NONE => raise Fail "set TASK29_ALLOC_SHIM to the absolute bracket.so"
val library = Foreign.loadLibrary shimPath
val runtimePath = Foreign.buildCall0
  (Foreign.getSymbol library "task29_alloc_runtime", (), Foreign.cString)
val abiCheck = Foreign.buildCall0
  (Foreign.getSymbol library "task29_alloc_abi_check", (), Foreign.cInt)
val _ = print ("@@TASK29_ALLOC_RUNTIME_V1\t" ^ runtimePath () ^ "\n")
val maps = TextIO.openIn "/proc/self/maps"
fun emitMaps () = case TextIO.inputLine maps of
    NONE => ()
  | SOME line => (print ("@@TASK29_ALLOC_MAP_V1\t" ^ line); emitMaps ())
val _ = emitMaps ()
val _ = TextIO.closeIn maps
val abi = abiCheck ()
val _ = check "C ABI null/short/unaligned/no-allocation controls" (abi = 15)
val _ = print ("@@TASK29_ALLOC_ABI_V1\t" ^ Int.toString abi ^ "\n")

(* Build ALL foreign closures before any bracket.  Start/end are no-argument
 * cVoid calls; no tuple, pointer or uint64 conversion at either boundary.
 * The remaining return/entry-glue cost is measured, not assumed zero.
 *)
val startCall = Foreign.buildCall0
  (Foreign.getSymbol library "task29_alloc_start", (), Foreign.cVoid)
val endCall = Foreign.buildCall0
  (Foreign.getSymbol library "task29_alloc_end", (), Foreign.cVoid)
val getCall = Foreign.buildCall1
  (Foreign.getSymbol library "task29_alloc_get",
   Foreign.cInt, Foreign.cUint64Large)
val startBracket = fn () => startCall ()
val endBracket = fn () => endCall ()

(* Preexisting mutable roots prevent constant folding and make results escape.
 * Reuse the SAME allocating closure for empty/small/large controls: compiler
 * allocation grouping and any fixed per-call reservation then remain visible
 * as raw overhead, rather than being guessed from final object graph size.
 *)
val action = ref (fn () => ())
val arraySize = ref 0
val arrayResult = ref (Array.array (0, 0))
val byteSize = ref 0
val byteResult = ref (Word8Array.array (0, 0w0))
val refCount = ref 0
val refResult = ref ([] : int ref list)
val bigInput = ref (IntInf.<< (1, 0w8192) + 17)
val bigResult = ref (0 : IntInf.int)
val compiledResult = ref (fn () => ())
val compileInput = TextIO.openString
  ("fun task29_alloc_code_control (n : int) = " ^
   "if n = 0 then 0 else n + task29_alloc_code_control (n - 1);\n")
val compileRead = fn () => TextIO.input1 compileInput
val compileOptions = [PolyML.Compiler.CPOutStream (fn _ => ())]
val noopWork = fn () => ()
val arrayWork = fn () => arrayResult := Array.array (!arraySize, 37)
val byteWork = fn () => byteResult := Word8Array.array (!byteSize, 0wx5a)
fun makeRefs n = let
  fun loop left acc =
    if left = 0 then acc else loop (left - 1) (ref left :: acc)
in loop n [] end
val refWork = fn () => refResult := makeRefs (!refCount)
val bigWork = fn () => bigResult := !bigInput * !bigInput
val gcWork = fn () => PolyML.fullGC ()
(* Retain the compiler's executable entry closure, without installing its
 * declaration in HOL's namespace.  This tests code-path positivity only.
 *)
val compileWork = fn () =>
  compiledResult := PolyML.compiler (compileRead, compileOptions)

fun at xs i = List.nth (xs, i) : LargeInt.int
fun total xs = at xs 0
fun sum xs = List.foldl (op +) (0 : LargeInt.int) xs
fun fields xs = String.concatWith "\t" (map LargeInt.toString xs)
val countIndexes = [3, 4, 5, 6, 7]
val lastEnd = ref (NONE : LargeInt.int list option)
val labels = ref ([] : string list)
fun ordered (a, b) =
  List.all (fn i => at a i <= at b i) countIndexes
fun valid label s =
  (check (label ^ " ABI=1, word bytes=8, overflow=0")
     (at s 0 = 1 andalso at s 1 = 8 andalso at s 2 = 0);
   check (label ^ " total equals category sum")
     (at s 3 = sum (List.drop (s, 4))))
fun endpoint label side s =
  print ("@@TASK29_ALLOC_ENDPOINT_V1\t" ^ label ^ "\t" ^ side ^
         "\t" ^ fields s ^ "\n")

(* No decoding, formatting, assertions, label work or result tuple construction
 * between start/end.  The indirect action call prevents specializing the
 * measuring function to a particular allocating operation.  The only values
 * returned by boundary calls and by work are unit.
 *)
fun measure label work = let
  val _ = check (label ^ " unique record label")
    (not (List.exists (fn s => s = label) (!labels)))
  val _ = labels := label :: !labels
  val _ = action := work
  val _ = startBracket ()
  val _ = (!action) ()
  val _ = endBracket ()
  (* C storage is now frozen until the next start.  Getter result conversion,
   * snapshot lists, and all following output are outside the bracket.
   *)
  val a = List.tabulate (8, getCall)
  val b = List.tabulate (8, fn i => getCall (8 + i))
  val _ = endpoint label "start" a
  val _ = endpoint label "end" b
  val _ = valid (label ^ " start") a
  val _ = valid (label ^ " end") b
  val _ = check (label ^ " endpoint monotonicity") (ordered (a, b))
  val _ = case !lastEnd of
      NONE => ()
    | SOME prev => check (label ^ " process monotonicity")
        (ordered (prev, a))
  val _ = lastEnd := SOME b
  val d = map (fn i => at b i - at a i) countIndexes
  val _ = print ("@@TASK29_ALLOC_DELTA_V1\t" ^ label ^ "\t" ^
                 fields d ^ "\n")
  val _ = check (label ^ " delta total equals category sum")
    (total d = sum (tl d))
in d end

(* Every endpoint record contains, in ABI order: version, word bytes, overflow,
 * total, native, RTS, interpreter, code.  Delta records contain the last five.
 * IntInf/LargeInt arithmetic avoids host overflow on subtraction/byte scaling.
 *)
val _ = print
  "@@TASK29_ALLOC_SCOPE_V1\tcontrols-only; not full runtime validation\n"
val _ = measure "noop-warmup-1" noopWork
val _ = measure "noop-warmup-2" noopWork
val idle = measure "noop-baseline" noopWork
val idle2 = measure "noop-repeat-1" noopWork
val idle3 = measure "noop-repeat-2" noopWork
val _ = check "no-op category deltas repeat exactly"
  (idle = idle2 andalso idle = idle3)
val _ = print ("@@TASK29_ALLOC_NOOP_V1\t" ^ fields idle ^ "\n")

(* Warm GC before fixing the GC-wrapper baseline.  This does not assume the
 * FFI or fullGC wrapper is allocation-free.  Equality below is deliberately
 * strict: unexplained activity fails the control instead of being subtracted
 * as a convenient tolerance.  Run without allocating background ML threads.
 *)
val _ = measure "gc-warmup" gcWork
val gcEmpty = measure "gc-before-retained" gcWork
val gcEmpty2 = measure "gc-before-retained-repeat" gcWork
val _ = check "full-GC wrapper baseline repeats" (gcEmpty = gcEmpty2)

(* Eight-byte target layouts from the pinned basis sources:
 * Array: header 1 + n payload words.
 * Word8Array: byte-storage header 1 + ceil(n/8) payload words, plus the
 * three-word Array(length, storage) descriptor.  No string length word.
 * Ref list: each retained ref is 2 words and each cons is 3, hence 5*n.
 * Compiler grouping can add a fixed call/terminal-iteration reservation.
 * Publish observed - physical layout, WITHOUT calling it calibrated truth.
 * Exact tests use differences from the SAME closure's zero-size execution.
 *)
fun layout label n physical observed = let
  val residual = total observed - physical
  val _ = print ("@@TASK29_ALLOC_LAYOUT_V1\t" ^ label ^ "\t" ^
    Int.toString n ^ "\t" ^ LargeInt.toString physical ^ "\t" ^
    LargeInt.toString (total observed) ^ "\t" ^
    LargeInt.toString residual ^ "\t" ^
    LargeInt.toString (8 * total observed) ^ "\n")
in check (label ^ " covers physical storage") (residual >= 0) end
(* Layout columns: label, elements/bytes/count, physical words, raw total
 * words, raw overhead words, raw total bytes.  Raw endpoints take precedence.
 *)
fun wordArray n = let
  val label = "word-array-" ^ Int.toString n
  val _ = arraySize := n
  val d = measure label arrayWork
  val _ = check (label ^ " retained length/content")
    (Array.length (!arrayResult) = n andalso
     (n = 0 orelse
      (Array.sub (!arrayResult, 0) = 37 andalso
       Array.sub (!arrayResult, n - 1) = 37)))
  val _ = layout label n (1 + Int.toLarge n) d
in d end
fun byteArray n = let
  val label = "byte-array-" ^ Int.toString n
  val _ = byteSize := n
  val d = measure label byteWork
  val _ = check (label ^ " retained length/content")
    (Word8Array.length (!byteResult) = n andalso
     (n = 0 orelse
      (Word8Array.sub (!byteResult, 0) = 0wx5a andalso
       Word8Array.sub (!byteResult, n - 1) = 0wx5a)))
  val _ = layout label n (4 + Int.toLarge ((n + 7) div 8)) d
in d end
fun refs n = let
  val label = "ref-list-" ^ Int.toString n
  val _ = refCount := n
  val d = measure label refWork
  val _ = check (label ^ " retained refs/content")
    (length (!refResult) = n andalso
     List.all (fn (r, i) => !r = i)
       (ListPair.zip (!refResult, List.tabulate (n, fn i => i + 1))))
  val _ = layout label n (5 * Int.toLarge n) d
in d end
fun exactDifference label zero d words =
  check label (total d - total zero = words)

val array0 = wordArray 0
fun testWord n = let
  val d = wordArray n
in exactDifference ("word array exact storage slope " ^ Int.toString n)
     array0 d (Int.toLarge n)
end
val _ = List.app testWord [1, 2, 127, 1024, 1048576]
(* The large array remains rooted in arrayResult throughout both GCs. *)
val bytes0 = byteArray 0
fun testBytes n = let
  val d = byteArray n
in exactDifference ("byte array exact rounded storage slope " ^ Int.toString n)
     bytes0 d (Int.toLarge ((n + 7) div 8))
end
val _ = List.app testBytes [1, 7, 8, 9, 15, 16, 17, 8192, 8388608]

val refs0 = refs 0
val refs1 = refs 1
val refs256 = refs 256
val refs512 = refs 512
val _ = exactDifference "one escaping ref/cons storage" refs0 refs1 5
val _ = exactDifference "256 escaping ref/cons storage" refs0 refs256 1280
val _ = exactDifference "512 escaping ref/cons storage" refs0 refs512 2560
val _ = exactDifference "ref count doubling has exact slope"
  refs256 refs512 1280
val _ = check "escaping ref list exercises native allocator"
  (at refs512 1 > at refs0 1)

val runtime = measure "rts-bignum-multiply" bigWork
val _ = check "bignum escaped and has expected result"
  (!bigResult = !bigInput * !bigInput)
val _ = check "bignum exercises RTS allocator" (at runtime 2 > at idle 2)

val gcLive1 = measure "gc-with-retained-arrays-1" gcWork
val gcLive2 = measure "gc-with-retained-arrays-2" gcWork
val _ = check "large retained objects remain live after full GC"
  (Array.length (!arrayResult) = 1048576 andalso
   Array.sub (!arrayResult, 1048575) = 37 andalso
   Word8Array.length (!byteResult) = 8388608 andalso
   Word8Array.sub (!byteResult, 8388607) = 0wx5a andalso
   length (!refResult) = 512)
val _ = check "full GC does not charge retained-data copying"
  (gcLive1 = gcEmpty andalso gcLive2 = gcEmpty)

val code = measure "compile-retained-entry-closure" compileWork
val _ = TextIO.closeIn compileInput
val _ = check "compilation exercises code-space allocation"
  (at code 4 > at idle 4)
(* No invocation of compiledResult: keeping the entry closure reachable is
 * sufficient here.  No exact code-size/alignment or interpreter claim.
 *)
val idleLast1 = measure "noop-final-1" noopWork
val idleLast2 = measure "noop-final-2" noopWork
val _ = check "no-op remains stable after allocation/GC/compiler controls"
  (idleLast1 = idle andalso idleLast2 = idle)
val _ = print
  ("@@TASK29_ALLOC_UNCLAIMED_V1\tcompact32; interpreter paths; threads; " ^
   "foreign-thread callbacks; failed allocations; saturation/overflow " ^
   "injection; image import/export; exact " ^
   "code alignment/refill; allocator slow-path coverage; " ^
   "prebuilt compiler/image lineage; " ^
   "full runtime completeness; TASK29B matrix\n")
val _ = print ("@@TASK29_ALLOC_CONTROLS_COMPLETE_V1\t" ^
               Int.toString (length (!labels)) ^ "\n")
