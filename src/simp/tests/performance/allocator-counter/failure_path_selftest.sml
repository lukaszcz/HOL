(* RTS, native and code-space FAILURE path controls, dedicated
 * Holmake/testutils launcher:  failure-path-controls.exe -H 32 --gcthreads=1
 * Use the sealed patched runtime and TASK29_ALLOC_SHIM=absolute/bracket.so.
 * The driver merges stderr into stdout, keeps the whole receipt and imposes a
 * finite process-group timeout. Synthetic unit tests are protocol tests only.
 *
 * RTS and native failure: after every closure exists and a warm full GC,
 * failure_limit.c installs a verified RLIMIT_AS of current virtual bytes +
 * 64 MiB (--maxheap alone does not fail large objects). IntInf.<< (1, 2^30
 * bits and 1.5*2^30 bits) then need 128/192 MiB of limbs and
 * Array.array (16777216, _) needs 128 MiB: Processes::FindAllocationSpace
 * returns 0 for a real RTS caller (the shift) or a real native caller (the
 * array); the runtime prints its exhaustion line and interrupts the thread.
 * We catch the Interrupt like failure_selftest.sml.
 *
 * Code failure: on AArch64 the code area is a pre-reserved 2 GiB region, so
 * RLIMIT_AS cannot fail it. PolyCopyByteVecToClosure is given a byte vector
 * larger than that region; MemMgr::AllocCodeSpace returns 0 because the
 * request exceeds the reserved region (the failure is raised before the
 * headerMap is created, so the OS limit plays no part in it). The RTS then
 * calls QuickGC; only the Fail "Insufficient memory" that follows depends on
 * the OS limit making that QuickGC fail. Were QuickGC to succeed, the RTS
 * would retry and could loop without end: the driver's process-group
 * timeout is the guard. This proves exactly one hooked failed AllocCodeSpace
 * per failed attempt. It does NOT prove that a code request succeeds after a
 * GC, and it uses one size because any request beyond the region fails the
 * same way. The vector is never copied (the request fails first) and no
 * code object is installed. Each attempt uses its own fresh closure (a
 * failed closure is locked). The vector, closures and an exception-only
 * control are created BEFORE any bracket, and so is the RTS entry
 * (rtsCallFull2 allocates code on first use): no bracket contains a
 * successful code allocation. The control calls the same RTS function with
 * a word (not byte) object, which raises Fail "Not byte data area": the
 * same-size packet through the same call, with no code-space request.
 *
 * The three object casts below (allocateWordMemory closure and word-object
 * vector, allocateByteMemory vector) mirror the compiler's own use in
 * CodeArray.ML. They are control-only and confined to this isolated
 * process: the fake closure is only ever handed to PolyCopyByteVecToClosure,
 * which overwrites it, and is never called. A real compiled closure must
 * not be used: the call would write into it.
 * Recovery is judged by exact RTS slopes and by real compiler runs whose raw
 * vectors must equal their pre-failure vectors.
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
val limitAddressSpace = Foreign.buildCall0
  (sym "task29_failure_limit", (), Foreign.cInt)
val getLimit = Foreign.buildCall1
  (sym "task29_failure_limit_get", Foreign.cInt, Foreign.cUint64Large)
fun emit kind values =
  print ("@@TASK29_PATH_" ^ kind ^ "_V1\t" ^
         String.concatWith "\t" values ^ "\n")
fun at xs i = List.nth (xs, i) : LargeInt.int
fun fields xs = map LargeInt.toString xs
fun sum xs = List.foldl (op +) (0 : LargeInt.int) xs
val _ = emit "SCOPE"
  ["rts-native-and-code-failure-paths-only; not full runtime validation"]
val _ = emit "PROFILE" ["failure"]
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
(* word bytes; RTS failed shifts (bits); native failed array words; code
 * vector words; recovery limbs *)
val _ = emit "CONFIG"
  ["8", "1073741824", "1610612736", "16777216", "335544320", "1", "128"]

(* Every root, closure, exception and vector exists BEFORE the OS limit. *)
val sentinel = Array.array (1024, 0w90 : Word.word)
val big = ref (0 : IntInf.int)
val shift = ref (0w0 : Word.word)
val noopWork = fn () => ()
val manualExn : exn = Fail "Insufficient memory"
val manualWork = fn () => raise manualExn
val rtsWork = fn () => big := IntInf.<< (1, !shift)
val compiled = ref (fn () => ())
val compileWork = fn () => let
  val input = TextIO.openString
    ("fun task29_code (n : int) = " ^
     "if n = 0 then 0 else n + task29_code (n - 1);\n")
in compiled := PolyML.compiler (fn () => TextIO.input1 input,
                                [PolyML.Compiler.CPOutStream (fn _ => ())])
end
val okSize = 1000
val nativeRoot = ref (Array.array (0, 0w0 : Word.word))
val nativeWork = fn () =>
  nativeRoot := Array.array (Word.toInt (!shift), 0wx37)
(* The RTS entry point is resolved here, outside every bracket: its first
 * use allocates code. *)
val copy : Word8Vector.vector * (unit -> unit) -> unit =
  RunCall.rtsCallFull2 "PolyCopyByteVecToClosure"
fun newClosure () : (unit -> unit) =
  RunCall.allocateWordMemory (0w1, 0wx48, 0w0)
fun newVector n : Word8Vector.vector =
  RunCall.allocateByteMemory (Word.fromInt n, 0wx41)
(* A word object where a byte vector is required: the call raises Fail
 * "Not byte data area" before it looks at the closure. *)
val wordVector : Word8Vector.vector =
  RunCall.allocateWordMemory (0w1, 0wx40, 0w0)
val codeSize = 335544320
val bigVector = newVector codeSize
fun copyWork vector = let
  val closure = newClosure ()
in fn () => ignore (copy (vector, closure)) end
val controlLabels = ["code-ctl-before-1", "code-ctl-before-2",
                     "code-ctl-limited-1", "code-ctl-limited-2"]
val failLabels = ["code-fail-" ^ Int.toString codeSize ^ "-1",
                  "code-fail-" ^ Int.toString codeSize ^ "-2"]
val codeWorks =
  map (fn l => (l, copyWork wordVector)) controlLabels @
  map (fn l => (l, copyWork bigVector)) failLabels
fun codeWork label =
  case List.find (fn (l, _) => l = label) codeWorks of
      SOME (_, work) => work
    | NONE => raise Fail ("missing code work " ^ label)

val enabled = [Thread.EnableBroadcastInterrupt true,
               Thread.InterruptState Thread.InterruptAsynchOnce]
val synchronous = [Thread.EnableBroadcastInterrupt true,
                   Thread.InterruptState Thread.InterruptSynch]
val saved = ref (Thread.getAttributes ())
val action = ref noopWork
(* 0 not run, 1 returned, 2 Interrupt, 3 Fail "Insufficient memory", 4 other *)
val outcome = ref 0
fun protectedWork () =
  (((Thread.setAttributes enabled; (!action) (); outcome := 1)
    handle Thread.Interrupt =>
             (Thread.setAttributes synchronous; outcome := 2)
         | Fail s => (Thread.setAttributes synchronous;
                      outcome :=
                        (if s = "Insufficient memory" then 3 else 4)));
   Thread.setAttributes (!saved))

val previous = ref (NONE : LargeInt.int list option)
val previousPath = ref (NONE : LargeInt.int list option)
val labels = ref ([] : string list)
fun ordered idx (a, b) = List.all (fn i => at a i <= at b i) idx
val rawIndexes = [3, 4, 5, 6, 7]
val pathIndexes = List.tabulate (28, fn i => i + 3)
fun valid xs = at xs 0 = 1 andalso at xs 1 = 8 andalso at xs 2 = 0 andalso
               at xs 3 = sum (List.drop (xs, 4))
fun pathValid xs = at xs 0 = 1 andalso at xs 1 = 8 andalso at xs 2 = 0 andalso
                   at xs 30 = 0 andalso at xs 31 = 0

fun measure label kind a b work = let
  val _ = check (label ^ " unique label")
    (not (List.exists (fn x => x = label) (!labels)))
  val _ = labels := label :: !labels
  val _ = action := work
  val _ = outcome := 0
  val _ = shift := Word.fromInt (a * b)
  val _ = saved := Thread.getAttributes ()
  val _ = big := 0
  val _ = emit "REQUEST" [label, kind, Int.toString a, Int.toString b]
  val _ = TextIO.flushOut TextIO.stdOut
  val _ = startBracket ()
  val _ = protectedWork ()
  val _ = endBracket ()
  val s = List.tabulate (8, getCall)
  val e = List.tabulate (8, fn i => getCall (8 + i))
  val ps = List.tabulate (32, getPath)
  val pe = List.tabulate (32, fn i => getPath (32 + i))
  val _ = emit "ENDPOINT" (label :: "start" :: fields s)
  val _ = emit "ENDPOINT" (label :: "end" :: fields e)
  val _ = emit "PENDPOINT" (label :: "start" :: fields ps)
  val _ = emit "PENDPOINT" (label :: "end" :: fields pe)
  val _ = check (label ^ " valid monotonic endpoints")
    (valid s andalso valid e andalso ordered rawIndexes (s, e) andalso
     pathValid ps andalso pathValid pe andalso ordered pathIndexes (ps, pe))
  val _ = case !previous of NONE => () | SOME p =>
    check (label ^ " process monotonicity") (ordered rawIndexes (p, s))
  val _ = case !previousPath of NONE => () | SOME p =>
    check (label ^ " process path monotonicity") (ordered pathIndexes (p, ps))
  val _ = previous := SOME e
  val _ = previousPath := SOME pe
  val _ = emit "RAW" (label :: fields (map (fn i => at e i - at s i)
                                           rawIndexes))
  val _ = emit "PATH" (label :: fields (map (fn i => at pe i - at ps i)
                                            pathIndexes))
  val intact = Array.length sentinel = 1024 andalso
               Array.all (fn w => w = 0w90) sentinel
  val log2 = if kind = "rts-ok" then IntInf.log2 (!big)
             else if kind = "native-ok" then Array.length (!nativeRoot)
             else 0
  val _ = emit "RESULT" [label, Int.toString (!outcome), Int.toString log2,
                         if intact then "1" else "0"]
in () end

val noops = ["noop-warmup-1", "noop-warmup-2", "noop-before-1",
             "noop-before-2"]
val manuals = ["manual-warmup-1", "manual-warmup-2", "manual-before-1",
               "manual-before-2"]
val _ = List.app (fn l => measure l "noop" 0 0 noopWork) noops
val _ = List.app (fn l => measure l "manual" 0 0 manualWork) manuals
val _ = List.app (fn l => measure l "compile" 0 0 compileWork)
  ["compile-warmup-1", "compile-before-1", "compile-before-2"]
fun control label r = measure label "code-ctl" 0 r (codeWork label)
val _ = List.app (fn r => control ("code-ctl-before-" ^ Int.toString r) r)
  [1, 2]
val _ = List.app (fn m => measure ("rts-ok-before-" ^ Int.toString m)
  "rts-ok" 64 m rtsWork) [1, 128]

(* Warm full GC, then the one-shot verified OS bound. *)
val _ = PolyML.fullGC ()
val limitStatus = limitAddressSpace ()
val _ = check "OS address-space limit applied and verified"
  (limitStatus = 1)
val limitValues = List.tabulate (4, getLimit)
val _ = emit "LIMIT" (fields (Int.toLarge limitStatus :: limitValues))
val _ = List.app (fn r => control ("code-ctl-limited-" ^ Int.toString r) r)
  [1, 2]

val rtsBits = [1073741824, 1610612736]
val nativeFail = 16777216
val _ = List.app (fn r => let
    val rs = Int.toString r
  in
    List.app (fn bits => let
        val bs = Int.toString bits
      in
        measure ("rts-fail-" ^ bs ^ "-" ^ rs) "rts-fail" 1 bits rtsWork;
        List.app (fn m => measure
          ("rts-ok-" ^ bs ^ "-" ^ rs ^ "-" ^ Int.toString m)
          "rts-ok" 64 m rtsWork) [1, 128]
      end) rtsBits;
    let val ns = Int.toString nativeFail in
      measure ("native-fail-" ^ ns ^ "-" ^ rs) "native-fail" 1 nativeFail
        nativeWork;
      measure ("native-ok-" ^ ns ^ "-" ^ rs) "native-ok" 1 okSize nativeWork
    end;
    let val ns = Int.toString codeSize in
      measure ("code-fail-" ^ ns ^ "-" ^ rs) "code-fail" codeSize r
        (codeWork ("code-fail-" ^ ns ^ "-" ^ rs));
      measure ("compile-after-" ^ ns ^ "-" ^ rs) "compile" 0 0 compileWork
    end
  end) [1, 2]
val _ = measure "compile-final" "compile" 0 0 compileWork
val _ = List.app (fn l => measure l "noop" 0 0 noopWork)
  ["noop-final-1", "noop-final-2"]
val _ = emit "THREADS" ("end" :: PathThreads.threads ())
val _ = emit "UNCLAIMED"
  ["compact32; foreign-created-thread callbacks; interpreter " ^
   "reservation failures here; code-space success after a GC; image " ^
   "lineage; TASK29B matrix"]
val _ = emit "COMPLETE" [Int.toString (length (!labels))]
val _ = TextIO.flushOut TextIO.stdOut
