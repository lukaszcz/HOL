(* Actual failed NATIVE reservations only; not RTS/interpreter/code failures.
 * Dedicated Holmake/testutils launcher, NOT the main controls process:
 *   failure-controls.exe -H 32 --maxheap=96 --gcthreads=1
 * Use the sealed patched runtime and TASK29_ALLOC_SHIM=absolute/bracket.so.
 * The driver MUST merge stderr into stdout, preserve the entire receipt,
 * impose a finite process-group timeout, and reject timeouts/nonzero exits.
 * This fixture must fit the small initial heap: hol.state0, not hol.state.
 * Never increase the cap/initial heap to accommodate a failed startup.
 * --maxheap=96 is only a soft heap cap: AllocHeapSpace permits oversized
 * objects. The real failure guard is failure_limit.c in the SAME bracket.so:
 * RLIMIT_AS = current virtual bytes + 64 MiB, installed after warm fullGC.
 * The 128/192 MiB payloads exceed that incremental OS address-space budget;
 * this dedicated process's existing heap data must remain below 64 MiB.
 *
 * Read-only audit: pinned polyml-5.9.2-2/src:
 * basis/Array.sml:68-75: legal dynamic lengths use allocateWordMemory;
 * libpolyml/arm64.cpp:SetMemRegisters: a null reservation clears allocWords;
 * libpolyml/processes.cpp:FindAllocationSpace: failed QuickGC prints
 * "Run out of store - interrupting threads", broadcasts, then processes
 * ASYNCHRONOUS requests. Synch/Defer cannot recover at this point.
 * ProcessAsynchRequests uses a PREBUILT Interrupt packet and changes
 * AsynchOnce to Synch before delivery. basis/Thread.sml:setAttributes can
 * deliver an already pending interrupt immediately. Therefore the handler
 * surrounds BOTH setAttributes and the action; an interrupt before entry
 * is caught for cleanup but REJECTED, not mistaken for allocation failure.
 * HOL exports Thread=PolyThread.Thread, so use Thread.Interrupt directly.
 * No unsafe casts, counter writes, compiler invocation, or synthetic OOM.
 *)
open testutils

fun check label yes = (tprint label; if yes then OK () else die label)
val shimPath =
  case OS.Process.getEnv "TASK29_ALLOC_SHIM" of
      SOME p => if OS.Path.isAbsolute p then p
                else raise Fail "TASK29_ALLOC_SHIM must be absolute"
    | NONE => raise Fail "set TASK29_ALLOC_SHIM"
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
val limitAddressSpace = Foreign.buildCall0
  (Foreign.getSymbol library "task29_failure_limit", (), Foreign.cInt)
val getLimit = Foreign.buildCall1
  (Foreign.getSymbol library "task29_failure_limit_get",
   Foreign.cInt, Foreign.cUint64Large)
val _ = print
  ("@@TASK29_FAILURE_SCOPE_V1\tfailed-native-reservations-only; " ^
   "not full runtime validation\n")
val _ = print ("@@TASK29_FAILURE_RUNTIME_V1\t" ^ runtimePath () ^ "\n")
val maps = TextIO.openIn "/proc/self/maps"
fun emitMaps () = case TextIO.inputLine maps of
    NONE => ()
  | SOME line => (print ("@@TASK29_FAILURE_MAP_V1\t" ^ line); emitMaps ())
val _ = emitMaps ()
val _ = TextIO.closeIn maps
val abi = abiCheck ()
val _ = print ("@@TASK29_FAILURE_ABI_V1\t" ^ Int.toString abi ^ "\n")
val _ = check "failure C ABI controls" (abi = 15)
(* word bytes, initial/cap MiB, repeats, two dynamic lengths, sentinel
 * length/value, successful-array value. Payloads alone are 128/192 MiB.
 *)
val _ = print
  ("@@TASK29_FAILURE_CONFIG_V1\t8\t32\t96\t2\t16777216\t25165824" ^
   "\t1024\t90\t37\n")
val _ = check "both oversized requests are legal Array lengths"
  (25165824 < Array.maxLen)

(* All roots, foreign closures, attribute lists and explicit exception values
 * are constructed BEFORE measurement. No requested-size storage is created
 * by the manual control. Failed assignment must leave result=sentinel.
 *)
val sentinel = Array.array (1024, 0w90 : Word.word)
val result = ref sentinel
val requested = ref 0
val entered = ref false
val returned = ref false
val interrupted = ref false
val noopWork = fn () => ()
val action = ref noopWork
val arrayWork = fn () => result := Array.array (!requested, 0w37)
val manualException : exn = Thread.Interrupt
val manualWork = fn () => raise manualException
val enabled = [Thread.EnableBroadcastInterrupt true,
               Thread.InterruptState Thread.InterruptAsynchOnce]
val synchronous = [Thread.EnableBroadcastInterrupt true,
                   Thread.InterruptState Thread.InterruptSynch]
val savedAttributes = ref (Thread.getAttributes ())

(* The SAME protected, indirect call for no-op/manual/success/failure.
 * Normalize the handler's state explicitly for the manual raise too; a plain
 * ML raise does not perform the RTS's AsynchOnce -> Synch transition.
 * The wildcard below is cleanup-and-RERAISE only. Only Thread.Interrupt can
 * become an accepted outcome; Size/Fail/other exceptions terminate the run.
 *)
fun protectedWork () =
  (((Thread.setAttributes enabled;
     entered := true;
     (!action) ();
     returned := true)
    handle Thread.Interrupt =>
      (Thread.setAttributes synchronous; interrupted := true));
   Thread.setAttributes (!savedAttributes))
  handle ex => (Thread.setAttributes (!savedAttributes); raise ex)

fun at xs i = List.nth (xs, i) : LargeInt.int
fun fields xs = String.concatWith "\t" (map LargeInt.toString xs)
fun sum xs = List.foldl (op +) (0 : LargeInt.int) xs
val indexes = [3, 4, 5, 6, 7]
val previous = ref (NONE : LargeInt.int list option)
val labels = ref ([] : string list)
fun ordered (a, b) = List.all (fn i => at a i <= at b i) indexes
fun valid xs =
  at xs 0 = 1 andalso at xs 1 = 8 andalso at xs 2 = 0 andalso
  at xs 3 = sum (List.drop (xs, 4))
fun endpoint label side xs =
  print ("@@TASK29_FAILURE_ENDPOINT_V1\t" ^ label ^ "\t" ^ side ^
         "\t" ^ fields xs ^ "\n")
fun bit b = if b then 1 else 0
fun checksum a = Array.foldl (fn (w, n) => Word.toInt w + n) 0 a
fun retained () =
  Array.length sentinel = 1024 andalso
  Array.all (fn w => w = 0w90) sentinel

fun measure label kind n work = let
  val _ = check (label ^ " unique label")
    (not (List.exists (fn s => s = label) (!labels)))
  val _ = labels := label :: !labels
  val _ = action := work
  val _ = requested := n
  val _ = result := sentinel
  val _ = entered := false
  val _ = returned := false
  val _ = interrupted := false
  val _ = savedAttributes := Thread.getAttributes ()
  val _ = print ("@@TASK29_FAILURE_REQUEST_V1\t" ^ label ^ "\t" ^ kind ^
                 "\t" ^ Int.toString n ^ "\n")
  (* Flush BEFORE the bracket, so the RTS stderr diagnostic has a definite
   * place in the merged process receipt. Never print that diagnostic here.
   *)
  val _ = TextIO.flushOut TextIO.stdOut
  val _ = startBracket ()
  val _ = protectedWork ()
  val _ = endBracket ()
  (* The full failure, handler AND restoration have now finished. All getters,
   * result validation, checksums and formatting occur outside the bracket.
   *)
  val a = List.tabulate (8, getCall)
  val b = List.tabulate (8, fn i => getCall (8 + i))
  val _ = endpoint label "start" a
  val _ = endpoint label "end" b
  val _ = check (label ^ " valid monotonic endpoints")
    (valid a andalso valid b andalso ordered (a, b))
  val _ = case !previous of NONE => () | SOME p =>
    check (label ^ " process monotonicity") (ordered (p, a))
  val _ = previous := SOME b
  val delta = map (fn i => at b i - at a i) indexes
  val _ = print ("@@TASK29_FAILURE_RAW_V1\t" ^ label ^ "\t" ^
                 fields delta ^ "\n")
  val restored = Thread.getAttributes () = !savedAttributes
  val values = [bit (!entered), bit (!returned), bit (!interrupted),
                bit restored, Array.length sentinel, checksum sentinel,
                Array.length (!result), checksum (!result)]
  val _ = print ("@@TASK29_FAILURE_RESULT_V1\t" ^ label ^ "\t" ^
    String.concatWith "\t" (map Int.toString values) ^ "\n")
  val expectInterrupt = kind = "manual" orelse kind = "failure"
  val _ = check (label ^ " entered; exact outcome; attributes restored")
    (!entered andalso !returned = not expectInterrupt andalso
     !interrupted = expectInterrupt andalso restored)
  val _ = check (label ^ " rooted sentinel intact") (retained ())
  val _ = check (label ^ " result escaped/failed assignment unchanged")
    (if kind = "success" then
       Array.length (!result) = n andalso
       Array.all (fn w => w = 0w37) (!result)
     else !result = sentinel)
in delta end

(* Declare all helpers before installing the OS limit. Remaining top-level
 * body compilation/formatting may allocate, but must fit the 64 MiB budget.
 *)
fun successful zero label n = let
  val d = measure label "success" n arrayWork
  val difference = ListPair.map (op -) (d, zero)
  val words = Int.toLarge n
in check (label ^ " exact successful native payload slope")
     (difference = [words, words, 0, 0, 0])
end

fun failure manual zero repeat n = let
  val suffix = Int.toString n ^ "-" ^ Int.toString repeat
  val m = measure ("manual-" ^ suffix) "manual" 0 manualWork
  val d = measure ("fail-" ^ suffix) "failure" n arrayWork
  val _ = check ("failure has EXACT prebuilt-interrupt wrapper cost " ^ suffix)
    (m = manual andalso d = manual)
  val _ = check ("requested native reservation NOT charged " ^ suffix)
    (at d 0 < Int.toLarge n)
  (* Recovery is required after EVERY failure, including the last. Use the
   * same dynamic allocating closure as for failures, not a different path.
   *)
  val _ = List.app (fn size => successful zero
    ("recover-" ^ suffix ^ "-" ^ Int.toString size) size) [0, 256, 512]
in () end

(* FFI closures already exist. Warm fullGC before reading virtual size and
 * applying the one-shot OS bound; none of this is in a measured interval.
 * LIMIT_V1: success, vsize_before, applied_soft, hard, headroom (bytes).
 * The C helper independently re-reads RLIMIT_AS before reporting success.
 *)
val _ = PolyML.fullGC ()
val limitStatus = limitAddressSpace ()
val _ = check "OS address-space limit applied and verified" (limitStatus = 1)
val limitValues = List.tabulate (4, getLimit)
val _ = print ("@@TASK29_FAILURE_LIMIT_V1\t" ^
               fields (Int.toLarge limitStatus :: limitValues) ^ "\n")
val _ = check "exact OS address-space headroom and hard bound"
  (at limitValues 0 > 0 andalso
   at limitValues 3 = 67108864 andalso
   at limitValues 1 = at limitValues 0 + at limitValues 3 andalso
   at limitValues 2 >= at limitValues 1)

val _ = measure "noop-warmup-1" "noop" 0 noopWork
val _ = measure "noop-warmup-2" "noop" 0 noopWork
val idle = measure "noop-before-1" "noop" 0 noopWork
val idle2 = measure "noop-before-2" "noop" 0 noopWork
val _ = check "raw no-op wrapper repeats exactly" (idle = idle2)
val _ = measure "manual-warmup-1" "manual" 0 manualWork
val _ = measure "manual-warmup-2" "manual" 0 manualWork
val manual = measure "manual-before-1" "manual" 0 manualWork
val manual2 = measure "manual-before-2" "manual" 0 manualWork
val _ = check "prebuilt manual-interrupt wrapper repeats exactly"
  (manual = manual2)
val _ = check "manual wrapper not below no-op in any category"
  (ListPair.allEq (fn (x, y) => x >= y) (manual, idle))

val zero = measure "array-before-0" "success" 0 arrayWork
val _ = successful zero "array-before-256" 256
val _ = successful zero "array-before-512" 512
val _ = List.app (fn repeat => List.app (failure manual zero repeat)
                    [16777216, 25165824]) [1, 2]
val manualLast1 = measure "manual-final-1" "manual" 0 manualWork
val manualLast2 = measure "manual-final-2" "manual" 0 manualWork
val idleLast1 = measure "noop-final-1" "noop" 0 noopWork
val idleLast2 = measure "noop-final-2" "noop" 0 noopWork
val _ = check "raw wrappers stable after all failures and recovery"
  (manualLast1 = manual andalso manualLast2 = manual andalso
   idleLast1 = idle andalso idleLast2 = idle)
val _ = print
  ("@@TASK29_FAILURE_UNCLAIMED_V1\tRTS allocation failures; " ^
   "interpreter allocation failures; code allocation failures; " ^
   "compact32; overflow injection; foreign-thread callbacks; image lineage; " ^
   "full runtime completeness; TASK29B matrix\n")
val _ = print ("@@TASK29_FAILURE_COMPLETE_V1\t" ^
               Int.toString (length (!labels)) ^ "\n")
val _ = TextIO.flushOut TextIO.stdOut
