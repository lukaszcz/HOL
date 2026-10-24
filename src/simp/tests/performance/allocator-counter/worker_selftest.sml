(* Allocating ML worker/retirement controls, NOT full allocator validation.
 * Build as a separate native testutils fixture, using the same bracket.so as
 * selftest.sml.  Requires the pinned experimental runtime and 8-byte words.
 * No unsafe casts, synthetic increments, elapsed-time or tolerance assertions.
 *
 * API audit (read-only pinned polyml-5.9.2-2/src):
 * documentation/Reference/Threads.html; basis/Thread.sml, lines 398--730;
 * libpolyml/processes.cpp, MutexBlock/MutexUnlock/PolyThreadIsActive.
 * fork silently discards uncaught exceptions: EVERY entry has our handler.
 * isActive, not an acknowledgement, establishes actual retirement.
 *
 * Each worker alternates between two precreated mutex gates. The controller
 * owns both initially, releases one for work, and reacquires that gate only
 * after the worker acknowledges arrival at the OTHER, still-locked gate.
 * After acknowledgement the worker can only execute Mutex.lock/unlock; these
 * pinned paths allocate no managed objects and blocking releases ML memory
 * for GC. Thus parked means work is excluded by an owned gate, even if the
 * worker has not yet entered the RTS wait. The controller's tail polling loop
 * also allocates nothing. No CV registration race/list allocation, sleeps,
 * allocating FFI polling, or schedule-dependent application retry loops.
 * All actual coordination costs remain raw and must repeat EXACTLY.
 * A blocking generic Foreign call is NOT a GC-safe replacement for ML wait.
 *)
open testutils
(* HOL's ConcIsaLib exports the Poly/ML substructures under these names. *)
structure WT = Thread
structure WM = Mutex

fun check label yes = (tprint label; if yes then OK () else die label)
val shimPath =
  case OS.Process.getEnv "TASK29_ALLOC_SHIM" of
      SOME p => p
    | NONE => raise Fail "set TASK29_ALLOC_SHIM to absolute bracket.so"
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
val _ = print
  ("@@TASK29_WORKER_SCOPE_V1\tallocating-ML-workers-only; " ^
   "not full runtime validation\n")
val _ = print ("@@TASK29_WORKER_RUNTIME_V1\t" ^ runtimePath () ^ "\n")
val maps = TextIO.openIn "/proc/self/maps"
fun emitMaps () = case TextIO.inputLine maps of
    NONE => ()
  | SOME line => (print ("@@TASK29_WORKER_MAP_V1\t" ^ line); emitMaps ())
val _ = emitMaps ()
val _ = TextIO.closeIn maps
val abi = abiCheck ()
val _ = print ("@@TASK29_WORKER_ABI_V1\t" ^ Int.toString abi ^ "\n")
val _ = check "worker C ABI controls" (abi = 15)
(* workers, bytes/word, repetitions, sizes, words/ref+cons *)
val _ = print "@@TASK29_WORKER_CONFIG_V1\t4\t8\t2\t0\t256\t512\t5\n"

val lock = WM.mutex ()
val parked = ref 0
val failed = ref 0
val retiring = ref false
val size = ref 0
val gatesA = Vector.tabulate (4, fn _ => WM.mutex ())
val gatesB = Vector.tabulate (4, fn _ => WM.mutex ())
val _ = Vector.app WM.lock gatesA
val _ = Vector.app WM.lock gatesB
val phaseA = ref true
val released = ref gatesA
val roots = Vector.tabulate (4, fn _ => ref ([] : int ref list))
val errors = Vector.tabulate (4, fn _ => ref (NONE : exn option))
fun locked f =
  (WM.lock lock;
   (f () before WM.unlock lock)
   handle ex => (WM.unlock lock; raise ex))
fun makeRefs n = let
  fun loop left acc =
    if left = 0 then acc else loop (left - 1) (ref left :: acc)
in loop n [] end

(* Factory runs on the controller: even entry setup cannot escape into
 * Poly/ML's exception-discarding fork wrapper before our handler exists.
 *)
fun worker i = let
  val gateA = Vector.sub (gatesA, i)
  val gateB = Vector.sub (gatesB, i)
  val result = Vector.sub (roots, i)
  val error = Vector.sub (errors, i)
  (* No allocating operations after publication until the owned gate opens.
   * Boolean phase argument: no tuple or fresh closure per iteration.
   *)
  fun park gate =
    (WM.lock lock; parked := !parked + 1; WM.unlock lock;
     WM.lock gate; WM.unlock gate)
  fun work () = result := makeRefs (!size)
  fun loop first =
    (park (if first then gateA else gateB);
     if !retiring then () else (work (); loop (not first)))
  fun publish ex = locked (fn () =>
    (error := SOME ex; failed := !failed + 1))
in fn () => (loop true handle ex => publish ex) end
val attributes = [WT.EnableBroadcastInterrupt false,
                  WT.InterruptState WT.InterruptDefer]
(* Exactly four threads, precreated and reused, never fork inside a bracket. *)
val workers = Vector.tabulate (4, fn i => WT.fork (worker i, attributes))

(* No allocating closures/tuples or CV waits in either polling loop. *)
fun waitParked () =
  (WM.lock lock;
   if !parked = 4 orelse !failed <> 0 then WM.unlock lock
   else (WM.unlock lock; waitParked ()))
fun releaseWorkers () =
  (WM.lock lock;
   parked := 0;
   released := (if !phaseA then gatesA else gatesB);
   phaseA := not (!phaseA);
   Vector.app WM.unlock (!released);
   WM.unlock lock)
fun roundWork () =
  (releaseWorkers (); waitParked (); Vector.app WM.lock (!released))
fun allInactive () =
  not (WT.isActive (Vector.sub (workers, 0))) andalso
  not (WT.isActive (Vector.sub (workers, 1))) andalso
  not (WT.isActive (Vector.sub (workers, 2))) andalso
  not (WT.isActive (Vector.sub (workers, 3)))
fun waitInactive () = if allInactive () then () else waitInactive ()
fun retirementWork () =
  (retiring := true; releaseWorkers (); waitInactive ();
   Vector.app WM.lock (!released))
val noopWork = fn () => ()
val gcWork = fn () => PolyML.fullGC ()
val action = ref noopWork
fun activeCount () = Vector.foldl
  (fn (w, n) => if WT.isActive w then n + 1 else n) 0 workers
fun publishErrors label = Vector.appi
  (fn (i, r) => case !r of NONE => () | SOME ex =>
    print ("@@TASK29_WORKER_EXCEPTION_V1\t" ^ label ^ "\t" ^
           Int.toString i ^ "\t" ^ String.toString (General.exnMessage ex) ^
           "\n")) errors
val _ = waitParked ()
val _ = publishErrors "startup"
val _ = check "all four precreated workers parked without exceptions"
  (!parked = 4 andalso !failed = 0 andalso activeCount () = 4)

fun at xs i = List.nth (xs, i) : LargeInt.int
fun sum xs = List.foldl (op +) (0 : LargeInt.int) xs
fun fields xs = String.concatWith "\t" (map LargeInt.toString xs)
val indexes = [3, 4, 5, 6, 7]
val previous = ref (NONE : LargeInt.int list option)
val labels = ref ([] : string list)
fun endpoint label side s =
  print ("@@TASK29_WORKER_ENDPOINT_V1\t" ^ label ^ "\t" ^ side ^
         "\t" ^ fields s ^ "\n")
fun valid s =
  at s 0 = 1 andalso at s 1 = 8 andalso at s 2 = 0 andalso
  at s 3 = sum (List.drop (s, 4))
fun ordered (a, b) = List.all (fn i => at a i <= at b i) indexes

(* All state reads/output/decoding occur outside the C-frozen bracket.
 * RAW: label, n, parked-before/after, active-before/after, failures,
 *      total/native/RTS/interpreter/code delta words. No overhead subtraction.
 *)
fun measure label work = let
  val _ = check (label ^ " unique")
    (not (List.exists (fn s => s = label) (!labels)))
  val _ = labels := label :: !labels
  val _ = action := work
  val beforeParked = !parked
  val beforeActive = activeCount ()
  val _ = startBracket ()
  val _ = (!action) ()
  val _ = endBracket ()
  val a = List.tabulate (8, getCall)
  val b = List.tabulate (8, fn i => getCall (8 + i))
  val d = map (fn i => at b i - at a i) indexes
  val afterActive = activeCount ()
  val _ = endpoint label "start" a
  val _ = endpoint label "end" b
  val state = map Int.toLarge
    [!size, beforeParked, !parked, beforeActive, afterActive, !failed]
  val _ = print ("@@TASK29_WORKER_RAW_V1\t" ^ label ^ "\t" ^
                 fields (state @ d) ^ "\n")
  val _ = publishErrors label
  val _ = check (label ^ " no worker exception") (!failed = 0)
  val _ = check (label ^ " valid ABI/category sums") (valid a andalso valid b)
  val _ = check (label ^ " ordered endpoints") (ordered (a, b))
  val _ = case !previous of NONE => () | SOME p =>
    check (label ^ " process monotonic including retirement") (ordered (p, a))
  val _ = previous := SOME b
  val _ = check (label ^ " delta category sum") (hd d = sum (tl d))
  val _ = check (label ^ " quiescent workers")
    (if !retiring then !parked = 0 andalso afterActive = 0
     else beforeParked = 4 andalso !parked = 4 andalso
          beforeActive = 4 andalso afterActive = 4)
in d end

(* Verify every cell, not just a positive allocation count. *)
fun verifyRoots label n = Vector.appi (fn (i, r) => let
  fun correct [] next = next = n + 1
    | correct (r :: rs) next = !r = next andalso correct rs (next + 1)
  val _ = check (label ^ " worker " ^ Int.toString i ^ " retained contents")
    (length (!r) = n andalso correct (!r) 1)
in print ("@@TASK29_WORKER_RESULT_V1\t" ^ label ^ "\t" ^
          Int.toString i ^ "\t" ^ Int.toString n ^ "\t" ^
          Int.toString (n * (n + 1) div 2) ^ "\n") end) roots
fun workRound label n =
  (size := n;
   let val d = measure label roundWork
   in verifyRoots label n; d end)
fun exact label zero d n = let
  val words = 20 * Int.toLarge n
in check label (ListPair.mapEq (op -) (d, zero) =
                [words, words, 0, 0, 0]) end

val _ = measure "noop-warmup-1" noopWork
val _ = measure "noop-warmup-2" noopWork
val idle = measure "noop-before" noopWork
val _ = measure "gc-warmup" gcWork
val emptyGC = measure "gc-empty-1" gcWork
val emptyGC2 = measure "gc-empty-2" gcWork
val _ = check "empty GC wrapper repeats exactly" (emptyGC = emptyGC2)
val _ = workRound "workers-warmup-1" 0
val _ = workRound "workers-warmup-2" 0
val zero1 = workRound "workers-0-1" 0
val small1 = workRound "workers-256-1" 256
val large1 = workRound "workers-512-1" 512
val zero2 = workRound "workers-0-2" 0
val small2 = workRound "workers-256-2" 256
val large2 = workRound "workers-512-2" 512
val _ = exact "four workers exact 256 native ref/cons slope" zero1 small1 256
val _ = exact "four workers exact 512 native ref/cons slope" zero1 large1 512
val _ = exact "four workers exact doubling slope" small1 large1 256
val _ = check "all worker category deltas repeat exactly"
  (zero1 = zero2 andalso small1 = small2 andalso large1 = large2)
val liveGC1 = measure "gc-live-1" gcWork
val liveGC2 = measure "gc-live-2" gcWork
val parkedIdle = measure "noop-parked" noopWork
val _ = check "parked no-op stable" (parkedIdle = idle)
val _ = verifyRoots "before-retirement" 512
val _ = measure "retirement" retirementWork
val _ = Vector.appi (fn (i, w) => let
  val active = WT.isActive w
  val _ = print ("@@TASK29_WORKER_RETIRED_V1\t" ^ Int.toString i ^
                 "\t" ^ (if active then "1" else "0") ^ "\n")
in check ("actual isActive false " ^ Int.toString i) (not active) end) workers
val idle1 = measure "noop-retired-1" noopWork
val idle2 = measure "noop-retired-2" noopWork
val retiredGC1 = measure "gc-retired-1" gcWork
val retiredGC2 = measure "gc-retired-2" gcWork
val _ = verifyRoots "after-retired-gc" 512
val _ = check "retired no-op stable" (idle1 = idle andalso idle2 = idle)
val _ = check "GC never recounts live data before/after retirement"
  (liveGC1 = emptyGC andalso liveGC2 = emptyGC andalso
   retiredGC1 = emptyGC andalso retiredGC2 = emptyGC)
val _ = print
  ("@@TASK29_WORKER_UNCLAIMED_V1\tcompact32; foreign-created threads; " ^
   "interpreter coverage; failures/overflow; full runtime completeness; " ^
   "TASK29B matrix\n")
val _ = print ("@@TASK29_WORKER_COMPLETE_V1\t" ^
               Int.toString (length (!labels)) ^ "\n")
