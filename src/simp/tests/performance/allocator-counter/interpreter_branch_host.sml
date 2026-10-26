(* Native host, after the existing hybrid interpreter controls. Compile ALL
 * entries before brackets. Successful bytecode branch coverage only: a slow
 * bytecode branch does NOT establish segment refill, GC retry or failure.
 * No workers run here; the two C snapshots can therefore be reconciled.
 *)
structure Task29InterpreterBranches =
struct
open Task29InterpreterHost
val getBranch = Foreign.buildCall1
  (Foreign.getSymbol library "task29_alloc_interpreter_get",
   Foreign.cInt, Foreign.cUint64Large)
fun emit kind values =
  print ("@@TASK29_IBRANCH_" ^ kind ^ "_V1\t" ^
         String.concatWith "\t" values ^ "\n")
val plans = map (fn kind => (kind, map (fn repeat => map (fn n =>
  plan kind (kind ^ "-" ^ Int.toString n ^ "-" ^ repeat) n)
  [65536, 131072]) ["1", "2"])) ["refs", "words"]
val verifyRefs = entry
  "Task29Interpreter.verifyRefs \"after-live-gc\" 131072"
val verifyWords = entry
  "Task29Interpreter.verifyWords \"after-live-gc\" 131072"
(* Retained-result evidence uses this experiment's own prefix. Changing the
 * emitter is outside the bracket; no compiler or I/O is measured. *)
val setEmitter = entry
  "Task29Interpreter.resultPrefix := \"@@TASK29_IBRANCH_RESULT_V1\""
val previous = ref (NONE : (LargeInt.int list * LargeInt.int list) option)
fun branchValid s = at s 0 = 1 andalso at s 1 = 8 andalso
                    at s 2 = 0 andalso at s 7 = 0
fun branchOrdered (a,b) =
  List.all (fn i => at a i <= at b i) [3,4,5,6]
fun reconcile a b = at a 6 = at b 4 + at b 6
val labels = ref ([] : string list)
fun measure label code = let
  val _ = check "unique branch bracket"
    (not (List.exists (fn s => s = label) (!labels)))
  val _ = labels := label :: !labels
  val _ = startBracket ()
  val _ = ignore (code ())
  val _ = endBracket ()
  val a = List.tabulate (8, getCall)
  val b = List.tabulate (8, fn i => getCall (8+i))
  val ba = List.tabulate (8, getBranch)
  val bb = List.tabulate (8, fn i => getBranch (8+i))
  val delta = map (fn i => at b i - at a i) indexes
  val split = map (fn i => at bb i - at ba i) [3,4,5,6]
  val _ = emit "ENDPOINT" [label,"start",fields a]
  val _ = emit "ENDPOINT" [label,"end",fields b]
  val _ = emit "BRANCH" [label,"start",fields ba]
  val _ = emit "BRANCH" [label,"end",fields bb]
  val _ = emit "RAW" [label,fields delta]
  val _ = emit "SPLIT" [label,fields split]
  val _ = check (label ^ " ABI/sums/monotonicity")
    (valid a andalso valid b andalso ordered (a,b) andalso
     branchValid ba andalso branchValid bb andalso
     branchOrdered (ba,bb) andalso reconcile a ba andalso reconcile b bb)
  val _ = case !previous of NONE => () | SOME (p,bp) =>
    check "process-monotonic branch snapshots"
      (ordered (p,a) andalso branchOrdered (bp,ba))
  val _ = previous := SOME (b,bb)
in delta end
fun work kind (label,n,prepare,verify) = let
  val _ = ignore (prepare ())
  val d = measure label workEntry
  val _ = check "physical interpreted storage"
    (at d 3 >= Int.toLarge (if kind = "refs" then 5*n else n+1))
  val _ = ignore (verify ())
in d end
fun series (kind, rounds) = let
  val first = map (work kind) (hd rounds)
  val second = map (work kind) (List.nth (rounds,1))
  val _ = check (kind ^ " exact repeat, ALL categories") (first = second)
  val _ = exact (kind ^ " large-array/ref doubling")
    (hd first) (List.nth (first,1))
    (Int.toLarge ((if kind = "refs" then 5 else 1)*65536))
in () end
fun run () = let
  val _ = emit "SCOPE"
    ["successful-bytecode-fast-slow-controls; " ^
     "not refill/failure/lineage closure"]
  val abi = abiCheck ()
  val _ = emit "ABI" [Int.toString abi]
  val _ = check "branch ABI controls" (abi = 15)
  val _ = emit "CONFIG" ["8","2","65536","131072","5","1"]
  val _ = ignore (setEmitter ())
  val idle = measure "noop-before-1" noopEntry
  val idle2 = measure "noop-before-2" noopEntry
  val gc = measure "gc-empty-1" gcEntry
  val gc2 = measure "gc-empty-2" gcEntry
  val _ = List.app series plans
  val live = measure "gc-live-1" gcEntry
  val live2 = measure "gc-live-2" gcEntry
  val _ = ignore (verifyRefs ())
  val _ = ignore (verifyWords ())
  val final = measure "noop-final-1" noopEntry
  val final2 = measure "noop-final-2" noopEntry
  val _ = check "branch no-op costs stable"
    (idle = idle2 andalso idle = final andalso idle = final2)
  val _ = check "GC does not recount large retained bytecode objects"
    (gc = gc2 andalso gc = live andalso gc = live2)
  val _ = emit "UNCLAIMED"
    ["refill; GC retry; failed allocations; native compiler/image lineage; " ^
     "TASK29B matrix"]
  val _ = emit "COMPLETE" [Int.toString (length (!labels))]
in () end
end;
val _ = Task29InterpreterBranches.run ();
