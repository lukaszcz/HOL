(* TASK29B cumulative-allocation fixture, installed as Performance.sml.
   One case and one size per fresh process; MatrixSupport.sml is reused
   unchanged. Needs the private patched runtime (see allocator-counter/)
   and TASK29_ALLOC_SHIM naming the bracket.so linked against it.

   Brackets are separate records (see allocation_schema.py):
     startup           first probe: process load up to the fixture's start
     empty             no-op bracket; published, never subtracted
     canary            allocates one array of canaryArray words; the parser
                       demands its exact cost beyond `empty` per category
     setup             workload label size (nets within the phase)
     operation_first   one run (): the second one in the process, since the
                       workload builders already run it once inside setup
     operation_steady  ALLOC_STEADY runs, repeated ALLOC_REPEATS times
     apply             verify (), which also consumes the retained result
   fullGC and the beforeBatch/afterBatch assertions are outside brackets.
   After the last bracket an untimed `work` phase (structure "v1", see
   allocation_schema.py) counts the operation's trace events and kernel
   inferences twice and fingerprints the retained result; nothing of it is
   inside a bracket.
   Counts are predeclared by the driver, never calibrated here. No decoding,
   output or label work happens between a bracket's start and end; the
   endpoints are read from C storage afterwards and printed at the very end. *)
open HolKernel Paired MatrixSupport
val _ = new_theory "matrix_allocation"
(* history_theory_change: the exported theory has clock- and pid-dependent
   words and files below the working directory, so no transition is made;
   the reparse comes from the Context.restore in the case itself. *)
val _ = theoryChange := (fn _ => ())
fun integer name = valOf (Int.fromString (Paired.env name))
val label = Paired.env "PERF_CASE"
val size = integer "PERF_SIZE"
val steady = integer "ALLOC_STEADY"
val repeats = integer "ALLOC_REPEATS"
val _ = required (Lib.mem label cases andalso Lib.mem size sizes andalso
                  steady > 0 andalso repeats >= 3)

(* Build every foreign closure before any bracket. start/end are no-argument
   cVoid calls. Decoding happens only after a bracket has ended. *)
val library = Foreign.loadLibrary (Paired.env "TASK29_ALLOC_SHIM")
fun symbol name = Foreign.getSymbol library name
val runtimePath = Foreign.buildCall0
  (symbol "task29_alloc_runtime", (), Foreign.cString)
val abiCheck = Foreign.buildCall0
  (symbol "task29_alloc_abi_check", (), Foreign.cInt)
val startCall = Foreign.buildCall0
  (symbol "task29_alloc_start", (), Foreign.cVoid)
val endCall = Foreign.buildCall0
  (symbol "task29_alloc_end", (), Foreign.cVoid)
val getCall = Foreign.buildCall1
  (symbol "task29_alloc_get", Foreign.cInt, Foreign.cUint64Large)
val getPath = Foreign.buildCall1
  (symbol "task29_alloc_path_get", Foreign.cInt, Foreign.cUint64Large)
val identity = runtimePath ()
val abi = abiCheck ()
val _ = required (abi = 15)
val canaryArray = 1000
val canarySlot = ref (NONE : int Array.array option)

type endpoints = LargeInt.int list
val log = ref ([] : (string * endpoints * endpoints) list)
val cell = ref (NONE : workload option)
fun repeat n f = if n = 0 then () else (f (); repeat (n - 1) f)

(* The indirect work call keeps the bracket independent of the operation. *)
fun bracket name work = let
  val _ = startCall ()
  val _ = work ()
  val _ = endCall ()
  val s = List.tabulate (8, getCall)
  val e = List.tabulate (8, fn i => getCall (8 + i))
in log := (name, s, e) :: !log end

fun experiment () = let
  val _ = bracket "startup" (fn () => ())
  val _ = bracket "empty" (fn () => ())
  val _ = bracket "canary"
    (fn () => canarySlot := SOME (Array.array (canaryArray, 0)))
  val _ = required (Array.length (valOf (!canarySlot)) = canaryArray)
  val _ = canarySlot := NONE
  val _ = bracket "setup" (fn () => cell := SOME (workload label size))
  val {run, verify, beforeBatch, afterBatch} = valOf (!cell)
  fun batch name count work = let
    val _ = PolyML.fullGC ()
    val _ = beforeBatch ()
    val _ = bracket name work
  in afterBatch count end
  val _ = batch "operation_first" 1 run
  fun steadyBatch _ =
    batch "operation_steady" steady (fn () => repeat steady run)
  val _ = List.app steadyBatch (List.tabulate (repeats, I))
in bracket "apply" verify end
val _ = experiment ()
val work = workPhase (valOf (!cell))

fun fields xs = String.concatWith "," (map LargeInt.toString xs)
fun emitBracket index (name, s, e) =
  Paired.observe ("alloc." ^ name)
    (Int.toString index ^ ";" ^ fields s ^ ";" ^ fields e)
val _ = Paired.observe "alloc.config"
  (String.concatWith "," [label, Int.toString size, Int.toString steady,
                          Int.toString repeats, Int.toString abi,
                          Int.toString canaryArray])
val maps = TextIO.openIn "/proc/self/maps"
fun emitMaps () = case TextIO.inputLine maps of
    NONE => ()
  | SOME line => (print ("@@TASK29_ALLOC_MAP_V1\t" ^ line); emitMaps ())
val _ = print ("@@TASK29_ALLOC_RUNTIME_V1\t" ^ identity ^ "\n")
val _ = emitMaps ()
val _ = TextIO.closeIn maps
local
  val steadyIndex = ref 0
  fun index name =
    if name <> "operation_steady" then 0
    else let val i = !steadyIndex in (steadyIndex := i + 1; i) end
in
  val _ = List.app (fn r as (name, _, _) => emitBracket (index name) r)
                   (List.rev (!log))
end
(* The path snapshot of the last bracket: path counter 27 counts entries of
   a thread the runtime did not create (cumulative since process start, so it
   covers every bracket); word 31 is reserved. Both must be zero. *)
val _ = Paired.observe "alloc.foreign"
  (LargeInt.toString (getPath (32 + 3 + 27)) ^ "," ^
   LargeInt.toString (getPath (32 + 31)))
val _ = List.app (fn (key, value) => Paired.observe key value) work
val _ = Paired.check "allocation brackets" true
