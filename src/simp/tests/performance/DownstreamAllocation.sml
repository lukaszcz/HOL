(* TASK37 cumulative-allocation fixture for the `downstream_*` cases of
   ClientPerformance.sml, installed as Performance.sml in the place of
   MatrixAllocation.sml; the driver below is MatrixAllocation.sml's from its
   "Build every foreign closure" comment on, word for word
   (test_allocation_client.py compares them), and MatrixSupport.sml supplies
   the work phase. One case and one size per fresh process; needs the
   private patched runtime and TASK29_ALLOC_SHIM like MatrixAllocation.sml.

   The workloads are those of ClientPerformance.sml: `sink`, `consume`,
   `same`, `verify`, `conversion` and `downstream` are copied from it line
   for line (the test checks that), and the only additions are the lines
   that end in a comment saying alloc: each calls `retaining`, which gives
   the work phase the result to fingerprint (the retained theorem) and a
   use of it (apply the retained conversion or tactic again).
   The cases use numLib, reduceLib and bossLib, so the task that runs this
   fixture installs the shared client closure recompiled against the
   private simplifier (client_dependencies.py, as the timing path does),
   which is why this fixture is not part of ClientAllocation.sml: the
   TASK31 client cells keep loading no shared closure. *)
open HolKernel boolLib simpLib Paired
val _ = new_theory "task37_downstream_allocation"
val required = MatrixSupport.required
val retaining = MatrixSupport.retaining
val thmText = MatrixSupport.thmText
fun integer name = valOf (Int.fromString (Paired.env name))
val label = Paired.env "PERF_CASE"
val size = integer "PERF_SIZE"
val steady = integer "ALLOC_STEADY"
val repeats = integer "ALLOC_REPEATS"
val _ = required (size >= 0 andalso size <= 10000 andalso
                  steady > 0 andalso repeats >= 3)
val selected = label
val workloadSize = size
val sink = ref 0
fun consume () = sink := !sink + 1
fun same expected actual =
  aconv (concl expected) (concl actual) andalso
  HOLset.equal (hypset expected,hypset actual)
fun verify expected actual =
  required (same expected actual andalso
    List.all (fn s => s = "DISK_THM") (#1 (Tag.dest_tag (tag actual))))
type workload = {run:unit -> unit, verify:unit -> unit}

fun conversion stage make input expected : workload = let
  val slot = ref (make ())
  val proof = ref expected
  fun apply () = proof := (!slot) input
  fun run () =
    (case stage of
       "construct" => slot := make ()
     | "reuse" => apply ()
     | "complete" => (slot := make (); apply ())
     | _ => raise Fail "unknown conversion stage";
     consume ())
  fun check () =
    (if stage = "construct" then apply () else (); verify expected (!proof))
  val _ = apply ()
  val _ = check ()
  val _ = retaining (fn () => thmText (!proof))                (*alloc*)
                    (fn () => ignore ((!slot) input))          (*alloc*)
in {run=run,verify=check} end

(* These dependencies are available in the shared ordinary baseline closure.
   Integer/real builds and fresh loading have explicit matrix prerequisites;
   never substitute a boolean toy for those missing downstream environments. *)
fun downstream name n : workload = let
  val count = Int.max (1,n)
  val p = mk_var ("client_downstream_p",bool)
  val number = numSyntax.mk_numeral (Arbnum.fromInt count)
  val sum = numSyntax.mk_plus (number,numSyntax.zero_tm)
  val arithmeticInput = mk_eq (sum,number)
  val expected = EQT_INTRO (SPEC number arithmeticTheory.ADD_0)
  val reduceInput = sum
  val reduceExpected = SPEC number arithmeticTheory.ADD_0
in case name of
    "downstream_arithmetic" => conversion "complete"
      (fn () => SIMP_CONV numLib.arith_ss []) arithmeticInput expected
  | "downstream_reduce" => conversion "complete"
      (fn () => reduceLib.REDUCE_CONV) reduceInput reduceExpected
  | "downstream_boss" => let
      val target = mk_conj (p,T)
      val goal = ([p],target)
      val expected = CONJ (ASSUME p) TRUTH
      val proof = ref expected
      fun run () = let
        val (gs,vf) = testutils.runtac
          (bossLib.ASM_SIMP_TAC (bossLib.boss_ss ()) []) goal
        val _ = required (null gs)
      in proof := vf []; consume () end
      val _ = run ()                                           (*alloc*)
      val _ = retaining (fn () => thmText (!proof)) run        (*alloc*)
    in {run=run,verify=fn () => verify expected (!proof)} end
  | _ => raise Fail ("unknown downstream case: " ^ name)
end

fun choose () =
  if String.isPrefix "downstream_" selected then
    downstream selected workloadSize
  else raise Fail ("unknown downstream PERF_CASE: " ^ selected)
type workload = MatrixSupport.workload
val workPhase = MatrixSupport.workPhase
fun workload _ _ = let
  val {run,verify=check} = choose ()
in MatrixSupport.basic run check end

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
