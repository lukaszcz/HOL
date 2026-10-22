(* Direct ordinary Cond_rewr probes. No traversal, simplifier projections,
   extension modules, or production instrumentation. Retained-graph allocation
   auditing is separate from these timing batches and their storage schema. *)
open HolKernel boolSyntax Conv Drule Paired
val _ = new_theory "conditional_performance"
fun required b = if b then () else raise Fail "invalid conditional benchmark"
fun integer s = valOf (Int.fromString (Paired.env s))
val samples = integer "PERF_SAMPLES"
val seconds = valOf (Real.fromString (Paired.env "PERF_SECONDS"))
val sink = ref 0
val callbacks = ref 0
fun callback () = callbacks := !callbacks + 1
fun consume n = sink := !sink + n
fun repeat n f = if n = 0 then () else (f (); repeat (n - 1) f)
fun real x = Real.fmt (StringCvt.SCI (SOME 12)) x
fun emit key fields = Paired.observe key (String.concatWith "," fields)
fun measure n f = let
  val beforeCallbacks = !callbacks
  val timer = Timer.startCPUTimer ()
  val walltimer = Timer.startRealTimer ()
  val beforeSink = !sink
  val _ = repeat n f
  val {nongc={usr,sys},gc={usr=gu,sys=gs}} = Timer.checkCPUTimes timer
  val {usr=cu,sys=cs} = Timer.checkCPUTimer timer
  val gc = Timer.checkGCTime timer
  val wall = Time.toReal (Timer.checkRealTimer walltimer)
  val times = map Time.toReal [usr,sys,gu,gs,cu,cs,gc]
  val _ = required (List.all (fn t => t >= 0.0) times)
  val _ = required (Real.abs (Time.toReal cu -
                    Time.toReal usr - Time.toReal gu) < 0.02)
  val _ = required (Real.abs (Time.toReal cs -
                    Time.toReal sys - Time.toReal gs) < 0.02)
  val _ = required (Real.abs (Time.toReal gc - Time.toReal gu) < 0.02)
  (* Only timed solver calls count. Saved construction results are exercised
     after the timer, and cannot change the measured consumption. *)
  val _ = consume (!callbacks - beforeCallbacks)
in (wall, map real (wall :: times) @ [Int.toString (!sink - beforeSink)])
end
val (_, accounting) = measure 5 (fn () => (PolyML.fullGC (); consume 1))
val _ = emit "timer.accounting" accounting
val _ = Paired.check "timer accounting" true

val x = mk_var ("conditional_x",bool)
val a = mk_var ("conditional_a",bool)
val b = mk_var ("conditional_b",bool)
val plain = CONJUNCT1 (SPEC x boolTheory.AND_CLAUSES)
(* The condition shares a matched variable, so both instantiation and the
   solver's returned hypothesis must survive into the checked kernel proof. *)
val rule = DISCH (mk_neg x) plain
val condition = mk_neg a
val conditionProof = ASSUME condition
val plainExpected = CONJUNCT1 (SPEC a boolTheory.AND_CLAUSES)
val input = lhs (concl plainExpected)
val expected = CONJUNCT2 (CONJ conditionProof plainExpected)
fun solve stack tm =
  (required (length stack = 1 andalso aconv (hd stack) condition andalso
             aconv tm condition);
   callback (); conditionProof)
fun noSolve _ _ = raise Fail "unexpected side condition"
fun verify expected th =
  required (aconv (concl th) (concl expected) andalso
            HOLset.equal (hypset th,hypset expected))
fun use expected th = (verify expected th; consume 1)
val namedRule = ("conditional",rule)
val namedPlain = ("unconditional",plain)
val conditional = Cond_rewr.COND_REWR_CONV namedRule false
val unconditional = Cond_rewr.COND_REWR_CONV namedPlain false
val saved = conditional solve []

(* A genuine variable-permutation theorem; choose the descending direction
   explicitly and leave bounded=false so the AC order check is exercised. *)
val acRule = SPEC_ALL boolTheory.CONJ_SYM
val acAB = mk_conj (a,b)
val acBA = mk_conj (b,a)
val (acInput,acOther,acExpected) =
  if Cond_rewr.ac_term_ord (acAB,acBA) = GREATER then
    (acAB,acBA,SPECL [a,b] boolTheory.CONJ_SYM)
  else (acBA,acAB,SPECL [b,a] boolTheory.CONJ_SYM)
val namedAC = ("AC",acRule)
val ac = Cond_rewr.COND_REWR_CONV namedAC false
val savedAC = ac noSolve []
val _ = verify expected (saved input)
val _ = verify plainExpected (unconditional noSolve [] input)
val _ = verify acExpected (savedAC acInput)
val _ = Paired.check "workload inputs"
  (length (hyp expected) = 1 andalso null (hyp plainExpected) andalso
   Cond_rewr.ac_term_ord (acInput,acOther) = GREATER andalso
   not (can savedAC acOther))

fun bench label f verifyResult = let
  fun calibration n = let
    val _ = PolyML.fullGC ()
    val (wall, fields) = measure n f
    val _ = verifyResult ()
    val _ = emit ("calibration." ^ label) (Int.toString n :: fields)
  in if wall >= seconds then n
     else (required (n < 1073741824); calibration (n * 2)) end
  val n = calibration 1
  fun sample i = let
    val _ = PolyML.fullGC ()
    val (_, fields) = measure n f
    val _ = verifyResult ()
    val _ = emit ("batch." ^ label)
      (Int.toString i :: Int.toString n :: fields)
  in Paired.check ("results " ^ label) true end
in List.app sample (List.tabulate (samples,I)) end
(* Store at the matcher-construction boundary, before solver and stack
   application. Each closure escapes; batch-end proof checks prevent a dead
   construction benchmark without charging application to construction. *)
val slot = ref conditional
val _ = bench "conditional_construct"
  (fn () => (slot := Cond_rewr.COND_REWR_CONV namedRule false; consume 1))
  (fn () => verify expected ((!slot) solve [] input))
val _ = bench "unconditional_construct"
  (fn () => (slot := Cond_rewr.COND_REWR_CONV namedPlain false; consume 1))
  (fn () => verify plainExpected ((!slot) noSolve [] input))
val _ = bench "conditional_reuse"
  (fn () => use expected (saved input)) (fn () => ())
val _ = bench "conditional_complete"
  (fn () => use expected
    (Cond_rewr.COND_REWR_CONV namedRule false solve [] input)) (fn () => ())
val _ = bench "ac_construct"
  (fn () => (slot := Cond_rewr.COND_REWR_CONV namedAC false; consume 1))
  (fn () => verify acExpected ((!slot) noSolve [] acInput))
val _ = bench "ac_reuse"
  (fn () => use acExpected (savedAC acInput)) (fn () => ())
val _ = emit "sink" [Int.toString (!sink)]
