(* TASK28 P09 fragments/compilation/exclusions/history/retained graphs.
   One case and one size per fresh process. Validate with
     performance_schema.validate(events, samples, seconds,
       labels=[PERF_CASE], consumed={PERF_CASE: 1}, storage=False).
   MatrixSupport.cases is the authoritative case list; sizes are
   0/1/10/100/1000/10000. Raw graph output is a separate non-Paired record.
   No outliers are removed; acceptance requires the external paired runner. *)
open HolKernel Paired MatrixSupport
val _ = new_theory "matrix_performance"
fun integer name = valOf (Int.fromString (Paired.env name))
val label = Paired.env "PERF_CASE"
val size = integer "PERF_SIZE"
val samples = integer "PERF_SAMPLES"
val seconds = valOf (Real.fromString (Paired.env "PERF_SECONDS"))
(* Fixed-count experiments use the same complete calibration history in both
   selections, even if an earlier doubling already exceeds the time target. *)
val iterations = Option.map (fn s => valOf (Int.fromString s))
                            (OS.Process.getEnv "PERF_ITERATIONS")
fun powerOfTwo n = n = 1 orelse
                  (n > 1 andalso n mod 2 = 0 andalso powerOfTwo (n div 2))
val _ = required (case iterations of NONE => true | SOME n =>
                  n <= 1073741824 andalso powerOfTwo n)
val _ = required (Lib.mem label cases andalso Lib.mem size sizes andalso
                  samples > 0 andalso Real.isFinite seconds andalso
                  seconds > 0.0)
val sink = ref 0
fun consume () = sink := !sink + 1
fun repeat n f = if n = 0 then () else (f (); repeat (n-1) f)
fun real x = Real.fmt (StringCvt.SCI (SOME 12)) x
fun emit key fields = Paired.observe key (String.concatWith "," fields)
fun measure n f = let
  val old = !sink
  val timer = Timer.startCPUTimer ()
  val walltimer = Timer.startRealTimer ()
  val _ = repeat n f
  val {nongc={usr,sys},gc={usr=gu,sys=gs}} = Timer.checkCPUTimes timer
  val {usr=cu,sys=cs} = Timer.checkCPUTimer timer
  val gc = Timer.checkGCTime timer
  val wall = Time.toReal (Timer.checkRealTimer walltimer)
  val times = map Time.toReal [usr,sys,gu,gs,cu,cs,gc]
  val _ = required (wall > 0.0 andalso List.all (fn t => t >= 0.0) times)
  val _ = required (Real.abs
    (Time.toReal cu - Time.toReal usr - Time.toReal gu) < 0.02)
  val _ = required (Real.abs
    (Time.toReal cs - Time.toReal sys - Time.toReal gs) < 0.02)
  (* Poly/ML CPU includes GC; checkGCTime reports GC USER only. *)
  val _ = required (Real.abs (Time.toReal gc - Time.toReal gu) < 0.02)
in (wall,map real (wall :: times) @ [Int.toString (!sink-old)]) end
val (_,accounting) = measure 5 (fn () => (PolyML.fullGC (); consume ()))
val _ = emit "timer.accounting" accounting
val _ = Paired.check "timer accounting" true
val {run,verify,beforeBatch,afterBatch} = workload label size
(* Exercise the initial retained result, including every proof's complete
   hypothesis set, before claiming that the workload inputs are valid. *)
val _ = verify ()
val _ = Paired.check "workload inputs" true
fun step () = (run (); consume ())
fun measured stage count = let
  val _ = PolyML.fullGC ()
  val _ = beforeBatch ()
  val snapshot = RuntimeMetrics.beforeBatch ()
  val result = measure count step
  val _ = RuntimeMetrics.afterBatch (stage,count,snapshot)
  val _ = afterBatch count
  (* Verification can spend bounded quotas or invoke collectors. Snapshot
     counts BEFORE verification, then re-anchor the next batch. Every run
     stores a fresh result except the explicitly named reuse workloads. *)
  val _ = verify ()
in result end
fun calibrate count = let
  val (wall,fields) = measured "calibration" count
  val _ = emit ("calibration." ^ label) (Int.toString count :: fields)
  val finished = case iterations of NONE => wall >= seconds
                                 | SOME n => count = n
in if finished then (required (wall >= seconds); count) else
     (required (count < 1073741824); calibrate (count * 2)) end
(* Compile the entire driver BEFORE executing calibration. A top-level
   [val count = calibrate 1] followed by [fun sample ... count ...] lets the
   compiler embed the measured count and allocates compiler data between
   calibration and sampling. The count here is a runtime local instead. *)
fun experiment () = let
  val count = calibrate 1
  fun sample i = let
    val (_,fields) = measured "sample" count
    val _ = emit ("batch." ^ label)
      (Int.toString i :: Int.toString count :: fields)
  in Paired.check ("results " ^ label) true end
in List.app sample (List.tabulate (samples,I)) end
val _ = experiment ()
val _ = emit "sink" [Int.toString (!sink)]
(* Optional graph evidence has its own prefix and schema, deliberately not
   an extra Paired event. Timings above still have consumption exactly one.
   These are reachable words, NOT allocated bytes, RSS or total live heap. *)
val _ = (!rawStorage) ()
val _ = if label = "storage_graph" then
          ignore (RuntimeMetrics.release ()) else ()
