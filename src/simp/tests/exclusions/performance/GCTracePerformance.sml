(* Separate GC diagnosis: unchanged full matrix and verification. Statistics
   snapshots OUTSIDE timers. Longer common schedule is sealed by the runner.
   sizeAllocationFree is GC-updated, NOT a cumulative allocation counter. *)
open HolKernel Paired ExclusionInputs
val samples = valOf (Int.fromString (Paired.env "PERF_SAMPLES"))
val keys = List.concat (map (fn n => map (fn label =>
  label ^ "." ^ Int.toString n) labels) sizes)
fun parseFixed text = let
  fun entry text = case String.fields (fn c => c = #"=") text of
      [key,value] => let
        val _ = required (size value > 0 andalso
                          CharVector.all Char.isDigit value)
        val count = valOf (Int.fromString value)
        val _ = required (count > 0 andalso count <= 1073741824)
      in (key,count) end
    | _ => raise Fail "malformed PERF_FIXED"
  val entries = map entry (String.fields (fn c => c = #",") text)
  val _ = required (samples >= 3 andalso length entries = length keys andalso
    List.all (fn key => length (List.filter
      (fn (k,_) => k = key) entries) = 1) keys)
in entries end
val fixed = parseFixed (Paired.env "PERF_FIXED")
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
  val _ = required (Real.abs (Time.toReal gc - Time.toReal gu) < 0.02)
in map real (wall :: times) @ [Int.toString (!sink-old)] end
fun stats () = let
  val s = PolyML.Statistics.getLocalStats ()
in map Int.toString [#gcFullGCs s, #gcPartialGCs s, #gcSharePasses s] @
   map LargeInt.toString [#sizeHeap s, #sizeHeapFreeLastFullGC s,
     #sizeHeapFreeLastGC s, #sizeAllocation s, #sizeAllocationFree s,
     #sizeCode s, #sizeStacks s]
end
val accounting = measure 5 (fn () => (PolyML.fullGC (); consume ()))
val _ = emit "timer.accounting" accounting
val _ = Paired.check "timer accounting" true
fun bench n ({label,build,verify,makers,collectors}:workload) = let
  val key = label ^ "." ^ Int.toString n
  val count = #2 (valOf (List.find (fn (k,_) => k = key) fixed))
  val slot = ref (build ())
  fun step () = (slot := build (); consume ())
  fun batch phase i = let
    val _ = PolyML.fullGC ()
    val oldM = !makerCalls
    val oldC = !collectorCalls
    val tracekey = phase ^ Int.toString i ^ "." ^ key
    val _ = Paired.observe ("gctrace.begin." ^ tracekey) "begin"
    val prior = stats ()
    val fields = measure count step
    val after = stats ()
    val _ = Paired.observe ("gctrace.end." ^ tracekey) "end"
    val actualM = !makerCalls-oldM
    val actualC = !collectorCalls-oldC
    (* Proof and traversal verification may call callbacks: counts are
       sampled before verification, and each next batch uses new anchors. *)
    val _ = required (actualM = makers * count andalso
                      actualC = collectors * count)
    val _ = verify (!slot)
    val _ = emit (phase ^ "." ^ key)
      ((if phase = "batch" then [Int.toString i] else []) @
       [Int.toString count] @ fields)
    val _ = emit ("callbacks." ^ phase ^ "." ^ key)
      (map Int.toString [actualM,actualC])
    val statkey = "gcstats." ^ phase ^
      (if phase = "batch" then Int.toString i else "") ^ "." ^ key
    val _ = emit (statkey ^ ".before") prior
    val _ = emit (statkey ^ ".after") after
  in Paired.check (phase ^ " results " ^ key) true end
  val _ = batch "calibration" 0
in List.app (batch "batch") (List.tabulate (samples,I)) end
val _ = List.app (fn n => List.app (bench n) (workloads n)) sizes
val _ = emit "sink" [Int.toString (!sink)]
val _ = Paired.observe "complete" "TASK17-exclusion-performance-v1"
