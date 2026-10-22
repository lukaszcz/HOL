(* Fixed identical schedules; construction, reuse and complete are distinct.
   No adaptive candidate-specific schedule or unconsumed function result. *)
open HolKernel Paired TacticInputs
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
val selected = case OS.Process.getEnv "PERF_ROWS" of
    NONE => keys
  | SOME text => String.fields (fn c => c = #",") text
val _ = required (not (null selected) andalso
  selected = List.filter (fn key => List.exists (fn k => k = key) selected)
                         keys)
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
val accounting = measure 5 (fn () => (PolyML.fullGC (); consume ()))
val _ = emit "timer.accounting" accounting
val _ = Paired.check "timer accounting" true
fun bench n ({label,run,verify}:workload) = let
  val key = label ^ "." ^ Int.toString n
  val count = #2 (valOf (List.find (fn (k,_) => k = key) fixed))
  fun step () = (run (); consume ())
  fun batch phase i = let
    val _ = PolyML.fullGC ()
    val old = [!constructs,!applications,!validations]
    val fields = measure count step
    (* Anchor before consuming constructed closures outside the timer. *)
    val actual = ListPair.map (op -)
      ([!constructs,!applications,!validations],old)
    val _ = verify ()
    val _ = emit (phase ^ "." ^ key)
      ((if phase = "batch" then [Int.toString i] else []) @
       [Int.toString count] @ fields)
    val _ = emit ("stages." ^ phase ^ "." ^ key)
      (map Int.toString actual)
  in Paired.check (phase ^ " results " ^ key) true end
  val _ = batch "calibration" 0
in List.app (batch "batch") (List.tabulate (samples,I)) end
val _ = List.app (fn n => List.app (fn (w:workload) =>
  if List.exists (fn key => key = #label w ^ "." ^ Int.toString n) selected
  then bench n w else ()) (workloads n)) sizes
val _ = emit "sink" [Int.toString (!sink)]
val _ = Paired.observe "complete" "TASK18-tactic-performance-v1"
