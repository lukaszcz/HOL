(* Construction/update/merge only is timed. Each result escapes to a ref;
   full ordered theorem/name inspection and a kernel proof consume the saved
   result after every calibration and sample, outside construction timing. *)
open HolKernel Paired FragmentInputs
val _ = new_theory "fragment_performance"
val samples = valOf (Int.fromString (Paired.env "PERF_SAMPLES"))
val seconds = valOf (Real.fromString (Paired.env "PERF_SECONDS"))
(* Fixed mode rejects partial, duplicate and unknown schedules before timing.
   Do not call workloads just to enumerate keys: it mutates TypeBase. *)
val labels = ["rewrites", "rewrites_with_names", "named_rewrites",
  "named_rewrites_with_names", "SSFRAG", "update", "add_named_rwt",
  "merge", "merge_duplicate", "merge_named", "named_merge", "ac_create",
  "ac_merge", "type_create", "type_lookup"]
val keys = List.concat (map (fn n =>
  map (fn label => label ^ "." ^ Int.toString n) labels) sizes)
fun parseFixed text = let
  fun entry text =
    case String.fields (fn c => c = #"=") text of
      [key,value] => let
        val _ = required (size value > 0 andalso
                          CharVector.all Char.isDigit value)
        val count = valOf (Int.fromString value)
        val _ = required (count > 0)
      in (key,count) end
    | _ => raise Fail "malformed PERF_FIXED entry"
  val entries = map entry (String.fields (fn c => c = #",") text)
  val _ = required (length entries = length keys andalso
    List.all (fn key => length (List.filter
      (fn (k,_) => k = key) entries) = 1) keys)
in entries end
val fixed = Option.map parseFixed (OS.Process.getEnv "PERF_FIXED")
val sink = ref 0
fun consume () = sink := !sink + 1
fun repeat n f = if n = 0 then () else (f (); repeat (n - 1) f)
fun real x = Real.fmt (StringCvt.SCI (SOME 12)) x
fun emit key fs = Paired.observe key (String.concatWith "," fs)
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
  (* Poly/ML's checkGCTime is GC user, not user+system. Do not add it
     to checkCPUTimer, which already includes GC. *)
  val _ = required (Real.abs (Time.toReal gc - Time.toReal gu) < 0.02)
in (wall,map real (wall :: times) @ [Int.toString (!sink - old)]) end
val (_,accounting) = measure 5 (fn () => (PolyML.fullGC (); consume ()))
val _ = emit "timer.accounting" accounting
val _ = Paired.check "timer accounting" true
fun bench n (w as {label,build,...}:workload) = let
  val key = label ^ "." ^ Int.toString n
  val slot = ref (build ())
  fun step () = (slot := build (); consume ())
  fun check () = (verify w (!slot); proof w (!slot))
  fun calibrate count = let
    val _ = PolyML.fullGC ()
    val (wall,fields) = measure count step
    val _ = check ()
    val _ = emit ("calibration." ^ key) (Int.toString count :: fields)
  in if Option.isSome fixed orelse wall >= seconds then count else
    (required (count < 1073741824); calibrate (count * 2)) end
  val initial = case fixed of NONE => 1 | SOME entries =>
    #2 (valOf (List.find (fn (k,_) => k = key) entries))
  val count = calibrate initial
  fun sample i = let
    val _ = PolyML.fullGC ()
    val (_,fields) = measure count step
    val _ = check ()
    val _ = emit ("batch." ^ key)
      (Int.toString i :: Int.toString count :: fields)
  in Paired.check ("results " ^ key) true end
in List.app sample (List.tabulate (samples,I)) end
val _ = List.app (fn n => List.app (bench n) (workloads n)) sizes
val _ = emit "sink" [Int.toString (!sink)]
