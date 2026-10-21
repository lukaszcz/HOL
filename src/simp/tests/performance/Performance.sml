(* Result-consuming diagnostic probes; no production instrumentation. *)
open HolKernel boolLib simpLib boolSimps Paired
val _ = new_theory "performance_baseline"
fun required b = if b then () else raise Fail "invalid benchmark result"
fun integer s = valOf (Int.fromString (Paired.env s))
val samples = integer "PERF_SAMPLES"
val seconds = valOf (Real.fromString (Paired.env "PERF_SECONDS"))
val sink = ref 0
fun consume n = sink := !sink + n
fun repeat n f = if n = 0 then () else (f (); repeat (n - 1) f)
fun real x = Real.fmt (StringCvt.SCI (SOME 12)) x
fun emit key fields = Paired.observe key (String.concatWith "," fields)
fun measure n f = let
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
in (wall, map real (wall :: times) @ [Int.toString (!sink - beforeSink)])
end
(* Force measurable GC: checkCPUTimer includes GC, checkGCTime is GC USER
   only. Never add it to checkCPUTimer or call it total GC CPU. *)
val (_, accounting) = measure 5 (fn () => (PolyML.fullGC (); consume 1))
val _ = emit "timer.accounting" accounting
val _ = Paired.check "timer accounting" true
val rules = List.tabulate (1000, fn i => let
  val name = "r" ^ Int.toString i
  val _ = new_constant (name,bool)
  val c = mk_const (name,bool)
in ASSUME (mk_eq (c,T)) end)
val target = lhs (concl (hd rules))
val expected = concl (hd rules)
val base = pureSimps.pure_ss
val frag = rewrites rules
val installed = base ++ frag
val projection = traversedata_for_ss installed
val stored = Traverse.TRAVERSE projection []
val _ = Paired.check "workload inputs"
  (length (frag_rewrites frag) = 1000 andalso
   aconv (concl (stored target)) expected)
fun verifyTh th =
  required (aconv (concl th) expected andalso
            length (hyp th) = 1 andalso aconv (hd (hyp th)) expected)
fun verifySS ss = verifyTh (SIMP_CONV ss [] target)
fun verifyFrag f =
  (required (length (frag_rewrites f) = 1000); verifySS (base ++ f))
fun useTh th = (verifyTh th; consume (length (hyp th)))
fun bench label f verify = let
  fun calibration n = let
    val _ = PolyML.fullGC ()
    val (wall, data) = measure n f
    val _ = verify ()
    val _ = emit ("calibration." ^ label) (Int.toString n :: data)
  in if wall >= seconds then n
     else (required (n < 1073741824); calibration (n * 2)) end
  val n = calibration 1
  fun sample i = let
    val _ = PolyML.fullGC ()
    val (_, data) = measure n f
    val _ = verify ()
    val _ = emit ("batch." ^ label)
      (Int.toString i :: Int.toString n :: data)
  in Paired.check ("results " ^ label) true end
in List.app sample (List.tabulate (samples,I)) end
(* Equal-arity roots remove tuple-size artifacts. Also retain the original
   two-root vs three-root method for direct historical comparison. *)
fun storage n = let
  val rs = List.take (rules,n)
  val f = rewrites rs
  val ss = base ++ f
  val _ = if n = 0 then () else verifySS ss
  val _ = PolyML.fullGC ()
  val anchor = PolyML.objSize (base,f,base)
  val result = PolyML.objSize (base,f,ss)
  val historical = PolyML.objSize (ss,base,f) - PolyML.objSize (base,f)
  val fa = PolyML.objSize (base,rs,base)
  val fr = PolyML.objSize (base,rs,f)
  val sizes = [n,PolyML.objSize base,PolyML.objSize f,PolyML.objSize ss,
               anchor,result,result-anchor,historical,fa,fr,fr-fa]
in
  emit "storage" (map Int.toString sizes);
  Paired.check "retained graphs" (result >= anchor andalso fr >= fa)
end
val _ = List.app storage [0,10,100,1000]
val fragSlot = ref frag
val ssSlot = ref installed
val projectionSlot = ref projection
val convSlot = ref stored
val _ = bench "rewrites_1000"
  (fn () => (fragSlot := rewrites rules;
             consume (length (frag_rewrites (!fragSlot)))))
  (fn () => verifyFrag (!fragSlot))
val _ = bench "merge_frags_1000"
  (fn () => (fragSlot := merge_ss [frag];
             consume (length (frag_rewrites (!fragSlot)))))
  (fn () => verifyFrag (!fragSlot))
val _ = bench "compile_1000"
  (fn () => (ssSlot := (base ++ frag); consume (length (ssfrags_of (!ssSlot)))))
  (fn () => verifySS (!ssSlot))
val _ = bench "delete_missing_1000"
  (fn () => (ssSlot := (installed -* ["missing"]);
             consume (length (ssfrags_of (!ssSlot)))))
  (fn () => verifySS (!ssSlot))
val _ = bench "project_1000"
  (fn () => (projectionSlot := traversedata_for_ss installed;
             consume (length (#rewriters (!projectionSlot)))))
  (fn () => verifyTh (Traverse.TRAVERSE (!projectionSlot) [] target))
val _ = bench "construct_traverse_1000"
  (fn () => (convSlot := Traverse.TRAVERSE projection []; consume 1))
  (fn () => verifyTh ((!convSlot) target))
val _ = bench "empty_add_1000"
  (fn () => (ssSlot := (installed ++ empty_ssfrag);
             consume (length (ssfrags_of (!ssSlot)))))
  (fn () => verifySS (!ssSlot))
val _ = bench "simp_installed_1000"
  (fn () => useTh (SIMP_CONV installed [] target)) (fn () => ())
val _ = bench "raw_reuse_1000"
  (fn () => useTh (stored target)) (fn () => ())
val _ = bench "projection_apply_1000"
  (fn () => useTh
    (Traverse.TRAVERSE (traversedata_for_ss installed) [] target))
  (fn () => ())
val _ = bench "compile_apply_1000"
  (fn () => useTh (SIMP_CONV (base ++ frag) [] target)) (fn () => ())
val _ = emit "sink" [Int.toString (!sink)]
