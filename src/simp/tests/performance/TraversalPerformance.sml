(* Direct legacy Traverse.REDUCER probes. No simpLib projections, rewrite
   nets, Cond_rewr, extension APIs, or production instrumentation. *)
open HolKernel boolSyntax Conv Paired
val _ = new_theory "traversal_performance"
fun required b = if b then () else raise Fail "invalid traversal benchmark"
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
  (* Callback increments are timed. Fold them into the checked sink only
     here, so batch-end exercises do not contaminate measured consumption. *)
  val _ = consume (!callbacks - beforeCallbacks)
in (wall, map real (wall :: times) @ [Int.toString (!sink - beforeSink)])
end
(* Same inclusive/non-GC/GC accounting control as Performance.sml. *)
val (_, accounting) = measure 5 (fn () => (PolyML.fullGC (); consume 1))
val _ = emit "timer.accounting" accounting
val _ = Paired.check "timer accounting" true

val a = mk_var ("traverse_a",bool)
val b = mk_var ("traverse_b",bool)
val c = mk_var ("traverse_c",bool)
val miss = mk_var ("traverse_miss",bool)
val ab = ASSUME (mk_eq (a,b))
val bc = ASSUME (mk_eq (b,c))
val missExpected = REFL miss
exception Context of thm
val reducer = Traverse.REDUCER
  {name=SOME "direct equation",initial=Context ab,
   addcontext=fn (Context _,[th]) => (callback (); Context th)
     | _ => raise Fail "wrong collector context",
   apply=fn {context,...} =>
     case context of
         Context th => let val target = lhs (concl th)
           in fn tm => if aconv tm target then th else NO_CONV tm end
       | _ => raise Fail "lost collector context"}
(* No descent for atom probes; deliberately no representation work. *)
val atomRules = Travrules.TRAVRULES
  {relations=[Travrules.EQ_preorder],congprocs=[],weakenprocs=[]}
fun data rules : Traverse.traverse_data =
  {rewriters=[reducer],dprocs=[],limit=NONE,relation=equality,
   travrules=rules}
val atomData = data atomRules
val facts = [bc]
fun verify expected th =
  required (aconv (concl th) (concl expected) andalso
            HOLset.equal (hypset th,hypset expected))
fun use expected th = (verify expected th; consume 1)
val empty = Traverse.TRAVERSE atomData []
val contextual = Traverse.TRAVERSE atomData facts
(* Raw traversal may signal no change; totalize only the saved miss probe. *)
val missing = QCONV (TRY_CONV contextual)
val _ = verify ab (empty a)
val _ = verify bc (contextual b)
val _ = verify missExpected (missing miss)

(* A unary spine visits exactly depth+1 nodes, not the function heads.
   One relation selection and depth+1 per-context factories are consumed.
   The congruence actually uses the depther and produces a kernel proof. *)
val depth = 64
val g = mk_var ("traverse_g",bool --> bool)
fun spine 0 tm = tm | spine n tm = mk_comb (g,spine (n-1) tm)
val deepInput = spine depth a
val deepExpected = funpow depth (fn th => MK_COMB (REFL g,th)) ab
val factory : Opening.congproc = fn rel =>
  (required (aconv rel equality); callback ();
   fn {depther,...} =>
     (callback ();
      fn tm => if is_comb tm then
        MK_COMB (REFL (rator tm),depther ([],equality) (rand tm))
      else NO_CONV tm))
val deepRules = Travrules.TRAVRULES
  {relations=[Travrules.EQ_preorder],congprocs=[factory],weakenprocs=[]}
val deep = Traverse.TRAVERSE (data deepRules) []
val _ = Paired.check "workload inputs"
  (length (hyp deepExpected) = 1 andalso
   aconv (lhs (concl deepExpected)) deepInput)

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
val slot = ref empty
val _ = bench "construct_empty"
  (fn () => (slot := Traverse.TRAVERSE atomData []; consume 1))
  (fn () => verify ab ((!slot) a))
val _ = bench "construct_context"
  (fn () => (slot := Traverse.TRAVERSE atomData facts; consume 1))
  (fn () => verify bc ((!slot) b))
val _ = bench "reuse_hit" (fn () => use bc (contextual b)) (fn () => ())
val _ = bench "reuse_miss"
  (fn () => use missExpected (missing miss)) (fn () => ())
val _ = bench "complete_context"
  (fn () => use bc (Traverse.TRAVERSE atomData facts b)) (fn () => ())
val _ = bench "deep_factory_64"
  (fn () => use deepExpected (deep deepInput)) (fn () => ())
val _ = emit "sink" [Int.toString (!sink)]
