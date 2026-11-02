(* TASK28 ordinary client probes. One PERF_CASE/PERF_SIZE per process.
   All construction outputs escape through typed refs and are exercised after
   each batch. Proof reconstruction is timed for application/complete cases.
   This is source isolation, not fresh-load or independent-build evidence. *)
open HolKernel boolLib simpLib Paired
val _ = new_theory "task28_client_performance"
fun required b = if b then () else raise Fail "invalid client benchmark"
fun integer key = valOf (Int.fromString (Paired.env key))
val selected = Paired.env "PERF_CASE"
val workloadSize = integer "PERF_SIZE"
val samples = integer "PERF_SAMPLES"
val seconds = valOf (Real.fromString (Paired.env "PERF_SECONDS"))
val fixedIterations = Option.map (fn s => valOf (Int.fromString s))
                                 (OS.Process.getEnv "PERF_ITERATIONS")
(* The fixed-count schedule is [ramp] (no PERF_SCHEDULE: every count 1, 2, 4,
   ..., N, a power of two) or [warmup] (one batch of exactly N, any N, then
   the samples). *)
val schedule = OS.Process.getEnv "PERF_SCHEDULE"
val warmup = schedule = SOME "warmup"
fun powerOfTwo n = n = 1 orelse
                  (n > 1 andalso n mod 2 = 0 andalso powerOfTwo (n div 2))
val _ = required (schedule = NONE orelse warmup)
val _ = required (case fixedIterations of NONE => not warmup | SOME n =>
                  n >= 1 andalso n <= 1073741824 andalso
                  (warmup orelse powerOfTwo n))
val _ = required (workloadSize >= 0 andalso workloadSize <= 10000 andalso
                  samples > 0 andalso Real.isFinite seconds andalso
                  seconds > 0.0)
val sink = ref 0
fun consume () = sink := !sink + 1
fun repeat n f = if n = 0 then () else (f (); repeat (n-1) f)
fun real x = Real.fmt (StringCvt.SCI (SOME 12)) x
fun emit key fields = Paired.observe key (String.concatWith "," fields)
fun same expected actual =
  aconv (concl expected) (concl actual) andalso
  HOLset.equal (hypset expected,hypset actual)
fun verify expected actual =
  required (same expected actual andalso
    List.all (fn s => s = "DISK_THM") (#1 (Tag.dest_tag (tag actual))))
type workload = {run:unit -> unit, verify:unit -> unit}

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
in (wall,map real (wall :: times) @ [Int.toString (!sink-old)]) end
val (_,accounting) = measure 5 (fn () => (PolyML.fullGC (); consume ()))
val _ = emit "timer.accounting" accounting
val _ = Paired.check "timer accounting" true

(* No theorem is discarded: even pure construction stores the last closure;
   reuse and complete retain the last proof and verify it after every batch. *)
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
in {run=run,verify=check} end

(* Direct REDUCER setup, with a genuine private context and kernel-proved
   congruence descent. Weakening is a separately selected low-priority path. *)
fun traversal name n : workload = let
  val a = mk_var ("client_a",bool)
  val b = mk_var ("client_b",bool)
  val c = mk_var ("client_c",bool)
  val miss = mk_var ("client_miss",bool)
  val ab = ASSUME (mk_eq (a,b))
  val bc = ASSUME (mk_eq (b,c))
  exception Context of thm
  val ordinary = Traverse.REDUCER
    {name=SOME "equation",initial=Context ab,
     addcontext=fn (_, [th]) => Context th
       | (ctxt,[]) => ctxt
       | _ => raise Fail "unexpected collector facts",
     apply=fn {context,...} => case context of
       Context th => fn tm =>
         if aconv tm (lhs (concl th)) then th else NO_CONV tm
     | _ => raise Fail "lost private collector context"}
  val g = mk_var ("client_g",bool --> bool)
  fun spine 0 tm = tm | spine k tm = mk_comb (g,spine (k-1) tm)
  val descend : Opening.congproc = fn rel =>
    (required (aconv rel boolSyntax.equality);
     fn {depther,...} => fn tm =>
       if is_comb tm then
         MK_COMB (REFL (rator tm),depther ([],boolSyntax.equality) (rand tm))
       else NO_CONV tm)
  val weak : Opening.congproc = fn _ => fn _ => fn tm =>
    if aconv tm a then ab else NO_CONV tm
  (* Two identical side conditions are solved via the actual traversal
     continuation, not a precomputed external solver. The rule and condition
     hypotheses both survive. *)
  val condition = mk_var ("client_condition",bool)
  val conditionEq = EQT_INTRO (ASSUME condition)
  val conditional = DISCH condition ab
  val guarded = Traverse.REDUCER
    {name=SOME "repeated side conditions",initial=Context ab,
     addcontext=fn (ctxt,_) => ctxt,
     apply=fn {solver,stack,...} => fn tm =>
       if aconv tm condition then conditionEq
       else if aconv tm a then let
         val first = solver (condition :: stack) condition
         val second = solver (condition :: stack) condition
       in CONJUNCT1 (CONJ (MP conditional first) second) end
       else NO_CONV tm}
  val failed = Traverse.REDUCER
    {name=SOME "failed condition",initial=Context ab,
     addcontext=fn (ctxt,_) => ctxt,
     apply=fn {solver,stack,...} => fn tm =>
       if aconv tm a then
         (ignore (solver (miss :: stack) miss); NO_CONV tm)
       else NO_CONV tm}
  fun make reducers congs weaks facts () =
    QCONV (TRY_CONV (Traverse.TRAVERSE
      {rewriters=reducers,dprocs=[],limit=NONE,
       relation=boolSyntax.equality,
       travrules=Travrules.TRAVRULES
         {relations=[Travrules.EQ_preorder],congprocs=congs,
          weakenprocs=weaks}} facts))
  val atom = make [ordinary] [] [] []
  val contextual = make [ordinary] [] [] [bc]
  val deep = make [ordinary] [descend] [] []
  val deepExpected = funpow n (fn th => MK_COMB (REFL g,th)) ab
in case name of
    "traversal_construct" => conversion "construct" atom a ab
  | "traversal_context_construct" =>
      conversion "construct" contextual b bc
  | "traversal_complete" => conversion "complete" contextual b bc
  | "traversal_reuse_hit" => conversion "reuse" contextual b bc
  | "traversal_reuse_miss" => conversion "reuse" contextual miss (REFL miss)
  | "traversal_deep" => conversion "reuse" deep (spine n a) deepExpected
  | "traversal_congruence" =>
      conversion "complete" deep (spine n a) deepExpected
  | "traversal_weakening" =>
      conversion "reuse" (make [] [] [weak] []) a ab
  | "traversal_side_conditions" =>
      conversion "reuse" (make [guarded] [descend] [] [])
        (spine n a)
        (funpow n (fn th => MK_COMB (REFL g,th))
          (ADD_ASSUM condition ab))
  | "traversal_failed_candidates" =>
      conversion "reuse" (make [failed,ordinary] [descend] [] [])
        (spine n a) deepExpected
  | "traversal_saved" => conversion "reuse" deep (spine n a) deepExpected
  | _ => raise Fail ("unknown traversal case: " ^ name)
end

(* Each tactic run reconstructs the proof with its actual returned validation.
   Both exact hypotheses and ordered residual assumptions/goals are checked. *)
fun tacticWork oper stage installed n : workload = let
  val p = mk_var ("client_p",bool)
  val target = mk_conj (p,T)
  val rule = REWRITE_CONV [boolTheory.AND_CLAUSES] target
  val extras = List.tabulate (n,fn i =>
    mk_var ("client_extra" ^ Int.toString i,bool))
  val asl = p :: extras
  val goal = (asl,target)
  val ss = if installed then pureSimps.pure_ss ++ rewrites [rule]
           else pureSimps.pure_ss
  val args = if installed then [] else [rule]
  val cfg = {strip=false,elimvars=false,droptrues=false,oldestfirst=true}
  fun make () = case oper of
      "supplied" => SIMP_TAC ss args
    | "installed" => SIMP_TAC ss args
    | "asm" => ASM_SIMP_TAC ss args
    | "full" => FULL_SIMP_TAC ss args
    | "reverse" => REV_FULL_SIMP_TAC ss args
    | "no_strip_full" => NO_STRIP_FULL_SIMP_TAC ss args
    | "no_strip_reverse" => NO_STRIP_REV_FULL_SIMP_TAC ss args
    | "global" => global_simp_tac cfg ss args
    | "req0" => global_simp_tac cfg ss [Req0 rule]
    | "reqD" => global_simp_tac cfg ss [ReqD rule]
    | "req0_reqD" => global_simp_tac cfg ss [Req0 (ReqD rule)]
    | "reqD_req0" => global_simp_tac cfg ss [ReqD (Req0 rule)]
    | _ => raise Fail ("unknown tactic operation: " ^ oper)
  val slot = ref (make ())
  val expected =
    if List.exists (fn s => s = oper)
         ["supplied","installed","asm","global","req0","reqD",
          "req0_reqD","reqD_req0"] then CONJ (ASSUME p) TRUTH
    else List.foldl (fn (t,th) => ADD_ASSUM t th)
           (CONJ (ASSUME p) TRUTH) extras
  val proof = ref expected
  val residual = ref ([] : Abbrev.goal list)
  fun solve (assumptions,w) = let
    fun go t = case List.find (aconv t) assumptions of
        SOME a => ASSUME a
      | NONE => if aconv t T then TRUTH
        else if is_conj t then CONJ (go (lhand t)) (go (rand t))
        else raise Fail "unprovable client residual"
  in go w end
  fun apply () = let
    val (gs,vf) = testutils.runtac (!slot) goal
    val th = vf (map solve gs)
  in residual := gs; proof := th end
  fun check () = let
    val _ = if stage = "construct" then apply () else ()
    val _ = verify expected (!proof)
    val _ = if oper = "supplied" orelse oper = "installed" then
      required (case !residual of [(assumptions,w)] =>
        ListPair.allEq (fn (a,b) => aconv a b) (assumptions,asl) andalso
        aconv w p | _ => false)
      else required (null (!residual))
  in () end
  fun run () =
    (case stage of
       "construct" => slot := make ()
     | "reuse" => apply ()
     | "complete" => (slot := make (); apply ())
     | _ => raise Fail "unknown tactic stage";
     consume ())
  val _ = apply ()
  val _ = check ()
in {run=run,verify=check} end

(* Directional passes retain ordered residual dependencies, not just a closed
   boolean endpoint. This is separate from the full-pass closing workloads. *)
fun dependencyWork reverse stage n : workload = let
  val p = mk_var ("client_dep_p",bool)
  val q = mk_var ("client_dep_q",bool)
  val r = mk_var ("client_dep_r",bool)
  val pq = mk_eq (p,q)
  val qr = mk_eq (q,r)
  val pr = mk_eq (p,r)
  val identity = mk_eq (r,r)
  val extras = List.tabulate (n,fn i =>
    mk_var ("client_dep_extra" ^ Int.toString i,bool))
  val asl = [pq,qr] @ extras
  val want = (if reverse then [pr,qr] else [pq,qr]) @ extras
  fun make () =
    (if reverse then NO_STRIP_REV_FULL_SIMP_TAC else NO_STRIP_FULL_SIMP_TAC)
      empty_ss []
  val slot = ref (make ())
  val proof = ref (REFL r)
  val residual = ref ([] : Abbrev.goal list)
  val expected = List.foldl (fn (tm,th) => ADD_ASSUM tm th) (REFL r) asl
  fun apply () = let
    val (gs,vf) = testutils.runtac (!slot) (asl,identity)
  in residual := gs; proof := vf (map (fn _ => REFL r) gs) end
  fun check () =
    (if stage = "construct" then apply () else ();
     verify expected (!proof);
     required (case !residual of [(assumptions,w)] =>
       ListPair.allEq (fn (a,b) => aconv a b) (assumptions,want) andalso
       aconv w identity | _ => false))
  fun run () =
    (case stage of
       "construct" => slot := make ()
     | "reuse" => apply ()
     | "complete" => (slot := make (); apply ())
     | _ => raise Fail "unknown dependency stage";
     consume ())
  val _ = apply ()
  val _ = check ()
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
    in {run=run,verify=fn () => verify expected (!proof)} end
  | _ => raise Fail ("unknown downstream case: " ^ name)
end

fun choose () =
  if String.isPrefix "traversal_" selected then
    traversal selected workloadSize
  else if String.isPrefix "downstream_" selected then
    downstream selected workloadSize
  else let
    val choices = List.concat (map (fn oper => map (fn stage =>
      ("tactic_" ^ String.map Char.toLower oper ^ "_" ^ stage,
       (oper,stage)))
      ["construct","reuse","complete"])
      ["supplied","installed","asm","full","reverse","no_strip_full",
       "no_strip_reverse","global","req0","reqD","req0_reqD","reqD_req0",
       "dependency_full","dependency_reverse"])
    val (oper,stage) = case List.find (fn (key,_) => key = selected) choices of
        SOME (_,value) => value
      | NONE => raise Fail ("unknown client PERF_CASE: " ^ selected)
  in if oper = "dependency_full" orelse oper = "dependency_reverse" then
       dependencyWork (oper = "dependency_reverse") stage workloadSize
     else tacticWork oper stage (oper = "installed") workloadSize end
val {run,verify=check} = choose ()
val _ = check ()
val _ = Paired.check "workload inputs" true
fun measured stage count = let
  val _ = PolyML.fullGC ()
  val snapshot = RuntimeMetrics.beforeBatch ()
  val result = measure count run
  val _ = RuntimeMetrics.afterBatch (stage,count,snapshot)
  val _ = check ()
in result end
fun calibrate count = let
  val (wall,fields) = measured "calibration" count
  val _ = emit ("calibration." ^ selected) (Int.toString count :: fields)
  val finished = case fixedIterations of NONE => wall >= seconds
                                      | SOME n => count = n
in if finished then (required (wall >= seconds); count) else
     (required (count < 1073741824); calibrate (count*2)) end
(* The warm-up batch is not a sample: it has its own observation key, and the
   runtime record of the fixture for it is a calibration record. It must last
   at least half the target seconds, as every sample must (the validator
   checks the samples), else the experiment fails; it never recalibrates. *)
fun warm count = let
  val (wall,fields) = measured "calibration" count
  val _ = emit ("warmup." ^ selected) (Int.toString count :: fields)
in (required (wall >= seconds / 2.0); count) end
(* Keep calibration and samples in one precompiled driver, as in the fragment
   fixture. No compiler invocation may intervene after calibration starts. *)
fun experiment () = let
  val iterations =
    if warmup then warm (valOf fixedIterations) else calibrate 1
  fun sample i = let
    val (_,fields) = measured "sample" iterations
    val _ = emit ("batch." ^ selected)
      (Int.toString i :: Int.toString iterations :: fields)
  in Paired.check ("results " ^ selected) true end
in List.app sample (List.tabulate (samples,I)) end
val _ = experiment ()
val _ = emit "sink" [Int.toString (!sink)]
