(* TASK31 cumulative-allocation fixture for the ClientPerformance cases,
   installed as Performance.sml in the place of MatrixAllocation.sml; the
   driver below is MatrixAllocation.sml's from its "Build every foreign
   closure" comment on, word for word (test_allocation_task.py compares
   them), and MatrixSupport.sml supplies the work phase. One case and one
   size per fresh process; needs the private patched runtime and
   TASK29_ALLOC_SHIM like MatrixAllocation.sml.

   The workloads are those of ClientPerformance.sml: the text from `sink`
   to `dependencyWork` and `choose` is copied from it, line for line (the
   test checks that too), and the only additions are the lines that end
   in a comment saying alloc: each calls `retaining`, which gives the work
   phase the result to fingerprint (the retained theorem, and the residual
   goals of a tactic) and a use of it (apply the retained conversion or
   tactic again).
   The timed closures, `run` and `verify`, are the ones of the timing
   fixture, so the operation and apply words are those of the clients.
   Not copied: the timing driver (batches, calibration, RuntimeMetrics) and
   `downstream`, whose cases belong to TASK_32/33. *)
open HolKernel boolLib simpLib Paired
val _ = new_theory "task31_client_allocation"
val required = MatrixSupport.required
val retaining = MatrixSupport.retaining
val thmText = MatrixSupport.thmText
val goalText = MatrixSupport.goalText
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
  val _ = retaining                                            (*alloc*)
    (fn () => thmText (!proof) ^ "|" ^                         (*alloc*)
       String.concatWith ";" (map goalText (!residual)))       (*alloc*)
    (fn () => apply ())                                        (*alloc*)
in {run=run,verify=check} end

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
  val _ = retaining                                            (*alloc*)
    (fn () => thmText (!proof) ^ "|" ^                         (*alloc*)
       String.concatWith ";" (map goalText (!residual)))       (*alloc*)
    (fn () => apply ())                                        (*alloc*)
in {run=run,verify=check} end

fun choose () =
  if String.isPrefix "traversal_" selected then
    traversal selected workloadSize
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
