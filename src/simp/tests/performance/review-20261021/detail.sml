open HolKernel boolLib simpLib boolSimps
val _ = new_theory "reviewbench"
val sink = ref 0
fun repeat n f = if n <= 0 then () else (f (); repeat (n-1) f)
fun measure n f = let
  val timer = Timer.startCPUTimer ()
  val walltimer = Timer.startRealTimer ()
  val _ = repeat n f
  val {usr,sys} = Timer.checkCPUTimer timer
  val gc = Time.toReal (Timer.checkGCTime timer)
  val wall = Time.toReal (Timer.checkRealTimer walltimer)
in {cpu=Time.toReal (Time.+ (usr,sys)),gc=gc,wall=wall} end
fun bench label f = let
  fun calibrate n = if #wall (measure n f) >= 0.15 then n else calibrate (n*2)
  val n = calibrate 1
  val samples = List.tabulate (5,fn _ => (PolyML.fullGC (); measure n f))
  fun median get = List.nth(Listsort.sort Real.compare (map get samples),2) / Real.fromInt n
in print ("DETAIL " ^ label ^ " cpu=" ^ Real.toString (median #cpu) ^
          " gc=" ^ Real.toString (median #gc) ^ " wall=" ^
          Real.toString (median #wall) ^ " reps=" ^ Int.toString n ^ "\n") end
fun use_th th = sink := !sink + length (hyp th)
val rules = List.tabulate (1000, fn i => let
  val name = "r" ^ Int.toString i
  val _ = new_constant (name,bool)
  val c = mk_const (name,bool)
in ASSUME (mk_eq (c,T)) end)
val ten = List.take (rules,10)
val hundred = List.take (rules,100)
val target = lhs (concl (hd rules))
val atom = mk_var ("absent",bool)
val f10 = rewrites ten
val f1000 = rewrites rules
val ss10 = pureSimps.pure_ss ++ f10
val ss1000 = pureSimps.pure_ss ++ f1000
val named = name_ss "kept" f1000
val removable = name_ss "removed" (rewrites [boolTheory.TRUTH])
val replay = pureSimps.pure_ss ++ named ++ removable
val recursive = List.foldl (fn (_,t) => mk_conj(T,t)) atom (List.tabulate(100, I))
val stored_conv = Traverse.TRAVERSE (traversedata_for_ss ss1000) []
val bool_conv = Traverse.TRAVERSE (traversedata_for_ss bool_ss) []
fun countfrag frag = sink := !sink + length (frag_rewrites frag)
fun countss ss = sink := !sink + length (ssfrags_of ss)
fun run_tac tac g = let val (gs,_) = testutils.runtac tac g
                   in sink := !sink + length gs end
val _ = print ("SIZE empty=" ^ Int.toString (PolyML.objSize pureSimps.pure_ss) ^
  " frag1000=" ^ Int.toString (PolyML.objSize f1000) ^
  " ss1000=" ^ Int.toString (PolyML.objSize ss1000) ^ "\n")
val _ = bench "rewrites_1000" (fn () => countfrag (rewrites rules))
val _ = bench "merge_frags_1000" (fn () => countfrag (merge_ss [f1000]))
val _ = bench "compile_1000" (fn () => countss (pureSimps.pure_ss ++ f1000))
val _ = bench "delete_missing_1000" (fn () => countss (ss1000 -* ["missing"]))
val _ = bench "replay_1000" (fn () => countss (remove_ssfrags ["removed"] replay))
val _ = bench "simp_supplied_1000" (fn () => use_th (SIMP_CONV pureSimps.pure_ss rules target))
val _ = bench "asm_simp_supplied_1000" (fn () => run_tac (ASM_SIMP_TAC pureSimps.pure_ss rules) ([],target))
val _ = bench "raw_reuse_bool_depth100" (fn () => use_th (bool_conv recursive))
val _ = print ("SINK " ^ Int.toString (!sink) ^ "\n")
val _ = OS.Process.exit OS.Process.success
