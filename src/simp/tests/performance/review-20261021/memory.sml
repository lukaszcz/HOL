open HolKernel boolLib simpLib boolSimps
val _ = new_theory "reviewbench"
val sink = ref 0
fun repeat n f = if n <= 0 then () else (f (); repeat (n-1) f)
fun measure n f = let
  val timer = Timer.startCPUTimer ()
  val _ = repeat n f
  val {usr,sys} = Timer.checkCPUTimer timer
in Time.toReal (Time.+ (usr,sys)) end
fun bench label f = let
  fun calibrate n = if measure n f >= 0.15 then n else calibrate (n*2)
  val n = calibrate 1
  val samples = List.tabulate (5,fn _ => (PolyML.fullGC (); measure n f))
  val med = List.nth (Listsort.sort Real.compare samples,2)
in print ("BENCH " ^ label ^ " " ^ Real.toString (med / Real.fromInt n) ^
          " reps=" ^ Int.toString n ^ " samples=" ^
          String.concatWith "," (map Real.toString samples) ^ "\n") end
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
fun report n = let
  val frag = rewrites (List.take(rules,n))
  val ss = pureSimps.pure_ss ++ frag
  val anchor = PolyML.objSize (pureSimps.pure_ss,frag)
  val with_result = PolyML.objSize (ss,pureSimps.pure_ss,frag)
in print("MEMORY " ^ Int.toString n ^ " " ^ Int.toString (with_result-anchor) ^ "\n") end
val _ = List.app report [0,10,100,1000]
val _ = OS.Process.exit OS.Process.success
