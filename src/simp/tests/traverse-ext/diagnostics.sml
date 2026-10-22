(* Construction/reuse diagnostics only, not a performance acceptance gate.
   Execute separately after builds. Results and callback counts are consumed. *)
open HolKernel Parse boolLib
val n = 20000
val a = ``ext_diagnostic_a:bool``
val b = ``ext_diagnostic_b:bool``
val ab = ASSUME (boolSyntax.mk_eq (a,b))
val collected = ref 0
val applied = ref 0
exception Context
val ordinary = Traverse.REDUCER
  {name=NONE,initial=Context,
   addcontext=fn (ctxt,_) => (collected := !collected + 1; ctxt),
   apply=fn _ => fn tm =>
     (applied := !applied + 1;
      if aconv tm a then ab else NO_CONV tm)}
val rules = Travrules.TRAVRULES
  {relations=[Travrules.EQ_preorder],congprocs=[],weakenprocs=[]}
val old_data : Traverse.traverse_data =
  {rewriters=[ordinary],dprocs=[],limit=NONE,
   travrules=rules,relation=boolSyntax.equality}
val new_data : TraverseExt.traverse_data =
  {rewriters=[TraverseExt.lift ordinary],dprocs=[],limit=NONE,
   travrules=rules,relation=boolSyntax.equality}
val builders =
  [("ordinary-default",Traverse.TRAVERSE old_data,false),
   ("extended-default",TraverseExt.TRAVERSE new_data,false),
   (* TASK_11 removes the old mixed-refresh route: restored Traverse has
      no configured engine. The remaining routes keep all result/count
      assertions below; configured refresh belongs only to TraverseExt. *)
   ("extended-refresh",TraverseExt.XTRAVERSE
      (new_data,TraverseExt.default_config),true)]
fun require ok = if ok then () else raise Fail "diagnostic result/count"
fun consume cv = let val th = cv a in
  require (aconv (concl th) (concl ab) andalso
           HOLset.equal (hypset th,hypset ab))
end
fun timed f = let
  val cpu = Timer.startCPUTimer ()
  val wall = Timer.startRealTimer ()
  val result = f ()
  val elapsed = Timer.checkRealTimer wall
  val {usr,sys} = Timer.checkCPUTimer cpu
in
  (result,"usr=" ^ Time.toString usr ^ " sys=" ^ Time.toString sys ^
          " wall=" ^ Time.toString elapsed)
end
fun run (label,build,refresh) = let
  val _ = (collected := 0; applied := 0)
  val (conversions,construction) = timed
    (fn () => List.tabulate (n,fn _ => build [TRUTH]))
  val initial = !collected
  val _ = require (initial = (if refresh then 0 else n) andalso !applied = 0)
  val _ = List.app consume conversions
  val _ = require (!collected = n andalso !applied = 2*n)
  val _ = (collected := 0; applied := 0)
  val saved = build [TRUTH]
  val ((),reuse) = timed
    (fn () => List.app (fn _ => consume saved) (List.tabulate (n,fn i => i)))
  val _ = require (!collected = (if refresh then n else 1) andalso
                   !applied = 2*n)
in
  print (label ^ " n=" ^ Int.toString n ^ " construction " ^
         construction ^ " initial-collect=" ^ Int.toString initial ^ "\n");
  print (label ^ " n=" ^ Int.toString n ^ " reuse " ^ reuse ^
         " collect=" ^ Int.toString (!collected) ^
         " apply=" ^ Int.toString (!applied) ^ "\n")
end
val _ = List.app run builders
val _ = print "TraverseExt construction/reuse diagnostics complete\n"
val _ = OS.Process.exit OS.Process.success
