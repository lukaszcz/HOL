(* Additional baseline-only pins; the original 47-case input is unchanged. *)
open HolKernel Parse boolLib simpLib
val _ = new_theory "priorlimits"
val p = ``limits_p:bool``
val q = ``limits_q:bool``
val r = ``limits_r:bool``
val side = ``limits_side:bool``
val unsolved = ``limits_unsolved:bool``
val pq = ASSUME (mk_eq (p,q))
val qr = ASSUME (mk_eq (q,r))
val side_rule = ASSUME (mk_eq (side,unsolved))
val events = ref ([] : string list)
fun record s = events := !events @ [s]
fun same a b = aconv (concl a) (concl b) andalso
  HOLset.equal (hypset a,hypset b)
exception LimitsContext
val reducer = Traverse.REDUCER
  {name=NONE,initial=LimitsContext,addcontext=fn (c,_) => c,
   apply=fn {solver,...} => fn tm =>
     if aconv tm p then
       (record "root";
        ((ignore (solver [] side); raise Fail "unsolved side succeeded")
         handle HOL_ERR _ => record "solver-rejected"); pq)
     else if aconv tm q then (record "second"; qr)
     else if aconv tm side then (record "side"; side_rule)
     else NO_CONV tm}
val base = pureSimps.pure_ss ++ dproc_ss reducer
fun raw n = QCONV (TRY_CONV
  (Traverse.TRAVERSE (traversedata_for_ss (limit n base)) []))
val _ = Paired.check "zero limit returns reflexivity"
  (same (raw 0 p) (REFL p) andalso null (!events))
val _ = events := []
val one = raw 1 p
val _ = Paired.check "one limit retains root after failed solver"
  (same one pq)
val _ = Paired.check "one limit exact failed-attempt callbacks"
  (!events = ["root","side","solver-rejected"])
val _ = events := []
val two = raw 2 p
val _ = Paired.check "solver failure rolls back spent traversal allowance"
  (same two (TRANS pq qr))
val _ = Paired.check "two limit exact callback order"
  (!events = ["root","side","solver-rejected","second"])
val failed = ASSUME
  ``(limits_condition /\ T) ==> ((limits_f:'a -> 'b) x = y)``
val input = ``(limits_h:'b -> bool -> 'c) (limits_f (x:'a)) (limits_z /\ T)``
val th = QCONV (SIMP_CONV (limit 1 boolSimps.bool_ss) [failed]) input
val _ = Paired.check "failed condition restores enclosing sibling allowance"
  (aconv (concl th)
    (mk_eq (input,``(limits_h:'b -> bool -> 'c) (limits_f (x:'a)) limits_z``))
   andalso null (hyp th))
