(* Retained graph words, not cumulative allocation or serialized heap size.
   Equal-arity roots retain inputs once and subtract shared module closures. *)
open HolKernel boolLib simpLib Paired
val _ = new_theory "compiled_core_graph"
val sizes = [0,1,10,100,1000,10000]
fun rule i = let
  val name = "compiled_core_r" ^ Int.toString i
  val _ = new_constant (name,bool)
in ASSUME (mk_eq (mk_const (name,bool),T)) end
val rules = List.tabulate (10000,rule)
val base = pureSimps.pure_ss
fun same (a,b) = aconv (concl a) (concl b) andalso
  HOLset.equal (hypset a,hypset b)
fun row label n anchor union =
  (Paired.observe ("graph." ^ label)
     (String.concatWith "," (map Int.toString
       [n,anchor,union,union-anchor]));
   Paired.check (label ^ " " ^ Int.toString n) (union >= anchor))
val _ = List.app (fn n => let
  val rs = List.take (rules,n)
  val f = rewrites rs
  val ss = base ++ f
  val merged = merge_ss [f]
  val td = traversedata_for_ss ss
  fun proof conv = List.all (fn rw =>
    same (Conv.QCONV conv (lhs (concl rw)),rw))
    (if n = 0 then [] else [hd rs,List.last rs])
  val _ = Paired.check ("proofs " ^ Int.toString n)
    (length (frag_rewrites f) = n andalso
     length (frag_rewrites merged) = n andalso
     proof (SIMP_CONV ss []) andalso
     proof (Traverse.TRAVERSE td []) andalso
     proof (SIMP_CONV (base ++ merged) []) andalso
     (n <> 0 orelse same
       (Conv.QCONV (SIMP_CONV ss []) T,REFL T)))
  val _ = PolyML.fullGC ()
  val _ = row "fragment" n (PolyML.objSize (base,rs,base))
                          (PolyML.objSize (base,rs,f))
  val _ = row "compiled" n (PolyML.objSize (base,f,base))
                          (PolyML.objSize (base,f,ss))
  val _ = row "merge" n (PolyML.objSize (base,f,base))
                       (PolyML.objSize (base,f,merged))
  val _ = row "projection" n (PolyML.objSize (ss,ss,ss))
                            (PolyML.objSize (ss,ss,td))
  (* objSize unit/sensitivity control: cons=3, reference=2 words. *)
  val cells = List.tabulate (n,fn i => ref i)
  val _ = row "cells" n (PolyML.objSize ((),[],()))
                       (PolyML.objSize ((),cells,()))
in () end) sizes
val _ = Paired.observe "complete" "TASK16-compiled-core-graph-v1"
