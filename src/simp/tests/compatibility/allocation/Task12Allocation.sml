(* Structural probe, deliberately separate from the measured timing fixtures.
   objSize inspects reachable graph words, NOT cumulative allocated words.
   No representation casts or closure-layout assumptions. *)
open HolKernel boolSyntax Drule Paired
val _ = new_theory "task12_allocation"
val sizes = [0,1,8,64,256,1024]
fun required b = if b then () else raise Fail "allocation probe invariant"
fun emit key ns = Paired.observe key
  (String.concatWith "," (map Int.toString ns))

val x = mk_var ("allocation_x",bool)
val y = mk_var ("allocation_y",bool)
val plain = CONJUNCT1 (SPEC x boolTheory.AND_CLAUSES)
val conditional = DISCH (mk_neg x) plain
val perm = SPECL [x,y] boolTheory.CONJ_SYM
fun rule kind i = let
  val suffix = Int.toString i
  val a = mk_var ("allocation_a" ^ suffix,bool)
  val b = mk_var ("allocation_b" ^ suffix,bool)
  val th = INST [x |-> a,y |-> b]
    (case kind of "conditional" => conditional | "ac" => perm | _ => plain)
  val (conditions,eqn) = strip_imp (concl th)
  val (l,r) = dest_eq eqn
  val (th,input) =
    if kind = "ac" andalso Cond_rewr.ac_term_ord (l,r) <> GREATER
    then (SYM th,r) else (th,l)
in ((kind ^ suffix,th),input,conditions) end
fun solver _ tm = ASSUME tm
fun increment base results =
  PolyML.objSize (base,results,base) - PolyML.objSize (base,[],base)
fun same th input =
  let val (l,r) = dest_eq (concl th)
  in aconv l input andalso not (aconv l r) end
fun sample kind n = let
  (* A constant-size sentinel roots static matcher/module dependencies even
     at n=0; it does not share any rule-specific variable/name with inputs. *)
  val (seed,_,_) = rule kind ~1
  val anchor = Cond_rewr.COND_REWR_CONV seed false
  val inputs = List.tabulate (n,rule kind)
  val constructors = map (fn (named,_,_) =>
    Cond_rewr.COND_REWR_CONV named false) inputs
  val solved = map (fn f => f solver) constructors
  val saved = map (fn f => f []) solved
  val results = ListPair.map (fn (f,(_,tm,_)) => f tm) (saved,inputs)
  val _ = required (ListPair.allEq (fn (th,((_,expected),tm,conditions)) =>
    same th tm andalso aconv (concl th) (snd (strip_imp (concl expected)))
    andalso HOLset.equal (hypset th,HOLset.fromList Term.compare conditions))
    (results,inputs))
  val _ = emit ("graph." ^ kind)
    [n,increment (anchor,inputs,solver) constructors,
     increment (anchor,inputs,solver,constructors) solved,
     increment (anchor,inputs,solver,constructors,solved) saved,
     increment (anchor,inputs,solver,constructors,solved,saved) results]
in Paired.check (kind ^ " " ^ Int.toString n) true end
val _ = List.app (fn kind => List.app (sample kind) sizes)
  ["unconditional","conditional","ac"]
(* A positive sensitivity control: one fresh mutable cell per list element.
   Same-shaped anchors remove the root tuple, but retain list/cell words. *)
val _ = List.app (fn n => let
  val cells = List.tabulate (n,fn i => ref i)
  val _ = emit "control.cells" [n,increment () cells]
in Paired.check ("cells " ^ Int.toString n) (increment () cells = 5 * n)
end) sizes
