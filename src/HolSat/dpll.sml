(* Taken from code by Michael Norrish to        *)
(* accompany Proof Tools chapter of the Manual. *)
(* Acts as a failsafe for SAT_TAUT_PROVE        *)
(* on trivial problems.                         *)
(* Ultimate entry-point is DPLL_TAUT            *)

structure dpll =
struct

open HolKernel Parse boolLib def_cnf satCommonTools satTools

datatype result = Unsat of thm | Sat of term -> term

fun count_atom (v,acc) = Termtab.map_default (v,0) (fn n => n + 1) acc

fun count_vars ds acc =
    case ds of
      [] => acc
    | lit::lits => let
        val v = dest_neg lit handle HOL_ERR _ => lit
      in
        count_vars lits (count_atom (v,acc))
      end

fun getBiggest acc =
    #1 (Termtab.fold (fn (v,cnt) => fn (a as (bestv,bestcnt)) =>
                         if cnt > bestcnt then (v,cnt) else a)
                     acc
                     (boolSyntax.T, 0))

(* The first unit we see, or the var that occurs most often *)
fun find_splitting_var phi =
  let
    fun count (clause,acc) = fold_clause_atoms count_atom clause acc
    fun scan clause pending visited =
        case total dest_conj clause of
            SOME (left,right) => scan left (right :: pending) visited
          | NONE =>
              if is_disj clause then
                case pending of
                    next :: rest => scan next rest (clause :: visited)
                  | [] => getBiggest (List.foldl count Termtab.empty
                            (List.rev (clause :: visited)))
              else (dest_neg clause handle HOL_ERR _ => clause)
  in scan phi [] [] end

fun split_branch v value th =
  REWRITE_RULE [ASSUME (mk_eq (v,value))] th

fun casesplit v th =
  (split_branch v boolSyntax.T th, split_branch v boolSyntax.F th)

fun mk_satmap th = let
  val hyps = hypset th
  fun foldthis (t,acc) = let
    val (l,r) = dest_eq t
  in
    Termtab.update (l,r) acc
  end handle HOL_ERR _ => acc
  val fmap = HOLset.foldl foldthis Termtab.empty hyps
in
  Sat (fn v => case Termtab.lookup fmap v of
                   SOME t => t
                 | NONE => boolSyntax.T)
end

local
datatype search_result = Refutation of thm | Assignment of thm

fun search initial_th = let (* [ci] |- cnf *)
   fun recurse th = let (* [assigns, ci] |- curr *)
    val c = concl th (* current *)
  in
    if aconv c boolSyntax.T then
      Assignment th
    else if aconv c boolSyntax.F then
      Refutation th
    else let
        val v = find_splitting_var c
      in
        case recurse (split_branch v boolSyntax.T th) of
          Refutation l_false =>
          (case recurse (split_branch v boolSyntax.F th) of
               Refutation r_false =>
               Refutation (DISJ_CASES (SPEC v BOOL_CASES_AX) l_false r_false)
               (* [assignsr\v,assignsl\v,ci] |- F *)
            | x => x)
        | x => x
      end
  end
in
   recurse initial_th (* [ci] |-  F *)
end

in

fun CoreDPLL initial =
    case search initial of
        Refutation th => Unsat th
      | Assignment th => mk_satmap th

fun prepareDPLL (cnfv,lfn,clauseth) =
    (* clauses is (ci,[~t] |- ci') pairs, where ci' is expanded ci *)
    let val clauses = Array.foldr (op ::) [] clauseth
        val cnf_thm = List.foldl (fn ((c,_),cnf) => CONJ (ASSUME c) cnf)
                                 (*[ci] |- cnf*)
                                 (ASSUME (fst (hd clauses))) (tl clauses)
    in (cnfv,cnf_thm,lfn,clauses) end

fun doCNF neg_tm =
    let val (cnfv,_,lfn,clauseth) = to_cnf false neg_tm
    in prepareDPLL (cnfv,lfn,clauseth) end

fun undoCNF lfn clauses th = (* th is [ci] |-  F *)
    let
        (* Discharge the compact schematic CNF clauses before expanding the
           definitional substitution.  Repeated PROVE_HYP after INST makes
           every intermediate hypothesis-set operation traverse the expanded
           Boolean circuits. *)
        val discharged = List.foldl
          (fn ((clause,_),theorem) => DISCH clause theorem) th clauses
        val insts = RBM.foldl (fn (v,t,insts) => (v |-> t)::insts) [] lfn
        val inst_th = INST insts discharged
        val th0 = List.foldl (fn ((_,cth),theorem) => MP theorem cth)
                             inst_th (List.rev clauses) (* ~t |- F *)
    in th0 end

(* Proof-only fallback uses the already prepared clauses, including explicit
   CNF with compound atoms.  Do not re-clausify it or reconstruct a model. *)
fun DPLL_REFUTE lfn clauseth =
    let
        val compact = RBM.numItems lfn <> 0
        (* Balancing preserves left-to-right clause order for unit selection.
           Without substitution, each premise already proves its clause. *)
        val initial =
            if compact then
              ASSUME (minisatResolve.balanced_array
                boolSyntax.T fst boolSyntax.mk_conj clauseth)
            else minisatResolve.balanced_clause_proof clauseth
    in
      case search initial of
        Refutation th =>
          SOME (if compact then minisatResolve.finish_compact_cnf
                  (concl initial) lfn clauseth th else th)
      | Assignment _ => NONE
    end

end

fun mk_model_thm cnfv lfn t f =
    let
      fun literal v positive = if positive then v else mk_neg v
      val model =
          if isSome cnfv then
            List.rev (RBM.foldl (fn (v,source,rest) =>
              let val positive = is_T (f v)
              in if is_var source then literal source positive :: rest
                 else rest end) [] lfn)
          else List.map (fn v => literal v (is_T (f v))) (free_vars t)
    in satCheck model (mk_neg t) end

local
fun dpll_taut t (cnfv,cnf_thm,lfn,clauses) =
  case CoreDPLL cnf_thm of
      Unsat cnf_entails_F =>  (* [ci] |- F *)
        undoCNF lfn clauses cnf_entails_F (* [~t] |- F *)
    | Sat f => mk_model_thm cnfv lfn t f (* |- model ==> ~t *)
in
fun DPLL_TAUT t = dpll_taut t (doCNF (mk_neg t))
fun DPLL_TAUT_PREPARED t cnfv lfn clauseth =
    dpll_taut t (prepareDPLL (cnfv,lfn,clauseth))
end

(* implementation of DPLL ends *)

(* ----------------------------------------------------------------------
    Code below, due to John Harrison, generates tautologies stating that
    two different implementations of binary addition are equivalent
   ---------------------------------------------------------------------- *)

(*
fun halfsum x y = mk_eq(x,mk_neg y)
fun halfcarry x y = mk_conj(x,y)
fun ha x y s c = mk_conj(mk_eq(s,halfsum x y), mk_eq(c,halfcarry x y))

fun carry x y z = mk_disj(mk_conj(x,y), mk_conj(mk_disj(x,y), z))
fun sum x y z = halfsum (halfsum x y) z;
fun fa x y z s c = mk_conj(mk_eq(s,sum x y z), mk_eq(c,carry x y z))

fun list_conj cs = list_mk_conj cs handle HOL_ERR _ => boolSyntax.T

fun ripplecarry x y c out n =
    list_conj
      (List.tabulate(n, (fn i => fa (x i) (y i) (c i) (out i) (c (i + 1)))))

fun mk_index s i = mk_var(s ^ "_" ^ Int.toString i, bool)

val [x,y,out,c] = map mk_index ["X", "Y", "OUT", "C"]
val twobit_adder = ripplecarry x y c out 2

fun simp t =
    rhs (concl (QCONV (REWRITE_CONV [GSYM CONJ_ASSOC, GSYM DISJ_ASSOC]) t))

fun ripplecarry0 x y c out n =
    simp (ripplecarry x y (fn i => if i = 0 then boolSyntax.F
                                   else c i) out n)

fun ripplecarry1 x y c out n =
    simp (ripplecarry x y (fn i => if i = 0 then boolSyntax.T
                                   else c i) out n)

fun mux sel in0 in1 = mk_disj(mk_conj(mk_neg sel,in0), mk_conj(sel,in1))

fun offset n x i = x (n + i)
fun carryselect x y c0 c1 s0 s1 c s n k = let
  val k' = Int.min(n,k)
  val fm =
      mk_conj(mk_conj(ripplecarry0 x y c0 s0 k', ripplecarry1 x y c1 s1 k'),
              mk_conj(mk_eq(c k', mux (c 0) (c0 k') (c1 k')),
                      list_conj
                      (List.tabulate
                       (k',
                        (fn i => mk_eq(s i, mux (c 0) (s0 i) (s1 i)))))))
in
  if k' < k then fm
  else mk_conj(fm, carryselect (offset k x) (offset k y)
                               (offset k c0) (offset k c1)
                               (offset k s0) (offset k s1)
                               (offset k c) (offset k s)
                               (n - k) k)
end

(* call with positive n and k to generate tautologies *)
fun mk_adder_test n k = let
  val [x,y,c,s,c0,s0,c1,s1,c2,s2] =
      map mk_index ["x", "y", "c", "s", "c0", "s0", "c1", "s1", "c2", "s2"]
in
  simp
    (mk_imp(mk_conj(mk_conj(carryselect x y c0 c1 s0 s1 c s n k, mk_neg (c 0)),
                    ripplecarry0 x y c2 s2 n),
            mk_conj(mk_eq(c n, c2 n),
                    list_conj(List.tabulate(n, (fn i => mk_eq(s i, s2 i)))))))
end

(* example in tutorial is *)

val example = gen_all (mk_adder_test 3 2)

*)
end
