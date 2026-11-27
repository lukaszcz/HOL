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

local
datatype direction = Left | Right
datatype split = Unit of term * direction list | Choice of term

(* Find the first unit, or the atom that occurs most often. Record the
   unit's projection from the current conjunction when requested. *)
fun find_split track_path phi =
  let
    fun count (clause,acc) = fold_clause_atoms count_atom clause acc
    fun branch side path = if track_path then side :: path else path
    fun scan clause path pending visited =
        case dest_binary_application clause of
            SOME (head,left,right) =>
              if same_const conjunction head then
                scan left (branch Left path) ((right,path) :: pending)
                  visited
              else if same_const disjunction head then
                case pending of
                    (next,parent) :: rest =>
                      scan next (branch Right parent) rest (clause :: visited)
                  | [] => Choice (getBiggest (List.foldl count Termtab.empty
                            (List.rev (clause :: visited))))
              else Unit (clause,path)
          | NONE => Unit (clause,path)
  in scan phi [] [] [] end

fun unit_atom clause =
    if is_comb clause then
      let val (operator,operand) = dest_comb clause in
        if same_const negation operator then operand else clause
      end
    else clause

in
fun find_splitting_var phi =
    case find_split false phi of
        Unit (clause,_) => unit_atom clause
      | Choice atom => atom

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

(* Rewriting with an assumed Boolean equality such as T = T can loop.
   These pure rewrites simplify constants without an assignment. *)
val simplify_constants =
    PURE_REWRITE_RULE [AND_CLAUSES, OR_CLAUSES, NOT_CLAUSES]

fun search prove_units initial =
  let
    (* Rewriting preserves the initial hypotheses. Variables fixed there
       cannot become schematic in later unit proofs. *)
    val fixed_atom =
        if prove_units then
          let
            val vars = Portable.HOLSusp.delay (fn () => hyp_frees initial)
            val types = Portable.HOLSusp.delay (fn () => Thm.hyp_tyvars initial)
            fun fixed_var v =
              HOLset.member (Portable.HOLSusp.force vars,v)
            fun fixed_type ty =
              HOLset.member (Portable.HOLSusp.force types,ty)
            fun fixed atom =
              if is_var atom then fixed_var atom
              else
                not (isSome (HOLset.find (not o fixed_var)
                  (Term.FVL [atom] Term.empty_tmset))) andalso
                List.all fixed_type (Term.type_vars_in_term atom)
          in fixed end
        else K false
    fun project (Left,th) = CONJUNCT1 th
      | project (Right,th) = CONJUNCT2 th
    fun combine v l_false r_false =
      Refutation (DISJ_CASES (SPEC v BOOL_CASES_AX) l_false r_false)
    fun recurse th =
      let
        val c = concl th
        fun prove_unit path = List.foldl project th (List.rev path)
        fun deferred_unit () =
          case find_split true c of
              Unit (_,path) => prove_unit path
            | Choice _ => raise Fail "DPLL unit projection"
        (* Rewrite with just the assignment hypothesis. On refutation, the
           unit proof discharges it without rewriting the opposite branch. *)
        fun force_unit atom value prove_equality =
          case recurse (split_branch atom value th) of
              Refutation refutation =>
                Refutation (PROVE_HYP (prove_equality ()) refutation)
            | assignment => assignment
      in
        if is_T c then Assignment th
        else if is_F c then Refutation th
        else case find_split prove_units c of
          Unit (clause,path) =>
              let fun prove () = if prove_units then prove_unit path
                                 else deferred_unit ()
              in
                if is_F clause then Refutation (prove ())
                else if is_T clause then recurse (simplify_constants th)
                else if is_neg clause then
                  let val atom = dest_neg clause in
                    if is_T atom orelse is_F atom then
                      recurse (simplify_constants th)
                    else if prove_units then
                      let val equality = EQF_INTRO (prove ())
                      in
                        if fixed_atom atom then
                          force_unit atom boolSyntax.F (fn () => equality)
                        else recurse (REWRITE_RULE [equality] th)
                      end
                    else force_unit atom boolSyntax.F (EQF_INTRO o prove)
                  end
                else
                  force_unit clause boolSyntax.T (EQT_INTRO o prove)
              end
        | Choice v =>
            if is_T v orelse is_F v then recurse (simplify_constants th)
            else try_both th v
      end
    and try_both th v =
      case recurse (split_branch v boolSyntax.T th) of
          Refutation l_false =>
          (case recurse (split_branch v boolSyntax.F th) of
               Refutation r_false => combine v l_false r_false
            | x => x)
        | x => x
  in recurse initial end

in

fun CoreDPLL initial =
    case search false initial of
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
      case search true initial of
        Refutation th =>
          SOME (if compact then minisatResolve.finish_compact_cnf
                  (concl initial) lfn clauseth th else th)
      | Assignment _ => NONE
    end

end
end

fun mk_model_thm cnfv lfn t f =
    let
      fun literal v positive = if positive then v else mk_neg v
      val model =
          if isSome cnfv then
            List.rev (RBM.foldl (fn (v,source,rest) =>
              if is_var source then literal source (is_T (f v)) :: rest
              else rest) [] lfn)
          else List.map (fn v => literal v (is_T (f v))) (free_vars t)
    in satCheck model (mk_neg t) end

local
fun reverse_conjunction leaf join clauses =
    ArraySlice.foldl (fn (clause, rest) => join (leaf clause,rest))
      (leaf (Array.sub (clauses,0))) (ArraySlice.slice (clauses,1,NONE))

fun dpll_taut t cnfv lfn clauses =
    (* Keep the original conjunction and split order. Generated definitional
       clauses are disjunctions or literals. For callers supplying equality
       clauses, preserve the assumptions that mk_satmap may inspect. *)
    if RBM.numItems lfn <> 0 andalso Array.length clauses <> 0 andalso
       not (Array.exists (is_eq o fst) clauses) then
      let val cnf = reverse_conjunction fst mk_conj clauses
      in case CoreDPLL (ASSUME cnf) of
             Unsat th => minisatResolve.finish_compact_cnf_with
               (fn () => reverse_conjunction snd
                 (fn (left,right) => CONJ left right) clauses) cnf lfn th
           | Sat f => mk_model_thm cnfv lfn t f
      end
    else
      let val (_,cnf_thm,_,premises) = prepareDPLL (cnfv,lfn,clauses)
      in case CoreDPLL cnf_thm of
             Unsat th => undoCNF lfn premises th
           | Sat f => mk_model_thm cnfv lfn t f
      end
in
fun DPLL_TAUT t =
    let val (cnfv,_,lfn,clauses) = to_cnf false (mk_neg t)
    in dpll_taut t cnfv lfn clauses end
val DPLL_TAUT_PREPARED = dpll_taut
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
