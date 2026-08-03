open HolKernel testutils linarithInstTheory linarithCorpus

fun check (name, predicate) =
  (tprint name;
   if predicate () then OK () else die "failed")

fun valid_closes tactic goal =
  null (#1 (Tactical.VALID tactic goal))

fun tactic_fails tactic goal =
  ((ignore (Tactical.VALID tactic goal); false)
   handle Feedback.HOL_ERR _ => true)

fun normalized_rhs
      (instance : linarithData.linarith_instance) tm =
  #2 (boolSyntax.dest_eq
        (Thm.concl (#norm_conv instance tm)))

fun clean_norm (instance : linarithData.linarith_instance) tm =
  null (Thm.hyp (#norm_conv instance tm))

val int_instance = intLinarith.instance
val real_instance = realLinarith.instance
val rat_instance = ratLinarith.instance

val ix = Term.mk_var ("linarith_int_x", intSyntax.int_ty)
val iy = Term.mk_var ("linarith_int_y", intSyntax.int_ty)
val iz = Term.mk_var ("linarith_int_z", intSyntax.int_ty)
val i0 = intSyntax.zero_tm
val i2 = intSyntax.term_of_int (Arbint.fromInt 2)
val i3 = intSyntax.term_of_int (Arbint.fromInt 3)
val i7 = intSyntax.term_of_int (Arbint.fromInt 7)
val i8 = intSyntax.term_of_int (Arbint.fromInt 8)
val im1 = intSyntax.term_of_int (Arbint.fromInt ~1)
val im3 = intSyntax.term_of_int (Arbint.fromInt ~3)

fun iplus left right = intSyntax.mk_plus (left, right)
fun ileq left right = intSyntax.mk_leq (left, right)
fun iless left right = intSyntax.mk_less (left, right)

val _ =
  check
    ("int norm_conv satisfies cancellation and decision contract",
     fn () =>
       Term.aconv
         (normalized_rhs int_instance
           (ileq (iplus ix i3) (iplus ix i2)))
         boolSyntax.F andalso
       Term.aconv
         (normalized_rhs int_instance
           (ileq (iplus ix iy) (iplus iy iz)))
         (ileq ix iz) andalso
       Term.aconv
         (normalized_rhs int_instance (iless i7 i8))
         boolSyntax.T andalso
       clean_norm int_instance
         (ileq (iplus ix i3) (iplus ix i2)))

val _ =
  check
    ("int divmod facts cover INT_DIV_P and INT_MOD_P behavior",
     fn () =>
       let
         val facts = #atom_facts int_instance
         val positive = facts (intSyntax.mk_mod (ix, i3))
         val negative = facts (intSyntax.mk_div (ix, im3))
       in
         List.length positive = 3 andalso
         List.length negative = 3 andalso
         null (facts (intSyntax.mk_mod (ix, i0))) andalso
         List.all (null o Thm.hyp) (positive @ negative)
       end)

val rx = Term.mk_var ("linarith_real_x", realSyntax.real_ty)
val ry = Term.mk_var ("linarith_real_y", realSyntax.real_ty)
val rz = Term.mk_var ("linarith_real_z", realSyntax.real_ty)
val r0 = realSyntax.zero_tm
val r2 = RealArith.term_of_rat (Arbrat.fromInt 2)
val r3 = RealArith.term_of_rat (Arbrat.fromInt 3)
val r7 = RealArith.term_of_rat (Arbrat.fromInt 7)
val r8 = RealArith.term_of_rat (Arbrat.fromInt 8)
val rim2 =
  intrealSyntax.mk_real_of_int
    (intSyntax.term_of_int (Arbint.fromInt ~2))
val rhalf =
  RealArith.term_of_rat
    (Arbrat./ (Arbrat.one, Arbrat.two))

fun rplus left right = realSyntax.mk_plus (left, right)
fun rleq left right = realSyntax.mk_leq (left, right)
fun rless left right = realSyntax.mk_less (left, right)

val _ =
  check
    ("real norm_conv satisfies cancellation and decision contract",
     fn () =>
       Term.aconv
         (normalized_rhs real_instance
           (rleq (rplus rx r3) (rplus rx r2)))
         boolSyntax.F andalso
       Term.aconv
         (normalized_rhs real_instance
           (rleq (rplus rx ry) (rplus ry rz)))
         (rleq rx rz) andalso
       Term.aconv
         (normalized_rhs real_instance (rless r7 r8))
         boolSyntax.T andalso
       Term.aconv
         (normalized_rhs real_instance
           (boolSyntax.mk_eq (rplus rhalf rhalf,
              realSyntax.one_tm)))
         boolSyntax.T andalso
       Term.aconv
         (normalized_rhs real_instance
           (boolSyntax.mk_eq
             (rim2, RealArith.term_of_rat (Arbrat.fromInt ~2))))
         boolSyntax.T andalso
       clean_norm real_instance
         (rleq (rplus rx r3) (rplus rx r2)))

val qx = Term.mk_var ("linarith_rat_x", ratSyntax.rat_ty)
val qy = Term.mk_var ("linarith_rat_y", ratSyntax.rat_ty)
val qz = Term.mk_var ("linarith_rat_z", ratSyntax.rat_ty)
val q0 = ratSyntax.rat_0_tm
val q2 = #mk_lit (#dest rat_instance) (Arbrat.fromInt 2)
val q3 = #mk_lit (#dest rat_instance) (Arbrat.fromInt 3)
val q7 = #mk_lit (#dest rat_instance) (Arbrat.fromInt 7)
val q8 = #mk_lit (#dest rat_instance) (Arbrat.fromInt 8)
val rat_of_int_tm =
  prim_mk_const {Name = "rat_of_int", Thy = "rat"}
val qim2 =
  Term.mk_comb
    (rat_of_int_tm, intSyntax.term_of_int (Arbint.fromInt ~2))
val qhalf =
  #mk_lit (#dest rat_instance)
    (Arbrat./ (Arbrat.one, Arbrat.two))

fun qplus left right = ratSyntax.mk_rat_add (left, right)
fun qleq left right = ratSyntax.mk_rat_leq (left, right)
fun qless left right = ratSyntax.mk_rat_les (left, right)

val _ =
  check
    ("rat norm_conv satisfies cancellation and decision contract",
     fn () =>
       Term.aconv
         (normalized_rhs rat_instance
           (qleq (qplus qx q3) (qplus qx q2)))
         boolSyntax.F andalso
       Term.aconv
         (normalized_rhs rat_instance
           (qleq (qplus qx qy) (qplus qy qz)))
         (qleq qx qz) andalso
       Term.aconv
         (normalized_rhs rat_instance (qless q7 q8))
         boolSyntax.T andalso
       #dest_lit (#dest rat_instance) qhalf =
         Arbrat./ (Arbrat.one, Arbrat.two) andalso
       Term.aconv
         (normalized_rhs rat_instance
           (boolSyntax.mk_eq (qplus qhalf qhalf,
              ratSyntax.rat_1_tm)))
         boolSyntax.T andalso
       Term.aconv
         (normalized_rhs rat_instance
           (boolSyntax.mk_eq
             (qim2, #mk_lit (#dest rat_instance) (Arbrat.fromInt ~2))))
         boolSyntax.T andalso
       clean_norm rat_instance
         (qleq (qplus qx q3) (qplus qx q2)))

val _ =
  check
    ("int battery uses abs splitting through Tactical.VALID",
     fn () =>
       valid_closes (linarithLib.LINARITH_TAC [])
         ([], ileq i0 (intSyntax.mk_absval ix)))

val imod3 = intSyntax.mk_mod (ix, i3)
val idiv3 = intSyntax.mk_div (ix, i3)

val _ =
  check
    ("int battery uses discreteness and min/max splitting",
     fn () =>
       valid_closes (linarithLib.SIMPLE_LINARITH_TAC [])
         ([iless ix iy], ileq (iplus ix intSyntax.one_tm) iy) andalso
       valid_closes (linarithLib.LINARITH_TAC [])
         ([], ileq (intSyntax.mk_min (ix, iy)) ix) andalso
       valid_closes (linarithLib.LINARITH_TAC [])
         ([], ileq ix (intSyntax.mk_max (ix, iy))))

val _ =
  check
    ("int battery uses P-form divmod behavior through Tactical.VALID",
     fn () =>
       valid_closes (linarithLib.LINARITH_TAC [])
         ([], boolSyntax.mk_eq
           (ix, iplus (intSyntax.mk_mult (idiv3, i3)) imod3)) andalso
       valid_closes (linarithLib.LINARITH_TAC [])
         ([], ileq i0 imod3) andalso
       valid_closes (linarithLib.LINARITH_TAC [])
         ([], iless imod3 i3) andalso
       valid_closes (linarithLib.LINARITH_TAC [])
         ([], iless im3 (intSyntax.mk_mod (ix, im3))) andalso
       valid_closes (linarithLib.LINARITH_TAC [])
         ([], ileq (intSyntax.mk_mod (ix, im3)) i0))

val midpoint = realSyntax.mk_div (rplus rx ry, r2)

val _ =
  check
    ("real battery proves the lower dense midpoint bound",
     fn () =>
       valid_closes (linarithLib.SIMPLE_LINARITH_TAC [])
         ([rless rx ry], rless rx midpoint))

val _ =
  check
    ("real battery proves the upper dense midpoint bound",
     fn () =>
       valid_closes (linarithLib.SIMPLE_LINARITH_TAC [])
         ([rless rx ry], rless midpoint ry))

val _ =
  check
    ("real battery uses abs splitting through Tactical.VALID",
     fn () =>
       valid_closes (linarithLib.LINARITH_TAC [])
         ([], rleq r0 (realSyntax.mk_absval rx)))

val rat_transitivity =
  boolSyntax.mk_imp
    (boolSyntax.mk_conj (qleq qx qy, qless qy qz),
     qless qx qz)
val qmidpoint = ratSyntax.mk_rat_div (qplus qx qy, q2)

val _ =
  check
    ("real battery uses min/max splitting through Tactical.VALID",
     fn () =>
       valid_closes (linarithLib.LINARITH_TAC [])
         ([], rleq (realSyntax.mk_min (rx, ry)) rx) andalso
       valid_closes (linarithLib.LINARITH_TAC [])
         ([], rleq rx (realSyntax.mk_max (rx, ry))))

val _ =
  check
    ("rat field normalization proves dense midpoint bounds",
     fn () =>
       valid_closes (linarithLib.SIMPLE_LINARITH_TAC [])
         ([qless qx qy], qless qx qmidpoint) andalso
       valid_closes (linarithLib.SIMPLE_LINARITH_TAC [])
         ([qless qx qy], qless qmidpoint qy))

val _ =
  check
    ("rat battery exceeds RAT_BASIC_ARITH_CONV",
     fn () =>
       tactic_fails (Tactic.CONV_TAC ratLib.RAT_BASIC_ARITH_CONV)
         ([], rat_transitivity) andalso
       valid_closes (linarithLib.LINARITH_TAC [])
         ([], rat_transitivity) andalso
       Term.aconv
         (Thm.concl (linarithLib.LINARITH_PROVE rat_transitivity))
         rat_transitivity)

val n = Term.mk_var ("linarith_injection_n", numSyntax.num)
val m = Term.mk_var ("linarith_injection_m", numSyntax.num)
val p = Term.mk_var ("linarith_injection_p", numSyntax.num)
val ii = Term.mk_var ("linarith_injection_i", intSyntax.int_ty)
val ij = Term.mk_var ("linarith_injection_j", intSyntax.int_ty)
val ik = Term.mk_var ("linarith_injection_k", intSyntax.int_ty)
val rr = Term.mk_var ("linarith_injection_r", realSyntax.real_ty)
val qq = Term.mk_var ("linarith_injection_q", ratSyntax.rat_ty)
val n_int = intSyntax.mk_injected n
val m_int = intSyntax.mk_injected m
val p_int = intSyntax.mk_injected p
val ii_real = intrealSyntax.mk_real_of_int ii
val ij_real = intrealSyntax.mk_real_of_int ij
val ik_real = intrealSyntax.mk_real_of_int ik
val n_rat = ratSyntax.mk_rat_of_num n
val m_rat = ratSyntax.mk_rat_of_num m
val p_rat = ratSyntax.mk_rat_of_num p

fun inject from_ty to_ty tm =
  let
    val injection =
      valOf (linarithData.injection_for from_ty to_ty)
  in
    Term.mk_comb (#inj injection, tm)
  end

val n_real = inject numSyntax.num realSyntax.real_ty n
val m_real = inject numSyntax.num realSyntax.real_ty m
val ii_rat = inject intSyntax.int_ty ratSyntax.rat_ty ii
val ij_rat = inject intSyntax.int_ty ratSyntax.rat_ty ij
val ik_rat = inject intSyntax.int_ty ratSyntax.rat_ty ik
val im2_rat =
  inject intSyntax.int_ty ratSyntax.rat_ty
    (intSyntax.term_of_int (Arbint.fromInt ~2))

val _ =
  check
    ("all specified injections are registered at module load",
     fn () =>
       List.all Option.isSome
         [linarithData.injection_for numSyntax.num intSyntax.int_ty,
          linarithData.injection_for numSyntax.num realSyntax.real_ty,
          linarithData.injection_for intSyntax.int_ty realSyntax.real_ty,
          linarithData.injection_for numSyntax.num ratSyntax.rat_ty,
          linarithData.injection_for intSyntax.int_ty ratSyntax.rat_ty] andalso
       #dest_lit (#dest rat_instance) im2_rat = Arbrat.fromInt ~2)

val _ =
  check
    ("mixed num-to-int replay uses the registered injection",
     fn () =>
       valid_closes (linarithLib.SIMPLE_LINARITH_TAC [])
         ([numSyntax.mk_leq (n, m), ileq m_int ii], ileq n_int ii))

val _ =
  check
    ("mixed int-to-real replay uses the registered injection",
     fn () =>
       valid_closes (linarithLib.SIMPLE_LINARITH_TAC [])
         ([ileq ii ij, rleq ij_real rr], rleq ii_real rr))

val _ =
  check
    ("mixed num-to-real replay uses the registered injection",
     fn () =>
       valid_closes (linarithLib.SIMPLE_LINARITH_TAC [])
         ([numSyntax.mk_leq (n, m), rleq m_real rr], rleq n_real rr))

val _ =
  check
    ("num-to-int strict-order injection homomorphism replays",
     fn () =>
       valid_closes (linarithLib.SIMPLE_LINARITH_TAC [])
         ([numSyntax.mk_less (n, m)], iless n_int m_int))

val _ =
  check
    ("int-to-real strict-order injection homomorphism replays",
     fn () =>
       valid_closes (linarithLib.SIMPLE_LINARITH_TAC [])
         ([iless ii ij], rless ii_real ij_real))

val _ =
  check
    ("num-to-rat strict-order injection homomorphism replays",
     fn () =>
       valid_closes (linarithLib.SIMPLE_LINARITH_TAC [])
         ([numSyntax.mk_less (n, m)], qless n_rat m_rat))

val _ =
  check
    ("int-to-rat strict-order injection homomorphism replays",
     fn () =>
       valid_closes (linarithLib.SIMPLE_LINARITH_TAC [])
         ([iless ii ij], qless ii_rat ij_rat))

val _ =
  check
    ("negative injected literals normalize during mixed replay",
     fn () =>
       valid_closes (linarithLib.SIMPLE_LINARITH_TAC [])
         ([ileq ii (intSyntax.term_of_int (Arbint.fromInt ~2))],
          rleq ii_real rim2) andalso
       valid_closes (linarithLib.SIMPLE_LINARITH_TAC [])
         ([ileq ii (intSyntax.term_of_int (Arbint.fromInt ~2))],
          qleq ii_rat qim2))

val _ =
  check
    ("mixed int-to-rat replay uses the registered injection",
     fn () =>
       valid_closes (linarithLib.SIMPLE_LINARITH_TAC [])
         ([ileq ii ij, qleq ij_rat qq], qleq ii_rat qq))

val _ =
  check
    ("mixed num-to-rat replay uses the registered injection",
     fn () =>
       valid_closes (linarithLib.SIMPLE_LINARITH_TAC [])
         ([numSyntax.mk_leq (n, m), qleq m_rat qq], qleq n_rat qq))

val _ =
  check
    ("mixed sibling carriers replay through their common source",
     fn () =>
       valid_closes (linarithLib.SIMPLE_LINARITH_TAC [])
         ([rleq n_real r0, qless q0 n_rat], boolSyntax.F))

val _ =
  check
    ("num-to-int add homomorphism normalizes compound source terms",
     fn () =>
       valid_closes (linarithLib.SIMPLE_LINARITH_TAC [])
         ([numSyntax.mk_leq (numSyntax.mk_plus (n, m), p)],
          ileq (iplus n_int m_int) p_int))

val _ =
  check
    ("int-to-real add homomorphism normalizes compound source terms",
     fn () =>
       valid_closes (linarithLib.SIMPLE_LINARITH_TAC [])
         ([ileq (iplus ii ij) ik],
          rleq (rplus ii_real ij_real) ik_real))

val _ =
  check
    ("int-to-rat add homomorphism normalizes compound source terms",
     fn () =>
       valid_closes (linarithLib.SIMPLE_LINARITH_TAC [])
         ([ileq (iplus ii ij) ik],
          qleq (qplus ii_rat ij_rat) ik_rat))

val _ =
  check
    ("num-to-rat add homomorphism normalizes compound source terms",
     fn () =>
       valid_closes (linarithLib.SIMPLE_LINARITH_TAC [])
         ([numSyntax.mk_leq (numSyntax.mk_plus (n, m), p)],
          qleq (qplus n_rat m_rat) p_rat))

val _ =
  check
    ("injection mul homomorphisms normalize compound source terms",
     fn () =>
       let
         val n2 = numSyntax.mk_numeral (Arbnum.fromInt 2)
         val n2_int = intSyntax.mk_injected n2
       in
         valid_closes (linarithLib.SIMPLE_LINARITH_TAC [])
           ([numSyntax.mk_leq (numSyntax.mk_mult (n2, n), p)],
            ileq (intSyntax.mk_mult (n2_int, n_int)) p_int)
       end)

val _ =
  check
    ("Nonneg of injected atoms strengthens all target carriers",
     fn () =>
       valid_closes (linarithLib.SIMPLE_LINARITH_TAC [])
         ([], ileq i0 n_int) andalso
       valid_closes (linarithLib.SIMPLE_LINARITH_TAC [])
         ([], rleq r0 (realSyntax.mk_injected n)) andalso
       valid_closes (linarithLib.SIMPLE_LINARITH_TAC [])
         ([], qleq q0 n_rat))

val _ =
  check
    ("golden Added replay lifts Nonneg through num-to-int injection",
     fn () =>
       let
         val bad = ileq n_int im1
         val theorem =
           linarithReplay.mkthm
             [Thm.ASSUME bad]
             (linarithSolve.Added
               (linarithSolve.Nonneg n_int, linarithSolve.Asm 0))
       in
         Term.aconv (Thm.concl theorem) boolSyntax.F
       end)

val _ =
  check
    ("load-time registration warns and does not duplicate entries",
     fn () =>
       let
         val instance_count =
           List.length (linarithData.all_instances ())
         val injection_count =
           List.length (linarithData.injections ())
         val old_injections = linarithData.injections ()
         val warnings = ref ([] : string list)
         val saved = !Feedback.WARNING_outstream
         val _ =
           Feedback.WARNING_outstream :=
             (fn message => warnings := message :: !warnings)
         fun restore () = Feedback.WARNING_outstream := saved
         val _ =
           (List.app linarithData.register_instance
              [int_instance, real_instance, rat_instance];
            List.app linarithData.register_injection
              (List.rev old_injections);
            restore ())
           handle e => (restore (); raise e)
       in
         List.length (!warnings) = 3 andalso
         List.all
           (String.isSubstring "replacing the linarith instance")
           (!warnings) andalso
         instance_count = List.length (linarithData.all_instances ()) andalso
         injection_count = List.length (linarithData.injections ())
       end)

fun neq tm = boolSyntax.mk_neg tm

val nx = Term.mk_var ("linarith_neq_num", numSyntax.num)
val jx = Term.mk_var ("linarith_neq_int", intSyntax.int_ty)
val sx = Term.mk_var ("linarith_neq_real", realSyntax.real_ty)
val tx = Term.mk_var ("linarith_neq_rat", ratSyntax.rat_ty)
val num_eq0 = boolSyntax.mk_eq (nx, numSyntax.zero_tm)
val int_eq0 = boolSyntax.mk_eq (jx, i0)
val real_eq0 = boolSyntax.mk_eq (sx, r0)
val rat_eq0 = boolSyntax.mk_eq (tx, q0)
val equalities = [num_eq0, int_eq0, real_eq0, rat_eq0]
val disequalities = map neq equalities
val zero_bounds =
  [numSyntax.mk_leq (numSyntax.zero_tm, nx),
   numSyntax.mk_leq (nx, numSyntax.zero_tm),
   ileq i0 jx, ileq jx i0,
   rleq r0 sx, rleq sx r0,
   qleq q0 tx, qleq tx q0]
val neq_config : linarithData.linarith_config =
  {neq_limit = 4, split_limit = 9}

fun cross_neq_forward order =
  let
    val assumptions = map Thm.ASSUME (order @ zero_bounds)
  in
    Term.aconv
      (Thm.concl
        (linarithReplay.fwd_prove neq_config assumptions boolSyntax.F))
      boolSyntax.F
  end

val _ =
  check
    ("cross-type neq replay is independent of premise permutation",
     fn () =>
       cross_neq_forward disequalities andalso
       cross_neq_forward (List.rev disequalities) andalso
       valid_closes
         (linarithLib.CFG_LINARITH_TAC neq_config [])
         (disequalities @ zero_bounds, boolSyntax.F) andalso
       valid_closes
         (linarithLib.CFG_LINARITH_TAC neq_config [])
         (List.rev disequalities @ zero_bounds, boolSyntax.F))

val side_ss =
  simpLib.++ (boolSimps.bool_ss, linarithLib.LINARITH_ss)

fun conditional_goal condition =
  boolSyntax.mk_eq
    (boolSyntax.mk_cond (condition, boolSyntax.T, boolSyntax.F),
     boolSyntax.T)

val _ =
  check
    ("LINARITH_ss discharges int real and rat side conditions",
     fn () =>
       valid_closes (simpLib.FULL_SIMP_TAC side_ss [])
         ([ileq ix iy, ileq iy iz], conditional_goal (ileq ix iz)) andalso
       valid_closes (simpLib.FULL_SIMP_TAC side_ss [])
         ([rleq rx ry, rleq ry rz], conditional_goal (rleq rx rz)) andalso
       valid_closes (simpLib.FULL_SIMP_TAC side_ss [])
         ([qleq qx qy, qleq qy qz], conditional_goal (qleq qx qz)))

(* Translation of all 54 lemma goals in Isabelle's Arith_Examples.thy at
   f7e02b7e1f31.  Isabelle's nat coercion truncates negative integers, so
   [20], [21], [53], and [54] use Num (int_max i 0), rather than HOL4's
   absolute-value Num coercion.  Both upstream "oops" goals are retained:
   [47] is proved here, because splitting on demand never builds the
   disjunctive normal form whose size defeated upstream, while [48] is
   the corpus's one method boundary -- linear arithmetic's documented
   integer-divisibility incompleteness -- asserted to be reported,
   promptly and by that name, rather than run into.

   On 2026-08-02 the full instances selftest took 10.0s at level 2 versus
   7.7s at level 1 on an AMD Ryzen 9 9950X, down from 50.2s at level 2
   before the tactics began splitting on demand.  The 120s suite budget,
   30s goal budget, and 5s boundary budget deliberately leave ample
   headroom.

   linarithCorpus owns the driver, the budgets and the canonical goal
   numbering; the numbering check below pins this list to all of it. *)

val arith_examples_corpus : strength_goal list =
  [(1, StrengthSuccess, “(i:num) <= MAX i j”),
   (2, StrengthSuccess, “(i:int) <= int_max i j”),
   (3, StrengthSuccess, “MIN i j <= (i:num)”),
   (4, StrengthSuccess, “int_min i j <= (i:int)”),
   (5, StrengthSuccess, “MIN (i:num) j <= MAX i j”),
   (6, StrengthSuccess,
    “int_min (i:int) j <= int_max i j”),
   (7, StrengthSuccess,
    “MIN (i:num) j + MAX i j = i + j”),
   (8, StrengthSuccess,
    “int_min (i:int) j + int_max i j = i + j”),
   (9, StrengthSuccess,
    “(i:num) < j ==> MIN i j < MAX i j”),
   (10, StrengthSuccess,
    “(i:int) < j ==> int_min i j < int_max i j”),
   (11, StrengthSuccess, “(0:int) <= ABS i”),
   (12, StrengthSuccess, “(i:int) <= ABS i”),
   (13, StrengthSuccess, “ABS (ABS (i:int)) = ABS i”),
   (14, StrengthSuccess, “(x:num) <= y ==> x - y = 0”),
   (15, StrengthSuccess, “(x:num) - y = 0 ==> x <= y”),
   (16, StrengthSuccess, “((x:num) <= y) = (x - y = 0)”),
   (17, StrengthSuccess,
    “(x:num) < y /\ d < 1 ==> x - y = d”),
   (18, StrengthSuccess,
    “(x:num) < y /\ d < 1 ==> x - y - x = d - x”),
   (19, StrengthSuccess, “(x:int) < y ==> x - y < 0”),
   (20, StrengthSuccess,
    “Num (int_max ((i:int) + j) 0) <=
     Num (int_max i 0) + Num (int_max j 0)”),
   (21, StrengthSuccess,
    “(i:int) < j ==> Num (int_max (i - j) 0) = 0”),
   (22, StrengthSuccess, “(i:num) MOD 0 = i”),
   (23, StrengthSuccess, “(i:num) MOD 1 = 0”),
   (24, StrengthSuccess, “(i:num) MOD 42 <= 41”),
   (* HOL4 int_mod is unspecified at zero.  Isabelle's total zmod
      source goal therefore translates to its specified result. *)
   (25, StrengthSuccess, “(i:int) = i”),
   (26, StrengthSuccess, “(i:int) % 1 = 0”),
   (27, StrengthSuccess, “(i:int) % 42 <= 41”),
   (28, StrengthSuccess, “-(i:int) * 1 = 0 ==> i = 0”),
   (29, StrengthSuccess,
    “(0:int) < ABS i /\ ABS i * 1 < ABS i * j ==>
     1 < ABS i * j”),
   (30, StrengthSuccess, “(x:num) < SUC y <=> x <= y”),
   (31, StrengthSuccess,
    “((x:num) = z ==> x <> y) ==> x <> y \/ z <> y”),
   (32, StrengthSuccess, “((x:num) < SUC y) = (x <= y)”),
   (33, StrengthSuccess,
    “(x:num) < y /\ y < z ==> x < z”),
   (34, StrengthSuccess,
    “(x:num) < y /\ y < z ==> x < z”),
   (35, StrengthSuccess, “(P:bool) = Q ==> Q = P”),
   (36, StrengthSuccess,
    “P = ((x:num) = 0) /\ ~P = (y = 0) ==> MIN x y = 0”),
   (37, StrengthSuccess,
    “P = ((x:num) = 0) /\ ~P = (y = 0) ==>
     MAX x y = x + y”),
   (38, StrengthSuccess,
    “(x:num) <> y /\ a + 2 = b /\ a < y /\ y < b /\
     a < x /\ x < b ==> F”),
   (39, StrengthSuccess,
    “y < (x:num) /\ z < y /\ x < z ==> F”),
   (40, StrengthSuccess, “y < (x:num) - 5 ==> y < x”),
   (41, StrengthSuccess, “(x:num) <> 0 ==> 0 < x”),
   (42, StrengthSuccess,
    “(x:num) <> y /\ x <= y ==> x < y”),
   (43, StrengthSuccess,
    “(x:num) < y /\ P (x - y) ==> P 0”),
   (44, StrengthSuccess,
    “(x - y) - (x:num) = (x - x) - y”),
   (45, StrengthSuccess,
    “(a:num) < b /\ c < d ==> a - b = c - d”),
   (46, StrengthSuccess,
    “(a:num) - (b - (c - (d - e))) =
     a - (b - (c - (d - e)))”),
   (47, StrengthSuccess,
    “((n:num) < m /\ m < n') \/
     (n < m /\ m = n') \/
     (n < n' /\ n' < m) \/
     (n = n' /\ n' < m) \/
     (n = m /\ m < n') \/
     (n' < m /\ m < n) \/
     (n' < m /\ m = n) \/
     (n' < n /\ n < m) \/
     (n' = n /\ n < m) \/
     (n' = m /\ m < n) \/
     (m < n /\ n < n') \/
     (m < n /\ n' = n) \/
     (m < n' /\ n' < n) \/
     (m = n /\ n < n') \/
     (m = n' /\ n' < n) \/
     (n' = m /\ m = n)”),
   (48,
    StrengthExpectedFailure
      {error = "CFG_LINARITH_TAC: linear arithmetic found no proof",
       remedy =
         "requires intLib.ARITH_TAC/COOPER_TAC (integer divisibility)"},
    “2 * (x:num) <> 1”),
   (49, StrengthSuccess, “(0:num) < 1”),
   (50, StrengthSuccess, “(0:int) < 1”),
   (51, StrengthSuccess, “(47:num) + 11 < 8 * 15”),
   (52, StrengthSuccess, “(47:int) + 11 < 8 * 15”),
   (53, StrengthSuccess,
    “(a:num) <> b /\ (i:int) <> j /\ a < 2 /\ b < 2 ==>
     a + b <= Num (int_max (ABS i) (ABS j))”),
   (54, StrengthSuccess,
    “(i:int) <> j /\ (a:num) <> b /\ a < 2 /\ b < 2 ==>
     a + b <= Num (int_max (ABS i) (ABS j))”)]

val _ =
  check_numbering
    {suite = "Arith_Examples", numbering = full_numbering}
    arith_examples_corpus

val _ =
  if selftest_level () >= 2 then
    run_suite
      {suite = "Arith_Examples",
       tactic = fn () => linarithLib.LINARITH_TAC [],
       suite_budget = Time.fromSeconds 120,
       expected_successes = 53,
       expected_boundaries = 1}
      arith_examples_corpus
  else ()
