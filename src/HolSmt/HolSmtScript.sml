(* Copyright (c) 2009-2010 Tjark Weber. All rights reserved. *)

(* Various theorems for HolSmtLib *)
Theory HolSmt
Ancestors[qualified]
  bool realax real intreal integer combin words rich_list

  val op >> = Tactical.>>

  val T = tautLib.TAUT_PROVE
  val P = bossLib.PROVE []
  val S = simpLib.SIMP_PROVE (simpLib.++ (simpLib.++ (simpLib.++
    (bossLib.list_ss, boolSimps.COND_elim_ss), wordsLib.WORD_ss),
    wordsLib.WORD_BIT_EQ_ss)) [boolTheory.EQ_SYM_EQ]
  val A = intLib.ARITH_PROVE
  val R = RealArith.REAL_ARITH
  val W = wordsLib.WORD_DECIDE
  val B = blastLib.BBLAST_PROVE
  val M = bossLib.METIS_PROVE
  val I = simpLib.SIMP_PROVE (simpLib.++ (simpLib.++
    (bossLib.arith_ss, intSimps.INT_RWTS_ss), intSimps.INT_ARITH_ss))

  (* simplify 't' using 'thms', then prove the simplified term using
     'TAUT_PROVE' *)
  fun U thms t =
  let
    val t_eq_t' = simpLib.SIMP_CONV (simpLib.++ (simpLib.++ (simpLib.++
      (bossLib.std_ss, boolSimps.COND_elim_ss), wordsLib.WORD_ss),
      wordsLib.WORD_BIT_EQ_ss)) thms t
    val t' = tautLib.TAUT_PROVE (boolSyntax.rhs (Thm.concl t_eq_t'))
  in
    Thm.EQ_MP (Thm.SYM t_eq_t') t'
  end

  val s = Theory.save_thm

  val _ = ParseExtras.temp_loose_equality()

  (* constants used by Z3 *)

  (* real division -- in SMT-LIB, division by zero is not defined,
     unlike in HOL4 *)
  val smt_rdiv_exists = P ``?f. !x y. (y <> 0r) ==> (f x y = x / y)``
  val smt_rdiv_def = bossLib.new_specification ("smt_rdiv", ["smt_rdiv"],
    smt_rdiv_exists)

  val _ = s ("real_div_smt_rdiv", M [realaxTheory.real_div,
    realTheory.REAL_INV_0, realTheory.REAL_MUL_RZERO, smt_rdiv_def]
    ``!x y. x / y = if y = 0 then 0 else smt_rdiv x y``)

Theorem smt_rdiv_zero:
  !y. y <> 0r ==> (smt_rdiv 0r y = 0r)
Proof
  simp [smt_rdiv_def, realTheory.REAL_DIV_LZERO]
QED

(* The solver-side division interface agrees with HOL division exactly away
   from zero.  Export this directional form for proof replayers, which must
   never unfold the unconstrained zero-divisor branch. *)
Theorem smt_rdiv_eq_div:
  !x y. y <> 0r ==> (smt_rdiv x y = x / y)
Proof
  simp [smt_rdiv_def]
QED

Theorem smt_rdiv_refl:
    !x. x <> 0r ==> (smt_rdiv x x = 1r)
Proof
    simp [smt_rdiv_def, realTheory.REAL_DIV_REFL]
QED

Theorem smt_rdiv_one:
    !x. smt_rdiv x 1r = x
Proof
    simp [smt_rdiv_def, realaxTheory.real_div,
          realTheory.REAL_INV_1, realTheory.REAL_MUL_RID]
QED

Theorem smt_rdiv_neg_refl:
    !x. x <> 0r ==> (smt_rdiv x (-x) = -1r)
Proof
    simp [smt_rdiv_def, realTheory.REAL_DIV_REFL,
          realTheory.REAL_DIV_RNEG]
QED

Theorem smt_rdiv_neg_one:
  !x. smt_rdiv x (-1r) = -x
Proof
  simp [smt_rdiv_def, realTheory.REAL_DIV_RNEG,
        realaxTheory.real_div, realTheory.REAL_INV_1]
QED

(* Sign normalization for totalized SMT division.  These are guarded exactly
   where the specification agrees with HOL division, so they are useful
   replay lemmas without assigning a meaning to division by zero. *)
Theorem smt_rdiv_lneg:
  !x y. y <> 0r ==> (smt_rdiv (-x) y = -smt_rdiv x y)
Proof
  simp [smt_rdiv_def, realTheory.REAL_DIV_LNEG]
QED

Theorem smt_rdiv_rneg:
  !x y. y <> 0r ==> (smt_rdiv x (-y) = -smt_rdiv x y)
Proof
  simp [smt_rdiv_def, realTheory.REAL_DIV_RNEG]
QED

(* Z3 represents inverse by this explicit totalization.  These boundary
   lemmas identify that macro with HOL's total inverse, including at zero. *)
Theorem smt_rinv_def:
  !x. (if x = 0r then 0r else 1r / x) = realinv x
Proof
  rw [GSYM realTheory.REAL_INV_1OVER] >>
  Cases_on `x = 0r` >> simp [realTheory.REAL_INV_0]
QED

Theorem smt_rinv_inv:
  !x. (if (if x = 0r then 0r else 1r / x) = 0r then 0r
       else 1r / (if x = 0r then 0r else 1r / x)) = x
Proof
  simp [smt_rinv_def, realTheory.REAL_INV_INV]
QED

(* SMT sequence access is specified only for in-range indices.  This
   polymorphic choice is deliberately introduced by specification, rather
   than defining an out-of-range value: the latter is solver-underspecified.
   It is the list counterpart of smtstringz3Theory.seq_nth_i. *)
Theorem smt_seq_nth_exists[local]:
  ?f : 'a list -> int -> 'a.
    !s i. (0 <= i /\ Num i < LENGTH s) ==>
      (f s i = EL (Num i) s)
Proof
  qexists `\s i.
    if 0 <= i /\ Num i < LENGTH s then EL (Num i) s else @x. T` >>
  simp []
QED

val smt_seq_nth_spec =
  new_specification
    ("smt_seq_nth_spec", ["smt_seq_nth"], smt_seq_nth_exists);

Theorem smt_seq_nth_def = smt_seq_nth_spec

(* Generic list counterparts of the shared SMT sequence operations whose
   semantics are not a single stock list constant. *)
Definition smt_seq_extract_def:
  smt_seq_extract (s : 'a list) (i : int) (n : int) =
    if i < 0 \/ n <= 0 \/ LENGTH s <= Num i then []
    else TAKE (Num n) (DROP (Num i) s)
End

Definition smt_seq_at_def:
  smt_seq_at (s : 'a list) (i : int) =
    if i < 0 \/ LENGTH s <= Num i then [] else [EL (Num i) s]
End

Definition smt_seq_indexof_aux_def:
  (smt_seq_indexof_aux (t : 'a list) n [] =
     if t = [] then SOME n else NONE) /\
  (smt_seq_indexof_aux t n (h::s) =
     if IS_PREFIX (h::s) t then SOME n
     else smt_seq_indexof_aux t (SUC n) s)
End

Definition smt_seq_indexof_def:
  smt_seq_indexof (s : 'a list) t (i : int) : int =
    if i < 0 \/ LENGTH s < Num i then -1
    else
      case smt_seq_indexof_aux t (Num i) (DROP (Num i) s) of
        NONE => -1
      | SOME n => &n
End

Definition smt_seq_replace_raw_def:
  smt_seq_replace_raw (s : 'a list) t u =
    case smt_seq_indexof_aux t 0 s of
      NONE => s
    | SOME n => TAKE n s ++ u ++ DROP (n + LENGTH t) s
End

Definition smt_seq_replace_def:
  smt_seq_replace (s : 'a list) t u = smt_seq_replace_raw s t u
End

(* cvc5's update replaces the segment beginning at i.  Like LUPDATE it is
   a no-op outside the source sequence; its replacement is clipped at the
   end of that source sequence. *)
Definition smt_seq_update_def:
  smt_seq_update (s : 'a list) (i : int) (t : 'a list) =
    if i < 0 \/ LENGTH s <= Num i then s
    else TAKE (Num i) s ++ TAKE (LENGTH s - Num i) t ++
      DROP (Num i + LENGTH t) s
End

(* cvc5's CPC proof format totalizes integer Euclidean division and modulus.
   Unlike HOL's ediv/emod, these operators have specified zero-divisor
   branches, so model them explicitly in the shared HolSmt theory. *)
Definition smt_ediv_total_def:
  smt_ediv_total a b = if b = 0 then 0 else ediv a b
End

Definition smt_emod_total_def:
  smt_emod_total a b = if b = 0 then a else emod a b
End

Theorem smt_ediv_total_compute[compute]:
  smt_ediv_total a b =
    if b = 0 then 0 else if 0 < b then a / b else -(a / -b)
Proof
  simp [smt_ediv_total_def, integerTheory.EDIV_DEF]
QED

Theorem smt_emod_total_compute[compute]:
  smt_emod_total a b = if b = 0 then a else a % ABS b
Proof
  simp [smt_emod_total_def, integerTheory.EMOD_DEF]
QED

Theorem smt_ediv_total_eq_ediv:
  !a b. b <> 0 ==> (smt_ediv_total a b = ediv a b)
Proof
  simp [smt_ediv_total_def]
QED

Theorem smt_emod_total_eq_emod:
  !a b. b <> 0 ==> (smt_emod_total a b = emod a b)
Proof
  simp [smt_emod_total_def]
QED

Theorem smt_ediv_total_one:
  !a. smt_ediv_total a 1 = a
Proof
  simp [smt_ediv_total_def, integerTheory.EDIV_DEF]
QED

Theorem smt_ediv_total_zero:
  !a. smt_ediv_total a 0 = 0
Proof
  simp [smt_ediv_total_def]
QED

Theorem smt_emod_total_one:
  !a. smt_emod_total a 1 = 0
Proof
  simp [smt_emod_total_def, integerTheory.EMOD_DEF,
        integerTheory.INT_MOD_1]
QED

Theorem smt_emod_total_zero:
  !a. smt_emod_total a 0 = a
Proof
  simp [smt_emod_total_def]
QED

Theorem smt_ediv_total_neg:
  !a b. b < 0 ==> (smt_ediv_total a b = -smt_ediv_total a (-b))
Proof
  rpt gen_tac >> strip_tac >>
  `b <> 0` by intLib.ARITH_TAC >>
  `0 < -b` by intLib.ARITH_TAC >>
  `~(0 < b)` by intLib.ARITH_TAC >>
  `-b <> 0` by intLib.ARITH_TAC >>
  ASM_SIMP_TAC bossLib.arith_ss [smt_ediv_total_def,
    integerTheory.EDIV_DEF]
QED

Theorem smt_emod_total_neg:
  !a b. b < 0 ==> (smt_emod_total a b = smt_emod_total a (-b))
Proof
  rpt gen_tac >> strip_tac >>
  `b <> 0` by intLib.ARITH_TAC >>
  `0 < -b` by intLib.ARITH_TAC >>
  `~(0 < b)` by intLib.ARITH_TAC >>
  `-b <> 0` by intLib.ARITH_TAC >>
  ASM_SIMP_TAC bossLib.arith_ss [smt_emod_total_def,
    integerTheory.EMOD_DEF, integerTheory.INT_ABS_NEG]
QED

Theorem smt_emod_ediv_neg:
  !a b. b < 0 ==> (emod a b = a - b * ediv a b)
Proof
  rpt gen_tac >> strip_tac >>
  SUBGOAL_THEN ``(-b:int) <> 0`` ASSUME_TAC THEN1 intLib.ARITH_TAC >>
  SUBGOAL_THEN ``(0:int) < -b`` ASSUME_TAC THEN1 intLib.ARITH_TAC >>
  SUBGOAL_THEN ``~((0:int) < b)`` ASSUME_TAC THEN1 intLib.ARITH_TAC >>
  MP_TAC (Q.SPEC `a:int`
    (MATCH_MP (Q.SPEC `-b:int` integerTheory.INT_DIVISION)
      (ASSUME ``(-b:int) <> 0``))) >>
  STRIP_TAC >>
  ASM_SIMP_TAC bossLib.arith_ss [integerTheory.EDIV_DEF,
    integerTheory.EMOD_DEF, integerTheory.INT_ABS] >>
  intLib.ARITH_TAC
QED

Theorem smt_emod_ediv_pos:
  !a b. 0 < b ==> (emod a b = a - b * ediv a b)
Proof
  rpt gen_tac >> strip_tac >>
  SUBGOAL_THEN ``(b:int) <> 0`` ASSUME_TAC THEN1 intLib.ARITH_TAC >>
  SUBGOAL_THEN ``~((b:int) < 0)`` ASSUME_TAC THEN1 intLib.ARITH_TAC >>
  MP_TAC (Q.SPEC `a:int`
    (MATCH_MP (Q.SPEC `b:int` integerTheory.INT_DIVISION)
      (ASSUME ``(b:int) <> 0``))) >>
  STRIP_TAC >>
  ASM_SIMP_TAC bossLib.arith_ss [integerTheory.EDIV_DEF,
    integerTheory.EMOD_DEF, integerTheory.INT_ABS] >>
  intLib.ARITH_TAC
QED

Theorem smt_ediv_bounds_pos_aux:
  !q r v:int. 0 < v /\ 0 <= r /\ r < v ==>
    v * q <= q * v + r /\ q * v + r < v * (q + 1)
Proof
  rpt gen_tac >> strip_tac >> CONJ_TAC
  >- (CONV_TAC (LAND_CONV (REWR_CONV
        (Q.SPECL [`q:int`, `v:int`] integerTheory.INT_MUL_COMM))) >>
      ASM_SIMP_TAC bossLib.arith_ss [integerTheory.INT_LE_ADDR])
  >- (CONV_TAC (RAND_CONV (REWR_CONV integerTheory.INT_LDISTRIB)) >>
      CONV_TAC (RAND_CONV (LAND_CONV (REWR_CONV
        (Q.SPECL [`q:int`, `v:int`] integerTheory.INT_MUL_COMM)))) >>
      ASM_SIMP_TAC bossLib.arith_ss [integerTheory.INT_LT_LADD,
        integerTheory.INT_MUL_RID])
QED

Theorem smt_ediv_bounds_neg_aux:
  !q r v:int. v < 0 /\ 0 <= r /\ r < -v ==>
    v * -q <= q * -v + r /\ q * -v + r < v * (-q - 1)
Proof
  rpt gen_tac >> strip_tac >> CONJ_TAC
  >- (REWRITE_TAC [integerTheory.INT_MUL_RNEG] >>
      CONV_TAC (LAND_CONV (RAND_CONV (REWR_CONV
        (Q.SPECL [`q:int`, `v:int`] integerTheory.INT_MUL_COMM)))) >>
      ASM_SIMP_TAC bossLib.arith_ss [integerTheory.INT_LE_ADDR])
  >- (REWRITE_TAC [integerTheory.INT_SUB_LDISTRIB,
        integerTheory.INT_MUL_RNEG, integerTheory.INT_MUL_RID] >>
      CONV_TAC (LAND_CONV (LAND_CONV (RAND_CONV (REWR_CONV
        (Q.SPECL [`v:int`, `q:int`] integerTheory.INT_MUL_COMM))))) >>
      ASM_SIMP_TAC bossLib.arith_ss [integerTheory.int_sub,
        integerTheory.INT_LT_LADD])
QED

Theorem smt_ediv_bounds_pos_bridge:
  !q r u v:int. 0 < v /\ 0 <= r /\ r < v /\
    (u = q * v + r) ==>
    v * q <= u /\ u < v * (q + 1)
Proof
  rpt gen_tac >> strip_tac >>
  METIS_TAC [smt_ediv_bounds_pos_aux]
QED

Theorem smt_ediv_bounds_neg_bridge:
  !q r u v:int. v < 0 /\ 0 <= r /\ r < -v /\
    (u = q * -v + r) ==>
    v * -q <= u /\ u < v * (-q - 1)
Proof
  rpt gen_tac >> strip_tac >>
  METIS_TAC [smt_ediv_bounds_neg_aux]
QED

Theorem smt_ediv_total_bounds:
  !u v.
    (0 < v ==> v * smt_ediv_total u v <= u /\
               u < v * (smt_ediv_total u v + 1)) /\
    (v < 0 ==> v * smt_ediv_total u v <= u /\
               u < v * (smt_ediv_total u v - 1))
Proof
  rpt gen_tac >> CONJ_TAC
  >- (strip_tac >>
      `v <> 0` by intLib.ARITH_TAC >>
      MP_TAC (Q.SPEC `u:int`
        (MATCH_MP (Q.SPEC `v:int` integerTheory.INT_DIVISION)
          (ASSUME ``(v:int) <> 0``))) >>
      STRIP_TAC >>
      `~((v:int) < 0)` by intLib.ARITH_TAC >>
      Q.PAT_X_ASSUM `if (v:int) < 0 then _ else _`
        (fn h => MP_TAC h >>
          ASM_SIMP_TAC bossLib.arith_ss [] >>
          STRIP_TAC >>
          ASM_SIMP_TAC bossLib.arith_ss [smt_ediv_total_def,
            integerTheory.EDIV_DEF] >>
          MATCH_MP_TAC (Q.SPECL
            [`u / v:int`, `u % v:int`, `u:int`, `v:int`]
            smt_ediv_bounds_pos_bridge) >>
          CONJ_TAC
          >- ACCEPT_TAC (ASSUME ``(0:int) < v``)
          >- (CONJ_TAC
              >- ACCEPT_TAC (ASSUME ``(0:int) <= u % v``)
              >- (CONJ_TAC
                  >- ACCEPT_TAC (ASSUME ``(u % v:int) < v``)
                  >- ACCEPT_TAC
                    (ASSUME ``(u:int) = u / v * v + u % v``)))))
  >- (strip_tac >>
      `(-v:int) <> 0` by intLib.ARITH_TAC >>
      `0 < (-v:int)` by intLib.ARITH_TAC >>
      `~((-v:int) < 0)` by intLib.ARITH_TAC >>
      `~((0:int) < v)` by intLib.ARITH_TAC >>
      `(v:int) <> 0` by intLib.ARITH_TAC >>
      MP_TAC (Q.SPEC `u:int`
        (MATCH_MP (Q.SPEC `-v:int` integerTheory.INT_DIVISION)
          (ASSUME ``(-v:int) <> 0``))) >>
      STRIP_TAC >>
      Q.PAT_X_ASSUM `if (-v:int) < 0 then _ else _`
        (fn h => MP_TAC h >>
          ASM_SIMP_TAC bossLib.arith_ss [] >>
          STRIP_TAC >>
          ASM_SIMP_TAC bossLib.arith_ss [smt_ediv_total_def,
            integerTheory.EDIV_DEF] >>
          MATCH_MP_TAC (Q.SPECL
            [`u / -v:int`, `u % -v:int`, `u:int`, `v:int`]
            smt_ediv_bounds_neg_bridge) >>
          CONJ_TAC
          >- ACCEPT_TAC (ASSUME ``(v:int) < 0``)
          >- (CONJ_TAC
              >- ACCEPT_TAC (ASSUME ``(0:int) <= u % -v``)
              >- (CONJ_TAC
                  >- ACCEPT_TAC (ASSUME ``(u % -v:int) < -v``)
                  >- ACCEPT_TAC
                    (ASSUME ``(u:int) = u / -v * -v + u % -v``)))))
QED

Theorem smt_emod_total_ediv:
  !a b. smt_emod_total a b = a - b * smt_ediv_total a b
Proof
  gen_tac >> gen_tac >> Cases_on `b = 0` THENL
  [ simp [smt_ediv_total_def, smt_emod_total_def],
    ASM_REWRITE_TAC [smt_ediv_total_def, smt_emod_total_def] >>
    Cases_on `b < 0` THENL
    [ ACCEPT_TAC (Q.SPEC `a:int`
        (MATCH_MP smt_emod_ediv_neg
          (ASSUME ``(b:int) < 0``))),
      `0 < b` by intLib.ARITH_TAC >>
      ACCEPT_TAC (Q.SPEC `a:int`
        (MATCH_MP smt_emod_ediv_pos
          (ASSUME ``(0:int) < b``))) ] ]
QED

Theorem smt_emod_total_ediv_negone:
  !a b. smt_emod_total a b =
    a + -1 * (b * smt_ediv_total a b)
Proof
  simp [smt_emod_total_ediv, integerTheory.int_sub,
        GSYM integerTheory.INT_NEG_LMUL]
QED

Theorem smt_int_abs_gt:
  !x y : int.
    (ABS x > ABS y) =
    if x >= 0 then
      if y >= 0 then x > y else x > -y
    else if y >= 0 then -x > y else -x > -y
Proof
  rw [integerTheory.INT_ABS, integerTheory.INT_GT,
      integerTheory.INT_GE, integerTheory.int_le]
QED

Theorem smt_int_abs_mul_gt:
  !a b t u : int.
    (ABS a > ABS b) /\ (ABS t = ABS u) /\ t <> 0 ==>
    (ABS (a * t) > ABS (b * u))
Proof
  rpt strip_tac >>
  `0 < ABS t` by simp [] >>
  `0 < ABS a - ABS b` by
    fs [integerTheory.INT_SUB_LT, integerTheory.INT_GT] >>
  `0 < (ABS a - ABS b) * ABS t` by
    (match_mp_tac (REWRITE_RULE [integerTheory.INT_0]
       integerTheory.INT_LT_MUL) >> fs []) >>
  fs [GSYM integerTheory.INT_ABS_MUL, integerTheory.INT_GT,
      integerTheory.int_sub, integerTheory.INT_RDISTRIB,
      GSYM integerTheory.INT_NEG_LMUL] >>
  Q.PAT_X_ASSUM `ABS t = ABS u`
    (fn th => REWRITE_TAC [GSYM th]) >>
  intLib.ARITH_TAC
QED

  (* exclusive or *)
  val xor_def = bossLib.Define `xor x y = ~(x <=> y)`

  (* array_ext[T] yields an index i such that select A i <> select B i
     (provided A and B are different arrays of type T) *)
  val array_ext_def = bossLib.Define `array_ext A B = @i. A i <> B i`

  (* translation of HOL constants *)

  val int_ceiling_floor = s ("int_ceiling_floor",
    M [intrealTheory.INT_CEILING_NEG, realTheory.REAL_NEGNEG]
      ``!r. clgtoks r = -flrtoks (-r)``)

  (* used for Z3 proof reconstruction *)

  val _ = s ("ALL_DISTINCT_NIL", S ``ALL_DISTINCT [] = T``)
  val _ = s ("ALL_DISTINCT_CONS", S
    ``!h t. ALL_DISTINCT (h::t) = ~MEM h t /\ ALL_DISTINCT t``)
  val _ = s ("NOT_MEM_NIL", S ``!x. ~MEM x [] = T``)
  val _ = s ("NOT_MEM_CONS", S ``!x h t. ~MEM x (h::t) = (x <> h) /\ ~MEM x t``)
  val _ = s ("AND_T", T ``!p. p /\ T <=> p``)
  val _ = s ("T_AND", T ``(T /\ p <=> T /\ q) ==> (p <=> q)``)
  val _ = s ("F_OR", T ``(F \/ p <=> F \/ q) ==> (p <=> q)``)
  val _ = s ("CONJ_CONG", T ``(p <=> q) ==> (r <=> s) ==> (p /\ r <=> q /\ s)``)
  val _ = s ("NOT_NOT_ELIM", T ``!p. ~~p ==> p``)
  val _ = s ("NOT_NOT_INTRO", T ``!p. p <=> ~~p``)
  val _ = s ("NOT_REVERSE", T ``(p <=> ~q) ==> (q <=> ~p)``)
  val _ = s ("NOT_FALSE", T ``!p. p ==> ~p ==> F``)
  val _ = s ("NNF_CONJ", T
    ``!p q r s. (~p <=> r) ==> (~q <=> s) ==> (~(p /\ q) <=> r \/ s)``)
  val _ = s ("NNF_DISJ", T
    ``!p q r s. (~p <=> r) ==> (~q <=> s) ==> (~(p \/ q) <=> r /\ s)``)
  val _ = s ("NNF_NOT_NOT", T ``!p q. (p <=> q) ==> (~~p <=> q)``)
  val _ = s ("NEG_IFF_1_1", T ``(q <=> p) ==> ~(p <=> ~q)``)
  val _ = s ("NEG_IFF_1_2", T ``~(p <=> ~q) ==> (q <=> p)``)
  val _ = s ("NEG_IFF_2_1", T ``(p <=> ~q) ==> ~(p <=> q)``)
  val _ = s ("NEG_IFF_2_2", T ``~(p <=> q) ==> (p <=> ~q)``)
  val _ = s ("DISJ_ELIM_1", T ``!p q r. (p \/ q ==> r) ==> p ==> r``)
  val _ = s ("DISJ_ELIM_2", T ``!p q r. (p \/ q ==> r) ==> q ==> r``)
  val _ = s ("IMP_DISJ_1", T ``(p ==> q) ==> ~p \/ q``)
  val _ = s ("IMP_DISJ_2", T ``(~p ==> q) ==> p \/ q``)
  val _ = s ("IMP_FALSE", T ``!p. (~p ==> F) ==> p``)
  val _ = s ("AND_IMP_INTRO_SYM", T ``p /\ q ==> r <=> p ==> q ==> r``)
  val _ = s ("VALID_IFF_TRUE", T ``!p. p ==> (p <=> T)``)
  val _ = s ("NOT_P_OR_P", T ``~p \/ p``)
  val _ = s ("SKOLEM_FORALL", P ``?a. ~(!x. P x) <=> ~(P a)``)
  val _ = s ("SKOLEM_EXISTS", P ``?a. (?x. P x) <=> P a``)

  val _ = s ("NUM_FORALL_TO_INT",
    M [integerTheory.INT_POS, integerTheory.NUM_OF_INT,
       integerTheory.INT_OF_NUM]
      ``!P. (!n :num. P n) <=> (!i :int. 0 <= i ==> P (Num i))``)
  val _ = s ("NUM_EXISTS_TO_INT",
    M [integerTheory.INT_POS, integerTheory.NUM_OF_INT,
       integerTheory.INT_OF_NUM]
      ``!P. (?n :num. P n) <=> (?i :int. 0 <= i /\ P (Num i))``)

  val _ = s ("NUM_TO_INT_GUARDED",
    M [integerTheory.INT_OF_NUM]
      ``!i :int. 0 <= i ==> (integer$int_of_num (Num i) = i)``)

  (* Bags are functions into num.  Relativizing that codomain by the same
     proved R1 pass used for a bare num gives the Int-array representation
     exactly its required pointwise non-negativity condition. *)
Theorem BAG_FORALL_TO_INT:
  !P. (!b : 'a -> num. P b) <=>
      (!c : 'a -> int. (!x. 0 <= c x) ==> P (\x. Num (c x)))
Proof
  gen_tac >> eq_tac
  >- (strip_tac >> gen_tac >> strip_tac >>
      qpat_x_assum `!b. P b`
        (fn th => ACCEPT_TAC (Q.SPEC `\x. Num (c x)` th)))
  >> strip_tac >> gen_tac >>
     qpat_x_assum `!c. (!x. 0 <= c x) ==> P (\x. Num (c x))`
       (mp_tac o Q.SPEC `\x. &(b x)`) >>
     Q.SUBGOAL_THEN `(\x. b x) = b` (fn th => simp[th]) >>
     simp[boolTheory.FUN_EQ_THM]
QED

Theorem BAG_EXISTS_TO_INT:
  !P. (?b : 'a -> num. P b) <=>
      (?c : 'a -> int. (!x. 0 <= c x) /\ P (\x. Num (c x)))
Proof
  gen_tac >> eq_tac
  >- (strip_tac >> qexists_tac `\x. &(b x)` >>
      Q.SUBGOAL_THEN `(\x. b x) = b` (fn th => simp[th]) >>
      simp[boolTheory.FUN_EQ_THM])
  >> strip_tac >> qexists_tac `\x. Num (c x)` >>
     qpat_x_assum `P (\x. Num (c x))` ACCEPT_TAC
QED

Theorem BAG_COUNT_INT_NONNEG:
  !b x. 0 <= integer$int_of_num (b x)
Proof
  simp[]
QED

  (* NUM_FLOOR is the natural-valued floor.  Below zero it is definitionally
     zero, so this closes the non-positive branch before num-to-int transfer
     instead of leaving a num-valued operator for the SMT encoder. *)
  val num_floor_nonpos = s ("num_floor_nonpos",
    M [realTheory.NUM_FLOOR_BASE, realTheory.REAL_LT_01,
       realTheory.REAL_LET_TRANS]
      ``!r. r <= 0 ==> (realax$NUM_FLOOR r = 0)``)

  (* Associativity of saturated natural subtraction.  Normalizing this
     identity before SMT translation avoids an otherwise large ite-expanded
     checked cvc5 arithmetic replay. *)
Theorem num_sub_assoc:
    !x y z:num. x - y - z = x - (y + z)
Proof
    Induct_on `x` >> simp[]
QED

Theorem num_floor_zero:
    realax$NUM_FLOOR 0r = 0n
Proof
    simp[]
QED

Theorem num_ceiling_zero:
    realax$NUM_CEILING 0r = 0n
Proof
    simp [int_ceiling_floor]
QED

  (* The cvc5 floor-introduction replay rule uses the remainder formulation
     of the floor
     bounds.  Derive it once from HOL's canonical floor interval theorem. *)
Theorem int_floor_remainder_bounds:
    !r.
      (0r <= r - real_of_int (intreal$INT_FLOOR r) /\
       r - real_of_int (intreal$INT_FLOOR r) < 1r)
Proof
    METIS_TAC [intrealTheory.INT_FLOOR_BOUNDS',
      R ``!r f:real.
          (r - 1r < f /\ f <= r) ==>
          (0r <= r - f /\ r - f < 1r)``]
QED

Theorem int_floor_zero[local]:
    intreal$INT_FLOOR 0r = 0i
Proof
    simp [intrealTheory.INT_FLOOR]
QED

Theorem int_floor_nonneg[local]:
    !r. 0r <= r ==> 0i <= intreal$INT_FLOOR r
Proof
    rpt strip_tac >> Cases_on `r = 0r` >- simp [int_floor_zero] >>
    `0r < r` by metis_tac [realTheory.REAL_LE_LT] >>
    `intreal$INT_FLOOR 0r <= intreal$INT_FLOOR r` by
      metis_tac [intrealTheory.INT_FLOOR_MONO] >>
    metis_tac [int_floor_zero]
QED

Theorem int_floor_nonpos[local]:
    !r. r <= 0r ==> intreal$INT_FLOOR r <= 0i
Proof
    rpt strip_tac >> Cases_on `r = 0r` >- simp [int_floor_zero] >>
    `r < 0r` by metis_tac [realTheory.REAL_LE_LT] >>
    `intreal$INT_FLOOR r <= intreal$INT_FLOOR 0r` by
      metis_tac [intrealTheory.INT_FLOOR_MONO] >>
    metis_tac [int_floor_zero]
QED

Theorem int_max_id[local]:
    !i:int. 0i <= i ==> (integer$int_max 0 i = i)
Proof
    rpt strip_tac >> simp [integerTheory.INT_MAX] >> intLib.ARITH_TAC
QED

Theorem int_max_zero[local]:
    !i:int. i <= 0i ==> (integer$int_max 0 i = 0)
Proof
    rpt strip_tac >> simp [integerTheory.INT_MAX] >> intLib.ARITH_TAC
QED

Theorem int_ceiling_nonneg[local]:
    !r. 0r <= r ==> 0i <= intreal$INT_CEILING r
Proof
    rpt strip_tac >>
    `-r <= 0r` by simp[] >>
    `intreal$INT_FLOOR (-r) <= 0i` by
      metis_tac [int_floor_nonpos] >>
    rw [int_ceiling_floor] >> intLib.ARITH_TAC
QED

Theorem int_ceiling_nonpos[local]:
    !r. r <= 0r ==> intreal$INT_CEILING r <= 0i
Proof
    rpt strip_tac >>
    `0r <= -r` by simp[] >>
    `0i <= intreal$INT_FLOOR (-r)` by
      metis_tac [int_floor_nonneg] >>
    rw [int_ceiling_floor] >> intLib.ARITH_TAC
QED

Theorem int_num_ceiling_total:
    !r. &(realax$NUM_CEILING r) =
        integer$int_max 0 (intreal$INT_CEILING r)
Proof
    gen_tac >> Cases_on `0r <= r`
    >- (rw [intrealTheory.INT_NUM_CEILING] >>
        sym_tac >> metis_tac [int_max_id, int_ceiling_nonneg])
    >- (`r <= 0r` by metis_tac [realTheory.REAL_NOT_LE,
                                 realTheory.REAL_LT_IMP_LE] >>
        rw [realTheory.NUM_CEILING_BASE] >>
        sym_tac >> metis_tac [int_max_zero, int_ceiling_nonpos,
                              int_ceiling_floor])
QED

  val _ = s ("num_ceiling_to_int_eq",
    M [int_num_ceiling_total, integerTheory.INT_INJ]
      ``!r n. (realax$NUM_CEILING r = n) <=>
          (integer$int_max 0 (intreal$INT_CEILING r) = &n)``)

Theorem int_num_floor_total:
    !r. &(realax$NUM_FLOOR r) =
        integer$int_max 0 (intreal$INT_FLOOR r)
Proof
    gen_tac >> Cases_on `0r <= r`
    >- (rw [intrealTheory.INT_NUM_FLOOR] >>
        sym_tac >> metis_tac [int_max_id, int_floor_nonneg])
    >- (`r <= 0r` by metis_tac [realTheory.REAL_NOT_LE,
                                 realTheory.REAL_LT_IMP_LE] >>
        rw [num_floor_nonpos] >>
        sym_tac >> metis_tac [int_max_zero, int_floor_nonpos])
QED

  val _ = s ("num_floor_to_int_eq",
    M [int_num_floor_total, integerTheory.INT_INJ]
      ``!r n. (realax$NUM_FLOOR r = n) <=>
          (integer$int_max 0 (intreal$INT_FLOOR r) = &n)``)

  val _ = s ("INT_NUM_EDIV",
    prove(
      ``!n m. integer$int_of_num (n DIV m) =
          if integer$int_of_num m = 0i then 0i
          else integer$ediv (integer$int_of_num n) (integer$int_of_num m)``,
      rpt strip_tac >> Cases_on `m` >- fs[] >>
      `integer$int_of_num (SUC n') <> 0i`
        by fs[integerTheory.INT_INJ] >>
      `0i < integer$int_of_num (SUC n')`
        by fs[integerTheory.INT_LT] >>
      metis_tac[integerTheory.INT_DIV, integerTheory.INT_DIV_EDIV]))

  val _ = s ("INT_NUM_EMOD",
    prove(
      ``!n m. integer$int_of_num (n MOD m) =
          if integer$int_of_num m = 0i then integer$int_of_num n
          else integer$emod (integer$int_of_num n) (integer$int_of_num m)``,
      rpt strip_tac >> Cases_on `m` >- fs[] >>
      `integer$int_of_num (SUC n') <> 0i`
        by fs[integerTheory.INT_INJ] >>
      `0i < integer$int_of_num (SUC n')`
        by fs[integerTheory.INT_LT] >>
      metis_tac[integerTheory.INT_MOD, integerTheory.INT_MOD_EMOD]))

  (* used for Z3's proof rule def-axiom *)

  val _ = s ("d001", T ``~(p <=> q) \/ ~p \/ q``)
  val _ = s ("d002", T ``~(p <=> q) \/ p \/ ~q``)
  val _ = s ("d003", T ``(p <=> ~q) \/ ~p \/ q``)
  val _ = s ("d004", T ``(~p <=> q) \/ p \/ ~q``)
  val _ = s ("d005", T ``(p <=> q) \/ ~p \/ ~q``)
  val _ = s ("d006", T ``(p <=> q) \/ p \/ q``)
  val _ = s ("d007", T ``~(~p <=> q) \/ p \/ q``)
  val _ = s ("d008", T ``~(p <=> ~q) \/ p \/ q``)
  val _ = s ("d009", T ``~p \/ q \/ ~(p <=> q)``)
  val _ = s ("d010", T ``p \/ ~q \/ ~(p <=> q)``)
  val _ = s ("d011", T ``p \/ q \/ ~(~p <=> q)``)
  val _ = s ("d012", T ``p \/ q \/ ~(p <=> ~q)``)
  val _ = s ("d013", T ``(~p /\ ~q) \/ p \/ q``)
  val _ = s ("d014", T ``(~p /\ q) \/ p \/ ~q``)
  val _ = s ("d015", T ``(p /\ ~q) \/ ~p \/ q``)
  val _ = s ("d016", T ``(p /\ q) \/ ~p \/ ~q``)
  val _ = s ("d017", P ``p \/ (y = if p then x else y)``)
  val _ = s ("d018", P ``~p \/ (x = if p then x else y)``)
  val _ = s ("d019", P ``p \/ ((if p then x else y) = y)``)
  val _ = s ("d020", P ``~p \/ ((if p then x else y) = x)``)
  val _ = s ("d021", P ``p \/ q \/ ~(if p then r else q)``)
  val _ = s ("d022", P ``~p \/ q \/ ~(if p then q else r)``)
  val _ = s ("d023", P ``(if p then q else r) \/ ~p \/ ~q``)
  val _ = s ("d024", P ``(if p then q else r) \/ p \/ ~r``)
  val _ = s ("d025", P ``(if p then ~q else r) \/ ~p \/ q``)
  val _ = s ("d026", P ``(if p then q else ~r) \/ p \/ r``)
  val _ = s ("d027", P ``~(if p then q else r) \/ ~p \/ q``)
  val _ = s ("d028", P ``~(if p then q else r) \/ p \/ r``)

  (* used for Z3's proof rule intro-def *)
  val _ = s ("i001", Drule.UNDISCH (T ``(n = t) ==> (n = t)``))
  val _ = s ("i002", Drule.UNDISCH (T ``(n = t) ==> ~n \/ t``))
  val _ = s ("i003", Drule.UNDISCH (T ``(n = t) ==> (n \/ ~t) /\ (~n \/ t)``))
  val _ = s ("i004", Drule.UNDISCH (P ``(n = if c then t1 else t2) ==> (~c \/ (n = t1)) /\ (c \/ (n = t2))``))
  (* Z3's C1-observed :lambda-def axioms expose one- and two-argument
     function definitions pointwise. *)
  val _ = s ("i005", Drule.UNDISCH (P
    ``(n = t) ==> (!x. t x = n x)``))
  val _ = s ("i006", Drule.UNDISCH (P
    ``(n = t) ==> (!x y. t x y = n x y)``))

  (* used for Z3's proof rule rewrite *)

  val _ = s ("r001", P ``(x = y) <=> (y = x)``)
  val _ = s ("r002", P ``(x = x) <=> T``)
  val _ = s ("r003", T ``(p <=> T) <=> p``)
  val _ = s ("r004", T ``(T <=> p) <=> p``)
  val _ = s ("r005", T ``(p <=> F) <=> ~p``)
  val _ = s ("r006", T ``(F <=> p) <=> ~p``)
  val _ = s ("r007", T ``(~p <=> ~q) <=> (p <=> q)``)
  val _ = s ("r008", T ``~(p <=> ~q) <=> (p <=> q)``)
  val _ = s ("r009", T ``~(~p <=> q) <=> (p <=> q)``)
  val _ = s ("r010", T ``(~p <=> q) <=> (p <=/=> q)``)

  val _ = s ("r011", P ``(if T then x else y) = x``)
  val _ = s ("r012", P ``(if F then x else y) = y``)
  val _ = s ("r013", T ``(if p then q else T) <=> (~p \/ q)``)
  val _ = s ("r014", T ``(if p then q else T) <=> (q \/ ~p)``)
  val _ = s ("r015", T ``(if p then q else ~q) <=> (p <=> q)``)
  val _ = s ("r016", T ``(if p then q else ~q) <=> (q <=> p)``)
  val _ = s ("r017", T ``(if p then ~q else q) <=> (p <=> ~q)``)
  val _ = s ("r018", T ``(if p then ~q else q) <=> (~q <=> p)``)
  val _ = s ("r019", P ``(if ~p then x else y) = (if p then y else x)``)
  val _ = s ("r020", P
    ``(if p then (if q then x else y) else x) = (if p /\ ~q then y else x)``)
  val _ = s ("r021", P
    ``(if p then (if q then x else y) else x) = (if ~q /\ p then y else x)``)
  val _ = s ("r022", P
    ``(if p then (if q then x else y) else y) = (if p /\ q then x else y)``)
  val _ = s ("r023", P
    ``(if p then (if q then x else y) else y) = (if q /\ p then x else y)``)
  val _ = s ("r024", P
    ``(if p then x else (if p then y else z)) = (if p then x else z)``)
  val _ = s ("r025", P
    ``(if p then x else (if q then x else y)) = (if p \/ q then x else y)``)
  val _ = s ("r026", P
    ``(if p then x else (if q then x else y)) = (if q \/ p then x else y)``)
  val _ = s ("r027", P
    ``(if p then x = y else x = z) <=> (x = if p then y else z)``)
  val _ = s ("r028", P
    ``(if p then x = y else y = z) <=> (y = if p then x else z)``)
  val _ = s ("r029", P
    ``(if p then x = y else z = y) <=> (y = if p then x else z)``)

  val _ = s ("r030", T ``(~p ==> q) <=> (p \/ q)``)
  val _ = s ("r031", T ``(~p ==> q) <=> (q \/ p)``)
  val _ = s ("r032", T ``~(p ==> q) <=> ~(~p \/ q)``)
  val _ = s ("r033", P ``~(?x. P x ==> Q) <=> ~?x. ~P x \/ Q``)
  val _ = s ("r034", P ``~(?x. P x ==> Q) <=> ~?x. Q \/ ~P x``)
  val _ = s ("r035", P ``~(?x. ~P x \/ Q) <=> ~?x. ~P x \/ Q``)
  val _ = s ("r036", P ``~(?x. ~P x \/ Q) <=> ~?x. Q \/ ~P x``)
  val _ = s ("r037", T ``(p ==> q) <=> (~p \/ q)``)
  val _ = s ("r038", T ``(p ==> q) <=> (q \/ ~p)``)
  val _ = s ("r039", T ``(T ==> p) <=> p``)
  val _ = s ("r040", T ``(p ==> T) <=> T``)
  val _ = s ("r041", T ``(F ==> p) <=> T``)
  val _ = s ("r042", T ``(p ==> p) <=> T``)
  val _ = s ("r043", T ``((p <=> q) ==> r) <=> (r \/ (q <=> ~p))``)

  val _ = s ("r044", T ``~T <=> F``)
  val _ = s ("r045", T ``~F <=> T``)
  val _ = s ("r046", T ``~~p <=> p``)

  val _ = s ("r047", T ``p \/ q <=> q \/ p``)
  val _ = s ("r048", T ``p \/ T <=> T``)
  val _ = s ("r049", T ``p \/ ~p <=> T``)
  val _ = s ("r050", T ``~p \/ p <=> T``)
  val _ = s ("r051", T ``T \/ p <=> T``)
  val _ = s ("r052", T ``p \/ F <=> p``)
  val _ = s ("r053", T ``F \/ p <=> p``)

  val _ = s ("r054", T ``p /\ q <=> q /\ p``)
  val _ = s ("r055", T ``p /\ T <=> p``)
  val _ = s ("r056", T ``T /\ p <=> p``)
  val _ = s ("r057", T ``p /\ F <=> F``)
  val _ = s ("r058", T ``F /\ p <=> F``)
  val _ = s ("r059", T ``p /\ q <=> ~(~p \/ ~q)``)
  val _ = s ("r060", T ``~p /\ q <=> ~(p \/ ~q)``)
  val _ = s ("r061", T ``p /\ ~q <=> ~(~p \/ q)``)
  val _ = s ("r062", T ``~p /\ ~q <=> ~(p \/ q)``)
  val _ = s ("r063", T ``p /\ q <=> ~(~q \/ ~p)``)
  val _ = s ("r064", T ``~p /\ q <=> ~(~q \/ p)``)
  val _ = s ("r065", T ``p /\ ~q <=> ~(q \/ ~p)``)
  val _ = s ("r066", T ``~p /\ ~q <=> ~(q \/ p)``)

  val _ = s ("r067", U [combinTheory.APPLY_UPDATE_ID] ``(x =+ f x) f = f``)

  val _ = s ("r068", S ``ALL_DISTINCT [x; x] <=> F``)
  val _ = s ("r069", S ``ALL_DISTINCT [x; y] <=> x <> y``)
  val _ = s ("r070", S ``ALL_DISTINCT [x; y] <=> y <> x``)

  val _ = s ("r071", A ``((x :int) = y) <=> (x + -1 * y = 0)``)
  val _ = s ("r072", A ``((x :int) = y + z) <=> (x + -1 * z = y)``)
  val _ = s ("r073", A ``((x :int) = y + -1 * z) <=> (x + (-1 * y + z) = 0)``)
  val _ = s ("r074", A ``((x :int) = -1 * y + z) <=> (y + (-1 * z + x) = 0)``)
  val _ = s ("r075", A ``((x :int) = y + z) <=> (x + (-1 * y + -1 * z) = 0)``)
  val _ = s ("r076", A ``((x :int) = y + z) <=> (y + (z + -1 * x) = 0)``)
  val _ = s ("r077", A ``((x :int) = y + z) <=> (y + (-1 * x + z) = 0)``)
  val _ = s ("r078", A ``((x :int) = y + z) <=> (z + -1 * x = -y)``)
  val _ = s ("r079", A ``((x :int) = -y + z) <=> (z + -1 * x = y)``)
  val _ = s ("r080", A ``(-1 * (x :int) = -y) <=> (x = y)``)
  val _ = s ("r081", A ``(-1 * (x :int) + y = z) <=> (x + -1 * y = -z)``)
  val _ = s ("r082", A ``((x :int) + y = 0) <=> (y = -x)``)
  val _ = s ("r083", A ``((x :int) + y = z) <=> (y + -1 * z = -x)``)
  val _ = s ("r084", A
    ``((a :int) + (-1 * x + (v * y + w * z)) = 0) <=> (x + (-v * y + -w * z) = a)``)

  val _ = s ("r085", A ``0 + (x :int) = x``)
  val _ = s ("r086", A ``(x :int) + 0 = x``)
  val _ = s ("r087", A ``(x :int) + y = y + x``)
  val _ = s ("r088", A ``(x :int) + x = 2 * x``)
  val _ = s ("r089", A ``(x :int) + y + z = x + (y + z)``)
  val _ = s ("r090", A ``(x :int) + y + z = x + (z + y)``)
  val _ = s ("r091", A ``(x :int) + (y + z) = y + (z + x)``)
  val _ = s ("r092", A ``(x :int) + (y + z) = y + (x + z)``)
  val _ = s ("r093", A ``(x :int) + (y + (z + u)) = y + (z + (u + x))``)

  val _ = s ("r094", A ``(x :int) >= x <=> T``)
  val _ = s ("r095", A ``(x :int) >= y <=> x + -1 * y >= 0``)
  val _ = s ("r096", A ``(x :int) >= y <=> y + -1 * x <= 0``)
  val _ = s ("r097", A ``(x :int) >= y + z <=> y + (z + -1 * x) <= 0``)
  val _ = s ("r098", A ``-1 * (x :int) >= 0 <=> x <= 0``)
  val _ = s ("r099", A ``-1 * (x :int) >= -y <=> x <= y``)
  val _ = s ("r100", A ``-1 * (x :int) + y >= 0 <=> x + -1 * y <= 0``)
  val _ = s ("r101", A ``(x :int) + -1 * y >= 0 <=> y <= x``)

  val _ = s ("r102", A ``(x :int) > y <=> ~(y >= x)``)
  val _ = s ("r103", A ``(x :int) > y <=> ~(x <= y)``)
  val _ = s ("r104", A ``(x :int) > y <=> ~(x + -1 * y <= 0)``)
  val _ = s ("r105", A ``(x :int) > y <=> ~(y + -1 * x >= 0)``)
  val _ = s ("r106", A ``(x :int) > y + z <=> ~(z + -1 * x >= -y)``)

  val _ = s ("r107", A ``x <= (x :int) <=> T``)
  val _ = s ("r108", A ``0 <= (1 :int) <=> T``)
  val _ = s ("r109", A ``(x :int) <= y <=> y >= x``)
  val _ = s ("r110", A ``0 <= -(x :int) + y <=> y >= x``)
  val _ = s ("r111", A ``-1 * (x :int) <= 0 <=> x >= 0``)
  val _ = s ("r112", A ``(x :int) <= y <=> x + -1 * y <= 0``)
  val _ = s ("r113", A ``(x :int) <= y <=> y + -1 * x >= 0``)
  val _ = s ("r114", A ``-1 * (x :int) + y <= 0 <=> x + -1 * y >= 0``)
  val _ = s ("r115", A ``-1 * (x :int) + y <= -z <=> x + -1 * y >= z``)
  val _ = s ("r116", A ``-(x :int) + y <= z <=> y + -1 * z <= x``)
  val _ = s ("r117", A ``(x :int) + -1 * y <= z <=> x + (-1 * y + -1 * z) <= 0``)
  val _ = s ("r118", A ``(x :int) <= y + z <=> x + -1 * z <= y``)
  val _ = s ("r119", A ``(x :int) <= y + z <=> z + -1 * x >= -y``)
  val _ = s ("r120", A ``(x :int) <= y + z <=> x + (-1 * y + -1 * z) <= 0``)

  val _ = s ("r121", A ``(x :int) < y <=> ~(y <= x)``)
  val _ = s ("r122", A ``(x :int) < y <=> ~(x >= y)``)
  val _ = s ("r123", A ``(x :int) < y <=> ~(y + -1 * x <= 0)``)
  val _ = s ("r124", A ``(x :int) < y <=> ~(x + -1 * y >= 0)``)
  val _ = s ("r125", A ``(x :int) < y + -1 * z <=> ~(x + -1 * y + z >= 0)``)
  val _ = s ("r126", A ``(x :int) < y + -1 * z <=> ~(x + (-1 * y + z) >= 0)``)
  val _ = s ("r127", A ``(x :int) < -y + z <=> ~(z + -1 * x <= y)``)
  val _ = s ("r128", A ``(x :int) < -y + (z + u) <=> ~(z + (u + -1 * x) <= y)``)
  val _ = s ("r129", A
    ``(x :int) < -y + (z + (u + v)) <=> ~(z + (u + (v + -1 * x)) <= y)``)

  val _ = s ("r130", A ``-(x :int) + y < z <=> ~(y + -1 * z >= x)``)
  val _ = s ("r131", A ``(x :int) + y < z <=> ~(z + -1 * y <= x)``)
  val _ = s ("r132", A ``0 < -(x :int) + y <=> ~(y <= x)``)

  val _ = s ("r133", A ``(x :int) - 0 = x``)
  val _ = s ("r134", A ``0 - (x :int) = -x``)
  val _ = s ("r135", A ``0 - (x :int) = -1 * x``)
  val _ = s ("r136", A ``(x :int) - y = -y + x``)
  val _ = s ("r137", A ``(x :int) - y = x + -1 * y``)
  val _ = s ("r138", A ``(x :int) - y = -1 * y + x``)
  val _ = s ("r139", A ``(x :int) - 1 = -1 + x``)
  val _ = s ("r140", A ``(x :int) + y - z = x + (y + -1 * z)``)
  val _ = s ("r141", A ``(x :int) + y - z = x + (-1 * z + y)``)

  val _ = s ("r142", R ``(0 = -u * (x :real)) <=> (u * x = 0)``)
  val _ = s ("r143", R ``(a = -u * (x :real)) <=> (u * x = -a)``)
  val _ = s ("r144", R ``((a :real) = x + (y + z)) <=> (x + (y + (-1 * a + z)) = 0)``)
  val _ = s ("r145", R ``((a :real) = x + (y + z)) <=> (x + (y + (z + -1 * a)) = 0)``)
  val _ = s ("r146", R ``((a :real) = -u * y + v * z) <=> (u * y + (-v * z + a) = 0)``)
  val _ = s ("r147", R ``((a :real) = -u * y + -v * z) <=> (u * y + (a + v * z) = 0)``)
  val _ = s ("r148", R ``(-(a :real) = -u * x + v * y) <=> (u * x + -v * y = a)``)
  val _ = s ("r149", R
    ``((a :real) = -u * x + (-v * y + w * z)) <=> (u * x + (v * y + (-w * z + a)) = 0)``)
  val _ = s ("r150", R
    ``((a :real) = -u * x + (v * y + w * z)) <=> (u * x + (-v * y + -w * z) = -a)``)
  val _ = s ("r151", R
    ``((a :real) = -u * x + (v * y + -w * z)) <=> (u * x + (-v * y + w * z) = -a)``)
  val _ = s ("r152", R
    ``((a :real) = -u * x + (-v * y + w * z)) <=> (u * x + (v * y + -w * z) = -a)``)
  val _ = s ("r153", R ``((a :real) = -u * x + (-v * y + -w * z)) <=> (u * x + (v * y + w * z) = -a)``)
  val _ = s ("r154", R ``(-(a :real) = -u * x + (v * y + w * z)) <=> (u * x + (-v * y + -w * z) = a)``)
  val _ = s ("r155", R ``(-(a :real) = -u * x + (v * y + -w * z)) <=> (u * x + (-v * y + w * z) = a)``)
  val _ = s ("r156", R ``(-(a :real) = -u * x + (-v * y + w * z)) <=> (u * x + (v * y + -w * z) = a)``)
  val _ = s ("r157", R ``(-(a :real) = -u * x + (-v * y + -w * z)) <=> (u * x + (v * y + w * z) = a)``)
  val _ = s ("r158", R ``((a :real) = -u * x + (-1 * y + w * z)) <=> (u * x + (y + -w * z) = -a)``)
  val _ = s ("r159", R ``((a :real) = -u * x + (-1 * y + -w * z)) <=> (u * x + (y + w * z) = -a)``)
  val _ = s ("r160", R ``(-u * (x :real) + -v * y = -a) <=> (u * x + v * y = a)``)
  val _ = s ("r161", R ``(-1 * (x :real) + (-v * y + -w * z) = -a) <=> (x + (v * y + w * z) = a)``)
  val _ = s ("r162", R ``(-u * (x :real) + (v * y + w * z) = -a) <=> (u * x + (-v * y + -w * z) = a)``)
  val _ = s ("r163", R ``(-u * (x :real) + (-v * y + w * z) = -a) <=> (u * x + (v * y + -w * z) = a)``)
  val _ = s ("r164", R ``(-u * (x :real) + (-v * y + -w * z) = -a) <=> (u * x + (v * y + w * z) = a)``)

  val _ = s ("r165", R ``(x :real) + -1 * y >= 0 <=> y <= x``)
  val _ = s ("r166", R ``(x :real) >= y <=> x + -1 * y >= 0``)

  val _ = s ("r167", R ``(x :real) > y <=> ~(x + -1 * y <= 0)``)

  val _ = s ("r168", R ``(x :real) <= y <=> x + -1 * y <= 0``)
  val _ = s ("r169", R ``(x :real) <= y + z <=> x + -1 * z <= y``)
  val _ = s ("r170", R ``-u * (x :real) <= a <=> u * x >= -a``)
  val _ = s ("r171", R ``-u * (x :real) <= -a <=> u * x >= a``)
  val _ = s ("r172", R ``-u * (x :real) + v * y <= 0 <=> u * x + -v * y >= 0``)
  val _ = s ("r173", R ``-u * (x :real) + v * y <= a <=> u * x + -v * y >= -a``)
  val _ = s ("r174", R ``-u * (x :real) + v * y <= -a <=> u * x + -v * y >= a``)
  val _ = s ("r175", R ``-u * (x :real) + -v * y <= a <=> u * x + v * y >= -a``)
  val _ = s ("r176", R ``-u * (x :real) + -v * y <= -a <=> u * x + v * y >= a``)
  val _ = s ("r177", R
    ``-u * (x :real) + (v * y + w * z) <= 0 <=> u * x + (-v * y + -w * z) >= 0``)
  val _ = s ("r178", R
    ``-u * (x :real) + (v * y + -w * z) <= 0 <=> u * x + (-v * y + w * z) >= 0``)
  val _ = s ("r179", R
    ``-u * (x :real) + (-v * y + w * z) <= 0 <=> u * x + (v * y + -w * z) >= 0``)
  val _ = s ("r180", R
    ``-u * (x :real) + (-v * y + -w * z) <= 0 <=> u * x + (v * y + w * z) >= 0``)
  val _ = s ("r181", R
    ``-u * (x :real) + (v * y + w * z) <= a <=> u * x + (-v * y + -w * z) >= -a``)
  val _ = s ("r182", R
    ``-u * (x :real) + (v * y + w * z) <= -a <=> u * x + (-v * y + -w * z) >= a``)
  val _ = s ("r183", R
    ``-u * (x :real) + (v * y + -w * z) <= a <=> u * x + (-v * y + w * z) >= -a``)
  val _ = s ("r184", R
    ``-u * (x :real) + (v * y + -w * z) <= -a <=> u * x + (-v * y + w * z) >= a``)
  val _ = s ("r185", R
    ``-u * (x :real) + (-v * y + w * z) <= a <=> u * x + (v * y + -w * z) >= -a``)
  val _ = s ("r186", R
    ``-u * (x :real) + (-v * y + w * z) <= -a <=> u * x + (v * y + -w * z) >= a``)
  val _ = s ("r187", R
    ``-u * (x :real) + (-v * y + -w * z) <= a <=> u * x + (v * y + w * z) >= -a``)
  val _ = s ("r188", R
    ``-u * (x :real) + (-v * y + -w * z) <= -a <=> u * x + (v * y + w * z) >= a``)
  val _ = s ("r189", R
    ``(-1 * (x :real) + (v * y + w * z) <= -a) <=> (x + (-v * y + -w * z) >= a)``)

  val _ = s ("r190", R ``(x :real) < y <=> ~(x >= y)``)
  val _ = s ("r191", R ``-u * (x :real) < a <=> ~(u * x <= -a)``)
  val _ = s ("r192", R ``-u * (x :real) < -a <=> ~(u * x <= a)``)
  val _ = s ("r193", R ``-u * (x :real) + v * y < 0 <=> ~(u * x + -v * y <= 0)``)
  val _ = s ("r194", R ``-u * (x :real) + -v * y < 0 <=> ~(u * x + v * y <= 0)``)
  val _ = s ("r195", R ``-u * (x :real) + v * y < a <=> ~(u * x + -v * y <= -a)``)
  val _ = s ("r196", R ``-u * (x :real) + v * y < -a <=> ~(u * x + -v * y <= a)``)
  val _ = s ("r197", R ``-u * (x :real) + -v * y < a <=> ~(u * x + v * y <= -a)``)
  val _ = s ("r198", R ``-u * (x :real) + -v * y < -a <=> ~(u * x + v * y <= a)``)
  val _ = s ("r199", R
    ``-u * (x :real) + (v * y + w * z) < a <=> ~(u * x + (-v * y + -w * z) <= -a)``)
  val _ = s ("r200", R
    ``-u * (x :real) + (v * y + w * z) < -a <=> ~(u * x + (-v * y + -w * z) <= a)``)
  val _ = s ("r201", R
    ``-u * (x :real) + (v * y + -w * z) < a <=> ~(u * x + (-v * y + w * z) <= -a)``)
  val _ = s ("r202", R
    ``-u * (x :real) + (v * y + -w * z) < -a <=> ~(u * x + (-v * y + w * z) <= a)``)
  val _ = s ("r203", R
    ``-u * (x :real) + (-v * y + w * z) < a <=> ~(u * x + (v * y + -w * z) <= -a)``)
  val _ = s ("r204", R
    ``-u * (x :real) + (-v * y + w * z) < -a <=> ~(u * x + (v * y + -w * z) <= a)``)
  val _ = s ("r205", R
    ``-u * (x :real) + (-v * y + -w * z) < a <=> ~(u * x + (v * y + w * z) <= -a)``)
  val _ = s ("r206", R
    ``-u * (x :real) + (-v * y + -w * z) < -a <=> ~(u * x + (v * y + w * z) <= a)``)
  val _ = s ("r207", R
    ``-u * (x :real) + (-v * y + w * z) < 0 <=> ~(u * x + (v * y + -w * z) <= 0)``)
  val _ = s ("r208", R
    ``-u * (x :real) + (-v * y + -w * z) < 0 <=> ~(u * x + (v * y + w * z) <= 0)``)
  val _ = s ("r209", R
    ``-1 * (x :real) + (v * y + w * z) < a <=> ~(x + (-v * y + -w * z) <= -a)``)
  val _ = s ("r210", R
    ``-1 * (x :real) + (v * y + w * z) < -a <=> ~(x + (-v * y + -w * z) <= a)``)
  val _ = s ("r211", R
    ``-1 * (x :real) + (v * y + -w * z) < a <=> ~(x + (-v * y + w * z) <= -a)``)
  val _ = s ("r212", R
    ``-1 * (x :real) + (v * y + -w * z) < -a <=> ~(x + (-v * y + w * z) <= a)``)
  val _ = s ("r213", R
    ``-1 * (x :real) + (-v * y + w * z) < a <=> ~(x + (v * y + -w * z) <= -a)``)
  val _ = s ("r214", R
    ``-1 * (x :real) + (-v * y + w * z) < -a <=> ~(x + (v * y + -w * z) <= a)``)
  val _ = s ("r215", R
    ``-1 * (x :real) + (-v * y + -w * z) < a <=> ~(x + (v * y + w * z) <= -a)``)
  val _ = s ("r216", R
    ``-1 * (x :real) + (-v * y + -w * z) < -a <=> ~(x + (v * y + w * z) <= a)``)
  val _ = s ("r217", R
    ``-u * (x :real) + (-1 * y + -w * z) < -a <=> ~(u * x + (y + w * z) <= a)``)
  val _ = s ("r218", R
    ``-u * (x :real) + (v * y + -1 * z) < -a <=> ~(u * x + (-v * y + z) <= a)``)

  val _ = s ("r219", R ``0 + (x :real) = x``)
  val _ = s ("r220", R ``(x :real) + 0 = x``)
  val _ = s ("r221", R ``(x :real) + y = y + x``)
  val _ = s ("r222", R ``(x :real) + x = 2 * x``)
  val _ = s ("r223", R ``(x :real) + y + z = x + (y + z)``)
  val _ = s ("r224", R ``(x :real) + y + z = x + (z + y)``)
  val _ = s ("r225", R ``(x :real) + (y + z) = y + (z + x)``)
  val _ = s ("r226", R ``(x :real) + (y + z) = y + (x + z)``)

  val _ = s ("r227", R ``0 - (x :real) = -x``)
  val _ = s ("r228", R ``0 - u * (x :real) = -u * x``)
  val _ = s ("r229", R ``(x :real) - 0 = x``)
  val _ = s ("r230", R ``(x :real) - y = x + -1 * y``)
  val _ = s ("r231", R ``(x :real) - y = -1 * y + x``)
  val _ = s ("r232", R ``(x :real) - u * y = x + -u * y``)
  val _ = s ("r233", R ``(x :real) - u * y = -u * y + x``)
  val _ = s ("r234", R ``(x :real) + y - z = x + (y + -1 * z)``)
  val _ = s ("r235", R ``(x :real) + y - z = x + (-1 * z + y)``)
  val _ = s ("r236", R ``(x :real) + y - u * z = -u * z + (x + y)``)
  val _ = s ("r237", R ``(x :real) + y - u * z = x + (-u * z + y)``)
  val _ = s ("r238", R ``(x :real) + y - u * z = x + (y + -u * z)``)

  val _ = s ("r239", R ``0 * (x :real) = 0``)
  val _ = s ("r240", R ``1 * (x :real) = x``)

  val _ = s ("r241", W ``0w + x = x``)
  val _ = s ("r242", W ``(x :'a word) + y = y + x``)
  val _ = s ("r243", W ``1w + (1w + x) = 2w + x``)
  val _ = s ("r244", Drule.EQT_ELIM
    (wordsLib.WORD_ARITH_CONV ``((x :'a word) + z = y + x) <=> (y = z)``))

  val _ = s ("r245", Drule.UNDISCH_ALL (bossLib.PROVE
    [wordsTheory.word_concat_0] ``FINITE univ(:'a) ==> x < dimword(:'b) ==>
      ((0w :'a word) @@ (n2w x :'b word) = (n2w x :'c word))``))
  val _ = s ("r246", Drule.UNDISCH (simpLib.SIMP_PROVE bossLib.std_ss
    [wordsTheory.w2w_n2w, Thm.SYM (Drule.SPEC_ALL wordsTheory.MOD_DIMINDEX)]
    ``x < dimword(:'a) ==> (w2w (n2w x :'a word) = (n2w x :'b word))``))
  val _ = s ("r247", Drule.UNDISCH_ALL (bossLib.PROVE
    [wordsTheory.word_concat_0_eq] ``FINITE univ(:'a) ==>
      dimindex(:'b) <= dimindex(:'c) ==> y < dimword(:'b) ==>
      (((0w :'a word) @@ (x :'b word) = (n2w y :'c word)) <=> (x = n2w y))``))
  val _ = s ("r248", Drule.UNDISCH_ALL (bossLib.PROVE
      [wordsTheory.word_concat_0_eq] ``FINITE univ(:'a) ==>
      dimindex(:'b) <= dimindex(:'c) ==> y < dimword(:'b) ==>
      (((0w :'a word) @@ (x :'b word) = (n2w y :'c word)) <=> (n2w y = x))``))
  val _ = s ("r249", Drule.UNDISCH_ALL (bossLib.PROVE
    [wordsTheory.word_concat_0_eq] ``FINITE univ(:'a) ==>
      dimindex(:'b) <= dimindex(:'c) ==> y < dimword(:'b) ==>
      (((n2w y :'c word) = (0w :'a word) @@ (x :'b word)) <=> (x = n2w y))``))
  val _ = s ("r250", Drule.UNDISCH_ALL (bossLib.PROVE
    [wordsTheory.word_concat_0_eq] ``FINITE univ(:'a) ==>
      dimindex(:'b) <= dimindex(:'c) ==> y < dimword(:'b) ==>
      (((n2w y :'c word) = (0w :'a word) @@ (x :'b word)) <=> (n2w y = x))``))

  val _ = s ("r251", W ``x && y = y && x``)
  val _ = s ("r252", W ``x && y && z = y && x && z``)
  val _ = s ("r253", W ``x && y && z = (x && y) && z``)
  val _ = s ("r254", W ``(1w = (x :word1) && y) <=> (1w = x) /\ (1w = y)``)
  val _ = s ("r255", W ``(1w = (x :word1) && y) <=> (1w = y) /\ (1w = x)``)
  val _ = s ("r256", W ``(7 >< 0) (x :word8) = x``)
  val _ = s ("r257", W ``x <+ y <=> ~(y <=+ x)``)
  val _ = s ("r258", W ``(x :'a word) * y = y * x``)
  val _ = s ("r259", W ``(0 >< 0) (x :word1) = x``)
  val _ = s ("r260", W ``(x && y) && z = x && y && z``)
  val _ = s ("r261", W ``0w || x = x``)

  (* used for Z3's proof rule th_lemma *)

  val _ = s ("t001", U [boolTheory.EQ_SYM_EQ, combinTheory.UPDATE_def]
    ``(x = y) \/ (f x = (y =+ z) f x)``)
  val _ = s ("t002", U [boolTheory.EQ_SYM_EQ, combinTheory.UPDATE_def]
    ``(x = y) \/ (f y = (x =+ z) f y)``)
  val _ = s ("t003", U [boolTheory.EQ_SYM_EQ, combinTheory.UPDATE_def]
    ``(x = y) \/ ((y =+ z) f x = f x)``)
  val _ = s ("t004", U [boolTheory.EQ_SYM_EQ, combinTheory.UPDATE_def]
    ``(x = y) \/ ((x =+ z) f y = f y)``)
  val _ = s ("t005", Tactical.prove
    (``(f = g) \/ (f (array_ext f g) <> g (array_ext f g))``,
      Tactic.DISJ_CASES_TAC
        (Thm.SPEC ``?x. f x <> g x`` boolTheory.EXCLUDED_MIDDLE)
      >> Rewrite.REWRITE_TAC [array_ext_def]
      >> bossLib.METIS_TAC []))

  val _ = s ("t006", A ``((x :int) <> y) \/ (x <= y)``)
  val _ = s ("t007", A ``((x :int) <> y) \/ (x >= y)``)
  val _ = s ("t008", A ``((x :int) <> y) \/ (x + -1 * y >= 0)``)
  val _ = s ("t009", A ``((x :int) <> y) \/ (x + -1 * y <= 0)``)
  val _ = s ("t010", A ``((x :int) = y) \/ ~(x <= y) \/ ~(x >= y)``)
  val _ = s ("t011", A ``~((x :int) <= 0) \/ x <= 1``)
  val _ = s ("t012", A ``~((x :int) <= -1) \/ x <= 0``)
  val _ = s ("t013", A ``~((x :int) >= 0) \/ x >= -1``)
  val _ = s ("t014", A ``~((x :int) >= 0) \/ ~(x <= -1)``)
  val _ = s ("t015", A ``(x :int) >= y \/ x <= y``)

  val _ = s ("t016", R ``(x :real) <> y \/ x + -1 * y >= 0``)

  val _ = s ("t017", Tactical.prove (``(x :'a word) <> ~x``,
    let
      val RW = bossLib.RW_TAC (bossLib.++ (bossLib.bool_ss, fcpLib.FCP_ss))
    in
      RW []
      >> Tactic.EXISTS_TAC ``0 :num``
      >> RW [wordsTheory.DIMINDEX_GT_0, wordsTheory.word_1comp_def]
      >> tautLib.TAUT_TAC
    end))
  val _ = s ("t018", W ``(x = y) ==> x ' i ==> y ' i``)
  val _ = s ("t019", S ``(1w = ~(x :word1)) \/ x ' 0``)
  val _ = s ("t020", S ``(x :word1) ' 0 ==> (0w = ~x)``)
  val _ = s ("t021", S ``(x :word1) ' 0 ==> (1w = x)``)
  val _ = s ("t022", S ``~((x :word1) ' 0) ==> (0w = x)``)
  val _ = s ("t023", S ``~((x :word1) ' 0) ==> (1w = ~x)``)
  val _ = s ("t024", S ``(0w = ~(x :word1)) \/ ~(x ' 0)``)
  val _ = s ("t025", U []
    ``(1w = ~(x :word1) || ~y) \/ ~(~(x ' 0) \/ ~(y ' 0))``)
  val _ = s ("t026", U []
    ``(0w = (x :word8)) \/ x ' 0 \/ x ' 1 \/ x ' 2 \/ x ' 3 \/ x ' 4 \/ x ' 5 \/ x ' 6 \/ x ' 7``)
  val _ = s ("t027", S
    ``(((x :word1) = 1w) <=> p) <=> (x = if p then 1w else 0w)``)
  val _ = s ("t028", S
    ``((1w = (x :word1)) <=> p) <=> (x = if p then 1w else 0w)``)
  val _ = s ("t029", S
    ``(p <=> ((x :word1) = 1w)) <=> (x = if p then 1w else 0w)``)
  val _ = s ("t030", S
    ``(p <=> (1w = (x :word1))) <=> (x = if p then 1w else 0w)``)
  val _ = s ("t031", B
    ``(0w:word32 = 0xFFFFFFFFw * sw2sw (x :word8)) ==> ~(x ' 0)``)
  val _ = s ("t032", B
    ``(0w:word32 = 0xFFFFFFFFw * sw2sw (x :word8)) ==> ~(x ' 1 <=> ~(x ' 0))``)
  val _ = s ("t033", B ``(0w:word32 = 0xFFFFFFFFw * sw2sw (x :word8)) ==>
      ~(x ' 2 <=> ~(x ' 0) /\ ~(x ' 1))``)
  val _ = s ("t034", M [
      simpLib.SIMP_PROVE bossLib.bool_ss [
        wordsTheory.WORD_ADD_BIT0, wordsLib.WORD_DECIDE ``1w :'a word ' 0``
      ] ``x ' 0 ==> ~(1w + (x :'a word)) ' 0``
    ] ``(1w + (x :'a word) = y) ==> x ' 0 ==> ~(y ' 0)``)
  val _ = s ("t035", S ``(1w = x :word1) \/ (0 >< 0) x <> (1w :word1)``)

  (* used to prove hypotheses of other proforma theorems (recursively) *)

  val _ = s ("p001", wordsTheory.ZERO_LT_dimword)  (* ``0 < dimword(:'a)`` *)
  val _ = s ("p002", wordsTheory.ONE_LT_dimword)  (* ``1 < dimword(:'a)`` *)
  val _ = s ("p003", S ``255 < dimword (:8)``)
  val _ = s ("p004", S ``FINITE univ(:unit)``)
  val _ = s ("p005", S ``FINITE univ(:16)``)
  val _ = s ("p006", S ``FINITE univ(:24)``)
  val _ = s ("p007", S ``FINITE univ(:30)``)
  val _ = s ("p008", S ``FINITE univ(:31)``)
  val _ = s ("p009", S ``dimindex (:8) <= dimindex (:32)``)
