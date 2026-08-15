open HolKernel Parse boolLib bossLib

open ringTheory

val _ = new_theory "parityAlgebraTranslation"

(* Isabelle/HOL f7e02b7e1f311d9c41ee075d22ff788b3e0de6db,
   src/HOL/Examples/Groebner_Examples.thy:61-95.  Isabelle's [idom]
   class becomes an explicit HOL4 ring record together with carrier
   hypotheses for every source variable. *)
Definition source_ring_sq_def:
  source_ring_sq (r : 'a ring) x = r.prod.op x x
End

Definition source_ring_sum8_def:
  source_ring_sum8 (r : 'a ring) a b c d e f g h =
    r.sum.op a
      (r.sum.op b
        (r.sum.op c
          (r.sum.op d
            (r.sum.op e (r.sum.op f (r.sum.op g h))))))
End

Definition source_ring_neg_def:
  source_ring_neg (r : 'a ring) x = r.sum.inv x
End

Theorem source_ring_factor_square_left:
  !r : 'a ring. !x y.
    IntegralDomain r /\ x IN r.carrier /\ y IN r.carrier /\
    r.prod.op (r.prod.exp x 2) y = r.prod.exp x 2 ==>
    r.prod.op (r.prod.exp x 2) (ring_sub r y r.prod.id) = r.sum.id
Proof
  rpt strip_tac
  >> ringLib.EXPLICIT_RING_TAC
QED

Theorem source_ring_factor_square_right:
  !r : 'a ring. !x y.
    IntegralDomain r /\ x IN r.carrier /\ y IN r.carrier /\
    r.prod.op x (r.prod.exp y 2) = r.prod.exp y 2 ==>
    r.prod.op (r.prod.exp y 2) (ring_sub r x r.prod.id) = r.sum.id
Proof
  rpt strip_tac
  >> ringLib.EXPLICIT_RING_TAC
QED

Theorem source_idom_square_cases:
  !r : 'a ring. !x y.
    IntegralDomain r /\ x IN r.carrier /\ y IN r.carrier /\
    r.prod.op (r.prod.exp x 2) y = r.prod.exp x 2 /\
    r.prod.op x (r.prod.exp y 2) = r.prod.exp y 2 ==>
    (x = r.sum.id \/ y = r.prod.id) /\
    (y = r.sum.id \/ x = r.prod.id)
Proof
  rpt strip_tac
  >> `Ring r` by metis_tac[integral_domain_is_ring]
  >> `r.prod.exp x 2 IN r.carrier /\
      r.prod.exp y 2 IN r.carrier`
       by metis_tac[ring_exp_element]
  >> `ring_sub r y r.prod.id IN r.carrier /\
      ring_sub r x r.prod.id IN r.carrier`
       by metis_tac[ring_sub_element, ring_one_element]
  >> `r.prod.op (r.prod.exp x 2)
        (ring_sub r y r.prod.id) = r.sum.id`
       by metis_tac[source_ring_factor_square_left]
  >> `r.prod.op (r.prod.exp y 2)
        (ring_sub r x r.prod.id) = r.sum.id`
       by metis_tac[source_ring_factor_square_right]
  >> `r.prod.exp x 2 = r.sum.id \/
      ring_sub r y r.prod.id = r.sum.id`
       by metis_tac[integral_domain_mult_eq_zero]
  >> `r.prod.exp y 2 = r.sum.id \/
      ring_sub r x r.prod.id = r.sum.id`
       by metis_tac[integral_domain_mult_eq_zero]
  >> `r.prod.exp x 2 = r.sum.id <=> x = r.sum.id`
       by simp[integral_domain_exp_eq_zero]
  >> `r.prod.exp y 2 = r.sum.id <=> y = r.sum.id`
       by simp[integral_domain_exp_eq_zero]
  >> `ring_sub r x r.prod.id = r.sum.id <=> x = r.prod.id`
       by simp[ring_sub_eq_zero, ring_one_element]
  >> `ring_sub r y r.prod.id = r.sum.id <=> y = r.prod.id`
       by simp[ring_sub_eq_zero, ring_one_element]
  >> metis_tac[]
QED

Theorem source_idom_squares_x_nonzero_x:
  !r : 'a ring. !x y.
    IntegralDomain r /\ x IN r.carrier /\ y IN r.carrier /\
    r.prod.op (r.prod.exp x 2) y = r.prod.exp x 2 /\
    r.prod.op x (r.prod.exp y 2) = r.prod.exp y 2 /\
    x <> r.sum.id ==>
    x = r.prod.id
Proof
  metis_tac[source_idom_square_cases,
            integral_domain_one_ne_zero]
QED

Theorem source_idom_squares_x_nonzero_y:
  !r : 'a ring. !x y.
    IntegralDomain r /\ x IN r.carrier /\ y IN r.carrier /\
    r.prod.op (r.prod.exp x 2) y = r.prod.exp x 2 /\
    r.prod.op x (r.prod.exp y 2) = r.prod.exp y 2 /\
    x <> r.sum.id ==>
    y = r.prod.id
Proof
  metis_tac[source_idom_square_cases,
            integral_domain_one_ne_zero]
QED

Theorem source_idom_squares_y_nonzero_x:
  !r : 'a ring. !x y.
    IntegralDomain r /\ x IN r.carrier /\ y IN r.carrier /\
    r.prod.op (r.prod.exp x 2) y = r.prod.exp x 2 /\
    r.prod.op x (r.prod.exp y 2) = r.prod.exp y 2 /\
    y <> r.sum.id ==>
    x = r.prod.id
Proof
  metis_tac[source_idom_square_cases,
            integral_domain_one_ne_zero]
QED

Theorem source_idom_squares_y_nonzero_y:
  !r : 'a ring. !x y.
    IntegralDomain r /\ x IN r.carrier /\ y IN r.carrier /\
    r.prod.op (r.prod.exp x 2) y = r.prod.exp x 2 /\
    r.prod.op x (r.prod.exp y 2) = r.prod.exp y 2 /\
    y <> r.sum.id ==>
    y = r.prod.id
Proof
  metis_tac[source_idom_square_cases,
            integral_domain_one_ne_zero]
QED

Theorem source_idom_simultaneous_squares:
  !r : 'a ring. !x y.
    IntegralDomain r /\ x IN r.carrier /\ y IN r.carrier ==>
    ((r.prod.op (r.prod.exp x 2) y = r.prod.exp x 2 /\
      r.prod.op x (r.prod.exp y 2) = r.prod.exp y 2) <=>
     (x = r.prod.id /\ y = r.prod.id) \/
     (x = r.sum.id /\ y = r.sum.id))
Proof
  rpt strip_tac
  >> `Ring r` by metis_tac[integral_domain_is_ring]
  >> `r.prod.exp x 2 IN r.carrier /\
      r.prod.exp y 2 IN r.carrier`
       by metis_tac[ring_exp_element]
  >> `ring_sub r y r.prod.id IN r.carrier /\
      ring_sub r x r.prod.id IN r.carrier`
       by metis_tac[ring_sub_element, ring_one_element]
  >> eq_tac
  >- (strip_tac
      >> `r.prod.op (r.prod.exp x 2)
            (ring_sub r y r.prod.id) = r.sum.id`
           by metis_tac[source_ring_factor_square_left]
      >> `r.prod.op (r.prod.exp y 2)
            (ring_sub r x r.prod.id) = r.sum.id`
           by metis_tac[source_ring_factor_square_right]
      >> `r.prod.exp x 2 = r.sum.id \/
          ring_sub r y r.prod.id = r.sum.id`
           by metis_tac[integral_domain_mult_eq_zero]
      >> `r.prod.exp y 2 = r.sum.id \/
          ring_sub r x r.prod.id = r.sum.id`
           by metis_tac[integral_domain_mult_eq_zero]
      >> `r.prod.exp x 2 = r.sum.id <=> x = r.sum.id`
           by simp[integral_domain_exp_eq_zero]
      >> `r.prod.exp y 2 = r.sum.id <=> y = r.sum.id`
           by simp[integral_domain_exp_eq_zero]
      >> `ring_sub r x r.prod.id = r.sum.id <=> x = r.prod.id`
           by simp[ring_sub_eq_zero, ring_one_element]
      >> `ring_sub r y r.prod.id = r.sum.id <=> y = r.prod.id`
           by simp[ring_sub_eq_zero, ring_one_element]
      >> metis_tac[integral_domain_one_ne_zero])
  >> strip_tac
  >> fs[]
  >> simp[ring_one_exp, ring_zero_exp]
QED

Theorem source_idom_four_square:
  !r : 'a ring.
  !x1 x2 x3 x4 y1 y2 y3 y4.
    IntegralDomain r /\
    x1 IN r.carrier /\ x2 IN r.carrier /\
    x3 IN r.carrier /\ x4 IN r.carrier /\
    y1 IN r.carrier /\ y2 IN r.carrier /\
    y3 IN r.carrier /\ y4 IN r.carrier ==>
    r.prod.op
      (r.sum.op (source_ring_sq r x1)
        (r.sum.op (source_ring_sq r x2)
          (r.sum.op (source_ring_sq r x3) (source_ring_sq r x4))))
      (r.sum.op (source_ring_sq r y1)
        (r.sum.op (source_ring_sq r y2)
          (r.sum.op (source_ring_sq r y3) (source_ring_sq r y4)))) =
    r.sum.op
      (source_ring_sq r
        (ring_sub r
          (ring_sub r
            (ring_sub r (r.prod.op x1 y1) (r.prod.op x2 y2))
            (r.prod.op x3 y3))
          (r.prod.op x4 y4)))
      (r.sum.op
        (source_ring_sq r
          (ring_sub r
            (r.sum.op (r.sum.op (r.prod.op x1 y2) (r.prod.op x2 y1))
              (r.prod.op x3 y4))
            (r.prod.op x4 y3)))
        (r.sum.op
          (source_ring_sq r
            (r.sum.op
              (ring_sub r (r.prod.op x1 y3) (r.prod.op x2 y4))
              (r.sum.op (r.prod.op x3 y1) (r.prod.op x4 y2))))
          (source_ring_sq r
            (r.sum.op
              (ring_sub r
                (r.sum.op (r.prod.op x1 y4) (r.prod.op x2 y3))
                (r.prod.op x3 y2))
              (r.prod.op x4 y1)))))
Proof
  rpt strip_tac
  >> simp[source_ring_sq_def]
  >> ringLib.EXPLICIT_RING_TAC
QED

Theorem source_idom_eight_square:
  !r : 'a ring.
  !p1 q1 r1 s1 t1 u1 v1 w1 p2 q2 r2 s2 t2 u2 v2 w2.
    IntegralDomain r /\
    p1 IN r.carrier /\ q1 IN r.carrier /\
    r1 IN r.carrier /\ s1 IN r.carrier /\
    t1 IN r.carrier /\ u1 IN r.carrier /\
    v1 IN r.carrier /\ w1 IN r.carrier /\
    p2 IN r.carrier /\ q2 IN r.carrier /\
    r2 IN r.carrier /\ s2 IN r.carrier /\
    t2 IN r.carrier /\ u2 IN r.carrier /\
    v2 IN r.carrier /\ w2 IN r.carrier ==>
    r.prod.op
      (source_ring_sum8 r
        (source_ring_sq r p1) (source_ring_sq r q1)
        (source_ring_sq r r1) (source_ring_sq r s1)
        (source_ring_sq r t1) (source_ring_sq r u1)
        (source_ring_sq r v1) (source_ring_sq r w1))
      (source_ring_sum8 r
        (source_ring_sq r p2) (source_ring_sq r q2)
        (source_ring_sq r r2) (source_ring_sq r s2)
        (source_ring_sq r t2) (source_ring_sq r u2)
        (source_ring_sq r v2) (source_ring_sq r w2)) =
    source_ring_sum8 r
      (source_ring_sq r
        (source_ring_sum8 r
          (r.prod.op p1 p2)
          (source_ring_neg r (r.prod.op q1 q2))
          (source_ring_neg r (r.prod.op r1 r2))
          (source_ring_neg r (r.prod.op s1 s2))
          (source_ring_neg r (r.prod.op t1 t2))
          (source_ring_neg r (r.prod.op u1 u2))
          (source_ring_neg r (r.prod.op v1 v2))
          (source_ring_neg r (r.prod.op w1 w2))))
      (source_ring_sq r
        (source_ring_sum8 r
          (r.prod.op p1 q2) (r.prod.op q1 p2)
          (r.prod.op r1 s2)
          (source_ring_neg r (r.prod.op s1 r2))
          (r.prod.op t1 u2)
          (source_ring_neg r (r.prod.op u1 t2))
          (source_ring_neg r (r.prod.op v1 w2))
          (r.prod.op w1 v2)))
      (source_ring_sq r
        (source_ring_sum8 r
          (r.prod.op p1 r2)
          (source_ring_neg r (r.prod.op q1 s2))
          (r.prod.op r1 p2) (r.prod.op s1 q2)
          (r.prod.op t1 v2) (r.prod.op u1 w2)
          (source_ring_neg r (r.prod.op v1 t2))
          (source_ring_neg r (r.prod.op w1 u2))))
      (source_ring_sq r
        (source_ring_sum8 r
          (r.prod.op p1 s2) (r.prod.op q1 r2)
          (source_ring_neg r (r.prod.op r1 q2))
          (r.prod.op s1 p2) (r.prod.op t1 w2)
          (source_ring_neg r (r.prod.op u1 v2))
          (r.prod.op v1 u2)
          (source_ring_neg r (r.prod.op w1 t2))))
      (source_ring_sq r
        (source_ring_sum8 r
          (r.prod.op p1 t2)
          (source_ring_neg r (r.prod.op q1 u2))
          (source_ring_neg r (r.prod.op r1 v2))
          (source_ring_neg r (r.prod.op s1 w2))
          (r.prod.op t1 p2) (r.prod.op u1 q2)
          (r.prod.op v1 r2) (r.prod.op w1 s2)))
      (source_ring_sq r
        (source_ring_sum8 r
          (r.prod.op p1 u2) (r.prod.op q1 t2)
          (source_ring_neg r (r.prod.op r1 w2))
          (r.prod.op s1 v2)
          (source_ring_neg r (r.prod.op t1 q2))
          (r.prod.op u1 p2)
          (source_ring_neg r (r.prod.op v1 s2))
          (r.prod.op w1 r2)))
      (source_ring_sq r
        (source_ring_sum8 r
          (r.prod.op p1 v2) (r.prod.op q1 w2)
          (r.prod.op r1 t2)
          (source_ring_neg r (r.prod.op s1 u2))
          (source_ring_neg r (r.prod.op t1 r2))
          (r.prod.op u1 s2) (r.prod.op v1 p2)
          (source_ring_neg r (r.prod.op w1 q2))))
      (source_ring_sq r
        (source_ring_sum8 r
          (r.prod.op p1 w2)
          (source_ring_neg r (r.prod.op q1 v2))
          (r.prod.op r1 u2) (r.prod.op s1 t2)
          (source_ring_neg r (r.prod.op t1 s2))
          (source_ring_neg r (r.prod.op u1 r2))
          (r.prod.op v1 q2) (r.prod.op w1 p2)))
Proof
  rpt strip_tac
  >> simp[source_ring_sq_def, source_ring_sum8_def,
          source_ring_neg_def]
  >> ringLib.EXPLICIT_RING_TAC
QED

Theorem source_Z_integral_domain:
  IntegralDomain Z
Proof
  rw[IntegralDomain_def, Z_ring, Z_def, Z_add_def, Z_mult_def,
     integerTheory.INT_ENTIRE]
QED

val integer_instance_rewrites =
  [source_Z_integral_domain, source_ring_sq_def,
   source_ring_sum8_def, source_ring_neg_def,
   Z_def, Z_add_def, Z_mult_def]

fun instantiate_Z theorem =
  SPEC ``Z : int ring``
    (INST_TYPE [Type.alpha |-> intSyntax.int_ty] theorem)

val source_idom_simultaneous_squares_int =
  save_thm
    ("source_idom_simultaneous_squares_int",
     SIMP_RULE (srw_ss ()) integer_instance_rewrites
       (instantiate_Z source_idom_simultaneous_squares))

val source_idom_four_square_int =
  save_thm
    ("source_idom_four_square_int",
     SIMP_RULE (srw_ss ()) integer_instance_rewrites
       (instantiate_Z source_idom_four_square))

val source_idom_eight_square_int =
  save_thm
    ("source_idom_eight_square_int",
     SIMP_RULE (srw_ss ()) integer_instance_rewrites
       (instantiate_Z source_idom_eight_square))

val _ = export_theory ()
