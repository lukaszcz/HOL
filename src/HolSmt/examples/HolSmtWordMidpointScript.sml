Theory HolSmtWordMidpoint
Ancestors
  words
Libs
  HolSmtLib

(* Hacker's Delight midpoint and average identities, together with the
   carry decomposition of word addition. *)

Theorem midpoint_bounds32:
  !lo hi : word32.
    lo <=+ hi ==>
    lo <=+ lo + ((hi - lo) >>> 1) /\
    lo + ((hi - lo) >>> 1) <=+ hi
Proof
  Z3_TAC
QED

Theorem midpoint_agreement32:
  !lo hi : word32.
    lo <=+ hi ==>
    lo + ((hi - lo) >>> 1) = (lo && hi) + ((lo ?? hi) >>> 1)
Proof
  Z3_TAC
QED

Theorem average_without_overflow32:
  !x y : word32.
    x <=+ x + y ==>
    (x && y) + ((x ?? y) >>> 1) = (x + y) >>> 1
Proof
  Z3_TAC
QED

Theorem sum_decomposition8:
  !x y : word8. x + y = (x ?? y) + 2w * (x && y)
Proof
  Z3_TAC
QED
