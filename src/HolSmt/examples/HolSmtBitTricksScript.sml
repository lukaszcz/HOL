Theory HolSmtBitTricks
Ancestors
  words
Libs
  HolSmtLib

(* Classic bit-level programming tricks (in the style of Warren's
   "Hacker's Delight"), verified over word32 via SMT bit vectors. *)

(* Swapping two variables without a temporary: after a := x ?? y,
   b := y ?? a, a := a ?? b, the values are exchanged.  The two
   conjuncts state the final contents of b and a. *)
Theorem xor_swap:
  !x y : word32. (x ?? y) ?? (y ?? (x ?? y)) = y /\ y ?? (x ?? y) = x
Proof
  Z3_TAC
QED

(* The masking test for 8-byte alignment agrees with the
   shift-out/shift-in round trip. *)
Theorem align_roundtrip:
  !x : word32. (x && 7w = 0w) <=> ((x >>> 3) << 3 = x)
Proof
  Z3_TAC
QED
