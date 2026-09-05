Theory HolSmtArraySwap
Ancestors
  integer combin
Libs
  HolSmtLib

(* Swapping two array entries is an involution: performing the same swap
   twice restores the original array.  Each update reads from the array
   before that swap, just as the textbook temporary-variable algorithm does. *)
Definition array_swap_def:
  array_swap (a : int -> int) i j =
    (j =+ a i) ((i =+ a j) a)
End

Theorem array_swap_involution:
  !a i j. array_swap (array_swap a i j) i j = a
Proof
  PURE_REWRITE_TAC [array_swap_def] >> Z3_TAC
QED
