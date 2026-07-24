(* Copyright (c) 2026 The HOL4 contributors. *)

(* Definitional semantics for Z3's internal string-proof vocabulary. *)
Theory smtstringz3
Ancestors[qualified]
  smtstring bit

(* Z3's internal Char sort is represented by num.  Proof parsing maps
   (_ Char n) directly to the numeral n; well-formed character terms
   carry the side condition n <= 196607. *)

Definition seq_unit_def:
  seq_unit (c : num) = [c]
End

(* Z3 numbers the tail after position i, so tail s 0 drops the head. *)
Definition seq_tail_def:
  seq_tail (s : num list) i = DROP (SUC i) s
End

Definition seq_eq_def:
  seq_eq (s : num list) t <=> s = t
End

(* nth_i is deliberately specified only in range.  Z3 leaves its value
   outside the sequence unspecified, so no out-of-range equation may be
   added here. *)
Theorem seq_nth_i_exists[local]:
  ?f : num list -> num -> num.
    !s i. i < LENGTH s ==> f s i = EL i s
Proof
  qexists `\s i. if i < LENGTH s then EL i s else 0` >>
  simp []
QED

val seq_nth_i_def =
  new_specification
    ("seq_nth_i_def", ["seq_nth_i"], seq_nth_i_exists);

Definition char_is_digit_def:
  char_is_digit (c : num) <=> 48 <= c /\ c <= 57
End

Definition seq_digit2int_def:
  seq_digit2int (c : num) : int = &c - 48
End

(* Defensive alias for older plans.  The recorded Z3 spelling in every
   supported version is seq.digit2int. *)
Definition seq_digit_def:
  seq_digit (c : num) : int = seq_digit2int c
End

(* seq.stoi s i is Z3's value for the prefix ending at position i. *)
Definition seq_stoi_def:
  seq_stoi (s : num list) i =
    smtstr_to_int (TAKE (SUC i) s)
End

Definition char_bit_def:
  char_bit k (c : num) <=> BIT k c
End

(* TASK_03's clause catalog refuted the original construction-order
   interpretation of k.  The regex argument is already the residual
   language and k is a cursor into s.  Keep aut_state as an explicit
   boundary for the replay layer, but do not invent derivative states. *)
Definition aut_state_def:
  aut_state k (r : reglan) = r
End

Definition aut_accept_def:
  aut_accept (s : num list) k r <=>
    smt_in_re (DROP k s) (aut_state k r)
End

(* seq.prefix.c/d/x/y/z are proof-local witnesses, not theory constants.
   TASK_17 must introduce them through the existing z3name!k
   definition-recording machinery. *)

val _ = computeLib.add_funs
  [seq_unit_def, seq_tail_def, seq_eq_def, seq_nth_i_def,
   char_is_digit_def, seq_digit2int_def, seq_digit_def,
   seq_stoi_def, char_bit_def, aut_state_def, aut_accept_def];

(* Evaluation equations consumed by the character and regex replay rungs. *)

Theorem seq_unit_compute[compute]:
  seq_unit c = [c]
Proof
  simp [seq_unit_def]
QED

Theorem seq_tail_compute[compute]:
  seq_tail s i = DROP (SUC i) s
Proof
  simp [seq_tail_def]
QED

Theorem seq_eq_compute[compute]:
  seq_eq s t <=> s = t
Proof
  simp [seq_eq_def]
QED

Theorem seq_nth_i_compute[compute]:
  (seq_nth_i (h::s) 0 = h) /\
  (i < LENGTH s ==>
   seq_nth_i (h::s) (SUC i) = seq_nth_i s i)
Proof
  simp [seq_nth_i_def]
QED

Theorem char_is_digit_compute[compute]:
  char_is_digit c <=> 48 <= c /\ c <= 57
Proof
  simp [char_is_digit_def]
QED

Theorem seq_digit2int_compute[compute]:
  seq_digit2int c = &c - 48
Proof
  simp [seq_digit2int_def]
QED

Theorem seq_digit_compute[compute]:
  seq_digit c = seq_digit2int c
Proof
  simp [seq_digit_def]
QED

Theorem seq_stoi_compute[compute]:
  seq_stoi s i = smtstr_to_int (TAKE (SUC i) s)
Proof
  simp [seq_stoi_def]
QED

Theorem char_bit_compute[compute]:
  char_bit k c <=> BIT k c
Proof
  simp [char_bit_def]
QED

Theorem aut_state_compute[compute]:
  aut_state k r = r
Proof
  simp [aut_state_def]
QED

Theorem aut_accept_compute[compute]:
  aut_accept s k r <=> smt_in_re (DROP k s) r
Proof
  simp [aut_accept_def, aut_state_def]
QED

Theorem aut_accept_zero:
  aut_accept s 0 r <=> smt_in_re s r
Proof
  simp [aut_accept_compute]
QED

Theorem aut_accept_suc:
  aut_accept (c::s) (SUC k) r <=> aut_accept s k r
Proof
  simp [aut_accept_compute]
QED

(* Ground checks of TASK_03's M/B/T/N clause shapes. *)
Theorem aut_accept_catalog_eval:
  (~smt_in_re [98] (reglan_range [97] [122]) \/
   aut_accept [98] 0 (reglan_range [97] [122])) /\
  (aut_accept [98] 0 (reglan_range [97] [122]) ==>
   1 <= LENGTH [98]) /\
  (~aut_accept [98] 0 (reglan_range [97] [122]) \/
   LENGTH [98] <= 0 \/
   (97 <= seq_nth_i [98] 0 /\ seq_nth_i [98] 0 <= 122 /\
    aut_accept [98] 1 (reglan_to_re []))) /\
  (~aut_accept [98] 1 (reglan_to_re []) \/
   LENGTH [98] <= 1) /\
  (~aut_accept [97; 97] 0
       (reglan_loop (reglan_to_re [97]) 1 3) \/
   LENGTH [97; 97] <= 0 \/
   (seq_nth_i [97; 97] 0 = 97 /\
    aut_accept [97; 97] 1
      (reglan_loop (reglan_to_re [97]) 0 2))) /\
  (~aut_accept [97; 97] 2 (reglan_to_re []) \/
   LENGTH [97; 97] <= 2) /\
  (~aut_accept [97; 98] 0
       (reglan_comp (reglan_to_re [97])) \/
   LENGTH [97; 98] <= 0 \/
   (seq_nth_i [97; 98] 0 <> 97 \/
    aut_accept [97; 98] 1 (reglan_plus reglan_allchar)))
Proof
  simp [seq_nth_i_def] >>
  EVAL_TAC
QED

Theorem z3_internal_eval:
  seq_unit 97 = [97] /\
  seq_tail [10; 20; 30] 0 = [20; 30] /\
  seq_tail [10; 20; 30] 1 = [30] /\
  seq_eq [1; 2] [1; 2] /\
  seq_nth_i [10; 20; 30] 1 = 20 /\
  char_is_digit 48 /\ char_is_digit 57 /\
  ~char_is_digit 47 /\ ~char_is_digit 58 /\
  seq_digit2int 48 = 0 /\ seq_digit2int 57 = 9 /\
  seq_digit 53 = 5 /\
  seq_stoi [52; 50] 0 = 4 /\
  seq_stoi [52; 50] 1 = 42 /\
  char_bit 0 3 /\ char_bit 1 3 /\ ~char_bit 2 3
Proof
  simp [seq_nth_i_def] >>
  EVAL_TAC
QED
