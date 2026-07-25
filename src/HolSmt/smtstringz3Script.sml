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

(* TASK_03's five-version catalog refutes a construction-order state
   number: k is the cursor in the original string, while the regex argument
   already denotes the residual language. *)
Definition aut_state_def:
  aut_state (s : num list) k = DROP k s
End

Definition aut_accept_def:
  aut_accept (s : num list) k r <=>
    smt_in_re (aut_state s k) r
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
  aut_state s k = DROP k s
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

Theorem aut_accept_nonnullable_length:
  aut_accept s k r /\ ~re_nullable r ==> SUC k <= LENGTH s
Proof
  rw [aut_accept_compute, smtstringTheory.re_nullable_correct] >>
  Cases_on `k < LENGTH s`
  >- decide_tac
  >> `LENGTH s <= k` by decide_tac >>
  fs [listTheory.DROP_LENGTH_TOO_LONG]
QED

Theorem aut_accept_nonnullable_length_int:
  aut_accept s k r /\ ~re_nullable r ==>
  (&(SUC k) : int) <= &(smtstr_len s)
Proof
  strip_tac >>
  drule aut_accept_nonnullable_length >>
  simp [smtstringTheory.smtstr_len_def]
QED

Theorem aut_accept_range_length_int:
  aut_accept s k (reglan_range lo hi) ==>
  (&(SUC k) : int) <= &(smtstr_len s)
Proof
  metis_tac [aut_accept_nonnullable_length_int,
             smtstringTheory.re_nullable_def]
QED

Theorem aut_accept_range_length_zero:
  aut_accept s 0 (reglan_range lo hi) ==>
  (&(smtstr_len s) : int) >= 1
Proof
  strip_tac >>
  drule aut_accept_range_length_int >>
  simp [integerTheory.INT_GE, integerTheory.INT_OF_NUM_LE]
QED

Theorem aut_accept_loop_positive_length_zero:
  aut_accept s 0 (reglan_loop (reglan_to_re [c]) (SUC i) n) ==>
  (&(smtstr_len s) : int) >= 1
Proof
  strip_tac >>
  `~re_nullable
      (reglan_loop (reglan_to_re [c]) (SUC i) n)` by
    simp [smtstringTheory.re_nullable_def] >>
  `aut_accept s 0
      (reglan_loop (reglan_to_re [c]) (SUC i) n) /\
   ~re_nullable
      (reglan_loop (reglan_to_re [c]) (SUC i) n)` by
    simp [] >>
  drule aut_accept_nonnullable_length_int >>
  simp [integerTheory.INT_GE, integerTheory.INT_OF_NUM_LE]
QED

Theorem aut_accept_loop_positive_length_seq_unit:
  aut_accept s 0
    (reglan_loop (reglan_to_re (seq_unit c)) 1 n) ==>
  (&(smtstr_len s) : int) >= 1
Proof
  strip_tac >>
  `~re_nullable
      (reglan_loop (reglan_to_re (seq_unit c)) 1 n)` by
    simp [smtstringTheory.re_nullable_def, seq_unit_compute] >>
  `aut_accept s 0
      (reglan_loop (reglan_to_re (seq_unit c)) 1 n) /\
   ~re_nullable
      (reglan_loop (reglan_to_re (seq_unit c)) 1 n)` by
    simp [] >>
  drule aut_accept_nonnullable_length_int >>
  simp [integerTheory.INT_GE, integerTheory.INT_OF_NUM_LE]
QED

Theorem aut_accept_plus_allchar_length_one:
  aut_accept s 1 (reglan_plus reglan_allchar) ==>
  (&(smtstr_len s) : int) >= 2
Proof
  strip_tac >>
  `aut_accept s 1 (reglan_plus reglan_allchar) /\
   ~re_nullable (reglan_plus reglan_allchar)` by
    simp [smtstringTheory.re_nullable_def] >>
  drule aut_accept_nonnullable_length_int >>
  simp [integerTheory.INT_GE, integerTheory.INT_OF_NUM_LE]
QED

Theorem aut_accept_step:
  k < LENGTH s ==>
  (aut_accept s k r <=>
   aut_accept s (SUC k)
     (re_deriv (seq_nth_i s k) r))
Proof
  strip_tac >>
  `DROP k s = EL k s::DROP (SUC k) s` by
    simp [rich_listTheory.DROP_CONS_EL] >>
  `seq_nth_i s k = EL k s` by
    simp [seq_nth_i_def] >>
  simp [aut_accept_compute, smtstringTheory.re_deriv_correct]
QED

Theorem aut_accept_transition:
  aut_accept s k r ==>
  LENGTH s <= k \/
  aut_accept s (SUC k)
    (re_deriv (seq_nth_i s k) r)
Proof
  Cases_on `k < LENGTH s`
  >- simp [aut_accept_step]
  >> decide_tac
QED

Theorem aut_accept_transition_int:
  ~aut_accept s k r \/
  (&(smtstr_len s) : int) <= &k \/
  aut_accept s (SUC k)
    (re_deriv (seq_nth_i s k) r)
Proof
  simp [smtstringTheory.smtstr_len_def,
        integerTheory.INT_OF_NUM_LE] >>
  metis_tac [aut_accept_transition]
QED

Theorem aut_accept_range_deriv:
  aut_accept s k
      (re_deriv d (reglan_range [97] [122])) <=>
  d <= 122 /\ 97 <= d /\
  aut_accept s k (reglan_to_re [])
Proof
  Cases_on `97 <= d /\ d <= 122`
  >- (`d <= 196607` by decide_tac >>
      fs [smtstringTheory.re_deriv_def, aut_accept_compute,
          smtstringTheory.smt_in_re_def])
  >> fs [smtstringTheory.re_deriv_def, aut_accept_compute,
         smtstringTheory.smt_in_re_def]
QED

Theorem aut_accept_loop_deriv_1_3:
  aut_accept s k
      (re_deriv d (reglan_loop (reglan_to_re [c]) 1 3)) <=>
  d = c /\
  aut_accept s k (reglan_loop (reglan_to_re [c]) 0 2)
Proof
  simp [aut_accept_compute,
        smtstringTheory.re_deriv_loop_singleton_1_3]
QED

Theorem aut_accept_loop_deriv_0_2:
  aut_accept s k
      (re_deriv d (reglan_loop (reglan_to_re [c]) 0 2)) <=>
  d = c /\
  aut_accept s k (reglan_loop (reglan_to_re [c]) 0 1)
Proof
  simp [aut_accept_compute,
        smtstringTheory.re_deriv_loop_singleton_0_2]
QED

Theorem aut_accept_loop_deriv_0_1:
  aut_accept s k
      (re_deriv d (reglan_loop (reglan_to_re [c]) 0 1)) <=>
  d = c /\ aut_accept s k (reglan_to_re [])
Proof
  simp [aut_accept_compute,
        smtstringTheory.re_deriv_loop_singleton_0_1]
QED

Theorem aut_accept_loop_nullable_deriv_1_2:
  aut_accept s k
      (re_deriv d
        (reglan_loop
          (reglan_union (reglan_to_re [c]) (reglan_to_re []))
          1 2)) <=>
  d = c /\
  aut_accept s k
    (reglan_loop
      (reglan_union (reglan_to_re [c]) (reglan_to_re []))
      0 1)
Proof
  simp [aut_accept_compute,
        smtstringTheory.re_deriv_loop_nullable_singleton_1_2]
QED

Theorem aut_accept_loop_nullable_deriv_0_1:
  aut_accept s k
      (re_deriv d
        (reglan_loop
          (reglan_union (reglan_to_re [c]) (reglan_to_re []))
          0 1)) <=>
  d = c /\ aut_accept s k (reglan_to_re [])
Proof
  simp [aut_accept_compute,
        smtstringTheory.re_deriv_loop_nullable_singleton_0_1]
QED

Theorem aut_accept_range_transition_zero:
  ~aut_accept s 0 (reglan_range [97] [122]) \/
  (&(smtstr_len s) : int) <= 0 \/
  (seq_nth_i s 0 <= 122 /\ 97 <= seq_nth_i s 0 /\
   aut_accept s 1 (reglan_to_re []))
Proof
  PURE_REWRITE_TAC [GSYM aut_accept_range_deriv] >>
  PURE_REWRITE_TAC [integerTheory.INT_OF_NUM_LE] >>
  Cases_on `aut_accept s 0 (reglan_range [97] [122])` >>
  simp [smtstringTheory.smtstr_len_def] >>
  drule aut_accept_transition >>
  simp []
QED

Theorem aut_accept_loop_transition_zero:
  ~aut_accept s 0
      (reglan_loop (reglan_to_re [c]) 1 3) \/
  (&(smtstr_len s) : int) <= 0 \/
  (seq_nth_i s 0 = c /\
   aut_accept s 1
     (reglan_loop (reglan_to_re [c]) 0 2))
Proof
  PURE_REWRITE_TAC [GSYM aut_accept_loop_deriv_1_3] >>
  PURE_REWRITE_TAC [integerTheory.INT_OF_NUM_LE] >>
  Cases_on
    `aut_accept s 0
       (reglan_loop (reglan_to_re [c]) 1 3)` >>
  simp [smtstringTheory.smtstr_len_def] >>
  drule aut_accept_transition >>
  simp []
QED

Theorem aut_accept_loop_transition_one:
  ~aut_accept s 1
      (reglan_loop (reglan_to_re [c]) 0 2) \/
  (&(smtstr_len s) : int) <= 1 \/
  (seq_nth_i s 1 = c /\
   aut_accept s 2
     (reglan_loop (reglan_to_re [c]) 0 1))
Proof
  PURE_REWRITE_TAC [GSYM aut_accept_loop_deriv_0_2] >>
  PURE_REWRITE_TAC [integerTheory.INT_OF_NUM_LE] >>
  Cases_on
    `aut_accept s 1
       (reglan_loop (reglan_to_re [c]) 0 2)` >>
  simp [smtstringTheory.smtstr_len_def] >>
  drule aut_accept_transition >>
  simp []
QED

Theorem aut_accept_loop_transition_two:
  ~aut_accept s 2
      (reglan_loop (reglan_to_re [c]) 0 1) \/
  (&(smtstr_len s) : int) <= 2 \/
  (seq_nth_i s 2 = c /\
   aut_accept s 3 (reglan_to_re []))
Proof
  PURE_REWRITE_TAC [GSYM aut_accept_loop_deriv_0_1] >>
  PURE_REWRITE_TAC [integerTheory.INT_OF_NUM_LE] >>
  Cases_on
    `aut_accept s 2
       (reglan_loop (reglan_to_re [c]) 0 1)` >>
  simp [smtstringTheory.smtstr_len_def] >>
  drule aut_accept_transition >>
  simp []
QED

Theorem aut_accept_empty:
  aut_accept s k (reglan_to_re []) <=> LENGTH s <= k
Proof
  simp [aut_accept_compute, smtstringTheory.smt_in_re_def]
QED

Theorem aut_accept_empty_terminal_int:
  ~aut_accept s k (reglan_to_re []) \/
  (&(smtstr_len s) : int) <= &k \/ F
Proof
  simp [aut_accept_empty, smtstringTheory.smtstr_len_def,
        integerTheory.INT_OF_NUM_LE]
QED

Theorem aut_accept_comp_singleton_transition:
  ~aut_accept s 0
      (reglan_comp (reglan_to_re [c])) \/
  (&(smtstr_len s) : int) <= 0 \/
  (seq_nth_i s 0 <> c \/
   aut_accept s 1 (reglan_plus reglan_allchar))
Proof
  Cases_on `s` >>
  simp [aut_accept_compute, smtstringTheory.smtstr_len_def,
        seq_nth_i_compute, smtstringTheory.smt_in_re_def,
        smtstringTheory.smt_in_re_plus_allchar,
        smtstringTheory.wfstr_compute] >>
  Cases_on `t` >>
  simp [smtstringTheory.wfstr_compute] >>
  metis_tac []
QED

Theorem aut_accept_comp_range_transition:
  ~aut_accept s 0
      (reglan_comp (reglan_range [lo] [hi])) \/
  (&(smtstr_len s) : int) <= 0 \/
  (seq_nth_i s 0 < lo \/ hi < seq_nth_i s 0 \/
   aut_accept s 1 (reglan_plus reglan_allchar))
Proof
  Cases_on `s` >>
  simp [aut_accept_compute, smtstringTheory.smtstr_len_def,
        seq_nth_i_compute, smtstringTheory.smt_in_re_def,
        smtstringTheory.smt_in_re_plus_allchar,
        smtstringTheory.wfstr_compute] >>
  Cases_on `t` >>
  simp [smtstringTheory.wfstr_compute] >>
  metis_tac []
QED

Theorem aut_accept_inter_range_comp_transition:
  ~aut_accept s 0
      (reglan_inter
        (reglan_range [97] [122])
        (reglan_comp (reglan_to_re [109]))) \/
  (&(smtstr_len s) : int) <= 0 \/
  (97 <= seq_nth_i s 0 /\ seq_nth_i s 0 <= 122 /\
   seq_nth_i s 0 <> 109 /\
   aut_accept s 1 (reglan_to_re []))
Proof
  Cases_on `s` >>
  simp [aut_accept_compute, smtstringTheory.smtstr_len_def,
        seq_nth_i_compute, smtstringTheory.smt_in_re_def,
        smtstringTheory.wfstr_compute] >>
  metis_tac []
QED

Theorem aut_accept_loop_nullable_transition_zero:
  ~aut_accept s 0
      (reglan_loop
        (reglan_union (reglan_to_re [c]) (reglan_to_re []))
        1 2) \/
  (&(smtstr_len s) : int) <= 0 \/
  (seq_nth_i s 0 = c /\
   aut_accept s 1
     (reglan_loop
       (reglan_union (reglan_to_re [c]) (reglan_to_re []))
       0 1))
Proof
  PURE_REWRITE_TAC
    [GSYM aut_accept_loop_nullable_deriv_1_2] >>
  PURE_REWRITE_TAC [integerTheory.INT_OF_NUM_LE] >>
  Cases_on
    `aut_accept s 0
       (reglan_loop
         (reglan_union (reglan_to_re [c]) (reglan_to_re []))
         1 2)` >>
  simp [smtstringTheory.smtstr_len_def] >>
  drule aut_accept_transition >>
  simp []
QED

Theorem aut_accept_loop_nullable_transition_one:
  ~aut_accept s 1
      (reglan_loop
        (reglan_union (reglan_to_re [c]) (reglan_to_re []))
        0 1) \/
  (&(smtstr_len s) : int) <= 1 \/
  (seq_nth_i s 1 = c /\
   aut_accept s 2 (reglan_to_re []))
Proof
  PURE_REWRITE_TAC
    [GSYM aut_accept_loop_nullable_deriv_0_1] >>
  PURE_REWRITE_TAC [integerTheory.INT_OF_NUM_LE] >>
  Cases_on
    `aut_accept s 1
       (reglan_loop
         (reglan_union (reglan_to_re [c]) (reglan_to_re []))
         0 1)` >>
  simp [smtstringTheory.smtstr_len_def] >>
  drule aut_accept_transition >>
  simp []
QED

Theorem aut_accept_range_transition_seq_unit:
  ~aut_accept s 0
      (reglan_range (seq_unit 97) (seq_unit 122)) \/
  (&(smtstr_len s) : int) <= 0 \/
  (seq_nth_i s 0 <= 122 /\ 97 <= seq_nth_i s 0 /\
   aut_accept s 1 (reglan_to_re []))
Proof
  PURE_REWRITE_TAC [seq_unit_compute] >>
  ACCEPT_TAC aut_accept_range_transition_zero
QED

Theorem aut_accept_loop_transition_seq_unit_zero:
  ~aut_accept s 0
      (reglan_loop (reglan_to_re (seq_unit c)) 1 3) \/
  (&(smtstr_len s) : int) <= 0 \/
  (seq_nth_i s 0 = c /\
   aut_accept s 1
     (reglan_loop (reglan_to_re (seq_unit c)) 0 2))
Proof
  PURE_REWRITE_TAC [seq_unit_compute] >>
  ACCEPT_TAC aut_accept_loop_transition_zero
QED

Theorem aut_accept_loop_transition_seq_unit_one:
  ~aut_accept s 1
      (reglan_loop (reglan_to_re (seq_unit c)) 0 2) \/
  (&(smtstr_len s) : int) <= 1 \/
  (seq_nth_i s 1 = c /\
   aut_accept s 2
     (reglan_loop (reglan_to_re (seq_unit c)) 0 1))
Proof
  PURE_REWRITE_TAC [seq_unit_compute] >>
  ACCEPT_TAC aut_accept_loop_transition_one
QED

Theorem aut_accept_loop_transition_seq_unit_two:
  ~aut_accept s 2
      (reglan_loop (reglan_to_re (seq_unit c)) 0 1) \/
  (&(smtstr_len s) : int) <= 2 \/
  (seq_nth_i s 2 = c /\
   aut_accept s 3 (reglan_to_re []))
Proof
  PURE_REWRITE_TAC [seq_unit_compute] >>
  ACCEPT_TAC aut_accept_loop_transition_two
QED

Theorem aut_accept_comp_transition_seq_unit:
  ~aut_accept s 0
      (reglan_comp (reglan_to_re (seq_unit c))) \/
  (&(smtstr_len s) : int) <= 0 \/
  (seq_nth_i s 0 <> c \/
   aut_accept s 1 (reglan_plus reglan_allchar))
Proof
  PURE_REWRITE_TAC [seq_unit_compute] >>
  ACCEPT_TAC aut_accept_comp_singleton_transition
QED

Theorem aut_accept_comp_range_transition_seq_unit:
  ~aut_accept s 0
      (reglan_comp
        (reglan_range (seq_unit lo) (seq_unit hi))) \/
  (&(smtstr_len s) : int) <= 0 \/
  (seq_nth_i s 0 < lo \/ hi < seq_nth_i s 0 \/
   aut_accept s 1 (reglan_plus reglan_allchar))
Proof
  PURE_REWRITE_TAC [seq_unit_compute] >>
  ACCEPT_TAC aut_accept_comp_range_transition
QED

Theorem aut_accept_inter_transition_seq_unit:
  ~aut_accept s 0
      (reglan_inter
        (reglan_range (seq_unit 97) (seq_unit 122))
        (reglan_comp (reglan_to_re (seq_unit 109)))) \/
  (&(smtstr_len s) : int) <= 0 \/
  (97 <= seq_nth_i s 0 /\ seq_nth_i s 0 <= 122 /\
   seq_nth_i s 0 <> 109 /\
   aut_accept s 1 (reglan_to_re []))
Proof
  PURE_REWRITE_TAC [seq_unit_compute] >>
  ACCEPT_TAC aut_accept_inter_range_comp_transition
QED

Theorem aut_accept_loop_nullable_transition_seq_unit_zero:
  ~aut_accept s 0
      (reglan_loop
        (reglan_union
          (reglan_to_re (seq_unit c)) (reglan_to_re []))
        1 2) \/
  (&(smtstr_len s) : int) <= 0 \/
  (seq_nth_i s 0 = c /\
   aut_accept s 1
     (reglan_loop
       (reglan_union
         (reglan_to_re (seq_unit c)) (reglan_to_re []))
       0 1))
Proof
  PURE_REWRITE_TAC [seq_unit_compute] >>
  ACCEPT_TAC aut_accept_loop_nullable_transition_zero
QED

Theorem aut_accept_loop_nullable_transition_seq_unit_one:
  ~aut_accept s 1
      (reglan_loop
        (reglan_union
          (reglan_to_re (seq_unit c)) (reglan_to_re []))
        0 1) \/
  (&(smtstr_len s) : int) <= 1 \/
  (seq_nth_i s 1 = c /\
   aut_accept s 2 (reglan_to_re []))
Proof
  PURE_REWRITE_TAC [seq_unit_compute] >>
  ACCEPT_TAC aut_accept_loop_nullable_transition_one
QED

(* TASK_02 draft_substr and draft_re_comp record the length, at/nth_i,
   and head/tail decomposition clauses below. *)

Theorem seq_unit_length:
  smtstr_len (seq_unit c) = 1
Proof
  simp [seq_unit_def, smtstringTheory.smtstr_len_def]
QED

Theorem seq_split_at:
  i < LENGTH s ==>
    s =
      TAKE i s ++
      smtstr_concat (seq_unit (seq_nth_i s i)) (seq_tail s i)
Proof
  strip_tac >>
  simp [seq_unit_def, seq_tail_def,
        smtstringTheory.smtstr_concat_def,
        seq_nth_i_def] >>
  metis_tac [rich_listTheory.TAKE_DROP_SUC]
QED

Theorem seq_head_tail:
  s = [] \/
  seq_eq s
    (smtstr_concat (seq_unit (seq_nth_i s 0)) (seq_tail s 0))
Proof
  Cases_on `s` >>
  simp [seq_eq_def, seq_unit_def, seq_tail_def,
        smtstringTheory.smtstr_concat_def, seq_nth_i_def]
QED

(* TASK_02 draft_regex_membership, draft_substr, and draft_re_comp all emit
   this integer-length form of the head/tail alternative. *)

Theorem seq_head_tail_int:
  &(smtstr_len s) = 0 \/
  seq_eq s
    (smtstr_concat (seq_unit (seq_nth_i s 0)) (seq_tail s 0))
Proof
  Cases_on `s` >>
  simp [seq_eq_def, seq_unit_def, seq_tail_def,
        smtstringTheory.smtstr_concat_def,
        smtstringTheory.smtstr_len_def, seq_nth_i_def]
QED

Theorem seq_head_tail_int_zero_left:
  0 = &(smtstr_len s) \/
  seq_eq s
    (smtstr_concat (seq_unit (seq_nth_i s 0)) (seq_tail s 0))
Proof
  metis_tac [seq_head_tail_int]
QED

(* TASK_02 draft_regex_membership uses these singleton consequences of the
   prefix witnesses and concat decompositions. *)

Theorem seq_prefixof_singleton:
  seq_eq s
      (smtstr_concat (seq_unit (seq_nth_i s 0)) (seq_tail s 0)) /\
    smtstr_prefixof s (seq_unit c) ==>
  s = seq_unit c
Proof
  Cases_on `s` >>
  simp [seq_eq_def, seq_unit_def, seq_tail_def,
        smtstringTheory.smtstr_concat_def,
        smtstringTheory.smtstr_prefixof_singleton,
        seq_nth_i_def]
QED

Theorem seq_prefixof_head:
  seq_eq s
      (smtstr_concat (seq_unit (seq_nth_i s 0)) (seq_tail s 0)) /\
    smtstr_prefixof s (seq_unit c) ==>
  c = seq_nth_i s 0
Proof
  Cases_on `s` >>
  simp [seq_eq_def, seq_unit_def, seq_tail_def,
        smtstringTheory.smtstr_concat_def,
        smtstringTheory.smtstr_prefixof_singleton,
        seq_nth_i_def]
QED

Theorem seq_concat_middle_singleton:
  seq_eq (seq_unit d)
    (smtstr_concat p (smtstr_concat (seq_unit c) q)) ==>
  c = d
Proof
  simp [seq_eq_def, seq_unit_def] >>
  metis_tac [smtstringTheory.smtstr_concat_middle_singleton]
QED

Theorem seq_concat_middle_singleton_result:
  seq_eq (seq_unit d)
    (smtstr_concat p (smtstr_concat (seq_unit c) q)) ==>
  d = c
Proof
  metis_tac [seq_concat_middle_singleton]
QED

Theorem seq_concat_middle_singleton_right:
  smtstr_concat p (smtstr_concat (seq_unit c) q) = seq_unit d ==>
  d = c
Proof
  simp [seq_unit_def] >>
  metis_tac [smtstringTheory.smtstr_concat_middle_singleton]
QED

Theorem seq_concat_middle_singleton_left:
  seq_unit d = smtstr_concat p (smtstr_concat (seq_unit c) q) ==>
  d = c
Proof
  metis_tac [seq_concat_middle_singleton_right]
QED

Theorem seq_head_shared_singleton_prefix:
  s =
      smtstr_concat
        (seq_unit (seq_nth_i s 0)) (seq_tail s 0) /\
    s = smtstr_concat p (smtstr_concat (seq_unit c) q) /\
    seq_unit d = smtstr_concat p (smtstr_concat (seq_unit e) r) ==>
  seq_nth_i s 0 = c
Proof
  Cases_on `p`
  >- (Cases_on `s` >>
      simp [seq_unit_def, seq_tail_def, seq_nth_i_def,
            smtstringTheory.smtstr_concat_def])
  >> simp [seq_unit_def, smtstringTheory.smtstr_concat_def]
QED

Theorem seq_head_shared_singleton_prefix_right:
  seq_eq s
      (smtstr_concat
        (seq_unit (seq_nth_i s 0)) (seq_tail s 0)) ==>
    s = smtstr_concat p (smtstr_concat (seq_unit c) q) ==>
    smtstr_concat p (smtstr_concat (seq_unit d) r) = seq_unit e ==>
  seq_nth_i s 0 = c
Proof
  rpt strip_tac >>
  Cases_on `p`
  >- (Cases_on `s` >>
      fs [seq_eq_def, seq_unit_def, seq_tail_def, seq_nth_i_def,
          smtstringTheory.smtstr_concat_def])
  >> fs [seq_eq_def, seq_unit_def,
         smtstringTheory.smtstr_concat_def]
QED

(* TASK_02 draft_length emits the exact two-unit reconstruction after proving
   a sequence has length two. *)

Theorem seq_length_two:
  smtstr_len s = 2 ==>
  seq_eq
    (smtstr_concat
      (seq_unit (seq_nth_i s 0)) (seq_unit (seq_nth_i s 1))) s
Proof
  Cases_on `s`
  >- simp [smtstringTheory.smtstr_len_def]
  >> Cases_on `t`
  >- simp [smtstringTheory.smtstr_len_def]
  >> Cases_on `t'`
  >- simp [seq_eq_def, seq_unit_def, seq_nth_i_def,
           smtstringTheory.smtstr_concat_def,
           smtstringTheory.smtstr_len_def]
  >> simp [smtstringTheory.smtstr_len_def]
QED

Theorem seq_two_two_concat_not_three:
  seq_eq
      (smtstr_concat
        (seq_unit (seq_nth_i y 0)) (seq_unit (seq_nth_i y 1))) y /\
    seq_eq
      (smtstr_concat
        (seq_unit (seq_nth_i x 0)) (seq_unit (seq_nth_i x 1))) x /\
    smtstr_concat (seq_unit a)
      (smtstr_concat (seq_unit b) (seq_unit c)) =
      smtstr_concat x y ==>
  F
Proof
  rpt strip_tac >>
  fs [seq_eq_def] >>
  `smtstr_len
      (smtstr_concat
        (seq_unit (seq_nth_i y 0)) (seq_unit (seq_nth_i y 1))) =
    smtstr_len y` by (AP_TERM_TAC >> first_assum ACCEPT_TAC) >>
  `smtstr_len
      (smtstr_concat
        (seq_unit (seq_nth_i x 0)) (seq_unit (seq_nth_i x 1))) =
    smtstr_len x` by (AP_TERM_TAC >> first_assum ACCEPT_TAC) >>
  `smtstr_len
      (smtstr_concat (seq_unit a)
        (smtstr_concat (seq_unit b) (seq_unit c))) =
    smtstr_len (smtstr_concat x y)` by
      (AP_TERM_TAC >> first_assum ACCEPT_TAC) >>
  fs [seq_unit_length, smtstringTheory.smtstr_len_concat] >>
  decide_tac
QED

Theorem seq_tail_step:
  SUC i < LENGTH s ==>
    seq_tail s i =
      smtstr_concat
        (seq_unit (seq_nth_i s (SUC i))) (seq_tail s (SUC i))
Proof
  strip_tac >>
  simp [seq_unit_def, seq_tail_def,
        smtstringTheory.smtstr_concat_def,
        seq_nth_i_def, rich_listTheory.DROP_EL_CONS,
        arithmeticTheory.ADD1]
QED

Theorem seq_tail_zero_step:
  s <> smtstr_at s 0 /\
    seq_eq (seq_unit (seq_nth_i s 0)) (smtstr_at s 0) /\
    seq_eq s
      (smtstr_concat (seq_unit (seq_nth_i s 0)) (seq_tail s 0)) ==>
  seq_tail s 0 =
    smtstr_concat (seq_unit (seq_nth_i s 1)) (seq_tail s 1)
Proof
  Cases_on `s`
  >- simp [seq_eq_def, seq_unit_def, seq_tail_def,
           smtstringTheory.smtstr_concat_def,
           smtstringTheory.smtstr_at_def,
           smtstringTheory.smtstr_substr_def]
  >> Cases_on `t`
  >- simp [seq_eq_def, seq_unit_def, seq_tail_def, seq_nth_i_def,
           smtstringTheory.smtstr_concat_def,
           smtstringTheory.smtstr_at_def,
           smtstringTheory.smtstr_substr_def]
  >> simp [seq_eq_def, seq_unit_def, seq_tail_def, seq_nth_i_def,
           smtstringTheory.smtstr_concat_def,
           smtstringTheory.smtstr_at_def,
           smtstringTheory.smtstr_substr_def]
QED

Theorem seq_tail_length:
  smtstr_len (seq_tail s i) = LENGTH s - SUC i
Proof
  simp [seq_tail_def, smtstringTheory.smtstr_len_def]
QED

Theorem seq_at_nth:
  i < LENGTH s ==>
    smtstr_at s (&i) = seq_unit (seq_nth_i s i)
Proof
  simp [smtstringTheory.smtstr_at_in_range, seq_unit_def,
        seq_nth_i_def]
QED

Theorem seq_at_zero:
  s = [] \/ seq_eq (smtstr_at s 0) (seq_unit (seq_nth_i s 0))
Proof
  Cases_on `s` >>
  simp [seq_eq_def, seq_at_nth]
QED

(* TASK_02 draft_str_to_int records char.is_digit, digit2int values 0--9,
   and char.bit indices 0--17.  Unicode code points fit in 18 bits. *)

Theorem char_is_digit_unicode:
  char_is_digit c ==> c <= 196607
Proof
  simp [char_is_digit_def] >>
  decide_tac
QED

Theorem seq_digit2int_digit_bounds:
  char_is_digit c ==>
    0 <= seq_digit2int c /\ seq_digit2int c <= 9
Proof
  simp [char_is_digit_def, seq_digit2int_def] >>
  intLib.ARITH_TAC
QED

Theorem seq_digit2int_digit:
  char_is_digit c ==> seq_digit2int c = &(c - 48)
Proof
  simp [char_is_digit_def, seq_digit2int_def] >>
  intLib.ARITH_TAC
QED

Theorem unicode_max_lt_2exp18:
  (196607 : num) < 2 ** 18
Proof
  CONV_TAC (RAND_CONV reduceLib.EXP_CONV) >>
  numLib.REDUCE_TAC
QED

Theorem unicode_lt_2exp18:
  (c : num) <= 196607 ==> c < 2 ** 18
Proof
  strip_tac >>
  MATCH_MP_TAC
    (Q.SPECL [`c`, `(196607 : num)`, `(2 : num) ** 18`]
       arithmeticTheory.LESS_EQ_LESS_TRANS) >>
  simp [unicode_max_lt_2exp18]
QED

Theorem char_bit_above_unicode:
  c <= 196607 /\ 18 <= k ==> ~char_bit k c
Proof
  strip_tac >>
  simp [char_bit_def] >>
  irule bitTheory.NOT_BIT_GT_TWOEXP >>
  drule unicode_lt_2exp18 >>
  drule bitTheory.TWOEXP_MONO2 >>
  decide_tac
QED

(* Ground EVAL checks for TASK_03's cursor interpretation. *)
Theorem aut_accept_catalog_eval:
  aut_state [97; 98] 0 = [97; 98] /\
  aut_state [97; 98] 1 = [98] /\
  aut_state [97; 98] 2 = [] /\
  aut_accept [97] 0 (reglan_range [97] [122]) /\
  aut_accept [97] 1 (reglan_to_re []) /\
  ~aut_accept [97; 98] 1 (reglan_to_re []) /\
  aut_accept [97; 98] 1 reglan_allchar
Proof
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
