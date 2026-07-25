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

(* Characters which distinguish derivatives of a regex.  Literal code
   points occur in syntax order; 0 represents the remaining well-formed
   character class and 196608 represents ill-formed characters. *)
Definition aut_chars_def:
  (aut_chars reglan_none = []) /\
  (aut_chars reglan_all = []) /\
  (aut_chars reglan_allchar = []) /\
  (aut_chars (reglan_to_re s) = s) /\
  (aut_chars (reglan_range lo hi) = lo ++ hi) /\
  (aut_chars (reglan_concat r1 r2) =
     aut_chars r1 ++ aut_chars r2) /\
  (aut_chars (reglan_union r1 r2) =
     aut_chars r1 ++ aut_chars r2) /\
  (aut_chars (reglan_inter r1 r2) =
     aut_chars r1 ++ aut_chars r2) /\
  (aut_chars (reglan_diff r1 r2) =
     aut_chars r1 ++ aut_chars r2) /\
  (aut_chars (reglan_comp r) = aut_chars r) /\
  (aut_chars (reglan_star r) = aut_chars r) /\
  (aut_chars (reglan_plus r) = aut_chars r) /\
  (aut_chars (reglan_opt r) = aut_chars r) /\
  (aut_chars (reglan_power r n) = aut_chars r) /\
  (aut_chars (reglan_loop r i n) = aut_chars r)
End

Definition aut_alphabet_def:
  aut_alphabet r = nub (aut_chars r ++ [0; 196608])
End

(* Z3 constructs automaton states breadth first.  Preserve that order:
   existing states first, then each state's derivatives in character-class
   order, discarding repeats at their later occurrences. *)
Definition aut_extend_def:
  aut_extend cs states =
    nub
      (states ++
       FLAT (MAP (\r. MAP (\c. re_deriv c r) cs) states))
End

Definition aut_enumerate_def:
  (aut_enumerate 0 cs states = nub states) /\
  (aut_enumerate (SUC fuel) cs states =
     aut_enumerate fuel cs (aut_extend cs states))
End

Definition aut_derivatives_def:
  aut_derivatives fuel r =
    aut_enumerate fuel (aut_alphabet r) [r]
End

(* Expanding SUC k rounds is sufficient to compute the construction-order
   prefix needed for state k.  A missing index denotes the empty language. *)
Definition aut_state_def:
  aut_state k (r : reglan) =
    if k = 0 then r
    else
      let states = aut_derivatives (SUC k) r
      in
        if k < LENGTH states then EL k states
        else reglan_none
End

Definition aut_accept_def:
  aut_accept (s : num list) k r <=>
    smt_in_re s (aut_state k r)
End

(* seq.prefix.c/d/x/y/z are proof-local witnesses, not theory constants.
   TASK_17 must introduce them through the existing z3name!k
   definition-recording machinery. *)

val _ = computeLib.add_funs
  [seq_unit_def, seq_tail_def, seq_eq_def, seq_nth_i_def,
   char_is_digit_def, seq_digit2int_def, seq_digit_def,
   seq_stoi_def, char_bit_def, aut_chars_def, aut_alphabet_def,
   aut_extend_def, aut_enumerate_def, aut_derivatives_def,
   aut_state_def, aut_accept_def];

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

Theorem aut_chars_compute[compute]:
  (aut_chars reglan_none = []) /\
  (aut_chars reglan_all = []) /\
  (aut_chars reglan_allchar = []) /\
  (aut_chars (reglan_to_re s) = s) /\
  (aut_chars (reglan_range lo hi) = lo ++ hi) /\
  (aut_chars (reglan_concat r1 r2) =
     aut_chars r1 ++ aut_chars r2) /\
  (aut_chars (reglan_union r1 r2) =
     aut_chars r1 ++ aut_chars r2) /\
  (aut_chars (reglan_inter r1 r2) =
     aut_chars r1 ++ aut_chars r2) /\
  (aut_chars (reglan_diff r1 r2) =
     aut_chars r1 ++ aut_chars r2) /\
  (aut_chars (reglan_comp r) = aut_chars r) /\
  (aut_chars (reglan_star r) = aut_chars r) /\
  (aut_chars (reglan_plus r) = aut_chars r) /\
  (aut_chars (reglan_opt r) = aut_chars r) /\
  (aut_chars (reglan_power r n) = aut_chars r) /\
  (aut_chars (reglan_loop r i n) = aut_chars r)
Proof
  simp [aut_chars_def]
QED

Theorem aut_alphabet_compute[compute]:
  aut_alphabet r = nub (aut_chars r ++ [0; 196608])
Proof
  simp [aut_alphabet_def]
QED

Theorem aut_extend_compute[compute]:
  aut_extend cs states =
    nub
      (states ++
       FLAT (MAP (\r. MAP (\c. re_deriv c r) cs) states))
Proof
  simp [aut_extend_def]
QED

Theorem aut_derivatives_compute[compute]:
  aut_derivatives fuel r =
    aut_enumerate fuel (aut_alphabet r) [r]
Proof
  simp [aut_derivatives_def]
QED

Theorem aut_state_compute[compute]:
  (aut_state 0 r = r) /\
  (aut_state (SUC k) r =
     let states = aut_derivatives (SUC (SUC k)) r
     in
       if SUC k < LENGTH states then EL (SUC k) states
       else reglan_none)
Proof
  simp [aut_state_def]
QED

Theorem aut_accept_compute[compute]:
  aut_accept s k r <=> smt_in_re s (aut_state k r)
Proof
  simp [aut_accept_def]
QED

Theorem aut_accept_zero:
  aut_accept s 0 r <=> smt_in_re s r
Proof
  simp [aut_accept_compute, aut_state_compute]
QED

Theorem aut_enumerate_distinct:
  ALL_DISTINCT (aut_enumerate fuel cs states)
Proof
  qid_spec_tac `states` >>
  Induct_on `fuel` >>
  simp [aut_enumerate_def, listTheory.all_distinct_nub]
QED

Theorem aut_derivatives_distinct:
  ALL_DISTINCT (aut_derivatives fuel r)
Proof
  simp [aut_derivatives_def, aut_enumerate_distinct]
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

(* Ground EVAL checks for TASK_03's range and complement catalogs. *)
Theorem aut_accept_catalog_eval:
  aut_state 0 (reglan_range [97] [122]) =
    reglan_range [97] [122] /\
  aut_state 1 (reglan_range [97] [122]) = reglan_to_re [] /\
  aut_state 2 (reglan_range [97] [122]) = reglan_none /\
  aut_accept [] 1 (reglan_range [97] [122]) /\
  aut_state 1 (reglan_comp (reglan_to_re [97])) =
    reglan_comp (reglan_to_re []) /\
  aut_state 2 (reglan_comp (reglan_to_re [97])) =
    reglan_comp reglan_none /\
  ~aut_accept [] 1 (reglan_comp (reglan_to_re [97])) /\
  aut_accept [] 2 (reglan_comp (reglan_to_re [97]))
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
