(* Copyright (c) 2026 The HOL4 contributors. *)

(* Definitional semantics for Z3's internal string-proof vocabulary. *)
Theory smtstringz3
Ancestors[qualified]
  smtstring bit words

(* Official SMT strings use num code points.  Proof parsing gives Z3's
   internal Char sort a bounded 18-bit representation and converts at
   the sequence boundary. *)

Definition seq_unit_def:
  seq_unit (c : num) = SmtStr [c]
End

(* Z3 numbers the tail after position i, so tail s 0 drops the head. *)
Definition seq_tail_def:
  seq_tail s i = SmtStr (DROP (SUC i) (smtstr_rep s))
End

Definition seq_eq_def:
  seq_eq (s : smtstr) t <=> s = t
End

(* nth_i is deliberately specified only in range.  Z3 leaves its value
   outside the sequence unspecified, so no out-of-range equation may be
   added here.  The code-point bound is not such an equation: Z3's element
   sort is Char, so whatever seq.nth_i returns is a character whether or not
   the index is in range.  Recording that keeps 'seq_unit (seq_nth_i s i)'
   a genuine one-character string, which the bounded ':smtstr' carrier needs
   and which the sequence-shape lemmas below rely on. *)
Theorem seq_nth_i_exists[local]:
  ?f : smtstr -> num -> num.
    (!s i.
       i < LENGTH (smtstr_rep s) ==>
       f s i = EL i (smtstr_rep s)) /\
    (!s i. f s i <= 196607)
Proof
  qexists
    `\s i.
       if i < LENGTH (smtstr_rep s) then
         EL i (smtstr_rep s)
       else 0` >>
  rw [] >>
  `EVERY (\c. c <= 196607) (DROP i (smtstr_rep s))` by
    (irule rich_listTheory.EVERY_DROP >> simp []) >>
  rfs [rich_listTheory.DROP_CONS_EL]
QED

val seq_nth_i_spec =
  new_specification
    ("seq_nth_i_spec", ["seq_nth_i"], seq_nth_i_exists);

Theorem seq_nth_i_def = CONJUNCT1 seq_nth_i_spec

Theorem seq_nth_i_bound[simp] = CONJUNCT2 seq_nth_i_spec

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
  seq_stoi s i =
    smtstr_to_int (SmtStr (TAKE (SUC i) (smtstr_rep s)))
End

Definition char_bit_def:
  char_bit k (c : num) <=> BIT k c
End

(* TASK_03's five-version catalog refutes a construction-order state
   number: k is the cursor in the original string, while the regex argument
   already denotes the residual language. *)
Definition aut_state_def:
  aut_state s k = SmtStr (DROP k (smtstr_rep s))
End

Definition aut_accept_def:
  aut_accept s k r <=>
    smt_in_re (aut_state s k) r
End

(* seq.prefix.c/d/x/y/z are proof-local witnesses, not theory constants.
   TASK_17 must introduce them through the existing z3name!k
   definition-recording machinery. *)

(* Evaluation equations consumed by the character and regex replay rungs. *)

(* A constructor-recursive equation would be unsound under the bounded
   carrier: 'SmtStr (h::s)' constrains nothing unless 'h' is a code point.
   The evaluation rule is therefore the representation-level one, which
   'smtstr_rep_compute' already reduces for a literal argument. *)
Theorem seq_nth_i_compute[compute]:
  i < LENGTH (smtstr_rep s) ==>
  (seq_nth_i s i = EL i (smtstr_rep s))
Proof
  simp [seq_nth_i_def]
QED

(* Proof parsing represents Z3's internal Char sort by an 18-bit word.
   Official SMT strings remain num lists; these lemmas are the checked
   boundary between those representations. *)

Theorem char_is_digit_word18:
  char_is_digit (w2n (c : 18 word)) <=>
    (n2w 48 : 18 word) <=+ c /\ c <=+ (n2w 57 : 18 word)
Proof
  simp [char_is_digit_def, wordsTheory.WORD_LS]
QED

Theorem char_le_word18:
  w2n (c : 18 word) <= w2n d <=> c <=+ d
Proof
  simp [wordsTheory.WORD_LS]
QED

Theorem char_bit_word18:
  k < 18 ==>
    (char_bit k (w2n (c : 18 word)) <=> word_bit k c)
Proof
  rw [char_bit_def] >>
  `c = n2w (w2n c)` by simp [] >>
  pop_assum SUBST1_TAC >>
  simp [wordsTheory.word_bit_n2w, arithmeticTheory.LESS_MOD,
        wordsTheory.w2n_lt]
QED

Theorem aut_accept_compute[compute]:
  aut_accept s k r <=>
    smt_in_re (SmtStr (DROP k (smtstr_rep s))) r
Proof
  simp [aut_accept_def, aut_state_def]
QED

Theorem aut_accept_zero:
  aut_accept s 0 r <=> smt_in_re s r
Proof
  simp [aut_accept_compute]
QED

(* The automaton state is a suffix of the representation, and every suffix of
   a representation is itself a wellformed word.  Reading 'aut_accept' as a
   word-level membership therefore discharges the code-point side conditions
   once and for all, and lets the transition lemmas below appeal to the
   unconditional word-level derivative correspondence. *)

Theorem aut_accept_lang:
  aut_accept s k r <=> re_lang r (DROP k (smtstr_rep s))
Proof
  `EVERY (\c. c <= 196607) (DROP k (smtstr_rep s))` by
    (irule rich_listTheory.EVERY_DROP >> simp []) >>
  simp [aut_accept_compute, smtstringTheory.smt_in_re_rep,
        smtstringTheory.smtstr_rep_def]
QED

Theorem aut_accept_empty:
  aut_accept s k (reglan_to_re (SmtStr [])) <=>
  LENGTH (smtstr_rep s) <= k
Proof
  simp [aut_accept_lang, smtstringTheory.re_lang_def,
        smtstringTheory.smtstr_rep_def]
QED

Theorem aut_accept_plus_allchar:
  aut_accept s k (reglan_plus reglan_allchar) <=>
  DROP k (smtstr_rep s) <> []
Proof
  `EVERY (\c. c <= 196607) (DROP k (smtstr_rep s))` by
    (irule rich_listTheory.EVERY_DROP >> simp []) >>
  simp [aut_accept_compute, smtstringTheory.smt_in_re_plus_allchar,
        GSYM smtstringTheory.smtstr_rep_eq_nil,
        smtstringTheory.smtstr_rep_def]
QED

(* A loop whose two bounds have been driven down to zero accepts exactly the
   empty word; the derivative lemmas below hand the terminal state back in
   this shape. *)
Theorem aut_accept_loop_empty:
  aut_accept s k (reglan_loop r 0 0) <=>
  aut_accept s k (reglan_to_re (SmtStr []))
Proof
  simp [aut_accept_compute, smtstringTheory.smt_in_re_loop_empty]
QED

Theorem aut_accept_nonnullable_length:
  aut_accept s k r /\ ~re_nullable r ==>
  SUC k <= LENGTH (smtstr_rep s)
Proof
  rw [aut_accept_compute, smtstringTheory.re_nullable_correct] >>
  Cases_on `k < LENGTH (smtstr_rep s)`
  >- decide_tac
  >> `LENGTH (smtstr_rep s) <= k` by decide_tac >>
  fs [listTheory.DROP_LENGTH_TOO_LONG,
      smtstringTheory.smtstr_rep_def]
QED

Theorem aut_accept_nonnullable_length_int:
  aut_accept s k r /\ ~re_nullable r ==>
  (&(SUC k) : int) <= smtstr_len s
Proof
  strip_tac >>
  drule aut_accept_nonnullable_length >>
  simp [smtstringTheory.smtstr_len_def]
QED

Theorem aut_accept_range_length_int:
  aut_accept s k (reglan_range lo hi) ==>
  (&(SUC k) : int) <= smtstr_len s
Proof
  metis_tac [aut_accept_nonnullable_length_int,
             smtstringTheory.re_nullable_def]
QED

Theorem aut_accept_range_length_zero:
  aut_accept s 0 (reglan_range lo hi) ==>
  smtstr_len s >= 1
Proof
  strip_tac >>
  drule aut_accept_range_length_int >>
  simp [integerTheory.INT_GE, integerTheory.INT_OF_NUM_LE]
QED

(* 'reglan_to_re (SmtStr [c])' is a one-character language only when 'c' is a
   real code point: out of range 'SmtStr [c]' is an unconstrained element of
   ':smtstr' and may well be the empty string, which would make the loop
   nullable.  Hence the bound. *)

Theorem aut_accept_loop_positive_length_zero:
  c <= 196607 /\
  aut_accept s 0 (reglan_loop (reglan_to_re (SmtStr [c])) (SUC i) n) ==>
  smtstr_len s >= 1
Proof
  strip_tac >>
  `~re_nullable
      (reglan_loop (reglan_to_re (SmtStr [c])) (SUC i) n)` by
    simp [smtstringTheory.re_nullable_def,
          GSYM smtstringTheory.smtstr_rep_eq_nil,
          smtstringTheory.smtstr_rep_def] >>
  `aut_accept s 0
      (reglan_loop (reglan_to_re (SmtStr [c])) (SUC i) n) /\
   ~re_nullable
      (reglan_loop (reglan_to_re (SmtStr [c])) (SUC i) n)` by
    simp [] >>
  drule aut_accept_nonnullable_length_int >>
  simp [integerTheory.INT_GE, integerTheory.INT_OF_NUM_LE]
QED

Theorem aut_accept_loop_positive_length_seq_unit:
  c <= 196607 /\
  aut_accept s 0 (reglan_loop (reglan_to_re (seq_unit c)) 1 n) ==>
  smtstr_len s >= 1
Proof
  PURE_REWRITE_TAC [seq_unit_def] >>
  mp_tac (Q.INST [`i` |-> `0`] aut_accept_loop_positive_length_zero) >>
  simp []
QED

Theorem aut_accept_plus_allchar_length_one:
  aut_accept s 1 (reglan_plus reglan_allchar) ==>
  smtstr_len s >= 2
Proof
  strip_tac >>
  `aut_accept s 1 (reglan_plus reglan_allchar) /\
   ~re_nullable (reglan_plus reglan_allchar)` by
    simp [smtstringTheory.re_nullable_def] >>
  drule aut_accept_nonnullable_length_int >>
  simp [integerTheory.INT_GE, integerTheory.INT_OF_NUM_LE]
QED

Theorem aut_accept_step:
  k < LENGTH (smtstr_rep s) ==>
  (aut_accept s k r <=>
  aut_accept s (SUC k)
     (re_deriv (seq_nth_i s k) r))
Proof
  strip_tac >>
  `DROP k (smtstr_rep s) =
     EL k (smtstr_rep s)::DROP (SUC k) (smtstr_rep s)` by
    simp [rich_listTheory.DROP_CONS_EL] >>
  `seq_nth_i s k = EL k (smtstr_rep s)` by
    simp [seq_nth_i_def] >>
  simp [aut_accept_lang, smtstringTheory.re_deriv_lang]
QED

Theorem aut_accept_transition:
  aut_accept s k r ==>
  LENGTH (smtstr_rep s) <= k \/
  aut_accept s (SUC k)
    (re_deriv (seq_nth_i s k) r)
Proof
  Cases_on `k < LENGTH (smtstr_rep s)`
  >- simp [aut_accept_step]
  >> decide_tac
QED

Theorem aut_accept_transition_int:
  ~aut_accept s k r \/
  smtstr_len s <= &k \/
  aut_accept s (SUC k)
    (re_deriv (seq_nth_i s k) r)
Proof
  simp [smtstringTheory.smtstr_len_def,
        integerTheory.INT_OF_NUM_LE] >>
  metis_tac [aut_accept_transition]
QED

(* The derivative of a regex the Z3 automaton walks over, computed once for
   arbitrary range endpoints, arbitrary loop bounds and an arbitrary state.
   The named instances further down are corollaries; nothing here is tied to
   the endpoints or bounds a particular benchmark happens to use. *)

Theorem aut_accept_range_deriv:
  lo <= 196607 /\ hi <= 196607 ==>
  (aut_accept s k
      (re_deriv d (reglan_range (SmtStr [lo]) (SmtStr [hi]))) <=>
   d <= hi /\ lo <= d /\
   aut_accept s k (reglan_to_re (SmtStr [])))
Proof
  strip_tac >>
  Cases_on `lo <= d /\ d <= hi`
  >- (`d <= 196607` by decide_tac >>
      fs [smtstringTheory.re_deriv_def, aut_accept_compute,
          smtstringTheory.smt_in_re_def,
          smtstringTheory.smtstr_rep_def])
  >> fs [smtstringTheory.re_deriv_def, aut_accept_compute,
         smtstringTheory.smt_in_re_def,
         smtstringTheory.smtstr_rep_def]
QED

Theorem aut_accept_loop_deriv:
  c <= 196607 ==>
  (aut_accept s k
      (re_deriv d (reglan_loop (reglan_to_re (SmtStr [c])) i n)) <=>
   n <> 0 /\ d = c /\
   aut_accept s k
     (reglan_loop (reglan_to_re (SmtStr [c])) (i - 1) (n - 1)))
Proof
  strip_tac >>
  simp [aut_accept_compute,
        smtstringTheory.re_deriv_loop_singleton]
QED

Theorem aut_accept_loop_nullable_deriv:
  c <= 196607 ==>
  (aut_accept s k
      (re_deriv d
        (reglan_loop
          (reglan_union (reglan_to_re (SmtStr [c])) (reglan_to_re (SmtStr [])))
          i n)) <=>
   i <= n /\ n <> 0 /\ d = c /\
   aut_accept s k
     (reglan_loop
       (reglan_union (reglan_to_re (SmtStr [c])) (reglan_to_re (SmtStr [])))
       0 (n - 1)))
Proof
  strip_tac >>
  simp [aut_accept_compute,
        smtstringTheory.re_deriv_loop_nullable_singleton]
QED

Theorem aut_accept_loop_deriv_1_3:
  c <= 196607 ==>
  (aut_accept s k
      (re_deriv d (reglan_loop (reglan_to_re (SmtStr [c])) 1 3)) <=>
   d = c /\
   aut_accept s k (reglan_loop (reglan_to_re (SmtStr [c])) 0 2))
Proof
  rw [aut_accept_loop_deriv]
QED

Theorem aut_accept_loop_deriv_0_2:
  c <= 196607 ==>
  (aut_accept s k
      (re_deriv d (reglan_loop (reglan_to_re (SmtStr [c])) 0 2)) <=>
   d = c /\
   aut_accept s k (reglan_loop (reglan_to_re (SmtStr [c])) 0 1))
Proof
  rw [aut_accept_loop_deriv]
QED

Theorem aut_accept_loop_deriv_0_1:
  c <= 196607 ==>
  (aut_accept s k
      (re_deriv d (reglan_loop (reglan_to_re (SmtStr [c])) 0 1)) <=>
   d = c /\ aut_accept s k (reglan_to_re (SmtStr [])))
Proof
  rw [aut_accept_loop_deriv, aut_accept_loop_empty]
QED

Theorem aut_accept_loop_nullable_deriv_1_2:
  c <= 196607 ==>
  (aut_accept s k
      (re_deriv d
        (reglan_loop
          (reglan_union (reglan_to_re (SmtStr [c])) (reglan_to_re (SmtStr [])))
          1 2)) <=>
   d = c /\
   aut_accept s k
     (reglan_loop
       (reglan_union (reglan_to_re (SmtStr [c])) (reglan_to_re (SmtStr [])))
       0 1))
Proof
  rw [aut_accept_loop_nullable_deriv]
QED

Theorem aut_accept_loop_nullable_deriv_0_1:
  c <= 196607 ==>
  (aut_accept s k
      (re_deriv d
        (reglan_loop
          (reglan_union (reglan_to_re (SmtStr [c])) (reglan_to_re (SmtStr [])))
          0 1)) <=>
   d = c /\ aut_accept s k (reglan_to_re (SmtStr [])))
Proof
  rw [aut_accept_loop_nullable_deriv, aut_accept_loop_empty]
QED

(* The transition steps Z3's 'aut.accept' proofs emit, again for arbitrary
   endpoints, bounds and states. *)

Theorem aut_accept_range_transition:
  lo <= 196607 /\ hi <= 196607 ==>
  (~aut_accept s k (reglan_range (SmtStr [lo]) (SmtStr [hi])) \/
   smtstr_len s <= &k \/
   (seq_nth_i s k <= hi /\ lo <= seq_nth_i s k /\
    aut_accept s (SUC k) (reglan_to_re (SmtStr []))))
Proof
  strip_tac >>
  Cases_on `aut_accept s k (reglan_range (SmtStr [lo]) (SmtStr [hi]))` >>
  simp [smtstringTheory.smtstr_len_def,
        integerTheory.INT_OF_NUM_LE] >>
  drule aut_accept_transition >>
  simp [aut_accept_range_deriv]
QED

Theorem aut_accept_loop_transition:
  c <= 196607 ==>
  (~aut_accept s k (reglan_loop (reglan_to_re (SmtStr [c])) i n) \/
   smtstr_len s <= &k \/
   (n <> 0 /\ seq_nth_i s k = c /\
    aut_accept s (SUC k)
      (reglan_loop (reglan_to_re (SmtStr [c])) (i - 1) (n - 1))))
Proof
  strip_tac >>
  Cases_on `aut_accept s k (reglan_loop (reglan_to_re (SmtStr [c])) i n)` >>
  simp [smtstringTheory.smtstr_len_def,
        integerTheory.INT_OF_NUM_LE] >>
  drule aut_accept_transition >>
  simp [aut_accept_loop_deriv]
QED

Theorem aut_accept_loop_nullable_transition:
  c <= 196607 ==>
  (~aut_accept s k
      (reglan_loop
        (reglan_union (reglan_to_re (SmtStr [c])) (reglan_to_re (SmtStr [])))
        i n) \/
   smtstr_len s <= &k \/
   (i <= n /\ n <> 0 /\ seq_nth_i s k = c /\
    aut_accept s (SUC k)
      (reglan_loop
        (reglan_union (reglan_to_re (SmtStr [c])) (reglan_to_re (SmtStr [])))
        0 (n - 1))))
Proof
  strip_tac >>
  Cases_on
    `aut_accept s k
       (reglan_loop
         (reglan_union (reglan_to_re (SmtStr [c])) (reglan_to_re (SmtStr [])))
         i n)` >>
  simp [smtstringTheory.smtstr_len_def,
        integerTheory.INT_OF_NUM_LE] >>
  drule aut_accept_transition >>
  simp [aut_accept_loop_nullable_deriv]
QED

Theorem aut_accept_empty_terminal_int:
  ~aut_accept s k (reglan_to_re (SmtStr [])) \/
  smtstr_len s <= &k \/ F
Proof
  simp [aut_accept_empty, smtstringTheory.smtstr_len_def,
        integerTheory.INT_OF_NUM_LE]
QED

(* The complement and intersection steps read the transition character out of
   the string itself, so its code-point bound comes for free; only the
   endpoints written into the regex need one. *)

Theorem aut_accept_comp_transition:
  ~aut_accept s k (reglan_comp (reglan_to_re (SmtStr [c]))) \/
  smtstr_len s <= &k \/
  (seq_nth_i s k <> c \/
   aut_accept s (SUC k) (reglan_plus reglan_allchar))
Proof
  Cases_on `LENGTH (smtstr_rep s) <= k`
  >- simp [smtstringTheory.smtstr_len_def,
           integerTheory.INT_OF_NUM_LE]
  >> `k < LENGTH (smtstr_rep s)` by decide_tac >>
  `seq_nth_i s k = EL k (smtstr_rep s)` by
    simp [seq_nth_i_def] >>
  `DROP k (smtstr_rep s) =
     EL k (smtstr_rep s)::DROP (SUC k) (smtstr_rep s)` by
    simp [rich_listTheory.DROP_CONS_EL] >>
  `EVERY (\c. c <= 196607) (DROP k (smtstr_rep s))` by
    (irule rich_listTheory.EVERY_DROP >> simp []) >>
  rfs [] >>
  simp [aut_accept_lang, aut_accept_plus_allchar,
        smtstringTheory.re_lang_def,
        smtstringTheory.smtstr_rep_def] >>
  metis_tac []
QED

Theorem aut_accept_comp_range_transition:
  lo <= 196607 /\ hi <= 196607 ==>
  (~aut_accept s k
      (reglan_comp (reglan_range (SmtStr [lo]) (SmtStr [hi]))) \/
   smtstr_len s <= &k \/
   (seq_nth_i s k < lo \/ hi < seq_nth_i s k \/
    aut_accept s (SUC k) (reglan_plus reglan_allchar)))
Proof
  strip_tac >>
  Cases_on `LENGTH (smtstr_rep s) <= k`
  >- simp [smtstringTheory.smtstr_len_def,
           integerTheory.INT_OF_NUM_LE]
  >> `k < LENGTH (smtstr_rep s)` by decide_tac >>
  `seq_nth_i s k = EL k (smtstr_rep s)` by
    simp [seq_nth_i_def] >>
  `DROP k (smtstr_rep s) =
     EL k (smtstr_rep s)::DROP (SUC k) (smtstr_rep s)` by
    simp [rich_listTheory.DROP_CONS_EL] >>
  `EVERY (\c. c <= 196607) (DROP k (smtstr_rep s))` by
    (irule rich_listTheory.EVERY_DROP >> simp []) >>
  rfs [] >>
  simp [aut_accept_lang, aut_accept_plus_allchar,
        smtstringTheory.re_lang_def,
        smtstringTheory.smtstr_rep_def,
        smtstringTheory.smtstr_len_def,
        integerTheory.INT_OF_NUM_LE] >>
  decide_tac
QED

Theorem aut_accept_inter_range_comp_transition:
  lo <= 196607 /\ hi <= 196607 /\ m <= 196607 ==>
  (~aut_accept s k
      (reglan_inter
        (reglan_range (SmtStr [lo]) (SmtStr [hi]))
        (reglan_comp (reglan_to_re (SmtStr [m])))) \/
   smtstr_len s <= &k \/
   (lo <= seq_nth_i s k /\ seq_nth_i s k <= hi /\
    seq_nth_i s k <> m /\
    aut_accept s (SUC k) (reglan_to_re (SmtStr []))))
Proof
  strip_tac >>
  Cases_on `LENGTH (smtstr_rep s) <= k`
  >- simp [smtstringTheory.smtstr_len_def,
           integerTheory.INT_OF_NUM_LE]
  >> `k < LENGTH (smtstr_rep s)` by decide_tac >>
  `seq_nth_i s k = EL k (smtstr_rep s)` by
    simp [seq_nth_i_def] >>
  `DROP k (smtstr_rep s) =
     EL k (smtstr_rep s)::DROP (SUC k) (smtstr_rep s)` by
    simp [rich_listTheory.DROP_CONS_EL] >>
  `EVERY (\c. c <= 196607) (DROP k (smtstr_rep s))` by
    (irule rich_listTheory.EVERY_DROP >> simp []) >>
  rfs [] >>
  simp [aut_accept_lang, aut_accept_empty,
        smtstringTheory.re_lang_def,
        smtstringTheory.smtstr_rep_def] >>
  metis_tac []
QED

(* Instances for the endpoints, bounds and states the recorded Z3 corpus
   uses.  Each is a specialisation of a general lemma above.  They are kept
   because a proof step at state 0 mentions the literal 1, which no 'SUC k'
   pattern matches. *)

Theorem aut_accept_comp_singleton_transition:
  ~aut_accept s 0 (reglan_comp (reglan_to_re (SmtStr [c]))) \/
  smtstr_len s <= 0 \/
  (seq_nth_i s 0 <> c \/
   aut_accept s 1 (reglan_plus reglan_allchar))
Proof
  mp_tac (Q.INST [`k` |-> `0`] aut_accept_comp_transition) >>
  simp []
QED

Theorem aut_accept_comp_range_transition_zero:
  lo <= 196607 /\ hi <= 196607 ==>
  (~aut_accept s 0
      (reglan_comp (reglan_range (SmtStr [lo]) (SmtStr [hi]))) \/
   smtstr_len s <= 0 \/
   (seq_nth_i s 0 < lo \/ hi < seq_nth_i s 0 \/
    aut_accept s 1 (reglan_plus reglan_allchar)))
Proof
  mp_tac (Q.INST [`k` |-> `0`] aut_accept_comp_range_transition) >>
  simp []
QED

Theorem aut_accept_inter_range_comp_transition_zero:
  ~aut_accept s 0
      (reglan_inter
        (reglan_range (SmtStr [97]) (SmtStr [122]))
        (reglan_comp (reglan_to_re (SmtStr [109])))) \/
  smtstr_len s <= 0 \/
  (97 <= seq_nth_i s 0 /\ seq_nth_i s 0 <= 122 /\
   seq_nth_i s 0 <> 109 /\
   aut_accept s 1 (reglan_to_re (SmtStr [])))
Proof
  mp_tac
    (Q.INST [`lo` |-> `97`, `hi` |-> `122`, `m` |-> `109`, `k` |-> `0`]
       aut_accept_inter_range_comp_transition) >>
  simp []
QED

Theorem aut_accept_range_transition_zero:
  ~aut_accept s 0 (reglan_range (SmtStr [97]) (SmtStr [122])) \/
  smtstr_len s <= 0 \/
  (seq_nth_i s 0 <= 122 /\ 97 <= seq_nth_i s 0 /\
   aut_accept s 1 (reglan_to_re (SmtStr [])))
Proof
  mp_tac
    (Q.INST [`lo` |-> `97`, `hi` |-> `122`, `k` |-> `0`]
       aut_accept_range_transition) >>
  simp []
QED

Theorem aut_accept_loop_transition_zero:
  c <= 196607 ==>
  (~aut_accept s 0
      (reglan_loop (reglan_to_re (SmtStr [c])) 1 3) \/
   smtstr_len s <= 0 \/
   (seq_nth_i s 0 = c /\
    aut_accept s 1
      (reglan_loop (reglan_to_re (SmtStr [c])) 0 2)))
Proof
  mp_tac
    (Q.INST [`i` |-> `1`, `n` |-> `3`, `k` |-> `0`]
       aut_accept_loop_transition) >>
  simp []
QED

Theorem aut_accept_loop_transition_one:
  c <= 196607 ==>
  (~aut_accept s 1
      (reglan_loop (reglan_to_re (SmtStr [c])) 0 2) \/
   smtstr_len s <= 1 \/
   (seq_nth_i s 1 = c /\
    aut_accept s 2
      (reglan_loop (reglan_to_re (SmtStr [c])) 0 1)))
Proof
  mp_tac
    (Q.INST [`i` |-> `0`, `n` |-> `2`, `k` |-> `1`]
       aut_accept_loop_transition) >>
  simp []
QED

Theorem aut_accept_loop_transition_two:
  c <= 196607 ==>
  (~aut_accept s 2
      (reglan_loop (reglan_to_re (SmtStr [c])) 0 1) \/
   smtstr_len s <= 2 \/
   (seq_nth_i s 2 = c /\
    aut_accept s 3 (reglan_to_re (SmtStr []))))
Proof
  mp_tac
    (Q.INST [`i` |-> `0`, `n` |-> `1`, `k` |-> `2`]
       aut_accept_loop_transition) >>
  simp [aut_accept_loop_empty]
QED

Theorem aut_accept_loop_nullable_transition_zero:
  c <= 196607 ==>
  (~aut_accept s 0
      (reglan_loop
        (reglan_union (reglan_to_re (SmtStr [c])) (reglan_to_re (SmtStr [])))
        1 2) \/
   smtstr_len s <= 0 \/
   (seq_nth_i s 0 = c /\
    aut_accept s 1
      (reglan_loop
        (reglan_union (reglan_to_re (SmtStr [c])) (reglan_to_re (SmtStr [])))
        0 1)))
Proof
  mp_tac
    (Q.INST [`i` |-> `1`, `n` |-> `2`, `k` |-> `0`]
       aut_accept_loop_nullable_transition) >>
  simp []
QED

Theorem aut_accept_loop_nullable_transition_one:
  c <= 196607 ==>
  (~aut_accept s 1
      (reglan_loop
        (reglan_union (reglan_to_re (SmtStr [c])) (reglan_to_re (SmtStr [])))
        0 1) \/
   smtstr_len s <= 1 \/
   (seq_nth_i s 1 = c /\
    aut_accept s 2 (reglan_to_re (SmtStr []))))
Proof
  mp_tac
    (Q.INST [`i` |-> `0`, `n` |-> `1`, `k` |-> `1`]
       aut_accept_loop_nullable_transition) >>
  simp [aut_accept_loop_empty]
QED

(* The same instances in Z3's 'seq.unit' spelling. *)

Theorem aut_accept_range_transition_seq_unit:
  ~aut_accept s 0
      (reglan_range (seq_unit 97) (seq_unit 122)) \/
  smtstr_len s <= 0 \/
  (seq_nth_i s 0 <= 122 /\ 97 <= seq_nth_i s 0 /\
   aut_accept s 1 (reglan_to_re (SmtStr [])))
Proof
  PURE_REWRITE_TAC [seq_unit_def] >>
  ACCEPT_TAC aut_accept_range_transition_zero
QED

Theorem aut_accept_loop_transition_seq_unit_zero:
  c <= 196607 ==>
  (~aut_accept s 0
      (reglan_loop (reglan_to_re (seq_unit c)) 1 3) \/
   smtstr_len s <= 0 \/
   (seq_nth_i s 0 = c /\
    aut_accept s 1
      (reglan_loop (reglan_to_re (seq_unit c)) 0 2)))
Proof
  PURE_REWRITE_TAC [seq_unit_def] >>
  ACCEPT_TAC aut_accept_loop_transition_zero
QED

Theorem aut_accept_loop_transition_seq_unit_one:
  c <= 196607 ==>
  (~aut_accept s 1
      (reglan_loop (reglan_to_re (seq_unit c)) 0 2) \/
   smtstr_len s <= 1 \/
   (seq_nth_i s 1 = c /\
    aut_accept s 2
      (reglan_loop (reglan_to_re (seq_unit c)) 0 1)))
Proof
  PURE_REWRITE_TAC [seq_unit_def] >>
  ACCEPT_TAC aut_accept_loop_transition_one
QED

Theorem aut_accept_loop_transition_seq_unit_two:
  c <= 196607 ==>
  (~aut_accept s 2
      (reglan_loop (reglan_to_re (seq_unit c)) 0 1) \/
   smtstr_len s <= 2 \/
   (seq_nth_i s 2 = c /\
    aut_accept s 3 (reglan_to_re (SmtStr []))))
Proof
  PURE_REWRITE_TAC [seq_unit_def] >>
  ACCEPT_TAC aut_accept_loop_transition_two
QED

Theorem aut_accept_comp_transition_seq_unit:
  ~aut_accept s 0
      (reglan_comp (reglan_to_re (seq_unit c))) \/
  smtstr_len s <= 0 \/
  (seq_nth_i s 0 <> c \/
   aut_accept s 1 (reglan_plus reglan_allchar))
Proof
  PURE_REWRITE_TAC [seq_unit_def] >>
  ACCEPT_TAC aut_accept_comp_singleton_transition
QED

Theorem aut_accept_comp_range_transition_seq_unit:
  lo <= 196607 /\ hi <= 196607 ==>
  (~aut_accept s 0
      (reglan_comp
        (reglan_range (seq_unit lo) (seq_unit hi))) \/
   smtstr_len s <= 0 \/
   (seq_nth_i s 0 < lo \/ hi < seq_nth_i s 0 \/
    aut_accept s 1 (reglan_plus reglan_allchar)))
Proof
  PURE_REWRITE_TAC [seq_unit_def] >>
  ACCEPT_TAC aut_accept_comp_range_transition_zero
QED

Theorem aut_accept_inter_transition_seq_unit:
  ~aut_accept s 0
      (reglan_inter
        (reglan_range (seq_unit 97) (seq_unit 122))
        (reglan_comp (reglan_to_re (seq_unit 109)))) \/
  smtstr_len s <= 0 \/
  (97 <= seq_nth_i s 0 /\ seq_nth_i s 0 <= 122 /\
   seq_nth_i s 0 <> 109 /\
   aut_accept s 1 (reglan_to_re (SmtStr [])))
Proof
  PURE_REWRITE_TAC [seq_unit_def] >>
  ACCEPT_TAC aut_accept_inter_range_comp_transition_zero
QED

Theorem aut_accept_loop_nullable_transition_seq_unit_zero:
  c <= 196607 ==>
  (~aut_accept s 0
      (reglan_loop
        (reglan_union
          (reglan_to_re (seq_unit c)) (reglan_to_re (SmtStr [])))
        1 2) \/
   smtstr_len s <= 0 \/
   (seq_nth_i s 0 = c /\
    aut_accept s 1
      (reglan_loop
        (reglan_union
          (reglan_to_re (seq_unit c)) (reglan_to_re (SmtStr [])))
        0 1)))
Proof
  PURE_REWRITE_TAC [seq_unit_def] >>
  ACCEPT_TAC aut_accept_loop_nullable_transition_zero
QED

Theorem aut_accept_loop_nullable_transition_seq_unit_one:
  c <= 196607 ==>
  (~aut_accept s 1
      (reglan_loop
        (reglan_union
          (reglan_to_re (seq_unit c)) (reglan_to_re (SmtStr [])))
        0 1) \/
   smtstr_len s <= 1 \/
   (seq_nth_i s 1 = c /\
    aut_accept s 2 (reglan_to_re (SmtStr []))))
Proof
  PURE_REWRITE_TAC [seq_unit_def] >>
  ACCEPT_TAC aut_accept_loop_nullable_transition_one
QED

(* TASK_02 draft_substr and draft_re_comp record the length, at/nth_i,
   and head/tail decomposition clauses below. *)

(* 'seq_unit c' is a one-character string only for a real code point: out of
   range 'SmtStr [c]' is an unconstrained element of ':smtstr'. *)
Theorem seq_unit_length:
  c <= 196607 ==> smtstr_len (seq_unit c) = 1
Proof
  simp [seq_unit_def, smtstringTheory.smtstr_len_def,
        smtstringTheory.smtstr_rep_def]
QED

Theorem seq_split_at:
  i < LENGTH (smtstr_rep s) ==>
    s =
      smtstr_concat (SmtStr (TAKE i (smtstr_rep s)))
        (smtstr_concat
          (seq_unit (seq_nth_i s i)) (seq_tail s i))
Proof
  strip_tac >>
  `EL i (smtstr_rep s) <= 196607` by
    (`EVERY (\c. c <= 196607) (DROP i (smtstr_rep s))` by
       (irule rich_listTheory.EVERY_DROP >> simp []) >>
     rfs [rich_listTheory.DROP_CONS_EL]) >>
  `EVERY (\c. c <= 196607) (TAKE i (smtstr_rep s))` by
    (irule rich_listTheory.EVERY_TAKE >> simp []) >>
  `EVERY (\c. c <= 196607) (DROP (SUC i) (smtstr_rep s))` by
    (irule rich_listTheory.EVERY_DROP >> simp []) >>
  `seq_nth_i s i = EL i (smtstr_rep s)` by
    simp [seq_nth_i_def] >>
  `TAKE i (smtstr_rep s) ++
     EL i (smtstr_rep s)::DROP (SUC i) (smtstr_rep s) =
   smtstr_rep s` by
    (`TAKE i (smtstr_rep s) ++ [EL i (smtstr_rep s)] ++
        DROP (SUC i) (smtstr_rep s) = smtstr_rep s` by
       simp [rich_listTheory.TAKE_DROP_SUC] >>
     fs []) >>
  simp [seq_unit_def, seq_tail_def,
        smtstringTheory.smtstr_concat_def,
        smtstringTheory.smtstr_rep_def]
QED

Theorem seq_head_tail:
  s = SmtStr [] \/
  seq_eq s
    (smtstr_concat (seq_unit (seq_nth_i s 0)) (seq_tail s 0))
Proof
  Cases_on `s = SmtStr []`
  >- simp []
  >> disj2_tac >>
  `smtstr_rep s <> []` by
    metis_tac [smtstringTheory.smtstr_rep_eq_nil] >>
  `0 < LENGTH (smtstr_rep s)` by
    (Cases_on `smtstr_rep s` >> fs []) >>
  drule seq_split_at >>
  simp [seq_eq_def, smtstringTheory.smtstr_concat_nil_left]
QED

(* TASK_02 draft_regex_membership, draft_substr, and draft_re_comp all emit
   this integer-length form of the head/tail alternative. *)

Theorem seq_head_tail_int:
  smtstr_len s = 0 \/
  seq_eq s
    (smtstr_concat (seq_unit (seq_nth_i s 0)) (seq_tail s 0))
Proof
  simp [smtstringTheory.smtstr_len_eq_zero] >>
  ACCEPT_TAC seq_head_tail
QED

Theorem seq_head_tail_int_zero_left:
  0 = smtstr_len s \/
  seq_eq s
    (smtstr_concat (seq_unit (seq_nth_i s 0)) (seq_tail s 0))
Proof
  metis_tac [seq_head_tail_int]
QED

(* Z3's head/tail decomposition witnesses that the string is non-empty: the
   head is a genuine character, so the representation has one. *)
Theorem seq_head_tail_nonempty[local]:
  s = smtstr_concat (seq_unit (seq_nth_i s 0)) (seq_tail s 0) ==>
  smtstr_rep s <> []
Proof
  disch_then (fn th => ONCE_REWRITE_TAC [th]) >>
  `EVERY (\c. c <= 196607) (DROP 1 (smtstr_rep s))` by
    (irule rich_listTheory.EVERY_DROP >> simp []) >>
  simp [seq_unit_def, seq_tail_def,
        smtstringTheory.smtstr_concat_def,
        smtstringTheory.smtstr_rep_def]
QED

(* TASK_02 draft_regex_membership uses these singleton consequences of the
   prefix witnesses and concat decompositions.  A witness character written
   into the regex or into a concatenation is only pinned down by 'SmtStr' if
   it is a real code point, so those characters carry the bound; characters
   read out of the string with 'seq_nth_i' do not, because the specification
   already records that they are code points. *)

Theorem seq_prefixof_singleton:
  c <= 196607 /\
  seq_eq s
      (smtstr_concat (seq_unit (seq_nth_i s 0)) (seq_tail s 0)) /\
    smtstr_prefixof s (seq_unit c) ==>
  s = seq_unit c
Proof
  rpt strip_tac >>
  fs [seq_eq_def] >>
  `smtstr_rep s <> []` by metis_tac [seq_head_tail_nonempty] >>
  `s <> SmtStr []` by
    metis_tac [smtstringTheory.smtstr_rep_eq_nil] >>
  fs [seq_unit_def] >>
  `s = SmtStr [] \/ s = SmtStr [c]` by
    metis_tac [smtstringTheory.smtstr_prefixof_singleton] >>
  fs []
QED

Theorem seq_prefixof_head:
  c <= 196607 /\
  seq_eq s
      (smtstr_concat (seq_unit (seq_nth_i s 0)) (seq_tail s 0)) /\
    smtstr_prefixof s (seq_unit c) ==>
  c = seq_nth_i s 0
Proof
  rpt strip_tac >>
  `s = seq_unit c` by metis_tac [seq_prefixof_singleton] >>
  rw [] >>
  simp [seq_unit_def, seq_nth_i_def,
        smtstringTheory.smtstr_rep_def]
QED

Theorem seq_concat_middle_singleton:
  c <= 196607 /\ d <= 196607 /\
  seq_eq (seq_unit d)
    (smtstr_concat p (smtstr_concat (seq_unit c) q)) ==>
  c = d
Proof
  rw [seq_eq_def] >>
  metis_tac [seq_unit_def,
             smtstringTheory.smtstr_concat_middle_singleton]
QED

Theorem seq_concat_middle_singleton_result:
  c <= 196607 /\ d <= 196607 /\
  seq_eq (seq_unit d)
    (smtstr_concat p (smtstr_concat (seq_unit c) q)) ==>
  d = c
Proof
  metis_tac [seq_concat_middle_singleton]
QED

Theorem seq_concat_middle_singleton_right:
  c <= 196607 /\ d <= 196607 /\
  smtstr_concat p (smtstr_concat (seq_unit c) q) = seq_unit d ==>
  d = c
Proof
  metis_tac [seq_unit_def,
             smtstringTheory.smtstr_concat_middle_singleton]
QED

Theorem seq_concat_middle_singleton_left:
  c <= 196607 /\ d <= 196607 /\
  seq_unit d = smtstr_concat p (smtstr_concat (seq_unit c) q) ==>
  d = c
Proof
  metis_tac [seq_concat_middle_singleton_right]
QED

Theorem seq_head_shared_singleton_prefix:
  c <= 196607 /\ d <= 196607 /\ e <= 196607 /\
  s =
      smtstr_concat
        (seq_unit (seq_nth_i s 0)) (seq_tail s 0) /\
    s = smtstr_concat p (smtstr_concat (seq_unit c) q) /\
    seq_unit d = smtstr_concat p (smtstr_concat (seq_unit e) r) ==>
  seq_nth_i s 0 = c
Proof
  rpt strip_tac >>
  `smtstr_rep p ++ [e] ++ smtstr_rep r = [d]` by
    (qpat_x_assum `seq_unit d = _` mp_tac >>
     simp [seq_unit_def, smtstringTheory.smtstr_concat_def,
           smtstringTheory.smtstr_rep_def, smtstringTheory.SmtStr_11] >>
     metis_tac []) >>
  `smtstr_rep p = []` by (Cases_on `smtstr_rep p` >> fs []) >>
  `smtstr_rep s = c::smtstr_rep q` by
    (qpat_x_assum `s = smtstr_concat p _` mp_tac >>
     simp [seq_unit_def, smtstringTheory.smtstr_concat_def,
           smtstringTheory.smtstr_rep_def] >>
     rw [] >>
     simp []) >>
  simp [seq_nth_i_def]
QED

Theorem seq_head_shared_singleton_prefix_right:
  c <= 196607 /\ d <= 196607 /\ e <= 196607 ==>
  seq_eq s
      (smtstr_concat
        (seq_unit (seq_nth_i s 0)) (seq_tail s 0)) ==>
    s = smtstr_concat p (smtstr_concat (seq_unit c) q) ==>
    smtstr_concat p (smtstr_concat (seq_unit d) r) = seq_unit e ==>
  seq_nth_i s 0 = c
Proof
  rpt strip_tac >>
  `smtstr_rep p ++ [d] ++ smtstr_rep r = [e]` by
    (qpat_x_assum `smtstr_concat p _ = seq_unit e` mp_tac >>
     simp [seq_unit_def, smtstringTheory.smtstr_concat_def,
           smtstringTheory.smtstr_rep_def, smtstringTheory.SmtStr_11] >>
     metis_tac []) >>
  `smtstr_rep p = []` by (Cases_on `smtstr_rep p` >> fs []) >>
  `smtstr_rep s = c::smtstr_rep q` by
    (qpat_x_assum `s = smtstr_concat p _` mp_tac >>
     simp [seq_unit_def, smtstringTheory.smtstr_concat_def,
           smtstringTheory.smtstr_rep_def] >>
     rw [] >>
     simp []) >>
  simp [seq_nth_i_def]
QED

(* TASK_02 draft_length emits the exact two-unit reconstruction after proving
   a sequence has length two. *)

Theorem seq_length_two:
  smtstr_len s = 2 ==>
  seq_eq
    (smtstr_concat
      (seq_unit (seq_nth_i s 0)) (seq_unit (seq_nth_i s 1))) s
Proof
  simp [smtstringTheory.smtstr_len_def] >>
  strip_tac >>
  `seq_nth_i s 0 = EL 0 (smtstr_rep s)` by
    simp [seq_nth_i_def] >>
  `seq_nth_i s 1 = EL 1 (smtstr_rep s)` by
    simp [seq_nth_i_def] >>
  `EVERY (\c. c <= 196607) (smtstr_rep s)` by simp [] >>
  Cases_on `smtstr_rep s` >>
  fs [] >>
  Cases_on `t` >>
  fs [] >>
  simp [seq_eq_def, seq_unit_def,
        smtstringTheory.smtstr_concat_def,
        smtstringTheory.smtstr_rep_def] >>
  metis_tac [smtstringTheory.SmtStr_smtstr_rep]
QED

Theorem seq_two_two_concat_not_three:
  a <= 196607 /\ b <= 196607 /\ c <= 196607 /\
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
  `smtstr_len (seq_unit a) = 1 /\ smtstr_len (seq_unit b) = 1 /\
   smtstr_len (seq_unit c) = 1` by simp [seq_unit_length] >>
  fs [seq_unit_length, smtstringTheory.smtstr_len_concat] >>
  intLib.ARITH_TAC
QED

Theorem seq_tail_step:
  SUC i < LENGTH (smtstr_rep s) ==>
    seq_tail s i =
      smtstr_concat
        (seq_unit (seq_nth_i s (SUC i))) (seq_tail s (SUC i))
Proof
  strip_tac >>
  `EL (SUC i) (smtstr_rep s) <= 196607` by
    (`EVERY (\c. c <= 196607) (DROP (SUC i) (smtstr_rep s))` by
       (irule rich_listTheory.EVERY_DROP >> simp []) >>
     rfs [rich_listTheory.DROP_CONS_EL]) >>
  `EVERY (\c. c <= 196607) (DROP (SUC (SUC i)) (smtstr_rep s))` by
    (irule rich_listTheory.EVERY_DROP >> simp []) >>
  `seq_nth_i s (SUC i) = EL (SUC i) (smtstr_rep s)` by
    simp [seq_nth_i_def] >>
  `DROP (SUC i) (smtstr_rep s) =
     EL (SUC i) (smtstr_rep s)::DROP (SUC (SUC i)) (smtstr_rep s)` by
    simp [rich_listTheory.DROP_CONS_EL] >>
  simp [seq_unit_def, seq_tail_def,
        smtstringTheory.smtstr_concat_def,
        smtstringTheory.smtstr_rep_def]
QED

Theorem seq_tail_zero_step:
  s <> smtstr_at s 0 /\
    seq_eq (seq_unit (seq_nth_i s 0)) (smtstr_at s 0) /\
    seq_eq s
      (smtstr_concat (seq_unit (seq_nth_i s 0)) (seq_tail s 0)) ==>
  seq_tail s 0 =
    smtstr_concat (seq_unit (seq_nth_i s 1)) (seq_tail s 1)
Proof
  rpt strip_tac >>
  fs [seq_eq_def] >>
  `LENGTH (smtstr_rep s) <> 0` by
    (strip_tac >>
     `smtstr_rep s = []` by (Cases_on `smtstr_rep s` >> fs []) >>
     `EVERY (\c. c <= 196607) (DROP 1 (smtstr_rep s))` by
       (irule rich_listTheory.EVERY_DROP >> simp []) >>
     `smtstr_rep
        (smtstr_concat (seq_unit (seq_nth_i s 0)) (seq_tail s 0)) =
      smtstr_rep s` by (AP_TERM_TAC >> simp []) >>
     rfs [seq_unit_def, seq_tail_def,
          smtstringTheory.smtstr_concat_def,
          smtstringTheory.smtstr_rep_def]) >>
  `LENGTH (smtstr_rep s) <> 1` by
    (strip_tac >>
     qpat_x_assum `s <> smtstr_at s 0` mp_tac >>
     simp [] >>
     qpat_x_assum `seq_unit _ = smtstr_at s 0`
       (fn th => REWRITE_TAC [GSYM th]) >>
     `seq_nth_i s 0 = EL 0 (smtstr_rep s)` by
       simp [seq_nth_i_def] >>
     Cases_on `smtstr_rep s` >>
     fs [] >>
     simp [seq_unit_def] >>
     metis_tac [smtstringTheory.SmtStr_smtstr_rep]) >>
  `SUC 0 < LENGTH (smtstr_rep s)` by decide_tac >>
  drule seq_tail_step >>
  simp []
QED

Theorem seq_tail_length:
  smtstr_len (seq_tail s i) =
    &(LENGTH (smtstr_rep s) - SUC i)
Proof
  `EVERY (\c. c <= 196607) (DROP (SUC i) (smtstr_rep s))` by
    (irule rich_listTheory.EVERY_DROP >> simp []) >>
  simp [seq_tail_def, smtstringTheory.smtstr_len_def,
        smtstringTheory.smtstr_rep_def]
QED

Theorem seq_at_nth:
  i < LENGTH (smtstr_rep s) ==>
    smtstr_at s (&i) = seq_unit (seq_nth_i s i)
Proof
  simp [smtstringTheory.smtstr_at_in_range, seq_unit_def,
        seq_nth_i_def, smtstringTheory.smtstr_rep_def]
QED

Theorem seq_at_zero:
  s = SmtStr [] \/
  seq_eq (smtstr_at s 0) (seq_unit (seq_nth_i s 0))
Proof
  Cases_on `s = SmtStr []`
  >- simp []
  >> disj2_tac >>
  `smtstr_rep s <> []` by
    metis_tac [smtstringTheory.smtstr_rep_eq_nil] >>
  `0 < LENGTH (smtstr_rep s)` by
    (Cases_on `smtstr_rep s` >> fs []) >>
  drule seq_at_nth >>
  simp [seq_eq_def]
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
Triviality aut_accept_catalog_eval:
  aut_state (SmtStr [97; 98]) 0 = SmtStr [97; 98] /\
  aut_state (SmtStr [97; 98]) 1 = SmtStr [98] /\
  aut_state (SmtStr [97; 98]) 2 = SmtStr [] /\
  aut_accept (SmtStr [97]) 0
    (reglan_range (SmtStr [97]) (SmtStr [122])) /\
  aut_accept (SmtStr [97]) 1 (reglan_to_re (SmtStr [])) /\
  ~aut_accept (SmtStr [97; 98]) 1 (reglan_to_re (SmtStr [])) /\
  aut_accept (SmtStr [97; 98]) 1 reglan_allchar
Proof
  EVAL_TAC
QED

Triviality z3_internal_eval:
  seq_unit 97 = SmtStr [97] /\
  seq_tail (SmtStr [10; 20; 30]) 0 = SmtStr [20; 30] /\
  seq_tail (SmtStr [10; 20; 30]) 1 = SmtStr [30] /\
  seq_eq (SmtStr [1; 2]) (SmtStr [1; 2]) /\
  seq_nth_i (SmtStr [10; 20; 30]) 1 = 20 /\
  char_is_digit 48 /\ char_is_digit 57 /\
  ~char_is_digit 47 /\ ~char_is_digit 58 /\
  seq_digit2int 48 = 0 /\ seq_digit2int 57 = 9 /\
  seq_digit 53 = 5 /\
  seq_stoi (SmtStr [52; 50]) 0 = 4 /\
  seq_stoi (SmtStr [52; 50]) 1 = 42 /\
  char_bit 0 3 /\ char_bit 1 3 /\ ~char_bit 2 3
Proof
  simp [seq_nth_i_def, smtstringTheory.smtstr_rep_def] >>
  EVAL_TAC
QED
