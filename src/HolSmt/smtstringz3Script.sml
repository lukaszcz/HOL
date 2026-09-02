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

(* The parser introduces exactly these three representation crossings:
   Char results are packed with n2w, Char arguments are unpacked with w2n,
   and Int-sorted sequence indices cross back to num through Num.  The
   w2n/n2w direction is intentionally restricted to valid Z3 code points;
   its premise lets replay simplification fail closed for an arbitrary word
   payload while accepting literals and seq_nth_i results. *)

Theorem char_word18_w2n_n2w:
  n <= 196607 ==>
  (w2n (n2w n : 18 word) = n)
Proof
  strip_tac >>
  simp [wordsTheory.w2n_n2w, wordsTheory.dimword_def,
        arithmeticTheory.LESS_MOD]
QED

Theorem char_word18_n2w_w2n:
  n2w (w2n (c : 18 word)) = c
Proof
  simp []
QED

Theorem char_num_of_int:
  Num (&n) = n
Proof
  simp []
QED

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
  !i s. &i < smtstr_len s ==>
    s =
      smtstr_concat (SmtStr (TAKE i (smtstr_rep s)))
        (smtstr_concat
          (seq_unit (seq_nth_i s i)) (seq_tail s i))
Proof
  rpt strip_tac >>
  fs [smtstringTheory.smtstr_len_def] >>
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

(* A single position theorem replaces replay lemmas fixed at head position
   zero.  Its numeral index is specialized and reduced by SmtStringProve. *)
Theorem seq_concat_position:
  !i p c q.
    c <= 196607 /\ smtstr_len p = &i ==>
    seq_nth_i
      (smtstr_concat p (smtstr_concat (seq_unit c) q)) i = c
Proof
  rpt strip_tac >>
  fs [smtstringTheory.smtstr_len_def] >>
  simp [seq_nth_i_def, seq_unit_def,
        smtstringTheory.smtstr_concat_def,
        smtstringTheory.smtstr_rep_def,
        rich_listTheory.EL_APPEND2]
QED

(* A singleton result forces every prefix before its displayed middle
   character to be empty.  This structural fact has no fixed position; the
   replay prover combines it with seq_concat_position specialized at the
   position present in the certificate. *)
Theorem concat_singleton_prefix_length:
  !p c q d.
    c <= 196607 /\ d <= 196607 /\
    SmtStr [d] = smtstr_concat p (smtstr_concat (SmtStr [c]) q) ==>
    smtstr_len p = 0
Proof
  rpt strip_tac >>
  `smtstr_rep p ++ [c] ++ smtstr_rep q = [d]` by
    (pop_assum mp_tac >>
     simp [smtstringTheory.smtstr_concat_def,
           smtstringTheory.smtstr_rep_def,
           smtstringTheory.SmtStr_11]) >>
  `smtstr_rep p = []` by
    (Cases_on `smtstr_rep p` >> fs []) >>
  simp [smtstringTheory.smtstr_len_def]
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
  `&0 < smtstr_len s` by
    (simp [smtstringTheory.smtstr_len_def] >>
     Cases_on `smtstr_rep s` >> fs []) >>
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

(* Equality orientation at the String-prover boundary makes one spelling per
   family sufficient.  TASK_18 replaces these remaining instances with
   replay-time specialization of parametric decomposition theorems. *)

(* Reconstruct every sequence of numeral length n from its nth_i values.
   Replay specializes n first, then EVAL expands GENLIST and REDUCE_CONV
   discharges concrete numeral side conditions before bounded search. *)
Theorem seq_length_decompose:
  !n s.
    smtstr_len s = &(n : num) ==>
    seq_eq (SmtStr (GENLIST (seq_nth_i s) n)) s
Proof
  rpt strip_tac >>
  fs [smtstringTheory.smtstr_len_def] >>
  `GENLIST (seq_nth_i s) n = smtstr_rep s` by
    (rw [listTheory.LIST_EQ_REWRITE] >>
     simp [seq_nth_i_def]) >>
  fs [seq_eq_def]
QED

(* The old position-zero certificate established tail nonemptiness indirectly:
   the sequence is its prefix, selected unit, and tail, but differs from the
   same prefix ending at smtstr_at.  This index-parametric form exposes the
   resulting guard needed by seq_tail_step. *)
Theorem seq_tail_step_guard:
  !i s.
    s <>
      smtstr_concat (SmtStr (TAKE i (smtstr_rep s)))
        (smtstr_at s (&i)) /\
    seq_eq (seq_unit (seq_nth_i s i)) (smtstr_at s (&i)) /\
    seq_eq s
      (smtstr_concat (SmtStr (TAKE i (smtstr_rep s)))
        (smtstr_concat
          (seq_unit (seq_nth_i s i)) (seq_tail s i))) ==>
    &(SUC i) < smtstr_len s
Proof
  rpt strip_tac >>
  fs [seq_eq_def] >>
  `i < LENGTH (smtstr_rep s)` by
    (qpat_x_assum `seq_unit _ = smtstr_at _ _`
       (fn th => mp_tac (AP_TERM ``smtstr_len`` th)) >>
     simp [seq_unit_length, smtstringTheory.smtstr_len_at] >>
     Cases_on `LENGTH (smtstr_rep s) <= i` >> fs []) >>
  `SUC i < LENGTH (smtstr_rep s)` by
    (spose_not_then assume_tac >>
     `LENGTH (smtstr_rep s) = SUC i` by decide_tac >>
     `seq_tail s i = SmtStr []` by
       (qpat_x_assum `LENGTH (smtstr_rep s) = SUC i`
          (fn th => simp [seq_tail_def, GSYM th])) >>
     fs [smtstringTheory.smtstr_concat_nil_right] >>
     qpat_x_assum `seq_unit _ = smtstr_at _ _`
       (fn th => fs [th])) >>
  simp [smtstringTheory.smtstr_len_def]
QED

Theorem seq_tail_step:
  !i s. &(SUC i) < smtstr_len s ==>
    seq_tail s i =
      smtstr_concat
        (seq_unit (seq_nth_i s (SUC i))) (seq_tail s (SUC i))
Proof
  rpt strip_tac >>
  fs [smtstringTheory.smtstr_len_def] >>
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

Theorem seq_tail_length:
  smtstr_len (seq_tail s i) =
    &(LENGTH (smtstr_rep s) - SUC i)
Proof
  `EVERY (\c. c <= 196607) (DROP (SUC i) (smtstr_rep s))` by
    (irule rich_listTheory.EVERY_DROP >> simp []) >>
  simp [seq_tail_def, smtstringTheory.smtstr_len_def,
        smtstringTheory.smtstr_rep_def]
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
