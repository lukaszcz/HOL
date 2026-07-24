(* Copyright (c) 2026 The HOL4 contributors. *)

(* SMT-LIB Unicode strings represented as lists of Unicode code points. *)
Theory smtstring
Ancestors[qualified]
  integer rich_list

Definition wfstr_def:
  wfstr (s : num list) <=> EVERY (\c. c <= 196607) s
End

Definition smtstr_concat_def:
  smtstr_concat (s : num list) t = s ++ t
End

Definition smtstr_len_def:
  smtstr_len (s : num list) = LENGTH s
End

Definition smtstr_substr_def:
  smtstr_substr (s : num list) (i : int) (n : int) =
    if i < 0 \/ n <= 0 \/ LENGTH s <= Num i then []
    else TAKE (Num n) (DROP (Num i) s)
End

Definition smtstr_at_def:
  smtstr_at (s : num list) (i : int) = smtstr_substr s i 1
End

Definition smtstr_prefixof_def:
  smtstr_prefixof (s : num list) t <=> IS_PREFIX t s
End

Definition smtstr_suffixof_def:
  smtstr_suffixof (s : num list) t <=> IS_SUFFIX t s
End

Definition smtstr_contains_def:
  smtstr_contains (s : num list) t <=> IS_SUBLIST s t
End

Definition smtstr_indexof_aux_def:
  (smtstr_indexof_aux t n [] =
     if t = [] then SOME n else NONE) /\
  (smtstr_indexof_aux t n (h::s) =
     if IS_PREFIX (h::s) t then SOME n
     else smtstr_indexof_aux t (SUC n) s)
End

Definition smtstr_indexof_def:
  smtstr_indexof (s : num list) t (i : int) =
    if i < 0 \/ LENGTH s < Num i then -1
    else
      case smtstr_indexof_aux t (Num i) (DROP (Num i) s) of
        NONE => -1
      | SOME n => &n
End

Definition smtstr_lt_def:
  smtstr_lt (s : num list) t <=> LLEX $< s t
End

Definition smtstr_le_def:
  smtstr_le (s : num list) t <=> smtstr_lt s t \/ s = t
End

Definition smtstr_char_def:
  smtstr_char (c : num) = [c]
End

(* SMT-LIB regular languages over Unicode code points. *)

Datatype:
  reglan
    = reglan_none
    | reglan_all
    | reglan_allchar
    | reglan_to_re (num list)
    | reglan_range (num list) (num list)
    | reglan_concat reglan reglan
    | reglan_union reglan reglan
    | reglan_inter reglan reglan
    | reglan_diff reglan reglan
    | reglan_comp reglan
    | reglan_star reglan
    | reglan_plus reglan
    | reglan_opt reglan
    | reglan_power reglan num
    | reglan_loop reglan num num
End

Definition reglan_dot_def:
  reglan_dot (p : num list -> bool) q s <=>
    ?u v. p u /\ q v /\ s = u ++ v
End

Definition reglan_kstar_def:
  reglan_kstar (p : num list -> bool) s <=>
    ?ss. EVERY (\u. p u /\ u <> []) ss /\ s = FLAT ss
End

Definition reglan_repeat_def:
  reglan_repeat (p : num list -> bool) n s <=>
    ?ss. LENGTH ss = n /\ EVERY p ss /\ s = FLAT ss
End

Definition reglan_loop_lang_def:
  (reglan_loop_lang (p : num list -> bool) i 0 s <=>
     if i = 0 then reglan_repeat p 0 s else F) /\
  (reglan_loop_lang p i (SUC n) s <=>
     (i <= SUC n /\ reglan_repeat p (SUC n) s) \/
     reglan_loop_lang p i n s)
End

Definition smt_in_re_def:
  (smt_in_re s reglan_none <=> F) /\
  (smt_in_re s reglan_all <=> wfstr s) /\
  (smt_in_re s reglan_allchar <=>
     ?c. c <= 196607 /\ s = [c]) /\
  (smt_in_re s (reglan_to_re t) <=> s = t) /\
  (smt_in_re s (reglan_range lo hi) <=>
     ?a b c.
       lo = [a] /\ hi = [b] /\ a <= c /\ c <= b /\
       c <= 196607 /\ s = [c]) /\
  (smt_in_re s (reglan_concat r1 r2) <=>
     reglan_dot (\u. smt_in_re u r1) (\v. smt_in_re v r2) s) /\
  (smt_in_re s (reglan_union r1 r2) <=>
     smt_in_re s r1 \/ smt_in_re s r2) /\
  (smt_in_re s (reglan_inter r1 r2) <=>
     smt_in_re s r1 /\ smt_in_re s r2) /\
  (smt_in_re s (reglan_diff r1 r2) <=>
     smt_in_re s r1 /\ ~smt_in_re s r2) /\
  (smt_in_re s (reglan_comp r) <=>
     wfstr s /\ ~smt_in_re s r) /\
  (smt_in_re s (reglan_star r) <=>
     reglan_kstar (\u. smt_in_re u r) s) /\
  (smt_in_re s (reglan_plus r) <=>
     reglan_dot
       (\u. smt_in_re u r)
       (reglan_kstar (\u. smt_in_re u r)) s) /\
  (smt_in_re s (reglan_opt r) <=> s = [] \/ smt_in_re s r) /\
  (smt_in_re s (reglan_power r n) <=>
     reglan_repeat (\u. smt_in_re u r) n s) /\
  (smt_in_re s (reglan_loop r i n) <=>
     reglan_loop_lang (\u. smt_in_re u r) i n s)
End

Definition re_nullable_def:
  (re_nullable reglan_none = F) /\
  (re_nullable reglan_all = T) /\
  (re_nullable reglan_allchar = F) /\
  (re_nullable (reglan_to_re s) <=> s = []) /\
  (re_nullable (reglan_range lo hi) = F) /\
  (re_nullable (reglan_concat r1 r2) <=>
     re_nullable r1 /\ re_nullable r2) /\
  (re_nullable (reglan_union r1 r2) <=>
     re_nullable r1 \/ re_nullable r2) /\
  (re_nullable (reglan_inter r1 r2) <=>
     re_nullable r1 /\ re_nullable r2) /\
  (re_nullable (reglan_diff r1 r2) <=>
     re_nullable r1 /\ ~re_nullable r2) /\
  (re_nullable (reglan_comp r) <=> ~re_nullable r) /\
  (re_nullable (reglan_star r) = T) /\
  (re_nullable (reglan_plus r) <=> re_nullable r) /\
  (re_nullable (reglan_opt r) = T) /\
  (re_nullable (reglan_power r n) <=> n = 0 \/ re_nullable r) /\
  (re_nullable (reglan_loop r i n) <=>
     i <= n /\ (i = 0 \/ re_nullable r))
End

Definition reglan_power_deriv_def:
  (reglan_power_deriv dr nullable r 0 = reglan_none) /\
  (reglan_power_deriv dr nullable r (SUC n) =
     let head = reglan_concat dr (reglan_power r n)
     in
       if nullable then
         reglan_union head (reglan_power_deriv dr nullable r n)
       else head)
End

Definition reglan_loop_deriv_def:
  (reglan_loop_deriv dr nullable r i 0 = reglan_none) /\
  (reglan_loop_deriv dr nullable r i (SUC n) =
     if i <= SUC n then
       reglan_union
         (reglan_power_deriv dr nullable r (SUC n))
         (reglan_loop_deriv dr nullable r i n)
     else reglan_none)
End

Definition re_deriv_def:
  (re_deriv c reglan_none = reglan_none) /\
  (re_deriv c reglan_all =
     if c <= 196607 then reglan_all else reglan_none) /\
  (re_deriv c reglan_allchar =
     if c <= 196607 then reglan_to_re [] else reglan_none) /\
  (re_deriv c (reglan_to_re s) =
     case s of
       [] => reglan_none
     | h::t => if c = h then reglan_to_re t else reglan_none) /\
  (re_deriv c (reglan_range lo hi) =
     case lo of
       [a] =>
         (case hi of
            [b] =>
              if a <= c /\ c <= b /\ c <= 196607 then
                reglan_to_re []
              else reglan_none
          | _ => reglan_none)
     | _ => reglan_none) /\
  (re_deriv c (reglan_concat r1 r2) =
     let head = reglan_concat (re_deriv c r1) r2
     in
       if re_nullable r1 then
         reglan_union head (re_deriv c r2)
       else head) /\
  (re_deriv c (reglan_union r1 r2) =
     reglan_union (re_deriv c r1) (re_deriv c r2)) /\
  (re_deriv c (reglan_inter r1 r2) =
     reglan_inter (re_deriv c r1) (re_deriv c r2)) /\
  (re_deriv c (reglan_diff r1 r2) =
     reglan_diff (re_deriv c r1) (re_deriv c r2)) /\
  (re_deriv c (reglan_comp r) =
     if c <= 196607 then reglan_comp (re_deriv c r)
     else reglan_none) /\
  (re_deriv c (reglan_star r) =
     reglan_concat (re_deriv c r) (reglan_star r)) /\
  (re_deriv c (reglan_plus r) =
     reglan_concat (re_deriv c r) (reglan_star r)) /\
  (re_deriv c (reglan_opt r) = re_deriv c r) /\
  (re_deriv c (reglan_power r n) =
     reglan_power_deriv (re_deriv c r) (re_nullable r) r n) /\
  (re_deriv c (reglan_loop r i n) =
     reglan_loop_deriv (re_deriv c r) (re_nullable r) r i n)
End

val _ = computeLib.add_funs
  [re_nullable_def, reglan_power_deriv_def,
   reglan_loop_deriv_def, re_deriv_def];

(* Evaluation-ready characterizations for the persistent compute set. *)

Theorem wfstr_compute[compute]:
  (wfstr [] <=> T) /\
  (wfstr (c::s) <=> c <= 196607 /\ wfstr s)
Proof
  simp [wfstr_def]
QED

Theorem smtstr_concat_compute[compute]:
  (smtstr_concat [] t = t) /\
  (smtstr_concat (h::s) t = h::smtstr_concat s t)
Proof
  simp [smtstr_concat_def]
QED

Theorem smtstr_len_compute[compute]:
  (smtstr_len [] = 0) /\
  (smtstr_len (h::s) = SUC (smtstr_len s))
Proof
  simp [smtstr_len_def]
QED

Theorem smtstr_substr_compute[compute]:
  smtstr_substr s i n =
    if i < 0 \/ n <= 0 \/ LENGTH s <= Num i then []
    else TAKE (Num n) (DROP (Num i) s)
Proof
  simp [smtstr_substr_def]
QED

Theorem smtstr_at_compute[compute]:
  smtstr_at s i = smtstr_substr s i 1
Proof
  simp [smtstr_at_def]
QED

Theorem smtstr_prefixof_compute[compute]:
  smtstr_prefixof s t <=> IS_PREFIX t s
Proof
  simp [smtstr_prefixof_def]
QED

Theorem smtstr_suffixof_compute[compute]:
  smtstr_suffixof s t <=> IS_SUFFIX t s
Proof
  simp [smtstr_suffixof_def]
QED

Theorem smtstr_contains_compute[compute]:
  smtstr_contains s t <=> IS_SUBLIST s t
Proof
  simp [smtstr_contains_def]
QED

Theorem smtstr_indexof_aux_compute[compute]:
  (smtstr_indexof_aux t n [] =
     if t = [] then SOME n else NONE) /\
  (smtstr_indexof_aux t n (h::s) =
     if IS_PREFIX (h::s) t then SOME n
     else smtstr_indexof_aux t (SUC n) s)
Proof
  simp [smtstr_indexof_aux_def]
QED

Theorem smtstr_indexof_compute[compute]:
  smtstr_indexof s t i =
    if i < 0 \/ LENGTH s < Num i then -1
    else
      case smtstr_indexof_aux t (Num i) (DROP (Num i) s) of
        NONE => -1
      | SOME n => &n
Proof
  simp [smtstr_indexof_def]
QED

Theorem smtstr_lt_compute[compute]:
  (~smtstr_lt [] []) /\
  (smtstr_lt [] (h::t)) /\
  (~smtstr_lt (h::s) []) /\
  (smtstr_lt (h1::t1) (h2::t2) <=>
     h1 < h2 \/ h1 = h2 /\ smtstr_lt t1 t2)
Proof
  simp [smtstr_lt_def, listTheory.LLEX_THM]
QED

Theorem smtstr_le_compute[compute]:
  smtstr_le s t <=> smtstr_lt s t \/ s = t
Proof
  simp [smtstr_le_def]
QED

Theorem smtstr_char_compute[compute]:
  smtstr_char c = [c]
Proof
  simp [smtstr_char_def]
QED

(* Wellformedness algebra for every string-valued operator above. *)

Theorem wfstr_concat:
  wfstr s /\ wfstr t ==> wfstr (smtstr_concat s t)
Proof
  simp [wfstr_def, smtstr_concat_def, listTheory.EVERY_APPEND]
QED

Theorem wfstr_substr:
  wfstr s ==> wfstr (smtstr_substr s i n)
Proof
  rw [wfstr_def, smtstr_substr_def] >>
  irule rich_listTheory.EVERY_TAKE >>
  irule rich_listTheory.EVERY_DROP >>
  fs []
QED

Theorem wfstr_at:
  wfstr s ==> wfstr (smtstr_at s i)
Proof
  simp [smtstr_at_def, wfstr_substr]
QED

Theorem wfstr_char:
  c <= 196607 ==> wfstr (smtstr_char c)
Proof
  simp [wfstr_def, smtstr_char_def]
QED

(* Language-algebra facts used by the derivative proof. *)

Theorem reglan_repeat_zero:
  reglan_repeat p 0 s <=> s = []
Proof
  simp [reglan_repeat_def]
QED

Theorem reglan_repeat_suc:
  reglan_repeat p (SUC n) s <=>
    reglan_dot p (reglan_repeat p n) s
Proof
  rw [reglan_repeat_def, reglan_dot_def, EQ_IMP_THM]
  >- (Cases_on `ss` >>
      fs [] >>
      qexistsl [`h`, `FLAT t`] >>
      simp [] >>
      qexists `t` >>
      simp [])
  >- (qexists `u::ss` >>
      simp [])
QED

Theorem reglan_repeat_nil:
  reglan_repeat p n [] <=> n = 0 \/ p []
Proof
  Induct_on `n` >>
  simp [reglan_repeat_zero, reglan_repeat_suc, reglan_dot_def] >>
  metis_tac []
QED

Theorem reglan_loop_lang_too_large:
  n < i ==> ~reglan_loop_lang p i n s
Proof
  Induct_on `n` >>
  simp [reglan_loop_lang_def]
QED

Theorem reglan_loop_lang_nil:
  reglan_loop_lang p i n [] <=>
    i <= n /\ (i = 0 \/ p [])
Proof
  Induct_on `n` >>
  simp [reglan_loop_lang_def, reglan_repeat_nil] >>
  numLib.ARITH_TAC
QED

Theorem reglan_dot_cons:
  (!t. p (c::t) <=> dp t) /\
  (!t. q (c::t) <=> dq t) ==>
  (reglan_dot p q (c::s) <=>
   reglan_dot dp q s \/ p [] /\ dq s)
Proof
  rw [reglan_dot_def] >>
  metis_tac [listTheory.APPEND_EQ_CONS]
QED

Theorem reglan_dot_cons_unfold:
  reglan_dot p q (c::s) <=>
    reglan_dot (\t. p (c::t)) q s \/ p [] /\ q (c::s)
Proof
  rw [reglan_dot_def] >>
  metis_tac [listTheory.APPEND_EQ_CONS]
QED

Theorem reglan_kstar_nil:
  reglan_kstar p []
Proof
  simp [reglan_kstar_def] >>
  qexists `[]` >>
  simp []
QED

Theorem reglan_kstar_cons:
  (!t. p (c::t) <=> dp t) ==>
  (reglan_kstar p (c::s) <=>
   reglan_dot dp (reglan_kstar p) s)
Proof
  rw [reglan_kstar_def, reglan_dot_def, EQ_IMP_THM]
  >- (Cases_on `ss` >>
      fs [] >>
      Cases_on `h` >>
      fs [] >>
      metis_tac [])
  >- (qexists `(c::u)::ss` >>
      simp [])
QED

Theorem reglan_kstar_cons_unfold:
  reglan_kstar p (c::s) <=>
    reglan_dot (\t. p (c::t)) (reglan_kstar p) s
Proof
  irule reglan_kstar_cons >>
  simp []
QED

Theorem re_nullable_correct:
  re_nullable r <=> smt_in_re [] r
Proof
  Induct_on `r` >>
  simp [re_nullable_def, smt_in_re_def, wfstr_def,
        reglan_dot_def, reglan_kstar_nil, reglan_repeat_nil,
        reglan_loop_lang_nil] >>
  metis_tac []
QED

Theorem reglan_power_deriv_correct:
  (!t. smt_in_re t dr <=> smt_in_re (c::t) r) /\
  (nullable <=> smt_in_re [] r) ==>
  (smt_in_re s (reglan_power_deriv dr nullable r n) <=>
   reglan_repeat (\u. smt_in_re u r) n (c::s))
Proof
  strip_tac >>
  qid_spec_tac `s` >>
  Induct_on `n`
  >- simp [reglan_power_deriv_def, smt_in_re_def,
           reglan_repeat_zero]
  >> rpt strip_tac >>
  Cases_on `nullable` >>
  fs [reglan_power_deriv_def, smt_in_re_def,
      reglan_repeat_suc, reglan_dot_cons_unfold] >>
  metis_tac []
QED

Theorem reglan_loop_deriv_correct:
  (!t. smt_in_re t dr <=> smt_in_re (c::t) r) /\
  (nullable <=> smt_in_re [] r) ==>
  (smt_in_re s (reglan_loop_deriv dr nullable r i n) <=>
   reglan_loop_lang (\u. smt_in_re u r) i n (c::s))
Proof
  strip_tac >>
  fs [] >>
  qid_spec_tac `s` >>
  Induct_on `n`
  >- simp [reglan_loop_deriv_def, smt_in_re_def,
           reglan_loop_lang_def, reglan_repeat_zero]
  >> rpt strip_tac >>
  Cases_on `i <= SUC n`
  >- (`smt_in_re s
         (reglan_power_deriv dr (smt_in_re [] r) r (SUC n)) <=>
       reglan_repeat (\u. smt_in_re u r) (SUC n) (c::s)` by
        (irule reglan_power_deriv_correct >>
         simp []) >>
      simp [reglan_loop_deriv_def, smt_in_re_def,
            reglan_loop_lang_def])
  >- (`n < i` by fs [] >>
      simp [reglan_loop_deriv_def, smt_in_re_def,
            reglan_loop_lang_def, reglan_loop_lang_too_large])
QED

Theorem re_deriv_correct:
  smt_in_re (c::s) r <=> smt_in_re s (re_deriv c r)
Proof
  qid_spec_tac `s` >>
  Induct_on `r` >>
  rpt strip_tac
  >- simp [re_deriv_def, smt_in_re_def]
  >- (Cases_on `c <= 196607` >>
      simp [re_deriv_def, smt_in_re_def, wfstr_def])
  >- (Cases_on `c <= 196607` >>
      simp [re_deriv_def, smt_in_re_def] >>
      metis_tac [])
  >- (Cases_on `l` >>
      simp [re_deriv_def, smt_in_re_def] >>
      Cases_on `c = h` >>
      simp [smt_in_re_def])
  >- (Cases_on `l` >>
      simp [re_deriv_def, smt_in_re_def] >>
      Cases_on `t` >>
      simp [smt_in_re_def] >>
      Cases_on `l0` >>
      simp [smt_in_re_def] >>
      Cases_on `t` >>
      simp [smt_in_re_def] >>
      Cases_on `h <= c /\ c <= h' /\ c <= 196607` >>
      simp [smt_in_re_def])
  >- (simp [re_deriv_def, smt_in_re_def,
            re_nullable_correct, reglan_dot_cons_unfold] >>
      Cases_on `smt_in_re [] r` >>
      simp [smt_in_re_def])
  >- simp [re_deriv_def, smt_in_re_def]
  >- simp [re_deriv_def, smt_in_re_def]
  >- simp [re_deriv_def, smt_in_re_def]
  >- (Cases_on `c <= 196607` >>
      simp [re_deriv_def, smt_in_re_def, wfstr_def])
  >- simp [re_deriv_def, smt_in_re_def,
           reglan_kstar_cons_unfold, reglan_dot_def]
  >- (simp [re_deriv_def, smt_in_re_def,
            reglan_dot_cons_unfold,
            reglan_kstar_cons_unfold, reglan_dot_def] >>
      metis_tac [])
  >- simp [re_deriv_def, smt_in_re_def]
  >- simp [re_deriv_def, smt_in_re_def,
           re_nullable_correct, reglan_power_deriv_correct]
  >- simp [re_deriv_def, smt_in_re_def,
           re_nullable_correct, reglan_loop_deriv_correct]
QED

Theorem smt_in_re_deriv[compute]:
  smt_in_re s r <=>
    re_nullable (FOLDL (\r c. re_deriv c r) r s)
Proof
  qid_spec_tac `r` >>
  Induct_on `s` >>
  simp [re_nullable_correct, re_deriv_correct]
QED

(* Symbolic one-step rules used by the string theory prover. *)

Theorem smt_in_re_concat:
  smt_in_re s (reglan_concat r1 r2) <=>
    ?u v. smt_in_re u r1 /\ smt_in_re v r2 /\ s = u ++ v
Proof
  simp [smt_in_re_def, reglan_dot_def]
QED

Theorem smt_in_re_star_cons:
  smt_in_re (c::s) (reglan_star r) <=>
    smt_in_re s
      (reglan_concat (re_deriv c r) (reglan_star r))
Proof
  simp [re_deriv_correct, re_deriv_def]
QED

(* Ground checks pin the SMT-LIB totalization and empty-string cases. *)

Theorem smtstr_core_eval:
  smtstr_concat [1; 2] [3] = [1; 2; 3] /\
  smtstr_len [10; 20; 30] = 3 /\
  smtstr_at [10; 20] (-1) = [] /\
  smtstr_at [10; 20] 0 = [10] /\
  smtstr_at [10; 20] 2 = [] /\
  smtstr_at [] 0 = [] /\
  smtstr_substr [10; 20; 30] (-1) 2 = [] /\
  smtstr_substr [10; 20; 30] 1 0 = [] /\
  smtstr_substr [10; 20; 30] 1 (-1) = [] /\
  smtstr_substr [10; 20; 30] 3 1 = [] /\
  smtstr_substr [10; 20; 30] 1 5 = [20; 30] /\
  smtstr_prefixof [] [1; 2] /\
  smtstr_prefixof [1] [1; 2] /\
  smtstr_suffixof [] [1; 2] /\
  smtstr_suffixof [2] [1; 2] /\
  smtstr_contains [1; 2; 3] [2; 3] /\
  smtstr_contains [1; 2; 3] [] /\
  smtstr_indexof [1; 2; 1; 2] [1; 2] 1 = 2 /\
  smtstr_indexof [1; 2] [3] 0 = -1 /\
  smtstr_indexof [1; 2] [1] (-1) = -1 /\
  smtstr_indexof [1; 2] [] 2 = 2 /\
  smtstr_indexof [1; 2] [] 3 = -1 /\
  smtstr_indexof [] [] 0 = 0 /\
  smtstr_lt [1; 2] [1; 3] /\
  ~smtstr_lt [1; 2] [1; 2] /\
  smtstr_le [1; 2] [1; 2] /\
  smtstr_char 196607 = [196607] /\
  wfstr [196607] /\
  ~wfstr [196608]
Proof
  EVAL_TAC
QED

Theorem reglan_eval:
  ~smt_in_re [] reglan_none /\
  smt_in_re [1; 196607] reglan_all /\
  ~smt_in_re [196608] reglan_all /\
  smt_in_re [65] reglan_allchar /\
  ~smt_in_re [65; 66] reglan_allchar /\
  smt_in_re [1; 2] (reglan_to_re [1; 2]) /\
  smt_in_re [66] (reglan_range [65] [67]) /\
  ~smt_in_re [68] (reglan_range [65] [67]) /\
  ~smt_in_re [66] (reglan_range [65; 66] [67]) /\
  smt_in_re [1; 2]
    (reglan_concat (reglan_to_re [1]) (reglan_to_re [2])) /\
  smt_in_re [2]
    (reglan_union (reglan_to_re [1]) (reglan_to_re [2])) /\
  smt_in_re [2]
    (reglan_inter
       (reglan_range [1] [3]) (reglan_range [2] [4])) /\
  smt_in_re [1]
    (reglan_diff (reglan_range [1] [3]) (reglan_to_re [2])) /\
  ~smt_in_re [2]
    (reglan_diff (reglan_range [1] [3]) (reglan_to_re [2])) /\
  smt_in_re [2] (reglan_comp (reglan_to_re [1])) /\
  ~smt_in_re [1] (reglan_comp (reglan_to_re [1])) /\
  ~smt_in_re [196608] (reglan_comp reglan_none) /\
  smt_in_re [1; 1] (reglan_star (reglan_to_re [1])) /\
  smt_in_re [] (reglan_star (reglan_to_re [1])) /\
  smt_in_re [1] (reglan_plus (reglan_to_re [1])) /\
  ~smt_in_re [] (reglan_plus (reglan_to_re [1])) /\
  smt_in_re [] (reglan_opt (reglan_to_re [1])) /\
  smt_in_re [1] (reglan_opt (reglan_to_re [1])) /\
  smt_in_re [1; 1] (reglan_power (reglan_to_re [1]) 2) /\
  ~smt_in_re [1] (reglan_power (reglan_to_re [1]) 2) /\
  smt_in_re [] (reglan_loop (reglan_to_re [1]) 0 0) /\
  ~smt_in_re [] (reglan_loop (reglan_to_re [1]) 1 0) /\
  smt_in_re [1] (reglan_loop (reglan_to_re [1]) 1 3) /\
  smt_in_re [1; 1; 1] (reglan_loop (reglan_to_re [1]) 1 3) /\
  ~smt_in_re [1; 1; 1; 1]
    (reglan_loop (reglan_to_re [1]) 1 3)
Proof
  EVAL_TAC
QED
