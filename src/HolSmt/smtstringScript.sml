(* Copyright (c) 2026 The HOL4 contributors. *)

(* SMT-LIB Unicode strings represented as lists of Unicode code points. *)
Theory smtstring
Ancestors[qualified]
  ASCIInumbers integer rich_list

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

Definition str_inj_def:
  str_inj (s : string) = MAP ORD (EXPLODE s)
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

Theorem str_inj_compute[compute]:
  (str_inj "" = []) /\
  (str_inj (STRING c s) = ORD c::str_inj s)
Proof
  simp [str_inj_def]
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

(* Injection from native HOL strings. *)

Theorem ORD_unicode_bound[local]:
  ORD c <= 196607
Proof
  `ORD c < 256` by simp [stringTheory.ORD_BOUND] >>
  decide_tac
QED

Theorem wfstr_str_inj:
  wfstr (str_inj s)
Proof
  simp [wfstr_def, str_inj_def, listTheory.EVERY_MAP,
        ORD_unicode_bound]
QED

Theorem str_inj_11[simp]:
  str_inj s = str_inj t <=> s = t
Proof
  qid_spec_tac `t` >>
  Induct_on `s` >>
  Cases_on `t` >>
  simp [str_inj_compute, stringTheory.ORD_11]
QED

Theorem str_inj_STRCAT:
  str_inj (STRCAT s t) =
    smtstr_concat (str_inj s) (str_inj t)
Proof
  simp [str_inj_def, smtstr_concat_def,
        stringTheory.IMPLODE_EXPLODE_I]
QED

Theorem str_inj_STRLEN:
  STRLEN s = LENGTH (str_inj s)
Proof
  simp [str_inj_def, stringTheory.IMPLODE_EXPLODE_I]
QED

Theorem str_inj_isPREFIX:
  isPREFIX s t <=>
    smtstr_prefixof (str_inj s) (str_inj t)
Proof
  qid_spec_tac `t` >>
  Induct_on `s` >>
  Cases_on `t` >>
  simp [str_inj_compute, smtstr_prefixof_def,
        rich_listTheory.IS_PREFIX, stringTheory.ORD_11]
QED

Theorem LLEX_MAP_ORD:
  LLEX $< (MAP ORD s) (MAP ORD t) <=>
    LLEX char_lt s t
Proof
  qid_spec_tac `t` >>
  Induct_on `s` >>
  Cases_on `t` >>
  simp [listTheory.LLEX_THM, stringTheory.char_lt_def,
        stringTheory.ORD_11]
QED

Theorem str_inj_string_lt:
  string_lt s t <=>
    smtstr_lt (str_inj s) (str_inj t)
Proof
  simp [stringTheory.string_lt_LLEX, smtstr_lt_def, str_inj_def,
        stringTheory.IMPLODE_EXPLODE_I, LLEX_MAP_ORD]
QED

Theorem str_inj_string_le:
  string_le s t <=>
    smtstr_le (str_inj s) (str_inj t)
Proof
  simp [stringTheory.string_le_def, smtstr_le_def,
        str_inj_string_lt] >>
  metis_tac []
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

(* Leftmost string and regular-language replacement. *)

Definition smtstr_replace_def:
  smtstr_replace (s : num list) t u =
    case smtstr_indexof_aux t 0 s of
      NONE => s
    | SOME n =>
        TAKE n s ++ u ++ DROP (n + LENGTH t) s
End

Definition smtstr_replace_all_aux_def:
  (smtstr_replace_all_aux 0 (s : num list) t u = s) /\
  (smtstr_replace_all_aux (SUC fuel) [] t u = []) /\
  (smtstr_replace_all_aux (SUC fuel) (h::s) t u =
     if IS_PREFIX (h::s) t then
       u ++ smtstr_replace_all_aux fuel
         (DROP (LENGTH t) (h::s)) t u
     else h::smtstr_replace_all_aux fuel s t u)
End

Definition smtstr_replace_all_def:
  smtstr_replace_all (s : num list) t u =
    if t = [] then s
    else smtstr_replace_all_aux (LENGTH s) s t u
End

Definition smtstr_shortest_re_aux_def:
  (smtstr_shortest_re_aux r s n 0 =
     if smt_in_re (TAKE n s) r then SOME n else NONE) /\
  (smtstr_shortest_re_aux r s n (SUC k) =
     if smt_in_re (TAKE n s) r then SOME n
     else smtstr_shortest_re_aux r s (SUC n) k)
End

Definition smtstr_shortest_re_def:
  smtstr_shortest_re allow_empty r (s : num list) =
    if allow_empty then
      smtstr_shortest_re_aux r s 0 (LENGTH s)
    else
      case s of
        [] => NONE
      | h::t => smtstr_shortest_re_aux r s 1 (LENGTH t)
End

Definition smtstr_find_re_aux_def:
  (smtstr_find_re_aux allow_empty r n ([] : num list) =
     case smtstr_shortest_re allow_empty r [] of
       NONE => NONE
     | SOME m => SOME (n, m)) /\
  (smtstr_find_re_aux allow_empty r n (h::s) =
     case smtstr_shortest_re allow_empty r (h::s) of
       NONE => smtstr_find_re_aux allow_empty r (SUC n) s
     | SOME m => SOME (n, m))
End

Definition smtstr_find_re_def:
  smtstr_find_re allow_empty r s =
    smtstr_find_re_aux allow_empty r 0 s
End

Definition smtstr_replace_re_def:
  smtstr_replace_re (s : num list) r u =
    case smtstr_find_re T r s of
      NONE => s
    | SOME (i, n) => TAKE i s ++ u ++ DROP (i + n) s
End

Theorem smtstr_shortest_re_aux_lower:
  smtstr_shortest_re_aux r s n k = SOME m ==> n <= m
Proof
  qid_spec_tac `n` >>
  Induct_on `k` >>
  simp [smtstr_shortest_re_aux_def] >>
  rw [] >>
  res_tac >>
  decide_tac
QED

Theorem smtstr_shortest_re_nonempty:
  smtstr_shortest_re F r s = SOME n ==> 0 < n
Proof
  Cases_on `s` >>
  simp [smtstr_shortest_re_def] >>
  strip_tac >>
  drule smtstr_shortest_re_aux_lower >>
  decide_tac
QED

Theorem smtstr_find_re_aux_nonempty:
  smtstr_find_re_aux F r i s = SOME (j, n) ==> 0 < n
Proof
  qid_spec_tac `i` >>
  Induct_on `s` >>
  rw [smtstr_find_re_aux_def] >>
  BasicProvers.every_case_tac >>
  fs [] >>
  metis_tac [smtstr_shortest_re_nonempty]
QED

Theorem smtstr_find_re_nonempty:
  smtstr_find_re F r s = SOME (i, n) ==> 0 < n
Proof
  metis_tac [smtstr_find_re_def, smtstr_find_re_aux_nonempty]
QED

Definition smtstr_replace_re_all_aux_def:
  (smtstr_replace_re_all_aux 0 (s : num list) r u = s) /\
  (smtstr_replace_re_all_aux (SUC fuel) s r u =
    case smtstr_find_re F r s of
      NONE => s
    | SOME (i, n) =>
        TAKE i s ++ u ++
        smtstr_replace_re_all_aux fuel (DROP (i + n) s) r u)
End

Definition smtstr_replace_re_all_def:
  smtstr_replace_re_all (s : num list) r u =
    smtstr_replace_re_all_aux (LENGTH s) s r u
End

(* SMT-LIB character and decimal conversions. *)

Definition smtstr_is_digit_def:
  smtstr_is_digit (s : num list) <=>
    ?c. s = [c] /\ 48 <= c /\ c <= 57
End

Definition smtstr_to_code_def:
  smtstr_to_code (s : num list) =
    case s of
      [c] => &c
    | _ => -1
End

Definition smtstr_from_code_def:
  smtstr_from_code (n : int) =
    if n < 0 \/ 196607 < Num n then [] else [Num n]
End

Definition smtstr_digits_def:
  smtstr_digits (s : num list) <=>
    EVERY (\c. 48 <= c /\ c <= 57) s
End

Definition smtstr_to_int_def:
  smtstr_to_int (s : num list) =
    if s = [] \/ ~smtstr_digits s then -1
    else
      &ASCIInumbers$num_from_dec_string (MAP CHR s)
End

Definition smtstr_from_int_def:
  smtstr_from_int (n : int) =
    if n < 0 then []
    else MAP ORD (ASCIInumbers$num_to_dec_string (Num n))
End

val _ = computeLib.add_funs
  [smtstr_replace_def, smtstr_replace_all_aux_def,
   smtstr_replace_all_def,
   smtstr_shortest_re_aux_def, smtstr_shortest_re_def,
   smtstr_find_re_aux_def, smtstr_find_re_def,
   smtstr_replace_re_def, smtstr_replace_re_all_aux_def,
   smtstr_replace_re_all_def,
   smtstr_is_digit_def, smtstr_to_code_def,
   smtstr_from_code_def, smtstr_digits_def,
   smtstr_to_int_def, smtstr_from_int_def];

(* Public computation equations. *)

Theorem smtstr_replace_compute[compute]:
  smtstr_replace s t u =
    case smtstr_indexof_aux t 0 s of
      NONE => s
    | SOME n =>
        TAKE n s ++ u ++ DROP (n + LENGTH t) s
Proof
  simp [smtstr_replace_def]
QED

Theorem smtstr_replace_all_compute[compute]:
  smtstr_replace_all s t u =
    if t = [] then s
    else smtstr_replace_all_aux (LENGTH s) s t u
Proof
  simp [smtstr_replace_all_def]
QED

Theorem smtstr_replace_re_compute[compute]:
  smtstr_replace_re s r u =
    case smtstr_find_re T r s of
      NONE => s
    | SOME (i, n) => TAKE i s ++ u ++ DROP (i + n) s
Proof
  simp [smtstr_replace_re_def]
QED

Theorem smtstr_replace_re_all_compute[compute]:
  smtstr_replace_re_all s r u =
    smtstr_replace_re_all_aux (LENGTH s) s r u
Proof
  simp [smtstr_replace_re_all_def]
QED

Theorem smtstr_is_digit_compute[compute]:
  (~smtstr_is_digit []) /\
  (smtstr_is_digit [c] <=> 48 <= c /\ c <= 57) /\
  (~smtstr_is_digit (c1::c2::s))
Proof
  simp [smtstr_is_digit_def]
QED

Theorem smtstr_to_code_compute[compute]:
  (smtstr_to_code [] = -1) /\
  (smtstr_to_code [c] = &c) /\
  (smtstr_to_code (c1::c2::s) = -1)
Proof
  simp [smtstr_to_code_def]
QED

Theorem smtstr_from_code_compute[compute]:
  smtstr_from_code n =
    if n < 0 \/ 196607 < Num n then [] else [Num n]
Proof
  simp [smtstr_from_code_def]
QED

Theorem smtstr_digits_compute[compute]:
  (smtstr_digits [] <=> T) /\
  (smtstr_digits (c::s) <=>
     48 <= c /\ c <= 57 /\ smtstr_digits s)
Proof
  simp [smtstr_digits_def, CONJ_ASSOC]
QED

Theorem smtstr_to_int_compute[compute]:
  smtstr_to_int s =
    if s = [] \/ ~smtstr_digits s then -1
    else &ASCIInumbers$num_from_dec_string (MAP CHR s)
Proof
  simp [smtstr_to_int_def]
QED

Theorem smtstr_from_int_compute[compute]:
  smtstr_from_int n =
    if n < 0 then []
    else MAP ORD (ASCIInumbers$num_to_dec_string (Num n))
Proof
  simp [smtstr_from_int_def]
QED

(* The ASCIInumbers bridge and SMT-LIB's divergent error cases. *)

Theorem smtstr_to_int_ascii:
  s <> [] /\ smtstr_digits s ==>
  smtstr_to_int s =
    &ASCIInumbers$num_from_dec_string (MAP CHR s)
Proof
  simp [smtstr_to_int_def]
QED

Theorem smtstr_to_int_empty:
  smtstr_to_int [] = -1
Proof
  simp [smtstr_to_int_def]
QED

Theorem smtstr_to_int_nondigit:
  ~smtstr_digits s ==> smtstr_to_int s = -1
Proof
  simp [smtstr_to_int_def]
QED

Theorem smtstr_from_int_ascii:
  0 <= n ==>
  smtstr_from_int n =
    MAP ORD (ASCIInumbers$num_to_dec_string (Num n))
Proof
  strip_tac >>
  Cases_on `n < 0` >>
  simp [smtstr_from_int_def] >>
  intLib.ARITH_TAC
QED

Theorem smtstr_from_int_negative:
  n < 0 ==> smtstr_from_int n = []
Proof
  simp [smtstr_from_int_def]
QED

Theorem smtstr_digits_num_to_dec_string:
  smtstr_digits
    (MAP ORD (ASCIInumbers$num_to_dec_string n))
Proof
  rw [smtstr_digits_def, listTheory.EVERY_MAP] >>
  mp_tac
    (ASCIInumbersTheory.EVERY_isDigit_num_to_dec_string
       |> Q.SPEC `n`) >>
  simp [listTheory.EVERY_MEM, stringTheory.isDigit_def]
QED

Theorem smtstr_from_int_nonempty:
  0 <= n ==> smtstr_from_int n <> []
Proof
  strip_tac >>
  Cases_on `n < 0` >>
  fs [smtstr_from_int_def,
      ASCIInumbersTheory.num_to_dec_string_nil] >>
  intLib.COOPER_TAC
QED

Theorem smtstr_to_int_from_int:
  0 <= n ==> smtstr_to_int (smtstr_from_int n) = n
Proof
  strip_tac >>
  `smtstr_from_int n =
     MAP ORD (ASCIInumbers$num_to_dec_string (Num n))` by
    metis_tac [smtstr_from_int_ascii] >>
  `smtstr_digits (smtstr_from_int n)` by
    simp [smtstr_digits_num_to_dec_string] >>
  `smtstr_from_int n <> []` by
    metis_tac [smtstr_from_int_nonempty] >>
  simp [smtstr_to_int_def, listTheory.MAP_MAP_o,
        combinTheory.o_DEF, ASCIInumbersTheory.toNum_toString,
        integerTheory.INT_OF_NUM]
QED

(* Wellformedness closure for every new string-valued operator. *)

Theorem wfstr_replace:
  wfstr s /\ wfstr u ==> wfstr (smtstr_replace s t u)
Proof
  rw [smtstr_replace_def] >>
  BasicProvers.every_case_tac >>
  fs [wfstr_def, listTheory.EVERY_APPEND] >>
  metis_tac [rich_listTheory.EVERY_TAKE,
             rich_listTheory.EVERY_DROP]
QED

Theorem wfstr_replace_all_aux:
  wfstr s /\ wfstr u ==>
  wfstr (smtstr_replace_all_aux fuel s t u)
Proof
  qid_spec_tac `u` >>
  qid_spec_tac `t` >>
  qid_spec_tac `s` >>
  qid_spec_tac `fuel` >>
  recInduct smtstr_replace_all_aux_ind >>
  rw [smtstr_replace_all_aux_def]
  >- (fs [wfstr_def] >>
      first_x_assum irule >>
      irule rich_listTheory.EVERY_DROP >>
      simp [])
  >- fs [wfstr_def]
QED

Theorem wfstr_replace_all:
  wfstr s /\ wfstr u ==> wfstr (smtstr_replace_all s t u)
Proof
  rw [smtstr_replace_all_def] >>
  metis_tac [wfstr_replace_all_aux]
QED

Theorem wfstr_replace_re:
  wfstr s /\ wfstr u ==> wfstr (smtstr_replace_re s r u)
Proof
  rw [smtstr_replace_re_def] >>
  BasicProvers.every_case_tac >>
  fs [wfstr_def, listTheory.EVERY_APPEND] >>
  metis_tac [rich_listTheory.EVERY_TAKE,
             rich_listTheory.EVERY_DROP]
QED

Theorem wfstr_replace_re_all_aux:
  wfstr s /\ wfstr u ==>
  wfstr (smtstr_replace_re_all_aux fuel s r u)
Proof
  qid_spec_tac `s` >>
  Induct_on `fuel` >>
  simp [smtstr_replace_re_all_aux_def] >>
  rpt gen_tac >>
  BasicProvers.every_case_tac >>
  fs [wfstr_def, listTheory.EVERY_APPEND] >>
  metis_tac [rich_listTheory.EVERY_TAKE,
             rich_listTheory.EVERY_DROP]
QED

Theorem wfstr_replace_re_all:
  wfstr s /\ wfstr u ==> wfstr (smtstr_replace_re_all s r u)
Proof
  rw [smtstr_replace_re_all_def] >>
  metis_tac [wfstr_replace_re_all_aux]
QED

Theorem wfstr_from_code:
  wfstr (smtstr_from_code n)
Proof
  rw [smtstr_from_code_def, wfstr_def] >>
  fs []
QED

Theorem wfstr_from_int:
  wfstr (smtstr_from_int n)
Proof
  rw [smtstr_from_int_def, wfstr_def,
      listTheory.EVERY_MAP, listTheory.EVERY_MEM] >>
  fs [listTheory.MEM_MAP] >>
  metis_tac
    [stringTheory.ORD_BOUND,
     DECIDE ``!x:num. x < 256 ==> x <= 196607``]
QED

(* Replay algebra.  The TASK_02 draft_length recording rewrites "abc" to a
   seq.unit/Char chain and uses concat unit, associativity, and length. *)

Theorem smtstr_concat_assoc:
  smtstr_concat (smtstr_concat s t) u =
    smtstr_concat s (smtstr_concat t u)
Proof
  simp [smtstr_concat_def, listTheory.APPEND_ASSOC]
QED

Theorem smtstr_concat_nil_left:
  smtstr_concat [] s = s
Proof
  simp [smtstr_concat_def]
QED

Theorem smtstr_concat_nil_right:
  smtstr_concat s [] = s
Proof
  simp [smtstr_concat_def]
QED

Theorem smtstr_len_concat:
  smtstr_len (smtstr_concat s t) =
    smtstr_len s + smtstr_len t
Proof
  simp [smtstr_concat_def, smtstr_len_def]
QED

Theorem smtstr_len_concat_int:
  &(smtstr_len (smtstr_concat s t)) =
    &(smtstr_len s) + &(smtstr_len t)
Proof
  simp [smtstr_len_concat, integerTheory.INT_OF_NUM_ADD]
QED

Theorem smtstr_len_nonnegative:
  0 <= &(smtstr_len s)
Proof
  simp []
QED

Theorem smtstr_len_char:
  smtstr_len (smtstr_char c) = 1
Proof
  simp [smtstr_len_def, smtstr_char_def]
QED

Theorem smtstr_unit_concat:
  smtstr_concat (smtstr_char c) s = c::s
Proof
  simp [smtstr_concat_def, smtstr_char_def]
QED

Theorem smtstr_literal3_units:
  smtstr_concat (smtstr_char a)
    (smtstr_concat (smtstr_char b) (smtstr_char c)) = [a; b; c]
Proof
  simp [smtstr_concat_def, smtstr_char_def]
QED

(* TASK_02 draft_regex_membership uses prefix witnesses; the contains and
   suffix operator recordings use the same append decompositions. *)

Theorem smtstr_prefixof_decompose:
  smtstr_prefixof s t <=>
    ?u. t = smtstr_concat s u
Proof
  simp [smtstr_prefixof_def, smtstr_concat_def,
        rich_listTheory.IS_PREFIX_APPEND]
QED

Theorem smtstr_suffixof_decompose:
  smtstr_suffixof s t <=>
    ?u. t = smtstr_concat u s
Proof
  simp [smtstr_suffixof_def, smtstr_concat_def,
        rich_listTheory.IS_SUFFIX_APPEND]
QED

Theorem smtstr_contains_decompose:
  smtstr_contains s t <=>
    ?u v. s = smtstr_concat u (smtstr_concat t v)
Proof
  simp [smtstr_contains_def, smtstr_concat_def,
        rich_listTheory.IS_SUBLIST_APPEND]
QED

Theorem smtstr_prefixof_trans:
  smtstr_prefixof s t /\ smtstr_prefixof t u ==>
    smtstr_prefixof s u
Proof
  simp [smtstr_prefixof_decompose] >>
  metis_tac [smtstr_concat_assoc]
QED

Theorem smtstr_suffixof_trans:
  smtstr_suffixof s t /\ smtstr_suffixof t u ==>
    smtstr_suffixof s u
Proof
  simp [smtstr_suffixof_decompose] >>
  metis_tac [smtstr_concat_assoc]
QED

Theorem smtstr_contains_trans:
  smtstr_contains s t /\ smtstr_contains t u ==>
    smtstr_contains s u
Proof
  simp [smtstr_contains_decompose] >>
  metis_tac [smtstr_concat_assoc]
QED

(* TASK_02 draft_str_lt records irreflexivity and the two-direction
   comparison clause.  These facts give the strict/non-strict order kit. *)

Theorem smtstr_lt_irrefl:
  ~smtstr_lt s s
Proof
  Induct_on `s` >>
  simp [smtstr_lt_compute]
QED

Theorem smtstr_lt_trans:
  smtstr_lt s t /\ smtstr_lt t u ==> smtstr_lt s u
Proof
  `transitive (LLEX ($< : num -> num -> bool))` by
    (irule listTheory.LLEX_transitive >>
     simp [relationTheory.transitive_def] >>
     decide_tac) >>
  fs [smtstr_lt_def] >>
  metis_tac [relationTheory.transitive_def]
QED

Theorem smtstr_lt_trichotomy:
  smtstr_lt s t \/ s = t \/ smtstr_lt t s
Proof
  qid_spec_tac `t` >>
  Induct_on `s` >>
  Cases_on `t` >>
  simp [smtstr_lt_compute] >>
  metis_tac [arithmeticTheory.LT_CASES]
QED

Theorem smtstr_le_refl:
  smtstr_le s s
Proof
  simp [smtstr_le_def]
QED

Theorem smtstr_lt_imp_le:
  smtstr_lt s t ==> smtstr_le s t
Proof
  simp [smtstr_le_def]
QED

Theorem smtstr_le_trans:
  smtstr_le s t /\ smtstr_le t u ==> smtstr_le s u
Proof
  rw [smtstr_le_def] >>
  metis_tac [smtstr_lt_trans]
QED

Theorem smtstr_le_total:
  smtstr_le s t \/ smtstr_le t s
Proof
  metis_tac [smtstr_lt_trichotomy, smtstr_le_def]
QED

(* TASK_02 draft_substr couples str.at/substr with concat lengths and
   nonnegative tail lengths.  The following boundary lemmas expose all
   totalization branches without unfolding smtstr_substr in consumers. *)

Theorem smtstr_len_substr:
  smtstr_len (smtstr_substr s i n) =
    if i < 0 \/ n <= 0 \/ LENGTH s <= Num i then 0
    else MIN (Num n) (LENGTH s - Num i)
Proof
  rw [smtstr_len_def, smtstr_substr_def,
      listTheory.LENGTH_TAKE_EQ] >>
  simp [arithmeticTheory.MIN_DEF]
QED

Theorem smtstr_len_substr_source_bound:
  smtstr_len (smtstr_substr s i n) <= smtstr_len s
Proof
  rw [smtstr_len_substr, smtstr_len_def] >>
  simp [arithmeticTheory.MIN_DEF]
QED

Theorem smtstr_len_substr_count_bound:
  smtstr_len (smtstr_substr s i n) <= Num n
Proof
  rw [smtstr_len_substr] >>
  simp [arithmeticTheory.MIN_DEF]
QED

Theorem smtstr_at_in_range:
  0 <= i /\ Num i < LENGTH s ==>
    smtstr_at s i = [EL (Num i) s]
Proof
  strip_tac >>
  `~(i < 0)` by intLib.ARITH_TAC >>
  fs [smtstr_at_def, smtstr_substr_def,
      listTheory.TAKE1_DROP]
QED

Theorem smtstr_len_at:
  smtstr_len (smtstr_at s i) =
    if i < 0 \/ LENGTH s <= Num i then 0 else 1
Proof
  Cases_on `i < 0 \/ LENGTH s <= Num i`
  >- simp [smtstr_at_def, smtstr_len_substr]
  >> fs [] >>
  `0 < LENGTH s - Num i` by decide_tac >>
  simp [smtstr_at_def, smtstr_len_substr,
        arithmeticTheory.MIN_DEF]
QED

Theorem smtstr_len_at_bound:
  smtstr_len (smtstr_at s i) <= 1
Proof
  rw [smtstr_len_at]
QED

Theorem smtstr_at_zero:
  s = [] \/ smtstr_at s 0 = [EL 0 s]
Proof
  Cases_on `s` >>
  simp [smtstr_at_in_range]
QED

Theorem smtstr_substr_zero_one:
  smtstr_substr s 0 1 = smtstr_at s 0
Proof
  simp [smtstr_at_def]
QED

Theorem smtstr_indexof_aux_bounds:
  smtstr_indexof_aux t n s = SOME k ==>
    n <= k /\ k <= n + LENGTH s
Proof
  qid_spec_tac `n` >>
  Induct_on `s` >>
  rw [smtstr_indexof_aux_def] >>
  res_tac >>
  decide_tac
QED

Theorem smtstr_indexof_lower_bound:
  0 <= smtstr_indexof s t i ==> i <= smtstr_indexof s t i
Proof
  rw [smtstr_indexof_def] >>
  BasicProvers.every_case_tac >>
  fs [] >>
  drule smtstr_indexof_aux_bounds >>
  intLib.ARITH_TAC
QED

Theorem smtstr_indexof_upper_bound:
  0 <= smtstr_indexof s t i ==>
    smtstr_indexof s t i <= &(smtstr_len s)
Proof
  rw [smtstr_indexof_def, smtstr_len_def] >>
  BasicProvers.every_case_tac >>
  fs [] >>
  drule smtstr_indexof_aux_bounds >>
  simp [] >>
  intLib.ARITH_TAC
QED

Theorem smtstr_indexof_negative:
  smtstr_indexof s t i < 0 <=> smtstr_indexof s t i = -1
Proof
  rw [smtstr_indexof_def] >>
  BasicProvers.every_case_tac >>
  simp []
QED

(* TASK_02 draft_str_to_int records digit2int values 0--9.  These official
   conversion facts expose the corresponding code-point and digit bounds. *)

Theorem smtstr_is_digit_wfstr:
  smtstr_is_digit s ==> wfstr s
Proof
  strip_tac >>
  fs [smtstr_is_digit_def, wfstr_def]
QED

Theorem smtstr_is_digit_to_code_bounds:
  smtstr_is_digit s ==>
    48 <= smtstr_to_code s /\ smtstr_to_code s <= 57
Proof
  strip_tac >>
  fs [smtstr_is_digit_def, smtstr_to_code_def]
QED

Theorem smtstr_from_code_to_code:
  0 <= n /\ Num n <= 196607 ==>
    smtstr_to_code (smtstr_from_code n) = n
Proof
  rw [smtstr_from_code_def, smtstr_to_code_def] >>
  intLib.ARITH_TAC
QED

(* TASK_02 draft_re_comp/draft_re_loop aut.accept clauses unfold one
   character at a time.  Package the concat and star derivative equations
   at the semantic boundary used by the replay prover. *)

Theorem smt_in_re_concat:
  smt_in_re s (reglan_concat r1 r2) <=>
    ?u v. smt_in_re u r1 /\ smt_in_re v r2 /\ s = u ++ v
Proof
  simp [smt_in_re_def, reglan_dot_def]
QED

Theorem smt_in_re_concat_cons:
  smt_in_re (c::s) (reglan_concat r1 r2) <=>
    smt_in_re s (reglan_concat (re_deriv c r1) r2) \/
    re_nullable r1 /\ smt_in_re s (re_deriv c r2)
Proof
  Cases_on `re_nullable r1` >>
  simp [re_deriv_correct, re_deriv_def, smt_in_re_def]
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
  str_inj "Az" = [65; 122] /\
  wfstr [196607] /\
  ~wfstr [196608]
Proof
  EVAL_TAC
QED

Theorem smtstr_a2_eval:
  smtstr_replace [97; 98; 99; 97; 98; 99] [98; 99] [88] =
    [97; 88; 97; 98; 99] /\
  smtstr_replace [97; 98] [] [88] = [88; 97; 98] /\
  smtstr_replace [97; 98] [99] [88] = [97; 98] /\
  smtstr_replace_all [97; 98; 97] [97] [99] = [99; 98; 99] /\
  smtstr_replace_all [97; 98] [] [99] = [97; 98] /\
  smtstr_replace_all [97; 97; 97] [97; 97] [98] = [98; 97] /\
  smtstr_replace_re [97; 98]
    (reglan_union (reglan_to_re [97])
                  (reglan_to_re [97; 98])) [120] =
    [120; 98] /\
  smtstr_replace_re [97; 98]
    (reglan_union (reglan_to_re [98])
                  (reglan_to_re [97; 98])) [120] =
    [120] /\
  smtstr_replace_re [97; 98] (reglan_to_re []) [120] =
    [120; 97; 98] /\
  smtstr_replace_re_all [97; 98; 97]
    (reglan_union (reglan_to_re [])
                  (reglan_to_re [97])) [120] =
    [120; 98; 120] /\
  smtstr_replace_re_all [97; 98] (reglan_to_re []) [120] =
    [97; 98] /\
  smtstr_replace_re_all [97; 98] reglan_allchar [120] =
    [120; 120] /\
  smtstr_is_digit [48] /\
  smtstr_is_digit [57] /\
  ~smtstr_is_digit [] /\
  ~smtstr_is_digit [48; 49] /\
  ~smtstr_is_digit [47] /\
  smtstr_to_code [196607] = 196607 /\
  smtstr_to_code [] = -1 /\
  smtstr_to_code [1; 2] = -1 /\
  smtstr_from_code 0 = [0] /\
  smtstr_from_code 196607 = [196607] /\
  smtstr_from_code (-1) = [] /\
  smtstr_from_code 196608 = [] /\
  smtstr_to_int [48; 48; 49; 50; 51] = 123 /\
  smtstr_to_int [] = -1 /\
  smtstr_to_int [45; 49] = -1 /\
  smtstr_from_int 0 = [48] /\
  smtstr_from_int 123 = [49; 50; 51] /\
  smtstr_from_int (-123) = [] /\
  smtstr_to_int (smtstr_from_int 9876) = 9876
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
