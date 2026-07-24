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
