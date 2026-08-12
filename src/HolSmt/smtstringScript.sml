(* Copyright (c) 2026 The HOL4 contributors. *)

(* SMT-LIB Unicode strings wrap lists of Unicode code points so the SMT sort
   is carried by the HOL type rather than reconstructed from wfstr guards.
   The carrier is a type definition rather than a free datatype precisely so
   that the code-point bound is an inhabitant property: every ':smtstr' is
   wellformed, so the HOL universe of the type is exactly the SMT-LIB String
   universe and binders need no relativization in either direction. *)
Theory smtstring
Ancestors[qualified]
  ASCIInumbers integer rich_list

Theorem SMTSTR_EXISTS[local]:
  ?l. (\l. EVERY (\c : num. c <= 196607) l) l
Proof
  Q.EXISTS_TAC `[]` >>
  simp []
QED

val smtstr_tyax = new_type_definition ("smtstr", SMTSTR_EXISTS)

val smtstr_bij = define_new_type_bijections {
  name = "smtstr_BIJ",
  ABS = "SmtStr",
  REP = "smtstr_rep",
  tyax = smtstr_tyax}

Theorem SmtStr_smtstr_rep[simp] = CONJUNCT1 smtstr_bij

Theorem smtstr_rep_SmtStr = BETA_RULE (CONJUNCT2 smtstr_bij)

(* Kept under its historical name: every rewrite that used to unfold the
   datatype's representation function now discharges the code-point bound
   as a side condition instead. *)
Theorem smtstr_rep_def[simp]:
  !l. EVERY (\c. c <= 196607) l ==> (smtstr_rep (SmtStr l) = l)
Proof
  simp [smtstr_rep_SmtStr]
QED

Theorem smtstr_rep_bound[simp]:
  EVERY (\c. c <= 196607) (smtstr_rep s)
Proof
  simp [smtstr_rep_SmtStr]
QED

(* Every substring of a representation is again a legal representation; the
   substring operators below rely on this to re-abstract their results. *)
Theorem smtstr_rep_bound_substr[simp]:
  EVERY (\c. c <= 196607) (TAKE n (DROP m (smtstr_rep s)))
Proof
  irule rich_listTheory.EVERY_TAKE >>
  irule rich_listTheory.EVERY_DROP >>
  simp []
QED

(* Out-of-range code points have no ':smtstr' image, so ground evaluation
   must report the violation rather than silently pick a representative. *)
Theorem smtstr_rep_compute[compute]:
  !l. smtstr_rep (SmtStr l) =
      if EVERY (\c. c <= 196607) l then l
      else FAIL smtstr_rep ^(mk_var ("code point out of range", bool))
        (SmtStr l)
Proof
  rw [combinTheory.FAIL_THM]
QED

Theorem smtstr_rep_11[simp]:
  (smtstr_rep s = smtstr_rep t) <=> (s = t)
Proof
  metis_tac [SmtStr_smtstr_rep]
QED

Theorem smtstr_eq_SmtStr:
  EVERY (\c. c <= 196607) l ==>
  ((s = SmtStr l <=> smtstr_rep s = l) /\
   (SmtStr l = s <=> l = smtstr_rep s))
Proof
  strip_tac >>
  metis_tac [SmtStr_smtstr_rep, smtstr_rep_def]
QED

Theorem smtstr_rep_eq_nil:
  (smtstr_rep s = []) <=> (s = SmtStr [])
Proof
  eq_tac
  >- metis_tac [SmtStr_smtstr_rep]
  >> strip_tac >>
  simp []
QED

(* ':smtstr' is a type definition rather than a datatype, so the compute set
   gets no constructor injectivity theorem.  Routing ground equality through
   the representation restores it: 'smtstr_rep_compute' reduces each side to
   its code-point list, or reports the out-of-range violation. *)
Theorem SmtStr_eq_compute[compute]:
  (SmtStr u = SmtStr v) <=>
    (smtstr_rep (SmtStr u) = smtstr_rep (SmtStr v))
Proof
  simp []
QED

Theorem SmtStr_11:
  EVERY (\c. c <= 196607) u /\ EVERY (\c. c <= 196607) v ==>
  ((SmtStr u = SmtStr v) <=> (u = v))
Proof
  strip_tac >>
  metis_tac [smtstr_rep_def]
QED

Theorem smtstr_eq_singleton:
  c <= 196607 ==> ((s = SmtStr [c]) <=> (smtstr_rep s = [c]))
Proof
  strip_tac >>
  `EVERY (\c. c <= 196607) [c]` by simp [] >>
  metis_tac [smtstr_eq_SmtStr]
QED

Theorem ranged_smtstr_nchotomy:
  !s. ?l. (s = SmtStr l) /\ EVERY (\c. c <= 196607) l
Proof
  gen_tac >>
  qexists_tac `smtstr_rep s` >>
  simp []
QED

Definition smtstr_size_def:
  smtstr_size (s : smtstr) = 0
End

(* Registering the ranged nchotomy keeps 'Cases_on' usable on ':smtstr' and
   makes it deliver the code-point bound alongside the representation. *)
val _ = TypeBase.export [
  TypeBasePure.mk_nondatatype_info (
    ``:smtstr``,
    {nchotomy = SOME ranged_smtstr_nchotomy,
     induction = NONE,
     size = SOME (``smtstr_size``, smtstr_size_def),
     encode = NONE})]

Definition wfstr_def:
  wfstr s <=> EVERY (\c. c <= 196607) (smtstr_rep s)
End

(* The bound is now carried by the type, so wellformedness is a theorem.
   'wfstr' survives as a constant because the SMT-LIB regex semantics below
   are stated in terms of it. *)
Theorem wfstr[simp]:
  wfstr s
Proof
  simp [wfstr_def]
QED

Definition smtstr_concat_def:
  smtstr_concat s t = SmtStr (smtstr_rep s ++ smtstr_rep t)
End

Definition smtstr_len_def:
  smtstr_len s : int = &(LENGTH (smtstr_rep s))
End

Definition smtstr_substr_def:
  smtstr_substr s (i : int) (n : int) =
    if i < 0 \/ n <= 0 \/ LENGTH (smtstr_rep s) <= Num i then
      SmtStr []
    else
      SmtStr (TAKE (Num n) (DROP (Num i) (smtstr_rep s)))
End

Definition smtstr_at_def:
  smtstr_at s (i : int) = smtstr_substr s i 1
End

Theorem smtstr_substr_full:
  smtstr_substr s 0 (smtstr_len s) = s
Proof
  qspec_then `s` strip_assume_tac ranged_smtstr_nchotomy >>
  Cases_on `l` >>
  simp [smtstr_substr_def, smtstr_len_def]
QED

Definition smtstr_update_def:
  smtstr_update s (i : int) t =
    if i < 0 \/ LENGTH (smtstr_rep s) <= Num i then s
    else SmtStr (TAKE (Num i) (smtstr_rep s) ++
      TAKE (LENGTH (smtstr_rep s) - Num i) (smtstr_rep t) ++
      DROP (Num i + LENGTH (smtstr_rep t)) (smtstr_rep s))
End

Definition smtstr_rev_def:
  smtstr_rev s = SmtStr (REVERSE (smtstr_rep s))
End

Theorem smtstr_rev_rev:
  smtstr_rev (smtstr_rev s) = s
Proof
  qspec_then `s` strip_assume_tac ranged_smtstr_nchotomy >>
  simp [smtstr_rev_def]
QED

Definition smtstr_prefixof_def:
  smtstr_prefixof s t <=>
    IS_PREFIX (smtstr_rep t) (smtstr_rep s)
End

Definition smtstr_suffixof_def:
  smtstr_suffixof s t <=>
    IS_SUFFIX (smtstr_rep t) (smtstr_rep s)
End

Definition smtstr_contains_def:
  smtstr_contains s t <=>
    IS_SUBLIST (smtstr_rep s) (smtstr_rep t)
End

Definition smtstr_indexof_aux_def:
  (smtstr_indexof_aux t n [] =
     if t = [] then SOME n else NONE) /\
  (smtstr_indexof_aux t n (h::s) =
     if IS_PREFIX (h::s) t then SOME n
     else smtstr_indexof_aux t (SUC n) s)
End

Definition smtstr_indexof_def:
  smtstr_indexof s t (i : int) =
    if i < 0 \/ LENGTH (smtstr_rep s) < Num i then -1
    else
      case smtstr_indexof_aux (smtstr_rep t) (Num i)
        (DROP (Num i) (smtstr_rep s)) of
        NONE => -1
      | SOME n => &n
End

Definition smtstr_lt_def:
  smtstr_lt s t <=> LLEX $< (smtstr_rep s) (smtstr_rep t)
End

Definition smtstr_le_def:
  smtstr_le s t <=> smtstr_lt s t \/ s = t
End

Definition smtstr_char_def:
  smtstr_char (c : num) = SmtStr [c]
End

Definition str_inj_def:
  str_inj (s : string) = SmtStr (MAP ORD (EXPLODE s))
End

(* SMT-LIB regular languages over Unicode code points. *)

Datatype:
  reglan
    = reglan_none
    | reglan_all
    | reglan_allchar
    | reglan_to_re smtstr
    | reglan_range smtstr smtstr
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

val reglan_loop_lang_compute_thm =
  DB.fetch "smtstring" "reglan_loop_lang_compute";

(* The word-level semantics.  The auxiliary language operators decompose a
   word into arbitrary 'num list' pieces, so the recursive clauses cannot be
   phrased as 'smt_in_re (SmtStr u) r': 'SmtStr u' is unconstrained when 'u'
   leaves the code-point range, whereas the pieces a decomposition produces
   are always sublists of a wellformed word.  're_lang' carries the semantics
   over raw words, and 'smt_in_re' reads it off the representation. *)

Definition re_lang_def:
  (re_lang reglan_none (u : num list) <=> F) /\
  (re_lang reglan_all u <=> EVERY (\c. c <= 196607) u) /\
  (re_lang reglan_allchar u <=> ?c. c <= 196607 /\ u = [c]) /\
  (re_lang (reglan_to_re t) u <=> u = smtstr_rep t) /\
  (re_lang (reglan_range lo hi) u <=>
     ?a b c.
       smtstr_rep lo = [a] /\ smtstr_rep hi = [b] /\ a <= c /\ c <= b /\
       c <= 196607 /\ u = [c]) /\
  (re_lang (reglan_concat r1 r2) u <=>
     reglan_dot (\x. re_lang r1 x) (\y. re_lang r2 y) u) /\
  (re_lang (reglan_union r1 r2) u <=>
     re_lang r1 u \/ re_lang r2 u) /\
  (re_lang (reglan_inter r1 r2) u <=>
     re_lang r1 u /\ re_lang r2 u) /\
  (re_lang (reglan_diff r1 r2) u <=>
     re_lang r1 u /\ ~re_lang r2 u) /\
  (re_lang (reglan_comp r) u <=>
     EVERY (\c. c <= 196607) u /\ ~re_lang r u) /\
  (re_lang (reglan_star r) u <=>
     reglan_kstar (\x. re_lang r x) u) /\
  (re_lang (reglan_plus r) u <=>
     reglan_dot
       (\x. re_lang r x)
       (reglan_kstar (\x. re_lang r x))
       u) /\
  (re_lang (reglan_opt r) u <=> u = [] \/ re_lang r u) /\
  (re_lang (reglan_power r n) u <=>
     reglan_repeat (\x. re_lang r x) n u) /\
  (re_lang (reglan_loop r i n) u <=>
     reglan_loop_lang (\x. re_lang r x) i n u)
End

Definition smt_in_re_def:
  (smt_in_re s reglan_none <=> F) /\
  (smt_in_re s reglan_all <=> wfstr s) /\
  (smt_in_re s reglan_allchar <=>
     ?c. c <= 196607 /\ s = SmtStr [c]) /\
  (smt_in_re s (reglan_to_re t) <=> s = t) /\
  (smt_in_re s (reglan_range lo hi) <=>
     ?a b c.
       smtstr_rep lo = [a] /\ smtstr_rep hi = [b] /\ a <= c /\ c <= b /\
       c <= 196607 /\ s = SmtStr [c]) /\
  (smt_in_re s (reglan_concat r1 r2) <=>
     reglan_dot
       (\u. re_lang r1 u)
       (\v. re_lang r2 v)
       (smtstr_rep s)) /\
  (smt_in_re s (reglan_union r1 r2) <=>
     smt_in_re s r1 \/ smt_in_re s r2) /\
  (smt_in_re s (reglan_inter r1 r2) <=>
     smt_in_re s r1 /\ smt_in_re s r2) /\
  (smt_in_re s (reglan_diff r1 r2) <=>
     smt_in_re s r1 /\ ~smt_in_re s r2) /\
  (smt_in_re s (reglan_comp r) <=>
     wfstr s /\ ~smt_in_re s r) /\
  (smt_in_re s (reglan_star r) <=>
     reglan_kstar (\u. re_lang r u) (smtstr_rep s)) /\
  (smt_in_re s (reglan_plus r) <=>
     reglan_dot
       (\u. re_lang r u)
       (reglan_kstar (\u. re_lang r u))
       (smtstr_rep s)) /\
  (smt_in_re s (reglan_opt r) <=>
     s = SmtStr [] \/ smt_in_re s r) /\
  (smt_in_re s (reglan_power r n) <=>
     reglan_repeat (\u. re_lang r u) n (smtstr_rep s)) /\
  (smt_in_re s (reglan_loop r i n) <=>
     reglan_loop_lang (\u. re_lang r u) i n (smtstr_rep s))
End

Theorem smt_in_re_rep:
  smt_in_re s r <=> re_lang r (smtstr_rep s)
Proof
  qid_spec_tac `s` >>
  Induct_on `r` >>
  simp [smt_in_re_def, re_lang_def, wfstr_def] >>
  metis_tac [smtstr_eq_singleton, smtstr_rep_eq_nil]
QED

Definition re_nullable_def:
  (re_nullable reglan_none = F) /\
  (re_nullable reglan_all = T) /\
  (re_nullable reglan_allchar = F) /\
  (re_nullable (reglan_to_re s) <=> s = SmtStr []) /\
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
     if c <= 196607 then reglan_to_re (SmtStr []) else reglan_none) /\
  (re_deriv c (reglan_to_re s) =
     case smtstr_rep s of
       [] => reglan_none
     | h::t =>
         if c = h then reglan_to_re (SmtStr t) else reglan_none) /\
  (re_deriv c (reglan_range lo hi) =
     case smtstr_rep lo of
       [a] =>
         (case smtstr_rep hi of
            [b] =>
              if a <= c /\ c <= b /\ c <= 196607 then
                reglan_to_re (SmtStr [])
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

(* Evaluation-ready characterizations for the persistent compute set.
   'smtstr_concat_def', 'smtstr_len_def' and 'smtstr_lt_def' are already
   persistent compute rules, and 'smtstr_rep_compute' evaluates the
   representation of a literal, so ground evaluation needs no
   constructor-recursive equations.  Such equations would in any case be
   unsound now: 'SmtStr (h::s)' constrains nothing unless 'h' is in range. *)

Theorem smtstr_rep_concat[simp]:
  smtstr_rep (smtstr_concat s t) = smtstr_rep s ++ smtstr_rep t
Proof
  simp [smtstr_concat_def, smtstr_rep_def]
QED

(* Injection from native HOL strings. *)

Theorem ORD_unicode_bound[simp]:
  ORD c <= 196607
Proof
  `ORD c < 256` by simp [stringTheory.ORD_BOUND] >>
  decide_tac
QED

Theorem EVERY_MAP_ORD_bound[simp]:
  EVERY (\c. c <= 196607) (MAP ORD l)
Proof
  simp [listTheory.EVERY_MAP]
QED

Theorem smtstr_rep_str_inj[simp]:
  smtstr_rep (str_inj s) = MAP ORD (EXPLODE s)
Proof
  simp [str_inj_def, smtstr_rep_def]
QED

Theorem str_inj_compute[compute]:
  (str_inj "" = SmtStr []) /\
  (str_inj (STRING c s) =
     SmtStr (ORD c::smtstr_rep (str_inj s)))
Proof
  simp [str_inj_def]
QED

Theorem MAP_ORD_11:
  MAP ORD s = MAP ORD t <=> s = t
Proof
  qid_spec_tac `t` >>
  Induct_on `s` >>
  Cases_on `t` >>
  simp [stringTheory.ORD_11]
QED

Theorem str_inj_11[simp]:
  str_inj s = str_inj t <=> s = t
Proof
  simp [str_inj_def, SmtStr_11, MAP_ORD_11]
QED

Theorem str_inj_STRCAT:
  str_inj (STRCAT s t) =
    smtstr_concat (str_inj s) (str_inj t)
Proof
  simp [str_inj_def, smtstr_concat_def, smtstr_rep_def,
        stringTheory.IMPLODE_EXPLODE_I]
QED

Theorem str_inj_STRLEN:
  smtstr_len (str_inj s) = &(STRLEN s)
Proof
  simp [smtstr_len_def, str_inj_def, smtstr_rep_def,
        stringTheory.IMPLODE_EXPLODE_I]
QED

Theorem str_inj_isPREFIX:
  isPREFIX s t <=>
    smtstr_prefixof (str_inj s) (str_inj t)
Proof
  qid_spec_tac `t` >>
  Induct_on `s` >>
  Cases_on `t` >>
  simp [str_inj_compute, smtstr_prefixof_def,
        smtstr_rep_def,
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
        smtstr_rep_def,
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

Theorem reglan_repeat_singleton:
  reglan_repeat (\u. u = [c]) n s <=> s = REPLICATE n c
Proof
  qid_spec_tac `s` >>
  Induct_on `n` >>
  simp [reglan_repeat_zero, reglan_repeat_suc, reglan_dot_def]
QED

Theorem REPLICATE_small[local]:
  REPLICATE 1 c = [c] /\
  REPLICATE 2 c = [c; c] /\
  REPLICATE 3 c = [c; c; c]
Proof
  EVAL_TAC
QED

Theorem REPLICATE_eq_cons[local]:
  (d::u = REPLICATE j c) <=>
  ?m. j = SUC m /\ d = c /\ u = REPLICATE m c
Proof
  Cases_on `j` >>
  simp [] >>
  metis_tac []
QED

(* A loop language is the union of the powers between its two bounds.  Every
   loop fact below is an instance of this equation, so none of them has to
   fix the bounds to the ones a particular benchmark happens to use. *)

Theorem reglan_loop_lang_bounds:
  reglan_loop_lang p i n s <=>
  ?j. i <= j /\ j <= n /\ reglan_repeat p j s
Proof
  Induct_on `n` >>
  rw [reglan_loop_lang_def] >>
  eq_tac >> rw []
  >- (qexists `SUC n` >> simp [])
  >- (qexists `j` >> simp [])
  >> Cases_on `j = SUC n` >>
  fs [] >>
  disj2_tac >>
  qexists `j` >>
  simp []
QED

Theorem reglan_loop_lang_singleton:
  reglan_loop_lang (\u. u = [c]) i n s <=>
  ?j. i <= j /\ j <= n /\ s = REPLICATE j c
Proof
  simp [reglan_loop_lang_bounds, reglan_repeat_singleton]
QED

Theorem reglan_repeat_nullable_singleton:
  reglan_repeat (\u. u = [c] \/ u = []) n s <=>
  ?m. m <= n /\ s = REPLICATE m c
Proof
  qid_spec_tac `s` >>
  Induct_on `n`
  >- simp [reglan_repeat_zero]
  >> rpt strip_tac >>
  simp [reglan_repeat_suc, reglan_dot_def] >>
  eq_tac
  >- (rw []
      >- (qexists `SUC m` >> simp [])
      >> qexists `m` >>
      simp [])
  >> rw [] >>
  Cases_on `m` >>
  fs [] >>
  qexistsl [`[c]`, `REPLICATE n' c`] >>
  simp [] >>
  qexists `n'` >>
  simp []
QED

Theorem reglan_loop_lang_nullable_singleton:
  reglan_loop_lang (\u. u = [c] \/ u = []) i n s <=>
  i <= n /\ ?m. m <= n /\ s = REPLICATE m c
Proof
  simp [reglan_loop_lang_bounds, reglan_repeat_nullable_singleton] >>
  eq_tac >> rw []
  >- decide_tac
  >- (qexists `m` >> simp [])
  >> qexists `n` >>
  simp [] >>
  qexists `m` >>
  simp []
QED

(* 'SmtStr [c]' pins down a one-character language only when 'c' is a real
   code point: out of range it is an unconstrained element of ':smtstr', so
   for instance 'SmtStr [c]' and 'SmtStr [c; c]' need not differ.  Every
   singleton-language fact below therefore carries the code-point bound. *)

Theorem smt_in_re_loop_singleton:
  c <= 196607 ==>
  (smt_in_re s (reglan_loop (reglan_to_re (SmtStr [c])) i n) <=>
   ?j. i <= j /\ j <= n /\ s = SmtStr (REPLICATE j c))
Proof
  strip_tac >>
  simp [smt_in_re_def, re_lang_def, smtstr_rep_def,
        reglan_loop_lang_singleton] >>
  `!j. EVERY (\c. c <= 196607) (REPLICATE j c)` by
    simp [rich_listTheory.EVERY_REPLICATE] >>
  metis_tac [smtstr_eq_SmtStr]
QED

Theorem smt_in_re_loop_nullable_singleton:
  c <= 196607 ==>
  (smt_in_re s
     (reglan_loop
       (reglan_union (reglan_to_re (SmtStr [c])) (reglan_to_re (SmtStr [])))
       i n) <=>
   i <= n /\ ?m. m <= n /\ s = SmtStr (REPLICATE m c))
Proof
  strip_tac >>
  simp [smt_in_re_def, re_lang_def, smtstr_rep_def,
        reglan_loop_lang_nullable_singleton] >>
  `!j. EVERY (\c. c <= 196607) (REPLICATE j c)` by
    simp [rich_listTheory.EVERY_REPLICATE] >>
  metis_tac [smtstr_eq_SmtStr]
QED

(* A loop with both bounds zero is the empty-word language; the derivative
   lemmas below use this to hand the terminal state back in the shape the
   replay path expects. *)

Theorem smt_in_re_loop_empty:
  smt_in_re s (reglan_loop r 0 0) <=>
  smt_in_re s (reglan_to_re (SmtStr []))
Proof
  simp [smt_in_re_def, reglan_loop_lang_def, reglan_repeat_zero,
        smtstr_rep_eq_nil]
QED

(* Named instances for the bounds the recorded Z3 corpus uses.  They are
   corollaries of the general lemmas above, not independent proofs. *)

Theorem smt_in_re_loop_singleton_0_1:
  c <= 196607 ==>
  (smt_in_re s (reglan_loop (reglan_to_re (SmtStr [c])) 0 1) <=>
   s = SmtStr [] \/ s = SmtStr [c])
Proof
  rw [smt_in_re_loop_singleton] >>
  eq_tac >> rw []
  >- (`j = 0 \/ j = 1` by decide_tac >> fs [REPLICATE_small])
  >- (qexists `0` >> simp [])
  >> qexists `1` >>
  simp [REPLICATE_small]
QED

Theorem smt_in_re_loop_singleton_0_2:
  c <= 196607 ==>
  (smt_in_re s (reglan_loop (reglan_to_re (SmtStr [c])) 0 2) <=>
   s = SmtStr [] \/ s = SmtStr [c] \/ s = SmtStr [c; c])
Proof
  rw [smt_in_re_loop_singleton] >>
  eq_tac >> rw []
  >- (`j = 0 \/ j = 1 \/ j = 2` by decide_tac >> fs [REPLICATE_small])
  >- (qexists `0` >> simp [])
  >- (qexists `1` >> simp [REPLICATE_small])
  >> qexists `2` >>
  simp [REPLICATE_small]
QED

Theorem smt_in_re_loop_singleton_1_3:
  c <= 196607 ==>
  (smt_in_re s (reglan_loop (reglan_to_re (SmtStr [c])) 1 3) <=>
   s = SmtStr [c] \/ s = SmtStr [c; c] \/ s = SmtStr [c; c; c])
Proof
  rw [smt_in_re_loop_singleton] >>
  eq_tac >> rw []
  >- (`j = 1 \/ j = 2 \/ j = 3` by decide_tac >> fs [REPLICATE_small])
  >- (qexists `1` >> simp [REPLICATE_small])
  >- (qexists `2` >> simp [REPLICATE_small])
  >> qexists `3` >>
  simp [REPLICATE_small]
QED

Theorem smt_in_re_loop_nullable_singleton_0_1:
  c <= 196607 ==>
  (smt_in_re s
      (reglan_loop
        (reglan_union (reglan_to_re (SmtStr [c])) (reglan_to_re (SmtStr [])))
        0 1) <=>
   s = SmtStr [] \/ s = SmtStr [c])
Proof
  rw [smt_in_re_loop_nullable_singleton] >>
  eq_tac >> rw []
  >- (`m = 0 \/ m = 1` by decide_tac >> fs [REPLICATE_small])
  >- (qexists `0` >> simp [])
  >> qexists `1` >>
  simp [REPLICATE_small]
QED

Theorem smt_in_re_loop_nullable_singleton_1_2:
  c <= 196607 ==>
  (smt_in_re s
      (reglan_loop
        (reglan_union (reglan_to_re (SmtStr [c])) (reglan_to_re (SmtStr [])))
        1 2) <=>
   s = SmtStr [] \/ s = SmtStr [c] \/ s = SmtStr [c; c])
Proof
  rw [smt_in_re_loop_nullable_singleton] >>
  eq_tac >> rw []
  >- (`m = 0 \/ m = 1 \/ m = 2` by decide_tac >> fs [REPLICATE_small])
  >- (qexists `0` >> simp [])
  >- (qexists `1` >> simp [REPLICATE_small])
  >> qexists `2` >>
  simp [REPLICATE_small]
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

Theorem re_nullable_lang:
  re_nullable r <=> re_lang r []
Proof
  Induct_on `r` >>
  simp [re_nullable_def, re_lang_def,
        reglan_dot_def, reglan_kstar_nil, reglan_repeat_nil,
        reglan_loop_lang_nil, smtstr_rep_eq_nil] >>
  metis_tac []
QED

Theorem re_nullable_correct:
  re_nullable r <=> smt_in_re (SmtStr []) r
Proof
  simp [smt_in_re_rep, re_nullable_lang]
QED

Theorem reglan_power_deriv_correct:
  (!t. re_lang dr t <=> re_lang r (c::t)) /\
  (nullable <=> re_lang r []) ==>
  (re_lang (reglan_power_deriv dr nullable r n) s <=>
   reglan_repeat (\u. re_lang r u) n (c::s))
Proof
  strip_tac >>
  qid_spec_tac `s` >>
  Induct_on `n`
  >- simp [reglan_power_deriv_def, re_lang_def, reglan_repeat_zero]
  >> rpt strip_tac >>
  Cases_on `nullable` >>
  fs [reglan_power_deriv_def, re_lang_def,
      reglan_repeat_suc, reglan_dot_cons_unfold] >>
  metis_tac []
QED

Theorem reglan_loop_deriv_correct:
  (!t. re_lang dr t <=> re_lang r (c::t)) /\
  (nullable <=> re_lang r []) ==>
  (re_lang (reglan_loop_deriv dr nullable r i n) s <=>
   reglan_loop_lang (\u. re_lang r u) i n (c::s))
Proof
  strip_tac >>
  fs [] >>
  qid_spec_tac `s` >>
  Induct_on `n`
  >- simp [reglan_loop_deriv_def, re_lang_def,
           reglan_loop_lang_def, reglan_repeat_zero]
  >> rpt strip_tac >>
  Cases_on `i <= SUC n`
  >- (`re_lang (reglan_power_deriv dr (re_lang r []) r (SUC n)) s <=>
       reglan_repeat (\u. re_lang r u) (SUC n) (c::s)` by
        (irule reglan_power_deriv_correct >>
         simp []) >>
      simp [reglan_loop_deriv_def, re_lang_def, reglan_loop_lang_def])
  >- (`n < i` by fs [] >>
      simp [reglan_loop_deriv_def, re_lang_def,
            reglan_loop_lang_def, reglan_loop_lang_too_large])
QED

Theorem re_deriv_lang:
  re_lang r (c::u) <=> re_lang (re_deriv c r) u
Proof
  qid_spec_tac `u` >>
  Induct_on `r` >>
  rpt strip_tac
  >- simp [re_deriv_def, re_lang_def]
  >- (Cases_on `c <= 196607` >>
      simp [re_deriv_def, re_lang_def])
  >- (Cases_on `c <= 196607` >>
      simp [re_deriv_def, re_lang_def] >>
      metis_tac [])
  >- (Cases_on `s` >>
      Cases_on `l` >>
      simp [re_deriv_def, re_lang_def, smtstr_rep_def] >>
      Cases_on `c = h` >>
      fs [re_lang_def, smtstr_rep_def])
  >- (Cases_on `smtstr_rep s` >>
      simp [re_deriv_def, re_lang_def] >>
      Cases_on `t` >>
      simp [re_lang_def] >>
      Cases_on `smtstr_rep s0` >>
      simp [re_lang_def] >>
      Cases_on `t` >>
      simp [re_lang_def] >>
      Cases_on `h <= c /\ c <= h' /\ c <= 196607` >>
      simp [re_lang_def])
  >- (`reglan_dot (\x. re_lang r x) (\y. re_lang r' y) (c::u) <=>
       reglan_dot
         (\x. re_lang (re_deriv c r) x) (\y. re_lang r' y) u \/
       re_lang r [] /\ re_lang (re_deriv c r') u` by
        (rw [reglan_dot_def] >>
         metis_tac [listTheory.APPEND_EQ_CONS]) >>
      PURE_REWRITE_TAC [re_deriv_def, re_lang_def, re_nullable_lang] >>
      Cases_on `re_lang r []` >>
      fs [re_lang_def])
  >- simp [re_deriv_def, re_lang_def]
  >- simp [re_deriv_def, re_lang_def]
  >- simp [re_deriv_def, re_lang_def]
  >- (Cases_on `c <= 196607` >>
      simp [re_deriv_def, re_lang_def])
  >- simp [re_deriv_def, re_lang_def, reglan_kstar_cons_unfold,
           reglan_dot_def]
  >- (simp [re_deriv_def, re_lang_def,
            reglan_dot_cons_unfold,
            reglan_kstar_cons_unfold] >>
      simp [reglan_dot_def] >>
      metis_tac [])
  >- simp [re_deriv_def, re_lang_def]
  >- simp [re_deriv_def, re_lang_def, re_nullable_lang,
           reglan_power_deriv_correct]
  >- simp [re_deriv_def, re_lang_def, re_nullable_lang,
           reglan_loop_deriv_correct]
QED

(* The word-level statement above is unconditional; its ':smtstr' reading
   needs the leading character and the tail to be genuine code points,
   because 'SmtStr (c::s)' is otherwise unconstrained. *)

Theorem re_deriv_correct:
  EVERY (\x. x <= 196607) (c::s) ==>
  (smt_in_re (SmtStr (c::s)) r <=>
   smt_in_re (SmtStr s) (re_deriv c r))
Proof
  strip_tac >>
  fs [smt_in_re_rep, smtstr_rep_def, re_deriv_lang]
QED

Theorem reglan_kstar_allchar_gen[local]:
  (!u. p u <=> ?c. c <= 196607 /\ u = [c]) ==>
  !s. reglan_kstar p s <=> EVERY (\c. c <= 196607) s
Proof
  strip_tac >>
  Induct
  >- simp [reglan_kstar_nil]
  >> rpt strip_tac >>
  PURE_REWRITE_TAC [reglan_kstar_cons_unfold] >>
  simp [reglan_dot_def] >>
  metis_tac []
QED

Theorem reglan_kstar_allchar:
  reglan_kstar (\u. ?c. c <= 196607 /\ u = [c]) s <=>
  EVERY (\c. c <= 196607) s
Proof
  irule reglan_kstar_allchar_gen >>
  simp []
QED

Theorem smt_in_re_star_allchar:
  smt_in_re s (reglan_star reglan_allchar) <=> wfstr s
Proof
  simp [smt_in_re_def, re_lang_def, reglan_kstar_allchar]
QED

Theorem smt_in_re_plus_allchar:
  smt_in_re s (reglan_plus reglan_allchar) <=>
  wfstr s /\ s <> SmtStr []
Proof
  `EVERY (\c. c <= 196607) (smtstr_rep s)` by simp [] >>
  Cases_on `smtstr_rep s` >>
  fs [smt_in_re_def, re_lang_def, reglan_kstar_allchar,
      reglan_dot_def, GSYM smtstr_rep_eq_nil] >>
  qexistsl [`[h]`, `t`] >>
  simp []
QED

(* Derivatives of a bounded loop over a one-character language, for arbitrary
   bounds: consuming one character lowers both bounds by one.  The named
   instances below are corollaries. *)

Theorem re_deriv_loop_singleton:
  c <= 196607 ==>
  (smt_in_re s (re_deriv d (reglan_loop (reglan_to_re (SmtStr [c])) i n)) <=>
   n <> 0 /\ d = c /\
   smt_in_re s (reglan_loop (reglan_to_re (SmtStr [c])) (i - 1) (n - 1)))
Proof
  strip_tac >>
  simp [smt_in_re_rep, GSYM re_deriv_lang, re_lang_def, smtstr_rep_def,
        reglan_loop_lang_singleton, REPLICATE_eq_cons] >>
  eq_tac >> rw []
  >- decide_tac
  >- (qexists `m` >> simp [])
  >> qexists `SUC j` >>
  simp [] >>
  qexists `j` >>
  simp []
QED

(* The nullable variant collapses the lower bound: once the body accepts the
   empty word every repetition count below the upper bound is reachable. *)

Theorem re_deriv_loop_nullable_singleton:
  c <= 196607 ==>
  (smt_in_re s
     (re_deriv d
       (reglan_loop
         (reglan_union (reglan_to_re (SmtStr [c])) (reglan_to_re (SmtStr [])))
         i n)) <=>
   i <= n /\ n <> 0 /\ d = c /\
   smt_in_re s
     (reglan_loop
       (reglan_union (reglan_to_re (SmtStr [c])) (reglan_to_re (SmtStr [])))
       0 (n - 1)))
Proof
  strip_tac >>
  simp [smt_in_re_rep, GSYM re_deriv_lang, re_lang_def, smtstr_rep_def,
        reglan_loop_lang_nullable_singleton, REPLICATE_eq_cons] >>
  eq_tac >> rw []
  >- decide_tac
  >- (qexists `m'` >> simp [])
  >> qexists `SUC m` >>
  simp [] >>
  qexists `m` >>
  simp []
QED

Theorem re_deriv_loop_singleton_1_3:
  c <= 196607 ==>
  (smt_in_re s
      (re_deriv d (reglan_loop (reglan_to_re (SmtStr [c])) 1 3)) <=>
   d = c /\ smt_in_re s (reglan_loop (reglan_to_re (SmtStr [c])) 0 2))
Proof
  rw [re_deriv_loop_singleton]
QED

Theorem re_deriv_loop_singleton_0_2:
  c <= 196607 ==>
  (smt_in_re s
      (re_deriv d (reglan_loop (reglan_to_re (SmtStr [c])) 0 2)) <=>
   d = c /\ smt_in_re s (reglan_loop (reglan_to_re (SmtStr [c])) 0 1))
Proof
  rw [re_deriv_loop_singleton]
QED

Theorem re_deriv_loop_singleton_0_1:
  c <= 196607 ==>
  (smt_in_re s
      (re_deriv d (reglan_loop (reglan_to_re (SmtStr [c])) 0 1)) <=>
   d = c /\ smt_in_re s (reglan_to_re (SmtStr [])))
Proof
  rw [re_deriv_loop_singleton, smt_in_re_loop_empty]
QED

Theorem re_deriv_loop_nullable_singleton_1_2:
  c <= 196607 ==>
  (smt_in_re s
      (re_deriv d
        (reglan_loop
          (reglan_union (reglan_to_re (SmtStr [c])) (reglan_to_re (SmtStr [])))
          1 2)) <=>
   d = c /\
   smt_in_re s
     (reglan_loop
       (reglan_union (reglan_to_re (SmtStr [c])) (reglan_to_re (SmtStr [])))
       0 1))
Proof
  rw [re_deriv_loop_nullable_singleton]
QED

Theorem re_deriv_loop_nullable_singleton_0_1:
  c <= 196607 ==>
  (smt_in_re s
      (re_deriv d
        (reglan_loop
          (reglan_union (reglan_to_re (SmtStr [c])) (reglan_to_re (SmtStr [])))
          0 1)) <=>
   d = c /\ smt_in_re s (reglan_to_re (SmtStr [])))
Proof
  rw [re_deriv_loop_nullable_singleton, smt_in_re_loop_empty]
QED

Theorem smt_in_re_deriv[compute]:
  smt_in_re s r <=>
    re_nullable (FOLDL (\r c. re_deriv c r) r (smtstr_rep s))
Proof
  `!u r. re_lang r u <=>
         re_nullable (FOLDL (\r c. re_deriv c r) r u)` by
    (Induct >>
     simp [re_nullable_lang, re_deriv_lang]) >>
  simp [smt_in_re_rep]
QED

(* Leftmost string and regular-language replacement. *)

Definition smtstr_replace_raw_def:
  smtstr_replace_raw (s : num list) t u =
    case smtstr_indexof_aux t 0 s of
      NONE => s
    | SOME n =>
        TAKE n s ++ u ++ DROP (n + LENGTH t) s
End

Definition smtstr_replace_def:
  smtstr_replace s t u =
    SmtStr
      (smtstr_replace_raw
         (smtstr_rep s) (smtstr_rep t) (smtstr_rep u))
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
  smtstr_replace_all s t u =
    if smtstr_rep t = [] then s
    else
      SmtStr
        (smtstr_replace_all_aux (LENGTH (smtstr_rep s))
           (smtstr_rep s) (smtstr_rep t) (smtstr_rep u))
End

Definition smtstr_shortest_re_aux_def:
  (smtstr_shortest_re_aux r s n 0 =
     if smt_in_re (SmtStr (TAKE n s)) r then SOME n else NONE) /\
  (smtstr_shortest_re_aux r s n (SUC k) =
     if smt_in_re (SmtStr (TAKE n s)) r then SOME n
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

Definition smtstr_replace_re_raw_def:
  smtstr_replace_re_raw (s : num list) r u =
    case smtstr_find_re T r s of
      NONE => s
    | SOME (i, n) => TAKE i s ++ u ++ DROP (i + n) s
End

Definition smtstr_replace_re_def:
  smtstr_replace_re s r u =
    SmtStr
      (smtstr_replace_re_raw
         (smtstr_rep s) r (smtstr_rep u))
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
  smtstr_replace_re_all s r u =
    SmtStr
      (smtstr_replace_re_all_aux (LENGTH (smtstr_rep s))
         (smtstr_rep s) r (smtstr_rep u))
End

(* SMT-LIB character and decimal conversions. *)

Definition smtstr_is_digit_def:
  smtstr_is_digit s <=>
    ?c. smtstr_rep s = [c] /\ 48 <= c /\ c <= 57
End

Definition smtstr_to_code_def:
  smtstr_to_code s =
    case smtstr_rep s of
      [c] => &c
    | _ => -1
End

Definition smtstr_from_code_def:
  smtstr_from_code (n : int) =
    if n < 0 \/ 196607 < Num n then SmtStr []
    else SmtStr [Num n]
End

Definition smtstr_digits_def:
  smtstr_digits s <=>
    EVERY (\c. 48 <= c /\ c <= 57) (smtstr_rep s)
End

Definition smtstr_to_int_def:
  smtstr_to_int s =
    if s = SmtStr [] \/ ~smtstr_digits s then -1
    else
      &ASCIInumbers$num_from_dec_string (MAP CHR (smtstr_rep s))
End

Definition smtstr_from_int_def:
  smtstr_from_int (n : int) =
    if n < 0 then SmtStr []
    else
      SmtStr (MAP ORD (ASCIInumbers$num_to_dec_string (Num n)))
End

(* Public computation equations. *)

(* 'smtstr_to_code_def' and 'smtstr_digits_def' are directly executable, so
   they serve as their own compute rules; 'smtstr_is_digit_def' is stated
   with an existential and needs the case-split form below. *)

Theorem smtstr_is_digit_compute[compute]:
  smtstr_is_digit s <=>
    case smtstr_rep s of
      [c] => 48 <= c /\ c <= 57
    | _ => F
Proof
  simp [smtstr_is_digit_def] >>
  Cases_on `smtstr_rep s` >>
  simp [] >>
  Cases_on `t` >>
  simp []
QED

(* The ASCIInumbers bridge and SMT-LIB's divergent error cases. *)

Theorem smtstr_to_int_ascii:
  s <> SmtStr [] /\ smtstr_digits s ==>
  smtstr_to_int s =
    &ASCIInumbers$num_from_dec_string (MAP CHR (smtstr_rep s))
Proof
  simp [smtstr_to_int_def]
QED

Theorem smtstr_to_int_empty:
  smtstr_to_int (SmtStr []) = -1
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
    SmtStr (MAP ORD (ASCIInumbers$num_to_dec_string (Num n)))
Proof
  strip_tac >>
  `~(n < 0)` by intLib.ARITH_TAC >>
  simp [smtstr_from_int_def]
QED

Theorem smtstr_from_int_negative:
  n < 0 ==> smtstr_from_int n = SmtStr []
Proof
  simp [smtstr_from_int_def, smtstr_rep_def]
QED

Theorem smtstr_digits_num_to_dec_string:
  smtstr_digits
    (SmtStr (MAP ORD (ASCIInumbers$num_to_dec_string n)))
Proof
  rw [smtstr_digits_def, smtstr_rep_def,
      listTheory.EVERY_MAP] >>
  mp_tac
    (ASCIInumbersTheory.EVERY_isDigit_num_to_dec_string
       |> Q.SPEC `n`) >>
  simp [listTheory.EVERY_MEM, stringTheory.isDigit_def]
QED

Theorem smtstr_from_int_nonempty:
  0 <= n ==> smtstr_from_int n <> SmtStr []
Proof
  strip_tac >>
  `~(n < 0)` by intLib.ARITH_TAC >>
  simp [smtstr_from_int_def, smtstr_eq_SmtStr,
        ASCIInumbersTheory.num_to_dec_string_nil]
QED

Theorem smtstr_to_int_from_int:
  0 <= n ==> smtstr_to_int (smtstr_from_int n) = n
Proof
  strip_tac >>
  `smtstr_from_int n =
     SmtStr (MAP ORD (ASCIInumbers$num_to_dec_string (Num n)))` by
    metis_tac [smtstr_from_int_ascii] >>
  `smtstr_digits (smtstr_from_int n)` by
    simp [smtstr_digits_num_to_dec_string] >>
  `smtstr_from_int n <> SmtStr []` by
    metis_tac [smtstr_from_int_nonempty] >>
  simp [smtstr_to_int_def, smtstr_rep_def,
        listTheory.MAP_MAP_o,
        combinTheory.o_DEF, ASCIInumbersTheory.toNum_toString,
        integerTheory.INT_OF_NUM]
QED

(* Replay algebra.  The TASK_02 draft_length recording rewrites "abc" to a
   seq.unit/Char chain and uses concat unit, associativity, and length. *)

Theorem smtstr_concat_assoc:
  smtstr_concat (smtstr_concat s t) u =
    smtstr_concat s (smtstr_concat t u)
Proof
  simp [smtstr_concat_def, smtstr_rep_def,
        listTheory.APPEND_ASSOC]
QED

Theorem smtstr_concat_nil_left:
  smtstr_concat (SmtStr []) s = s
Proof
  Cases_on `s` >>
  simp [smtstr_concat_def, smtstr_rep_def]
QED

Theorem smtstr_concat_nil_right:
  smtstr_concat s (SmtStr []) = s
Proof
  Cases_on `s` >>
  simp [smtstr_concat_def, smtstr_rep_def]
QED

(* TASK_02 draft_regex_membership compares a concat with a singleton and
   concludes that the distinguished middle character is that singleton. *)

Theorem smtstr_concat_middle_singleton:
  c <= 196607 /\ d <= 196607 /\
  smtstr_concat p (smtstr_concat (SmtStr [c]) q) = SmtStr [d] ==>
  c = d
Proof
  rpt strip_tac >>
  `smtstr_rep p ++ [c] ++ smtstr_rep q = [d]` by
    (pop_assum mp_tac >>
     simp [smtstr_concat_def, smtstr_rep_def, SmtStr_11]) >>
  Cases_on `smtstr_rep p` >>
  fs []
QED

Theorem smtstr_singleton_concat_middle:
  c <= 196607 /\ d <= 196607 /\
  SmtStr [d] = smtstr_concat p (smtstr_concat (SmtStr [c]) q) ==>
  d = c
Proof
  metis_tac [smtstr_concat_middle_singleton]
QED

Theorem smtstr_len_concat:
  smtstr_len (smtstr_concat s t) =
    smtstr_len s + smtstr_len t
Proof
  simp [smtstr_concat_def, smtstr_len_def,
        smtstr_rep_def,
        integerTheory.INT_OF_NUM_ADD]
QED

(* TASK_02 draft_regex_membership, draft_substr, and draft_re_comp use
   zero length as the empty-string branch of their sequence clauses. *)

Theorem smtstr_len_nonnegative:
  0 <= smtstr_len s
Proof
  simp [smtstr_len_def, smtstr_rep_def]
QED

Theorem smtstr_len_eq_zero:
  smtstr_len s = 0 <=> s = SmtStr []
Proof
  simp [smtstr_len_def, smtstr_rep_eq_nil]
QED

(* 'smtstr_char c' is the SMT-LIB one-character string only for a genuine
   code point; out of range it is an unconstrained ':smtstr'. *)

Theorem smtstr_rep_char:
  c <= 196607 ==> smtstr_rep (smtstr_char c) = [c]
Proof
  simp [smtstr_char_def, smtstr_rep_def]
QED

Theorem smtstr_len_char:
  c <= 196607 ==> smtstr_len (smtstr_char c) = 1
Proof
  simp [smtstr_len_def, smtstr_rep_char]
QED

Theorem smtstr_unit_concat:
  c <= 196607 ==>
  smtstr_concat (smtstr_char c) s = SmtStr (c::smtstr_rep s)
Proof
  simp [smtstr_concat_def, smtstr_rep_char]
QED

Theorem smtstr_literal3_units:
  a <= 196607 /\ b <= 196607 /\ c <= 196607 ==>
  smtstr_concat (smtstr_char a)
    (smtstr_concat (smtstr_char b) (smtstr_char c)) =
      SmtStr [a; b; c]
Proof
  strip_tac >>
  simp [smtstr_concat_def, smtstr_rep_char, smtstr_rep_def]
QED

(* TASK_02 draft_regex_membership uses prefix witnesses; the contains and
   suffix operator recordings use the same append decompositions. *)

Theorem smtstr_prefixof_decompose:
  smtstr_prefixof s t <=>
    ?u. t = smtstr_concat s u
Proof
  simp [smtstr_prefixof_def, smtstr_concat_def,
        rich_listTheory.IS_PREFIX_APPEND] >>
  eq_tac
  >- (strip_tac >>
      `EVERY (\c. c <= 196607) (smtstr_rep s ++ l)` by
        metis_tac [smtstr_rep_bound] >>
      `EVERY (\c. c <= 196607) l` by fs [] >>
      qexists `SmtStr l` >>
      simp [smtstr_rep_def] >>
      metis_tac [SmtStr_smtstr_rep])
  >- (strip_tac >>
      qexists `smtstr_rep u` >>
      simp [smtstr_rep_def])
QED

Theorem smtstr_suffixof_decompose:
  smtstr_suffixof s t <=>
    ?u. t = smtstr_concat u s
Proof
  simp [smtstr_suffixof_def, smtstr_concat_def,
        rich_listTheory.IS_SUFFIX_APPEND] >>
  eq_tac
  >- (strip_tac >>
      `EVERY (\c. c <= 196607) (l ++ smtstr_rep s)` by
        metis_tac [smtstr_rep_bound] >>
      `EVERY (\c. c <= 196607) l` by fs [] >>
      qexists `SmtStr l` >>
      simp [smtstr_rep_def] >>
      metis_tac [SmtStr_smtstr_rep])
  >- (strip_tac >>
      qexists `smtstr_rep u` >>
      simp [smtstr_rep_def])
QED

Theorem smtstr_contains_decompose:
  smtstr_contains s t <=>
    ?u v. s = smtstr_concat u (smtstr_concat t v)
Proof
  simp [smtstr_contains_def, smtstr_concat_def,
        rich_listTheory.IS_SUBLIST_APPEND] >>
  eq_tac
  >- (strip_tac >>
      `EVERY (\c. c <= 196607) (l ++ smtstr_rep t ++ l')` by
        (qpat_x_assum `smtstr_rep s = _` (SUBST1_TAC o SYM) >>
         simp []) >>
      `EVERY (\c. c <= 196607) l /\ EVERY (\c. c <= 196607) l'` by fs [] >>
      qexistsl [`SmtStr l`, `SmtStr l'`] >>
      simp [smtstr_rep_def] >>
      metis_tac [SmtStr_smtstr_rep])
  >- (strip_tac >>
      qexistsl [`smtstr_rep u`, `smtstr_rep v`] >>
      simp [smtstr_rep_def])
QED

(* TASK_02 draft_regex_membership records reflexive prefix clauses.  The
   suffix and contains variants complete the same symbolic A6 family used by
   the TASK_02 per-operator recordings. *)

Theorem smtstr_prefixof_refl:
  smtstr_prefixof s s
Proof
  simp [smtstr_prefixof_decompose] >>
  qexists `SmtStr []` >>
  simp [smtstr_concat_nil_right]
QED

Theorem smtstr_suffixof_refl:
  smtstr_suffixof s s
Proof
  simp [smtstr_suffixof_decompose] >>
  qexists `SmtStr []` >>
  simp [smtstr_concat_nil_left]
QED

Theorem smtstr_contains_refl:
  smtstr_contains s s
Proof
  simp [smtstr_contains_decompose] >>
  qexistsl [`SmtStr []`, `SmtStr []`] >>
  simp [smtstr_concat_nil_left, smtstr_concat_nil_right]
QED

(* TASK_02 draft_regex_membership repeatedly specializes prefix reasoning to
   a one-character right operand.  The implication lemmas connect the
   TASK_02 prefix/suffix recordings to their contains consequences. *)

Theorem smtstr_prefixof_singleton:
  c <= 196607 ==>
  (smtstr_prefixof s (SmtStr [c]) <=>
   s = SmtStr [] \/ s = SmtStr [c])
Proof
  strip_tac >>
  Cases_on `smtstr_rep s`
  >- fs [smtstr_prefixof_def, smtstr_rep_def, smtstr_eq_SmtStr]
  >> Cases_on `t` >>
  fs [smtstr_prefixof_def, smtstr_rep_def, smtstr_eq_SmtStr,
      rich_listTheory.IS_PREFIX]
QED

Theorem smtstr_prefixof_imp_contains:
  smtstr_prefixof s t ==> smtstr_contains t s
Proof
  simp [smtstr_prefixof_decompose, smtstr_contains_decompose] >>
  metis_tac [smtstr_concat_nil_left]
QED

Theorem smtstr_suffixof_imp_contains:
  smtstr_suffixof s t ==> smtstr_contains t s
Proof
  simp [smtstr_suffixof_decompose, smtstr_contains_decompose] >>
  metis_tac [smtstr_concat_nil_right]
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

Theorem LLEX_num_irrefl[local]:
  !l : num list. ~LLEX $< l l
Proof
  Induct >>
  simp [listTheory.LLEX_THM]
QED

Theorem LLEX_num_trichotomy[local]:
  !l1 l2 : num list. LLEX $< l1 l2 \/ l1 = l2 \/ LLEX $< l2 l1
Proof
  Induct >>
  Cases_on `l2` >>
  simp [listTheory.LLEX_THM] >>
  metis_tac [arithmeticTheory.LESS_LESS_CASES]
QED

Theorem smtstr_lt_irrefl:
  ~smtstr_lt s s
Proof
  simp [smtstr_lt_def, LLEX_num_irrefl]
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
  simp [smtstr_lt_def] >>
  metis_tac [LLEX_num_trichotomy, smtstr_rep_11]
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
    if i < 0 \/ n <= 0 \/ LENGTH (smtstr_rep s) <= Num i then 0
    else &(MIN (Num n) (LENGTH (smtstr_rep s) - Num i))
Proof
  rw [smtstr_len_def, smtstr_substr_def,
      smtstr_rep_def,
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
  smtstr_len (smtstr_substr s i n) <= &(Num n)
Proof
  rw [smtstr_len_substr] >>
  simp [arithmeticTheory.MIN_DEF]
QED

Theorem smtstr_at_in_range:
  0 <= i /\ Num i < LENGTH (smtstr_rep s) ==>
    smtstr_at s i = SmtStr [EL (Num i) (smtstr_rep s)]
Proof
  strip_tac >>
  `~(i < 0)` by intLib.ARITH_TAC >>
  fs [smtstr_at_def, smtstr_substr_def,
      smtstr_rep_def,
      listTheory.TAKE1_DROP]
QED

Theorem smtstr_len_at:
  smtstr_len (smtstr_at s i) =
    if i < 0 \/ LENGTH (smtstr_rep s) <= Num i then 0 else 1
Proof
  Cases_on `i < 0 \/ LENGTH (smtstr_rep s) <= Num i`
  >- simp [smtstr_at_def, smtstr_len_substr]
  >> fs [] >>
  `0 < LENGTH (smtstr_rep s) - Num i` by decide_tac >>
  simp [smtstr_at_def, smtstr_len_substr,
        arithmeticTheory.MIN_DEF]
QED

Theorem smtstr_len_at_bound:
  smtstr_len (smtstr_at s i) <= 1
Proof
  rw [smtstr_len_at]
QED

Theorem smtstr_at_zero:
  s = SmtStr [] \/
  smtstr_at s 0 = SmtStr [EL 0 (smtstr_rep s)]
Proof
  Cases_on `smtstr_rep s` >>
  fs [smtstr_rep_eq_nil, smtstr_at_in_range]
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
    smtstr_indexof s t i <= smtstr_len s
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
  rw [smtstr_from_code_def, smtstr_to_code_def,
      smtstr_rep_def] >>
  intLib.ARITH_TAC
QED

(* TASK_02 draft_re_comp/draft_re_loop aut.accept clauses unfold one
   character at a time.  Package the concat and star derivative equations
   at the semantic boundary used by the replay prover. *)

Theorem smt_in_re_concat:
  smt_in_re s (reglan_concat r1 r2) <=>
    ?u v.
      smt_in_re u r1 /\ smt_in_re v r2 /\
      s = smtstr_concat u v
Proof
  simp [smt_in_re_rep, re_lang_def, reglan_dot_def,
        smtstr_concat_def] >>
  eq_tac
  >- (strip_tac >>
      `EVERY (\c. c <= 196607) (x ++ y)` by
        (qpat_x_assum `smtstr_rep s = _` (SUBST1_TAC o SYM) >>
         simp []) >>
      `EVERY (\c. c <= 196607) x /\ EVERY (\c. c <= 196607) y` by fs [] >>
      qexistsl [`SmtStr x`, `SmtStr y`] >>
      simp [smtstr_rep_def] >>
      metis_tac [SmtStr_smtstr_rep])
  >- (strip_tac >>
      qexistsl [`smtstr_rep u`, `smtstr_rep v`] >>
      simp [smtstr_rep_def])
QED

Theorem smt_in_re_concat_cons:
  EVERY (\x. x <= 196607) (c::s) ==>
  (smt_in_re (SmtStr (c::s)) (reglan_concat r1 r2) <=>
   smt_in_re (SmtStr s) (reglan_concat (re_deriv c r1) r2) \/
   re_nullable r1 /\ smt_in_re (SmtStr s) (re_deriv c r2))
Proof
  strip_tac >>
  `smt_in_re (SmtStr (c::s)) (reglan_concat r1 r2) <=>
   smt_in_re (SmtStr s) (re_deriv c (reglan_concat r1 r2))` by
    simp [re_deriv_correct] >>
  pop_assum SUBST1_TAC >>
  Cases_on `re_nullable r1` >>
  simp [re_deriv_def, smt_in_re_def]
QED

Theorem smt_in_re_star_cons:
  EVERY (\x. x <= 196607) (c::s) ==>
  (smt_in_re (SmtStr (c::s)) (reglan_star r) <=>
   smt_in_re (SmtStr s)
     (reglan_concat (re_deriv c r) (reglan_star r)))
Proof
  strip_tac >>
  `smt_in_re (SmtStr (c::s)) (reglan_star r) <=>
   smt_in_re (SmtStr s) (re_deriv c (reglan_star r))` by
    simp [re_deriv_correct] >>
  pop_assum SUBST1_TAC >>
  simp [re_deriv_def]
QED

(* Ground checks pin the SMT-LIB totalization and empty-string cases. *)

Triviality smtstr_core_eval:
  smtstr_concat (SmtStr [1; 2]) (SmtStr [3]) =
    SmtStr [1; 2; 3] /\
  smtstr_len (SmtStr [10; 20; 30]) = 3 /\
  smtstr_at (SmtStr [10; 20]) (-1) = SmtStr [] /\
  smtstr_at (SmtStr [10; 20]) 0 = SmtStr [10] /\
  smtstr_at (SmtStr [10; 20]) 2 = SmtStr [] /\
  smtstr_at (SmtStr []) 0 = SmtStr [] /\
  smtstr_substr (SmtStr [10; 20; 30]) (-1) 2 = SmtStr [] /\
  smtstr_substr (SmtStr [10; 20; 30]) 1 0 = SmtStr [] /\
  smtstr_substr (SmtStr [10; 20; 30]) 1 (-1) = SmtStr [] /\
  smtstr_substr (SmtStr [10; 20; 30]) 3 1 = SmtStr [] /\
  smtstr_substr (SmtStr [10; 20; 30]) 1 5 =
    SmtStr [20; 30] /\
  smtstr_prefixof (SmtStr []) (SmtStr [1; 2]) /\
  smtstr_prefixof (SmtStr [1]) (SmtStr [1; 2]) /\
  smtstr_suffixof (SmtStr []) (SmtStr [1; 2]) /\
  smtstr_suffixof (SmtStr [2]) (SmtStr [1; 2]) /\
  smtstr_contains (SmtStr [1; 2; 3]) (SmtStr [2; 3]) /\
  smtstr_contains (SmtStr [1; 2; 3]) (SmtStr []) /\
  smtstr_indexof (SmtStr [1; 2; 1; 2]) (SmtStr [1; 2]) 1 = 2 /\
  smtstr_indexof (SmtStr [1; 2]) (SmtStr [3]) 0 = -1 /\
  smtstr_indexof (SmtStr [1; 2]) (SmtStr [1]) (-1) = -1 /\
  smtstr_indexof (SmtStr [1; 2]) (SmtStr []) 2 = 2 /\
  smtstr_indexof (SmtStr [1; 2]) (SmtStr []) 3 = -1 /\
  smtstr_indexof (SmtStr []) (SmtStr []) 0 = 0 /\
  smtstr_lt (SmtStr [1; 2]) (SmtStr [1; 3]) /\
  ~smtstr_lt (SmtStr [1; 2]) (SmtStr [1; 2]) /\
  smtstr_le (SmtStr [1; 2]) (SmtStr [1; 2]) /\
  smtstr_char 196607 = SmtStr [196607] /\
  str_inj "Az" = SmtStr [65; 122] /\
  smtstr_rep (SmtStr [196607]) = [196607]
Proof
  EVAL_TAC
QED

Triviality smtstr_a2_eval:
  smtstr_replace (SmtStr [97; 98; 99; 97; 98; 99])
    (SmtStr [98; 99]) (SmtStr [88]) =
      SmtStr [97; 88; 97; 98; 99] /\
  smtstr_replace (SmtStr [97; 98]) (SmtStr []) (SmtStr [88]) =
    SmtStr [88; 97; 98] /\
  smtstr_replace (SmtStr [97; 98]) (SmtStr [99]) (SmtStr [88]) =
    SmtStr [97; 98] /\
  smtstr_replace_all (SmtStr [97; 98; 97]) (SmtStr [97])
    (SmtStr [99]) = SmtStr [99; 98; 99] /\
  smtstr_replace_all (SmtStr [97; 98]) (SmtStr [])
    (SmtStr [99]) = SmtStr [97; 98] /\
  smtstr_replace_all (SmtStr [97; 97; 97]) (SmtStr [97; 97])
    (SmtStr [98]) = SmtStr [98; 97] /\
  smtstr_replace_re (SmtStr [97; 98])
    (reglan_union (reglan_to_re (SmtStr [97]))
                  (reglan_to_re (SmtStr [97; 98]))) (SmtStr [120]) =
    SmtStr [120; 98] /\
  smtstr_replace_re (SmtStr [97; 98])
    (reglan_union (reglan_to_re (SmtStr [98]))
                  (reglan_to_re (SmtStr [97; 98]))) (SmtStr [120]) =
    SmtStr [120] /\
  smtstr_replace_re (SmtStr [97; 98])
    (reglan_to_re (SmtStr [])) (SmtStr [120]) =
      SmtStr [120; 97; 98] /\
  smtstr_replace_re_all (SmtStr [97; 98; 97])
    (reglan_union (reglan_to_re (SmtStr []))
                  (reglan_to_re (SmtStr [97]))) (SmtStr [120]) =
    SmtStr [120; 98; 120] /\
  smtstr_replace_re_all (SmtStr [97; 98])
    (reglan_to_re (SmtStr [])) (SmtStr [120]) =
      SmtStr [97; 98] /\
  smtstr_replace_re_all (SmtStr [97; 98]) reglan_allchar
    (SmtStr [120]) = SmtStr [120; 120] /\
  smtstr_is_digit (SmtStr [48]) /\
  smtstr_is_digit (SmtStr [57]) /\
  ~smtstr_is_digit (SmtStr []) /\
  ~smtstr_is_digit (SmtStr [48; 49]) /\
  ~smtstr_is_digit (SmtStr [47]) /\
  smtstr_to_code (SmtStr [196607]) = 196607 /\
  smtstr_to_code (SmtStr []) = -1 /\
  smtstr_to_code (SmtStr [1; 2]) = -1 /\
  smtstr_from_code 0 = SmtStr [0] /\
  smtstr_from_code 196607 = SmtStr [196607] /\
  smtstr_from_code (-1) = SmtStr [] /\
  smtstr_from_code 196608 = SmtStr [] /\
  smtstr_to_int (SmtStr [48; 48; 49; 50; 51]) = 123 /\
  smtstr_to_int (SmtStr []) = -1 /\
  smtstr_to_int (SmtStr [45; 49]) = -1 /\
  smtstr_from_int 0 = SmtStr [48] /\
  smtstr_from_int 123 = SmtStr [49; 50; 51] /\
  smtstr_from_int (-123) = SmtStr [] /\
  smtstr_to_int (smtstr_from_int 9876) = 9876
Proof
  EVAL_TAC
QED

Triviality reglan_eval:
  ~smt_in_re (SmtStr []) reglan_none /\
  smt_in_re (SmtStr [1; 196607]) reglan_all /\
  smt_in_re (SmtStr [65]) reglan_allchar /\
  ~smt_in_re (SmtStr [65; 66]) reglan_allchar /\
  smt_in_re (SmtStr [1; 2]) (reglan_to_re (SmtStr [1; 2])) /\
  smt_in_re (SmtStr [66])
    (reglan_range (SmtStr [65]) (SmtStr [67])) /\
  ~smt_in_re (SmtStr [68])
    (reglan_range (SmtStr [65]) (SmtStr [67])) /\
  ~smt_in_re (SmtStr [66])
    (reglan_range (SmtStr [65; 66]) (SmtStr [67])) /\
  smt_in_re (SmtStr [1; 2])
    (reglan_concat (reglan_to_re (SmtStr [1])) (reglan_to_re (SmtStr [2]))) /\
  smt_in_re (SmtStr [2])
    (reglan_union (reglan_to_re (SmtStr [1])) (reglan_to_re (SmtStr [2]))) /\
  smt_in_re (SmtStr [2])
    (reglan_inter
       (reglan_range (SmtStr [1]) (SmtStr [3])) (reglan_range (SmtStr [2]) (SmtStr [4]))) /\
  smt_in_re (SmtStr [1])
    (reglan_diff (reglan_range (SmtStr [1]) (SmtStr [3])) (reglan_to_re (SmtStr [2]))) /\
  ~smt_in_re (SmtStr [2])
    (reglan_diff (reglan_range (SmtStr [1]) (SmtStr [3])) (reglan_to_re (SmtStr [2]))) /\
  smt_in_re (SmtStr [2]) (reglan_comp (reglan_to_re (SmtStr [1]))) /\
  ~smt_in_re (SmtStr [1]) (reglan_comp (reglan_to_re (SmtStr [1]))) /\
  smt_in_re (SmtStr [196607]) (reglan_comp reglan_none) /\
  smt_in_re (SmtStr [1; 1]) (reglan_star (reglan_to_re (SmtStr [1]))) /\
  smt_in_re (SmtStr []) (reglan_star (reglan_to_re (SmtStr [1]))) /\
  smt_in_re (SmtStr [1]) (reglan_plus (reglan_to_re (SmtStr [1]))) /\
  ~smt_in_re (SmtStr []) (reglan_plus (reglan_to_re (SmtStr [1]))) /\
  smt_in_re (SmtStr []) (reglan_opt (reglan_to_re (SmtStr [1]))) /\
  smt_in_re (SmtStr [1]) (reglan_opt (reglan_to_re (SmtStr [1]))) /\
  smt_in_re (SmtStr [1; 1])
    (reglan_power (reglan_to_re (SmtStr [1])) 2) /\
  ~smt_in_re (SmtStr [1])
    (reglan_power (reglan_to_re (SmtStr [1])) 2) /\
  smt_in_re (SmtStr [])
    (reglan_loop (reglan_to_re (SmtStr [1])) 0 0) /\
  ~smt_in_re (SmtStr [])
    (reglan_loop (reglan_to_re (SmtStr [1])) 1 0) /\
  smt_in_re (SmtStr [1])
    (reglan_loop (reglan_to_re (SmtStr [1])) 1 3) /\
  smt_in_re (SmtStr [1; 1; 1])
    (reglan_loop (reglan_to_re (SmtStr [1])) 1 3) /\
  ~smt_in_re (SmtStr [1; 1; 1; 1])
    (reglan_loop (reglan_to_re (SmtStr [1])) 1 3)
Proof
  EVAL_TAC
QED
