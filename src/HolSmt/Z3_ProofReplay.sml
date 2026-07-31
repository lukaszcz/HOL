(* Copyright (c) 2009-2011 Tjark Weber. All rights reserved. *)

(* Proof reconstruction for Z3: replaying Z3's proofs in HOL *)

structure Z3_ProofReplay =
struct

local

  open boolLib
  fun profile name f x =
    Profile.profile_with_exn_name name f x

  open Z3_Proof

  val op ++ = bossLib.++
  val op >> = Tactical.>>
  val op |-> = Lib.|->

  val ERR = Feedback.mk_HOL_ERR "Z3_ProofReplay"
  val WARNING = Feedback.HOL_WARNING "Z3_ProofReplay"

  (* An FP rewrite failure must cross the generic rewrite handlers without
     being mistaken for an invitation to try arithmetic or unification. *)
  exception FP_REWRITE_ERROR of exn

  val ALL_DISTINCT_NIL = HolSmtTheory.ALL_DISTINCT_NIL
  val ALL_DISTINCT_CONS = HolSmtTheory.ALL_DISTINCT_CONS
  val NOT_MEM_NIL = HolSmtTheory.NOT_MEM_NIL
  val NOT_MEM_CONS = HolSmtTheory.NOT_MEM_CONS
  val AND_T = HolSmtTheory.AND_T
  val T_AND = HolSmtTheory.T_AND
  val F_OR = HolSmtTheory.F_OR
  val CONJ_CONG = HolSmtTheory.CONJ_CONG
  val NOT_NOT_ELIM = HolSmtTheory.NOT_NOT_ELIM
  val NOT_NOT_INTRO = HolSmtTheory.NOT_NOT_INTRO
  val NOT_REVERSE = HolSmtTheory.NOT_REVERSE
  val NOT_FALSE = HolSmtTheory.NOT_FALSE
  val NNF_CONJ = HolSmtTheory.NNF_CONJ
  val NNF_DISJ = HolSmtTheory.NNF_DISJ
  val NNF_NOT_NOT = HolSmtTheory.NNF_NOT_NOT
  val NEG_IFF_1_1 = HolSmtTheory.NEG_IFF_1_1
  val NEG_IFF_1_2 = HolSmtTheory.NEG_IFF_1_2
  val NEG_IFF_2_1 = HolSmtTheory.NEG_IFF_2_1
  val NEG_IFF_2_2 = HolSmtTheory.NEG_IFF_2_2
  val DISJ_ELIM_1 = HolSmtTheory.DISJ_ELIM_1
  val DISJ_ELIM_2 = HolSmtTheory.DISJ_ELIM_2
  val IMP_DISJ_1 = HolSmtTheory.IMP_DISJ_1
  val IMP_DISJ_2 = HolSmtTheory.IMP_DISJ_2
  val IMP_FALSE = HolSmtTheory.IMP_FALSE
  val AND_IMP_INTRO_SYM = HolSmtTheory.AND_IMP_INTRO_SYM
  val VALID_IFF_TRUE = HolSmtTheory.VALID_IFF_TRUE

  val SIMP_PROVE_UPDATE = SmtArrayProve.simp_prove_update

  (* Instantiate `thm` (types and free variables) so its conclusion becomes
     `t`.  Fails if no such instantiation exists. *)
  fun exact_inst thm t =
    Drule.INST_TY_TERM (Term.match_term (Thm.concl thm) t) thm

  (***************************************************************************)
  (* functions that manipulate/access "global" state                         *)
  (***************************************************************************)

  type state = {
    (* keeps track of assumptions; (only) these may remain in the
       final theorem *)
    asserted_hyps : Term.term HOLset.set,
    (* keeps track of definitions introduced by Z3; these get added during the
       proof and are deleted at the end, just before returning the final theorem.
       all of them should be of the form: ``name = term`` *)
    definition_hyps : Term.term HOLset.set,
    (* stores certain theorems (proved by 'rewrite' or 'th_lemma') for
       later retrieval, to avoid re-reproving them *)
    thm_cache : Thm.thm Net.net,
    (* contains all of the variables that Z3 has defined *)
    var_set : Term.term HOLset.set,
    (* Parser-discovered FP decomposition associations.  These are hints, not
       hypotheses: rung 3 must prove a definition before adding it through
       [state_define]. *)
    bit_decompositions : bit_decomposition list,
    z3_version : string
  }

  fun state_assert (s : state) (t : Term.term) : state =
    {
      asserted_hyps = HOLset.add (#asserted_hyps s, t),
      definition_hyps = #definition_hyps s,
      thm_cache = #thm_cache s,
      var_set = #var_set s,
      bit_decompositions = #bit_decompositions s,
      z3_version = #z3_version s
    }

  fun state_define (s : state) (terms : Term.term list) : state =
    {
      asserted_hyps = #asserted_hyps s,
      definition_hyps = HOLset.addList (#definition_hyps s, terms),
      thm_cache = #thm_cache s,
      var_set = #var_set s,
      bit_decompositions = #bit_decompositions s,
      z3_version = #z3_version s
    }

  fun state_cache_thm (s : state) (thm : Thm.thm) : state =
    {
      asserted_hyps = #asserted_hyps s,
      definition_hyps = #definition_hyps s,
      thm_cache = Net.insert (Thm.concl thm, thm) (#thm_cache s),
      var_set = #var_set s,
      bit_decompositions = #bit_decompositions s,
      z3_version = #z3_version s
    }

  fun state_inst_cached_thm (s : state) (t : Term.term) : Thm.thm =
    Lib.tryfind  (* may fail *)
      (fn thm => exact_inst thm t)
      (Net.match t (#thm_cache s))

  (***************************************************************************)
  (* auxiliary functions                                                     *)
  (***************************************************************************)

  (* |- l1 \/ l2 \/ ... \/ ln \/ t   |- ~l1   |- ~l2   |- ...   |- ~ln
     -----------------------------------------------------------------
                                  |- t

     The input clause (including "t") is really treated as a set of
     literals: the resolvents need not be in the correct order, "t"
     need not be the rightmost disjunct (and if "t" is a disjunction,
     its disjuncts may even be spread throughout the input clause).
     Note also that "t" may be F, in which case it need not be present
     in the input clause.

     We treat all "~li" as atomic, even if they are negated
     disjunctions. *)
  fun unit_resolution (thms, t) =
  let
    val _ = if List.null thms then
        raise ERR "unit_resolution" ""
      else ()
    fun disjuncts dict (disj, thm) =
    let
      val (l, r) = boolSyntax.dest_disj disj
      (* |- l \/ r ==> ... *)
      val thm = Thm.DISCH disj thm
      val l_imp_concl = Thm.MP thm (Thm.DISJ1 (Thm.ASSUME l) r)
      val r_imp_concl = Thm.MP thm (Thm.DISJ2 l (Thm.ASSUME r))
    in
      disjuncts (disjuncts dict (l, l_imp_concl)) (r, r_imp_concl)
    end
    handle Feedback.HOL_ERR _ =>
      Redblackmap.insert (dict, disj, thm)
    fun prove_from_disj dict disj =
      Redblackmap.find (dict, disj)
      handle Redblackmap.NotFound =>
        let
          val (l, r) = boolSyntax.dest_disj disj
          val l_th = prove_from_disj dict l
          val r_th = prove_from_disj dict r
        in
          Thm.DISJ_CASES (Thm.ASSUME disj) l_th r_th
        end
    val dict = disjuncts (Redblackmap.mkDict Term.compare) (t, Thm.ASSUME t)
    (* derive 't' from each negated resolvent *)
    val dict = List.foldl (fn (th, dict) =>
      let
        val lit = Thm.concl th
        val (is_neg, neg_lit) = (true, boolSyntax.dest_neg lit)
          handle Feedback.HOL_ERR _ =>
            (false, boolSyntax.mk_neg lit)
        (* |- neg_lit ==> F *)
        val th = if is_neg then
            Thm.NOT_ELIM th
          else
            Thm.MP (Thm.SPEC lit NOT_FALSE) th
        (* neg_lit |- t *)
        val th = Thm.CCONTR t (Thm.MP th (Thm.ASSUME neg_lit))
      in
        Redblackmap.insert (dict, neg_lit, th)
      end) dict (List.tl thms)
    (* derive 't' from ``F`` (just in case ``F`` is a disjunct) *)
    val dict = Redblackmap.insert
      (dict, boolSyntax.F, Thm.CCONTR t (Thm.ASSUME boolSyntax.F))
    val clause = Thm.concl (List.hd thms)
    val clause_imp_t = prove_from_disj dict clause
  in
    Thm.MP (Thm.DISCH clause clause_imp_t) (List.hd thms)
  end

  (* e.g.,   "(A --> B) --> C --> D" acc   ==>   [A, B, C, D] @ acc *)
  fun strip_fun_tys ty acc =
    let
      val (dom, rng) = Type.dom_rng ty
    in
      strip_fun_tys dom (strip_fun_tys rng acc)
    end
    handle Feedback.HOL_ERR _ => ty :: acc

  (* approximate: only descends into combination terms and function types *)
  fun term_contains_real_ty tm =
    let val (rator, rand) = Term.dest_comb tm
    in
      term_contains_real_ty rator orelse term_contains_real_ty rand
    end
    handle Feedback.HOL_ERR _ =>
      List.exists (Lib.equal realSyntax.real_ty)
        (strip_fun_tys (Term.type_of tm) [])

  val type_contains = Library.type_contains  (* shared, see Library.sml *)

  fun term_contains_type pred tm =
    Lib.can (HolKernel.find_term
      (fn subtm => type_contains pred (Term.type_of subtm))) tm

  fun has_arith_atom tm =
    term_contains_type
      (fn ty =>
        Type.compare (ty, intSyntax.int_ty) = EQUAL orelse
        Type.compare (ty, realSyntax.real_ty) = EQUAL) tm

  fun has_word_atom tm =
    term_contains_type wordsSyntax.is_word_type tm

  fun is_function_type ty =
    Lib.can Type.dom_rng ty

  fun has_array_atom tm =
    Lib.can (HolKernel.find_term (fn subtm =>
      combinSyntax.is_update_comb subtm orelse
      (Term.is_comb subtm andalso
       let val rator = Lib.fst (Term.dest_comb subtm)
       in
         (Term.is_var rator andalso is_function_type (Term.type_of rator))
         orelse combinSyntax.is_update_comb rator
       end) orelse
      (Term.is_var subtm andalso is_function_type (Term.type_of subtm)))) tm

  (* returns "|- l = r", provided 'l' and 'r' are conjunctions that can be
     obtained from each other using associativity, commutativity and
     idempotence of conjunction, and identity of "T" wrt. conjunction.

     If 'r' is "F", 'l' must either contain "F" as a conjunct, or 'l'
     must contain both a literal and its negation. *)
  fun rewrite_conj (l, r) =
    let
      val Tl = boolSyntax.mk_conj (boolSyntax.T, l)
      val Tr = boolSyntax.mk_conj (boolSyntax.T, r)
      val Tl_eq_Tr = Drule.CONJUNCTS_AC (Tl, Tr)
      val p = Term.mk_var ("p", Type.bool)
      val q = Term.mk_var ("q", Type.bool)
    in
      Thm.MP (Thm.INST [p |-> l, q |-> r] T_AND) Tl_eq_Tr
    end
    handle Feedback.HOL_ERR _ =>
      if Feq r then
        let
          val l_imp_F = Thm.DISCH l (Library.gen_contradiction (Thm.ASSUME l))
        in
          Drule.EQF_INTRO (Thm.NOT_INTRO l_imp_F)
        end
      else
        raise ERR "rewrite_conj" ""

  (* returns "|- l = r", provided 'l' and 'r' are disjunctions that can be
     obtained from each other using associativity, commutativity and
     idempotence of disjunction, and identity of "F" wrt. disjunction.

     If 'r' is "T", 'l' must contain "T" as a disjunct, or 'l' must contain
     both a literal and its negation. *)
  fun rewrite_disj (l, r) =
    let
      val Fl = boolSyntax.mk_disj (boolSyntax.F, l)
      val Fr = boolSyntax.mk_disj (boolSyntax.F, r)
      val Fl_eq_Fr = Drule.DISJUNCTS_AC (Fl, Fr)
      val p = Term.mk_var ("p", Type.bool)
      val q = Term.mk_var ("q", Type.bool)
    in
      Thm.MP (Thm.INST [p |-> l, q |-> r] F_OR) Fl_eq_Fr
    end
    handle Feedback.HOL_ERR _ =>
      if Teq r then
        Drule.EQT_INTRO (Library.gen_excluded_middle l)
      else
        raise ERR "rewrite_disj" ""

  (* |- r1 /\ ... /\ rn = ~(s1 \/ ... \/ sn)

     Note that q <=> p may be negated to p <=> ~q.  Also, p <=> ~q may
     be negated to p <=> q. *)
  fun rewrite_nnf (l, r) =
  let
    val disj = boolSyntax.dest_neg r
    val conj_ths = Drule.CONJUNCTS (Thm.ASSUME l)
    (* transform equivalences in 'l' into equivalences as they appear
       in 'disj' *)
    val conj_dict = List.foldl (fn (th, dict) => Redblackmap.insert
      (dict, Thm.concl th, th)) (Redblackmap.mkDict Term.compare) conj_ths
    val var_p = Term.mk_var ("p", Type.bool)
    val var_q = Term.mk_var ("q", Type.bool)
    (* we map over equivalences in 'disj', possibly obtaining the
       negation of each one by forward reasoning from a suitable
       theorem in 'conj_dict' *)
    val iff_ths = List.mapPartial (Lib.total (fn t =>
      let
        val (p, q) = boolSyntax.dest_eq t  (* may fail *)
        val neg_q = boolSyntax.mk_neg q  (* may fail (because of type) *)
      in
        let
          val th = Redblackmap.find (conj_dict, boolSyntax.mk_eq (p, neg_q))
        in
          (* l |- ~(p <=> q) *)
          Thm.MP (Thm.INST [var_p |-> p, var_q |-> q] NEG_IFF_2_1) th
        end
        handle Redblackmap.NotFound =>
          let
            val q = boolSyntax.dest_neg q  (* may fail *)
            val th = Redblackmap.find (conj_dict, boolSyntax.mk_eq (q, p))
          in
            (* l |- ~(p <=> ~q) *)
            Thm.MP (Thm.INST [var_p |-> p, var_q |-> q] NEG_IFF_1_1) th
          end
      end)) (boolSyntax.strip_disj disj)
    (* [l, disj] |- F *)
    val F_th = unit_resolution (Thm.ASSUME disj :: conj_ths @ iff_ths,
      boolSyntax.F)
    fun disjuncts dict (thmfun, concl) =
    let
      val (l, r) = boolSyntax.dest_disj concl  (* may fail *)
    in
      disjuncts (disjuncts dict (fn th => thmfun (Thm.DISJ1 th r), l))
        (fn th => thmfun (Thm.DISJ2 l th), r)
    end
    handle Feedback.HOL_ERR _ =>  (* 'concl' is not a disjunction *)
      let
        (* |- concl ==> disjunction *)
        val th = Thm.DISCH concl (thmfun (Thm.ASSUME concl))
        (* ~disjunction |- ~concl *)
        val th = Drule.UNDISCH (Drule.CONTRAPOS th)
        val th = Thm.MP (Thm.SPEC (boolSyntax.dest_neg concl) NOT_NOT_ELIM) th
          handle Feedback.HOL_ERR _ => th
        val t = Thm.concl th
        val dict = Redblackmap.insert (dict, t, th)
      in
        (* if 't' is a negated equivalence, we check whether it can be
           transformed into an equivalence that is present in 'l' *)
        let
          val (p, q) = boolSyntax.dest_eq (boolSyntax.dest_neg t) (* may fail *)
          val neg_q = boolSyntax.mk_neg q  (* may fail (because of type) *)
        in
          let
            val _ = Redblackmap.find (conj_dict, boolSyntax.mk_eq (p, neg_q))
            (* ~disjunction |- p <=> ~q *)
            val subst = [var_p |-> p, var_q |-> q]
            val th1 = Thm.MP (Thm.INST subst NEG_IFF_2_2) th
            val dict = Redblackmap.insert (dict, Thm.concl th1, th1)
          in
            let
              val q = boolSyntax.dest_neg q  (* may fail *)
              val _ = Redblackmap.find (conj_dict, boolSyntax.mk_eq (q, p))
              (* ~disjunction |- q <=> p *)
              val subst = [var_p |-> p, var_q |-> q]
              val th1 = Thm.MP (Thm.INST subst NEG_IFF_1_2) th
            in
              Redblackmap.insert (dict, Thm.concl th1, th1)
            end
            handle Redblackmap.NotFound => dict
                 | Feedback.HOL_ERR _ => dict
          end
          handle Redblackmap.NotFound =>
            (* p <=> ~q is not a conjunction in 'l', so we skip
               deriving it; but we possibly still need to derive
               q <=> p *)
            let
              val q = boolSyntax.dest_neg q  (* may fail *)
              val _ = Redblackmap.find (conj_dict, boolSyntax.mk_eq (q, p))
              (* ~disjunction |- q <=> p *)
              val subst = [var_p |-> p, var_q |-> q]
              val th1 = Thm.MP (Thm.INST subst NEG_IFF_1_2) th
            in
              Redblackmap.insert (dict, Thm.concl th1, th1)
            end
            handle Redblackmap.NotFound => dict
                 | Feedback.HOL_ERR _ => dict
        end
        handle Feedback.HOL_ERR _ =>  (* 't' is not an equivalence *)
          dict
      end  (* disjuncts *)
    val dict = disjuncts (Redblackmap.mkDict Term.compare) (Lib.I, disj)
    (* derive ``T`` (just in case ``T`` is a conjunct) *)
    val dict = Redblackmap.insert (dict, boolSyntax.T, boolTheory.TRUTH)
    (* proves a conjunction 'conj', provided each conjunct is proved
      in 'dict' *)
    fun prove_conj dict conj =
      Redblackmap.find (dict, conj)
      handle Redblackmap.NotFound =>
        let
          val (l, r) = boolSyntax.dest_conj conj
        in
          Thm.CONJ (prove_conj dict l) (prove_conj dict r)
        end
    val r_imp_l = Thm.DISCH r (prove_conj dict l)
    val l_imp_r = Thm.DISCH l (Thm.NOT_INTRO (Thm.DISCH disj F_th))
  in
    Drule.IMP_ANTISYM_RULE l_imp_r r_imp_l
  end

  (* returns |- ~MEM x [a; b; c] = x <> a /\ x <> b /\ x <> c; fails
     if not applied to a term of the form ``~MEM x [a; b; c]`` *)
  fun NOT_MEM_CONV tm =
  let
    val (x, list) = listSyntax.dest_mem (boolSyntax.dest_neg tm)
  in
    let
      val (h, t) = listSyntax.dest_cons list
      (* |- ~MEM x (h::t) = (x <> h) /\ ~MEM x t *)
      val th1 = Drule.ISPECL [x, h, t] NOT_MEM_CONS
      val (neq, notmem) = boolSyntax.dest_conj (boolSyntax.rhs
        (Thm.concl th1))
      (* |- ~MEM x t = rhs *)
      val th2 = NOT_MEM_CONV notmem
      (* |- (x <> h) /\ ~MEM x t = (x <> h) /\ rhs *)
      val th3 = Thm.AP_TERM (Term.mk_comb (boolSyntax.conjunction, neq)) th2
      (* |- ~MEM x (h::t) = (x <> h) /\ rhs *)
      val th4 = Thm.TRANS th1 th3
    in
      if Teq (boolSyntax.rhs (Thm.concl th2)) then
        Thm.TRANS th4 (Thm.SPEC neq AND_T)
      else
        th4
    end
    handle Feedback.HOL_ERR _ =>  (* 'list' is not a cons *)
      if listSyntax.is_nil list then
        (* |- ~MEM x [] = T *)
        Drule.ISPEC x NOT_MEM_NIL
      else
        raise ERR "NOT_MEM_CONV" ""
  end

  (* returns "|- ALL_DISTINCT [x; y; z] = (x <> y /\ x <> z) /\ y <>
     z" (note the parentheses); fails if not applied to a term of the
     form ``ALL_DISTINCT [x; y; z]`` *)
  fun ALL_DISTINCT_CONV tm =
  let
    val list = listSyntax.dest_all_distinct tm
  in
    let
      val (h, t) = listSyntax.dest_cons list
      (* |- ALL_DISTINCT (h::t) = ~MEM h t /\ ALL_DISTINCT t *)
      val th1 = Drule.ISPECL [h, t] ALL_DISTINCT_CONS
      val (notmem, alldistinct) = boolSyntax.dest_conj
        (boolSyntax.rhs (Thm.concl th1))
      (* |- ~MEM h t = something *)
      val th2 = NOT_MEM_CONV notmem
      val something = boolSyntax.rhs (Thm.concl th2)
      (* |- ALL_DISTINCT t = rhs *)
      val th3 = ALL_DISTINCT_CONV alldistinct
      val rhs = boolSyntax.rhs (Thm.concl th3)
      val var_names = ["p", "q", "r", "s"]
      val redexes = List.map (fn v => Term.mk_var (v, Type.bool)) var_names
      val residues = [notmem, something, alldistinct, rhs]
      val substs = List.map Lib.|-> (ListPair.zip (redexes, residues))
      val th4 = Thm.INST substs CONJ_CONG
      (* |- ~MEM h t /\ ALL_DISTINCT t = something /\ rhs *)
      val th5 = Thm.MP (Thm.MP th4 th2) th3
      (* |- ALL_DISTINCT (h::t) = something /\ rhs *)
      val th6 = Thm.TRANS th1 th5
    in
      if Teq rhs then Thm.TRANS th6 (Thm.SPEC something AND_T)
      else th6
    end
    handle Feedback.HOL_ERR _ =>  (* 'list' is not a cons *)
      (* |- ALL_DISTINCT [] = T *)
      Thm.INST_TYPE [Type.alpha |-> listSyntax.dest_nil list]
        ALL_DISTINCT_NIL
  end

  (* returns |- (x = y) = (y = x), provided ``y = x`` is LESS than ``x
     = y`` wrt. Term.compare; fails if applied to a term that is not
     an equation; may raise Conv.UNCHANGED *)
  fun REORIENT_SYM_CONV tm =
  let
    val tm' = boolSyntax.mk_eq (Lib.swap (boolSyntax.dest_eq tm))
  in
    if Term.compare (tm', tm) = LESS then
      Conv.SYM_CONV tm
    else
      raise Conv.UNCHANGED
  end

  (* returns |- ALL_DISTINCT ... /\ T = ... *)
  fun rewrite_all_distinct (l, r) =
  let
    fun ALL_DISTINCT_AND_T_CONV t =
      ALL_DISTINCT_CONV t
        handle Feedback.HOL_ERR _ =>
          let
            val all_distinct = Lib.fst (boolSyntax.dest_conj t)
            val all_distinct_th = ALL_DISTINCT_CONV all_distinct
          in
            Thm.TRANS (Thm.SPEC all_distinct AND_T) all_distinct_th
          end
    val REORIENT_CONV = Conv.ONCE_DEPTH_CONV REORIENT_SYM_CONV
    (* since ALL_DISTINCT may be present in both 'l' and 'r', we
       normalize both 'l' and 'r' *)
    val l_eq_l' = Conv.THENC (ALL_DISTINCT_AND_T_CONV, REORIENT_CONV) l
    val r_eq_r' = Conv.THENC (fn t => ALL_DISTINCT_AND_T_CONV t
      handle Feedback.HOL_ERR _ => raise Conv.UNCHANGED, REORIENT_CONV) r
      handle Conv.UNCHANGED => Thm.REFL r
    (* get rid of parentheses *)
    val l'_eq_r' = Drule.CONJUNCTS_AC (boolSyntax.rhs (Thm.concl l_eq_l'),
      boolSyntax.rhs (Thm.concl r_eq_r'))
  in
    Thm.TRANS (Thm.TRANS l_eq_l' l'_eq_r') (Thm.SYM r_eq_r')
  end

  (* Returns a proof of `t` given a list of theorems as inputs. It relies on
     `metisLib.METIS_TAC` to find a proof. The returned theorem will have as
     hypotheses all the hypotheses of all the input theorems. *)
  fun metis_prove (thms, t) =
  let
    (* Gather all the hypotheses of all theorems together into a set of
       assumptions *)
    fun join_fn (thm, asm_set) = HOLset.union (asm_set, Thm.hypset thm)
    val asms = List.foldl join_fn Term.empty_tmset thms
  in
    Tactical.TAC_PROOF ((HOLset.listItems asms, t), metisLib.METIS_TAC thms)
  end

  val nnf_rewrites = [
    boolTheory.DE_MORGAN_THM,
    boolTheory.NOT_IMP,
    boolTheory.IMP_DISJ_THM,
    boolTheory.NOT_FORALL_THM,
    boolTheory.NOT_EXISTS_THM,
    boolTheory.NOT_CLAUSES,
    boolTheory.AND_CLAUSES,
    boolTheory.OR_CLAUSES,
    boolTheory.IMP_CLAUSES,
    boolTheory.EQ_CLAUSES
  ]

  fun nnf_structural_prove (thms, t) =
  let
    fun join_fn (thm, asm_set) = HOLset.union (asm_set, Thm.hypset thm)
    val asms = List.foldl join_fn Term.empty_tmset thms
    fun is_refl_eq thm =
      let val (l, r) = boolSyntax.dest_eq (Thm.concl thm)
      in l ~~ r end
      handle Feedback.HOL_ERR _ => false
    val rewrite_thms = List.filter (not o is_refl_eq) thms
    fun oriented_premise thm =
      if Thm.concl thm ~~ t then
        thm
      else
        let
          val (tl, tr) = boolSyntax.dest_eq t
          val (cl, cr) = boolSyntax.dest_eq (Thm.concl thm)
        in
          if tl ~~ cr andalso tr ~~ cl then Thm.SYM thm
          else raise ERR "nnf_structural_prove" "premise does not match"
        end
    fun reflexive_target () =
      let val (l, r) = boolSyntax.dest_eq t
      in Thm.ALPHA l r end
  in
    Lib.tryfind oriented_premise thms
    handle Feedback.HOL_ERR _ =>
    reflexive_target ()
    handle Feedback.HOL_ERR _ =>
    Tactical.TAC_PROOF ((HOLset.listItems asms, t),
      PURE_REWRITE_TAC (rewrite_thms @ nnf_rewrites) THEN
      bossLib.SIMP_TAC bossLib.bool_ss (rewrite_thms @ nnf_rewrites) THEN
      tautLib.TAUT_TAC)
  end

  fun nnf_prove (thms, t) =
    profile "nnf[structural]" nnf_structural_prove (thms, t)
    handle Feedback.HOL_ERR _ =>
      profile "nnf[metis-fallback]" metis_prove (thms, t)

  val INT_LE_RMUL_EXP = Tactical.prove(
    ``!a b n:int. 0 <= n ==> a <= b ==> a * n <= b * n``,
    REPEAT STRIP_TAC THEN
    bossLib.Cases_on `n = 0` THENL [
      bossLib.ASM_SIMP_TAC intLib.int_ss [],
      SUBGOAL_THEN ``0i < n`` ASSUME_TAC THENL [intLib.ARITH_TAC, ALL_TAC] THEN
      bossLib.Cases_on `a = b` THENL [
        bossLib.ASM_SIMP_TAC intLib.int_ss [],
        SUBGOAL_THEN ``a < b:int`` ASSUME_TAC THENL
          [intLib.ARITH_TAC, ALL_TAC] THEN
        Tactic.MP_TAC (Q.SPECL [`a:int`, `b:int`, `n:int`]
          intExtensionTheory.INT_LT_RMUL_EXP) THEN
        intLib.ARITH_TAC
      ]
    ])

  val INT_LE_LMUL_EXP = Tactical.prove(
    ``!a b n:int. 0 <= n ==> a <= b ==> n * a <= n * b``,
    metisLib.METIS_TAC [INT_LE_RMUL_EXP, integerTheory.INT_MUL_COMM])

  val INT_LE_MUL2 = Tactical.prove(
    ``!x1 x2 y1 y2:int.
        0 <= x1 /\ 0 <= y1 /\ x1 <= x2 /\ y1 <= y2 ==>
        x1 * y1 <= x2 * y2``,
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN ``x1 * y1 <= x2 * y1:int`` ASSUME_TAC THENL
      [metisLib.METIS_TAC [INT_LE_RMUL_EXP], ALL_TAC] THEN
    SUBGOAL_THEN ``x2 * y1 <= x2 * y2:int`` ASSUME_TAC THENL
      [metisLib.METIS_TAC [INT_LE_LMUL_EXP, integerTheory.INT_LE_TRANS],
       ALL_TAC] THEN
    metisLib.METIS_TAC [integerTheory.INT_LE_TRANS])

  fun int_product_bound_tac (asl, w) =
  let
    fun dest_not_leq_mult tm =
      let
        val (_, product) = intSyntax.dest_leq (boolSyntax.dest_neg tm)
        val (x, y) = intSyntax.dest_mult product
      in
        (x, y)
      end
    fun dest_lower_bound tm = SOME (intSyntax.dest_leq tm)
      handle Feedback.HOL_ERR _ => NONE
    fun lower_bounds_for x =
      List.mapPartial (fn tm =>
        case dest_lower_bound tm of
          SOME (lower, upper) => if upper ~~ x then SOME lower else NONE
        | NONE => NONE) asl
    fun candidate_tacs (x, y) =
      List.concat (map (fn x_lower =>
        map (fn y_lower =>
          Tactic.MP_TAC (Drule.SPECL [x_lower, x, y_lower, y] INT_LE_MUL2) THEN
          bossLib.FULL_SIMP_TAC
            (bossLib.arith_ss ++ intSimps.INT_RWTS_ss ++
             intSimps.INT_ARITH_ss) [] THEN
          intLib.ARITH_TAC) (lower_bounds_for y)) (lower_bounds_for x))
    val tacs = List.concat (List.mapPartial (fn tm =>
      SOME (candidate_tacs (dest_not_leq_mult tm))
      handle Feedback.HOL_ERR _ => NONE) asl)
    fun first [] _ = raise ERR "int_product_bound_tac"
      ("failed: " ^ Hol_pp.term_to_string w)
      | first (tac :: tacs) goal =
          tac goal handle Feedback.HOL_ERR _ => first tacs goal
  in
    first tacs (asl, w)
  end

  fun int_product_prove t =
    Tactical.TAC_PROOF (([], t),
      PURE_REWRITE_TAC [integerTheory.INT_GE] THEN
      (metisLib.METIS_TAC
         [integerTheory.INT_LE_MUL, integerTheory.INT_LE_SQUARE, INT_LE_MUL2]
       ORELSE
       REPEAT STRIP_TAC THEN int_product_bound_tac))

  val REAL_ZERO_FACTOR_NONNEG = Tactical.prove(
    ``!x:real. !y:real. x <= 0 ==> x >= 0 ==> 0 <= x * y``,
    Tactical.REPEAT STRIP_TAC THEN
    Tactic.MP_TAC
      (RealField.REAL_ARITH ``x >= 0:real ==> x <= 0 ==> x = 0``) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_TAC THEN
    ASM_REWRITE_TAC
      [realTheory.REAL_MUL_LZERO, realTheory.REAL_LE_REFL])

  val REAL_ZERO_FACTOR_NONNEG_CLAUSE = Tactical.prove(
    ``!x:real. !y:real. 0 <= x * y \/ ~(x <= 0) \/ ~(x >= 0)``,
    metisLib.METIS_TAC [REAL_ZERO_FACTOR_NONNEG])

  fun real_zero_factor_clause_prove t =
  let
    fun strip_disj tm =
      let val (l, r) = boolSyntax.dest_disj tm
      in l :: strip_disj r end
      handle Feedback.HOL_ERR _ => [tm]

    fun is_real_zero tm = tm ~~ realSyntax.zero_tm

    fun dest_nonneg_product lit =
      let
        val (l, r) = realSyntax.dest_leq lit
      in
        if is_real_zero l then realSyntax.dest_mult r
        else raise ERR "dest_nonneg_product" ""
      end
      handle Feedback.HOL_ERR _ =>
      let
        val (l, r) = realSyntax.dest_geq lit
      in
        if is_real_zero r then realSyntax.dest_mult l
        else raise ERR "dest_nonneg_product" ""
      end

    fun dest_neg_le_zero lit =
      let
        val (l, r) = realSyntax.dest_leq (boolSyntax.dest_neg lit)
      in
        if is_real_zero r then SOME l else NONE
      end
      handle Feedback.HOL_ERR _ =>
      let
        val (l, r) = realSyntax.dest_geq (boolSyntax.dest_neg lit)
      in
        if is_real_zero l then SOME r else NONE
      end
      handle Feedback.HOL_ERR _ => NONE

    fun dest_neg_ge_zero lit =
      let
        val (l, r) = realSyntax.dest_geq (boolSyntax.dest_neg lit)
      in
        if is_real_zero r then SOME l else NONE
      end
      handle Feedback.HOL_ERR _ =>
      let
        val (l, r) = realSyntax.dest_leq (boolSyntax.dest_neg lit)
      in
        if is_real_zero l then SOME r else NONE
      end
      handle Feedback.HOL_ERR _ => NONE

    val lits = strip_disj t
    val le_zero_vars = List.mapPartial dest_neg_le_zero lits
    val ge_zero_vars = List.mapPartial dest_neg_ge_zero lits

    fun find_bound_pair x =
      List.exists (fn y => x ~~ y) le_zero_vars andalso
      List.exists (fn y => x ~~ y) ge_zero_vars

    fun prove_for_factor (x, y) =
      if find_bound_pair x then
        let
          val thm = Drule.SPECL [x, y] REAL_ZERO_FACTOR_NONNEG_CLAUSE
        in
          metis_prove ([thm, realTheory.real_ge, realTheory.REAL_MUL_COMM], t)
        end
      else
        raise ERR "real_zero_factor_clause_prove" ""

    fun prove_from_lit lit =
      let
        val (l, r) = dest_nonneg_product lit
      in
        prove_for_factor (l, r)
        handle Feedback.HOL_ERR _ => prove_for_factor (r, l)
      end
  in
    Lib.tryfind prove_from_lit lits
  end

  (* `ediv 0 j` sign facts.  The `0i < j` split proves the two `j >= 0`
     clauses; the `j <= 0i` split with the positive-`j` subgoal proves the
     two `j <= 0` clauses. *)
  val ediv_pos_split_tac =
    GEN_TAC THEN Tactic.ASM_CASES_TAC ``0i < j`` THENL [
      intLib.ARITH_TAC,
      Tactic.ASM_CASES_TAC ``j = 0i`` THENL [
        intLib.ARITH_TAC,
        bossLib.ASM_SIMP_TAC intLib.int_ss
          [integerTheory.EDIV_DEF, integerTheory.INT_DIV_0]
      ]
    ]

  val ediv_nonpos_split_tac =
    GEN_TAC THEN Tactic.ASM_CASES_TAC ``j <= 0i`` THENL [
      intLib.ARITH_TAC,
      SUBGOAL_THEN ``0i < j /\ j <> 0i`` STRIP_ASSUME_TAC THENL [
        intLib.ARITH_TAC,
        bossLib.ASM_SIMP_TAC intLib.int_ss
          [integerTheory.EDIV_DEF, integerTheory.INT_DIV_0]
      ]
    ]

  (* `emod 0 j` sign facts; both clauses share the same case split. *)
  val emod_split_tac =
    GEN_TAC THEN Tactic.ASM_CASES_TAC ``j <= 0i`` THENL [
      intLib.ARITH_TAC,
      SUBGOAL_THEN ``0i < j /\ ~(j < 0i) /\ j <> 0i``
        STRIP_ASSUME_TAC THENL [
        intLib.ARITH_TAC,
        bossLib.ASM_SIMP_TAC intLib.int_ss
          [integerTheory.EMOD_DEF, integerTheory.INT_ABS,
           integerTheory.INT_MOD0]
      ]
    ]

  val EDIV_ZERO_SIGN_CLAUSE = Tactical.prove(
    ``!j:int. j >= 0 \/ ediv 0 j <= 0``, ediv_pos_split_tac)

  val EDIV_ZERO_GE_CLAUSE = Tactical.prove(
    ``!j:int. j >= 0 \/ ediv 0 j >= 0``, ediv_pos_split_tac)

  val EDIV_ZERO_NONPOS_CLAUSE = Tactical.prove(
    ``!j:int. j <= 0 \/ ediv 0 j <= 0``, ediv_nonpos_split_tac)

  val EDIV_ZERO_NONNEG_CLAUSE = Tactical.prove(
    ``!j:int. j <= 0 \/ ediv 0 j >= 0``, ediv_nonpos_split_tac)

  val EMOD_ZERO_SIGN_CLAUSE = Tactical.prove(
    ``!j:int. j <= 0 \/ emod 0 j >= 0``, emod_split_tac)

  val EMOD_ZERO_NONPOS_CLAUSE = Tactical.prove(
    ``!j:int. j <= 0 \/ emod 0 j <= 0``, emod_split_tac)

  val SMT_RDIV_CANCEL_CLAUSE = Tactical.prove(
    ``(y:real) = 0 \/ x = y * HolSmt$smt_rdiv x y``,
    Tactic.ASM_CASES_TAC ``(y:real) = 0`` THENL [
      ASM_REWRITE_TAC [],
      bossLib.ASM_SIMP_TAC (bossLib.srw_ss())
        [HolSmtTheory.smt_rdiv_eq_div, realTheory.REAL_DIV_LMUL]
    ])

  val SMT_RDIV_INTRO_CANCEL_CLAUSE = Tactical.prove(
    ``HolSmt$smt_rdiv (x:real) y = k ==>
      y = 0 \/ y * k = x``,
    bossLib.METIS_TAC [SMT_RDIV_CANCEL_CLAUSE])

  (* Returns a proof of `t` using arithmetic decision procedures. This function
     is used by both `z3_th_lemma_arith` and `z3_rewrite`. *)
  fun arith_prove t =
    exact_inst SMT_RDIV_INTRO_CANCEL_CLAUSE t
    handle Feedback.HOL_ERR _ =>
    exact_inst SMT_RDIV_CANCEL_CLAUSE t
    handle Feedback.HOL_ERR _ =>
    arith_prove_smt_rdiv t
    handle Feedback.HOL_ERR _ =>
    arith_prove_linear t
    handle Feedback.HOL_ERR _ =>
    int_product_prove t
    handle Feedback.HOL_ERR _ =>
    real_zero_factor_clause_prove t
    handle Feedback.HOL_ERR _ =>
      (* nonlinear fallback: only after linear tactics fail, to avoid
         expensive SOS certificate search on goals linear tactics handle *)
      if Library.is_nonlinear t then
        profile "arith_prove(nla)" Library.nla_prove t
      else raise ERR "arith_prove" (Hol_pp.term_to_string t)

  and arith_prove_smt_rdiv t =
    let
      val t_eq_t' =
        simpLib.SIMP_CONV (bossLib.srw_ss())
          [HolSmtTheory.smt_rdiv_eq_div] t
        handle Conv.UNCHANGED => Thm.REFL t
      val t' = boolSyntax.rhs (Thm.concl t_eq_t')
    in
      if Term.aconv t t' then
        raise ERR "arith_prove_smt_rdiv" "no concrete division normalization"
      else
        Thm.EQ_MP (Thm.SYM t_eq_t') (arith_prove_linear t')
    end

  and arith_prove_linear t =
    let
      fun arith_tactic (goal as (_, term)) =
        if term_contains_real_ty term then
          profile "arith_prove(real)" RealField.REAL_ARITH_TAC goal
        else
          profile "arith_prove(int)" intLib.ARITH_TAC goal
      val TRY = Tactical.TRY
      val ap_tactic =
        TRY AP_TERM_TAC >> TRY arith_tactic
        >> TRY AP_THM_TAC >> TRY arith_tactic
    in
      Tactical.TAC_PROOF (([], t),
        (* rewrite the `ediv` and `emod` symbols so that the arithmetic
           decision procedures can solve terms containing these functions *)
        PURE_REWRITE_TAC[EDIV_ZERO_SIGN_CLAUSE, EDIV_ZERO_GE_CLAUSE,
          EDIV_ZERO_NONPOS_CLAUSE, EDIV_ZERO_NONNEG_CLAUSE,
          EMOD_ZERO_SIGN_CLAUSE,
          EMOD_ZERO_NONPOS_CLAUSE, integerTheory.EDIV_DEF,
          integerTheory.EMOD_DEF]
        (* the next rewrites are a workaround for this issue:
           https://github.com/HOL-Theorem-Prover/HOL/issues/1207 *)
        >> PURE_REWRITE_TAC[integerTheory.INT_ABS, integerTheory.NUM_OF_INT]
        >> TRY arith_tactic
        >> bossLib.RW_TAC (bossLib.arith_ss ++ intSimps.INT_RWTS_ss ++
             intSimps.INT_ARITH_ss ++ realSimps.REAL_ARITH_ss)
               [Conv.GSYM integerTheory.INT_NEG_MINUS1]
        >> TRY arith_tactic
        >> Tactical.rpt (Tactical.CHANGED_TAC ap_tactic)
        >> Tactic.CONV_TAC (bossLib.EVALn 1000000)
        >> TRY arith_tactic)
    end

  (***************************************************************************)
  (* implementation of Z3's inference rules                                  *)
  (***************************************************************************)

  (* The Z3 documentation is rather outdated (as of version 2.11) and
     imprecise with respect to the semantics of Z3's inference rules.
     Ultimately, the most reliable way to determine the semantics is
     by observation: I applied Z3 to a large collection of SMT-LIB
     benchmarks, and from the resulting proofs I inferred what each
     inference rule does.  Therefore the implementation below may not
     cover rare corner cases that were not exercised by any benchmark
     in the collection. *)

  fun z3_and_elim (state, thm, t) =
    (state, Library.conj_elim (thm, t))

  fun z3_asserted (state, t) =
    (state_assert state t, Thm.ASSUME t)

  fun z3_commutativity (state, t) =
  let
    val (x, y) = boolSyntax.dest_eq (boolSyntax.lhs t)
  in
    (state, Drule.ISPECL [x, y] boolTheory.EQ_SYM_EQ)
  end

  (* Instances of Tseitin-style propositional tautologies:
     (or (not (and p q)) p)
     (or (not (and p q)) q)
     (or (and p q) (not p) (not q))
     (or (not (or p q)) p q)
     (or (or p q) (not p))
     (or (or p q) (not q))
     (or (not (iff p q)) (not p) q)
     (or (not (iff p q)) p (not q))
     (or (iff p q) (not p) (not q))
     (or (iff p q) p q)
     (or (not (ite a b c)) (not a) b)
     (or (not (ite a b c)) a c)
     (or (ite a b c) (not a) (not b))
     (or (ite a b c) a (not c))
     (or (not (not a)) (not a))
     (or (not a) a)

     Also
     (or p (= x (ite p y x)))

     Also
     ~ALL_DISTINCT [x; y; z] \/ (x <> y /\ x <> z /\ y <> z)
     ~(ALL_DISTINCT [x; y; z] /\ T) \/ (x <> y /\ x <> z /\ y <> z)

     There is a complication: 't' may contain arbitarily many
     irrelevant (nested) conjuncts/disjuncts, i.e.,
     conjunction/disjunction in the above tautologies can be of
     arbitrary arity.

     For the most part, 'z3_def_axiom' could be implemented by a
     single call to TAUT_PROVE.  The (partly less general)
     implementation below, however, is considerably faster.
  *)
  fun z3_def_axiom (state, t) =
    (state, Z3_ProformaThms.prove Z3_ProformaThms.def_axiom_thms t)
    handle Feedback.HOL_ERR _ =>
    (* or (or ... p ...) (not p) *)
    (* or (or ... (not p) ...) p *)
    (state, Library.gen_excluded_middle t)
    handle Feedback.HOL_ERR _ =>
    (* (or (not (and ... p ...)) p) *)
    let
      val (lhs, rhs) = boolSyntax.dest_disj t
      val conj = boolSyntax.dest_neg lhs
      (* conj |- rhs *)
      val thm = Library.conj_elim (Thm.ASSUME conj, rhs)  (* may fail *)
    in
      (* |- lhs \/ rhs *)
      (state, Drule.IMP_ELIM (Thm.DISCH conj thm))
    end
    handle Feedback.HOL_ERR _ =>
    (* ~ALL_DISTINCT [x; y; z] \/ x <> y /\ x <> z /\ y <> z *)
    (* ~(ALL_DISTINCT [x; y; z] /\ T) \/ x <> y /\ x <> z /\ y <> z *)
    let
      val (l, r) = boolSyntax.dest_disj t
      val all_distinct = boolSyntax.dest_neg l
      val all_distinct_th = ALL_DISTINCT_CONV all_distinct
        handle Feedback.HOL_ERR _ =>
          let
            val all_distinct = Lib.fst (boolSyntax.dest_conj all_distinct)
            val all_distinct_th = ALL_DISTINCT_CONV all_distinct
          in
            Thm.TRANS (Thm.SPEC all_distinct AND_T) all_distinct_th
          end
      (* get rid of parentheses *)
      val l_eq_r = Thm.TRANS all_distinct_th (Drule.CONJUNCTS_AC
        (boolSyntax.rhs (Thm.concl all_distinct_th), r))
    in
      (state, Drule.IMP_ELIM (Lib.fst (Thm.EQ_IMP_RULE l_eq_r)))
    end

  (* (!x. ?y. !z. P) = P *)
  fun z3_elim_unused (state, t) =
  let
    val (lhs, rhs) = boolSyntax.dest_eq t
    fun get_forall_thms term : term * thm * thm =
    let
      val (var, body) = boolSyntax.dest_forall term
      val th1 = Thm.DISCH term (Thm.SPEC var (Thm.ASSUME term))
      val th2 = Thm.DISCH body (Thm.GEN var (Thm.ASSUME body))
    in
      (body, th1, th2)
    end
    fun get_exists_thms term : term * thm * thm =
    let
      val (var, body) = boolSyntax.dest_exists term
      val th1 = Thm.DISCH term (Thm.CHOOSE (var, Thm.ASSUME term)
        (Thm.ASSUME body))
      val th2 = Thm.DISCH body (Thm.EXISTS (term, var) (Thm.ASSUME body))
    in
      (body, th1, th2)
    end
    fun strip_some_quants term =
    let
      val (body, th1, th2) =
        if boolSyntax.is_forall term then
          get_forall_thms term
        else
          get_exists_thms term
      val strip_th = Drule.IMP_ANTISYM_RULE th1 th2
    in
      if body ~~ rhs then
        strip_th  (* stripped enough quantifiers *)
      else
        Thm.TRANS strip_th (strip_some_quants body)
      end
  in
    (state, strip_some_quants lhs)
  end

  (* introduces a local hypothesis (which must be discharged by
     'z3_lemma' at some later point in the proof) *)
  fun z3_hypothesis (state, t) =
      (state, Thm.ASSUME t)

  (* `apply-def` unfolds a name introduced by `intro-def`.

     Z3 documents this rule as deriving ``F ~ n`` from a proof that ``n`` is a
     name for ``F``.  This parser represents equivalence modulo naming (``~``)
     as HOL equality, and `z3_intro_def` records the underlying definitional
     equality as a hypothesis. *)
  fun z3_apply_def (state, thm, t) =
  let
    fun oriented_def def =
      let
        val def_thm = Thm.ASSUME def
      in
        if Thm.concl def_thm ~~ t then
          def_thm
        else
          let val sym_def_thm = Thm.SYM def_thm
          in
            if Thm.concl sym_def_thm ~~ t then
              sym_def_thm
            else
              raise ERR "z3_apply_def" "definition has wrong orientation"
          end
      end
    val def_thm = Lib.tryfind oriented_def (HOLset.listItems (Thm.hypset thm))
  in
    (state, def_thm)
  end

  (*   ... |- ~p
     ------------
     ... |- p = F *)
  fun z3_iff_false (state, thm, _) =
    (state, Drule.EQF_INTRO thm)

  (*   ... |- p
     ------------
     ... |- p = T *)
  fun z3_iff_true (state, thm, _) =
    (state, Thm.MP (Thm.SPEC (Thm.concl thm) VALID_IFF_TRUE) thm)

  (* `intro-def` introduces a name for a term.

     `t` will be in one of the following schematic forms:

     1. name = term

     2. ~name \/ term

     3. (name \/ ~term) /\ (~name \/ term)

     ... or, when the term is of the form `if cond then t1 else t2`:

     4. (~cond \/ (name = t1)) /\ (cond \/ (name = t2))

     We then instantiate the following theorem:

     name = term |- t

     The introduced assumption is added to a set of hypotheses (i.e. the set
     of introduced definitions) stored in `state`. Since the variable names
     used in these definitions are local names introduced by Z3 for the
     purposes of completing the proof and should not otherwise be relevant in
     either the remaining hypotheses or the conclusion of the final theorem,
     we can remove all such definitions at the end of the proof.

     We must take an additional precaution: if `term` is a Z3-defined variable
     and it is "smaller" than `name`, then we must actually return the theorem:

     term = name |- t

     This is done to avoid ending up with circular definitions in the final
     theorem. *)

  fun z3_intro_def_proforma (state, t) =
  let
    val thm =
      case Net.match t Z3_ProformaThms.intro_def_thms of
        thm :: _ => thm
      | [] => raise ERR "z3_intro_def_proforma"
          "unsupported intro-def shape"
    val substs = Term.match_term (Thm.concl thm) t
    val term_substs = Lib.fst substs
    (* Check if the hypothesis should be changed from `name = term` to
       `term = name`. Note that `name` and `term` are actually called `n` and
       `t` in `intro_def_thms`, except for the 4th schematic form which doesn't
       have `t` (nor does it need to be oriented). *)
    fun is_varname s tm = Lib.fst (Term.dest_var tm) = s
    val name = Option.valOf (Lib.subst_assoc (is_varname "n") term_substs)
    val term_opt = Lib.subst_assoc (is_varname "t") term_substs
    val is_oriented =
      case term_opt of
        NONE => true (* `term_opt` will be NONE in the 4th schematic form *)
      | SOME term => Library.is_def_oriented (#var_set state) (name, term)
    (* Orient the hypothesis if necessary *)
    val thm = if is_oriented then thm else
      Conv.HYP_CONV_RULE (fn _ => true) Conv.SYM_CONV thm
    val inst_thm = Drule.INST_TY_TERM substs thm
    val asl = Thm.hyp inst_thm
  in
    (state_define state asl, inst_thm)
  end

  (* A :lambda-def axiom is printed pointwise, while replay records the
     underlying function definition.  HOL's first-order matcher deliberately
     refuses to instantiate a schematic function with a term containing the
     matched binder, so derive these C1-observed one- and two-binder forms
     explicitly.  Repeated AP_THM followed by beta is the kernel derivation
     underlying the corresponding FUN_EQ_THM instance. *)
  fun z3_intro_def_lambda (state, t) =
  let
    val _ = if List.null (Net.match t Z3_ProformaThms.intro_def_thms)
      then raise ERR "z3_intro_def_lambda"
        "unsupported :lambda-def intro-def shape"
      else ()
    val (vars, body) = boolSyntax.strip_forall t
    val _ = if List.length vars = 1 orelse List.length vars = 2 then ()
      else raise ERR "z3_intro_def_lambda"
        "unsupported :lambda-def binder count"
    val (lhs, rhs) = boolSyntax.dest_eq body
    fun named_application side =
      let
        val (name, args) = strip_comb side
      in
        if Term.is_var name andalso
           HOLset.member (#var_set state, name) andalso
           Lib.list_eq Term.aconv args vars
        then SOME name
        else NONE
      end
    val (name, term, name_on_left) =
      case (named_application lhs, named_application rhs) of
        (SOME name, _) => (name, rhs, true)
      | (_, SOME name) => (name, lhs, false)
      | _ => raise ERR "z3_intro_def_lambda"
          "pointwise axiom does not define a Z3 name"
    val residue = Term.list_mk_abs (vars, term)
    val def = boolSyntax.mk_eq (name, residue)
    val def_thm = Thm.ASSUME def
    val applied = List.foldl (fn (var, thm) => Thm.AP_THM thm var)
      def_thm vars
    val applied_rhs = Lib.snd (boolSyntax.dest_eq (Thm.concl applied))
    val beta = Conv.TOP_DEPTH_CONV Thm.BETA_CONV applied_rhs
    val pointwise = Thm.TRANS applied beta
    val pointwise = if name_on_left then pointwise else Thm.SYM pointwise
    val inst_thm = List.foldr (fn (var, thm) => Thm.GEN var thm)
      pointwise vars
    val _ = if Thm.concl inst_thm ~~ t then ()
      else raise ERR "z3_intro_def_lambda"
        "derived :lambda-def has the wrong conclusion"
  in
    (state_define state [def], inst_thm)
  end

  fun z3_intro_def (args as (_, t)) =
    if boolSyntax.is_forall t then z3_intro_def_lambda args
    else z3_intro_def_proforma args

  (*  [l1, ..., ln] |- F
     --------------------
     |- ~l1 \/ ... \/ ~ln

     'z3_lemma' could be implemented (essentially) by a single call to
     'TAUT_PROVE'.  The (less general) implementation below, however,
     is considerably faster. *)
  fun z3_lemma (state, thm, t) =
  let
    fun prove_literal maybe_no_hyp (th, lit) =
    let
      val (is_neg, neg_lit) = (true, boolSyntax.dest_neg lit)
        handle Feedback.HOL_ERR _ => (false, boolSyntax.mk_neg lit)
    in
      if maybe_no_hyp orelse HOLset.member (Thm.hypset th, neg_lit) then
        let
          val concl = Thm.concl th
          val th1 = Thm.DISCH neg_lit th
          val p = Term.mk_var ("p", Type.bool)
          val q = Term.mk_var ("q", Type.bool)
        in
          if is_neg then (
            if Feq concl then
              (* [...] |- ~neg_lit *)
              Thm.NOT_INTRO th1
            else
              (* [...] |- ~neg_lit \/ concl *)
              Thm.MP (Thm.INST [p |-> neg_lit, q |-> concl] IMP_DISJ_1) th1
          ) else
            if Feq concl then
              (* [...] |- lit *)
              Thm.MP (Thm.SPEC lit IMP_FALSE) th1
            else
              (* [...] |- lit \/ concl *)
              Thm.MP (Thm.INST [p |-> lit, q |-> concl] IMP_DISJ_2) th1
        end
      else
        raise ERR "z3_lemma" ""
    end
    fun prove (th, disj) =
      prove_literal false (th, disj)
        handle Feedback.HOL_ERR _ =>
          let
            val (l, r) = boolSyntax.dest_disj disj
          in
            (* We do NOT break 'l' apart recursively (because that would be
               slightly tricky to implement, and require associativity of
               disjunction).  Thus, 't' must be parenthesized to the right
               (e.g., "l1 \/ (l2 \/ l3)"). *)
            prove_literal true (prove (th, r), l)
          end
  in
    (state, prove (thm, t))
  end

  val conversion_equal = Library.conversion_equal "conversion_equal"

  val beta_equal = conversion_equal Thm.BETA_CONV
  val eta_equal = conversion_equal Drule.ETA_CONV

  (* |- l1 = r1  ...  |- ln = rn
     ----------------------------
     |- f l1 ... ln = f r1 ... rn

     C1 also exercises this rule below abstractions.  The ABS branch keeps the
     binder explicit, while beta and eta are closing rungs after structural
     application congruence has failed. *)
  (* Congruence below a lambda: `|- (\x. lbody) = (\x. rbody)` from a proof of
     `|- lbody = rbody`.  Both binders are alpha-converted to a fresh variable
     first, so a free variable on either side cannot be captured.  `prove_body`
     supplies the body equality. *)
  fun abs_congruence prove_body (l, r) =
  let
    val (lvar, _) = Term.dest_abs l
    val (rvar, _) = Term.dest_abs r
    val _ = if Term.type_of lvar = Term.type_of rvar then ()
      else raise ERR "abs_congruence" "lambda binder type mismatch"
    val var =
      if not (List.exists (Term.term_eq lvar) (Term.free_vars r)) then
        lvar
      else if not (List.exists (Term.term_eq rvar) (Term.free_vars l)) then
        rvar
      else
        Term.genvar (Term.type_of lvar)
    val lalpha = if Term.term_eq lvar var then Thm.REFL l
      else Drule.ALPHA_CONV var l
    val ralpha = if Term.term_eq rvar var then Thm.REFL r
      else Drule.ALPHA_CONV var r
    val (_, lbody) = Term.dest_abs
      (Lib.snd (boolSyntax.dest_eq (Thm.concl lalpha)))
    val (_, rbody) = Term.dest_abs
      (Lib.snd (boolSyntax.dest_eq (Thm.concl ralpha)))
    val body_thm = prove_body (lbody, rbody)
  in
    Thm.TRANS lalpha (Thm.TRANS (Thm.ABS var body_thm) (Thm.SYM ralpha))
  end

  fun monotonicity_prove (thms, t) =
  let
    val l_r_thms = List.map
      (fn thm => (boolSyntax.dest_eq (Thm.concl thm), thm)) thms
    fun from_premise (l, r) =
      Lib.tryfind (fn ((l', r'), thm) =>
        Thm.TRANS (Thm.ALPHA l l') (Thm.TRANS thm (Thm.ALPHA r' r))
          handle Feedback.HOL_ERR _ =>
            Thm.TRANS (Thm.ALPHA l r')
              (Thm.TRANS (Thm.SYM thm) (Thm.ALPHA l' r))) l_r_thms
    fun abs_equal (l, r) = abs_congruence make_equal (l, r)
    and comb_equal (l, r) =
      let
        val (l_op, l_arg) = Term.dest_comb l
        val (r_op, r_arg) = Term.dest_comb r
      in
        Thm.MK_COMB (make_equal (l_op, r_op), make_equal (l_arg, r_arg))
      end
    and make_equal (l, r) =
      Thm.ALPHA l r
      handle Feedback.HOL_ERR _ => from_premise (l, r)
      handle Feedback.HOL_ERR _ => abs_equal (l, r)
      handle Feedback.HOL_ERR _ => comb_equal (l, r)
      handle Feedback.HOL_ERR _ => beta_equal (l, r)
      handle Feedback.HOL_ERR _ => eta_equal (l, r)
    val (l, r) = boolSyntax.dest_eq t
  in
    make_equal (l, r)
    handle Feedback.HOL_ERR _ =>
      (* surprisingly, 'l' is sometimes of the form ``x /\ y ==> z``
         and must be transformed into ``x ==> y ==> z`` before any
         of the theorems in 'thms' can be applied - this is arguably
         a bug in Z3 (2.11) *)
      let
        val (xy, z) = boolSyntax.dest_imp l
        val (x, y) = boolSyntax.dest_conj xy
        val var_names = ["p", "q", "r"]
        val redexes = List.map (fn v => Term.mk_var (v, Type.bool)) var_names
        val substs = List.map Lib.|-> (ListPair.zip (redexes, [x, y, z]))
        val th1 = Thm.INST substs AND_IMP_INTRO_SYM
        val l' = Lib.snd (boolSyntax.dest_eq (Thm.concl th1))
      in
        Thm.TRANS th1 (make_equal (l', r))
      end
  end

  fun z3_monotonicity (state, thms, t) =
    (state, monotonicity_prove (thms, t))

  fun z3_mp (state, thm1, thm2, t) =
    (state, Thm.MP thm2 thm1 handle Feedback.HOL_ERR _ => Thm.EQ_MP thm2 thm1)

  (* `z3_mp_eq` implements the inference rule corresponding to `Thm.EQ_MP` *)
  fun z3_mp_eq (state, thm1, thm2, t) =
    (state, Thm.EQ_MP thm2 thm1)

  (* `z3_nnf_neg` creates a proof for a negative NNF step.

     The structural rung rewrites with Boolean/quantifier NNF theorems and
     premise equivalences. METIS remains only as a profiled last resort. *)
  fun z3_nnf_neg (state, thms, t) =
    (state, nnf_prove (thms, t))

  (* `z3_nnf_pos` creates a proof for a positive NNF step.

     The structural rung rewrites with Boolean/quantifier NNF theorems and
     premise equivalences. METIS remains only as a profiled last resort. *)
  fun z3_nnf_pos (state, thms, t) =
    (state, nnf_prove (thms, t))

  (* proof-bind records exactly which free variables in a pointwise premise
     are bound by the surrounding NNF step.  Keep the pointwise theorem for
     ordinary rewriting and add its checked forall congruence; ABS/FORALL_EQ
     rejects any attempt to capture a variable occurring in a hypothesis. *)
  fun z3_nnf_bound z3_nnf (state, bound_thms, t) =
  let
    (* The congruence is an extra rewrite, not a precondition: a premise that
       is not a boolean equation, or whose binder occurs in its hypotheses,
       still feeds the rungs the NNF machinery is built around, so an
       unliftable premise must not abort the whole step. *)
    fun lift ([], thm) = [thm]
      | lift (vars, thm) =
          let
            val lifted = List.foldr
              (fn (var, result) => Drule.FORALL_EQ var result) thm vars
          in
            [thm, lifted]
          end
          handle Feedback.HOL_ERR _ => [thm]
    val thms = List.concat (List.map lift bound_thms)
  in
    z3_nnf (state, thms, t)
  end

  (* The C1 HO corpus uses only nnf-pos.  Existing 4.15 FO certificates also
     put proof-bind below nnf-neg, so retain the same checked lifting there to
     avoid regressing the pre-existing replay surface. *)
  val z3_nnf_neg_bound = z3_nnf_bound z3_nnf_neg
  val z3_nnf_pos_bound = z3_nnf_bound z3_nnf_pos

  (* ~(... \/ p \/ ...)
     ------------------
             ~p         *)
  fun z3_not_or_elim (state, thm, t) =
  let
    val (is_neg, neg_t) = (true, boolSyntax.dest_neg t)
      handle Feedback.HOL_ERR _ =>
        (false, boolSyntax.mk_neg t)
    val disj = boolSyntax.dest_neg (Thm.concl thm)
    (* neg_t |- disj *)
    val th1 = Library.disj_intro (Thm.ASSUME neg_t, disj)
    (* |- ~disj ==> ~neg_t *)
    val th1 = Drule.CONTRAPOS (Thm.DISCH neg_t th1)
    (* |- ~neg_t *)
    val th1 = Thm.MP th1 thm
  in
    (state, if is_neg then th1 else Thm.MP (Thm.SPEC t NOT_NOT_ELIM) th1)
  end

  (*
     ------------------------------------------  QUANT_INST [u1,...,un]
       |- ~(!x1...xn. t) \/ t[u1/x1]...[un/xn]
  *)
  fun z3_quant_inst (state, terms, t) =
  let
    val t1 = Lib.fst (boolSyntax.dest_disj t)
    val t2 = boolSyntax.dest_neg t1
    val p_term = Term.mk_var ("p", Type.bool)
    val thm1 = Thm.INST [p_term |-> t2] HolSmtTheory.NOT_P_OR_P
    val thm2 = Thm.ASSUME t1
    val thm3_quant = Thm.ASSUME t2
    val thm3 = Drule.SPECL terms thm3_quant
    val thm = Drule.DISJ_CASES_UNION thm1 thm2 thm3
    (* The following is a quick workaround for the following Z3 issue:
       https://github.com/Z3Prover/z3/issues/7154
       The fix seems to be scheduled to be released in the Z3 version after
       v4.12.6. *)
    val thm' =
      if Thm.concl thm !~ t then
        metis_prove ([thm], t)
      else
        thm
  in
    (state, thm')
  end

  (*                     P = Q
     ---------------------------------------------
     (!x. ?y. !z. P x y z) = (!a. ?b. !c. Q a b c) *)
  fun z3_quant_intro (state, thm, t) =
  let
    (* Removes the outer quantifier and returns a function that inserts it into
       a theorem on both sides of an quality, and the term without the
       quantifier. *)
    fun dest_quant term : ((thm -> thm) * term) option =
      if boolSyntax.is_forall term then
        SOME (Lib.apfst Drule.FORALL_EQ (boolSyntax.dest_forall term))
      else if boolSyntax.is_exists term then
        SOME (Lib.apfst Drule.EXISTS_EQ (boolSyntax.dest_exists term))
      else
        NONE
    (* Removes all quantifiers and returns a list of functions that insert them
       back into a theorem, and the term without the quantifiers *)
    fun strip_quant term acc : (thm -> thm) list * term =
      case dest_quant term of
        NONE => (List.rev acc, term)
      | SOME (f, t) => strip_quant t (f :: acc)

    val (lhs, rhs) = boolSyntax.dest_eq t
    val (quantfs, _) = strip_quant lhs []
    (* P may be a quantified proposition itself; only retain *new*
       quantifiers *)
    val (P, _) = boolSyntax.dest_eq (Thm.concl thm)
    val quantfs = List.take (quantfs, List.length quantfs -
      List.length (Lib.fst (strip_quant P [])))
    (* P and Q in the conclusion may require variable renaming to match
       the premise -- we only look at P and hope Q will come out right *)
    fun strip_some_quants 0 term = term
      | strip_some_quants n term =
          strip_some_quants (n - 1) (Lib.snd (Option.valOf (dest_quant term)))
    val len = List.length quantfs
    val (tmsubst, _) = Term.match_term P (strip_some_quants len lhs)
    val thm = Thm.INST tmsubst thm
    (* add quantifiers (on both sides) *)
    val thm = List.foldr (fn (quantf, th) => quantf th)
      thm quantfs
    (* rename variables on rhs if necessary *)
    val (_, intermediate_rhs) = boolSyntax.dest_eq (Thm.concl thm)
    val thm = Thm.TRANS thm (Thm.ALPHA intermediate_rhs rhs)
  in
    (state, thm)
  end

  (* A proof for `R t t`, where R is a reflexive relation. The only `R` that are
     used are equivalence modulo namings, equality and equivalence, i.e. `~`,
     `=` or `iff`, all represented in HOL4 terms as `boolSyntax.mk_eq`. *)
  fun z3_refl (state, t) =
  let
    val (lhs, rhs) = boolSyntax.dest_eq t
  in
    (state, Thm.ALPHA lhs rhs)
  end

  fun rewrite_word_compare (l, r) =
    if wordsSyntax.is_word_compare l then
      let
        val thm = Conv.REWR_CONV wordsTheory.word_compare_def l
        val (_, rhs) = boolSyntax.dest_eq (Thm.concl thm)
      in
        if rhs ~~ r then thm else raise ERR "rewrite_word_compare" ""
      end
    else if wordsSyntax.is_word_compare r then
      Thm.SYM (rewrite_word_compare (r, l))
    else
      raise ERR "rewrite_word_compare" ""

  fun state_has_definition_for (state : state) var =
    List.exists
      (fn definition =>
        case Lib.total boolSyntax.dest_eq definition of
          SOME (lhs, _) => lhs ~~ var
        | NONE => false)
      (HOLset.listItems (#definition_hyps state))

  fun fresh_fp_bit_decompositions (state : state) =
    List.map
      (fn ({fp_var, bv_var, equation} : bit_decomposition) =>
        {fp_var = fp_var, bv_var = bv_var, equation = equation}
          : SmtFpProve.bit_decomposition)
      (List.filter
        (fn ({bv_var, ...} : bit_decomposition) =>
          not (state_has_definition_for state bv_var))
        (#bit_decompositions state))

  fun z3_rewrite (state, t) =
  let
    val (l, r) = boolSyntax.dest_eq t
  in
    if l ~~ r then
      (state, Thm.REFL l)
    else
      (* re-ordering conjunctions and disjunctions *)
      profile "rewrite(04)(conj/disj)" (fn () =>
      if boolSyntax.is_conj l then
        (state, profile "rewrite(04.1)(conj)" rewrite_conj (l, r))
      else if boolSyntax.is_disj l then
        (state, profile "rewrite(04.2)(disj)" rewrite_disj (l, r))
      else
        raise ERR "" "") ()
    handle Feedback.HOL_ERR _ =>

    (* |- r1 /\ ... /\ rn = ~(s1 \/ ... \/ sn) *)
    (state, profile "rewrite(05)(nnf)" rewrite_nnf (l, r))
    handle Feedback.HOL_ERR _ =>

    (* at this point, we should have dealt with all propositional
       tautologies (i.e., 'tautLib.TAUT_PROVE t' should fail here) *)

    (* Once an FP-shaped rewrite enters its dedicated ladder, failure at its
       unsupported rung is terminal.  In particular, generic unification
       must not turn an unsupported FP rewrite into a proof-local definition.
       FP_REWRITE_ERROR crosses the handlers below and is converted back to a
       structured HOL_ERR at the function boundary. *)
    if SmtFpProve.has_fp_theory_term t then
      ((state, profile "rewrite(02)(cache-fp)"
          (state_inst_cached_thm state) t)
        handle Feedback.HOL_ERR _ =>
          let
            val decompositions = fresh_fp_bit_decompositions state
            val thm = profile "rewrite(03)(fp)"
              (SmtFpProve.fp_prove_with_decompositions decompositions) t
              handle Feedback.HOL_ERR holerr =>
                raise FP_REWRITE_ERROR (Feedback.HOL_ERR holerr)
            val definitions = Thm.hyp thm
            val state = state_define (state_cache_thm state thm) definitions
          in
            (state, thm)
          end)
    else
      (* FP has had first refusal ahead of every generic semantic rung. *)
      (state, profile "rewrite(01)(proforma)"
        (Z3_ProformaThms.prove Z3_ProformaThms.rewrite_thms) t)

    handle Feedback.HOL_ERR _ =>

    (state, profile "rewrite(02)(cache)" (state_inst_cached_thm state) t)

    handle Feedback.HOL_ERR _ =>

    (* Z3's String theory emits rewrite steps for literal normalization,
       ground `str.*` evaluation, and regex normalization. *)
    let
      val thm = profile "rewrite(03)(string)"
        SmtStringProve.string_rewrite_prove t
    in
      (state_cache_thm state thm, thm)
    end

    handle Feedback.HOL_ERR _ =>

    (* |- ALL_DISTINCT ... /\ T = ... *)
    (state, profile "rewrite(06)(all_distinct)" rewrite_all_distinct (l, r))
    handle Feedback.HOL_ERR _ =>

    (* Resolve proof-local names before arithmetic.  These rewrites are not
       arithmetic tautologies until the fresh Z3 variable is recorded as a
       definition, and nonlinear fallback can otherwise spend a long time on
       the deliberately underconstrained formula. *)
    let
      val thm = profile "rewrite(06.5)(unification-early)"
        Library.gen_instantiation (l, r, #var_set state)
      val asl = Thm.hyp thm
      fun is_safe_early_definition tm =
        let val (name, residue) = boolSyntax.dest_eq tm
        in Term.type_of name = Type.bool orelse not (Term.is_var residue) end
      val _ = if not (List.null asl) andalso
          List.all is_safe_early_definition asl then ()
        else raise ERR "z3_rewrite"
          "early unification rejected a variable alias"
    in
      (state_define (state_cache_thm state thm) asl, thm)
    end

    handle Feedback.HOL_ERR _ =>

    let
      val thm = profile "rewrite(07)(SIMP_PROVE_UPDATE)" SIMP_PROVE_UPDATE t
        handle Feedback.HOL_ERR _ =>

        profile "rewrite(08)(WORD_DP)" (wordsLib.WORD_DP
          (bossLib.SIMP_CONV (bossLib.++ (bossLib.++ (bossLib.arith_ss,
            wordsLib.WORD_ss), wordsLib.WORD_EXTRACT_ss)) [])
          (Drule.EQT_ELIM o (bossLib.SIMP_CONV bossLib.arith_ss []))) t
        handle Feedback.HOL_ERR _ =>

        profile "rewrite(09)(WORD_ARITH_CONV)" (fn () =>
          Drule.EQT_ELIM (wordsLib.WORD_ARITH_CONV t)
            handle Conv.UNCHANGED => raise ERR "" "") ()
        handle Feedback.HOL_ERR _ =>

        profile "rewrite(09.1)(word_compare)" rewrite_word_compare (l, r)
        handle Feedback.HOL_ERR _ =>

        profile "rewrite(09.2)(word_compare_def)"
          (simpLib.SIMP_PROVE
            (simpLib.++ (bossLib.std_ss, wordsLib.WORD_ss))
            [wordsTheory.word_compare_def]) t
        handle Feedback.HOL_ERR _ =>

        (profile "rewrite(10)(BBLAST)" (Feedback.trace("print blast counterexamples", 0) blastLib.BBLAST_PROVE) t

        handle Feedback.HOL_ERR _ =>

        (* Z3 emits algebraic rewrites over its totalized division.  Before
           invoking nonlinear arithmetic, use the semantic bridge whenever
           simp can discharge the non-zero divisor condition. *)
        profile "rewrite(10.5)(smt-rdiv)"
          (simpLib.SIMP_PROVE (bossLib.srw_ss())
            [HolSmtTheory.smt_rdiv_eq_div]) t
        handle Feedback.HOL_ERR _ =>

        profile "rewrite(11)(arith)" arith_prove t

        | HolSatLib.SAT_cex _ => profile "rewrite(11)(arith)" arith_prove t)
        handle Feedback.HOL_ERR _ =>

        (* Rewrites emitted by Z3 may contain the solver's totalized real
           division.  Re-enter HOL division only after the non-zero side
           condition has been discharged by simp; this preserves the
           intentionally unconstrained zero-divisor case. *)
        profile "rewrite(11.05)(smt-rdiv)"
          (simpLib.SIMP_PROVE (bossLib.srw_ss())
            [HolSmtTheory.smt_rdiv_eq_div]) t
        handle Feedback.HOL_ERR _ =>

        profile "rewrite(11.1)(datatype)" SmtDatatypeProve.datatype_prove t

    in
      (state_cache_thm state thm, thm)
    end

    handle Feedback.HOL_ERR _ =>

    (* Congruence below a lambda; the shared `abs_congruence` handles the
       capture-avoiding binder alignment, while the body is replayed through
       `z3_rewrite` (threading the state via `state_ref`). *)
    profile "rewrite(11.2)(abs-congruence)" (fn () =>
      let
        val state_ref = ref state
        val thm = abs_congruence (fn (lbody, rbody) =>
          let
            val (state', body_thm) = z3_rewrite
              (!state_ref, boolSyntax.mk_eq (lbody, rbody))
          in
            state_ref := state'; body_thm
          end) (l, r)
      in
        (!state_ref, thm)
      end) ()
    handle Feedback.HOL_ERR _ =>

    (state, profile "rewrite(11.3)(beta)" beta_equal (l, r))
    handle Feedback.HOL_ERR _ =>

    (state, profile "rewrite(11.4)(eta)" eta_equal (l, r))
    handle Feedback.HOL_ERR _ =>

    (* If nothing worked, let's try unifying terms.
       As a motivating example, when proving `(if x < y then x else y) <= x`,
       Z3 v4.12.4 asks us to prove the following rewrite as one of the proof
       steps:

       ~(x + -1 * (if x + -1 * y >= 0 then y else x) >= 0) <=>
       ~(x + -1 * $var$(z3name!0) >= 0)

       ... where z3name!0 is a variable declared by Z3 at the beginning of its
       proof certificate, but which we know nothing about at this point.

       We use the following function to unify both sides of the equality such
       that we obtain instantiations for these variables invented by Z3 (i.e. in
       this example, we'll obtain ``z3name!0 = if x + -1 * y >= 0 then y else x``):

       > Unify.simp_unify_terms [] ``<lhs>`` ``<rhs>``;

       val it = [{redex = ``$var$(z3name!0)``, residue =
         ``if x + -1 * y >= 0 then y else x``}]: (term, term) subst

       We then prove the theorem by substituting the variable(s) and add
       ``z3name!0 = if ... then y else x`` to the list of Z3-provided
       definitions (as in the `z3_intro_def` handler), to make sure it gets
       removed from the set of hypotheses of the final theorem. *)

    (* General unification fallback.  The earlier `rewrite(06.5)` attempt runs
       before arithmetic but deliberately declines a bare variable alias
       (`v1 = v2`) so as not to commit an underconstrained proof-local
       definition prematurely.  Once the arithmetic and word rungs have had
       their chance, record such an alias here — this preserves the
       pre-existing replay behaviour for rewrites whose only reconstruction is
       a variable alias. *)
    let
      val (lhs, rhs) = boolSyntax.dest_eq t
      val thm = profile "rewrite(12.1)(unification)" Library.gen_instantiation
        (lhs, rhs, #var_set state)
      val asl = Thm.hyp thm
    in
      (state_define (state_cache_thm state thm) asl, thm)
    end

    handle Feedback.HOL_ERR _ =>

    let
      val (lhs, rhs) = boolSyntax.dest_eq t
      val rhs = boolSyntax.dest_neg (boolSyntax.dest_neg rhs)
      val thm = profile "rewrite(12.2)(unification)" Library.gen_instantiation
        (lhs, rhs, #var_set state)
      fun not_not_conv tm = Thm.SPEC tm NOT_NOT_INTRO
      val thm = Conv.CONV_RULE (Conv.RHS_CONV not_not_conv) thm
      val asl = Thm.hyp thm
    in
      (state_define (state_cache_thm state thm) asl, thm)
    end

    handle Feedback.HOL_ERR _ =>

    let
      val (lhs, rhs) = boolSyntax.dest_eq t
      val neg_lhs = boolSyntax.mk_neg lhs
      val var = boolSyntax.dest_neg rhs
      val def = boolSyntax.mk_eq (var, neg_lhs)
      val p = Term.mk_var ("p", Type.bool)
      val q = Term.mk_var ("q", Type.bool)
      val thm' = Thm.INST [p |-> var, q |-> lhs] NOT_REVERSE
      val thm = Drule.UNDISCH thm'
    in
      (state_define (state_cache_thm state thm) [def], thm)
    end
  end
  handle FP_REWRITE_ERROR error => raise error

  (* |- ~(!x. P x y) <=> ~(P (sk y) y)
     |- (?x. P x y) <=> P (sk y) y *)
  fun z3_skolem (state, t) =
  let
    val lhs = Lib.fst (boolSyntax.dest_eq t)
    val thm1 =
      if boolSyntax.is_exists lhs then
        HolSmtTheory.SKOLEM_EXISTS
      else
        HolSmtTheory.SKOLEM_FORALL
    val thm2 = Drule.SELECT_RULE thm1
    val thm3 = Conv.HO_REWR_CONV thm2 lhs
    val substs = Term.match_term t (Thm.concl thm3)
    val {redex, residue} = List.hd (Lib.fst substs)
    val thm4 = Thm.SYM (Thm.ASSUME (boolSyntax.mk_eq (redex, residue)))
    val thm5 = Drule.SUBST_CONV [redex |-> thm4] t
      (Thm.concl thm3)
    val thm = Thm.EQ_MP thm5 thm3
    val asl = Thm.hyp thm
  in
    (state_define state asl, thm)
  end

  fun z3_symm (state, thm, t) =
    (state, Thm.SYM thm)

  fun th_lemma_wrapper (name : string)
    (th_lemma_implementation : state * Term.term -> state * Thm.thm)
    (state, thms, t) : state * Thm.thm =
  let
    val t' = boolSyntax.list_mk_imp (List.map Thm.concl thms, t)
    val (state, thm) = (state,
      (* proforma theorems *)
      profile ("th_lemma[" ^ name ^ "](1)(proforma)")
        (Z3_ProformaThms.prove Z3_ProformaThms.th_lemma_thms) t'
      handle Feedback.HOL_ERR _ =>
        (* cached theorems *)
        profile ("th_lemma[" ^ name ^ "](2)(cache)")
          (state_inst_cached_thm state) t')
      handle Feedback.HOL_ERR _ =>
        (* do actual work to derive the theorem *)
        th_lemma_implementation (state, t')
  in
    (state, Drule.LIST_MP thms thm)
  end

  val z3_th_lemma_arith = th_lemma_wrapper "arith" (fn (state, t) =>
    let
      val thm = profile "th_lemma[arith](3)" arith_prove t
    in
      (* cache 'thm' *)
      (state_cache_thm state thm, thm)
    end)

  val z3_th_lemma_array = th_lemma_wrapper "array" (fn (state, t) =>
    (let
       val thm = profile "th_lemma[array](3)(array_prove)"
         SmtArrayProve.array_prove t
     in
       (* cache 'thm' *)
       (state_cache_thm state thm, thm)
     end
     handle Feedback.HOL_ERR _ =>
      raise ERR "z3_th_lemma_array"
        ("unsupported th-lemma shape: theory=array; checked replay is only " ^
         "implemented for function-update select/store/extensionality " ^
         "lemmas; conclusion=" ^ Library.term_to_string t)))

  val bv_th_lemma_prove =
  let
    (* Keep SIMP_TAC for conditional rewrites.  A 2026-07-08 Poly/ML 5.9.2
       retry with PURE_REWRITE_TAC did not reproduce the old segfault in the
       unit phase, but the full selftest run did not finish promptly after
       entering functional tests. *)
    val COND_REWRITE_TAC = simpLib.SIMP_TAC
      simpLib.empty_ss [boolTheory.COND_RAND, boolTheory.COND_RATOR]
  in
    fn t =>
      profile "th_lemma[bv](3)(WORD_BIT_EQ)" (fn () =>
        Drule.EQT_ELIM (Conv.THENC (simpLib.SIMP_CONV (simpLib.++
          (simpLib.++ (bossLib.std_ss, wordsLib.WORD_ss),
          wordsLib.WORD_BIT_EQ_ss)) [], tautLib.TAUT_CONV) t)) ()
      handle Feedback.HOL_ERR _ =>
        profile "th_lemma[bv](4)(COND_BBLAST)" Tactical.prove (t,
          Tactical.THEN (profile "th_lemma[bv](4.1)(COND_REWRITE_TAC)"
            COND_REWRITE_TAC, profile "th_lemma[bv](4.2)(BBLAST_TAC)"
            blastLib.BBLAST_TAC))
  end

  val z3_th_lemma_basic = th_lemma_wrapper "basic" (fn (state, t) =>
    let
      fun unsupported attempts =
        raise ERR "z3_th_lemma_basic"
          ("unsupported th-lemma shape: theory=basic; " ^
           "attempted theories=[" ^
           String.concatWith ", " (List.rev attempts) ^
           "]; checked replay is implemented for Boolean, arithmetic, " ^
           "bit-vector and array equality simplification lemmas; " ^
           "conclusion=" ^ Library.term_to_string t)

      fun metis attempts =
        profile "th_lemma[basic](7)(METIS)" metis_prove ([], t)
        handle Feedback.HOL_ERR _ => unsupported ("metis" :: attempts)

      fun array attempts =
        if has_array_atom t then
          (profile "th_lemma[basic](6)(array)" SmtArrayProve.array_prove t
           handle Feedback.HOL_ERR _ => metis ("array" :: attempts))
        else metis attempts

      fun bv attempts =
        if has_word_atom t then
          (profile "th_lemma[basic](5)(bv)" bv_th_lemma_prove t
           handle Feedback.HOL_ERR _ => array ("bv" :: attempts))
        else array attempts

      fun arith attempts =
        if has_arith_atom t then
          (profile "th_lemma[basic](4)(arith)" arith_prove t
           handle Feedback.HOL_ERR _ => bv ("arith" :: attempts))
        else bv attempts

      val thm = profile "th_lemma[basic](3)(TAUT_PROVE)"
        tautLib.TAUT_PROVE t
        handle Feedback.HOL_ERR _ => arith ["boolean"]
    in
      (* cache 'thm' *)
      (state_cache_thm state thm, thm)
    end)

  val z3_th_lemma_bv =
    th_lemma_wrapper "bv" (fn (state, t) =>
      let
        val thm = bv_th_lemma_prove t
      in
        (* cache 'thm' *)
        (state_cache_thm state thm, thm)
      end)

  val z3_th_lemma_datatype =
    th_lemma_wrapper "datatype" (fn (state, t) =>
      let
        val thm = profile "th_lemma[datatype](3)"
          SmtDatatypeProve.datatype_prove t
      in
        (* cache 'thm' *)
        (state_cache_thm state thm, thm)
      end)

  fun th_lemma_metadata_has_subkind subkinds
      ({subkind, ...} : th_lemma_metadata) =
    case subkind of
      SOME s => List.exists (Lib.equal s) subkinds
    | NONE => false

  fun advanced_th_lemma_obligation_theory ({theory, ...}
      : th_lemma_metadata) =
    case theory of
      "floating-point" => "fp"
    | "fpa" => "fp"
    | "sequence" => "seq"
    | "sequences" => "seq"
    | "strings" => "string"
    | "str" => "string"
    | "regex" => "regexp"
    | "re" => "regexp"
    | other => other

  fun advanced_th_lemma_obligation metadata =
  let
    val theory = advanced_th_lemma_obligation_theory metadata
    val feature_suffix =
      if theory = "nonlinear-arith" then "nonlinear-arith" else theory
    val feature = "proof-rule:th-lemma-" ^ feature_suffix
  in
    {missing_feature = feature, failing_case_ids = [feature]}
  end

  fun unsupported_advanced_th_lemma_message (state : state)
      (metadata : th_lemma_metadata) t =
  let
    val {missing_feature, failing_case_ids} =
      advanced_th_lemma_obligation metadata
  in
    "unsupported th-lemma shape: " ^
    th_lemma_metadata_to_string metadata ^
    "; z3_version=" ^ #z3_version state ^
    "; missing feature: " ^ missing_feature ^
    "; failing case IDs: " ^ String.concatWith ", " failing_case_ids ^
    "; proof-format limitation=Z3 does not emit a checked certificate " ^
    "for HolSmt replay of this advanced theory family; conclusion=" ^
    Library.term_to_string t
  end

  fun z3_th_lemma_advanced_unsupported metadata =
    th_lemma_wrapper ("advanced:" ^ #theory metadata) (fn (state, t) =>
      raise ERR "z3_th_lemma_advanced_unsupported"
        (unsupported_advanced_th_lemma_message state metadata t))

  (* Defensive only: no th-lemma-fp occurrence was observed in any of the
     TASK_02 proofs from supported Z3 4.11.2--4.15.3.  Keep the route checked
     nonetheless, with the FP shape gate ahead of every prover rung. *)
  fun z3_th_lemma_fp _ (state, thms, t) =
  let
    val t' = boolSyntax.list_mk_imp (List.map Thm.concl thms, t)
    val () =
      if SmtFpProve.has_fp_theory_term t' then ()
      else SmtFpProve.unsupported t'
    val thm = profile "th_lemma[fp]" SmtFpProve.fp_prove t'
  in
    (state_cache_thm state thm, Drule.LIST_MP thms thm)
  end

  fun z3_th_lemma_advanced metadata =
    if advanced_th_lemma_obligation_theory metadata = "fp" then
      z3_th_lemma_fp metadata
    else
      z3_th_lemma_advanced_unsupported metadata

  fun unsupported_string_th_lemma_message dispatch_theory
      (state : state) (metadata : th_lemma_metadata) t =
  let
    val {missing_feature, failing_case_ids} =
      advanced_th_lemma_obligation metadata
  in
    "unsupported th-lemma shape: theory=" ^ dispatch_theory ^ "; " ^
    th_lemma_metadata_to_string metadata ^
    "; z3_version=" ^ #z3_version state ^
    "; missing feature: " ^ missing_feature ^
    "; failing case IDs: " ^ String.concatWith ", " failing_case_ids ^
    "; proof-format limitation=the checked string prover has no rung for " ^
    "this clause shape; conclusion=" ^ Library.term_to_string t
  end

  (* `gate` runs the theory preconditions that must surface their own
     enumerated diagnostic.  Deciding this before the prover keeps the gate
     distinguishable from an ordinary prover failure — the contextual rung
     below would otherwise mask a gated clause behind the generic unsupported
     message. *)
  fun string_th_lemma_wrapper dispatch_theory gate metadata prover
      (state, thms, t) =
  let
    val t' = boolSyntax.list_mk_imp (List.map Thm.concl thms, t)
    val context = HOLset.listItems (#asserted_hyps state)
    val () = gate t'
    val thm =
      prover t'
      handle Feedback.HOL_ERR _ =>
        (profile ("Z3(rung:string/contextual:" ^ dispatch_theory ^ ")")
          (SmtStringProve.string_contextual_prove context) t'
          handle Feedback.HOL_ERR _ =>
          raise ERR ("z3_th_lemma_" ^ dispatch_theory)
            (unsupported_string_th_lemma_message dispatch_theory
              state metadata t'))
  in
    (state_cache_thm state thm, Drule.LIST_MP thms thm)
  end

  fun z3_th_lemma_seq metadata =
    string_th_lemma_wrapper "seq" SmtStringProve.check_seq_type metadata
      (SmtStringProve.string_prove arith_prove)

  fun z3_th_lemma_char metadata =
    string_th_lemma_wrapper "char" (fn _ => ()) metadata
      SmtStringProve.char_prove

  fun z3_trans (state, thm1, thm2, t) =
    (state, Thm.TRANS thm1 thm2)

  (* `z3_trans_star` is supposed to handle multiple symmetry and transitivity
     rules. Z3 provides the following example:

     A1 |- R a b   A2 |- R c b   A3 |- R c d
     --------------------------------------- trans*
                A1 u A2 u A3 |- R a d

     Although more generally, the proof rule is supposed to handle any number of
     theorems passed as arguments and any path between the elements.

     R must be a symmetric and transitive relation. Equality is the only
     relation observed in Z3 proof traces, so replay equality chains directly
     and keep METIS only as a measurable fallback. *)

  fun trans_star_exact_prove (thms, t) =
  let
    fun term_eq (t1, t2) = Term.compare (t1, t2) = EQUAL
    fun term_member tm = List.exists (fn tm' => term_eq (tm, tm'))
    val (lhs, rhs) = boolSyntax.dest_eq t
      handle Feedback.HOL_ERR _ =>
        raise ERR "trans_star_exact_prove"
          ("conclusion is not an equation: " ^ Library.term_to_string t)
    fun edge_thms thm =
      let
        val (l, r) = boolSyntax.dest_eq (Thm.concl thm)
          handle Feedback.HOL_ERR _ =>
            raise ERR "trans_star_exact_prove"
              ("premise is not an equation: " ^
               Library.term_to_string (Thm.concl thm))
      in
        [(l, r, thm), (r, l, Thm.SYM thm)]
      end
    val edges = List.concat (List.map edge_thms thms)
    fun outgoing tm =
      List.filter (fn (from, _, _) => term_eq (from, tm)) edges
    fun search [] _ = NONE
      | search ((node, path) :: rest) visited =
          if term_eq (node, rhs) then
            SOME (List.rev path)
          else
            let
              fun add_edge ((_, next, thm), (queue, visited')) =
                if term_member next visited' then
                  (queue, visited')
                else
                  ((next, thm :: path) :: queue, next :: visited')
              val (new_queue, visited') =
                List.foldl add_edge ([], visited) (outgoing node)
            in
              search (rest @ List.rev new_queue) visited'
            end
    fun chain [] = Thm.ALPHA lhs rhs
      | chain (thm :: thms') =
          List.foldl (fn (next, acc) => Thm.TRANS acc next) thm thms'
  in
    case search [(lhs, [])] [lhs] of
      SOME path => chain path
    | NONE =>
        raise ERR "trans_star_exact_prove"
          ("no equality path from " ^ Library.term_to_string lhs ^
           " to " ^ Library.term_to_string rhs ^ " through " ^
           Int.toString (List.length thms) ^ " premise(s)")
  end

  fun z3_trans_star (state, thms, t) =
    (state, profile "trans_star[exact]" trans_star_exact_prove (thms, t))
    handle (exact_err as Feedback.HOL_ERR _) =>
      (state, profile "trans_star[metis-fallback]" metis_prove (thms, t))
      handle Feedback.HOL_ERR _ => raise exact_err

  fun z3_true_axiom (state, t) =
    (state, boolTheory.TRUTH)

  fun z3_unit_resolution (state, thms, t) =
    (state, unit_resolution (thms, t))

  (* end of inference rule implementations *)

  (***************************************************************************)
  (* proof traversal, turning proofterms into theorems                       *)
  (***************************************************************************)

  fun take _ [] = []
    | take 0 _ = []
    | take n (x :: xs) = x :: take (n - 1) xs

  fun term_diag tm =
    Library.term_to_string tm
    handle _ => "<unprintable term>"

  fun thm_diag thm =
    Library.thm_to_string thm
    handle _ => "<unprintable theorem>"

  fun list_summary item_to_string items =
  let
    val total = List.length items
    val shown = take 3 items
    val body = String.concatWith ", " (List.map item_to_string shown)
    val more = if total > List.length shown then ", ..." else ""
  in
    "[" ^ body ^ more ^ "]"
  end

  fun term_set_summary label set =
    label ^ "=" ^ Int.toString (HOLset.numItems set) ^ " " ^
    list_summary term_diag (HOLset.listItems set)

  fun state_summary (state : state) =
    String.concatWith "; " [
      term_set_summary "asserted_hyps" (#asserted_hyps state),
      term_set_summary "definition_hyps" (#definition_hyps state),
      term_set_summary "z3_vars" (#var_set state),
      "bit_decompositions=" ^ Int.toString
        (List.length (#bit_decompositions state)),
      "z3_version=" ^ #z3_version state
    ]

  fun proofterm_replay_handler (AND_ELIM _) = "and_elim"
    | proofterm_replay_handler (APPLY_DEF _) = "apply_def"
    | proofterm_replay_handler (ASSERTED _) = "asserted"
    | proofterm_replay_handler (COMMUTATIVITY _) = "commutativity"
    | proofterm_replay_handler (DEF_AXIOM _) = "def_axiom"
    | proofterm_replay_handler (ELIM_UNUSED _) = "elim_unused"
    | proofterm_replay_handler (HYPOTHESIS _) = "hypothesis"
    | proofterm_replay_handler (IFF_FALSE _) = "iff_false"
    | proofterm_replay_handler (IFF_TRUE _) = "iff_true"
    | proofterm_replay_handler (INTRO_DEF _) = "intro_def"
    | proofterm_replay_handler (LEMMA _) = "lemma"
    | proofterm_replay_handler (MONOTONICITY _) = "monotonicity"
    | proofterm_replay_handler (MP _) = "mp"
    | proofterm_replay_handler (MP_EQ _) = "mp_eq"
    | proofterm_replay_handler (NNF_NEG _) = "nnf_neg"
    | proofterm_replay_handler (NNF_POS _) = "nnf_pos"
    | proofterm_replay_handler (NOT_OR_ELIM _) = "not_or_elim"
    | proofterm_replay_handler (PROOF_BIND _) = "proof_bind"
    | proofterm_replay_handler (QUANT_INST _) = "quant_inst"
    | proofterm_replay_handler (QUANT_INTRO _) = "quant_intro"
    | proofterm_replay_handler (REFL _) = "refl"
    | proofterm_replay_handler (REWRITE _) = "rewrite"
    | proofterm_replay_handler (SKOLEM _) = "skolem"
    | proofterm_replay_handler (SYMM _) = "symm"
    | proofterm_replay_handler (TH_LEMMA_ARITH _) = "th_lemma[arith]"
    | proofterm_replay_handler (TH_LEMMA_ARRAY _) = "th_lemma[array]"
    | proofterm_replay_handler (TH_LEMMA_BASIC _) = "th_lemma[basic]"
    | proofterm_replay_handler (TH_LEMMA_BV _) = "th_lemma[bv]"
    | proofterm_replay_handler (TH_LEMMA_DATATYPE _) = "th_lemma[datatype]"
    | proofterm_replay_handler (TH_LEMMA_SEQ _) = "th_lemma[seq]"
    | proofterm_replay_handler (TH_LEMMA_CHAR _) = "th_lemma[char]"
    | proofterm_replay_handler (TH_LEMMA_ADVANCED _) = "th_lemma[advanced]"
    | proofterm_replay_handler (TRANS _) = "trans"
    | proofterm_replay_handler (TRANS_STAR _) = "trans_star"
    | proofterm_replay_handler (TRUE_AXIOM _) = "true_axiom"
    | proofterm_replay_handler (UNIT_RESOLUTION _) = "unit_resolution"
    | proofterm_replay_handler (ID id) = "@" ^ Int.toString id
    | proofterm_replay_handler (THEOREM _) = "<replayed theorem>"

  fun proofterm_rule (ID id) = "@" ^ Int.toString id
    | proofterm_rule (THEOREM _) = "<replayed theorem>"
    | proofterm_rule (TH_LEMMA_ARITH (metadata, _, _)) =
        th_lemma_rule_name metadata
    | proofterm_rule (TH_LEMMA_ARRAY (metadata, _, _)) =
        th_lemma_rule_name metadata
    | proofterm_rule (TH_LEMMA_BASIC (metadata, _, _)) =
        th_lemma_rule_name metadata
    | proofterm_rule (TH_LEMMA_BV (metadata, _, _)) =
        th_lemma_rule_name metadata
    | proofterm_rule (TH_LEMMA_DATATYPE (metadata, _, _)) =
        th_lemma_rule_name metadata
    | proofterm_rule (TH_LEMMA_SEQ (metadata, _, _)) =
        th_lemma_rule_name metadata
    | proofterm_rule (TH_LEMMA_CHAR (metadata, _, _)) =
        th_lemma_rule_name metadata
    | proofterm_rule (TH_LEMMA_ADVANCED (metadata, _, _)) =
        th_lemma_rule_name metadata
    | proofterm_rule pt =
        (case lookup_rule_by_handler (proofterm_replay_handler pt) of
          SOME rule => #name rule
        | NONE => proofterm_replay_handler pt)

  fun proofterm_concl (AND_ELIM (_, concl)) = SOME concl
    | proofterm_concl (ASSERTED concl) = SOME concl
    | proofterm_concl (COMMUTATIVITY concl) = SOME concl
    | proofterm_concl (DEF_AXIOM concl) = SOME concl
    | proofterm_concl (ELIM_UNUSED concl) = SOME concl
    | proofterm_concl (HYPOTHESIS concl) = SOME concl
    | proofterm_concl (IFF_FALSE (_, concl)) = SOME concl
    | proofterm_concl (IFF_TRUE (_, concl)) = SOME concl
    | proofterm_concl (INTRO_DEF concl) = SOME concl
    | proofterm_concl (LEMMA (_, concl)) = SOME concl
    | proofterm_concl (MONOTONICITY (_, concl)) = SOME concl
    | proofterm_concl (MP (_, _, concl)) = SOME concl
    | proofterm_concl (MP_EQ (_, _, concl)) = SOME concl
    | proofterm_concl (NNF_NEG (_, concl)) = SOME concl
    | proofterm_concl (NNF_POS (_, concl)) = SOME concl
    | proofterm_concl (NOT_OR_ELIM (_, concl)) = SOME concl
    | proofterm_concl (PROOF_BIND _) = NONE
    | proofterm_concl (QUANT_INST (_, concl)) = SOME concl
    | proofterm_concl (QUANT_INTRO (_, concl)) = SOME concl
    | proofterm_concl (REFL concl) = SOME concl
    | proofterm_concl (REWRITE concl) = SOME concl
    | proofterm_concl (SKOLEM concl) = SOME concl
    | proofterm_concl (SYMM (_, concl)) = SOME concl
    | proofterm_concl (TH_LEMMA_ARITH (_, _, concl)) = SOME concl
    | proofterm_concl (TH_LEMMA_ARRAY (_, _, concl)) = SOME concl
    | proofterm_concl (TH_LEMMA_BASIC (_, _, concl)) = SOME concl
    | proofterm_concl (TH_LEMMA_BV (_, _, concl)) = SOME concl
    | proofterm_concl (TH_LEMMA_DATATYPE (_, _, concl)) = SOME concl
    | proofterm_concl (TH_LEMMA_SEQ (_, _, concl)) = SOME concl
    | proofterm_concl (TH_LEMMA_CHAR (_, _, concl)) = SOME concl
    | proofterm_concl (TH_LEMMA_ADVANCED (_, _, concl)) = SOME concl
    | proofterm_concl (TRANS (_, _, concl)) = SOME concl
    | proofterm_concl (TRANS_STAR (_, concl)) = SOME concl
    | proofterm_concl (TRUE_AXIOM concl) = SOME concl
    | proofterm_concl (UNIT_RESOLUTION (_, concl)) = SOME concl
    | proofterm_concl (ID _) = NONE
    | proofterm_concl (THEOREM thm) = SOME (Thm.concl thm)

  fun proofterm_ref (ID id) = "ID " ^ Int.toString id
    | proofterm_ref (THEOREM thm) = "THEOREM(" ^ term_diag (Thm.concl thm) ^ ")"
    | proofterm_ref pt =
        case proofterm_concl pt of
          SOME concl => proofterm_rule pt ^ "(" ^ term_diag concl ^ ")"
        | NONE => proofterm_rule pt

  fun rule_application name pts concl =
    name ^ "(premises=" ^ list_summary proofterm_ref pts ^
    ", conclusion=" ^ term_diag concl ^ ")"

  fun hol_err_diag holerr =
    Feedback.top_structure_of holerr ^ "." ^
    Feedback.top_function_of holerr ^ ": " ^
    Feedback.message_of holerr
    handle Feedback.HOL_ERR _ => Feedback.message_of holerr

  fun raise_replay_error function state name pts concl thms holerr =
    if SmtResource.is_resource_gate holerr then
      raise Feedback.HOL_ERR holerr
    else
      raise ERR function
        ("Z3 proof replay failure\n" ^
         "proof rule: " ^ name ^ "\n" ^
         "local proof subterm: " ^ rule_application name pts concl ^ "\n" ^
         "parsed HOL conclusion: " ^ term_diag concl ^ "\n" ^
         "replay state: " ^ state_summary state ^ "\n" ^
         "premise HOL theorems: " ^ list_summary thm_diag thms ^ "\n" ^
         "underlying HOL_ERR: " ^ hol_err_diag holerr)

  fun raise_final_error stage state thm holerr =
    raise ERR "check_proof"
      ("Z3 proof replay finalization failure\n" ^
       "stage: " ^ stage ^ "\n" ^
       "replay state: " ^ state_summary state ^ "\n" ^
       "local theorem: " ^ thm_diag thm ^ "\n" ^
       "underlying HOL_ERR: " ^ hol_err_diag holerr)

  (* We use a depth-first post-order traversal of the proof, checking
     each premise of a proofterm (i.e., deriving the corresponding
     theorem) before checking the proofterm's inference itself.
     Proofterms that have proof IDs then cause the proof to be updated
     (at this ID) immediately after they have been checked, so that
     future uses of the same proof ID merely require a lookup in the
     proof (rather than a new derivation of the theorem).  To achieve
     a tail-recursive implementation, we use continuation-passing
     style. *)

  fun check_thm (name, thm, concl) =
    if Thm.concl thm !~ concl then
      raise ERR "check_thm" (name ^ ": conclusion is " ^ Library.term_to_string
        (Thm.concl thm) ^ ", expected: " ^ Library.term_to_string concl)
    else if !Library.trace > 2 then
      Feedback.HOL_MESG
        ("HolSmtLib: " ^ name ^ " proved: " ^ Library.thm_to_string thm)
    else ()

  fun zero_prems (state : state, proof : proof)
      (name : string)
      (z3_rule_fn : state * Term.term -> state * Thm.thm)
      (concl : Term.term)
      (continuation : (state * proof) * Thm.thm -> (state * proof) * Thm.thm)
      : (state * proof) * Thm.thm =
  let
    val (state, thm) = profile name z3_rule_fn (state, concl)
      handle Feedback.HOL_ERR holerr =>
        raise_replay_error name state name [] concl [] holerr
    val _ = profile "check_thm" check_thm (name, thm, concl)
      handle Feedback.HOL_ERR holerr =>
        raise_replay_error "check_thm" state name [] concl [thm] holerr
  in
    continuation ((state, proof), thm)
  end

  fun one_arg_zero_prems (state : state, proof : proof)
      (name : string)
      (z3_rule_fn : state * 'a * Term.term -> state * Thm.thm)
      (arg : 'a, concl : Term.term)
      (continuation : (state * proof) * Thm.thm -> (state * proof) * Thm.thm)
      : (state * proof) * Thm.thm =
  let
    val (state, thm) = profile name z3_rule_fn (state, arg, concl)
      handle Feedback.HOL_ERR holerr =>
        raise_replay_error name state name [] concl [] holerr
    val _ = profile "check_thm" check_thm (name, thm, concl)
      handle Feedback.HOL_ERR holerr =>
        raise_replay_error "check_thm" state name [] concl [thm] holerr
  in
    continuation ((state, proof), thm)
  end

  fun one_prem (state_proof : state * proof)
      (name : string)
      (z3_rule_fn : state * Thm.thm * Term.term -> state * Thm.thm)
      (pt : proofterm, concl : Term.term)
      (continuation : (state * proof) * Thm.thm -> (state * proof) * Thm.thm)
      : (state * proof) * Thm.thm =
    thm_of_proofterm (state_proof, pt) (continuation o
      (fn ((state, proof), thm) =>
        let
          val (state, thm) = profile name z3_rule_fn (state, thm, concl)
            handle Feedback.HOL_ERR holerr =>
              raise_replay_error name state name [pt] concl [thm] holerr
          val _ = profile "check_thm" check_thm (name, thm, concl)
            handle Feedback.HOL_ERR holerr =>
              raise_replay_error "check_thm" state name [pt] concl [thm] holerr
        in
          ((state, proof), thm)
        end))

  and two_prems (state_proof : state * proof)
      (name : string)
      (z3_rule_fn : state * Thm.thm * Thm.thm * Term.term -> state * Thm.thm)
      (pt1 : proofterm, pt2 : proofterm, concl : Term.term)
      (continuation : (state * proof) * Thm.thm -> (state * proof) * Thm.thm)
      : (state * proof) * Thm.thm =
    thm_of_proofterm (state_proof, pt1) (continuation o
      (fn (state_proof, thm1) =>
        thm_of_proofterm (state_proof, pt2) (fn ((state, proof), thm2) =>
          let
            val (state, thm) = profile name z3_rule_fn
              (state, thm1, thm2, concl)
                handle Feedback.HOL_ERR holerr =>
                  raise_replay_error name state name [pt1, pt2] concl
                    [thm1, thm2] holerr
            val _ = profile "check_thm" check_thm (name, thm, concl)
              handle Feedback.HOL_ERR holerr =>
                raise_replay_error "check_thm" state name [pt1, pt2] concl
                  [thm1, thm2, thm] holerr
          in
            ((state, proof), thm)
          end)))

  and list_prems (state : state, proof : proof)
      (name : string)
      (z3_rule_fn : state * Thm.thm list * Term.term -> state * Thm.thm)
      ([] : proofterm list, concl : Term.term)
      (continuation : (state * proof) * Thm.thm -> (state * proof) * Thm.thm)
      (acc : Thm.thm list)
      : (state * proof) * Thm.thm =
    let
      val acc = List.rev acc
      val (state, thm) = profile name z3_rule_fn (state, acc, concl)
        handle Feedback.HOL_ERR holerr =>
          raise_replay_error name state name [] concl acc holerr
      val _ = profile "check_thm" check_thm (name, thm, concl)
        handle Feedback.HOL_ERR holerr =>
          raise_replay_error "check_thm" state name [] concl (thm :: acc) holerr
    in
      continuation ((state, proof), thm)
    end
    | list_prems (state_proof : state * proof)
      (name : string)
      (z3_rule_fn : state * Thm.thm list * Term.term -> state * Thm.thm)
      (pt :: pts : proofterm list, concl : Term.term)
      (continuation : (state * proof) * Thm.thm -> (state * proof) * Thm.thm)
      (acc : Thm.thm list)
      : (state * proof) * Thm.thm =
    thm_of_proofterm (state_proof, pt)
      (fn (state_proof, thm) =>
        list_prems state_proof name z3_rule_fn (pts, concl) continuation
          (thm :: acc))

  and list_bound_prems (state : state, proof : proof)
      (name : string)
      (z3_rule_fn : state * (Term.term list * Thm.thm) list * Term.term ->
        state * Thm.thm)
      ([] : proofterm list, concl : Term.term)
      (continuation : (state * proof) * Thm.thm -> (state * proof) * Thm.thm)
      (acc : (Term.term list * Thm.thm) list)
      : (state * proof) * Thm.thm =
    let
      val acc = List.rev acc
      val thms = List.map Lib.snd acc
      val (state, thm) = profile name z3_rule_fn (state, acc, concl)
        handle Feedback.HOL_ERR holerr =>
          raise_replay_error name state name [] concl thms holerr
      val _ = profile "check_thm" check_thm (name, thm, concl)
        handle Feedback.HOL_ERR holerr =>
          raise_replay_error "check_thm" state name [] concl
            (thm :: thms) holerr
    in
      continuation ((state, proof), thm)
    end
    | list_bound_prems (state_proof : state * proof)
      (name : string)
      (z3_rule_fn : state * (Term.term list * Thm.thm) list * Term.term ->
        state * Thm.thm)
      (pt :: pts : proofterm list, concl : Term.term)
      (continuation : (state * proof) * Thm.thm -> (state * proof) * Thm.thm)
      (acc : (Term.term list * Thm.thm) list)
      : (state * proof) * Thm.thm =
    let
      val (vars, body) =
        case pt of
          PROOF_BIND pair => pair
        | _ => ([], pt)
    in
      thm_of_proofterm (state_proof, body) (fn (state_proof, thm) =>
        list_bound_prems state_proof name z3_rule_fn (pts, concl)
          continuation ((vars, thm) :: acc))
    end

  and thm_of_proofterm (state_proof, AND_ELIM x) continuation =
        one_prem state_proof "and_elim" z3_and_elim x continuation
    | thm_of_proofterm (state_proof, APPLY_DEF x) continuation =
        one_prem state_proof "apply_def" z3_apply_def x continuation
    | thm_of_proofterm (state_proof, ASSERTED x) continuation =
        zero_prems state_proof "asserted" z3_asserted x continuation
    | thm_of_proofterm (state_proof, COMMUTATIVITY x) continuation =
        zero_prems state_proof "commutativity" z3_commutativity x continuation
    | thm_of_proofterm (state_proof, DEF_AXIOM x) continuation =
        zero_prems state_proof "def_axiom" z3_def_axiom x continuation
    | thm_of_proofterm (state_proof, ELIM_UNUSED x) continuation =
        zero_prems state_proof "elim_unused" z3_elim_unused x continuation
    | thm_of_proofterm (state_proof, HYPOTHESIS x) continuation =
        zero_prems state_proof "hypothesis" z3_hypothesis x continuation
    | thm_of_proofterm (state_proof, IFF_FALSE x) continuation =
        one_prem state_proof "iff_false" z3_iff_false x continuation
    | thm_of_proofterm (state_proof, IFF_TRUE x) continuation =
        one_prem state_proof "iff_true" z3_iff_true x continuation
    | thm_of_proofterm (state_proof, INTRO_DEF x) continuation =
        zero_prems state_proof "intro_def" z3_intro_def x continuation
    | thm_of_proofterm (state_proof, LEMMA x) continuation =
        one_prem state_proof "lemma" z3_lemma x continuation
    | thm_of_proofterm (state_proof, MONOTONICITY x) continuation =
        list_prems state_proof "monotonicity" z3_monotonicity x continuation []
    | thm_of_proofterm (state_proof, MP x) continuation =
        two_prems state_proof "mp" z3_mp x continuation
    | thm_of_proofterm (state_proof, MP_EQ x) continuation =
        two_prems state_proof "mp~" z3_mp_eq x continuation
    | thm_of_proofterm (state_proof, NNF_NEG x) continuation =
        list_bound_prems state_proof "nnf_neg" z3_nnf_neg_bound x
          continuation []
    | thm_of_proofterm (state_proof, NNF_POS x) continuation =
        list_bound_prems state_proof "nnf_pos" z3_nnf_pos_bound x
          continuation []
    | thm_of_proofterm (state_proof, NOT_OR_ELIM x) continuation =
        one_prem state_proof "not_or_elim" z3_not_or_elim x continuation
    | thm_of_proofterm (state_proof, PROOF_BIND (_, body)) continuation =
        (* proof-bind is a binder annotation rather than a logical rule.  The
           consumers that need the preserved variables (the NNF rules) destruct
           the annotation themselves; everywhere else — including an empty
           annotation — it erases to its body, which is the theorem the
           surrounding rule expects. *)
        thm_of_proofterm (state_proof, body) continuation
    | thm_of_proofterm (state_proof, QUANT_INST x) continuation =
        one_arg_zero_prems state_proof "quant_inst" z3_quant_inst x continuation
    (* A proof-bind premise of quant-intro only annotates which binders the
       surrounding step introduced.  `z3_quant_intro` recovers the quantifier
       structure from the terms themselves and `check_thm` validates the
       result, so the annotation erases and the rule takes the plain
       premise. *)
    | thm_of_proofterm (state_proof, QUANT_INTRO x) continuation =
        one_prem state_proof "quant_intro" z3_quant_intro x continuation
    | thm_of_proofterm (state_proof, REFL x) continuation =
        zero_prems state_proof "refl" z3_refl x continuation
    | thm_of_proofterm (state_proof, REWRITE x) continuation =
        zero_prems state_proof "rewrite" z3_rewrite x continuation
    | thm_of_proofterm (state_proof, SKOLEM x) continuation =
        zero_prems state_proof "skolem" z3_skolem x continuation
    | thm_of_proofterm (state_proof, SYMM x) continuation =
        one_prem state_proof "symm" z3_symm x continuation
    | thm_of_proofterm (state_proof, TH_LEMMA_ARITH (metadata, pts, concl))
        continuation =
        list_prems state_proof (th_lemma_rule_name metadata)
          z3_th_lemma_arith (pts, concl) continuation []
    | thm_of_proofterm (state_proof, TH_LEMMA_ARRAY (metadata, pts, concl))
        continuation =
        list_prems state_proof (th_lemma_rule_name metadata) z3_th_lemma_array
          (pts, concl) continuation []
    | thm_of_proofterm (state_proof, TH_LEMMA_BASIC (metadata, pts, concl))
        continuation =
        list_prems state_proof (th_lemma_rule_name metadata) z3_th_lemma_basic
          (pts, concl) continuation []
    | thm_of_proofterm (state_proof, TH_LEMMA_BV (metadata, pts, concl))
        continuation =
        list_prems state_proof (th_lemma_rule_name metadata) z3_th_lemma_bv
          (pts, concl) continuation []
    | thm_of_proofterm (state_proof, TH_LEMMA_DATATYPE
        (metadata, pts, concl)) continuation =
        list_prems state_proof (th_lemma_rule_name metadata)
          z3_th_lemma_datatype (pts, concl) continuation []
    | thm_of_proofterm (state_proof, TH_LEMMA_SEQ (metadata, pts, concl))
        continuation =
        list_prems state_proof (th_lemma_rule_name metadata)
          (z3_th_lemma_seq metadata) (pts, concl) continuation []
    | thm_of_proofterm (state_proof, TH_LEMMA_CHAR (metadata, pts, concl))
        continuation =
        list_prems state_proof (th_lemma_rule_name metadata)
          (z3_th_lemma_char metadata) (pts, concl) continuation []
    | thm_of_proofterm (state_proof, TH_LEMMA_ADVANCED (metadata, pts, concl))
        continuation =
        list_prems state_proof (th_lemma_rule_name metadata)
          (z3_th_lemma_advanced metadata) (pts, concl) continuation []
    | thm_of_proofterm (state_proof, TRANS x) continuation =
        two_prems state_proof "trans" z3_trans x continuation
    | thm_of_proofterm (state_proof, TRANS_STAR x) continuation =
        list_prems state_proof "trans*" z3_trans_star x continuation []
    | thm_of_proofterm (state_proof, TRUE_AXIOM x) continuation =
        zero_prems state_proof "true_axiom" z3_true_axiom x continuation
    | thm_of_proofterm (state_proof, UNIT_RESOLUTION x) continuation =
        list_prems state_proof "unit_resolution" z3_unit_resolution x
          continuation []
    | thm_of_proofterm ((state, proof), ID id) continuation =
        (case Redblackmap.peek (proof_steps proof, id) of
          SOME (THEOREM thm) =>
            continuation ((state, proof), thm)
        | SOME pt => (
            if !Library.trace > 2 then
              Feedback.HOL_MESG ("HolSmtLib: replaying proof at ID " ^ Int.toString id)
            else
              ();
            thm_of_proofterm ((state, proof), pt) (continuation o
              (* update the proof, replacing the original proofterm with
                 the theorem just derived *)
              (fn ((state, proof), thm) =>
                (
                  if !Library.trace > 2 then
                    Feedback.HOL_MESG
                      ("HolSmtLib: updating proof at ID " ^ Int.toString id)
                  else ();
                  ((state, update_proof_steps proof
                    (Redblackmap.insert (proof_steps proof, id, THEOREM thm))),
                    thm)
                )))
        )
        | NONE =>
            raise ERR "thm_of_proofterm"
              ("proof has no proofterm for ID " ^ Int.toString id))
    | thm_of_proofterm (state_proof, THEOREM thm) continuation =
        continuation (state_proof, thm)

  (* Remove the definitions `defs` from the set of hypotheses in `thm`,
     returning the resulting theorem, i.e.:

     A u defs |- t
     -------------  remove_definitions (defs, var_set)
       A |- t

     Each definition in `defs` must be of the form ``var = term``, where `var`
     must not be free in `t` nor in `A` and must be in `var_set`.

     There is a major complication: some definitions reference variables in
     other definitions and they may even be duplicated (with and without
     expansion), e.g.:

     z1 = x + 1
     z2 = x + 1 + 2
     z2 = z1 + 2
     z3 = 3 + y

     Furthermore, another major complication is that such nested definitions
     can easily cause exponential term blow-up in case all such definitions were
     to be fully expanded (e.g. by substituting each variable with one of its
     definitions), which might occur in a naive attempt at removing these
     definitions. Therefore, a more careful implementation is warranted.

     In general, the variable references can form a directed acyclic graph. For
     efficiency purposes (explained later), we first find a variable that is not
     referenced in any definition of the other variables.

     In the above example, one such variable could be `z2` or `z3` (we'll pick
     `z2` for this example), but not `z1`, since it is referenced in one of the
     definitions of `z2`.

     We then perform the following:

     1. Gather all definitions of this variable. In this example, the
     definitions for ``z2`` would be:

     z2 = z1 + 2
     z2 = x + 1 + 2

     2. Instantiate the variable with one of its definitions (chosen
     arbitrarily). In this example, it could result in the following hypotheses:

     z1 + 2 = z1 + 2
     z1 + 2 = x + 1 + 2

     3. For each of these hypotheses, we create a theorem proving the hypothesis
     so that we can remove it with Drule.PROVE_HYP. To prove such a theorem,
     first we unify the terms on both sides of the equality, such that we obtain
     new definitions for the variables in these hypotheses. For the first one,
     no new definitions are needed, which means such a theorem can be proven
     with REFL. For the second one, we get:

     z1 = x + 1

     We can then substitute `z1` with `x + 1`, then use REFL to prove the
     theorem. This is implemented in `Library.gen_instantiation`. Note that this
     theorem will have `z1 = x + 1` in its set of hypotheses, which
     Drule.PROVE_HYP then adds to the set of hypotheses of `thm`.

     However, this new hypothesis will be removed later when we process `z1`.
     Often, these additional hypotheses are identical to pre-existing ones, so
     they get deduplicated when added to the set of hypotheses of `thm`. By
     processing variables in this specific order, we thus avoid doing a lot of
     repeated work of removing the same definitions over and over again.

     Once all the definitions of the variable we've chosen are removed, we
     recurse into this same function, with the new set of definitions that are
     to be removed (corresponding to one less variable). Note that in general,
     at no point we needed to fully expand a definition (unless it's already
     expanded). *)

  fun remove_definitions (defs, var_set, thm): Thm.thm =
    if HOLset.isEmpty defs then
      thm
    else
      let
        (* Discharging a ground definition is an optimization, not an
           obligation: anything left behind stays an ordinary hypothesis for
           `remove_hyps` to deal with, exactly as it did before this shortcut
           existed.  A definition that does not evaluate is therefore skipped
           rather than failing the whole replay. *)
        fun prove_ground_def def =
          let
            val thm = bossLib.EVAL def
          in
            if boolSyntax.is_eq (Thm.concl thm) andalso
               Lib.snd (boolSyntax.dest_eq (Thm.concl thm)) ~~ boolSyntax.T
            then SOME (Drule.EQT_ELIM thm)
            else NONE
          end
          handle Feedback.HOL_ERR _ => NONE
        fun is_var_def def =
          boolSyntax.is_eq def andalso
          Term.is_var (Lib.fst (boolSyntax.dest_eq def))
        val (ground_defs, defs) =
          List.partition (not o is_var_def) (HOLset.listItems defs)
        val defs = HOLset.addList (Term.empty_tmset, defs)
        fun discharge_ground_def (def, thm) =
          case prove_ground_def def of
            SOME def_thm => Drule.PROVE_HYP def_thm thm
          | NONE => thm
        val thm = HOLset.foldl discharge_ground_def
          thm (HOLset.addList (Term.empty_tmset, ground_defs))
      in
        if HOLset.isEmpty defs then thm
        else
      let
        (* For convenience, `dest_defs` will contain a list of `(lhs, rhs)`
           pairs, where `lhs` is the var being defined and `rhs` its
           definition. *)
        val dest_defs = List.map boolSyntax.dest_eq (HOLset.listItems defs)
        val (lhs_l, rhs_l) = ListPair.unzip dest_defs
        (* `ref_set` will contain the set of all variables being referenced *)
        val ref_set = Term.FVL rhs_l Term.empty_tmset
        (* `def_set` will contain the set of all variables being defined.
           It should always be a subset of `var_set`. *)
        val def_set = List.foldl (Lib.flip HOLset.add) Term.empty_tmset lhs_l

        (* `unref_set` will contain the set of all the variables being defined
           but not being referenced *)
        val unref_set = HOLset.difference (def_set, ref_set)

        val () =
          if HOLset.isEmpty unref_set then
            raise ERR "remove_definitions" "no unreferenced variables"
          else
            ()

        (* Pick an arbitrary variable from `unref_set` *)
        val var = Option.valOf (HOLset.find (fn _ => true) unref_set)

        (* Get all the variable's definitions *)
        fun filter_def (v, d) = if Term.term_eq v var then SOME d else NONE
        val defs_to_remove = List.mapPartial filter_def dest_defs

        (* Pick an arbitrary definition for instantiation *)
        val inst = List.hd defs_to_remove

        (* Instantiate the variable with the definition *)
        val thm = Thm.INST [var |-> inst] thm

        (* For each definition corresponding to this variable, create a theorem
           that can eliminate the definition from the set of hypotheses of `thm` *)
        val hyp_thms = List.map (fn def => Library.gen_instantiation (inst, def,
          var_set)) defs_to_remove

        (* Remove all the definitions corresponding to this variable *)
        fun remove_hyp (hyp_thm, thm) = Drule.PROVE_HYP hyp_thm thm
        val thm = List.foldl remove_hyp thm hyp_thms

        (* Compute the new set of definitions to remove when recursing.
           Basically, it's all the definitions in `thm`, i.e. all hypotheses of
           the form ``var = def``, where ``var`` is in `var_set` *)
        fun is_definition hyp = boolSyntax.is_eq hyp andalso
          HOLset.member (var_set, Lib.fst (boolSyntax.dest_eq hyp))
        fun add_def (hyp, set) =
          if is_definition hyp then HOLset.add (set, hyp) else set
        val new_defs = HOLset.foldl add_def Term.empty_tmset (Thm.hypset thm)
      in
        (* Recurse to remove the remaining variables' definitions *)
        remove_definitions (new_defs, var_set, thm)
      end
      end

  (* this function identifies hypotheses in the final theorem that are not in
     the original list of assumptions and then tries to remove them; it's a
     workaround for the following Z3 issue, whose fix is currently still in
     progress:

     https://github.com/Z3Prover/z3/pull/7157 *)
  fun remove_hyps (asl, g, thm) : Thm.thm =
  let
    val hyps = Thm.hypset thm
    (* add the negation of the conclusion of the goal to the list of
       expected hypotheses *)
    val asl = (boolSyntax.mk_neg g) :: asl
    val asms = HOLset.addList (Term.empty_tmset, asl)
    val bad_hyps = HOLset.difference (hyps, asms)
    val smt_normalize_ss = bossLib.arith_ss ++ intSimps.INT_RWTS_ss ++
      intSimps.INT_ARITH_ss ++ realSimps.REAL_ARITH_ss
    (* Normalize Z3's total inverse macro before expanding ordinary division
       into smt_rdiv.  The two encodings are equivalent away from zero but
       have different useful normal forms for nested inverses. *)
    val smt_semantic_normalize_tac =
      bossLib.FULL_SIMP_TAC (bossLib.srw_ss())
        [realaxTheory.real_abs,
         HolSmtTheory.int_ceiling_floor,
         HolSmtTheory.smt_rinv_def,
         HolSmtTheory.smt_rinv_inv,
         Conv.GSYM realTheory.REAL_INV_1OVER,
         realTheory.REAL_INV_INV,
         HolSmtTheory.real_div_smt_rdiv,
         HolSmtTheory.smt_rdiv_lneg,
         HolSmtTheory.smt_rdiv_rneg]
    (* Normalize the two total-division encodings to their common semantic
       form.  The bridge to field division is conditional, so it is used only
       when simplification discharges its nonzero premise. *)
    fun smt_total_real_normalize_tac rdiv_bridges =
      bossLib.FULL_SIMP_TAC (bossLib.srw_ss())
        [realaxTheory.real_abs,
         HolSmtTheory.int_ceiling_floor,
         HolSmtTheory.smt_rinv_def,
         HolSmtTheory.smt_rinv_inv,
         Conv.GSYM realTheory.REAL_INV_1OVER,
         realTheory.REAL_INV_INV,
         HolSmtTheory.real_div_smt_rdiv] >>
      bossLib.FULL_SIMP_TAC (bossLib.srw_ss())
        [HolSmtTheory.smt_rdiv_eq_div] >>
      bossLib.FULL_SIMP_TAC (bossLib.srw_ss()) rdiv_bridges
    (* Solver literals reach replay as ``real_of_int i``.  REAL_INJ reduces
       their non-zero side conditions, allowing the semantic rdiv boundary
       lemma to align the solver form with HOL division without unfolding
       arbitrary divisions. *)
    fun smt_numeral_normalize_tac rdiv_bridges =
      bossLib.FULL_SIMP_TAC (bossLib.srw_ss())
        [realTheory.REAL_INJ,
         realaxTheory.real_abs,
         HolSmtTheory.int_ceiling_floor,
         HolSmtTheory.smt_rinv_def,
         HolSmtTheory.smt_rinv_inv,
         Conv.GSYM realTheory.REAL_INV_1OVER,
         realTheory.REAL_INV_INV] >>
      bossLib.FULL_SIMP_TAC (bossLib.srw_ss()) rdiv_bridges
    val (_, smt_rdiv_eq_body) =
      boolSyntax.strip_forall (Thm.concl HolSmtTheory.smt_rdiv_eq_div)
    val (_, smt_rdiv_eq_concl) = boolSyntax.dest_imp smt_rdiv_eq_body
    val smt_rdiv_const =
      Lib.fst (strip_comb
        (Lib.fst (boolSyntax.dest_eq smt_rdiv_eq_concl)))
    fun literal_rdiv_bridge tm =
      case strip_comb tm of
        (f, [x, y]) =>
      let
        val i = realSyntax.dest_injected y
        val _ = if intSyntax.is_int_literal i then () else raise ERR "" ""
        val y_ne_zero =
          Tactical.TAC_PROOF
            (([], boolSyntax.mk_neg (boolSyntax.mk_eq (y, realSyntax.zero_tm))),
             bossLib.FULL_SIMP_TAC (bossLib.srw_ss()) [realTheory.REAL_INJ])
      in
        if Term.same_const f smt_rdiv_const then
          SOME (Thm.MP (Drule.SPECL [x, y] HolSmtTheory.smt_rdiv_eq_div)
                       y_ne_zero)
        else NONE
      end handle _ => NONE
      | _ => NONE
    fun literal_rdiv_bridges tm =
      List.mapPartial literal_rdiv_bridge
        (HolKernel.find_terms (fn t =>
           let val (f, _) = strip_comb t
           in Term.same_const f smt_rdiv_const end
           handle _ => false) tm)
      handle _ => []
    fun smt_normalize_tac thms =
      bossLib.RW_TAC smt_normalize_ss
        (realaxTheory.real_abs ::
         HolSmtTheory.int_ceiling_floor ::
         HolSmtTheory.smt_rinv_def ::
         HolSmtTheory.smt_rinv_inv ::
         Conv.GSYM realTheory.REAL_INV_1OVER ::
         realTheory.REAL_INV_INV ::
         HolSmtTheory.real_div_smt_rdiv ::
         HolSmtTheory.smt_rdiv_lneg ::
         HolSmtTheory.smt_rdiv_rneg ::
         intrealTheory.is_int_alt ::
         intrealTheory.is_int_thm ::
         thms)
    fun smt_full_normalize_tac thms =
      bossLib.FULL_SIMP_TAC (bossLib.srw_ss())
        (realaxTheory.real_abs ::
         HolSmtTheory.int_ceiling_floor ::
         HolSmtTheory.smt_rinv_def ::
         HolSmtTheory.smt_rinv_inv ::
         Conv.GSYM realTheory.REAL_INV_1OVER ::
         realTheory.REAL_INV_INV ::
         HolSmtTheory.real_div_smt_rdiv ::
         HolSmtTheory.smt_rdiv_lneg ::
         HolSmtTheory.smt_rdiv_rneg ::
         intrealTheory.is_int_alt ::
         intrealTheory.is_int_thm ::
         thms)
    fun datatype_normalize_tac thms (asl, hyp) =
      let
        val combined = boolSyntax.list_mk_conj (hyp :: asl)
        val cases = List.map SmtDatatypeProve.nchotomy_for_term
          (SmtDatatypeProve.datatype_free_terms combined)
      in
        Tactical.THEN
          (Tactical.EVERY (List.map Tactic.FULL_STRUCT_CASES_TAC cases),
           smt_full_normalize_tac thms) (asl, hyp)
      end
    fun remove_hyp (hyp, thm) : Thm.thm =
    let
      val combined = boolSyntax.list_mk_conj (hyp :: asl)
      val datatype_thms = profile
        "check_proof(hyp_removal:datatype_facts)"
        SmtDatatypeProve.datatype_rewrite_thms combined
        handle _ => []
      val rdiv_bridges = profile
        "check_proof(hyp_removal:rdiv_bridges)" literal_rdiv_bridges combined
      fun try_tac name tac =
        SOME (profile name Tactical.TAC_PROOF ((asl, hyp), tac))
        handle _ => NONE
      fun first_success [] = NONE
        | first_success ((name, tac) :: tacs) =
            case try_tac name tac of
              SOME th => SOME th
            | NONE => first_success tacs
      val hyp_thm =
        case first_success
          [("check_proof(hyp_removal:numeral_normalize)",
              smt_numeral_normalize_tac rdiv_bridges),
           ("check_proof(hyp_removal:semantic_normalize)",
              smt_semantic_normalize_tac),
           ("check_proof(hyp_removal:total_real_normalize)",
              smt_total_real_normalize_tac rdiv_bridges),
           ("check_proof(hyp_removal:normalize)", smt_normalize_tac []),
           ("check_proof(hyp_removal:full_normalize)",
              smt_full_normalize_tac datatype_thms),
           ("check_proof(hyp_removal:datatype_normalize)",
              datatype_normalize_tac datatype_thms)] of
          SOME th => th
        | NONE => profile "check_proof(hyp_removal:METIS)"
            Tactical.TAC_PROOF ((asl, hyp), metisLib.METIS_TAC [])
    in
      Drule.PROVE_HYP hyp_thm thm
    end
  in
    HOLset.foldl remove_hyp thm bad_hyps
  end

  (* Workaround for a Z3 proof issue where a `hypothesis` rule introduces the
     literal tautology `p = p` and no later `lemma` rule discharges it.  Keep
     this intentionally narrow: other reflexive equalities are not known Z3
     artifacts and should not be silently removed. *)
  fun is_spurious_p_eq_p hyp =
    if boolSyntax.is_eq hyp then
      let
        val (lhs, rhs) = boolSyntax.dest_eq hyp
      in
        Term.term_eq lhs rhs andalso
        (case Lib.total Term.dest_var lhs of
           SOME ("p", ty) => ty = Type.bool
         | _ => false)
      end
    else
      false

  fun remove_extra_hyps (asserted, thm) =
  let
    val extra_hyps = HOLset.difference (Thm.hypset thm, asserted)
    fun remove_hyp (hyp, thm) =
      if is_spurious_p_eq_p hyp then
        Drule.PROVE_HYP (Thm.REFL (Lib.fst (boolSyntax.dest_eq hyp))) thm
      else
        thm
  in
    HOLset.foldl remove_hyp thm extra_hyps
  end
in
  (* For unit tests *)
  val remove_definitions = remove_definitions
  val remove_extra_hyps = remove_extra_hyps
  val beta_equal_for_test = beta_equal
  val eta_equal_for_test = eta_equal
  val monotonicity_prove_for_test = monotonicity_prove

  fun replay_root_for_test proof : Thm.thm =
  let
    val state = {
      asserted_hyps = Term.empty_tmset,
      definition_hyps = Term.empty_tmset,
      thm_cache = Net.empty,
      var_set = proof_vars proof,
      bit_decompositions = proof_bit_decompositions proof,
      z3_version = proof_version proof
    }
    val ((_, _), thm) = thm_of_proofterm ((state, proof), ID 0) Lib.I
  in
    thm
  end

  (* returns a theorem that concludes ``F``, with its hypotheses (a
     subset of) those asserted in the proof *)
  fun check_proof_impl (asl, g, proof) : Thm.thm =
  let
    val _ = if !Library.trace > 1 then
        Feedback.HOL_MESG "HolSmtLib: checking Z3 proof"
      else ()

    (* initial state *)
    val state = {
      asserted_hyps = Term.empty_tmset,
      definition_hyps = Term.empty_tmset,
      thm_cache = Net.empty,
      var_set = proof_vars proof,
      bit_decompositions = proof_bit_decompositions proof,
      z3_version = proof_version proof
    }

    (* ID 0 denotes the proof's root node *)
    val ((state, _), thm) = thm_of_proofterm ((state, proof), ID 0) Lib.I

    val _ = Feq (Thm.concl thm) orelse
      raise ERR "check_proof" "final conclusion is not 'F'"

    (* remove the definitions introduced by Z3 from the set of hypotheses *)
    val final_thm = profile "check_proof(remove_definitions)" remove_definitions
      (#definition_hyps state, #var_set state, thm)
      handle Feedback.HOL_ERR holerr =>
        raise_final_error "remove_definitions" state thm holerr

    (* workaround for Z3 bug *)
    val final_thm = profile "check_proof(remove_extra_hyps)" remove_extra_hyps
      (#asserted_hyps state, final_thm)
      handle Feedback.HOL_ERR holerr =>
        raise_final_error "remove_extra_hyps" state final_thm holerr

    (* if the final theorem contains hyps that are not in `asl`, it likely means
       that we've run into a Z3 issue where it slightly modifies the original
       assumptions; as a workaround we try to remove those hyps here *)
    val final_thm = profile "check_proof(hyp_removal)" remove_hyps
      (asl, g, final_thm)
      handle Feedback.HOL_ERR holerr =>
        raise_final_error "hyp_removal" state final_thm holerr

    (* check that the final theorem contains no hyps other than those that have
       been asserted or those used by the hypothesis-removal workaround above *)
    val allowed_hyps = HOLset.union (#asserted_hyps state,
      HOLset.addList (Term.empty_tmset, boolSyntax.mk_neg g :: asl))
    val _ = profile "check_proof(hypcheck)" HOLset.isSubset
      (Thm.hypset final_thm, allowed_hyps) orelse
      raise ERR "check_proof" "final theorem contains additional hyp(s)"
      handle Feedback.HOL_ERR holerr =>
        raise_final_error "hypcheck" state final_thm holerr
  in
    final_thm
  end


  fun check_proof args : Thm.thm =
    profile "check_proof(total)" check_proof_impl args

end  (* local *)

end
