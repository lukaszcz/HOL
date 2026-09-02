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

  val asserted_membership_diagnostic =
    "HOLSMT_TRANSLATION_ASSERTED_MEMBERSHIP"

  (* Dedicated-theory failures must cross the generic rewrite handlers
     without inviting arithmetic or unification fallbacks. *)
  exception FP_REWRITE_ERROR of exn
  exception BAG_REWRITE_ERROR of exn
  exception STRING_REWRITE_ERROR of exn
  exception BV_REWRITE_ERROR of exn

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

  (* Instantiate `thm` (types and free variables) so its conclusion becomes
     `t`.  Fails if no such instantiation exists. *)
  fun exact_inst thm t =
    Drule.INST_TY_TERM (Term.match_term (Thm.concl thm) t) thm

  (***************************************************************************)
  (* functions that manipulate/access "global" state                         *)
  (***************************************************************************)

  type state = {
    (* The exact assertions emitted for the original goal.  An [asserted]
       proof node is admissible only when its parsed term is a member of this
       set; this is the enforcement half of translation round-trip identity. *)
    allowed_asserted_hyps : Term.term HOLset.set,
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
       hypotheses: fp(3)(bit-decomposition) must prove a definition before
       adding it through [state_define]. *)
    bit_decompositions : bit_decomposition list,
    (* Exact per-translation operator provenance.  Only definitions selected
       by SmtLib's EncodedSymbol records may be unfolded during replay. *)
    translation_definitions : SmtLib.emitted_definition list,
    (* One mutable atom cache for the complete proof replay.  Every general
       reduction node in this state shares its owning-theory expansions. *)
    skeleton_context : SmtSkeletonProve.context,
    z3_version : string
  }

  fun state_assert (s : state) (t : Term.term) : state =
    {
      allowed_asserted_hyps = #allowed_asserted_hyps s,
      asserted_hyps = HOLset.add (#asserted_hyps s, t),
      definition_hyps = #definition_hyps s,
      thm_cache = #thm_cache s,
      var_set = #var_set s,
      bit_decompositions = #bit_decompositions s,
      translation_definitions = #translation_definitions s,
      skeleton_context = #skeleton_context s,
      z3_version = #z3_version s
    }

  fun state_define (s : state) (terms : Term.term list) : state =
    {
      allowed_asserted_hyps = #allowed_asserted_hyps s,
      asserted_hyps = #asserted_hyps s,
      definition_hyps = HOLset.addList (#definition_hyps s, terms),
      thm_cache = #thm_cache s,
      var_set = #var_set s,
      bit_decompositions = #bit_decompositions s,
      translation_definitions = #translation_definitions s,
      skeleton_context = #skeleton_context s,
      z3_version = #z3_version s
    }

  fun state_cache_thm (s : state) (thm : Thm.thm) : state =
    {
      allowed_asserted_hyps = #allowed_asserted_hyps s,
      asserted_hyps = #asserted_hyps s,
      definition_hyps = #definition_hyps s,
      thm_cache = Net.insert (Thm.concl thm, thm) (#thm_cache s),
      var_set = #var_set s,
      bit_decompositions = #bit_decompositions s,
      translation_definitions = #translation_definitions s,
      skeleton_context = #skeleton_context s,
      z3_version = #z3_version s
    }

  fun state_inst_cached_thm (s : state) (t : Term.term) : Thm.thm =
    let
      val available = HOLset.union (#asserted_hyps s, #definition_hyps s)
      fun instantiate thm =
        let val thm = exact_inst thm t in
          if HOLset.isSubset (Thm.hypset thm, available) then thm
          else raise ERR "state_inst_cached_thm" "unavailable hypothesis"
        end
    in
      Lib.tryfind instantiate (Net.match t (#thm_cache s))
    end

  (* FP decomposition theorems carry proof-local packed-word definitions.
     Instantiating one cached decomposition at a different FP/BV pair creates
     a second definition for the same skolem and breaks checked definition
     elimination.  FP replay therefore reuses only the exact recorded
     conclusion; its cheap proforma rung can simply re-prove other instances. *)
  fun state_exact_cached_thm (s : state) (t : Term.term) : Thm.thm =
    Lib.tryfind
      (fn thm =>
        if Thm.concl thm ~~ t then thm
        else raise ERR "state_exact_cached_thm" "different conclusion")
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

  fun term_contains_measure pred tm =
    let
      val seen = ref Term.empty_tmset
      val visited = ref 0
      fun visit subterm =
        if HOLset.member (!seen, subterm) then false
        else
          (visited := !visited + 1;
           seen := HOLset.add (!seen, subterm);
           pred subterm orelse
           case Term.dest_term subterm of
             Term.COMB (rator, rand) => visit rator orelse visit rand
           | Term.LAMB (_, body) => visit body
           | _ => false)
      val found = visit tm
    in
      {found = found, visited = !visited}
    end

  fun term_contains_type_measure pred =
    term_contains_measure
      (fn subterm => type_contains pred (Term.type_of subterm))

  fun term_contains_type pred tm =
    #found (term_contains_type_measure pred tm)

  fun has_arith_atom tm =
    term_contains_type
      (fn ty =>
        Type.compare (ty, intSyntax.int_ty) = EQUAL orelse
        Type.compare (ty, realSyntax.real_ty) = EQUAL) tm

  fun has_word_atom tm =
    term_contains_type wordsSyntax.is_word_type tm

  fun exact_decimal_index function_name text =
    let
      val n = String.size text
      fun all_digits i = i = n orelse
        (Char.isDigit (String.sub (text, i)) andalso all_digits (i + 1))
      val _ = n > 0 andalso all_digits 0 orelse
        raise ERR function_name
          "fpa2bv symbol has a malformed numeric identifier"
    in
      case Int.fromString text of
        SOME index => index
      | NONE => raise ERR function_name
          "fpa2bv numeric identifier is outside the supported range"
    end

  fun fp_k_index version var =
    let
      val name = Lib.fst (Term.dest_var var)
      val {prefix, packed_suffix} = fp_skolem_naming version
      val prefix_size = String.size prefix
      val _ = String.isPrefix prefix name orelse
        raise ERR "fp_k_index"
          ("fpa2bv symbol violates the naming contract for Z3 anchor " ^
           version)
      val digits = String.extract (name, prefix_size, NONE)
      val n = String.size digits
      val _ = n > 0 andalso String.sub (digits, n - 1) = packed_suffix orelse
        raise ERR "fp_k_index"
          ("fpa2bv packed symbol violates the suffix contract for Z3 " ^
           "anchor " ^ version)
    in
      exact_decimal_index "fp_k_index"
        (String.substring (digits, 0, n - 1))
    end

  fun fp_inferred_packed_vars_in version registered =
    List.filter
      (fn var => wordsSyntax.is_word_type (Term.type_of var) andalso
        Lib.can (fp_k_index version) var)
      (HOLset.listItems registered)

  fun fp_inferred_packed_vars_with_provenance version registered assertions =
    if List.exists SmtFpProve.has_fp_theory_term assertions then
      fp_inferred_packed_vars_in version registered
    else
      []

  (* Validate the complete fpa2bv allocation at once.  A packed word owns
     exactly its declared width of Boolean skolems; no unallocated Boolean
     fpa2bv names may remain.  Z3 may interleave unrelated skolem identifiers,
     so ordering is deterministic but identifiers need not be consecutive.
     Returning [] on an incoherent allocation makes admission fail closed. *)
  fun fp_per_bit_definitions_in version packed_vars registered =
  let
    fun compare_index (left, right) =
      Int.compare (fp_k_index version left, fp_k_index version right)
    val bv_vars = Listsort.sort compare_index packed_vars
    val _ = List.all (fn bv =>
      wordsSyntax.is_word_type (Term.type_of bv) andalso
      HOLset.member (registered, bv)) bv_vars orelse
      raise ERR "fp_per_bit_definitions"
        "packed fpa2bv symbol is absent or has the wrong sort"
    val bool_vars = Listsort.sort compare_index
      (List.filter
        (fn var => Term.type_of var = Type.bool andalso
          Lib.can (fp_k_index version) var)
        (HOLset.listItems registered))
    fun allocate ([], remaining, definitions) =
          if List.null remaining then List.rev definitions
          else raise ERR "fp_per_bit_definitions"
            "unallocated fpa2bv Boolean skolems"
      | allocate (bv :: bvs, remaining, definitions) =
          let
            val width = Arbnum.toInt (wordsSyntax.size_of bv)
            val _ = List.length remaining >= width orelse
              raise ERR "fp_per_bit_definitions"
                "too few fpa2bv Boolean skolems"
            val bits = List.take (remaining, width)
            val remaining = List.drop (remaining, width)
            fun definition (offset, bit) =
              boolSyntax.mk_eq (bit, wordsSyntax.mk_word_bit
                (numSyntax.term_of_int offset, bv))
          in
            allocate (bvs, remaining,
              List.revAppend
                (List.map definition
                   (ListPair.zip (List.tabulate (width, Lib.I), bits)),
                 definitions))
          end
  in
    allocate (bv_vars, bool_vars, [])
  end
  handle Fail _ => []
       | Option.Option => []
       | Overflow => []
       | Feedback.HOL_ERR _ => []

  fun fp_packed_vars (state : state) =
    case List.map
        (fn ({bv_var, ...} : bit_decomposition) => bv_var)
        (#bit_decompositions state) of
      [] =>
        fp_inferred_packed_vars_with_provenance
          (#z3_version state) (#var_set state)
          (HOLset.listItems (#allowed_asserted_hyps state))
    | recorded => recorded

  fun fp_per_bit_definitions (state : state) =
    fp_per_bit_definitions_in (#z3_version state)
      (fp_packed_vars state) (#var_set state)

  (* A word can disappear syntactically after fpa2bv lowering while its
     validated per-bit skolems remain.  Only bits from a complete coherent
     allocation are provenance; a lone or merely name-shaped variable is
     not. *)
  fun has_allocated_fp_bv_atom_in version packed registered target =
    let
      val definitions = fp_per_bit_definitions_in
        version packed registered
      val allocated = HOLset.addList (Term.empty_tmset,
        List.map (Lib.fst o boolSyntax.dest_eq) definitions)
    in
      not (List.null definitions) andalso
      #found (term_contains_measure
        (fn subterm => Term.is_var subterm andalso
          HOLset.member (allocated, subterm)) target)
    end

  fun has_allocated_fp_bv_atom (state : state) target =
    has_allocated_fp_bv_atom_in (#z3_version state)
      (fp_packed_vars state) (#var_set state) target

  fun require_bv_family function_name target =
    if has_word_atom target then ()
    else raise ERR function_name "goal is outside the bit-vector family"

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

  val ediv_tm = Term.prim_mk_const {Thy = "integer", Name = "ediv"}
  val emod_tm = Term.prim_mk_const {Thy = "integer", Name = "emod"}

  (* Collect divisors from the whole integer div/mod family.  Canonical
     totalization may expose raw [ediv]/[emod], so this is deliberately keyed
     by operation identity and arity rather than by a recorded clause shape. *)
  fun ediv_emod_divisors target =
    let
      fun divisor term =
        case boolSyntax.strip_comb term of
          (head, [_, denominator]) =>
            if List.exists (Term.same_const head)
                 [ediv_tm, emod_tm,
                  SmtReplayCanon.smt_ediv_total_tm,
                  SmtReplayCanon.smt_emod_total_tm] then
              SOME denominator
            else NONE
        | _ => NONE
      fun add (denominator, denominators) =
        if List.exists (Term.aconv denominator) denominators then denominators
        else denominator :: denominators
    in
      List.foldl add []
        (List.mapPartial divisor (Library.subterms target))
    end

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

  val ground_subterm_eval_max_nodes = 4096
  val ground_subterm_eval_max_calls = 8
  val ground_subterm_eval_steps_per_call = 100000

  (* One bounded pass over an arithmetic obligation.  At an open node the
     conversion visits each immediate child once.  At a closed compound it
     spends one EVAL budget: a changed compound is selected and its children
     are not visited; an unchanged compound is not selected and the pass
     continues once through its children.  Thus every node is attempted at
     most once and maximal closed compounds changed by bounded EVAL are never
     revisited.  The 4096-node preflight and eight-attempt guard are hard:
     exceeding either raises without returning a rewrite.  Each EVAL call
     instead has a soft 100000-step stopper.  Reaching it may return a
     partially changed kernel theorem, and the conversion accepts that proved
     partial rewrite.  Wholly unchanged inputs raise without manufacturing a
     rewrite. *)
  fun ground_subterm_eval_conv target =
    let
      val nodes = SmtResource.term_nodes_up_to
        ground_subterm_eval_max_nodes target
      val _ = nodes <= ground_subterm_eval_max_nodes orelse
        raise ERR "ground_subterm_eval_conv"
          ("resource limit: input exceeds " ^
           Int.toString ground_subterm_eval_max_nodes ^
           " syntax nodes")
      val calls = ref 0
      fun eval_closed tm =
        let
          val _ = !calls < ground_subterm_eval_max_calls orelse
            raise ERR "ground_subterm_eval_conv"
              ("resource limit: more than " ^
               Int.toString ground_subterm_eval_max_calls ^
               " closed-compound attempts")
          val _ = calls := !calls + 1
          val th = bossLib.EVALn ground_subterm_eval_steps_per_call tm
          val (lhs, rhs) = boolSyntax.dest_eq (Thm.concl th)
        in
          if lhs ~~ rhs then raise Conv.UNCHANGED else th
        end
      fun one_pass tm =
        if List.null (Term.free_vars tm) then
          if Term.is_comb tm orelse Term.is_abs tm then
            (eval_closed tm
             handle Conv.UNCHANGED =>
               descend tm)
          else raise Conv.UNCHANGED
        else
          descend tm
      and descend tm =
        if Term.is_comb tm then
          let
            val (rator, rand) = Term.dest_comb tm
            val rator_thm = SOME (one_pass rator)
              handle Conv.UNCHANGED => NONE
            val rand_thm = SOME (one_pass rand)
              handle Conv.UNCHANGED => NONE
          in
            case (rator_thm, rand_thm) of
              (SOME rator_thm, SOME rand_thm) =>
                Thm.MK_COMB (rator_thm, rand_thm)
            | (SOME rator_thm, NONE) => Thm.AP_THM rator_thm rand
            | (NONE, SOME rand_thm) => Thm.AP_TERM rator rand_thm
            | (NONE, NONE) => raise Conv.UNCHANGED
          end
        else if Term.is_abs tm then
          let
            val (binder, body) = Term.dest_abs tm
          in
            Thm.ABS binder (one_pass body)
          end
        else raise Conv.UNCHANGED
    in
      Conv.CHANGED_CONV one_pass target
    end

  fun profiled_ground_subterm_eval_conv target =
    profile "arith-linear(5)(ground-subterm-eval)"
      ground_subterm_eval_conv target

  (* Returns a proof of `t` using arithmetic decision procedures. This function
     is used by both `z3_th_lemma_arith` and `z3_rewrite`. *)
  fun arith_prove t =
    (* E1(a): exact instantiation decides the rdiv intro-cancel clause. *)
    profile "arith(1)(rdiv-intro-cancel)"
      (exact_inst SMT_RDIV_INTRO_CANCEL_CLAUSE) t
    handle Feedback.HOL_ERR _ =>
    (* E1(a): exact instantiation decides the rdiv cancel clause. *)
    profile "arith(2)(rdiv-cancel)" (exact_inst SMT_RDIV_CANCEL_CLAUSE) t
    handle Feedback.HOL_ERR _ =>
    (* E1(a): proved rdiv normalization ends in linear real arithmetic. *)
    profile "arith(3)(rdiv-normalize)" arith_prove_smt_rdiv t
    handle Feedback.HOL_ERR _ =>
    (* E1(a): the nested procedure decides linear int/real arithmetic. *)
    profile "arith(4)(linear)" arith_prove_linear t
    handle Feedback.HOL_ERR _ =>
    (* E1(b): div/mod replay is general with a loud two-divisor boundary. *)
    profile "arith(5)(ediv-emod)" arith_prove_ediv_emod t
    handle Feedback.HOL_ERR _ =>
    (* E1(b): this handles general matched nonlinear integer products. *)
    profile "arith(6)(integer-product-bounds)" int_product_prove t
    handle Feedback.HOL_ERR _ =>
    (* E1(b): this handles the real zero-factor clause family. *)
    profile "arith(7)(real-zero-factor)" real_zero_factor_clause_prove t
    handle Feedback.HOL_ERR _ =>
      (* nonlinear fallback: only after linear tactics fail, to avoid
         expensive SOS certificate search on goals linear tactics handle *)
      if Library.is_nonlinear t andalso
         not (Library.contains_nonpolynomial_arithmetic t) then
        (* E1(b): the general NLA procedure fails loudly at its boundary. *)
        profile "arith(8)(nla)" Library.nla_prove t
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

  and arith_prove_ediv_emod t =
    let
      (* Unfold totalized div/mod before the shared alias canonicalizer: its
         canonical emod spelling is an ediv polynomial, while Z3 conclusions
         can compare a totalized operation with the corresponding raw one.
         Keeping both raw operations aligned after the proved zero/nonzero
         definition split lets the arithmetic ladder handle any dividend. *)
      val unfold_total_conv = Rewrite.PURE_REWRITE_CONV
        [HolSmtTheory.smt_ediv_total_def,
         HolSmtTheory.smt_emod_total_def]
      val totalization = unfold_total_conv t
        handle Conv.UNCHANGED => Thm.REFL t
      val unfolded = boolSyntax.rhs (Thm.concl totalization)
      val aliases = SmtReplayCanon.cpc_term_canon_conv unfolded
      val normalization = Thm.TRANS totalization aliases
      val normalized = boolSyntax.rhs (Thm.concl normalization)
      val divisors = ediv_emod_divisors normalized
      val _ = not (List.null divisors) orelse
        raise ERR "arith_prove_ediv_emod" "no integer div/mod operation"
      (* Three sign branches are complete for each divisor but multiply
         across unrelated divisors.  This rung is the bounded two-divisor
         fragment; larger formulas fail closed and continue down the replay
         ladder instead of starting exponential case expansion.  Dividend
         and denominator expressions themselves remain unrestricted. *)
      val _ = List.length divisors <= 2 orelse
        raise ERR "arith_prove_ediv_emod"
          "outside bounded two-divisor integer div/mod arithmetic"
      val simplify = bossLib.ASM_SIMP_TAC intLib.int_ss
        [integerTheory.EDIV_DEF, integerTheory.EMOD_DEF,
         integerTheory.INT_ABS, integerTheory.INT_DIV_0,
         integerTheory.INT_MOD0]
      fun finish () =
        Tactical.TRY intLib.ARITH_TAC
        THEN simplify
        THEN Tactical.TRY intLib.ARITH_TAC
      fun split [] = finish ()
        | split (denominator :: rest) =
            let
              val zero = boolSyntax.mk_eq
                (denominator, intSyntax.zero_tm)
              val positive = intSyntax.mk_less
                (intSyntax.zero_tm, denominator)
              val negative = intSyntax.mk_less
                (denominator, intSyntax.zero_tm)
            in
              (* Split zero first so both sign branches retain the explicit
                 nonzero fact needed by INT_DIV_0 and INT_MOD0. *)
              Tactic.ASM_CASES_TAC zero THENL
                [Tactical.TRY intLib.ARITH_TAC THEN split rest,
                 Tactic.ASM_CASES_TAC positive THENL
                   [Tactical.TRY intLib.ARITH_TAC THEN split rest,
                    SUBGOAL_THEN negative ASSUME_TAC THENL
                      [intLib.ARITH_TAC,
                       Tactical.TRY intLib.ARITH_TAC THEN split rest]]]
            end
      val proof = Tactical.TAC_PROOF (([], normalized), split divisors)
    in
      Thm.EQ_MP (Thm.SYM normalization) proof
    end

  and arith_prove_linear t =
    let
      fun arith_tactic rung (goal as (_, term)) =
        if term_contains_real_ty term then
          profile ("arith-linear(" ^ rung ^ ")(real)")
            RealField.REAL_ARITH_TAC goal
        else
          profile ("arith-linear(" ^ rung ^ ")(int)") intLib.ARITH_TAC goal
      val TRY = Tactical.TRY
    in
      Tactical.TAC_PROOF (([], t),
        (* E1(a): proved unfolding normalizes the integer div/mod syntax. *)
        (* rewrite the `ediv` and `emod` symbols so that the arithmetic
           decision procedures can solve terms containing these functions *)
        profile "arith-linear(1)(unfold-div-mod)"
          (PURE_REWRITE_TAC[integerTheory.EDIV_DEF, integerTheory.EMOD_DEF])
        (* the next rewrites are a workaround for this issue:
           https://github.com/HOL-Theorem-Prover/HOL/issues/1207 *)
        (* E1(a): proved alias rewriting preserves the linear fragment. *)
        >> profile "arith-linear(2)(normalize-aliases)"
          (PURE_REWRITE_TAC
            [integerTheory.INT_ABS, integerTheory.NUM_OF_INT])
        (* E1(a): ARITH decides the normalized linear int/real fragment. *)
        >> TRY (arith_tactic "3")
        (* E1(a): the arithmetic simpsets decide polynomial normalization. *)
        >> profile "arith-linear(4)(polynomial-normalize)"
          (bossLib.RW_TAC
            (bossLib.arith_ss ++ intSimps.INT_RWTS_ss ++
             intSimps.INT_ARITH_ss ++ realSimps.REAL_ARITH_ss)
            [Conv.GSYM integerTheory.INT_NEG_MINUS1])
        (* E1(a): bounded evaluation decides closed arithmetic subterms. *)
        >> TRY (Tactic.CONV_TAC profiled_ground_subterm_eval_conv)
        (* E1(a): the final ARITH pass decides the remaining linear goal. *)
        >> TRY (arith_tactic "6"))
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

  fun z3_asserted (state : state, t) =
  let
    val _ = List.exists (Term.aconv t)
      (HOLset.listItems (#allowed_asserted_hyps state)) orelse
      raise ERR "z3_asserted"
        (asserted_membership_diagnostic ^
         ": proof asserted a term outside {~goal} U assumptions; term=" ^
         Library.term_to_string t)
    (* [ASSUME] is sound only after the translation-membership gate above. *)
    val theorem = Thm.ASSUME t
  in
    (state_assert state t, theorem)
  end

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
    Library.require_fastpath "Z3 def-axiom proforma" t
      (fn target =>
        (state,
         Z3_ProformaThms.prove Z3_ProformaThms.def_axiom_thms target)) t
    handle Feedback.HOL_ERR _ =>
    (* Array-encoded Set literals appear in Z3's Tseitin clauses as a
       select of the parsed EMPTY/UNIV predicate.  Normalize those recorded
       const-array forms before the propositional def-axiom cases below. *)
    (state, SmtArrayProve.set_simp_prove t)
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
    handle Feedback.HOL_ERR _ =>
      (state, Tactical.TAC_PROOF (([], t),
        Tactical.THEN
          (Tactical.REPEAT Tactic.COND_CASES_TAC,
           bossLib.ASM_SIMP_TAC boolSimps.bool_ss
             [boolTheory.EQ_SYM_EQ])))
    handle Feedback.HOL_ERR _ =>
      (state, tautLib.TAUT_PROVE t)

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

  (* A :lambda-def axiom is printed pointwise, while replay records the
     underlying function definition.  HOL's first-order matcher deliberately
     refuses to instantiate a schematic function with a term containing the
     matched binders, so derive every binder arity by iteration.  Repeated
     AP_THM followed by beta is the kernel derivation underlying the
     corresponding FUN_EQ_THM instance. *)
  fun z3_intro_def_lambda (state, t) =
  let
    val (vars, body) = boolSyntax.strip_forall t
    val _ = if List.null vars then raise ERR "z3_intro_def_lambda"
      "pointwise axiom has no binders" else ()
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
          ("unsupported :lambda-def intro-def shape: " ^
           "pointwise axiom does not define a Z3 name")
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

  fun z3_intro_def_general (state, target) =
  let
    val names = List.filter (fn variable =>
      HOLset.member (#var_set state, variable)) (Term.free_vars target)
    fun contains variable term =
      List.exists (Term.aconv variable) (Term.free_vars term)
    fun orient (name, residue) =
      if Library.is_def_oriented (#var_set state) (name, residue) then
        boolSyntax.mk_eq (name, residue)
      else
        boolSyntax.mk_eq (residue, name)
    fun prove_definition (name, residue) =
      let
        val definition = orient (name, residue)
        val condition =
          let
            val (left, right) = boolSyntax.dest_eq definition
          in
            case Lib.total boolSyntax.dest_cond right of
              SOME (condition, _, _) => SOME condition
            | NONE =>
                case Lib.total boolSyntax.dest_cond left of
                  SOME (condition, _, _) => SOME condition
                | NONE => NONE
          end
        val tactic =
          case condition of
            SOME condition =>
              Tactical.THEN
                (Tactic.ASM_CASES_TAC condition,
                 bossLib.ASM_SIMP_TAC boolSimps.bool_ss
                   [boolTheory.EQ_SYM_EQ])
          | NONE =>
              Tactical.THEN
                (Tactical.REPEAT Tactic.COND_CASES_TAC,
                 bossLib.ASM_SIMP_TAC boolSimps.bool_ss
                   [boolTheory.EQ_SYM_EQ])
        val theorem = Tactical.TAC_PROOF (([definition], target),
          tactic)
      in
        (state_define state [definition], theorem)
      end
    fun ordinary_candidates name =
      List.map (fn residue => (name, residue))
        (List.filter (fn residue =>
          Type.compare (Term.type_of residue, Term.type_of name) = EQUAL andalso
          not (Term.aconv residue name) andalso not (contains name residue))
          (Library.subterms target))
    fun equality_with_name name equation =
      let val (left, right) = boolSyntax.dest_eq equation in
        if Term.aconv left name andalso not (contains name right) then right
        else if Term.aconv right name andalso not (contains name left) then left
        else raise ERR "z3_intro_def_general" "equality has another name"
      end
    fun conditional_candidate name =
      let
        val (first, second) = boolSyntax.dest_conj target
        val (first_guard, first_equality) = boolSyntax.dest_disj first
        val (second_guard, second_equality) = boolSyntax.dest_disj second
        val condition = boolSyntax.dest_neg first_guard
        val _ = Term.aconv condition second_guard orelse
          raise ERR "z3_intro_def_general" "conditional guards differ"
        val then_value = equality_with_name name first_equality
        val else_value = equality_with_name name second_equality
      in
        (name, boolSyntax.mk_cond (condition, then_value, else_value))
      end
    val candidates = List.concat (List.map (fn name =>
      (conditional_candidate name :: ordinary_candidates name)
      handle Feedback.HOL_ERR _ => ordinary_candidates name) names)
  in
    Lib.tryfind prove_definition candidates
  end

  fun z3_intro_def (args as (_, t)) =
    if boolSyntax.is_forall t then z3_intro_def_lambda args
    else z3_intro_def_general args
      handle Feedback.HOL_ERR holerr =>
        raise ERR "z3_intro_def"
          ("general intro-def reconstruction failed: " ^
           Feedback.message_of holerr)

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
     (!x. ?y. !z. P x y z) = (!a. ?b. !c. Q a b c)

     The proof-bind variables are the binders introduced by this inference.
     Target binders determine only their logical kind; their variables are
     alpha-renamed to the annotation before rigidly checking the pointwise
     premise. *)
  fun quant_intro_annotation_mismatch detail =
    raise ERR "quant_intro_annotation_mismatch"
      ("quant_intro_annotation_mismatch: quant-intro proof-bind " ^
       "annotation mismatch: " ^ detail)

  fun z3_quant_intro (state, annotation, thm, t) =
  let
    datatype binder_kind = ForallBinder | ExistsBinder | AbsBinder

    (* Z3's quant-intro also introduces lambda binders for higher-order
       sequence functions. *)
    fun dest_binder term : (binder_kind * term * term) option =
      if boolSyntax.is_forall term then
        let val (var, body) = boolSyntax.dest_forall term
        in SOME (ForallBinder, var, body) end
      else if boolSyntax.is_exists term then
        let val (var, body) = boolSyntax.dest_exists term
        in SOME (ExistsBinder, var, body) end
      else if Term.is_abs term then
        let val (var, body) = Term.dest_abs term
        in SOME (AbsBinder, var, body) end
      else
        NONE

    fun kind_name ForallBinder = "forall"
      | kind_name ExistsBinder = "exists"
      | kind_name AbsBinder = "lambda"

    fun same_kind (ForallBinder, ForallBinder) = true
      | same_kind (ExistsBinder, ExistsBinder) = true
      | same_kind (AbsBinder, AbsBinder) = true
      | same_kind _ = false

    (* Peel exactly the annotated block and rename its target variables to
       the proof-bind variables.  This is recursive over the annotation, so
       neither supported binder forms nor arity depend on corpus examples. *)
    fun peel side term =
      let
        fun recurse [] body kinds = (List.rev kinds, body)
          | recurse (annotated :: rest) body kinds =
              (case dest_binder body of
                NONE => quant_intro_annotation_mismatch
                  (side ^ " has fewer binders than its annotation")
              | SOME (kind, target, residue) =>
                  if Type.compare
                      (Term.type_of annotated, Term.type_of target) = EQUAL
                  then recurse rest
                    (Term.subst [target |-> annotated] residue)
                    (kind :: kinds)
                  else quant_intro_annotation_mismatch
                    (side ^ " binder type differs from its annotation"))
      in
        recurse annotation term []
      end

    fun check_kinds [] = ()
      | check_kinds ((left, right) :: rest) =
          if same_kind (left, right) then check_kinds rest
          else quant_intro_annotation_mismatch
            ("conclusion binder kinds differ (" ^ kind_name left ^
             " versus " ^ kind_name right ^ ")")

    (* Replace H[v1,...,vn] by its universal closure as a hypothesis.  The
       closure still entails H at the current variables, but none of those
       variables remains free in the hypotheses seen by ABS/FORALL_EQ/
       EXISTS_EQ. *)
    fun close_hypothesis hyp result =
      let
        val captured = List.filter (fn var => Term.free_in var hyp) annotation
      in
        if List.null captured then result
        else
          let
            val closed = boolSyntax.list_mk_forall (captured, hyp)
            val instance = Drule.SPECL captured (Thm.ASSUME closed)
          in
            Drule.PROVE_HYP instance result
          end
      end

    fun add_binder (ForallBinder, var) result =
          Drule.FORALL_EQ var result
      | add_binder (ExistsBinder, var) result =
          Drule.EXISTS_EQ var result
      | add_binder (AbsBinder, var) result = Thm.ABS var result

    val _ = if List.null annotation then
        quant_intro_annotation_mismatch "annotation is empty"
      else if List.all Term.is_var annotation then ()
      else quant_intro_annotation_mismatch
        "annotation contains a non-variable binder"
    val (lhs, rhs) = boolSyntax.dest_eq t
      handle Feedback.HOL_ERR _ => quant_intro_annotation_mismatch
        "conclusion is not an equality"
    val (lhs_kinds, annotated_lhs) = peel "left conclusion" lhs
    val (rhs_kinds, annotated_rhs) = peel "right conclusion" rhs
    val _ = check_kinds (ListPair.zip (lhs_kinds, rhs_kinds))
    val (premise_lhs, premise_rhs) = boolSyntax.dest_eq (Thm.concl thm)
      handle Feedback.HOL_ERR _ => quant_intro_annotation_mismatch
        "pointwise premise is not an equality"
    val _ = if premise_lhs ~~ annotated_lhs then ()
      else quant_intro_annotation_mismatch
        ("annotated left conclusion body is not alpha-equal to the " ^
         "pointwise premise")
    val _ = if premise_rhs ~~ annotated_rhs then ()
      else quant_intro_annotation_mismatch
        ("annotated right conclusion body is not alpha-equal to the " ^
         "pointwise premise")
    val thm = List.foldl
      (fn (hyp, result) => close_hypothesis hyp result) thm (Thm.hyp thm)
    val _ = if List.exists
        (fn hyp => List.exists (fn var => Term.free_in var hyp) annotation)
        (Thm.hyp thm)
      then raise ERR "z3_quant_intro"
        "an annotated binder remains free in a premise hypothesis"
      else ()
    val thm = List.foldr
      (fn (binder, result) => add_binder binder result) thm
      (ListPair.zip (lhs_kinds, annotation))
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

  fun word_arith_prove target =
    Drule.EQT_ELIM (wordsLib.WORD_ARITH_CONV target)
      handle Conv.UNCHANGED => raise ERR "word_arith_prove" "unchanged"

  (* A counterexample means only that this decision procedure cannot prove
     the current rewrite.  Normalize that signal to the ladder's ordinary
     HOL_ERR failure so the next procedure (and, after BBLAST, the existing
     arithmetic route) still gets a chance. *)
  fun word_decider_attempt name prove target =
    prove target
      handle HolSatLib.SAT_cex _ =>
        raise ERR name "word decision procedure found a counterexample"

  fun bv_resource_prove_after_admission case_id prove target =
    SmtResource.with_resource_step_time "BitVector" case_id
      (fn target =>
        (SmtResource.check_resource_goal "BitVector" case_id target;
         prove target)) target

  fun bv_resource_prove case_id prove target =
    (require_bv_family case_id target;
     bv_resource_prove_after_admission case_id prove target)

  fun bv_next_rung first second target =
    first target
    handle Feedback.HOL_ERR holerr =>
      if SmtResource.is_resource_gate holerr then
        raise Feedback.HOL_ERR holerr
      else
        second target

  fun word_decide_raw target =
    (* E1(a): BBLAST decides the finite bit-vector fragment. *)
    profile "word-decide(1)(BBLAST)"
      (word_decider_attempt "word_decide(BBLAST)"
        (Feedback.trace ("print blast counterexamples", 0)
          blastLib.BBLAST_PROVE)) target

  fun word_decide target =
    bv_resource_prove "word-decide" word_decide_raw target

  fun occurring_translation_definitions definitions target =
    List.filter
      (fn definition =>
        let
          val head = SmtLib.emitted_definition_head definition
          fun matches subterm =
            if Term.is_const head andalso Term.is_const subterm then
              Term.same_const head subterm
            else
              subterm ~~ head
        in
          #found (term_contains_measure matches target)
        end)
      definitions

  (* A definition can admit the BV rewrite rung only when its registered,
     kernel-checked unfolding itself exposes the word family.  Merely
     occurring in the target is not enough: integer totalizations, for
     example, are emitted definitions but do not make an integer goal BV. *)
  fun definition_exposes_bv_family definition =
    has_word_atom (Thm.concl
      (SmtLib.emitted_definition_theorem definition))

  datatype bv_rewrite_route =
      DirectBV of SmtLib.emitted_definition list
    | LoweredBV
    | DefinedBV of SmtLib.emitted_definition list
    | OutsideBV

  fun classify_bv_rewrite direct_bv lowered_bv definitions target =
    let
      val occurring = List.filter definition_exposes_bv_family
        (occurring_translation_definitions definitions target)
    in
      if direct_bv target then DirectBV occurring
      else if lowered_bv target then LoweredBV
      else if List.null occurring then OutsideBV
      else DefinedBV occurring
    end

  (* One resource envelope owns the complete rewrite(17) operation: both
     size checks, the kernel normalization, and the final BBLAST.  Filtering
     definitions before entering this boundary prevents unrelated emitted
     definitions from admitting or charging a non-BV rewrite. *)
  fun rewrite17_under_budget normalize decide definitions target =
    let
      val theorems = List.map SmtLib.emitted_definition_theorem definitions
      val _ = not (List.null definitions) orelse
        raise ERR "rewrite17_under_budget"
          "translation emitted no definitional symbols"
      val normalization = normalize theorems target
      val (normalization_lhs, normalized) =
        boolSyntax.dest_eq (Thm.concl normalization)
      val _ = normalization_lhs ~~ target orelse
        raise ERR "rewrite17_under_budget"
          "normalization theorem has the wrong left-hand side"
      val _ = not (Term.aconv target normalized) orelse
        raise ERR "rewrite17_under_budget"
          "translation definitions did not occur in rewrite"
      val _ = require_bv_family "rewrite17_under_budget" normalized
      val _ = SmtResource.check_resource_goal
        "BitVector" "rewrite(17)" normalized
      val decision = decide normalized
    in
      Thm.EQ_MP (Thm.SYM normalization) decision
    end
    handle Conv.UNCHANGED =>
      raise ERR "rewrite17_under_budget"
        "translation definitions did not occur in rewrite"

  fun rewrite17 normalize decide definitions target =
    bv_resource_prove_after_admission "rewrite(17)"
      (rewrite17_under_budget normalize decide definitions) target

  fun bv_rewrite_prove_with_context rewrite_profile direct_bv lowered_bv
      definitions target =
    let
      val route = classify_bv_rewrite
        direct_bv lowered_bv definitions target
      fun rewrite16 target =
        bv_resource_prove_after_admission "rewrite(16)"
          (Library.require_fastpath "Z3 rewrite WORD_ARITH_CONV" target
            (rewrite_profile "rewrite(16)(WORD_ARITH_CONV)"
              (word_decider_attempt "z3_rewrite(WORD_ARITH_CONV)"
                word_arith_prove))) target
      fun rewrite17_production definitions target =
        rewrite_profile "rewrite(17)(translator-definitions+word)"
          (rewrite17 Rewrite.PURE_REWRITE_CONV word_decide_raw definitions)
          target
      fun rewrite18 case_id target =
        bv_resource_prove_after_admission case_id
          (rewrite_profile "rewrite(18)(BBLAST)"
            (word_decider_attempt "z3_rewrite(BBLAST)"
              (Feedback.trace ("print blast counterexamples", 0)
                blastLib.BBLAST_PROVE))) target
    in
      case route of
        DirectBV occurring =>
          bv_next_rung rewrite16
            (if List.null occurring then
               rewrite18 "rewrite(18)"
             else
               bv_next_rung (rewrite17_production occurring)
                 (rewrite18 "rewrite(18)")) target
      | LoweredBV =>
          (* Boolean fpa2bv residue bypasses inapplicable WORD_ARITH and
             definition scans, but uses the same gated complete BBLAST. *)
          rewrite18 "rewrite(18)(lowered-bv)" target
      | DefinedBV occurring => rewrite17_production occurring target
      | OutsideBV =>
          raise ERR "bv_rewrite_prove" "goal is outside the BV rewrite family"
    end

  fun bv_rewrite_prove rewrite_profile (state : state) =
    bv_rewrite_prove_with_context rewrite_profile has_word_atom
      (has_allocated_fp_bv_atom state) (#translation_definitions state)

  fun fp_bit_decompositions (state : state) =
    List.map
      (fn ({fp_var, bv_var, equation} : bit_decomposition) =>
        {fp_var = fp_var, bv_var = bv_var, equation = equation}
          : SmtFpProve.bit_decomposition)
      (#bit_decompositions state)

  fun is_pack_of fp_var tm =
    let
      val (head, argument) = Term.dest_comb tm
      val {Thy, Name, ...} = Term.dest_thy_const head
    in
      Thy = "smtfloat" andalso Name = "smtfp_pack_bv" andalso
      argument ~~ fp_var
    end
    handle Feedback.HOL_ERR _ => false

  (* Recursive replay can encounter one decomposition while proving a later
     dependency, then return to the same parser-recorded rewrite.  Reusing
     the already established packed definition is sound; a conflicting
     proof-local definition remains ineligible. *)
  fun eligible_fp_bit_decompositions (state : state) =
    let
      val definitions = HOLset.listItems (#definition_hyps state)
      fun eligible ({fp_var, bv_var, ...} : SmtFpProve.bit_decomposition) =
        case List.filter
            (fn definition =>
              case Lib.total boolSyntax.dest_eq definition of
                SOME (lhs, _) => lhs ~~ bv_var
              | NONE => false)
            definitions of
          [] => true
        | matching =>
            List.all
              (fn definition =>
                is_pack_of fp_var (Lib.snd
                  (boolSyntax.dest_eq definition)))
              matching
    in
      List.filter eligible (fp_bit_decompositions state)
    end

  (* This is Boolean normalization underneath a negated existential.
     HOL's simplifier descends through every quantifier, so this procedure
     covers any binder count without a one-binder proforma. *)
  fun quantified_boolean_rewrite_prove target =
    let
      fun dest_negated_exists tm =
        let
          val existential = boolSyntax.dest_neg tm
          val (variables, body) = boolSyntax.strip_exists existential
          val _ = List.null variables andalso
            raise ERR "quantified_boolean_rewrite_prove"
              "negated existential has no binders"
        in body end
      val (left, right) = boolSyntax.dest_eq target
      val _ = (dest_negated_exists left; dest_negated_exists right)
        handle Feedback.HOL_ERR _ =>
        raise ERR "quantified_boolean_rewrite_prove"
          "rewrite is not between negated existential formulas"
    in
      Tactical.TAC_PROOF (([], target),
        bossLib.SIMP_TAC boolSimps.bool_ss [boolTheory.IMP_DISJ_THM])
    end

  fun assert_rewrite_definitions state definitions =
    List.app (fn definition =>
      let val (lhs, _) = boolSyntax.dest_eq definition in
        if HOLset.member (#var_set state, lhs) then ()
        else raise ERR "z3_rewrite"
          ("unification produced a definition outside the proof variable " ^
           "set: " ^ Library.term_to_string definition)
      end) definitions

  (* Canonicalize Boolean polarity before the proof-local unifier.  Even
     negation prefixes are eliminated with NOT_NOT_INTRO; if the remaining
     sides have opposite polarity, NOT_REVERSE reduces the obligation to a
     checked complementary definition.  No proposition is assumed. *)
  fun boolean_normalized_unification (lhs, rhs, var_set) =
    let
      fun normalize tm =
        let
          val body = boolSyntax.dest_neg (boolSyntax.dest_neg tm)
          val step = Thm.SYM (Thm.SPEC body NOT_NOT_INTRO)
        in
          Thm.TRANS step (normalize body)
        end
        handle Feedback.HOL_ERR _ => Thm.REFL tm
      val lhs_normalized = normalize lhs
      val rhs_normalized = normalize rhs
      val lhs' = boolSyntax.rhs (Thm.concl lhs_normalized)
      val rhs' = boolSyntax.rhs (Thm.concl rhs_normalized)
      fun complementary_unification () =
        let
          val rhs_body = boolSyntax.dest_neg rhs'
          val premise = Library.gen_instantiation
            (rhs_body, boolSyntax.mk_neg lhs', var_set)
          val p = Term.mk_var ("p", Type.bool)
          val q = Term.mk_var ("q", Type.bool)
        in
          Thm.MP (Thm.INST [p |-> rhs_body, q |-> lhs'] NOT_REVERSE)
            premise
        end
        handle Feedback.HOL_ERR _ =>
          let
            val lhs_body = boolSyntax.dest_neg lhs'
            val premise = Library.gen_instantiation
              (lhs_body, boolSyntax.mk_neg rhs', var_set)
            val p = Term.mk_var ("p", Type.bool)
            val q = Term.mk_var ("q", Type.bool)
          in
            Thm.SYM
              (Thm.MP (Thm.INST [p |-> lhs_body, q |-> rhs'] NOT_REVERSE)
                premise)
          end
      val unified = Library.gen_instantiation (lhs', rhs', var_set)
        handle Feedback.HOL_ERR _ => complementary_unification ()
    in
      Thm.TRANS lhs_normalized
        (Thm.TRANS unified (Thm.SYM rhs_normalized))
    end

  fun linear_arithmetic_rewrite_prove target =
    let
      fun arithmetic_variable variable =
        SmtReplayCanon.is_arith_type (Term.type_of variable)
      fun arithmetic_constant tm =
        Term.is_const tm andalso
        let val {Thy, ...} = Term.dest_thy_const tm in
          Thy = "integer" orelse Thy = "real" orelse Thy = "intreal"
        end
      val _ = List.all arithmetic_variable (Term.free_vars target) orelse
        raise ERR "linear_arithmetic_rewrite_prove"
          "rewrite has a non-arithmetic variable"
      val _ = Lib.can (HolKernel.find_term arithmetic_constant) target orelse
        raise ERR "linear_arithmetic_rewrite_prove"
          "rewrite has no integer or real operator"
      val _ = not (Lib.can
        (HolKernel.find_term (Lib.can boolSyntax.dest_cond)) target) orelse
        raise ERR "linear_arithmetic_rewrite_prove"
          "conditional rewrite is outside polynomial normal form"
    in
      SmtReplayCanon.arith_poly_norm_prove target
    end

  fun rewrite_ladder_exhausted attempts target =
    ERR "z3_rewrite"
      ("rewrite ladder exhausted; attempted fragment classes=" ^
       "[" ^ String.concatWith ", " attempts ^ "]; conclusion=" ^
       Library.term_to_string target)

  datatype recursive_rewrite_site =
      RecursiveSkeleton
    | RecursiveEquality
    | RecursiveAbstraction

  (* A recursive rewrite returns through a fresh [z3_rewrite] exception
     boundary.  Re-wrap only resource gates so that the enclosing rewrite
     handler's ordinary HOL_ERR fallback cannot consume them.  All other
     recursive failures retain the existing fall-through semantics. *)
  fun recursive_rewrite_boundary _ recurse input =
    recurse input
    handle Feedback.HOL_ERR holerr =>
      if SmtResource.is_resource_gate holerr then
        raise BV_REWRITE_ERROR (Feedback.HOL_ERR holerr)
      else
        raise Feedback.HOL_ERR holerr

  fun z3_rewrite (state, t) =
  let
    val (l, r) = boolSyntax.dest_eq t
    val attempts = ref ([] : string list)
    val deferred_unification = ref (NONE : (thm * term list) option)
    fun record_attempt fragment =
      if List.exists (Lib.equal fragment) (!attempts) then ()
      else attempts := !attempts @ [fragment]
    fun rewrite_profile fragment name prove input =
      (record_attempt fragment; profile name prove input)
    fun skeleton_congruence () =
      let
        fun same_head (left, right) =
          let
            val (left_head, _) = boolSyntax.strip_comb left
            val (right_head, _) = boolSyntax.strip_comb right
          in
            Term.aconv left_head right_head orelse
              raise ERR "skeleton_congruence" "skeleton heads differ"
          end
        fun child (state, left_parent, right_parent) (left, right) =
          if Term.term_eq left right then
            (state, Thm.REFL left)
          else if Term.aconv left right then
            (state, Thm.ALPHA left right)
          else
            let
              val _ = Term.term_size left < Term.term_size left_parent andalso
                  Term.term_size right < Term.term_size right_parent orelse
                raise ERR "skeleton_congruence"
                  "recursive residue did not strictly shrink"
              val target = boolSyntax.mk_eq (left, right)
              val (state', theorem) = recursive_rewrite_boundary
                RecursiveSkeleton z3_rewrite (state, target)
              (* Contextual deferral is not recursive progress: lifting its
                 self-assumption would replace one whole obligation by a
                 harder residue.  Other checked definition hypotheses stay. *)
              val _ = List.exists (fn hypothesis =>
                  Term.aconv hypothesis target) (Thm.hyp theorem) andalso
                raise ERR "skeleton_congruence"
                  "recursive residue was deferred as its own assumption"
              val exact = Thm.EQ_MP
                (Thm.ALPHA (Thm.concl theorem) target) theorem
            in
              (state', exact)
            end
        fun unary dest (state, left, right) =
          let
            val _ = same_head (left, right)
            val (left_body, right_body) = (dest left, dest right)
            val (state', body_theorem) =
              child (state, left, right) (left_body, right_body)
          in
            (state', Thm.AP_TERM (Term.rator left) body_theorem)
          end
        fun binary dest (state, left, right) =
          let
            val _ = same_head (left, right)
            val (left_first, left_second) = dest left
            val (right_first, right_second) = dest right
            val (state', first_theorem) = child (state, left, right)
              (left_first, right_first)
            val (state'', second_theorem) = child (state', left, right)
              (left_second, right_second)
            val head = Term.rator (Term.rator left)
            val theorem = Thm.MK_COMB
              (Thm.MK_COMB (Thm.REFL head, first_theorem), second_theorem)
          in
            (state'', theorem)
          end
        fun quantified dest (state, left, right) =
          let
            val _ = same_head (left, right)
            val _ = dest left
            val _ = dest right
            val state_ref = ref state
            val abstraction_theorem = abs_congruence
              (fn (left_body, right_body) =>
                let
                  val (state', body_theorem) =
                    child (!state_ref, left, right)
                      (left_body, right_body)
                in
                  state_ref := state'; body_theorem
                end)
              (Term.rand left, Term.rand right)
          in
            (!state_ref,
             Thm.AP_TERM (Term.rator left) abstraction_theorem)
          end
        fun boolean_equality term =
          let val (left, right) = boolSyntax.dest_eq term in
            Term.type_of left = Type.bool andalso
            Term.type_of right = Type.bool
          end
          handle Feedback.HOL_ERR _ => false
        val result =
          if boolSyntax.is_neg l andalso boolSyntax.is_neg r then
            unary boolSyntax.dest_neg (state, l, r)
          else if boolSyntax.is_conj l andalso boolSyntax.is_conj r then
            binary boolSyntax.dest_conj (state, l, r)
          else if boolSyntax.is_disj l andalso boolSyntax.is_disj r then
            binary boolSyntax.dest_disj (state, l, r)
          else if boolSyntax.is_imp l andalso boolSyntax.is_imp r then
            binary boolSyntax.dest_imp (state, l, r)
          else if boolean_equality l andalso boolean_equality r then
            binary boolSyntax.dest_eq (state, l, r)
          else if boolSyntax.is_forall l andalso boolSyntax.is_forall r then
            quantified boolSyntax.dest_forall (state, l, r)
          else if boolSyntax.is_exists l andalso boolSyntax.is_exists r then
            quantified boolSyntax.dest_exists (state, l, r)
          else
            raise ERR "skeleton_congruence"
              "rewrite does not have a shared supported skeleton head"
        val (state', theorem) = result
        val exact = Thm.EQ_MP (Thm.ALPHA (Thm.concl theorem) t) theorem
      in
        (state_cache_thm state' exact, exact)
      end
  in
    (* E1(a): kernel reflexivity decides the reflexive-equality fragment. *)
    if l ~~ r then
      (state, Thm.REFL l)
    else
      (* E1(a): this decides Boolean AC-idempotent conjunction/disjunction. *)
      rewrite_profile "propositional-AC" "rewrite(1)(conj/disj)" (fn () =>
      if boolSyntax.is_conj l then
        (state, rewrite_conj (l, r))
      else if boolSyntax.is_disj l then
        (state, rewrite_disj (l, r))
      else
        raise ERR "" "") ()
    handle Feedback.HOL_ERR _ =>

    (* |- r1 /\ ... /\ rn = ~(s1 \/ ... \/ sn) *)
    (* E1(a): resolution decides the exact Z3 NNF shape implemented here:
       a conjunction of literals/equivalences equals the negation of a
       disjunction, including the two checked negated-equivalence variants. *)
    (state, rewrite_profile "propositional-NNF" "rewrite(2)(nnf)"
      rewrite_nnf (l, r))
    handle Feedback.HOL_ERR _ =>

    (* A Boolean tautology does not become an FP-specific obligation merely
       because an atom has FP type.  Decide the complete propositional
       fragment before entering the terminal FP ladder, while preserving the
       established cost order for non-FP rewrite families. *)

    (* Once an FP-shaped rewrite enters its dedicated ladder, failure at its
       unsupported rung is terminal.  In particular, generic unification
       must not turn an unsupported FP rewrite into a proof-local definition.
       FP_REWRITE_ERROR crosses the handlers below and is converted back to a
       structured HOL_ERR at the function boundary. *)
    if SmtFpProve.has_fp_theory_term t then
      ((state, rewrite_profile "propositional"
          "rewrite(fp-preflight)(TAUT_PROVE)" tautLib.TAUT_PROVE t)
        handle Feedback.HOL_ERR _ =>
       ((* E1(c): exact FP theorem reuse is a redundant performance cache. *)
        (state, rewrite_profile "cached-checked-theorems"
           "rewrite(3)(cache-fp)"
           (fn target =>
             Library.require_fastpath "Z3 rewrite FP theorem cache" target
               (state_exact_cached_thm state) target) t)
        handle Feedback.HOL_ERR _ =>
          let
            val eligible_decompositions =
              eligible_fp_bit_decompositions state
            val all_decompositions = fp_bit_decompositions state
            (* E1(b): checked lowering is the general selected FP rewrite
               procedure and fails loudly at its unsupported/D4 boundary. *)
            val thm = rewrite_profile "floating-point"
              "rewrite(4)(fp)"
              (SmtFpProve.fp_prove_with_context arith_prove
                eligible_decompositions all_decompositions) t
              handle Feedback.HOL_ERR holerr =>
                raise FP_REWRITE_ERROR (Feedback.HOL_ERR holerr)
            val definitions = Thm.hyp thm
            val state = state_define (state_cache_thm state thm) definitions
          in
            (state, thm)
          end))
    else
      (* FP has first refusal.  Z3's bag encoding then gets the count-array
         ladder before generic proformas; its [(_ map +)] terms parse to
         pointwise Int lambdas.  Native Seq follows with its bounded list
         ladder. *)
      (let
         (* E1(b): the general Bag prover fails loudly outside its family. *)
         val thm = rewrite_profile "bags" "rewrite(5)(bag)"
           (SmtBagProve.bag_prove_with_arith arith_prove) t
       in
         (state_cache_thm state thm, thm)
       end
       handle Feedback.HOL_ERR holerr =>
         if SmtResource.is_resource_gate holerr then
           raise BAG_REWRITE_ERROR (Feedback.HOL_ERR holerr)
         else
         (let
            (* E1(b): the general Seq prover has an explicit family gate. *)
            val thm = rewrite_profile "sequences" "rewrite(6)(seq)"
              SmtSeqProve.seq_prove t
          in
            (state_cache_thm state thm, thm)
          end
          handle Feedback.HOL_ERR holerr =>
            if SmtResource.is_resource_gate holerr then
              raise Feedback.HOL_ERR holerr
            else
              (* E1(a): canonicalization decides polynomial normal forms. *)
              (state, rewrite_profile "polynomial-normal-form"
                "rewrite(7)(poly-normal-form)"
                linear_arithmetic_rewrite_prove t)
              handle Feedback.HOL_ERR _ =>
              (* E1(a): simplification decides quantified Boolean normality. *)
              (state, rewrite_profile "quantified-propositional"
                "rewrite(8)(quantified-boolean)"
                quantified_boolean_rewrite_prove t)
              handle Feedback.HOL_ERR _ =>
              (* E1(c): rewrite proformas are redundant performance caches. *)
              (state, rewrite_profile "proforma-fastpaths"
                "rewrite(9)(proforma)"
                (fn target =>
                  Library.require_fastpath "Z3 rewrite proforma" target
                    Z3_ProformaThms.prove_rewrite target)
                t)
              handle Feedback.HOL_ERR _ =>
                let
                (* E1(b): the budgeted array/set procedure covers selected
                   beta, update, symbolic-index and extensional shapes and
                   fails loudly outside them or at its D4 boundary. *)
                val thm = rewrite_profile "arrays/set"
                  "rewrite(10)(array-set)"
                  SmtArrayProve.array_prove t
              in
                (state_cache_thm state thm, thm)
              end))

    handle Feedback.HOL_ERR holerr =>
    if SmtResource.is_resource_gate holerr then
      raise Feedback.HOL_ERR holerr
    else
      (* E1(c): theorem reuse is a redundant performance cache. *)
      (state, rewrite_profile "cached-checked-theorems"
        "rewrite(11)(cache)"
        (fn target =>
          Library.require_fastpath "Z3 rewrite theorem cache" target
            (state_inst_cached_thm state) target) t)

    handle Feedback.HOL_ERR _ =>

    (* Z3's String theory emits rewrite steps for literal normalization,
       ground `str.*` evaluation, and regex normalization. *)
    let
      (* E1(b): the general String/regex procedure has a loud boundary. *)
      val thm = rewrite_profile "strings/regex" "rewrite(12)(string)"
        SmtStringProve.string_rewrite_prove t
    in
      (state_cache_thm state thm, thm)
    end

    handle Feedback.HOL_ERR holerr =>
      if SmtResource.is_resource_gate holerr then
        raise STRING_REWRITE_ERROR (Feedback.HOL_ERR holerr)
      else

        (* |- ALL_DISTINCT ... /\ T = ... *)
        (* E1(a): recursive expansion decides literal-list distinctness. *)
        (state, rewrite_profile "datatype-literal-distinctness"
          "rewrite(13)(all_distinct)"
          rewrite_all_distinct (l, r))
    handle Feedback.HOL_ERR _ =>

    (* Resolve proof-local names before arithmetic.  These rewrites are not
       arithmetic tautologies until the fresh Z3 variable is recorded as a
       definition, and nonlinear fallback can otherwise spend a long time on
       the deliberately underconstrained formula. *)
    (* E1(a): one checked unifier decides proof-local definitions.  Safe
       definitions return immediately; bare aliases are saved for the end so
       semantic theory procedures retain their established priority. *)
    let
      val thm = rewrite_profile "proof-local-definitions"
        "rewrite(14)(unification)"
        (fn input => Library.gen_instantiation input
          handle Feedback.HOL_ERR _ => boolean_normalized_unification input)
        (l, r, #var_set state)
      val asl = Thm.hyp thm
      val _ = assert_rewrite_definitions state asl
      fun is_safe_early_definition tm =
        let val (name, residue) = boolSyntax.dest_eq tm
        in Term.type_of name = Type.bool orelse not (Term.is_var residue) end
      val safe = not (List.null asl) andalso
        List.all is_safe_early_definition asl
    in
      if safe then
        (state_define (state_cache_thm state thm) asl, thm)
      else
        (deferred_unification := SOME (thm, asl);
         raise ERR "z3_rewrite" "deferred proof-local variable alias")
    end

    handle Feedback.HOL_ERR _ =>

    (* Relate Z3's per-bit Boolean skolems to the packed BV skolem recorded
       by rewrite(4)(fp) or inferred by the exact-allocation fallback above.
       The resulting theorem retains only checked definitional hypotheses,
       which final replay eliminates as usual. *)
    (let
       val free_vars = HOLset.addList
         (Term.empty_tmset, Term.free_vars t)
       val packed_vars = fp_packed_vars state
       val _ = List.exists
           (fn var => HOLset.member (free_vars, var)) packed_vars orelse
         raise ERR "z3_rewrite" "no FP packed word in rewrite"
       val definitions = fp_per_bit_definitions state @
         HOLset.listItems (#definition_hyps state)
       (* E1(a): checked definitions reduce this fragment to BV blasting. *)
       val thm = rewrite_profile "floating-point/bit-vectors"
         "rewrite(15)(fp-packed-bits)"
         (SmtFpProve.definition_bitblast_prove definitions) t
       val state = state_define (state_cache_thm state thm) (Thm.hyp thm)
     in
       (state, thm)
     end
     handle Feedback.HOL_ERR holerr =>
       if SmtResource.is_resource_gate holerr then
         raise FP_REWRITE_ERROR (Feedback.HOL_ERR holerr)
       else
         raise Feedback.HOL_ERR holerr)

    handle Feedback.HOL_ERR _ =>

    let
      (* This semantic bridge is shared before and after arithmetic.  Word
         counterexamples are normalized to the ladder's ordinary failure, so
         they cannot bypass either occurrence or the later general rungs. *)
      fun smt_rdiv_prove () =
        (* E1(a): proved normalization decides side-condition-closed rdiv. *)
        rewrite_profile "linear-real-division" "rewrite(19)(smt-rdiv)"
          (simpLib.SIMP_PROVE (bossLib.srw_ss())
            [HolSmtTheory.smt_rdiv_eq_div]) t
      val thm =
        (bv_rewrite_prove (rewrite_profile "bit-vectors") state t
         handle Feedback.HOL_ERR holerr =>
           if SmtResource.is_resource_gate holerr then
             raise BV_REWRITE_ERROR (Feedback.HOL_ERR holerr)
           else

        (* Before arithmetic, use the semantic bridge whenever simp can
           discharge the non-zero divisor condition. *)
        smt_rdiv_prove ()
        handle Feedback.HOL_ERR _ =>

        (* E1(b): arithmetic combines complete linear and loud NLA routes. *)
        rewrite_profile "linear/nonlinear-arithmetic" "rewrite(20)(arith)"
          arith_prove t

        )
        handle Feedback.HOL_ERR _ =>

        smt_rdiv_prove ()
        handle Feedback.HOL_ERR _ =>

        (* E1(b): the TypeBase-driven simplification/cases/exhaustiveness/
           acyclicity procedure is general for selected registered datatype
           facts and fails loudly outside those shapes. *)
        rewrite_profile "datatypes" "rewrite(21)(datatype)"
          SmtDatatypeProve.datatype_prove t

    in
      (state_cache_thm state thm, thm)
    end

    handle Feedback.HOL_ERR _ =>

    (* Congruence one level below a Boolean equality.  Lambda definitions
       often appear as [(f = lhs) = (f = rhs)]; prove [lhs = rhs] through
       the ordinary rewrite ladder, then lift that checked theorem through
       the shared equality context with a kernel congruence step. *)
    (* E1(a): recursive kernel congruence decides shared Boolean equality. *)
    rewrite_profile "higher-order-congruence/beta/eta"
      "rewrite(22)(equality-congruence)" (fn () =>
      let
        val (ll, lr) = boolSyntax.dest_eq l
        val (rl, rr) = boolSyntax.dest_eq r
        (* [lift] rebuilds the equality around the proved argument; the
           partial applications of [=] come from [l] itself, so they are
           already instantiated at the argument type. *)
        val (sub_l, sub_r, lift) =
          if ll ~~ rl then
            (lr, rr, Thm.AP_TERM (Term.rator l))
          else if lr ~~ rr then
            (ll, rl, fn sub_thm =>
              Thm.AP_THM (Thm.AP_TERM (Term.rator (Term.rator l)) sub_thm) lr)
          else raise ERR "z3_rewrite" "no shared equality argument"
        val (state', sub_thm) = recursive_rewrite_boundary
          RecursiveEquality z3_rewrite
          (state, boolSyntax.mk_eq (sub_l, sub_r))
        val lifted = lift sub_thm
        val thm = Thm.EQ_MP (Thm.ALPHA (Thm.concl lifted) t) lifted
      in
        (state_cache_thm state' thm, thm)
      end) ()
    handle Feedback.HOL_ERR _ =>

    (* Congruence below a lambda; the shared `abs_congruence` handles the
       capture-avoiding binder alignment, while the body is replayed through
       `z3_rewrite` (threading the state via `state_ref`). *)
    (* E1(a): kernel abstraction congruence decides lambda bodies. *)
    rewrite_profile "higher-order-congruence/beta/eta"
      "rewrite(23)(abs-congruence)" (fn () =>
      let
        val state_ref = ref state
        val thm = abs_congruence (fn (lbody, rbody) =>
          let
            val (state', body_thm) = recursive_rewrite_boundary
              RecursiveAbstraction z3_rewrite
              (!state_ref, boolSyntax.mk_eq (lbody, rbody))
          in
            state_ref := state'; body_thm
          end) (l, r)
      in
        (!state_ref, thm)
      end) ()
    handle Feedback.HOL_ERR _ =>

    (* E1(a): kernel beta conversion decides beta equality. *)
    (state, rewrite_profile "higher-order-congruence/beta/eta"
      "rewrite(24)(beta)" beta_equal (l, r))
    handle Feedback.HOL_ERR _ =>

    (* E1(a): kernel eta conversion decides eta equality. *)
    (state, rewrite_profile "higher-order-congruence/beta/eta"
      "rewrite(25)(eta)" eta_equal (l, r))
    handle Feedback.HOL_ERR _ =>

    (* Recurse only below a shared Boolean/binder head, after every semantic
       theory rung has declined the complete rewrite.  [child] above proves
       unchanged positions reflexively and checks that each differing pair is
       strictly smaller before it re-enters [z3_rewrite]. *)
    rewrite_profile "boolean/binder-skeleton"
      "rewrite(25a)(skeleton-congruence)" skeleton_congruence ()
    handle Feedback.HOL_ERR _ =>

    (* Proof-local terms have already reached the general unifier before the
       theory-specific procedures above.  The examples below document why
       that semantic path exists.
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

    (case !deferred_unification of
       SOME (thm, asl) =>
         profile "rewrite(14)(unification:deferred-alias-return)"
           (fn () =>
             (state_define (state_cache_thm state thm) asl, thm)) ()
     | NONE => raise ERR "z3_rewrite" "no deferred proof-local definition")

    handle Feedback.HOL_ERR _ =>

    (* E1(b): a rewrite may be valid only under earlier asserted facts.
       Defer such an obligation as a hypothesis only when a proof context
       exists; final checked hypothesis removal must derive it from that
       context and fails loudly otherwise. *)
    if HOLset.isEmpty (#asserted_hyps state) then
      raise rewrite_ladder_exhausted (!attempts) t
    else
      (state, rewrite_profile "contextual-entailment"
        "rewrite(26)(contextual-entailment)" Thm.ASSUME t)
  end
  handle FP_REWRITE_ERROR error => raise error
       | BAG_REWRITE_ERROR error => raise error
       | STRING_REWRITE_ERROR error => raise error
       | BV_REWRITE_ERROR error => raise error

  fun z3_rewrite_entry (state, target) =
  let
    val orientation =
      profile "rewrite(entry)(canonical-orientation)"
        (Conv.QCHANGED_CONV SmtReplayCanon.z3_rewrite_canon_conv) target
      handle Conv.UNCHANGED => Thm.REFL target
    val canonical = boolSyntax.rhs (Thm.concl orientation)
    val (state, theorem) = z3_rewrite (state, canonical)
  in
    (state, Thm.EQ_MP (Thm.SYM orientation) theorem)
  end

  (* |- ~(!x. P x y) <=> ~(P (sk y) y)
     |- (?x. P x y) <=> P (sk y) y *)
  fun z3_skolem (state, t) =
  let
    val lhs = Lib.fst (boolSyntax.dest_eq t)
    fun skolem_theorem term =
      if boolSyntax.is_exists term then
        HolSmtTheory.SKOLEM_EXISTS
      else
        case Lib.total boolSyntax.dest_neg term of
          SOME body =>
            if boolSyntax.is_forall body then
              HolSmtTheory.SKOLEM_FORALL
            else
              raise ERR "z3_skolem" "expected a quantified formula"
        | NONE => raise ERR "z3_skolem" "expected a quantified formula"
    fun instantiate accumulated substs =
      let
        fun definition {redex, residue} =
          if HOLset.member (#var_set state, redex) then
            redex |-> Thm.SYM
              (Thm.ASSUME (boolSyntax.mk_eq (redex, residue)))
          else
            raise ERR "z3_skolem"
              "match produced a definition for a non-Z3 variable"
        val conversion = Drule.SUBST_CONV (List.map definition substs) t
          (Thm.concl accumulated)
      in
        Thm.EQ_MP conversion accumulated
      end
    (* Z3 may skolemize all or only a prefix of a binder block.  Peel at
       least one binder (this is the [sk] rule), then stop at the first
       prefix whose conclusion matches the recorded result. *)
    fun peel current accumulated =
      let
        val step = Conv.HO_REWR_CONV
          (Drule.SELECT_RULE (skolem_theorem current)) current
        val accumulated = Thm.TRANS accumulated step
      in
        case Lib.total (Term.match_term t) (Thm.concl accumulated) of
          SOME (substs, _) => instantiate accumulated substs
        | NONE => peel (boolSyntax.rhs (Thm.concl step)) accumulated
      end
    val thm = peel lhs (Thm.REFL lhs)
    val asl = Thm.hyp thm
  in
    (state_define state asl, thm)
  end

  fun z3_symm (state, thm, t) =
    (state, Thm.SYM thm)

  datatype th_lemma_cache_policy =
      D1PerformanceCache
    | SemanticProofLocalLookup

  fun skeleton_general_attempt state target =
    SmtSkeletonDispatch.attempt (#skeleton_context state) target

  fun skeleton_general_success result =
    profile "th_lemma[general](success)"
      (fn () => #theorem result) ()

  fun th_lemma_wrapper cache_policy (name : string)
    (th_lemma_implementation : state * Term.term -> state * Thm.thm)
    (state, thms, t) : state * Thm.thm =
  let
    val t' = boolSyntax.list_mk_imp (List.map Thm.concl thms, t)
    val has_proforma = name = "arith" orelse name = "array"
    val cache_rung = if has_proforma then "2" else "1"
    fun cached target =
      case cache_policy of
        D1PerformanceCache =>
          (* E1(c): fallback re-proves this redundant cache's family. *)
          Library.require_fastpath "Z3 th-lemma theorem cache" target
            (state_inst_cached_thm state) target
      | SemanticProofLocalLookup =>
          (* E1(a): finite checked-state lookup and instantiation is complete. *)
          state_inst_cached_thm state target
    fun checked_general target =
      case skeleton_general_attempt state target of
        SmtSkeletonDispatch.Proved result =>
          (state, skeleton_general_success result)
      | SmtSkeletonDispatch.Declined =>
          th_lemma_implementation (state, target)
    fun general () =
      ((state,
        profile ("th_lemma[" ^ name ^ "](" ^ cache_rung ^ ")(cache)")
          cached t')
      handle Feedback.HOL_ERR _ =>
        (* do actual work to derive the theorem *)
        checked_general t')
    val (state, thm) =
      if has_proforma then
        ((state,
          (* E1(c): th-lemma proformas are redundant performance caches. *)
          profile ("th_lemma[" ^ name ^ "](1)(proforma)")
            (fn target =>
              Library.require_fastpath "Z3 th-lemma proforma" target
                (Z3_ProformaThms.prove
                  Z3_ProformaThms.th_lemma_thms) target)
            t')
         handle Feedback.HOL_ERR _ => general ())
      else general ()
  in
    (state, Drule.LIST_MP thms thm)
  end

  (* Bags have no Z3 proof-theory tag: their encoded count arrays arrive at
     the arith or array registry entries below.  Retain a dedicated wrapper
     nevertheless so the bag route has the same cache/proforma discipline and
     profile identity as every other checked theory re-prover. *)
  val z3_th_lemma_bag =
    th_lemma_wrapper D1PerformanceCache "bag" (fn (state, t) =>
    let
      (* E1(b): the general Bag prover fails loudly outside its family. *)
      val thm = profile "th_lemma[bag](2)(bag_prove)"
        (SmtBagProve.bag_prove_with_arith arith_prove) t
    in
      (state_cache_thm state thm, thm)
    end)

  val bv_th_lemma_prove_raw =
  let
    (* Keep SIMP_TAC for conditional rewrites.  A 2026-07-08 Poly/ML 5.9.2
       retry with PURE_REWRITE_TAC did not reproduce the old segfault in the
       unit phase, but the full selftest run did not finish promptly after
       entering functional tests. *)
    val COND_REWRITE_TAC = simpLib.SIMP_TAC
      simpLib.empty_ss [boolTheory.COND_RAND, boolTheory.COND_RATOR]
    val PROFILED_BBLAST_CONV =
      blastLib.BBLAST_CONV_WITH_PROFILES
        (profile "th_lemma[bv](3)(COND_BBLAST:WORD_SIMP_CONV)")
        (profile "th_lemma[bv](3)(COND_BBLAST:BIT_TAUT_CONV)")
  in
    fn t =>
      (* E1(a): conditional normalization plus BBLAST decides BV.  Profile
         the actual simplification and propositional phases inside the
         complete converter; no speculative word-equality shortcut
         precedes this route. *)
      profile "th_lemma[bv](3)(COND_BBLAST)" Tactical.prove (t,
        Tactical.THEN
          (COND_REWRITE_TAC, Tactic.CONV_TAC PROFILED_BBLAST_CONV))
  end

  fun bv_th_lemma_prove target =
    bv_resource_prove "bv-th-lemma" bv_th_lemma_prove_raw target

  fun bv_th_lemma_basic_branch prove decline fallback target =
    if has_word_atom target then
      bv_next_rung prove fallback target
    else
      decline target

  fun arith_bv_fallback t fallback holerr =
    if SmtResource.is_resource_gate holerr then
      raise Feedback.HOL_ERR holerr
    else if has_word_atom t then
      fallback t
    else
      raise Feedback.HOL_ERR holerr

  (* The single production entry for TASK_19's propositionally-valid modulo
     atom-expansion class.  Admission is a code-level precondition in the
     dispatcher; a normal decline/failure lets the owning legacy theory rung
     run, while resource rejection always terminates the ladder. *)
  val z3_th_lemma_arith_generic =
    th_lemma_wrapper D1PerformanceCache "arith" (fn (state, t) =>
    let
      (* E1(b): arithmetic combines complete linear and loud NLA routes. *)
      val thm = profile "th_lemma[arith](3)" arith_prove t
        handle Feedback.HOL_ERR holerr =>
          (* E1(a): ordinary legacy arith-tagged BV failures end in complete
             BBLAST. Resource refusals must terminate this ladder. *)
          arith_bv_fallback t
            (profile "th_lemma[arith](4)(bv)" bv_th_lemma_prove) holerr
    in
      (* cache 'thm' *)
      (state_cache_thm state thm, thm)
    end)

  val z3_th_lemma_array_generic =
    th_lemma_wrapper D1PerformanceCache "array" (fn (state, t) =>
    (let
       (* E1(b): the budgeted array procedure covers selected beta, update,
          symbolic-index and extensional shapes and fails loudly outside
          them or at its D4 boundary. *)
       val thm = profile "th_lemma[array](3)(array_prove)"
         SmtArrayProve.array_prove t
     in
       (* cache 'thm' *)
       (state_cache_thm state thm, thm)
     end
     handle Feedback.HOL_ERR holerr =>
      if SmtResource.is_resource_gate holerr then
        raise Feedback.HOL_ERR holerr
      else
        raise ERR "z3_th_lemma_array"
          ("unsupported th-lemma shape: theory=array; checked replay is only " ^
           "implemented for function-update select/store/extensionality " ^
           "lemmas; conclusion=" ^ Library.term_to_string t)))

  fun th_lemma_target (_, thms, t) =
    boolSyntax.list_mk_imp (List.map Thm.concl thms, t)

  fun z3_th_lemma_arith args =
    if SmtBagProve.has_native_bag_encoding (th_lemma_target args) then
      z3_th_lemma_bag args
    else
      z3_th_lemma_arith_generic args

  fun z3_th_lemma_array args =
    if SmtBagProve.has_native_bag_encoding (th_lemma_target args) then
      z3_th_lemma_bag args
    else
      z3_th_lemma_array_generic args

  val z3_th_lemma_basic =
    th_lemma_wrapper D1PerformanceCache "basic" (fn (state, t) =>
    let
      fun unsupported attempts =
        raise ERR "z3_th_lemma_basic"
          ("unsupported th-lemma shape: theory=basic; " ^
           "attempted fragment classes=[" ^
           String.concatWith ", " (List.rev attempts) ^
           "]; checked replay is implemented for Boolean, arithmetic, " ^
           "bit-vector and array equality simplification lemmas; " ^
           "conclusion=" ^ Library.term_to_string t)

      fun metis attempts =
        (* E1(b): METIS is general proof search with a loud boundary. *)
        profile "th_lemma[basic](6)(METIS)" metis_prove ([], t)
        handle Feedback.HOL_ERR _ => unsupported
          ("first-order-proof-search" :: attempts)

      fun array attempts =
        if has_array_atom t then
          ((* E1(b): the budgeted selected array/set procedure has a loud
               unsupported/resource boundary. *)
           profile "th_lemma[basic](5)(array)" SmtArrayProve.array_prove t
           handle Feedback.HOL_ERR holerr =>
             if SmtResource.is_resource_gate holerr then
               raise Feedback.HOL_ERR holerr
             else metis ("array" :: attempts))
        else metis attempts

      fun bv attempts =
        bv_th_lemma_basic_branch
          (* E1(a): the terminal BBLAST route decides bit-vectors. *)
          (profile "th_lemma[basic](4)(bv)" bv_th_lemma_prove)
          (fn _ => array attempts)
          (fn _ => array ("bv" :: attempts)) t

      fun arith attempts =
        if has_arith_atom t then
          ((* E1(b): arithmetic has complete linear and loud NLA routes. *)
           profile "th_lemma[basic](3)(arith)" arith_prove t
           handle Feedback.HOL_ERR _ => bv ("arith" :: attempts))
        else bv attempts

      (* E1(a): TAUT_PROVE decides the propositional fragment. *)
      val thm = profile "th_lemma[basic](2)(TAUT_PROVE)"
        tautLib.TAUT_PROVE t
        handle Feedback.HOL_ERR _ => arith ["boolean"]
    in
      (* cache 'thm' *)
      (state_cache_thm state thm, thm)
    end)

  val z3_th_lemma_bv =
    th_lemma_wrapper D1PerformanceCache "bv" (fn (state, t) =>
      let
        val thm = bv_th_lemma_prove t
      in
        (* cache 'thm' *)
        (state_cache_thm state thm, thm)
      end)

  val z3_th_lemma_datatype =
    th_lemma_wrapper D1PerformanceCache "datatype" (fn (state, t) =>
      let
        (* E1(b): TypeBase-driven reconstruction is general for selected
           registered datatype facts and fails loudly outside those shapes. *)
        val thm = profile "th_lemma[datatype](2)"
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
    th_lemma_wrapper SemanticProofLocalLookup
      ("advanced:" ^ #theory metadata) (fn (state, t) =>
      (* E1(b): an uncached advanced family reaches this loud boundary. *)
      profile ("th_lemma[advanced:" ^ #theory metadata ^
        "](2)(unsupported)")
        (fn target =>
          raise ERR "z3_th_lemma_advanced_unsupported"
            (unsupported_advanced_th_lemma_message state metadata target)) t)

  (* Defensive only: no th-lemma-fp occurrence was observed in any of the
     TASK_02 proofs from supported Z3 4.11.2--4.15.3.  Keep the route checked
     nonetheless, with the FP shape gate ahead of every prover rung. *)
  fun z3_th_lemma_fp _ (state, thms, t) =
  let
    val t' = boolSyntax.list_mk_imp (List.map Thm.concl thms, t)
    val () =
      if SmtFpProve.has_fp_theory_term t' then ()
      else SmtFpProve.unsupported t'
    val (general, thm) =
      case skeleton_general_attempt state t' of
        SmtSkeletonDispatch.Proved result =>
          (true, skeleton_general_success result)
      | SmtSkeletonDispatch.Declined =>
          (* E1(b): checked lowering is the general selected FP th-lemma
             procedure and fails loudly at its unsupported/D4 boundary. *)
          (false, profile "th_lemma[fp](1)"
            (SmtFpProve.fp_prove_with_decompositions_and_arith
              arith_prove []) t')
  in
    (if general then state else state_cache_thm state thm,
     Drule.LIST_MP thms thm)
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
    (* Run the bounded DAG-aware family scan before the common attempt.  Once
       the String/character metadata guard has admitted the node, every
       target is offered: owned bridge atoms may be reduced while symbolic
       String leaves remain as propositional residuals. *)
    val _ = SmtStringProve.has_string_theory_term t'
    fun legacy () =
      ((* E1(b): the general String/regex procedure gates its family. *)
       profile ("th_lemma[" ^ dispatch_theory ^ "](1)(theory)")
         prover t')
      handle Feedback.HOL_ERR holerr =>
        if SmtResource.is_resource_gate holerr then
          raise Feedback.HOL_ERR holerr
        else
          ((* E1(b): contextual String/regex replay fails loudly at exit. *)
           profile ("th_lemma[" ^ dispatch_theory ^ "](2)(contextual)")
            (SmtStringProve.string_contextual_prove context) t'
            handle Feedback.HOL_ERR contextual_error =>
            if SmtResource.is_resource_gate contextual_error then
              raise Feedback.HOL_ERR contextual_error
            else
              raise ERR ("z3_th_lemma_" ^ dispatch_theory)
                (unsupported_string_th_lemma_message dispatch_theory
                  state metadata t'))
    val (general, thm) =
      case skeleton_general_attempt state t' of
        SmtSkeletonDispatch.Proved result =>
          (true, skeleton_general_success result)
      | SmtSkeletonDispatch.Declined => (false, legacy ())
  in
    (if general then state else state_cache_thm state thm,
     Drule.LIST_MP thms thm)
  end

  val z3_th_lemma_native_seq =
    th_lemma_wrapper D1PerformanceCache "seq" (fn (state, t) =>
    let
      val thm =
        (* E1(b): the general Seq procedure gates its supported family. *)
        profile "th_lemma[seq](2)(seq_prove)" SmtSeqProve.seq_prove t
        handle Feedback.HOL_ERR holerr =>
          if SmtResource.is_resource_gate holerr then
            raise Feedback.HOL_ERR holerr
          else
            (* E1(b): contextual Seq replay fails loudly at its boundary. *)
            profile "th_lemma[seq](3)(contextual)"
            (SmtSeqProve.seq_contextual_prove
              (HOLset.listItems (#asserted_hyps state))) t
    in
      (state_cache_thm state thm, thm)
    end)

  (* Z3's `seq` tag covers both Phase-4 Strings and polymorphic sequences.
     The latter are native HOL lists, while String remains on its dedicated
     carrier.  Keep the existing string wrapper intact for the former and
     select the native re-prover before any string-specific fallback. *)
  fun z3_th_lemma_seq metadata (args as (state, thms, t)) =
    let
      val target = boolSyntax.list_mk_imp (List.map Thm.concl thms, t)
    in
      if SmtSeqProve.has_seq_type target then
        z3_th_lemma_native_seq args
      else
        string_th_lemma_wrapper "seq" SmtStringProve.check_seq_type metadata
          (SmtStringProve.string_prove arith_prove) args
    end

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
      "translation_definitions=" ^ Int.toString
        (List.length (#translation_definitions state)),
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
    | proofterm_concl (APPLY_DEF (_, concl)) = SOME concl
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
           | HolSatLib.SAT_cex cex =>
        raise ERR name
          ("Z3 proof replay decision procedure found a counterexample\n" ^
           "proof rule: " ^ name ^ "\n" ^
           "parsed HOL conclusion: " ^ term_diag concl ^ "\n" ^
           "replay state: " ^ state_summary state ^ "\n" ^
           "counterexample theorem: " ^ thm_diag cex)
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

  and quant_intro_prem (state_proof : state * proof)
      (name : string)
      (z3_rule_fn : state * Term.term list * Thm.thm * Term.term ->
        state * Thm.thm)
      (pt : proofterm, concl : Term.term)
      (continuation : (state * proof) * Thm.thm -> (state * proof) * Thm.thm)
      : (state * proof) * Thm.thm =
    let
      val (vars, body) =
        case pt of
          PROOF_BIND ([], _) =>
            quant_intro_annotation_mismatch "annotation is empty"
        | PROOF_BIND pair => pair
        | _ => quant_intro_annotation_mismatch
            "premise is not an immediate proof-bind annotation"
    in
      thm_of_proofterm (state_proof, body) (continuation o
        (fn ((state, proof), thm) =>
          let
            val (state, thm) = profile name z3_rule_fn
              (state, vars, thm, concl)
              handle Feedback.HOL_ERR holerr =>
                raise_replay_error name state name [pt] concl [thm] holerr
            val _ = profile "check_thm" check_thm (name, thm, concl)
              handle Feedback.HOL_ERR holerr =>
                raise_replay_error "check_thm" state name [pt] concl
                  [thm] holerr
          in
            ((state, proof), thm)
          end))
    end

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
    | thm_of_proofterm (state_proof, QUANT_INTRO x) continuation =
        quant_intro_prem state_proof "quant_intro" z3_quant_intro x
          continuation
    | thm_of_proofterm (state_proof, REFL x) continuation =
        zero_prems state_proof "refl" z3_refl x continuation
    | thm_of_proofterm (state_proof, REWRITE x) continuation =
        zero_prems state_proof "rewrite" z3_rewrite_entry x continuation
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
        list_prems state_proof (th_lemma_rule_name metadata)
          z3_th_lemma_array (pts, concl) continuation []
    | thm_of_proofterm (state_proof, TH_LEMMA_BASIC (metadata, pts, concl))
        continuation =
        list_prems state_proof (th_lemma_rule_name metadata)
          z3_th_lemma_basic (pts, concl) continuation []
    | thm_of_proofterm (state_proof, TH_LEMMA_BV (metadata, pts, concl))
        continuation =
        list_prems state_proof (th_lemma_rule_name metadata)
          z3_th_lemma_bv (pts, concl) continuation []
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
  let
    (* Replay state remembers definitions established by earlier steps even
       when the final theorem no longer depends on them.  Definition
       elimination concerns theorem hypotheses, not the historical state. *)
    val defs = HOLset.intersection (defs, Thm.hypset thm)
  in
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
        fun discharge_ground_def (def, thm) =
          case prove_ground_def def of
            SOME def_thm => Drule.PROVE_HYP def_thm thm
          | NONE => thm
        val thm = HOLset.foldl discharge_ground_def
          thm (HOLset.addList (Term.empty_tmset, ground_defs))
        (* Substituting fpa2bv's per-bit definitions can turn its packed-word
           definition into the cyclic-looking but valid identity
           [w = v2w (GENLIST (flip word_bit w) ...)].  Discharge such checked
           word identities before searching the remaining definition DAG. *)
        fun prove_word_identity def =
          let val (lhs, _) = boolSyntax.dest_eq def in
            if wordsSyntax.is_word_type (Term.type_of lhs) then
              SOME (blastLib.BBLAST_PROVE def)
            else NONE
          end
          handle Feedback.HOL_ERR _ => NONE
               | HolSatLib.SAT_cex _ => NONE
        fun discharge_word_identity (def, (remaining, thm)) =
          case prove_word_identity def of
            SOME def_thm => (remaining, Drule.PROVE_HYP def_thm thm)
          | NONE => (def :: remaining, thm)
        val (defs, thm) = List.foldl discharge_word_identity ([], thm) defs
        val defs = HOLset.addList (Term.empty_tmset, defs)
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

        (* A packed fpa2bv word may participate in the benign cycle
           [k = pack x], [k = v2w bs], [b_i = bit i k].  If no ordinary DAG
           leaf exists, select the multiply-defined packed word; the checked
           word-list fallback below breaks the cycle into Boolean definitions. *)
        fun multiply_defined var =
          List.length (List.filter
            (fn (lhs, _) => Term.aconv lhs var) dest_defs) > 1
        val duplicate_set = HOLset.filter multiply_defined def_set
        val elimination_set =
          if HOLset.isEmpty unref_set then duplicate_set else unref_set
        val () =
          if HOLset.isEmpty elimination_set then
            raise ERR "remove_definitions"
              ("no unreferenced variables; definitions=" ^
               String.concatWith "; "
                 (List.map Library.term_to_string
                   (HOLset.listItems defs)))
          else
            ()

        (* Pick an arbitrary eliminable variable. *)
        val var = Option.valOf
          (HOLset.find (fn _ => true) elimination_set)

        (* Get all the variable's definitions *)
        fun filter_def (v, d) = if Term.term_eq v var then SOME d else NONE
        val defs_to_remove = List.mapPartial filter_def dest_defs

        (* Pick an arbitrary definition for instantiation *)
        val inst = List.hd defs_to_remove

        (* Instantiate the variable with the definition *)
        val thm = Thm.INST [var |-> inst] thm

        (* fpa2bv can define one packed word both semantically and as [mkbv]
           over fresh Boolean skolems.  Ordinary syntactic unification cannot
           solve that word equation; BBLAST can, under the canonical per-bit
           definitions that checked definition elimination will remove next. *)
        fun word_list_instantiation (left, right) =
          let
            fun dest_bits tm =
              let
                val (list_tm, index_ty) = bitstringSyntax.dest_v2w tm
                val (bits, _) = listSyntax.dest_list list_tm
                val _ = List.all
                  (fn bit => Term.is_var bit andalso
                    HOLset.member (var_set, bit)) bits orelse raise Match
              in
                (bits, index_ty)
              end
            val (word, bits, index_ty) =
              case Lib.total dest_bits right of
                SOME (bits, index_ty) => (left, bits, index_ty)
              | NONE =>
                  let val (bits, index_ty) = dest_bits left
                  in (right, bits, index_ty) end
            val width = List.length bits
            val word_var = Term.mk_var
              ("packed_definition_word", Term.type_of word)
            fun bit_definition (index, bit) =
              boolSyntax.mk_eq (bit, wordsSyntax.mk_word_bit
                (numSyntax.term_of_int (width - index - 1), word_var))
            val definitions = List.map bit_definition
              (ListPair.zip (List.tabulate (width, Lib.I), bits))
            val vector = bitstringSyntax.mk_v2w
              (listSyntax.mk_list (bits, Type.bool), index_ty)
            val conclusion = boolSyntax.mk_eq (word_var, vector)
            val theorem = Tactical.TAC_PROOF ((definitions, conclusion),
              Tactical.THEN
                (bossLib.ASM_SIMP_TAC (bossLib.srw_ss()) [],
                 blastLib.BBLAST_TAC))
            val theorem = Thm.INST [word_var |-> word] theorem
          in
            if Term.aconv (Thm.concl theorem)
                (boolSyntax.mk_eq (left, right)) then theorem
            else Thm.SYM theorem
          end
        val hyp_thms = List.map
          (fn def =>
            Library.gen_instantiation (inst, def, var_set)
            handle _ => word_list_instantiation (inst, def))
          defs_to_remove

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
          (let
             val i = realSyntax.dest_injected y
             val _ =
               if intSyntax.is_int_literal i then () else raise ERR "" ""
             val y_ne_zero =
               Tactical.TAC_PROOF
                 (([], boolSyntax.mk_neg
                   (boolSyntax.mk_eq (y, realSyntax.zero_tm))),
                  bossLib.FULL_SIMP_TAC (bossLib.srw_ss()) [realTheory.REAL_INJ])
           in
             if Term.same_const f smt_rdiv_const then
               SOME (Thm.MP (Drule.SPECL [x, y] HolSmtTheory.smt_rdiv_eq_div)
                            y_ne_zero)
             else NONE
           end handle _ => NONE)
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
    (* Z3 preprocesses with `solve-eqs`, so a `rewrite` step can hold only
       under the asserted equalities; replay defers such a step as a
       hypothesis.  Discharging it needs congruence from an assumption
       rather than a further rewrite set, which is what no normalization
       rung above can reach. *)
    fun entailment_tac goal =
      Timeout.apply SmtResource.max_hypothesis_entailment_time
        (Feedback.trace ("metis", 0) (bossLib.METIS_TAC [])) goal
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
    val beta_eta_conv = SmtReplayCanon.compose
      [Conv.TOP_DEPTH_CONV Thm.BETA_CONV,
       Conv.TOP_DEPTH_CONV Drule.ETA_CONV]
    (* 'asl' is fixed across the fold below, so normalize it at most once
       rather than once per removed hypothesis.  Most checked proofs have no
       extra hypothesis at all, so the work stays deferred until needed. *)
    val normalized_asl = ref NONE
    fun canonical_assumptions () =
      case !normalized_asl of
        SOME pairs => pairs
      | NONE =>
          let
            val pairs =
              List.map (fn a => (a, beta_eta_conv a)) asl
          in
            normalized_asl := SOME pairs; pairs
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
      val hyp_normalization = beta_eta_conv hyp
      val normalized_hyp = boolSyntax.rhs (Thm.concl hyp_normalization)
      fun canonical_assumption [] = NONE
        | canonical_assumption ((assumption, normalization) :: rest) =
            if Term.aconv (boolSyntax.rhs (Thm.concl normalization))
                 normalized_hyp then
              SOME (Thm.EQ_MP (Thm.SYM hyp_normalization)
                (Thm.EQ_MP normalization (Thm.ASSUME assumption)))
            else canonical_assumption rest
      (* Z3 can leave a proved String normalization as an extra hypothesis
         during solve-eqs finalization.  Discharge it through the same
         general, proof-producing String rewrite procedure used by rewrite
         replay.  Its resource refusal remains terminal; ordinary family
         mismatch falls through to the other semantic procedures. *)
      fun prove_string_hypothesis target =
        SmtStringProve.string_rewrite_prove target
        handle Feedback.HOL_ERR holerr =>
          if SmtResource.is_resource_gate holerr then
            raise Feedback.HOL_ERR holerr
          else
            let
              val (left, right) = boolSyntax.dest_eq target
              val reverse = boolSyntax.mk_eq (right, left)
            in
              Thm.SYM (SmtStringProve.string_rewrite_prove reverse)
            end
      fun string_hypothesis () =
        SOME (profile "check_proof(hyp_removal:string)"
          prove_string_hypothesis hyp)
        handle Feedback.HOL_ERR holerr =>
          if SmtResource.is_resource_gate holerr then
            raise Feedback.HOL_ERR holerr
          else NONE
      (* fpa2bv can leave a proved word normalization as an extra hypothesis
         after solve-eqs.  Discharge it with the checked, resource-gated word
         decision procedure used by ordinary replay. *)
      fun prove_word_hypothesis target =
        let
          val _ = Lib.can (HolKernel.find_term
            (wordsSyntax.is_word_type o Term.type_of)) target orelse
            raise ERR "prove_word_hypothesis" "no word subterm"
        in
          SmtResource.with_bitblast_step_time "hyp-removal-word"
            (fn term =>
              (SmtResource.check_bitblast_goal "hyp-removal-word" term;
               bv_th_lemma_prove term)) target
        end
      fun word_hypothesis () =
        SOME (profile "check_proof(hyp_removal:word)"
          prove_word_hypothesis hyp)
        handle Feedback.HOL_ERR holerr =>
          if SmtResource.is_resource_gate holerr then
            raise Feedback.HOL_ERR holerr
          else NONE
      val hyp_thm =
        case canonical_assumption (canonical_assumptions ()) of
          SOME th => th
        | NONE => (case string_hypothesis () of
          SOME th => th
        | NONE => (case word_hypothesis () of
          SOME th => th
        | NONE => (case first_success
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
                datatype_normalize_tac datatype_thms),
             ("check_proof(hyp_removal:entailment)", entailment_tac)] of
            SOME th => th
          | NONE => raise ERR "remove_hyps"
              ("extra hypothesis is not entailed by the goal's assumptions; " ^
               "hypothesis=" ^ Library.term_to_string hyp ^
               "; attempted=[String normalization, word decision, " ^
               "numeral division, semantic division, total division, " ^
               "arithmetic normalization, datatype normalization, " ^
               "context entailment]"))))
    in
      Drule.PROVE_HYP hyp_thm thm
    end
  in
    HOLset.foldl remove_hyp thm bad_hyps
  end

  (* A reflexive equality is independently derivable by the kernel, whatever
     spelling Z3 chose for its sides. *)
  fun is_reflexive_equality hyp =
    case Lib.total boolSyntax.dest_eq hyp of
      SOME (lhs, rhs) => Term.aconv lhs rhs
    | NONE => false

  fun remove_extra_hyps (asserted, thm) =
  let
    val extra_hyps = HOLset.difference (Thm.hypset thm, asserted)
    fun remove_hyp (hyp, thm) =
      if is_reflexive_equality hyp then
        Drule.PROVE_HYP (Thm.REFL (Lib.fst (boolSyntax.dest_eq hyp))) thm
      else
        thm
  in
    HOLset.foldl remove_hyp thm extra_hyps
  end
in
  (* For unit tests *)
  val asserted_membership_diagnostic = asserted_membership_diagnostic
  val remove_definitions = remove_definitions
  val remove_extra_hyps = remove_extra_hyps
  val remove_hyps_for_test = remove_hyps
  val quantified_boolean_rewrite_prove_for_test =
    quantified_boolean_rewrite_prove
  val beta_equal_for_test = beta_equal
  val eta_equal_for_test = eta_equal
  val monotonicity_prove_for_test = monotonicity_prove
  val arith_prove_for_test = arith_prove
  val arith_prove_ediv_emod_for_test = arith_prove_ediv_emod
  val ground_subterm_eval_conv_for_test =
    profiled_ground_subterm_eval_conv
  val ground_subterm_eval_max_nodes_for_test =
    ground_subterm_eval_max_nodes
  val ground_subterm_eval_max_calls_for_test =
    ground_subterm_eval_max_calls
  val word_decide_for_test = word_decide
  fun bv_family_measure_for_test target =
    term_contains_type_measure wordsSyntax.is_word_type target
  fun bv_rewrite_prove_for_test target =
    bv_rewrite_prove_with_context profile has_word_atom (fn _ => false)
      [] target
  fun bv_rewrite_prove_with_definitions_for_test definitions target =
    bv_rewrite_prove_with_context profile has_word_atom (fn _ => false)
      definitions target
  fun bv_rewrite_lowered_for_test version packed registered target =
    bv_rewrite_prove_with_context profile (fn _ => false)
      (has_allocated_fp_bv_atom_in version packed registered) [] target
  fun bv_rewrite_inferred_lowered_for_test version registered assertions
      target =
    let val packed = fp_inferred_packed_vars_with_provenance
      version registered assertions
    in
      bv_rewrite_lowered_for_test version packed registered target
    end
  fun bv_rewrite17_with_workers_for_test normalize decide definitions target =
    rewrite17 normalize decide definitions target
  val bv_next_rung_for_test = bv_next_rung
  val bv_th_lemma_prove_for_test = bv_th_lemma_prove
  val bv_th_lemma_basic_branch_for_test = bv_th_lemma_basic_branch
  val arith_bv_fallback_for_test = arith_bv_fallback

  fun skeleton_general_sequence_for_test targets =
    let
      val context = SmtSkeletonDispatch.new_context arith_prove
    in
      {procedure_names = SmtSkeletonDispatch.procedure_names context,
       results = List.map (SmtSkeletonDispatch.prove context) targets,
       cache_size = SmtSkeletonProve.cache_size context}
    end

  fun skeleton_general_admits_for_test target =
    case SmtSkeletonDispatch.attempt
        (SmtSkeletonDispatch.new_context arith_prove) target of
      SmtSkeletonDispatch.Proved _ => true
    | SmtSkeletonDispatch.Declined => false

  fun skeleton_general_word_branch_for_test word_expand fallback target =
    let
      fun unable _ = SmtSkeletonProve.Unable
      val context = SmtSkeletonProve.new_context
        [{name = "char-word", expand = unable},
         {name = "word", expand = word_expand},
         {name = "ground-regex", expand = unable},
         {name = "arithmetic", expand = unable}]
    in
      case SmtSkeletonDispatch.attempt context target of
        SmtSkeletonDispatch.Proved result => #theorem result
      | SmtSkeletonDispatch.Declined => fallback target
    end

  fun skeleton_general_arithmetic_branch_for_test arith_prove fallback
      target =
    let
      val context = SmtSkeletonDispatch.new_context arith_prove
    in
      case SmtSkeletonDispatch.attempt context target of
        SmtSkeletonDispatch.Proved result => #theorem result
      | SmtSkeletonDispatch.Declined => fallback target
    end

  fun skeleton_general_branch_for_test fallback target =
    case SmtSkeletonDispatch.attempt
        (SmtSkeletonDispatch.new_context arith_prove) target of
      SmtSkeletonDispatch.Proved result => #theorem result
    | SmtSkeletonDispatch.Declined => fallback target

  fun skeleton_duplicate_registry_for_test target =
    let
      fun unable _ = SmtSkeletonProve.Unable
      val context = SmtSkeletonProve.new_context
        [{name = "word", expand = unable},
         {name = "word", expand = unable}]
    in
      SmtSkeletonDispatch.attempt context target
    end

  fun recursive_rewrite_outer_for_test site recurse fallback input =
    ((recursive_rewrite_boundary site recurse input
      handle Feedback.HOL_ERR _ => fallback input)
     handle BV_REWRITE_ERROR error => raise error)

  fun skeleton_recursive_rewrite_for_test recurse fallback input =
    recursive_rewrite_outer_for_test
      RecursiveSkeleton recurse fallback input

  fun equality_recursive_rewrite_for_test recurse fallback input =
    recursive_rewrite_outer_for_test
      RecursiveEquality recurse fallback input

  fun abstraction_recursive_rewrite_for_test recurse fallback input =
    recursive_rewrite_outer_for_test
      RecursiveAbstraction recurse fallback input

  fun initial_replay_state allowed_asserted_hyps definitions proof : state = {
    allowed_asserted_hyps = allowed_asserted_hyps,
    asserted_hyps = Term.empty_tmset,
    definition_hyps = Term.empty_tmset,
    thm_cache = Net.empty,
    var_set = proof_vars proof,
    bit_decompositions = proof_bit_decompositions proof,
    translation_definitions = definitions,
    skeleton_context = SmtSkeletonDispatch.new_context arith_prove,
    z3_version = proof_version proof
  }

  (* Unit replay helpers do not have an original goal.  Derive their allowed
     set from the complete synthetic proof value so they continue to exercise
     individual rules.  Production replay never uses this helper: it supplies
     the original goal's assertions explicitly below. *)
  fun proof_asserted_hyps proof =
  let
    fun add_list pts set = List.foldl (fn (pt, set) => add pt set) set pts
    and add pt set =
      case pt of
        AND_ELIM (p, _) => add p set
      | APPLY_DEF (p, _) => add p set
      | ASSERTED t => HOLset.add (set, t)
      | COMMUTATIVITY _ => set
      | DEF_AXIOM _ => set
      | ELIM_UNUSED _ => set
      | HYPOTHESIS _ => set
      | IFF_FALSE (p, _) => add p set
      | IFF_TRUE (p, _) => add p set
      | INTRO_DEF _ => set
      | LEMMA (p, _) => add p set
      | MONOTONICITY (ps, _) => add_list ps set
      | MP (p, q, _) => add q (add p set)
      | MP_EQ (p, q, _) => add q (add p set)
      | NNF_NEG (ps, _) => add_list ps set
      | NNF_POS (ps, _) => add_list ps set
      | NOT_OR_ELIM (p, _) => add p set
      | PROOF_BIND (_, p) => add p set
      | QUANT_INST _ => set
      | QUANT_INTRO (p, _) => add p set
      | REFL _ => set
      | REWRITE _ => set
      | SKOLEM _ => set
      | SYMM (p, _) => add p set
      | TH_LEMMA_ARITH (_, ps, _) => add_list ps set
      | TH_LEMMA_ARRAY (_, ps, _) => add_list ps set
      | TH_LEMMA_BASIC (_, ps, _) => add_list ps set
      | TH_LEMMA_BV (_, ps, _) => add_list ps set
      | TH_LEMMA_DATATYPE (_, ps, _) => add_list ps set
      | TH_LEMMA_SEQ (_, ps, _) => add_list ps set
      | TH_LEMMA_CHAR (_, ps, _) => add_list ps set
      | TH_LEMMA_ADVANCED (_, ps, _) => add_list ps set
      | TRANS (p, q, _) => add q (add p set)
      | TRANS_STAR (ps, _) => add_list ps set
      | TRUE_AXIOM _ => set
      | UNIT_RESOLUTION (ps, _) => add_list ps set
      | ID _ => set
      | THEOREM _ => set
  in
    Redblackmap.foldl (fn (_, pt, set) => add pt set)
      Term.empty_tmset (proof_steps proof)
  end

  (* Exercise the semantic advanced-family cache policy without manufacturing
     an otherwise unsupported Z3 proof node.  The same finite checked-state
     lookup must remain available when D-mode disables performance caches. *)
  fun replay_advanced_with_cached_for_test cached target =
  let
    val metadata = mk_th_lemma_metadata
      ("nonlinear-arith", SOME "lemma", ["1"])
    val state = state_cache_thm
      (initial_replay_state Term.empty_tmset []
        (empty_proof "4.12.4")) cached
    val (_, thm) = z3_th_lemma_advanced metadata (state, [], target)
  in
    thm
  end

  fun replay_root_with_definitions_for_test definitions proof : Thm.thm =
  let
    val state = initial_replay_state (proof_asserted_hyps proof)
      definitions proof
    val ((_, _), thm) = thm_of_proofterm ((state, proof), ID 0) Lib.I
  in
    thm
  end

  fun replay_root_for_test proof : Thm.thm =
    replay_root_with_definitions_for_test [] proof

  fun replay_root_with_state_for_test proof =
  let
    val state = initial_replay_state (proof_asserted_hyps proof) [] proof
    val ((state, _), thm) = thm_of_proofterm ((state, proof), ID 0) Lib.I
  in
    {asserted_hyps = HOLset.listItems (#asserted_hyps state),
     definition_hyps = HOLset.listItems (#definition_hyps state),
     thm = thm}
  end

  (* returns a theorem that concludes ``F``, with its hypotheses (a
     subset of) those asserted in the proof *)
  fun check_proof_impl definitions (asl, g, proof) : Thm.thm =
  let
    val _ = if !Library.trace > 1 then
        Feedback.HOL_MESG "HolSmtLib: checking Z3 proof"
      else ()

    (* initial state *)
    val allowed_asserted_hyps = HOLset.addList
      (Term.empty_tmset, boolSyntax.mk_neg g :: asl)
    val state = initial_replay_state allowed_asserted_hyps definitions proof

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


  fun check_proof_with_definitions definitions args : Thm.thm =
    profile "check_proof(total)" (check_proof_impl definitions) args

  fun check_proof args : Thm.thm = check_proof_with_definitions [] args

end  (* local *)

end
