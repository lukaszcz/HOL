(* Copyright (c) 2026 The HOL4 contributors. *)

(* Shared, proved normal forms used at checked-replay boundaries. *)

structure SmtReplayCanon =
struct

  val ERR = Feedback.mk_HOL_ERR "SmtReplayCanon"

  (* Left-to-right conversion chain, total: an all-unchanged chain yields
     REFL rather than raising. *)
  fun compose conversions =
    Conv.QCONV (List.foldr Conv.THENC Conv.ALL_CONV conversions)

  (* The SMT arithmetic sorts: Int and Real. *)
  fun is_arith_type ty =
    Type.compare (ty, intSyntax.int_ty) = EQUAL orelse
    Type.compare (ty, realSyntax.real_ty) = EQUAL

  val smt_ediv_total_tm = Term.prim_mk_const
    {Thy = "HolSmt", Name = "smt_ediv_total"}
  val smt_emod_total_tm = Term.prim_mk_const
    {Thy = "HolSmt", Name = "smt_emod_total"}
  val smt_rdiv_tm = Term.prim_mk_const
    {Thy = "HolSmt", Name = "smt_rdiv"}

  fun smt_rdiv_nonzero_conv tm =
    let
      val (head, arguments) = boolSyntax.strip_comb tm
      val _ = Term.same_const head smt_rdiv_tm orelse raise Conv.UNCHANGED
      val (numerator, denominator) =
        case arguments of
          [numerator, denominator] => (numerator, denominator)
        | _ => raise Conv.UNCHANGED
      val nonzero = simpLib.SIMP_PROVE (bossLib.srw_ss ()) []
        (boolSyntax.mk_neg
          (boolSyntax.mk_eq (denominator, realSyntax.zero_tm)))
    in
      Thm.MP (Drule.SPECL [numerator, denominator]
        HolSmtTheory.smt_rdiv_eq_div) nonzero
    end
    handle Feedback.HOL_ERR _ => raise Conv.UNCHANGED

  fun is_ground_total tm =
    let
      val (head, args) = boolSyntax.strip_comb tm
    in
      List.length args = 2 andalso List.null (Term.free_vars tm) andalso
      (Term.same_const head smt_ediv_total_tm orelse
       Term.same_const head smt_emod_total_tm)
    end
    handle Feedback.HOL_ERR _ => false

  fun ground_total_conv tm =
    if is_ground_total tm then bossLib.EVAL tm else raise Conv.UNCHANGED

  val cpc_alias_rewrites = [
    Thm.CONJUNCT1 boolTheory.NOT_CLAUSES,
    Thm.CONJUNCT2 boolTheory.NOT_CLAUSES,
    boolTheory.COND_CLAUSES,
    integerTheory.INT_GT,
    integerTheory.INT_GE,
    integerTheory.int_sub,
    realTheory.real_gt,
    realTheory.real_ge,
    intrealTheory.real_of_int_add,
    intrealTheory.real_of_int_sub,
    intrealTheory.real_of_int_mul,
    intrealTheory.real_of_int_neg,
    intrealTheory.real_of_int_num,
    (* The SMT-LIB encoding spells to_int ceiling through negated to_int
       floor.  Canonicalize HOL's surface ceiling to that emitted form. *)
    HolSmtTheory.int_ceiling_floor,
    HolSmtTheory.smt_rdiv_lneg,
    HolSmtTheory.smt_rdiv_rneg
  ]

  (* Built once: PURE_REWRITE_CONV constructs its net when applied to the
     theorem list, so a per-call occurrence rebuilds it at every step. *)
  val cpc_alias_conv = Rewrite.PURE_REWRITE_CONV cpc_alias_rewrites

  val not_clauses_conv = Rewrite.PURE_REWRITE_CONV
    [Thm.CONJUNCT1 boolTheory.NOT_CLAUSES,
     Thm.CONJUNCT2 boolTheory.NOT_CLAUSES]

  val real_div_conv = Rewrite.PURE_REWRITE_CONV [realTheory.real_div]

  fun reorient_equality_conv tm =
    let
      val (left, right) = boolSyntax.dest_eq tm
      val reversed = boolSyntax.mk_eq (right, left)
    in
      if Term.compare (right, left) = LESS then
        Drule.IMP_ANTISYM_RULE
          (Thm.DISCH tm (Thm.SYM (Thm.ASSUME tm)))
          (Thm.DISCH reversed (Thm.SYM (Thm.ASSUME reversed)))
      else raise Conv.UNCHANGED
    end

  (* Z3 emits propositionally identical rewrite conclusions with arbitrary
     operand order.  Use one proof-producing key space for rewrite proformas:
     equality atoms and binary Boolean operands are oriented deterministically
     without simplifying, deleting, or reassociating operands.  Recursive
     binary orientation stays linear on large solver-generated formulas. *)
  fun reorient_binary_conv dest comm tm =
    let
      val (left, right) = dest tm
    in
      if Term.compare (right, left) = LESS then Conv.REWR_CONV comm tm
      else raise Conv.UNCHANGED
    end

  fun boolean_commute_conv tm =
    let
      fun conjunction source =
        let val premise = Thm.ASSUME source in
          Thm.DISCH source
            (Thm.CONJ (Thm.CONJUNCT2 premise) (Thm.CONJUNCT1 premise))
        end
      fun disjunction source left right =
        Thm.DISCH source
          (Thm.DISJ_CASES (Thm.ASSUME source)
            (Thm.DISJ2 right (Thm.ASSUME left))
            (Thm.DISJ1 (Thm.ASSUME right) left))
      val (left, right, forward, backward) =
        if boolSyntax.is_conj tm then
          let
            val (left, right) = boolSyntax.dest_conj tm
            val reverse = boolSyntax.mk_conj (right, left)
          in (left, right,
              fn () => conjunction tm,
              fn () => conjunction reverse) end
        else if boolSyntax.is_disj tm then
          let
            val (left, right) = boolSyntax.dest_disj tm
            val reverse = boolSyntax.mk_disj (right, left)
          in (left, right,
              fn () => disjunction tm left right,
              fn () => disjunction reverse right left) end
        else raise Conv.UNCHANGED
    in
      if Term.compare (right, left) = LESS then
        Drule.IMP_ANTISYM_RULE (forward ()) (backward ())
      else raise Conv.UNCHANGED
    end

  (* Canonical orientation only permutes children.  Visit each physically
     shared input node once, normalize its children first, and cache the
     checked equality for this invocation.  Tree-depth conversions revisit
     exponentially many paths through solver-generated shared circuits. *)
  fun dag_conversion revisit orient root =
    let
      val bucket_count = 4093
      val cache = Array.array
        (bucket_count, [] : (Term.term * Thm.thm) list)
      val active = ref ([] : Term.term list)
      fun normalize term =
        let
          val index = SmtResource.pointer_bucket bucket_count term
          val bucket = Array.sub (cache, index)
        in
          case List.find
              (fn (saved, _) => Portable.pointer_eq (saved, term)) bucket of
            SOME (_, theorem) => theorem
          | NONE =>
              let
                val _ = not (List.exists
                    (fn prior => Portable.pointer_eq (prior, term))
                    (!active)) orelse
                  raise ERR "dag_conversion" "cyclic rewrite expansion"
                val _ = active := term :: !active
                val children =
                  if Term.is_comb term then
                    let
                      val (operator, operand) = Term.dest_comb term
                      val operator_thm = normalize operator
                      val operand_thm = normalize operand
                    in
                      if Portable.pointer_eq (operator,
                           boolSyntax.rhs (Thm.concl operator_thm)) andalso
                         Portable.pointer_eq (operand,
                           boolSyntax.rhs (Thm.concl operand_thm)) then
                        Thm.REFL term
                      else Thm.MK_COMB (operator_thm, operand_thm)
                    end
                  else if Term.is_abs term then
                    let
                      val (variable, body) = Term.dest_abs term
                      val body_thm = normalize body
                    in
                      if Portable.pointer_eq
                           (body, boolSyntax.rhs (Thm.concl body_thm)) then
                        Thm.REFL term
                      else Thm.ABS variable body_thm
                    end
                  else Thm.REFL term
                val current = boolSyntax.rhs (Thm.concl children)
                val orientation = Conv.QCONV (Conv.TRY_CONV orient) current
                val right = boolSyntax.rhs (Thm.concl orientation)
                val orientation =
                  if revisit andalso not (Term.aconv current right) then
                    Thm.TRANS orientation (normalize right)
                  else orientation
                val theorem =
                  if Portable.pointer_eq (term, current) then orientation
                  else if Portable.pointer_eq (current,
                      boolSyntax.rhs (Thm.concl orientation)) then children
                  else Thm.TRANS children orientation
                val _ = Array.update (cache, index,
                  (term, theorem) :: Array.sub (cache, index))
                val _ = active := tl (!active)
              in theorem end
        end
    in normalize root end

  val dag_orientation_conv = dag_conversion false
  val dag_rewrite_conv = dag_conversion true

  (* Canonicalize physical sharing without changing any HOL syntax.  The
     postorder visitor interns alpha-equal terms after their children have
     been shared; every reuse is justified by kernel ALPHA, never by a hash. *)
  fun share_conv root =
    let
      val index = SmtResource.new_bounded_term_index
        SmtResource.max_bv_replay_term_nodes
      val representatives = ref (Redblackmap.mkDict Int.compare)
      fun intern term =
        case index term of
          NONE => Thm.REFL term
        | SOME id =>
            (case Redblackmap.peek (!representatives, id) of
               SOME representative => Thm.ALPHA term representative
             | NONE =>
                 (representatives := Redblackmap.insert
                    (!representatives, id, term);
                  Thm.REFL term))
    in dag_orientation_conv intern root end

  (* The head patterns are disjoint.  Orienting each parent after all of its
     children therefore establishes both normal forms in one postorder pass,
     including equalities whose Boolean operands were just permuted. *)
  val z3_primary_rewrite_canon_conv = dag_orientation_conv
    (Conv.FIRST_CONV [reorient_equality_conv, boolean_commute_conv])

  (* Z3 may express the same arithmetic rewrite through a dual relation,
     a negated conditional guard, or commuted addition.  These rules are
     deliberately separate from the primary canonicalizer: their broader
     normalization is accepted only when it closes the concrete difference
     between the two sides of the rewrite. *)
  val z3_cond_polarity_conv =
    dag_orientation_conv (Conv.REWR_CONV HolSmtTheory.COND_NEG)

  val z3_relation_dual_conv = dag_orientation_conv
    (Conv.FIRST_CONV (List.map Conv.REWR_CONV
    [integerTheory.INT_GT,
     integerTheory.INT_GE,
     integerTheory.INT_NOT_LT,
     integerTheory.INT_NOT_LE,
     realTheory.real_gt,
     realTheory.real_ge,
     realTheory.REAL_NOT_LT,
     realTheory.REAL_NOT_LE]))

  (* After relation aliases are normalized, a non-strict order in an ite
     guard is the complement of the reversed strict order.  Expose that
     negation only at the guard, then use the polymorphic polarity theorem
     to swap the branches. *)
  fun z3_order_cond_polarity_conv tm =
    let
      val (guard, _, _) = boolSyntax.dest_cond tm
      val expose_negation =
        if Lib.can intSyntax.dest_leq guard then
          Conv.REWR_CONV (Conv.GSYM integerTheory.INT_NOT_LT)
        else if Lib.can realSyntax.dest_leq guard then
          Conv.REWR_CONV (Conv.GSYM realTheory.REAL_NOT_LT)
        else
          raise Conv.UNCHANGED
    in
      Conv.THENC
        (Conv.RATOR_CONV
           (Conv.RATOR_CONV (Conv.RAND_CONV expose_negation)),
         Conv.REWR_CONV HolSmtTheory.COND_NEG) tm
    end
    handle Feedback.HOL_ERR _ => raise Conv.UNCHANGED

  fun additive_order_conv tm =
    if intSyntax.is_plus tm then
      reorient_binary_conv intSyntax.dest_plus
        integerTheory.INT_ADD_COMM tm
    else if realSyntax.is_plus tm then
      reorient_binary_conv realSyntax.dest_plus
        realTheory.REAL_ADD_COMM tm
    else
      raise Conv.UNCHANGED

  val z3_difference_rewrite_canon_conv = compose
    [z3_relation_dual_conv,
     dag_orientation_conv z3_order_cond_polarity_conv,
     z3_cond_polarity_conv,
     dag_orientation_conv additive_order_conv,
     z3_primary_rewrite_canon_conv]

  fun equality_operands_alpha_equal tm =
    let val (left, right) = boolSyntax.dest_eq tm
    in Term.aconv left right end

  fun z3_rewrite_canon_conv tm =
    let
      val primary = z3_primary_rewrite_canon_conv tm
      val primary_target = boolSyntax.rhs (Thm.concl primary)
    in
      if not (boolSyntax.is_eq primary_target) orelse
         equality_operands_alpha_equal primary_target then
        primary
      else
        let
          val secondary = z3_difference_rewrite_canon_conv primary_target
          val secondary_target = boolSyntax.rhs (Thm.concl secondary)
        in
          if equality_operands_alpha_equal secondary_target then
            Thm.TRANS primary secondary
          else
            primary
        end
    end

  fun reflexive_equality_conv tm =
    let
      val (left, right) = boolSyntax.dest_eq tm
    in
      if Term.aconv left right then Drule.EQT_INTRO (Thm.REFL left)
      else raise Conv.UNCHANGED
    end

  (* Normalization below propositions: relation aliases, pushed real_of_int,
     ground total computation, and eta.  Symbolic totalized integer
     arithmetic requires per-translation provenance and is unfolded by the
     CPC strong canonicalizer instead. *)
  val cpc_term_canon_conv =
    compose
      [cpc_alias_conv,
       Conv.TOP_DEPTH_CONV ground_total_conv,
       cpc_alias_conv,
       Conv.TOP_DEPTH_CONV Drule.ETA_CONV]

  val cpc_operand_canon_conv =
    compose
      [cpc_term_canon_conv,
       Conv.TOP_DEPTH_CONV reflexive_equality_conv,
       Conv.TOP_DEPTH_CONV reorient_equality_conv,
       (* Reflexive reduction only replaces a Boolean equality by T.  Of the
          term canonicalizer's rules, this can expose only ~T/~F; avoid a
          second ground-arithmetic and eta traversal at every CPC step. *)
       not_clauses_conv,
       Conv.TOP_DEPTH_CONV reflexive_equality_conv,
       Conv.TOP_DEPTH_CONV reorient_equality_conv]

  (* Preserve the outer equality needed by TRANS and EQ_MP.  Its operands use
     the same recursive orientation as CPC congruence sources, but only the
     structurally neutral Boolean reduction [x = x] -> T; a broad Boolean
     simplifier here could erase the very context a congruence step consumes.
     The Term.compare choice remains deterministic and idempotent. *)
  fun cpc_canon_conv tm =
    if boolSyntax.is_eq tm then
      compose
        [Conv.BINOP_CONV cpc_operand_canon_conv,
         reorient_equality_conv]
        tm
    else
      cpc_operand_canon_conv tm

  fun cpc_canon_rule theorem = Conv.CONV_RULE cpc_canon_conv theorem

  fun polynomial_conv ty =
    if Type.compare (ty, intSyntax.int_ty) = EQUAL then
      intLib.INT_POLY_CONV
    else if Type.compare (ty, realSyntax.real_ty) = EQUAL then
      RealField.REAL_POLY_CONV
    else
      raise ERR "arith_poly_norm_prove"
        "polynomial equality is neither integer nor real"

  fun normalize_polynomial conv tm =
    compose [cpc_term_canon_conv, conv] tm

  fun normalize_polynomial_function tm =
    let
      val (domain, range) = Type.dom_rng (Term.type_of tm)
      val variable = Term.genvar domain
      val applied = Term.mk_comb (tm, variable)
      val body = polynomial_conv range applied
      val abstraction = Thm.ABS variable body
      val expansion = Term.mk_abs (variable, applied)
      val eta = Drule.ETA_CONV expansion
    in
      Thm.TRANS (Thm.SYM eta) abstraction
    end

  fun polynomial_subterm_conv tm =
    let val ty = Term.type_of tm in
      if is_arith_type ty andalso
         not (List.null (Term.free_vars tm)) then
        polynomial_conv ty tm
      else
        raise Conv.UNCHANGED
    end

  fun arith_poly_norm_conversion target =
    let val ty = Term.type_of target in
      if is_arith_type ty then
        polynomial_conv ty target
      else if Lib.can Type.dom_rng ty then
        normalize_polynomial_function target
      else
        Conv.QCONV (Conv.TOP_DEPTH_CONV polynomial_subterm_conv) target
    end

  fun prove_polynomial_equality target =
    let
      val (left, right) = boolSyntax.dest_eq target
      val ty = Term.type_of left
      val _ = Type.compare (ty, Term.type_of right) = EQUAL orelse
        raise ERR "arith_poly_norm_prove"
          "polynomial equality has different operand types"
      val conv = polynomial_conv ty
      val left_norm = normalize_polynomial conv left
      val right_norm = normalize_polynomial conv right
      val normalized_left = boolSyntax.rhs (Thm.concl left_norm)
      val normalized_right = boolSyntax.rhs (Thm.concl right_norm)
      val _ = Term.aconv normalized_left normalized_right orelse
        raise ERR "arith_poly_norm_prove"
          "polynomial canonical forms differ"
    in
      Thm.TRANS left_norm (Thm.SYM right_norm)
    end

  (* CPC and Z3 use "polynomial normalization" for both expression
     equalities and equivalent arithmetic atoms (including negated order
     relations).  Canonicalize aliases once, use the direct polynomial
     conversion when the target has that shape, and otherwise invoke the
     common proof-producing arithmetic normalizer.  This is intentionally
     one general path: its cost and coverage depend on the input polynomial,
     not on a catalogue of recorded proof shapes. *)
  fun arith_poly_norm_prove target =
    let val ty = Term.type_of target in
    if is_arith_type ty then
      polynomial_conv ty target
    else case Lib.total Type.dom_rng ty of
      SOME (_, range) =>
        if is_arith_type range then
          normalize_polynomial_function target
        else
          raise ERR "arith_poly_norm_prove"
            "polynomial function has a non-arithmetic result type"
    | NONE => let
      (* CPC's polynomial normalizer treats total real division by a
         demonstrably nonzero denominator as ordinary field division.  The
         simplifier discharges only proved nonzero side conditions (notably
         numerals), so the underspecified zero branch remains untouched. *)
      val target_norm =
        if Library.contains_const smt_rdiv_tm target then
          compose
            [cpc_term_canon_conv,
             Conv.TOP_DEPTH_CONV smt_rdiv_nonzero_conv,
             real_div_conv] target
        else cpc_term_canon_conv target
      val normalized = boolSyntax.rhs (Thm.concl target_norm)
      val proof =
        prove_polynomial_equality normalized
        handle Feedback.HOL_ERR _ =>
          Library.arith_prove_with_cases normalized
    in
      Thm.EQ_MP (Thm.SYM target_norm) proof
    end
    end

end
