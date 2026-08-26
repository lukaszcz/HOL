(* Copyright (c) 2026 The HOL4 contributors. *)

(* Shared, proved normal forms used at checked-replay boundaries. *)

structure SmtReplayCanon =
struct

  val ERR = Feedback.mk_HOL_ERR "SmtReplayCanon"

  fun unchanged conv tm = conv tm handle Conv.UNCHANGED => Thm.REFL tm

  fun compose conversions tm =
    let
      fun step (conv, theorem) =
        let
          val current = boolSyntax.rhs (Thm.concl theorem)
          val next = unchanged conv current
        in
          Thm.TRANS theorem next
        end
    in
      List.foldl step (Thm.REFL tm) conversions
    end

  val smt_ediv_total_tm = Term.prim_mk_const
    {Thy = "HolSmt", Name = "smt_ediv_total"}
  val smt_emod_total_tm = Term.prim_mk_const
    {Thy = "HolSmt", Name = "smt_emod_total"}
  val smt_rdiv_tm = Term.prim_mk_const
    {Thy = "HolSmt", Name = "smt_rdiv"}

  fun contains_const constant tm =
    Lib.can (HolKernel.find_term (fn subterm =>
      Term.is_const subterm andalso Term.same_const subterm constant)) tm

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
    HolSmtTheory.smt_emod_total_ediv_negone,
    HolSmtTheory.smt_ediv_total_def,
    HolSmtTheory.smt_rdiv_lneg,
    HolSmtTheory.smt_rdiv_rneg
  ]

  fun reorient_equality_conv tm =
    let
      val reversed = boolSyntax.mk_eq (Lib.swap (boolSyntax.dest_eq tm))
    in
      if Term.compare (reversed, tm) = LESS then Conv.SYM_CONV tm
      else raise Conv.UNCHANGED
    end

  fun reflexive_equality_conv tm =
    let
      val (left, right) = boolSyntax.dest_eq tm
    in
      if Term.aconv left right then Drule.EQT_INTRO (Thm.REFL left)
      else raise Conv.UNCHANGED
    end

  (* Normalization below propositions: relation aliases, pushed real_of_int,
     totalized integer arithmetic, ground total computation, and eta. *)
  fun cpc_term_canon_conv tm =
    compose
      [Rewrite.PURE_REWRITE_CONV cpc_alias_rewrites,
       Conv.TOP_DEPTH_CONV ground_total_conv,
       Rewrite.PURE_REWRITE_CONV cpc_alias_rewrites,
       Conv.TOP_DEPTH_CONV Drule.ETA_CONV]
      tm

  fun cpc_operand_canon_conv tm =
    compose
      [cpc_term_canon_conv,
       Conv.TOP_DEPTH_CONV reflexive_equality_conv,
       Conv.TOP_DEPTH_CONV reorient_equality_conv,
       (* Reflexive reduction only replaces a Boolean equality by T.  Of the
          term canonicalizer's rules, this can expose only ~T/~F; avoid a
          second ground-arithmetic and eta traversal at every CPC step. *)
       Rewrite.PURE_REWRITE_CONV
         [Thm.CONJUNCT1 boolTheory.NOT_CLAUSES,
          Thm.CONJUNCT2 boolTheory.NOT_CLAUSES],
       Conv.TOP_DEPTH_CONV reflexive_equality_conv,
       Conv.TOP_DEPTH_CONV reorient_equality_conv]
      tm

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
      if (Type.compare (ty, intSyntax.int_ty) = EQUAL orelse
          Type.compare (ty, realSyntax.real_ty) = EQUAL) andalso
         not (List.null (Term.free_vars tm)) then
        polynomial_conv ty tm
      else
        raise Conv.UNCHANGED
    end

  fun arith_poly_norm_conversion target =
    let val ty = Term.type_of target in
      if Type.compare (ty, intSyntax.int_ty) = EQUAL orelse
         Type.compare (ty, realSyntax.real_ty) = EQUAL then
        polynomial_conv ty target
      else if Lib.can Type.dom_rng ty then
        normalize_polynomial_function target
      else
        unchanged (Conv.TOP_DEPTH_CONV polynomial_subterm_conv) target
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
    if Type.compare (ty, intSyntax.int_ty) = EQUAL orelse
       Type.compare (ty, realSyntax.real_ty) = EQUAL then
      polynomial_conv ty target
    else case Lib.total Type.dom_rng ty of
      SOME (_, range) =>
        if Type.compare (range, intSyntax.int_ty) = EQUAL orelse
           Type.compare (range, realSyntax.real_ty) = EQUAL then
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
        if contains_const smt_rdiv_tm target then
          compose
            [cpc_term_canon_conv,
             Conv.TOP_DEPTH_CONV smt_rdiv_nonzero_conv,
             Rewrite.PURE_REWRITE_CONV [realTheory.real_div]] target
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
