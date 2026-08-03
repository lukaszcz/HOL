signature linarithCancel =
sig
  include Abbrev

  (* Syntax and AC theorems of one carrier's addition, as consumed by
     cancel_common.  ac_fallback is an optional additive normalizer used
     when AC_CONV alone cannot justify a rearrangement. *)
  type ac_ops = {
    dest_less : term -> term * term,
    dest_leq : term -> term * term,
    strip_plus : term -> term list,
    mk_plus : term * term -> term,
    assoc : thm,
    comm : thm,
    rid : thm,
    ac_fallback : conv option
  }

  (* cancel_common ops cancel: given the carrier's left-cancellation
     theorem, remove one summand common to both sides of a relation.
     Raises UNCHANGED when there is nothing to cancel. *)
  val cancel_common : ac_ops -> thm -> conv

  (* The data an instance's norm_conv is made of: the carrier's three
     left-cancellation theorems, the polynomial normalizer for its
     expressions, the literal reducer, and the reflexivity theorems that
     decide a relation between equal sides.  expression_conv is expected
     to decline a term outside the carrier by raising UNCHANGED. *)
  type norm_spec = {
    ac : ac_ops,
    ty : hol_type,
    leq_cancel : thm,
    less_cancel : thm,
    eq_cancel : thm,
    expression_conv : conv,
    reduce_conv : conv,
    refl_thms : thm list
  }

  (* The whole of an instance's norm_conv: cancel down a relation of this
     carrier, and normalize anything else as an expression.  Which of the
     two a term is has to be decided before the conversions run, because
     ORELSEC catches HOL_ERR only, so an alternative that signals "not
     mine" by raising UNCHANGED is never reached past. *)
  val mk_norm_conv : norm_spec -> conv
end
