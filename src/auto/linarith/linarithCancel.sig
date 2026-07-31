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
    zero : term,
    assoc : thm,
    comm : thm,
    rid : thm,
    ac_fallback : conv option
  }

  (* cancel_common ops cancel: given the carrier's left-cancellation
     theorem, remove one summand common to both sides of a relation.
     Raises UNCHANGED when there is nothing to cancel. *)
  val cancel_common : ac_ops -> thm -> conv
end
