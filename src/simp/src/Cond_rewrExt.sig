(* Explicit extension compilation; ordinary Cond_rewr does not import this. *)
signature Cond_rewrExt =
sig
  include Abbrev
  type config =
    {solver : term list -> term -> thm, stack : term list,
     cond_depth : int option, term_ord : term * term -> order}
  type runners =
    {legacy : (term list -> term -> thm) -> term list -> conv,
     configured : config -> conv}
  val is_var_perm : term * term -> bool

  (* Low-level matcher preparation. The boolean is bounded status, not an
     allowance. Both closures share the one matcher. No counter is created.
     Legacy and configured NONE read Cond_rewr.stack_limit at each check;
     configured SOME n fixes depth without mutating the public reference. *)
  val COND_REWR_CONVS : string * thm -> bool -> runners
  val COND_REWR_CONV_WITH_CONFIG : string * thm -> bool -> config -> conv
  val COND_REWR_CONV_WITH_CONTEXT : string * thm -> bool ->
    {solver : term list -> term -> thm, stack : term list,
     cond_depth : int, term_ord : term * term -> order} -> conv

  (* Tracked construction binds the supplied ACTUAL control, including its
     current partially spent or exhausted value. No replacement ref/reset.
     Projection returns already-bound runners, without matching, recompiling,
     tracing or invoking callbacks. A successful application decrements once;
     failures do not spend. Callers synchronize concurrent mutation. *)
  type prepared
  val prepare : string * thm -> BoundedRewrites.control -> prepared
  val runners : prepared -> runners
  (* Explicit replay binding, not preparation: retain the same matcher and
     bind the supplied actual control without tracing or resetting it.
     Changing bounded/unbounded status raises HOL_ERR. *)
  val rebind : prepared -> BoundedRewrites.control -> prepared
end
