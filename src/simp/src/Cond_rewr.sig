(* ----------------------------------------------------------------------
    COND_REWR_CONV : thm -> bool -> (term -> thm) -> conv

    Build a conversion based on a conditional rewrite theorem.  The
    theorem must be of the form

          A |- P1 ==> ... Pm ==> (Q[x1,...,xn] = R[x1,...,xn])

    The conversion matches the input term against Q, using limited
    higher order matching.  This instantiates x1 ... xn, which the
    conversion then solves with the solver provided.  If any of the
    conditions are not solved COND_REWR_CONV fails.

    The theorem can be a permutative rewrite, such as
         |- (x = y) = (y = x)
         |- (x + y) = (y + x)

    In these cases the rewrite will be applied if

      * the ordering of the variables in the term is not in strictly
        ascending order, according to a term_lt function which places
        a total ordering on terms (Nb. The term ordering needs to be
        "AC" compatible - see Termord); or
      * if the boolean argument is true, which happens if the theorem
        being used is a bounded rewrite, and so cannot cause a loop
        when it is used.

    FAILURE CONDITIONS

    Fails if any of the assumptions cannot be solved by the solver,
    or if the term does not match the rewrite in the first place.
   ---------------------------------------------------------------------- *)

signature Cond_rewr =
sig

  include Abbrev
  type controlled_thm = BoundedRewrites.controlled_thm
  val ac_term_ord    : term * term -> order
  val mk_cond_rewrs  : controlled_thm -> controlled_thm list
  val IMP_EQ_CANON   : controlled_thm -> controlled_thm list
  (* The same, reporting what they discard or weaken at the given
     simplifier.trace level rather than the ambient one *)
  val mk_cond_rewrs_at : int -> controlled_thm -> controlled_thm list
  val IMP_EQ_CANON_AT  : int -> controlled_thm -> controlled_thm list
  val COND_REWR_CONV : string * thm -> bool ->
                       (term list -> term -> thm) -> term list -> conv

  (* COND_REWR_CONV's matcher, prepared once, behind two runners.  legacy
     is COND_REWR_CONV, reporting at the ambient simplifier.trace level.
     configured takes the side-condition depth (NONE: read stack_limit at
     each application), the order deciding whether a permutative rewrite
     applies, and the simplifier.trace level to report at.  legacy is
     configured with NONE, ac_term_ord and the ambient level. *)
  type config =
    {solver : term list -> term -> thm, stack : term list,
     cond_depth : int option, term_ord : term * term -> order,
     trace : int}
  type runners =
    {legacy : (term list -> term -> thm) -> term list -> conv,
     configured : config -> conv}
  val COND_REWR_CONVS : string * thm -> bool -> runners
  val is_var_perm : term * term -> bool
  val QUANTIFY_CONDITIONS : controlled_thm -> controlled_thm list
  val stack_limit : int ref

  (* run something, and report which rewrites fired while it ran *)
  val with_tracking : ('a -> 'b) -> 'a -> 'b * thm list

  (* report a fired rewrite to the current tracking extent, if any;
     used by the extension engine so both share one extent *)
  val note_rewrite : thm -> unit

end
