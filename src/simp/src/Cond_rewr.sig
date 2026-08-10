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
  val COND_REWR_CONV : string * thm -> bool ->
                       (term list -> term -> thm) -> term list -> conv

  (* As COND_REWR_CONV, but with the side-condition depth and the
     permutative term order supplied by the caller rather than taken from
     the user-level defaults.  This is the form a Traverse.CONTEXT_REDUCER
     can hand its traversal's own settings to; COND_REWR_CONV is this one
     at cond_depth = !stack_limit and term_ord = ac_term_ord. *)
  val COND_REWR_CONV_WITH_CONTEXT :
                       string * thm -> bool ->
                       {solver : term list -> term -> thm,
                        stack : term list,
                        cond_depth : int,
                        term_ord : term * term -> order} -> conv
  val QUANTIFY_CONDITIONS : controlled_thm -> controlled_thm list

  (* The user-level default for the side-condition depth.  It applies to
     every traversal whose simpset does not configure the depth. *)
  val stack_limit : int ref

  val used_rewrites : thm list ref
  val track_rewrites : bool ref

end
