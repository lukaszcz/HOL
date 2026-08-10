(* =====================================================================
 * FILE          : traverse.sig
 * DESCRIPTION   : A programmable term traversal engine for hol90
 *
 * AUTHOR        : Donald Syme
 * ===================================================================== *)

signature Traverse =
sig
  include Abbrev

   (* ---------------------------------------------------------------------
    * type context
    *
    * Each reducer collects the working context on its own.
    * A context object is the current state of a single reducer.
    * ---------------------------------------------------------------------*)

  type context = exn (* well known SML hack to allow any kind of data *)

   (* ---------------------------------------------------------------------
    * Reducers
    *   These are the things that get applied to terms during
    * traversal.  They prove theorems which state that the
    * current term reduces to a related
    *
    * Each reducer manages its own storage of the working context (of one
    * of the forms above - Nb. in SML exceptions are able to contain
    * any kind of data, so contexts can be any appropriate format.  This
    * is a hack, but it is the best way to get good data hiding in SML
    * without resorting to functors)
    *
    * The fields of a reducer are:
    *
    * apply:  This is the reducer itself.  The arguments passed by
    *   the traversal engine to the reduce routine are:
    *    solver:
    *      A continuation function, to be used if the reducer needs to
    *      solve some side conditions and want to continue traversing
    *      in order to do so.  The continuation invokes traversal
    *      under equality, then calls EQT_ELIM.
    *
    *      At the moment the continuation is primarily designed to
    *      be used to solve side conditions in context.
    *
    *      Note that this function is *not* the same as
    *      the congruence side condition solver.
    *
    *    context:
    *      The reducer's current view of the context, as
    *      collected by its "addcontext" function.
    *    term list:
    *      The current side condition stack, which grows as nested calls
    *      to the solver are made.
    *
    * conv:
    *   A continuation function, to be used if the reducer
    *   wants to continue traversing. The continuation invokes traversal
    *   under equality. Similar to solver, but does not call EQT_ELIM.
    *
    * addcontext: routine is invoked every time more context is added
    *   to the current environment by virtue of congruence routines.
    *
    * initial:  The inital context.
    * ---------------------------------------------------------------------*)

  datatype reducer = REDUCER of {
         name : string option,
         initial: context,
         addcontext : context * thm list -> context,
         apply: {solver:term list -> term -> thm,
                 conv: term list -> term -> thm,
                 context: context,
                 stack:term list,
                 relation : (term * (term -> thm))} -> conv
       }
       | CONTEXT_REDUCER of {
         name : string option,
         initial: context,
         addcontext : context * thm list -> context,
         apply: {solver:term list -> term -> thm,
                 conv: term list -> term -> thm,
                 context: context,
                 stack:term list,
                 cond_depth:int,
                 term_ord:term * term -> order,
                 relation : (term * (term -> thm))} -> conv
       }

  (* dest_reducer is the pre-CONTEXT_REDUCER interface, and has nowhere to
     put the traversal's own settings: a context reducer seen through it
     runs at the default side-condition depth (!Cond_rewr.stack_limit) and
     the default term order (Cond_rewr.ac_term_ord).  reducer_data is the
     accessor that preserves them. *)

  val dest_reducer : reducer ->
        {name : string option,
         initial: context,
         addcontext : context * thm list -> context,
         apply: {solver:term list -> term -> thm,
                 conv: term list -> term -> thm,
                 context: context,
                 stack:term list,
                 relation : (term * (term -> thm))} -> conv}

  val reducer_data : reducer ->
        {name : string option,
         initial: context,
         addcontext : context * thm list -> context,
         apply: {solver:term list -> term -> thm,
                 conv: term list -> term -> thm,
                 context: context,
                 stack:term list,
                 cond_depth:int,
                 term_ord:term * term -> order,
                 relation : (term * (term -> thm))} -> conv}

  val addctxt : thm list -> reducer -> reducer

  type simp_prover_ctxt =
       {stack        : term list,
        context_thms : thm list,
        recurse      : term -> thm}
  type ssolver =
       {name : string, solve : simp_prover_ctxt -> term -> thm}
  type subgoaler = simp_prover_ctxt -> term -> thm

 (* ----------------------------------------------------------------------
     TRAVERSE : {rewriters: reducer list,
                 dprocs: reducer list,
                 travrules: travrules,
                 relation: term,
                 limit : int option}
                -> thm list -> conv

     Implements a procedure which tries to prove a term is related
     to a (simpler) term by the relation given in the travrules.
     This is done by traversing the term, applying the
     procedures specified in the travrules at certain subterms.
     The traversal strategy is similar to TOP_DEPTH_CONV.

     The traversal has to be justified by congruence rules.
     These are also in the travrules.  See "Congprocs" for a more
     detailed description of congruence rules.

     In the case of rewriting and simplification, the relation used is
     equality (--`$=`--).  However traversal can also be used with
     other congruences and preorders.

     The behaviour of TRAVERSE depends almost totally on what
     is contained in the input travrules.

     The theorem list is a set of theorems to add initially as context
     to the traversal.

     FAILURE CONDITIONS

     TRAVERSE never fails, though it may diverge or raise an exception
     indicating that a term is unchanged by the traversal.

     Bad congruence rules may cause very strange behaviour.
    ---------------------------------------------------------------------- *)

   type traverse_data = {rewriters: reducer list,
                         limit : int option,
                         dprocs: reducer list,
                         travrules: Travrules.travrules,
                         relation: term};

   val TRAVERSE : traverse_data -> thm list -> conv

   (* The traversal-strategy settings that traverse_data does not carry.
      An unset field takes the value TRAVERSE runs at: no subgoaler, no
      extra solvers, !Cond_rewr.stack_limit as the side-condition depth
      and Cond_rewr.ac_term_ord as the permutative term order.  The
      unconfigured settings are default_config, so that
        XTRAVERSE (data, default_config) = TRAVERSE data. *)
   type traverse_config = {subgoaler: subgoaler option,
                           solvers: ssolver list,
                           cond_depth: int option,
                           term_ord: (term * term -> order) option};

   type xtraverse_data = traverse_data * traverse_config

   val default_config : traverse_config

   val XTRAVERSE : xtraverse_data -> thm list -> conv

   (* As XTRAVERSE, but keep initial reducer additions separate from
      theorems which extend generic solver and binder-capture contexts
      only. *)
   val TRAVERSE_WITH_CONTEXT :
       xtraverse_data ->
       {reducer_context : thm list, solver_context : thm list} -> conv

   (* Apply one reducer at the root, without descending.  Recursive
      side-condition proving still uses the full traversal. *)
   val ROOT_REWRITE : xtraverse_data -> thm list -> conv

   val ROOT_REWRITE_WITH_CONTEXT :
       xtraverse_data ->
       {reducer_context : thm list, solver_context : thm list} -> conv

end (* sig *)
