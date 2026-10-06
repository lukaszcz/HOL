# Note on the Simplifier Code

The simplifier has two layers.  `Traverse` is the conversion engine: it
rewrites one term and proves a theorem relating the input and output.
`simpLib` builds simpsets around that engine and supplies the tactic-level
loop which may solve or split goals.

## Important Types

**simpset**

:   (From `simpLib`.)
    A runtime simplification configuration, typically built by combining
    *simpset fragments*.  Its main components are:

    -   `mk_rewrs`, which turns arbitrary user theorems into controlled
        rewrites;
    -   `initial_net`, a higher-order term net containing rewrite and
        simplifier conversions;
    -   `dprocs`, the lower-priority decision procedures, represented as
        *reducers*;
    -   `travrules`, which contains relations and congruence procedures;
    -   tactic strategy data: named loopers and separate named safe and
        unsafe solver lists;
    -   engine strategy data: an optional subgoaler, conditional-rewrite
        depth, term order and traversal limit; and
    -   fragment history and exclusion data used when rebuilding a simpset.

    The solver distinction crosses the engine/tactic boundary.  The unsafe
    list is used inside `Traverse` to prove rewrite side conditions.  At the
    tactic layer, the invocation mode selects either the safe or unsafe list
    as final solvers.  A safe tactic invocation therefore still uses unsafe
    solvers for side conditions.

    Loopers are named tactics of type `simpset -> tactic`.  They are tried in
    registration order and receive the invocation simpset, including
    temporary marker processing and exclusions.  A looper must fail when it
    is inapplicable.  Simpset limits also bound successful looper rounds.

**ssfrag** (a “simpset fragment”)

:   (From `simpLib`.)
    A composable collection of user-provided data which is pushed into a
    *simpset*.  It can contain rewrites, conversions, theorem congruences,
    AC rewrites, decision procedures, relation-simplification data,
    loopers, safe and unsafe solvers, and an optional `filter` which
    adjusts the simpset's `mk_rewrs` function.

    The optional subgoaler, conditional depth and term order are whole-
    simpset strategy choices rather than fragment data.

**reducer**

:   (From `Traverse`.)
    A bundled piece of code and data capable of producing theorems relating
    input terms to fresh outputs.  Each reducer has its own notion of
    context, to which clients can add theorems.  These contexts use
    exceptions to provide existential types.  Added theorems may be goal
    assumptions or assumptions introduced by congruence rules.

    Each reducer has an `apply` function.  It receives the reducer's
    context, a `solver` for side conditions, a stack of side conditions
    already being attempted, a recursive `conv`, the current relation and
    an input term.  It should return a theorem of the form

        |- input R output

    where `R` is normally the supplied relation.

    Arithmetic decision procedures are reducers.  Their private context is
    the list of theorems they consider relevant (for example, Presburger
    terms), and they may ignore all other `apply` information.

    Reducers do not depend on the rest of the simplification code, although
    their `conv` and `solver` continuations call back into `Traverse`.

**simp_prover_ctxt**, **ssolver** and **subgoaler**

:   (From `Traverse`.)
    A `simp_prover_ctxt` is the common context supplied to the two
    side-condition proving seams:

        {stack        : term list,
         context_thms : thm list,
         recurse      : term -> thm}

    `stack` records nested side conditions.  `context_thms` contains the
    theorems currently in scope.  `recurse c` recursively simplifies `c`
    under equality in that same traversal context and returns a theorem
    `|- c = c'`.

    A `subgoaler` has type

        simp_prover_ctxt -> term -> thm

    and also returns a simplification equality.  An `ssolver` is a named
    record whose `solve` field has type

        simp_prover_ctxt -> term -> thm

    but proves its input term.  `simpLib.mk_tactic_solver` adapts a tactic to
    this interface while making `context_thms` available as assumptions.

**preorder**

:   (From `Travrules`.)
    A preorder identifies a relation of type `'a -> 'a -> bool` as reflexive
    and transitive.  It stores the relation constant and functions
    implementing transitivity and reflexivity.  Transitivity takes two
    theorems.  Reflexivity takes both the argument and an instantiated
    relation term, because the relation may be polymorphic.  For equality,
    the data is `min$=`, `TRANS` and essentially `REFL`.

**travrules**

:   (From `Travrules`.)
    A `travrules` value contains preorders and two lists of *congprocs*: the
    standard `congprocs` and the weakening `weakenprocs`.  The default
    `EQ_tr` contains the equality preorder and equality congruence procedure,
    with no weakening congruence procedures.

    This is static traversal information.  The dynamic `trav_state`, private
    to `Traverse`, stores the current relation, reducer contexts, context
    theorems and context free variables.  A simpset contains one merged
    `travrules` value.

**congproc**

:   (From `Opening`.)
    A congproc sets up recursive simplification of an input term.  Apart from
    the core equality congruences (`MK_COMB` and `ABS`), congprocs are built
    with `CONGPROC`.  In addition to the term, a congproc receives:

    -   `depther`, which recursively simplifies subterms;
    -   `solver`, which handles congruence-rule side conditions;
    -   `relation`, identifying the current relation; and
    -   `freevars`, the context's free variables, which matter when
        descending under a binder.

    Congprocs are stored in `travrules`.

## Context Accumulation

`Traverse` keeps two forms of context in parallel.  Each reducer has its
private existential context, while `trav_state.context_thms` retains the
actual theorem list for generic solvers.

The theorem list supplied to `TRAVERSE` initializes both forms.  Whenever a
congruence procedure descends with additional assumptions, `add_context`
passes the same theorem batch to every reducer and prepends it to
`context_thms`.  Thus side-condition provers see goal assumptions and the
assumptions introduced while traversing congruence rules, not merely the
initial user rewrite theorems.

`TRAVERSE_WITH_CONTEXT` separates its initial context into
`reducer_context` and `solver_context`.  Reducer-context theorems initialize
both forms, as with `TRAVERSE`; solver-context theorems do not affect private
reducer contexts, but extend both `context_thms` and the shared `freevars`
capture context.  Including their hypothesis free variables ensures that
descent under binders remains capture-avoiding.  `ROOT_REWRITE_WITH_CONTEXT`
provides the corresponding root-only operation.  This separation lets
callers expose the source theorem for an already-installed rule to solvers
without installing a second reducer or refreshing a bounded rewrite.

## Engine Side-Condition Pipeline

A reducer or congruence procedure calls the engine solver when a conditional
rewrite or congruence rule has a condition `c`.  `Traverse` constructs a
`simp_prover_ctxt` from the current side-condition stack, accumulated
`context_thms` and recursive equality traversal.  It then runs this pipeline:

1. Run the configured subgoaler on `c`, or use `recurse` when no subgoaler is
   configured, obtaining `|- c = c'`.
2. If `c'` is `T`, use `EQT_ELIM` to prove `c`.
3. Otherwise, try the engine solver records in order on `c'`.  The first
   solver which proves `c'` is transported back across the equality to prove
   `c`.

Only `HOL_ERR` means that a solver is inapplicable; unrelated exceptions
propagate.  Traversal-limit state is restored when this pipeline fails.
With no subgoaler and no solver records, a compatibility fast path performs
the original operation, `EQT_ELIM` after recursive traversal.

`traverseconfig_for_ss` always supplies the simpset's *unsafe* solver list
to this pipeline.  This is true even when the surrounding tactic is in safe
mode.

## Traversal Engine Settings

A simpset can configure conditional-rewrite depth and term ordering with
`set_cond_depth` and `set_term_ord`.  The corresponding fields live in
`Traverse.traverse_config`, the companion record of `traverse_data`, and
are options.  At traversal entry, an unconfigured depth resolves to the
user-level default `Cond_rewr.stack_limit`, while an unconfigured order
resolves to `Cond_rewr.ac_term_ord`.  `TRAVERSE`, which takes a
`traverse_data` alone, runs at `Traverse.default_config`, in which both
are unconfigured.

The resolved values travel explicitly in every reducer's `apply` record and
are passed directly to `COND_REWR_CONV_WITH_CONTEXT`.  There is no
dynamically scoped engine state.  Consequently, a nested traversal
resolves its own options and cannot inherit an enclosing simpset's
settings.  Changing `Cond_rewr.stack_limit` still affects every
unconfigured traversal, including one nested inside a traversal that has
its own configured depth.

The depth setting bounds nested conditional-rewrite attempts.  The term
order controls the orientation guard for unbounded permutative rewrites;
bounded rewrites continue to bypass that guard.

## Prepared Global Rewrites

`GEN_GLOBAL_SIMP_TAC` decodes its invocation-supplied ordinary rewrite
theorems once into prepared theorems and controls.  They are not added to
the simpset history.  Each assumption, conclusion, or implication-rebuild
traversal first processes its remaining marker directives, then runs that
marker-adjusted simpset's `mk_rewrs` filter over the same prepared values.
The resulting conversion closures therefore share one invocation-wide
bounded control even when local `Excl`, `ExclSF`, `SF`, `Cong`, `Split`, or
`AC` directives rebuild or alter the simpset.

Generic solvers, binder-capture tracking, and decision procedures receive
the prepared rules' underlying source theorems, with any artificial bounded
hypothesis removed.  Prepared conversions are installed only in each
traversal's sole rewriter reducer.  Public
`traversedata_for_ss`, `SIMP_CONV`,
`GEN_SIMP_TAC`, `TRAVERSE`, and `ROOT_REWRITE` retain their legacy behavior;
the prepared path is internal to `simpLib`.

## Tactic Loop and Conversion Boundary

`GEN_SIMP_TAC` and the usual simplification tactics use the following
per-goal strategy after processing theorem-list markers:

1. Rewrite the goal with `SIMP_CONV`.
2. On the residual goal, try final solvers in order.  Safe mode selects the
   safe list; ordinary mode selects the unsafe list.
3. If no final solver applies, run the first applicable enabled looper.
4. Recursively run the whole strategy on every subgoal produced by that
   looper.

In schematic tactic notation, the shape is:

    rewrite THEN
      (final_solver ORELSE
       TRY (first_looper THEN_LT ALLGOALS recurse))

If rewriting proves the goal, there is no residual goal for later stages.  If
neither a final solver nor a looper applies, `TRY` leaves the rewritten goal
open.  Re-entering the complete strategy after a looper is important: every
new subgoal is rewritten and gets its own solver and looper opportunity.

The conversion APIs deliberately stop at the engine boundary.  `SIMP_CONV`,
`SIMP_RULE` and `SIMP_PROVE` use unsafe solvers inside `Traverse` for rewrite
side conditions, but never run tactic-level loopers or final solvers.  They
also never use the safe solver list.  Assumption-rewriting passes in the
full-simplification tactics use this conversion-only behavior; their final
goal-directed simplification enters the tactic loop.

## Important Functions

`SIMP_QCONV`

:   (From `simpLib`.)
    Builds initial reducer contexts and calls `TRAVERSE` with the simpset's
    rewrite reducer, decision procedures, traversal rules and engine strategy
    fields.

`TRAVERSE`

:   (From `Traverse`.)
    Implements the simplifier's traversal of terms.  Its central ordering is
    schematically

        repeat high_priority then descend ...

    The high-priority phase fires the rewrite reducer.  Descent recursively
    simplifies subterms.  The remaining phase gives lower-priority decision
    procedures and weakening congruence procedures a chance to fire, so they
    effectively see terms bottom-up.  `ROOT_REWRITE` uses the same data and
    context machinery but applies a reducer only at the root.

`CONGPROC`

:   (From `Opening`.)
    Builds a congproc from a congruence theorem and a general reflexivity
    operation.  Reflexivity must support several relations at once: premises
    of a congruence theorem may use one relation while its conclusion uses
    equality, as happens with weakening congruences.

    Reprocessing congruence assumptions can unnecessarily revisit terms.  For
    example, the conditional-expression rule has the shape

        p = p' ==> (p' ==> t = t') ==> (~p' ==> e = e') ==>
        (COND p t e = COND p' t' e')

    The reprocess flag is set for the `~p'` assumption because it is not just
    a variable.  Reprocessing is important if negation exposes a simplifiable
    form, but if nothing changes at the top level it repeats descent into
    `p'`.
