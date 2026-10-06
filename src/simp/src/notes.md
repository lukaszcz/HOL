# Note on the Simplifier Code

## Important Types

**simpset**

:   (From `simpLib`.)
    Typically built by bundling *fragments* together, but is actually a collection of four important components:

    -   `mk_rewrs` function.
        This processes “arbitrary” user-provided theorems to turn them into proper rewrites.

    -   `net` a higher-order term-net containing simplifier-conversions

    -   `dprocs` a list of “decision procedures” (lower priority routines), which are *reducer*s.

    -   `travrules`, a *travrules* value

    It also holds strategy data: named loopers, named safe and unsafe solver lists, and an optional subgoaler, side-condition depth and term order.
    Every strategy change goes through `apply_strategy_event` and is recorded in the simpset history, so simpsets rebuilt from history keep it.

**ssfrag** (a ‘simpset fragment’)

:   (From `simpLib`.)
    A collection of user-provided data that gets pushed into *simpset*s.
    Includes rewrites, conversions, congruences, AC rewrites, decision procedures, relation-simplification data, loopers, safe and unsafe solvers and an optional `filter`, which is used to adjust the simpset `mk_rewrs` function.
    The subgoaler, side-condition depth and term order are whole-simpset settings, not fragment data.

**reducer**

:   (From `Traverse`.)
    A bundled piece of code/data that is capable of producing theorems relating input terms to fresh “outputs”.
    Each reducer has its own notion of “context”, values to which clients can add theorems.
    (These contexts are implemented with exceptions to give existential types.)
    Such added theorems may be goal assumptions, or provided by congruence rules.

    Each reducer has an `apply` function, which is passed a context, a `solver` for handling side conditions, a `stack` of already attempted side conditions, a continuation `conv`, a `relation` field and an input term.
    The `apply` function is expected to return a theorem of the form

        |- input  R   output

    where `R` might be as given in the `relation` field.
    A `CONTEXT_REDUCER`'s `apply` is additionally passed the traversal's
    side-condition depth and term order.
    A `CONFIG_REDUCER` receives an optional depth instead: `SOME n` is an
    explicit depth, while `NONE` leaves the default live for each native
    conditional rewrite candidate to read `Cond_rewr.stack_limit`.
    Both older constructor record shapes and the `dest_reducer` and
    `reducer_data` signatures are unchanged; `reducer_config_data` retains
    the option when adapting reducers (including `congLib` wrappers).

    Arithmetic decision procedures are `reducer`s.
    Their context is the list of theorems that they believe to be relevant (*i.e.*, Presburger terms), and they ignore all of the information provided by `apply` except the context.

    Reducers don’t depend on anything else in the simplification code base (though their `conv` and `solver`  continuations will call back into simplifier code).

**preorder**

:   (From `Travrules`.)
    A preorder encodes information enough to identify a relation (type `'a -> 'a -> bool`) as something that is reflexive and transitive.
    The preorder stores the constant of the particular relation, and two functions to implement transitivity and reflexivity.
    The former takes two theorems as input, while the latter takes both the argument to the relation and a relation term itself, which, if polymorphic, must have been instantiated so that it can be applied to the argument.
    For the equality case, this data is thus (`min$=`, `TRANS` and (essentially) `REFL`).

**travrules**

:   (From `Travrules`.)
    Embodies a list of *preorders* and two lists of *congprocs*: the “standard congprocs” (`congprocs`), and the “weakening congprocs” (`weakenprocs`).
    The “default” travrules value is `EQ_tr`, and contains the equality preorder, and the equality congproc as a standard congproc.
    (I.e., it has no weakening congprocs.)

    The travrules is a static piece of information for guiding simplification.
    The dynamic data that is maintained during simplification (containing context values, the relation currently being used and the context’s free variables) is a `trav_state`, which is private to module `Traverse`.

    Each simpset contains a list of `travrules` values.

**congproc**

:   (From `Opening`.)
    A congproc is a function that will set up recursive simplification of an input term.
    With the exception of the core equality congruences (`MK_COMB` and `ABS`) these are built with `CONGPROC` or `THREADED_CONGPROC`.
    In addition to the term, the congproc is passed a record of important data containing

    -   `depther`: a function which will be applied to subterms to produce simplified sub-terms
    -   `solver`: used to handle side-conditions in congruence rules
    -   `relation`: identifies the relation we’re using
    -   `freevars`: the free variables of the context, which may be relevant if descending under a binder

    `congproc` values are stored in `travrules`.

**simp_prover_ctxt**, **ssolver** and **subgoaler**

:   (From `Traverse`.)
    A `simp_prover_ctxt` is the record `{stack, context_thms, recurse}` passed to solvers and subgoalers: the side-condition stack, the theorems in scope, and recursive simplification of a term (returning `|- c = c'`).
    An `ssolver` is a named function proving its input term; a `subgoaler` returns `|- c = c'` for its input `c`.

## Context

`trav_state` keeps, alongside each reducer's private context, `context_thms`: the actual theorems, for solvers and subgoalers.
`add_context` adds a batch of theorems to both, and their hypotheses' free variables to `freevars`.
`TRAVERSE_WITH_CONTEXT` splits its initial theorems: `reducer_context` goes to both, `solver_context` only to `context_thms` and `freevars`.
This lets a caller show solvers the source of an already-installed rule without installing it twice or refreshing a bounded rewrite.

## Side conditions

The engine solver (`ctxt_solver` in `Traverse`) proves a condition `c` by running the subgoaler (or recursive traversal, if none is set) to get `|- c = c'`, then proving `c` from `c' = T` or from the first unsafe solver that proves `c'`.
Only `HOL_ERR` means a solver is inapplicable; on failure the traversal limit is restored.
With neither subgoaler nor solvers, the original `EQT_ELIM` path is taken.
`traverseconfig_for_ss` always supplies the unsafe list, even under a safe tactic; safe solvers are only ever final solvers in `GEN_SIMP_TAC`.

The depth and term order are options in `traverse_config`, resolved at traversal entry (unset: `!Cond_rewr.stack_limit`, read at each reducer application, and `Cond_rewr.ac_term_ord`) and passed explicitly to `COND_REWR_CONV_WITH_CONTEXT`.
There is no dynamically scoped state, so a nested traversal never inherits its caller's settings.

## Exclusion names

Bare `Excl` and `-*` retain develop's dots-only parser and ancestry check;
extended kernel `$` spellings and relaxed theory names require `rule:`.
Strict history entries are reparsed on replay; `rule:` keeps its resolved
pattern. Unmatched bare names silently record develop's rule deletion.

## Prepared global rewrites

The old simplification tactics dispatch strategy-free calls to develop's
code; strategy-bearing calls run as the new engines. Explicit
`GEN_GLOBAL_SIMP_TAC` calls always select counted prepared passes.

`GEN_GLOBAL_SIMP_TAC` decodes its ordinary theorem arguments once, without adding them to the simpset history.
Each traversal compiles them with its own marker-adjusted `mk_rewrs`, so bounded rewrites share one invocation-wide control; their source theorems go to the solver context.
`SIMP_CONV`, `GEN_SIMP_TAC`, `TRAVERSE` and `ROOT_REWRITE` do not use this path.

## Important Functions

`SIMP_QCONV`

:   (From `simpLib`.)
    Calls `TRAVERSE` after building initial context values for all of the embedded reducers (giving a trav_state)

`TRAVERSE`

:   (From `Traverse`.)
    Implements the logic of the simplifier’s traversal of terms.
    In particular, this is where the preorder/top-down nature of the simplifier wrt its equality rewrites is decided, because of the way it begins with

        repeat high_priority then descend ...

    The `high_priority` stuff here is to do fire the equality reducer.
    Descent is then the recursive simplification of sub-terms.
    The `...` portion is where decision procedures get to fire, and where weakenprocs get a chance to fire.
    These effectively see the term in bottom-up fashion as a result.

    `TRAVERSE` initializes supplied contexts at conversion construction.
    On each application, it constructs congruence and weakener conversions
    once per traversal context, before any root reduction, as on develop.
    Explicit `XTRAVERSE` refreshes contexts per application and accepts a
    `traverse_config` (subgoaler, solvers, depth, term order).
    `ROOT_REWRITE` applies the reducers at the root only.

`CONGPROC`

:   (From `Opening`.)
    This builds a *congproc* given a `congrule` theorem and a general notion of reflexivity in the function `refl`.
    Only `simpLib.threaded_cong_ss` selects `THREADED_CONGPROC`, which reads intermediate results from later antecedents and beta-reduces applied result variables; ordinary congruences keep `CONGPROC`.
    It’s important that `refl` be able to generate reflexivity theorems for multiple relations at once: this allows different relations to appear in the assumptions of `congrule`; the conclusion might want to draw conclusions about equality even as one of the assumptions is about another relation again (as happens in weakening congruences).

    One problem here is that reprocessing of assumptions can unnecessarily descend into terms that have already been processed once.
    For example, in the rule for conditional expressions, we have

        p = p’ ==> (p’ ==> t = t’) ==> (~p’ ==> e = e’) ==>
        (COND p t e = COND p’ t’ e’)

    and the reprocess flag will be set to true for the `~p’` assumption (it’s not just a variable).
    Sure, if negation descends over a disjunction or similar, this is an important thing to do (though the `mk_cond_rewr` could presumably do it too), but if nothing simplifies at the top level, it’s painful to have to descend into `p’` again.
