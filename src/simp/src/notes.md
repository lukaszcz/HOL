# Note on the Simplifier Code

## Persistent split rules (explicit opt-in)

Ordinary `simpLib` and `splitLib` loading and split-rule queries claim no
`split` attribute or theorem-set namespace. Local `Split`/`add_split` and
TypeBase-driven `split_ss` work without opt-in; persistent queries return
`[]` until library-owned registration is enabled.

A split-bearing script explicitly includes `splitPersistLib` in `Libs`
before its `[split]` declarations and calls
`Theory.add_ML_dependency "splitPersistLib"`. The former enables the script;
the latter initializes fresh imports before decoding and ancestry replay.
Record this dependency on the earliest split-bearing theory: a child's
ML dependencies cannot initialize its already-loading parents.
An explicit loader prelude calling `splitLib.enable_split_attribute ()`
before loading the whole graph is also supported.

`splitLib.exclude_split "Thy.Name"` persistently retracts an ancestor's named
rule; an unqualified name resolves in the writing theory. Exported REMOVE
keys are already resolved and cannot delete a descendant's same-named rule.
This differs from local `del_split` or `ExclX` exclusions. The theorem stays
in DB. Both the attribute and exporter must remain library-owned; explicit
initialization/removal rejects foreign ownership instead of replacing it.

Ownership/data follow `Context.restore`, but the ML loader is process-global.
After rewind to before opt-in, explicitly call the initialization API again;
merely loading an already-loaded module may not execute its body. Arrange
registration as serialized theory initialization, not during concurrent
proofs. Arbitrary late/current-segment replay is not the supported contract.
See `../compatibility/SPLIT_PERSISTENCE.md` for runnable fresh-process tests.

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

For all-`REDUCER` inputs, `TRAVERSE` uses a private original five-field
state: reducer contexts, relation information and hypothesis free variables.
Mixed contextual/configured reducers retain the generalized legacy schedule.
The generalized state stores generic `context_thms` only when a configured
subgoaler or unsafe solver can read them; otherwise that list stays empty.
`add_context` still delivers every batch to the reducers and preserves its
hypotheses' free variables, regardless of generic fact storage.
`TRAVERSE_WITH_CONTEXT` splits its initial theorems: `reducer_context` goes
through reducer collectors, while `solver_context` only contributes generic
facts (when readable) and hypothesis free variables for binder capture.
Reducer batches prepend generic facts; separated solver batches append them.
This lets a caller show solvers the source of an already-installed rule
without installing it twice or refreshing a bounded rewrite.

## Side conditions

The engine solver (`ctxt_solver` in `Traverse`) proves a condition `c` by running the subgoaler (or recursive traversal, if none is set) to get `|- c = c'`, then proving `c` from `c' = T` or from the first unsafe solver that proves `c'`.
Only `HOL_ERR` means a solver is inapplicable; on failure the traversal limit is restored.
With neither subgoaler nor solvers, the original `EQT_ELIM` path is taken.
`traverseconfig_for_ss` always supplies the unsafe list, even under a safe tactic; safe solvers are only ever final solvers in `GEN_SIMP_TAC`.

Native rule preparation produces direct legacy and configured runners
sharing one matcher and the actual bound reference. Each net entry holds
an original curried conversion and one cold companion containing the
configured runner and quota metadata. Collector-created rules use this same
insertion path; source handles alone do not inventory all bounded rules.
Legacy candidate application selects only the original conversion.

Depth and term order are options in `traverse_config`. On configured paths,
native rewrites receive the depth option unchanged through `CONFIG_REDUCER`
and `COND_REWR_CONV_WITH_CONFIG`. With `NONE`, each candidate-depth check
reads the current `Cond_rewr.stack_limit`; a failing user conversion can
change that default before the next candidate in the same net lookup.
An explicit `SOME n` uses `n` without reading or updating that global.

Older `CONTEXT_REDUCER` clients still receive an integer: an unset depth is
resolved when their reducer is applied. `COND_REWR_CONV_WITH_CONTEXT` adapts
an explicit integer to `SOME n`; it is not the live-default native path.
The direct legacy runner reads the live stack limit at its candidate check
and uses `Cond_rewr.ac_term_ord`. Configured term order defaults to that same
function at traversal entry.
Settings are passed explicitly, not installed by temporarily changing globals.
A separate nested invocation uses its own configuration.

## Exclusion names

Every `Excl` name and `-*` retain develop's dots-only parser and ancestry
check, with no namespace interpretation or strategy fallback. Unmatched
names silently record develop's rule deletion, including history entries
that are reparsed on replay.

Extended exclusions use the distinct `ExclX` marker. Its `rule:` namespace
accepts kernel `Thy$Name` spellings and non-ancestor theory names, keeping
its resolved pattern on replay. Bare `ExclX` names still use the strict
parser and prefer rewrites/decision procedures, falling back to strategy
targets only when neither matches. Multiple strategy kinds are ambiguous;
`looper:`, `solver:`, `split:` and `case:` select them explicitly. Every
unmatched `ExclX` name, including a bare name, is an error at processing,
not construction. Bounded `ExclX` remains an invocation control rather
than bounded deletion; requirement-wrapper precedence is unchanged.

Split/case ExclX targets record an incremental `EXCLUDE_LOOPER_EVENT` with
one resolved display name. It suppresses later local additions and ambient
split/TypeBase rules, including after fragment removal or Context.restore;
replay does not resolve the target again. Local split deletion events
precede this suppression event. Repetition is idempotent. Ordinary looper
and solver deletions remain point-in-history removals, as do strict and
resolved rule deletions: a later addition can reinstall those targets.

## Prepared global rewrites

The old simplification tactics retain develop's marker processing and pass
schedule for strategy-free invocations; strategy-bearing calls use the
extended engines. This choice is made on the goal, not when a reusable
tactic is constructed. Schedule compatibility does not imply a baseline-sized
state, absence of extension bookkeeping or a measured speedup. Explicit
`GEN_GLOBAL_SIMP_TAC` calls always select counted prepared passes.

`GEN_GLOBAL_SIMP_TAC` decodes its ordinary theorem arguments once, without adding them to the simpset history.
Each traversal compiles them with its own marker-adjusted `mk_rewrs`, so bounded rewrites share one invocation-wide control; their source theorems go to the solver context.
`SIMP_CONV`, `GEN_SIMP_TAC`, `TRAVERSE` and `ROOT_REWRITE` do not use this path.

## Important Functions

`SIMP_QCONV`

:   (From `simpLib`.)
    Selects the trusted original-ABI projection when conversion settings
    are absent and every decision procedure is an ordinary `REDUCER`.
    Otherwise it retains the configured projection and appropriate engine.
    Public `traversedata_for_ss` unconditionally returns the legacy
    projection, with a native `REDUCER` and unchanged supplied decision
    procedures. It carries the relation, traversal rules and limit, but
    omits simpset-specific traversal configuration, even for configured
    inputs. `legacy_traversedata_for_ss` is the optional dispatch API:
    after pure eligibility inspection it shares that same default builder.
    Neither extraction invokes collectors or recompiles installed rules.

    `xtraversedata_for_ss` instead uses the configured builder, returning
    a native `CONFIG_REDUCER` paired with the simpset's configuration.
    Branch-only consumers needing configured reducer data alone must use
    `#1 (xtraversedata_for_ss ss)`. Both projections share the actual
    installed bounded controls; extraction does not reset remaining uses.

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
    `ROOT_REWRITE` applies the reducers at the root only. Entry selection
    does not propagate to recursive conversions or side-condition proving:
    these still use full traversal, including relation-changing recursion.

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
