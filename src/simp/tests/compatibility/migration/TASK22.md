# TASK22 — traversal / derivation caller closure

All bounded clients use the existing explicit extension types. No ordinary
client migration, rebuilding import, reverse reducer adapter, retrospective
source discovery or new public entry point is needed.

| Client/contract | Construction and migrated owner |
| --- | --- |
| Native child-first/argument/observed preparation fixtures | `src/simp/src/selftest.sml` aliases `simpLib`/`Traverse` to extension modules before constructing tracked sets; original assertions retained |
| Focused derivation/lifetime fixtures | `tests/simp-ext/{selftest,tracked,derivation,lifetimes}.sml` construct `simpExtLib` sets and explicitly `TraverseExt.lift` opaque ordinary reducers |
| Generic solver/context/root clients | `tests/traverse-ext/selftest.sml` uses explicit extended data and split reducer/solver contexts; `tests/simp-ext/lifetimes.sml` adds nested/retained closure intersections |
| Configured safe/unsafe/global/looper clients | `tests/simp-ext/{strategies,tactics}.sml`, `APIExamples.sml`: tracked sets, actual proof validations and explicit extension tactics |
| External clasimp consumer | Existing separately scoped TASK25; no edits to the caller-owned worktree in TASK22 |

`prepare_child_first*` snapshots actual installed native/view/bundle controls
at each application, resets them to their declared limits within that scope,
and restores the snapshots using `Portable.finally`. Shared controls remain
shared inside a scope. Nested applications restore the enclosing private
counter, not the original public value. Neither conversion preparation nor
projection extraction replays history or recompiles installed rules.

Policy predicates are abort callbacks, not rewrite candidates. A failing
`keep_abstraction` now receives the same protection as charge/observation:
HOL_ERR cannot disappear into eta fallback or TRY_CONV. Private preparation
retains failure state across wrappers, including its argument-only adapter.
The direct conversion shares one guard between traversal and native ETA, so
late descent-created candidates cannot swallow policy HOL_ERR. The indexed
pretest scopes callback state separately, without resetting counters, charging
or observing; caught nested pretest errors cannot poison an outer derivation.
All scopes restore enclosing failure state on every exit. The traversal and
standalone argument normalizer also keep application-local failure state.

Native candidate dispatch transports policy failure as a completed search
outcome and rethrows outside `tryfind`, never invoking later conversions.
The private configured extractor threads the same abort check into nested
native searches. `TraverseExt.CHILD_FIRST_WITH_ABORT` is an additive driver
hook: its check is inert on success and rethrows a remembered failure before
callbacks, including solver continuations, factories and reducer descent.
Returned congruence/weakener conversions are guarded at invocation too:
all factories may already exist when selected child descent aborts. A policy
HOL_ERR cannot trigger fallback callbacks through FIRSTCQC_CONV. This changes
no ordinary congruence rejection, UNCHANGED or successful callback schedule.
This is needed when a native policy call occurs outside the traversal's own
predicate wrapper. Existing traversal entry points use an inert external
check and retain their own local protection; no existing client must migrate.
Standalone argument normalization also checks before calling user children.
Arbitrary reducer/solver HOL_ERR remains ordinary candidate rejection;
foreign payloads and Interrupt retain their original propagation.

Ordinary `Traverse`, `simpLib`, rewrite/congruence primitives, controls,
registries and loading paths are untouched. New tests are executed from the
separate extension selftest target, without adding ordinary imports. Standard
recipes and persistence are unchanged; their existing later-task scopes are
not new deferrals from TASK22.
