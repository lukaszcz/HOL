# Focused simpExtLib contracts (TASK_10)

Run from the repository root, once `simpExtLib` is available:

```
bin/Holmake --holstate="$PWD/bin/hol.state0" --no-project --no-cache \
  -C src/simp/tests/simp-ext -j1 check
```

`check` builds **and executes** `selftest.exe`, `tracked.exe`,
`exclusions.exe`, `strategies.exe` and `tactics.exe`. Building
`.uo` files alone is not validation. The production `simp-ext` target runs it
at `HOLSELFTESTLEVEL=1`. Expected Poly/ML type-error diagnostics
from `negative/*.ML` are normal successful test output.

## Construction and compiled clients

`../../src/pureSimpsExt.{sig,sml}` and
`../../src/boolSimpsExt.{sig,sml}` mechanically reproduce the ordinary
recipes using extension constructors, in the original order. The full BOOL
catalog is available, including optional ETA, ordinary versus explicitly
threaded congruences, conversions, and named fragments. Inputs are immutable
theorems/conversions; no ordinary fragment/set is promoted, inspected, or
reconstructed via `ssfrags_of`. BOOL retains the ordered recipe
`PURE -> BOOL -> NOT -> CONG -> UNWIND`; ETA is opt-in.

`APIExamples.sml` elaborates clients against the actual sealed production
modules. It checks the complete recipe catalog, explicit ordinary-reducer
lifting, configured reducers, both **extension-typed** projections, argument
preparation, bundle installation, and immutable AC/TypeBase/relational/threaded
factory inputs, plus explicit public congruence-fragment lifting and typed
congruence construction. No fake implementation or legacy projection adapter
is used.

## Semantic checks

- BOOL beta/boolean rewrites and contextual COND congruences; opt-in ETA and
  logical-binder exclusions.
- Saved live conditional depth observes changes to the shared
  `Cond_rewr.stack_limit` in both directions; explicit zero/40 overrides it
  without mutating it. Recursive conditional proofs compare conclusions and
  complete hypothesis sets; recursive side-condition rewrites are not tracked.
- Explicit opaque lifting preserves collector/application payload identity and
  relation/reflexivity callbacks, creates no source inventory, and distinguishes
  construction-once default collection from per-application configured refresh.
- Late projection extraction after exhaustion, in both orders; original/view
  quota sharing, source identity/order, partial/exhausted preserving replay,
  explicit reset replay, preserving filtering and source suspension. No getter
  compilation, maker callback or compilation trace is allowed.
- Prepared bundle combination retains bindings and partially spent actual
  controls; duplicate bindings fail rather than refreshing allowances.
- Parent/child-first overlapping rewrites, charging, argument-only root
  preservation, reusable private normalization with exhausted native quotas,
  and restoration on success and observer exceptions with exact payloads.
- Same-name ordinary/extension typed registries remain independent. Saved SF
  tactics resolve late, follow replacement/Context rewind, and fail when absent.
  SF's shared string-marker syntax does not permit cross-registry fallback.
- One Trace listener and one tracking extent observe both engines. Nesting in
  both directions isolates inner reports and restores outer tracking, including
  a foreign exception leaving the nested extent.
- Eight real Poly/ML negative clients reject reducer, set-consumer, fragment
  installation and compiled congruence-set crossings in **both directions**. The harness follows
  `../traverse-ext`: only `Fail "Static Errors"` counts as rejection; accepted
  code, missing files and other exceptions fail closed.

Closed rewrite fixtures check both sides of each conversion theorem and empty
hypotheses, not just the resulting term. Open conditional fixtures compare the
complete expected theorem/hypothesis set. Saved-tactic checks run through
`VALID`. Context snapshots, listeners and the global depth control are restored.

## Additive provenance

These tests add separate-type assertions; they do not move or weaken original
cases or alter the sealed TASK_06 coverage ledger. Comment anchors map to the
existing original contracts as follows:

| New block | Original semantic provenance |
| --- | --- |
| `The standard recipe order` | ordinary PURE/BOOL construction recipes |
| `A saved NONE stays live` | main selftest configured depth surface; TraverseExt live-depth contracts |
| `Lift construction and projection` | TraverseExt lifting and construction/reuse contracts |
| `Exhaust before extracting` / `Getter/source extraction` | main selftest compiled projection/source lifetime contracts |
| `Prepared bundles retain` | main selftest `combined_bundle_fixture` |
| `Child-first changes overlap` | main selftest `prepared_normalization_fixture`, observer/child-first contracts |
| `Two typed Context slots` | main selftest R4 late FRAG lookup and Context restoration |
| `One tracking slot` | TASK_08 singleton tracking/control ownership contract |

## Tracked compiler gate (TASK_14)

`tracked.sml` adds focused installation, identity and actual-control tests:
projection extraction before use, after partial use and after exhaustion in
both directions; duplicate slots/events, AC components and shared conjuncts;
persistent filtering and preserving replay; cached matcher rebinding versus
explicit reset; compilation/collector order and failure staging; inert getters
and explicit directive preparation; incompatible changed-maker statements;
private alias allowances and exceptional/nested restoration. Proof checks
compare complete expected conclusions and hypothesis sets.

The inventory getter `rewrite_sources` now rejects directives. First call
`prepare_rewrite_arguments` explicitly and inspect its returned set/rules.
See [TASK14 migration](../compatibility/migration/TASK14.md) for contracts and
[handoff](../compatibility/TASK_14_HANDOFF.md) for final evidence. This is
bounded tracked-compiler acceptance, not exhaustive TASK_21 view/bundle
validation, TASK_26 test migration or performance acceptance.

## Exclusion and replay gate (TASK_19)

`exclusions.sml` adds 159 checks on explicitly tracked objects. Both default
and configured projections are extracted/used in both orders. Complete
conclusions and hypothesis sets, not just endpoints, are compared.

| New block | Preserved original coverage / additional intersection |
| --- | --- |
| `A deleted conjunct` | native source/view deletion and partial-quota replay; literal/resolved deletion plus preserving removal/filtering of mixed native/prepared sources; surviving identity/order and actual sharing |
| `Failed extended resolution` | native namespace resolution and unmatched literal history; pending duplicate failures must leave old inventory/control state intact |
| `Strict and resolved histories` | native strict-history theory rewind; preserving reconstruction fails/succeeds under the same contract without refreshing live/exhausted controls |
| `Prohibition is distinct` | native named-fragment removal/strategy replay; force-add, duplicates, no-op identity, exact maker/opaque-collector ordering, limits and retained prohibition |
| `Namespace separation` | native strategy namespace/split suppression; ordinary loopers colliding with split/case displays survive suppression, later additions and preserving replay |

No original assertion is moved or relaxed. `src/selftest.sml` still runs its
642 source-tied native checks, including parser/warning/ambiguity contracts,
strategy targets, local/ambient split suppression, mixed views and failures.
The unchanged coverage ledger verifies those assertions and the 929-check
legacy exclusion suite. Full dependent-view invalidation remains TASK_21;
persistent split ownership/lifecycle remains TASK_23.

Only extension-owned `looper_tac` changes: split/case suppression applies to
split loopers, not unrelated ordinary names. Resolution, private history order,
strict reparsing versus resolved replay, and ordinary-reset versus explicit
preserving-control replay stay unchanged. There is no legacy-history identity
inference, new ordinary import, or ordinary representation change. See the
[TASK19 handoff](../compatibility/TASK_19_HANDOFF.md) for source-tied evidence.

## Configured tactics and strategies (TASK_20)

`strategies.sml` adds **186 checks / 63 executed validations**;
`tactics.sml` adds **58 checks / 18 executed validations**. All proofs are
kernel-derived; residual goals are actually proved, returned validations
called, and complete hypotheses and ordered goals compared.

| New coverage | Original provenance / added intersection |
| --- | --- |
| Final/condition solvers | Native safe/unsafe pipeline; list replacement/removal/order, invalid conclusions/hypotheses, alpha-equivalent contexts, recursion and exact exception payloads |
| Configured controls | Native live depth, custom order and root rewrite tests; saved conversions/tactics, shared default versus explicit depth |
| Loopers | Native replacement/round-limit tests; zero/one/multiple/unlimited rounds, UNCHANGED/failure/exception behavior, changed subgoal restart and saved reuse |
| Counted globals | Native mutual-assumption/fixpoint/root/implication groups; ordered branching and real reconstruction, counted unchanged rotations, conclusion fixpoint reentry and one invocation-wide looper budget |
| Child-first passes | Native child-first overlap; explicit traversal order and configured global reconstruction (private derivation restoration remains TASK_22) |
| Supplied invocation binding | Once rules across looper siblings, both traversal policies and saved reuse; final solvers receive untagged facts even when a maker drops their rewrites |
| Nested directives | Requirement/bound-qualified SF and Split execute; ReqD failures retain provenance; wrapped assumption policy, label and abbreviation options, including non-global ReqD failure retention |
| Bound local replay | Native `bound_global_fixture`; independent spent ambient quota plus partially spent/exhausted installed bundle and attached view, exact maker/collector schedule, zero bundle/view recompilation traces, same adjusted object observed by loopers and old saved conversions |
| Generic isolation | Generic classifier/tactic forwards extension markers inertly, no new split set/attribute registrations |

The original 642 native assertions and ordinary saved tactic/staging/load
fixtures remain unchanged. No fallback promotion or ordinary API is involved.
Local replay preserves all installed controls directly, rather than resetting
then repairing only the bundle via a second history replay. Installed view
matchers (including rejected shapes) are cached immutably in extension history;
replay checks source compatibility and rebinds only actual counters. Explicit
ordinary-reset replay still refreshes declared allowances. A public excluded
addition returns its exact input before entering compilation.

`APIExamples.sml` compiles explicit strategy, global, child-first and bound
clients. Branch-only help examples now use `simpExtLib`/`TraverseExt` and tracked
recipes; ordinary callers require no migration. See the
[TASK20 handoff](../compatibility/TASK_20_HANDOFF.md) for validation/evidence.
