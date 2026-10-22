# TASK20 — explicit configured tactics, strategies and markers

Final landing identifier: **TASK20-configured-tactics-v2** (containing commit).
Repair starting HEAD: `510641058` (the initial TASK20 implementation).
Predecessor: `14bab19f7` (TASK19).
Develop: `cccaa27d7099cbadc886983020cbe745db7793f3`.
Linux/aarch64, Poly/ML 5.9.2, shared `hol.state0`; isolated paired processes
use one GC thread. Initial production tree was clean; the supplied untracked
`evidence/task20/review/` and unrelated nested `.agent-files` changes were
preserved.

## Status and review correction

**All bounded TASK20 acceptance criteria now pass, including both reproduced
review failures. No TASK20 blocker remains.** The former completion statement
at `510641058` was premature: its tests missed the Abbr/FRAG exception-order
intersection and multiply-bounded genuine rewrites. The old top-level
`evidence/task20/validation.json` and logs describe that implementation, not
final acceptance. The supplied red reproducer is retained unchanged under
[`evidence/task20/review/`](evidence/task20/review/).

Final acceptance is tied to the actual repaired sources in
[`evidence/task20/repair/validation.json`](evidence/task20/repair/validation.json).
This is extension tactic/strategy acceptance, not whole-plan performance,
TASK21 view migration or TASK22 private derivation restoration.

## Implementation and API decisions

The initial implementation established these explicit extension-only paths:

- Non-global `GEN_SIMP_TAC` and its child-first counterpart bind supplied rules
  once per goal invocation. Looper siblings, recursive passes and solver
  recursion share those installed controls. Saved tactic reuse starts fresh
  supplied allowances; installed rules keep their live allowances. Final
  solvers receive untagged facts even when a maker rejects their rewrites.
- `simpMarkerLib.process_taclist_then_bind` separates supplied facts from
  changing assumption selection. Pretactics and requirements run once; only
  the assumption policy recurs. Requirements on tactic options are retained.
- Bound-qualified SF, Split, ExclX and other content directives execute as
  directives, not marker-headed rewrites. AC/Cong payloads are not recursively
  interpreted as directives. Wrapped NoAsms/IgnAsm apply to bound and unbound
  global passes; Abbr/label options and requirement failures retain provenance.
- Invocation-local removal preserves all compatible installed controls in one
  replay, including ambient quotas and prepared bundles. Traversal, solvers
  and loopers receive the same adjusted object. Cached installed view matchers
  (including rejected shapes) avoid recompilation during replay; source
  compatibility is checked before reusing matchers/rebinding counters.
  Ordinary-reset replay still resets declared allowances.
- A global invocation shares one looper budget across conclusion/fixpoint
  reentry and siblings. Reapplying a saved tactic resets that invocation
  budget. Excluded additions return the exact input before compilation.

The repair closes the two review failures:

1. `process_taclist_then_bind` now defers its binding callback until the Abbr
   pretactics succeed, rather than evaluating it while constructing `THEN`.
   Missing Abbr therefore raises `markerLib.UNABBREV_TAC` before FRAG lookup
   or rule compilation. Label lookup retains its earlier option-decoding
   stage. Requirement wrapping remains around the complete continuation.
   Binding still happens once, not again at every recursive assumption scan.
2. `process_tags0` looks through all bound wrappers solely to decide whether
   their payload is a content directive. A genuine rewrite is returned
   verbatim, including all bound hypotheses, so later `DEST_BOUNDED` chooses
   the original allowance. `Once (Ntimes rule 2)` retains bound **1**, not 2.
   Nested content directives still execute, and requirements remain checks
   rather than disappearing during this classification.

Safe mode continues to select final safe solvers only; conditional rewriting
uses unsafe solvers. Configured/live depth, custom order, root rebuilding,
implication-premise handling, assumptions, counted passes, proof reconstruction
and subgoal order remain covered.

No ordinary `simpLib`, generic `markerLib`, postkernel service, split registry,
shared public-control identity or external consumer changed. Ordinary
`simpLib.sml/.sig` and `markerLib.sml/.sig` remain byte-identical to develop;
final hashes are recorded in the repair manifest. There is no fallback into
ordinary simpsets or hidden promotion.

## Maintained tests

`tests/simp-ext/check` executes these suites at selftest level 1, outside
ordinary selftest imports:

- `strategies.sml`: **186 checks / 63 executed kernel-proof validations**.
  Safe/unsafe final and condition selection; recursion; replacement/removal/
  order; live and explicit depth; term order; looper limits and exceptions;
  invalid solver conclusions/hypotheses; counted globals, root rebuilding,
  implication premises and child-first order.
- `tactics.sml`: now **88 checks / 18 executed kernel-proof validations**
  (formerly 58). Original assertions are retained. New checks cover repeated
  saved parent/child/configured-alias Abbr-before-FRAG failures, later FRAG
  failure without a failing pretactic, earlier label lookup, zero callback
  executions after a failed pretactic, and exactly one after success.
  Four multiply-bounded real-rule forms retain their complete theorems and
  selected allowances; installed conversions consume exactly that quota and
  stay exhausted. SF and Split tests now exercise multiple bound wrappers.
  Existing invocation-wide Once, generic marker inertness/registration,
  plain solver facts and local bundle/view/ambient-sharing assertions pass.
  Local replay maker/collector schedules remain 1/3 and 2/6, with zero
  bundle/view recompilation traces.

Ordered goals and complete theorem hypotheses are compared; returned tactic
validations are actually called with kernel-derived residual proofs. The
unchanged native fixture retains **642 checks**, and existing extension suites
retain **88 focused + 174 tracked + 159 exclusion checks**. The original
coverage ledger still verifies **2,153 source-tied cases**. See the additive
coverage map in [`../simp-ext/README.md`](../simp-ext/README.md).

## Fresh final validation

All commands below exit **0**. The repair manifest records exact source/input,
command, runtime/tool/heap hashes, exit statuses, receipt hashes and paths.

| Command | Result / evidence under `evidence/task20/repair/` |
| --- | --- |
| Fresh Holmake-built copy of supplied review `selftest.sml`, exact procedure in review README | Build/run 0; all 3 assertions pass; selected bound 1 before/after; `review-build.log.gz`, `review.log.gz` |
| `bin/build -t --seq=tools/sequences/upto-parallel` | Complete routine sanity build; `routine.log.gz` |
| `python3 -B src/simp/tests/compatibility/run_prior_native.py --output /tmp/task20-repair/native` | 14 receipts; integrated `Holmake --no-project --no-cache --holstate=... -j1 -C src/simp/src HOLSELFTESTLEVEL=1 all`, all extension suites, actual native/traversal/exclusion/marker/registration/replay/fresh-load launchers, fresh split exports and heap lifecycle; `native/manifest.json.gz` |
| `python3 -B src/simp/tests/compatibility/run_paired.py --candidate HEAD --candidate-signature pass --candidate-behavior baseline --prior-contracts --public-contracts --staging-contracts --negative-controls --output /tmp/task20-repair/paired` | 44 receipts; reproducers, public clients, frozen 73/47/929/limit suites, strict unchanged staging matrix and fail-closed negative controls; `paired/manifest.json.gz` |
| `python3 -B src/simp/tests/tactics/run_behavior.py --output /tmp/task20-repair/behavior` | 307 ordinary checks / 116 executed validations per side; `behavior/manifest.json.gz` |
| `coverage_ledger.py`; `verify_evidence.py`; `audit_task14.py` | 2,153 original cases; 37 immutable inputs; inert getters/shared-control/cached-matcher structural gate |
| `tools/h4pedant/h4pedant src/simp/tests/simp-ext`; `tools/h4pedant/h4pedant --nolinelen src/simp/src`; `git diff --check` | Pass |

The maintained new staging assertion also failed before repair; its build
exited 0 and execution exited 1 (`red-build.log.gz`, `red-tactics.log.gz`).
The supplied review output independently reproduces both failures at starting
HEAD. No failed attempt is counted as final acceptance.

The paired runner selects starting committed HEAD `510641058`, whose ordinary
sources are identical to final sources. That is ordinary compatibility evidence,
not claimed execution of the extension repair. The native driver seals and
executes the actual working-tree extension sources, including the expanded
suite. Saved ordinary tactic/staging and fresh-load cleanup fixtures are
unchanged and passing. No generic registration was added.

## Files, documentation and cleanup

The original implementation's extension signatures, docfiles, API examples,
recipe links and S1/M1/A1 migration rows remain in place. Ordinary clients need
no migration. The repair changes `simpExtLib.sml`, `simpMarkerLib.{sml,sig}`,
`tactics.sml`, its coverage README and the marker/tactic migration rows to pin
the corrected bound and pretactic contracts. This handoff, preserved review
inputs and compact source-tied repair evidence close the task.

No work was deferred from TASK20. TASK21, TASK22 and TASK23 retain their
pre-existing source/view, private derivation/interrupt and persistence scopes;
none substitutes for unfinished work here. TASK21 is now unblocked.

Private review/build trees and task-created scratch evidence are removed after
recording compact unique receipts. Runners remove their copied source trees
and temporary persistence heaps. No generated executable, copied build tree or
heap is committed. Pre-existing local build products, unrelated temporary files
and unrelated nested-repository changes are left alone.
