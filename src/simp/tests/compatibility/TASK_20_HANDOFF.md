# TASK20 — explicit configured tactics, strategies and markers

Landing identifier: **TASK20-configured-tactics-v1** (containing commit).
Starting HEAD: `14bab19f7`.
Develop: `cccaa27d7099cbadc886983020cbe745db7793f3`.
Linux/aarch64, Poly/ML 5.9.2, shared `hol.state0`; isolated paired processes
use one GC thread. Initial main checkout was clean. Unrelated nested
`.agent-files` changes are preserved.

## Completion and implementation

**All bounded TASK20 acceptance criteria are satisfied. No blocker remains.**
This is extension tactic/strategy acceptance, not whole-plan performance,
exhaustive TASK21 view migration or TASK22 private derivation restoration.

The extension-owned APIs already existed, but their intersections were not
complete. The implementation fixes these defects without ordinary fallback:

- Non-global `GEN_SIMP_TAC` and its child-first counterpart now bind supplied
  rules once per goal invocation. Looper siblings, recursive passes and solver
  recursion share those installed controls. Saved tactic reuse starts fresh
  supplied allowances; already installed rules keep their live allowances.
  Final solvers receive untagged facts, even when a maker rejects their rewrites.
- New additive `simpMarkerLib.process_taclist_then_bind` separates supplied
  facts from the changing assumption policy. Pretactics and requirements run
  once; only assumption selection recurs. Label lookup still precedes requirement
  construction. Requirements on tactic options themselves are retained, not
  discarded by classification. The existing recursive marker API is unchanged.
- Bound-qualified SF, Split, ExclX and other directives execute as directives,
  not marker-headed rewrite rules. Actual bounded rewrites retain their bounds;
  AC/Cong payloads are not recursively interpreted as directives. Nested
  requirement failures retain their provenance. Abbr/label/NoAsms/IgnAsm options
  work beneath wrappers. NoAsms/IgnAsm apply to bound and unbound global passes.
- Invocation-local removal directly preserves **all** compatible installed
  controls. The former reset-then-repair replay restored only bundle controls,
  ran ambient makers/collectors twice and gave loopers the unrepaired object.
  That second replay is removed. Traversal, solvers and loopers now receive the
  same adjusted object, including spent ambient and bundle controls.
- Installed view matchers, including rejected shapes, are cached immutably in
  extension history. Replay first checks source compatibility and then reuses
  the matcher, rebinding actual counters only when necessary. Already installed
  bundles and attached views emit no recompilation traces during local replay.
  Ordinary-reset replay still resets declared allowances and preserves sharing.
- One global invocation owns one looper budget across conclusion fixpoint
  reentry and sibling branches. Applying the saved tactic again resets that
  invocation budget. Traversal limits remain independently enforced as before.
- Excluded additions return the exact input at the public `++` boundary before
  compilation. The unchanged TASK19 physical-identity assertion exposed that
  relying on the deeper constructor-pattern return was not robust after these
  compiler/layout changes; the explicit outer guard preserves the contract.

Safe mode still selects **final** safe solvers only; conditional rewriting
continues to use unsafe solvers. Configured/live depth, custom order, root
rewriting/rebuilding, implication-premise handling, assumptions, counted passes,
proof reconstruction and subgoal order remain covered and passing.

No ordinary `simpLib`, generic `markerLib`, postkernel service, split registry,
public shared-control identity, or external consumer changed. `simpLib.sml/.sig`
and `markerLib.sml/.sig` remain byte-identical to develop. In particular ordinary
simpLib SHA256s remain `ee324439ac66cd14858d6ea5dc45a867d44fa6762298f1cf7df45b13aed6c3cd`
and `d1979668da105341e6e97e900848a2d382eaac3a50650c89bbdeae8ee3689666`.

## Tests and source-tied evidence

[`evidence/task20/validation.json`](evidence/task20/validation.json) seals the
actual final compiled sources, fixtures, Python drivers and tool/heap hashes,
commands, exit statuses and retained receipt paths. All final commands exit 0:

| Command | Result / evidence |
| --- | --- |
| `bin/build -t --seq=tools/sequences/upto-parallel` | Final complete routine sanity build; `routine.log.gz` |
| `python3 src/simp/tests/compatibility/run_prior_native.py --output /tmp/task20-final/native` | 14 receipts, source/product seals; explicit integrated `Holmake --no-project --no-cache --holstate=... -j1 -C src/simp/src HOLSELFTESTLEVEL=1 all`, actual native/traversal/exclusion/marker/registration/replay/fresh-load/persistence launchers; `native/` |
| `python3 src/simp/tests/compatibility/run_paired.py --candidate HEAD --candidate-signature pass --candidate-behavior baseline --prior-contracts --public-contracts --staging-contracts --negative-controls --output /tmp/task20-final/paired` | 44 receipts: both original reproducers, public clients, frozen 73/47/929/limit suites, unchanged strict staging matrix and fail-closed controls; `paired/` |
| `python3 src/simp/tests/tactics/run_behavior.py --output /tmp/task20-final/behavior` | 307 supplemental ordinary checks / 116 executed validations per side; `behavior/` |
| `coverage_ledger.py`; `verify_evidence.py`; `audit_task14.py` | 2,153 original source-tied cases, 37 immutable inputs, inert getters/shared-control/cached-matcher structural gate |
| `tools/h4pedant/h4pedant src/simp/tests/simp-ext`; `tools/h4pedant/h4pedant --nolinelen src/simp/src`; `git diff --check` | Pass |

The new maintained suites execute through `tests/simp-ext/check`, integrated at
selftest level 1, not just `.uo` generation:

- `strategies.sml`: **186 checks / 63 executed kernel-proof validations**.
  Safe/unsafe final and condition selection, contextual recursion, replacement/
  removal/order, live/default depth, explicit depth, term order, looper limits,
  exact arbitrary exceptions, invalid solver conclusions/hypotheses, counted
  global passes, root rebuilding, implication premises and child-first order.
- `tactics.sml`: **58 checks / 18 executed kernel-proof validations**.
  Invocation-wide Once across ordered looper siblings in both traversal modes,
  saved reuse, global looper budget reentry, plain solver facts, nested options/
  SF/Split/requirements, generic marker inertness and unchanged registrations.
  Local replay intersects an exhausted ambient rule, partially spent/exhausted
  bundle and attached view. Old saved conversions and a looper observe actual
  shared exhaustion. Exact maker/collector schedules are 1/3 and 2/6 for the
  two cases; bundle/view recompilation trace count is zero.

Tests compare ordered goals and complete theorem hypotheses, and actually call
returned validations with kernel-derived residual proofs. The original native
`selftest.sml` is unchanged (**642 checks**); existing separate extension suites
retain **88 focused + 174 tracked + 159 exclusion checks**. The coverage map is
in [`../simp-ext/README.md`](../simp-ext/README.md).

The paired runner selects committed starting HEAD. Its ordinary sources are
identical to final sources; this is legacy evidence, **not** a claimed test of
the extension edit. The final native driver seals and executes actual working-
tree extension sources and both new suites. Ordinary saved tactic, staging and
fresh-load fixtures are unchanged and pass. Generic markers forward extension
markers inertly and acquire no new registrations.

## Evidence corrections and scope

The first native driver attempt completed every process successfully but
correctly failed its product seal: unchanged native selftest re-exports
`scratchTheory`, whose generated theory hash differed between integrated and
direct execution. These are outputs, not imported inputs. The driver now
excludes only `src/simp/src/.hol/objs/scratchTheory.{sml,sig,dat}` from that
product seal. Every `.uo/.ui`, other theory product, source, tool and exact native
stream remains sealed. A **fresh entire driver run** passes. The rejected attempt
is recorded in `native-seal-attempt.json`; it is not relabeled successful.

Exploratory fixture corrections preserved real behavior: ALLGOALS evaluates
later branches first while retaining output order; a Once allowance covers one
redex, not both occurrences in a tautology; ReqD around a content directive
still enforces decrease. The additive option decoder initially dropped ReqD
on options; review caught this and added four explicit non-global regressions.
Final validation follows all production/fixture corrections.

## Files, migration and cleanup

Production: `simpExtLib.{sig,sml}`, `simpMarkerLib.{sig,sml}` and source Holmake
cleanup list. Tests: new `strategies.sml`/`tactics.sml`, suite Holmakefile/README,
compiled `APIExamples.sml`, and the narrow native-driver output-sealing fix.
Docs: 24 branch-only strategy/tactic/marker help files move from `simpLib.*`
to `simpExtLib.*`; immediate links/types/examples use `TraverseExt` and explicit
tracked recipes. Ordinary Excl's literal net-deletion contract stays intact.
Migration rows S1/M1/A1 record invocation binding and replay decisions. Ordinary
callers require no migration. This handoff/evidence and actual progress status
complete the task.

No new out-of-scope repair or blocker remains. TASK21 is next, with its existing
source/view/bundle scope; TASK22 retains private derivation/interrupt restoration
and TASK23 retains persistence lifecycle work. None substitutes for unfinished
TASK20 work.

Task-owned scratch outputs, new launchers/object/dependency products and copied
receipt directories are removed after retaining compact unique evidence. No
copied build tree, generated executable or heap is committed; unrelated and
pre-existing products/caches remain untouched.
