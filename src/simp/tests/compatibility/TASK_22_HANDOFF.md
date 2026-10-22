# TASK22 — child-first derivation and solver/context lifetimes

Landing identifier: **TASK22-child-first-lifetimes-v3** (containing commit).
Starting HEAD: `2a1f2f26f956b22d8fabed8c5fbf3f9abbb9a825`.
Develop: `cccaa27d7099cbadc886983020cbe745db7793f3`.
Linux/aarch64, Poly/ML 5.9.2, configured `hol.state0`.
Initially only supplied untracked `evidence/task22/review2/` in the main tree;
unrelated nested `.agent-files` changes were preserved.

**All bounded TASK22 acceptance criteria pass. No TASK22 blocker remains.**
The v1/v2 completion claims missed callback staging: retaining the original
exception for eventual rethrow did not stop fallback conversion callbacks.
Their manifests are historical, not current acceptance. Supplied red evidence
is preserved unchanged in `evidence/task22/{review,review2}/`.
Current acceptance is [dispatch/validation.json](evidence/task22/dispatch/validation.json).

## Repair and API/control decisions

- Native child-first dispatch transports a policy exception as a completed
  search result and releases it **outside** `Lib.tryfind`. Neither a failing
  nor a successful later candidate can run after that abort. Ordinary
  conversion HOL_ERR/foreign rejection still tries subsequent candidates;
  ordinary Interrupt still propagates immediately. Parent-first search is
  unchanged. No generic `Lib`, conversion or kernel exception behavior changed.
- An inner search boundary alone is insufficient. Recursive conversions,
  conditional rewrites and lifted reducers can encounter late ETA inside an
  enclosing search or solver pipeline. The private configured extractor now
  threads the owner's same application-local abort check into native searches.
- Additive `TraverseExt.CHILD_FIRST_WITH_ABORT` lets that owner supply its
  inert-on-success check, independent of charging and observation. Traversal
  checks before solver/subgoaler continuations, factories, reducers, context
  descent and tracing. Existing entry points retain local protection and use
  an inert external check; no existing client must migrate. No successful
  policy/charge/observer callback was added or rescheduled.
- Standalone `NORMALIZE_ARGUMENTS` also checks local abort state before
  argument descent or user-child invocation; swallowed policy HOL_ERR cannot
  invoke a child before final rethrow.
- All existing preparation/pretest scopes remain application-local and
  reentrant. Fresh declared quota scopes and `Portable.finally` restoration
  are unchanged. Nested success/HOL_ERR/foreign/Interrupt restores enclosing
  private counters and abort state. Prepared derivation neither spends nor
  depends on caller allowances; direct conversion still spends actual caller
  quotas and never refills them on failure.

Only extension production sources/signatures changed. Ordinary `Traverse`,
`simpLib`, `Opening`, `Travrules` and `congLib` remain byte-identical to pinned
Develop. There is no reverse adapter, retrospective promotion, global cache,
new shared control, registration or persistence change. Caller ownership and
new driver-hook decisions are in [migration/TASK22.md](migration/TASK22.md).

## Maintained coverage

`tests/simp-ext/derivation.sml` executes **1,392 checks**: all 1,116 prior
assertions plus **276** new checks. `lifetimes.sml` executes **63 checks**:
all 60 prior assertions plus three explicit child-callback staging checks.
All eight focused launchers run through normal `check` and selftest level 1.

New intersections exercise all four paths (direct, prepared normalize,
observed normalize and prepared arguments), exact HOL_ERR provenance/payload,
foreign payload identity and the shared Interrupt constructor:

- Repeated descent-created native ETA aborts with failing AND successful
  matching fallback conversions; zero callbacks after abort, one policy abort,
  inert construction, saved recovery and complete theorem/hypothesis checks.
- Ordinary conversion errors still execute both fallback callbacks, while
  ordinary Interrupt executes neither. Success callback order is asserted.
- Nested native conversion, conditional rewrite and opaque reducer recursion;
  no enclosing fallback, later reducer, unsafe-solver continuation or observer
  after abort; saved conversions recover. These tests exposed and close the
  enclosing-search/solver-continuation holes, not merely the original sibling
  fallback reproducer.
- Standalone argument normalization never invokes the supplied child after
  its policy abort, including HOL_ERR swallowed by eta combinators.

Retained assertions cover private native/bundle/view/alias/conjunct/composed
quotas, exhaustion, nested scopes, unchanged terms, failed side conditions,
exact charge/observer/collector counts, opaque reducer lifting, saved contexts
and generic recurse lifetimes. Retained suites pass: **642 native**, **131
TraverseExt**, and **88 focused + 174 tracked + 159 exclusion + 186 strategy +
88 tactic + 407 source/view/bundle** checks, with **63 + 18 real tactic proof
validations**. These retain live default depth, custom order, solver safety,
proof validation, counted global passes, loop limits, congruence-selected
policy/descent and construction/reuse behavior. The immutable legacy streams
remain 73 original / 47 traversal / 929 exclusion plus limits; the ledger
verifies **2,153 source-tied cases**. No assertion was removed or weakened.

## Fresh validation

Exact commands, exits, source/input/runtime/tool/heap hashes, wrapper, logs
and receipt seals are in `evidence/task22/dispatch/validation.json`.
All acceptance commands exit **0**:

| Command (drivers under `tests/compatibility/`, Python with `-B`) | Evidence under `evidence/task22/dispatch/` |
| --- | --- |
| `bin/Holmake --holstate="$PWD/bin/hol.state0" --no-project --no-cache -C src/simp/tests/simp-ext -j1 check` | Eight executed launchers; `focused.log.gz` |
| `bin/build -t --seq=tools/sequences/upto-parallel` | Complete routine sanity build; `routine.log.gz` |
| `run_prior_native.py --output /tmp/task22-dispatch.1ybCMc/native-final` | 14 receipts; final working-tree sources, normal integrated selftest-level-1 build/execution, legacy/native/traversal/load/listener/split lifecycle; `native/` |
| `run_paired.py --candidate HEAD --candidate-signature pass --candidate-behavior baseline --prior-contracts --public-contracts --staging-contracts --negative-controls --output /tmp/task22-dispatch.1ybCMc/paired` | 44 receipts; ordinary ABI/staging/traces and fail-closed controls; `paired/` |
| `run_task22_negative.py --output /tmp/task22-dispatch.1ybCMc/negative-final2` | Ten isolated semantic negatives, 20 build/run receipts; `negative/` |
| Both supplied review fixtures, copied unchanged with `review/Holmakefile` into private directories; `Holmake --no-project --no-cache --no_prereqs -C "$tmp" -j1 check` | Both rebuilt and executed; `REVIEW_FAILURES=0`, `REVIEW2_FAILURES=0`; every `POST_ABORT_CALLBACKS=0`; `review*.log.gz` |
| `coverage_ledger.py`; `verify_evidence.py`; `audit_task14.py` | 2,153 cases, 37 immutable inputs and tracked-control structural contracts |
| `tools/h4pedant/h4pedant src/simp/tests/simp-ext`; `tools/h4pedant/h4pedant --nolinelen src/simp/src`; `git diff --check` | Pass; compact logs |

The paired driver selects committed starting HEAD `2a1f2f26f`, whose ordinary
sources equal final sources. It establishes ordinary compatibility, not final
extension execution. Focused/native/routine/review/negative runs execute final
working-tree extension code. All final checks follow the last executable edit.

Each semantic negative builds with exit **0** and executes with expected exit
**1**, failing its intended assertion, never a deferred static error. The six
prior controls are retained; four independent controls disable native abort
transport/checking, enclosing-search checking, solver continuation checking,
and standalone argument-child checking. Private loaded module paths, mutation
text, source hashes and completed-fixture markers are recorded. Historical
source negatives now copy their matching signature as well as implementation;
otherwise the new additive hook would cause a meaningless static failure.

Exploratory fixture corrections are not acceptance: fallback keys can match
before the policy abort, so tests distinguish post-abort callbacks from valid
earlier attempts; nested `SSFRAG` rules need named theorem pairs; unchanged
direct conversions require `QCONV` for reflexivity comparison. Original oracles
were not weakened. Deterministic Interrupt injection is tested; asynchronous
signal timing, whole-plan performance and independent clean builds are not
claimed by this bounded task.

## Files and cleanup

Changed production files: `TraverseExt.{sig,sml}`, `simpExtLib.{sig,sml}`.
Changed tests: `simp-ext/{derivation,lifetimes}.sml`, negative-control driver,
focused README, caller migration audit, this handoff and compact evidence.

The configured build path remains `/home/lukasz/dev/...`, while the checkout
is `/home/lukasz/work/...`. Commands use the archived temporary `bwrap`
same-checkout alias, fresh `/dev`, and configured cwd/HOLDIR/PATH; no config or
source rewrite and no copied production libraries. Runners remove their
private copied sources, caches and heaps immediately. New task-created test
products and scratch logs are removed after evidence archival; pre-existing
caller products and unrelated nested changes are preserved. No copied tree,
heap or generated executable is committed.

Progress has one TASK22 completion line. TASK23 is next; its persistence scope
and TASK24/25's recipes/external consumer scopes remain separate, not deferred
TASK22 work.
