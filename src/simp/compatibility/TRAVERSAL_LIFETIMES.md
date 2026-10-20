# TASK_05: traversal lifetime contracts

Landing identifier (commit subject):
`[TASK_05] Validate traversal staging and shared controls`.

Entry HEAD: `667320e9bebeeabc97e548301565911a88a26b13` (TASK_04), on
`simplifier`. No branch/reset/merge operation. The caller's TASK_04
status/commit corrections in task progress are preserved.

## Audit and changes

The audit preceded new assertions. Existing `src/simp/src/selftest.sml`
coverage was retained, including the assertions moved to extended extraction
by TASK_04:

- R2: construction-time context collection and reusable Once for native
  traversal; mixed-representation fallback; delayed total wrappers;
  per-application refresh for explicit engines and conversion settings.
- R6 and maker tests: exact congruence/weakener factories, factory rejection
  caching, retry/reuse, root abort, malformed-bound staging and compilation
  traces. P1/C2: fact order, binder protection, private contexts and live
  controls. Reflexivity/paired-runner tests: exception payloads and solver
  wrapping/Interrupt.
- Public/configured quota tests already alternate both orders, check full
  theorems/hypotheses/free variables, and count filter invocations. View and
  preserving-control replay tests already retain remaining quotas.
- Configured depth/order/subgoaler/solver and child-first positive tests
  already use explicit APIs. None were deleted, relaxed or moved back to
  public legacy extraction.

Two gaps warranted additional branch assertions in `selftest.sml`:

1. Extract the opposite projection **after** spending a use, then extract
   both again after exhaustion, in both starting orders. This uses the
   complete `XTRAVERSE (xtraversedata_for_ss ss)` pair as well as public
   `TRAVERSE`. Two uses remain two uses across per-application context
   refresh. A filter count of one and zero new-rewrite trace events bracket
   extraction/application: no recompilation or quota refresh is allowed.
2. Strengthen existing contextual/configured fallback checks: optional
   native rejection and configured extraction call no collectors; a saved
   `SIMP_CONV` with facts collects once per application, with counts
   `[0,1,2]`. Both reducer constructors still receive explicit depth one
   while the global limit is zero, and preserve the original theorem and
   depth-callback assertions.

No production defect was exposed, so no simplifier implementation or API
changed. The public/extended split and native dispatch from TASK_04 remain
unchanged.

## Shared executable differential fixture

`probes/support/TraversalContracts.sml` uses legacy APIs only. Both
`probes/legacy/traversal-lifetimes.sml` (paired input) and
`probes/support/RunTraversalContracts.sml` (native launcher) invoke the same
module. Its **47 assertions** verify:

- Raw traversal and congruence QCONV collect once at construction and reuse
  the private context; total SIMP/congruence wrappers delay collection and
  collect once per application (`[1,1,1]` versus `[0,1,2]`).
- Multiple collectors run R1/R2/D1/D2 with exact fact order. Recursive
  collection starts from the initialized private contexts on each reuse,
  not a context mutated by an earlier application. Empty initial facts
  invoke no collectors.
- Repeated legacy extraction shares partially spent/exhausted installed
  bounded rules. Theorems include hypotheses and free variables, not just
  equal final RHSs.
- Congruence and weakener relation/factory callbacks precede root attempts;
  retries reuse factories within an invocation, application reuse rebuilds
  them, and root abort still occurs after factory construction. Rejection
  before a root mutation stays cached.
- The live stack limit is read between native candidates and on application
  of an already constructed conversion; global changes are restored.
- Raw unchanged is HOL_ERR, public unchanged is UNCHANGED; foreign reducer
  payload identity survives raw/public application, while the legacy total
  congruence wrapper catches it. Foreign factory exceptions are rejected
  by develop's mapfilter, but Interrupt escapes. Conditional solver errors
  retain their actual HOL_ERR wrapping and Interrupt boundary.
- Malformed bounded tags raise Option before maker callbacks. All makers
  precede compilation traces, and projection invokes neither again.
- A real collector warning is forwarded unchanged, once at construction,
  not repeated on application. Warnings stay enabled.

Each scenario captures **every** Trace action (all levels), callback and
warning in one ordered stream. Exception events are included at their
actual position in that stream and also expose constructor/HOL_ERR fields
and complete diagnostics. Warning sinks/listeners are restored on all exits.
The tests do not silence, strip or normalize warning/exception output.

The normal `src/simp/src/Holmakefile` target `traversal-contracts` builds the
support launcher in its own dependency scope, executes it from that source
directory, and retains `traversal-contracts.log`. `HOLSELFTESTLEVEL` adds it
to `all` alongside `simp-selftest.log`. This avoids resolving private
simplifier modules through a not-yet-populated `sigobj` during bootstrap.

`run.py --suite` now permits focused selection, always including control and
the unchanged develop suite. Its default still runs every legacy probe;
unknown selections fail. This does not turn existing exclusion reds into
xfails or remove them from the broad differential gate.

## Validation and provenance

Final evidence: `results/task05/validation.json` and
`results/task05/differential-final/manifest.json`. They record exact argv,
exit codes, source/input hashes, loader audit and log receipts. Commands
from the repository root (`$HOLDIR` is its absolute path):

```sh
(cd src/simp/src && ../../../bin/Holmake --no-project --no-cache -j1 \
  --holstate="$HOLDIR/bin/hol.state0" selftest.exe && ./selftest.exe)
(cd src/simp/src && ../../../bin/Holmake --no-project --no-cache -j1 \
  --holstate="$HOLDIR/bin/hol.state0" traversal-contracts)
(cd src/marker && ../../bin/Holmake --no-project --no-cache -j1 \
  --holstate="$HOLDIR/bin/hol.state0" selftest.exe && ./selftest.exe)
bin/build -t --seq=tools/sequences/upto-parallel
python3 src/simp/compatibility/run.py --branch 667320e9b \
  --suite traversal-lifetimes --suite reducer-shape \
  --output src/simp/compatibility/results/task05/differential-final
(cd src/simp/compatibility && sha256sum -c inputs/SHA256SUMS)
tools/h4pedant/h4pedant src/simp/src \
  src/simp/compatibility/probes/support
git diff --check
```

All final commands exited **0**. Native selftest: **432 OK**; contracts:
**47 OK**; marker: **61 OK**. Existing ordinary SF-registration warnings
remain visible. The native final standalone run also included the five
availability-guarded later-datatype splitter tests; bootstrap runs without
those objects had 427 OK, without changing any guard/assertion. The routine
build ran the normal contract target and ended `Hol built successfully.`

Paired reference: `cccaa27d7099cbadc886983020cbe745db7793f3`.
Paired implementation library source: entry HEAD, since this task changes
only tests/build wiring/harness/docs, not production library sources. The
new fixture and runner are working-tree inputs snapshotted and hashed by
the manifest, not mistakenly claimed to come from the library commit.
Both lanes: traversal **47 OK**, reducer shape **7 OK**, control **4 OK**,
unchanged develop suite **73 OK**, all build/run exits zero. Traversal's
**273 ordered observations match**, and its complete raw run logs are
**byte-identical**, SHA-256:

`6e510a45c1d112c75244312af7c3c36cbe88dbc190a03835870b1200f2dd7890`

The raw logs include the real warning, all callbacks/traces and exception
diagnostics. No output normalization was used for this equality. Other
suites' complete logs are retained; the unchanged develop suite has no OBS
trace and is a passing assertion suite, not a universal trace comparison.
These are the harness's documented **mixed-source** lanes, not independent
full-repository builds: host kernel/heap, generated theories and other
shared dependencies remain shared and fingerprinted.

During fixture development, incorrect new oracles/target wiring failed
before final validation. Develop rejects foreign factory exceptions rather
than propagating them; the final oracle pins that distinction and Interrupt
instead. The final native target fixes private-module resolution, an
INCLUDES cycle and launcher cwd. These were fixture/build integration
mistakes, not production regressions or accepted remaining failures.
`validation.json` summarizes them. Initial successful and failed disposable
attempts, copied trees, caches and scratch logs were removed after retaining
final evidence. Only agent-created artifacts were cleaned.

## Handoff / remaining scope

Changed: `selftest.sml`, its Holmakefile, the three support fixture/launcher/
build files, legacy probe, runner selection, compatibility README, this
handoff, task05 evidence and task progress. No finalized API decision changes.
TASK_05 has **no open acceptance blockers**.

TASK_14 must rerun the broader paired matrix after exclusion/registration
repairs; the ten legacy exclusion and fresh-load reds remain owned by their
existing tasks, not this lifetime gate. TASK_17 must retain the mixed-source
provenance limitation, complete the final full-build/report/cleanup gates,
and avoid claiming universal observational equivalence from these finite
callbacks. No larger unrelated divergence was found or deferred by TASK_05.
