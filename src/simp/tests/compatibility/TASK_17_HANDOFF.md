# TASK_17 — literal exclusions and ordinary replay

Landing source identifier: **TASK17-literal-replay-v1** (containing commit).
Start/production HEAD: `ba366bcae12c373cdfadcc982ac0319f08045a05`.
Ordinary worktree initially clean; unrelated nested `.agent-files` state was
preserved. Pinned develop: `cccaa27d7099cbadc886983020cbe745db7793f3`.
Runtime: Linux/aarch64, Poly/ML 5.9.2, shared `hol.state0`, one GC thread in
paired measurements. No production flag, migration, preload or warm-up.

## Bounded acceptance

**All TASK17 acceptance criteria are satisfied. No TASK17 blocker remains.**
TASK16 already restored the entire ordinary source/signature pair. This landing
keeps those bodies unchanged and adds the missing exhaustive bounded audit,
fresh semantic observations, focused matrix and normal regression integration.
It does not invent a replacement wrapper or charge legacy clients new work.

- Literal `-*`/`remove_simps`/Excl parse strings, filter the original net once,
  then the original dproc list once. No extension inventory scan, namespace
  resolution, configured payload, early missing-name return or ExclX rewrite.
- Exact develop dotted parsing, prefixes, dproc names, warnings/errors and
  argument order match in the freshly rerun 929-check/2,703-observation stream.
  All other frozen prior observations remain intact too.
- New empty-net tests prove unmatched **nonempty** DELETE_EVENTs survive and
  are reparsed after a real current-theory change; only an empty list is inert.
  Restoring the naming context makes the same replay valid again.
- New replay checks pin maker composition/order and exact collector counts,
  ADDWEAKENER and dproc deletion scheduling, missing-removal UNCHANGED without
  callbacks, always-replaying exclusion, limits/excluded state and force-add.
  Anonymous exclusion/addition's baseline distinction is deliberately retained.
- Surviving conversions share actual remaining declared allowances through
  deletion; ordinary replay and fragment exclusion reset them by recompilation.
  Zero/two bounds, old exhaustion, replay exhaustion and independent old/new
  controls are proof-checked. This is not extension preserving-control replay.
- Conversions and saved/reused ordinary tactics use literal deletion. Tactic
  validations reconstruct the exact conclusion **and complete hypotheses**.
  No oracle, dropped subgoal or pretty-printed-endpoint substitute.
- The focused cost matrix removes the reported ~3x work: **44 rows**, sizes
  **0/10/1,000/10,000**, missing/matching/batched/qualified/partial,
  namespace-looking literal prefix/exact, dproc-only/mixed, empty-list and replay.
  Each timed batch consumes escaping results; proof, ordered dproc names,
  persistence and replay maker/collector counts are verified outside the timer.
  No row is hidden by a workload aggregate or a fixed regression tolerance.

Detailed source correspondence and API decisions: [`../exclusions/AUDIT.md`](../exclusions/AUDIT.md).
Ordinary source SHA256: `ee324439ac66cd14858d6ea5dc45a867d44fa6762298f1cf7df45b13aed6c3cd`;
signature: `d1979668da105341e6e97e900848a2d382eaac3a50650c89bbdeae8ee3689666`.
Both entire files are byte-identical to pinned develop. The supplemental
selftest seal is `3ce1f5a952ed60950cdae96e503832ee3caf49250753fb9471ac80f64355d39a`.

## Performance interpretation — bounded work, not universal timing parity

[`../exclusions/performance/evidence/RESULTS.md`](../exclusions/performance/evidence/RESULTS.md)
and [`GC_FOLLOWUP.md`](../exclusions/performance/evidence/GC_FOLLOWUP.md) retain
all raw outcomes and uncertainties. Final current **then** baseline-control
campaigns each have **ten fresh alternating AB/BA pairs**, three samples per
workload, the same fixed calibrated schedule, no concurrent builds/benchmarks
and no outlier removal. CPU/wall/GC/non-GC are separate.

Total-CPU point ratios span **0.972–1.020**, not ~3. CPU/wall intervals remain
unresolved in 43/44 rows; this is **not numerical parity**. The bounded no-extra-
algorithm-work conclusion is independently established by the byte-exact
source and **25 selected native occurrences**, identical after only adjacent
pool-relocation normalization, including delete/parser/net-filter/replay callers.
Full exact compiler records/differences are archived. Tracking-reference changes
in whole initializers are retained, not normalized away. No extra deletion,
fragment replay, allocation site or traversal was introduced.

Four GC-only slower intervals in the first final campaign remain visible.
A serial follow-up (four fresh pairs each current/control, target batches
16x longer) and separate GC/heap trace do not reproduce them as a stable
four-row slowdown. They show materially different adaptive nursery sizing and
collection counts despite identical operation counts; candidate retained heap
is smaller. This is not exact cumulative-allocation equality or a causal proof
for every GC delta. None of those uncertain numerical results is called a pass
of whole-plan parity. TASK17's bounded threefold-cost/no-extra-scan criterion
is met; no ordinary-body repair is left undone. Final expanded statistical and
independent-build gates are separate pre-existing plan criteria, not a waiver
or deferred TASK17 repair.

## Changed files and API decisions

- `src/simp/src/Holmakefile`: add `literal-exclusions` at selftest level 1 and
  its log cleanup. Ordinary imports and extension loading stay unchanged.
- `tests/exclusions/selftest.sml`, `run_behavior.py`, `test_behavior.py`,
  `Holmakefile`: 42 new checks on both source versions, strict ordered protocol,
  8 omission/order/count/proof/completion controls; normal integration also
  runs the 13 performance-schema and 2 codegen-adapter offline controls.
- `tests/exclusions/performance/`: ordinary-only fixed consumed-result matrix,
  isolated fresh-process runner, independent control, codegen correspondence,
  longer GC diagnostics, all per-row analyses and compact raw evidence.
- `tests/exclusions/{AUDIT.md,README.md,record_evidence.py,audit_evidence.py}`:
  bounded contract, commands and source-tied archived receipt audit.
- This handoff and actual `.agent-files/tasks/PROGRESS.md` status.

No public API, baseline literal behavior, extension source/signature,
source/view/quota contract, named registry, generic marker/postkernel service,
external consumer or immutable input/assertion ledger changed. TASK19's
extension inventory/suppression/control-preserving replay is untouched.
No new out-of-scope repair or follow-up was discovered.

## Fresh validation and exact evidence

Main receipts/source seals/commands are at
[`../exclusions/evidence/task17/validation.json`](../exclusions/evidence/task17/validation.json).
All final mandatory commands exit **0**, and executable launchers actually ran.
Per-process runtime/tool/heap/input/selected-source/loaded-path/product seals
are retained in the compressed manifests. These are isolated-source/shared-
dependency comparisons, **not independent clean repository builds**.

| Command/check | Fresh result / evidence |
| --- | --- |
| `run_behavior.py --output /tmp/task17-revalidated/behavior` | 42 checks per side, exact streams, two accepted executions; `behavior/` |
| `run_paired.py --candidate HEAD --candidate-signature pass --candidate-behavior baseline --public-contracts --prior-contracts --staging-contracts --negative-controls --output /tmp/task17-validation/paired` | 44 receipts; original ABI, nine public clients, 73/47/929/six-limit suites, callback/proof staging, fail-closed controls; `paired/` |
| `run_prior_native.py --output /tmp/task17-validation/native` | 14 receipts, native 642 checks, traversal/exclusion, markers, registration/replay, fresh loading and persistence; `native/` |
| `bin/build -t --seq=tools/sequences/upto-parallel` | Full routine sanity build, including new gate; `routine-final.log.gz` |
| `bin/Holmake --holstate="$PWD/bin/hol.state0" --no-project --no-cache -C src/simp/src -j1 HOLSELFTESTLEVEL=1 all` | Integrated ordinary/extension/new literal gates; `holmake-final.log.gz` |
| Python compatibility / performance / fragments / routes / fragment assembly | 135 / 30 / 36 / 7 / 15 pass; `python-*.log.gz` |
| Python compiled core / assembly / new behavior / exclusion performance / adapter | 9 / 10 / 8 / 13 / 2 pass; `python-*.log.gz` |
| Immutable verifier; coverage ledger | 37 original inputs and 2,153 source-tied cases intact; `immutable.log.gz`, `ledger.log.gz` |
| Four-size final timing/control and compiler campaigns | 40 measured processes, both final codegen collections; `performance/evidence/` |
| GC long/control and trace | 16 diagnostic timing processes plus separate trace pair; same evidence directory |
| Source/receipt and performance offline audits; h4pedant; diff check | Pass; maintained `audit_evidence.py`, performance `evidence/recheck.py` |

A final trailing-whitespace-only fixture cleanup was followed by fresh paired
behavior, routine and integrated Holmake runs; their final receipts are archived.
The final routine run includes the final normal-integration recipe. Subsequent
changes are documentation, offline evidence collectors and archives only;
measured production/performance fixtures are unchanged. No historical pass substitutes
for these fresh runs.

Exploratory semantic failures are archived separately in `attempts/`: an omitted
anonymous empty `&&` fragment in the expected history, an underconstrained SML
pair pattern, an inert test reducer incorrectly raising UNCHANGED instead of
NO_CONV, then two missing testutils tactic-context adaptations. Those fixtures
failed on develop before candidate acceptance. Corrected expectations implement
actual baseline contracts; final 42 checks run unchanged on both sides. The
attempt to rebuild the old ledger at its existing path was correctly rejected;
normal ledger verification passes without modifying it. Performance exploratory
failures, reruns and lossless compaction receipts are separately documented.

## Cleanup and next task

Private copied source/build trees, heaps and launchers are removed by runners.
Task-owned temporary logs/receipts and new Holmake cache/lock files are removed
after retaining compact unique evidence. Final raw timing/GC observations and
exact codegen records survive lossless compaction (about 8.3 MB), without copied
build trees or generated executables. Unrelated artifacts remain untouched.
**TASK18 is next.** No TASK17 work remains.
