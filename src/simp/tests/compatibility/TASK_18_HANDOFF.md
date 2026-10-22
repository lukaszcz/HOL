# TASK18 — ordinary tactic staging and marker paths

Landing identifier: **TASK18-legacy-tactics-v1** (containing commit).
Start/production HEAD: `5906ed6917b41140bf3cd978151a76b1d0c5df63`.
Pinned develop: `cccaa27d7099cbadc886983020cbe745db7793f3`.
The ordinary worktree started clean; unrelated nested `.agent-files` changes
were preserved. Linux/aarch64, Poly/ML 5.9.2, shared `hol.state0`, one GC thread
in isolated paired processes. Exact tool/heap/input/source/product hashes,
loaded paths, commands and exits are retained in the manifests.

## Bounded acceptance

**All TASK18 acceptance criteria are satisfied; no TASK18 blocker remains.**
TASK16's mechanical whole-file cutover already restored the implementation.
This task audits it, closes the original staged reds, extends missing ordinary
path coverage, measures construction/reuse/complete separately, and integrates
the strict gates. No gratuitous replacement wrapper or production edit is
needed. This is not acceptance of the whole performance plan, numerical timing
parity, independent clean builds, or TASK20's configured-tactic migration.

- Both original callback reproducers now match develop: one early printer
  call/two primitive inferences, no repeated printer callback on saved global
  tactic use, and valid saved application after the printer starts throwing.
  Construction failures occur at construction, with original exception identity.
- The unchanged, sealed **43-scenario TASK05 matrix** passes strict baseline
  expectations: **726 ordered events, 60 checks, 57 genuine validations per
  side**. Construction, first/second use, reconstruction, exact inference
  counts, diagnostic grammar/context capture, both wrappers/tagging orders,
  requirement-list quirks, installed/supplied bounds, zero/one/two allowances,
  malformed/negative bounds, missing/replaced/rewound fragments, labels, Abbr,
  ordered branches and nontrivial hypotheses are all executed, not skipped.
- New supplemental coverage passes **307 checks / 116 real validations per
  side**, also against an independent baseline/baseline control. It exercises
  all ordinary/full/reverse/no-strip aliases, assumption policies, full versus
  reverse dependency propagation, contradiction, psr/allasms configurations,
  conversions/rules/proving, nested wrapper/bound payloads and changing-goal
  reentry. Direct ASM/SIMP requirements deliberately remain application-time;
  full/global requirements remain construction-time. This distinction must
  not be flattened into one universal early preprocessing step.
- Returned validations are actually called with kernel-proved residual goals,
  including zero and multiple subgoals. Tests compare ordered goals/assumptions,
  reconstructed conclusions and complete hypothesis sets where specified,
  reject foreign hypotheses/oracle proofs, and include executable negative
  proof/branch-order controls. Pretty-printed endpoints are not proof evidence.
- Ordinary `simpLib.sml/.sig` and generic `markerLib.sml/.sig` remain entirely
  byte-identical to develop. Ordinary loading and execution contain no extension
  marker classification, strategy/configuration dispatch, looper/solver fallback
  or recursive extension processing. Actual traced supplemental loads reject
  extension engines, simpMarker and split modules.
- **Local baseline tactic/conversion/rule costs are recovered structurally**:
  original bodies/stages and all **53 named simpLib / 69 total selected native
  occurrences** retain the same instructions, call sites and static allocation
  reservations (only adjacent constant-pool relocation is normalized). The
  independent identical-source codegen control agrees. No work is moved out
  of construction/reuse/complete timing to obtain that conclusion.

Source/body/stage mapping and API decisions:
[`../tactics/AUDIT.md`](../tactics/AUDIT.md).
The ordinary source/signature SHA256s remain
`ee324439ac66cd14858d6ea5dc45a867d44fa6762298f1cf7df45b13aed6c3cd` /
`d1979668da105341e6e97e900848a2d382eaac3a50650c89bbdeae8ee3689666`.

## Cost evidence and explicit uncertainty

[`../tactics/performance/evidence/LOCAL_COSTS.md`](../tactics/performance/evidence/LOCAL_COSTS.md)
contains the local emitted-work argument, including unchanged partial stages
and allocation sites. Five aggregate compiler export records retain a symbolic
tracking-target difference (`Cond_rewr.with_tracking` to the shared ordinary
`SimpTracking.with_tracking`); it is not normalized away. All selected named
ordinary tactic/conversion/rule native bodies agree. This is local work, not
an assertion of identical downstream heaps or cumulative allocation.

The maintained matrix has **66 rows**: eleven ordinary operations, three
stages, two supplied/installed-rule scenarios. Construction saves/consumes the
actual curried value; reuse includes application and real tactic reconstruction;
complete includes construction, application and reconstruction. Stage counters,
escaping result sinks, proof/hypothesis/ordered-goal checks and exact consumed
counts guard every calibration/sample. Requirements stay inside measured
construction/complete; partial SIMP_CONV correctly defers term-dependent work.

Initial calibration, final current/control campaigns, and longer investigation
are all retained. Each final full campaign has **ten fresh alternating AB/BA
pairs**, three samples per row, the same calibrated schedule, separate CPU,
wall, non-GC and GC accounting, no concurrent task builds/benchmarks and no
outlier removal. Final batches span **0.078829–0.828066 seconds**. CPU point
ratios span **0.963–1.015**; timing intervals remain unresolved, not parity.
Every row/metric and independent baseline control is visible in
[`RESULTS.md`](../tactics/performance/evidence/RESULTS.md) and
[`ROWS.md`](../tactics/performance/evidence/ROWS.md).

Seven initial GC family-slower rows (three surviving control contrasts) and
one individual CPU/wall/non-GC row were **investigated, not waived**. The
predeclared follow-up uses **16x batches**, ten fresh current plus ten control
pairs and separate GC/heap diagnostic processes. None reproduces a slower
interval. The new intervals still include the earlier effects; this is not
statistical exclusion of those effects or proof of equality. Diagnostics show
large adaptive nursery/collection-frequency variation in both current and
identical-source control, comparable rounded nursery volume (not exact
allocation totals), and a real approximately **27.5 KB larger candidate live
heap** in these small fixtures. The latter is an environment difference, not
claimed storage parity. Actual extra loaded module is the shared ordinary
tracking service, not an extension engine. No speculative GC cause is asserted.
Full limits, raw observations and all eight targeted rows are preserved in
[`FOLLOWUP.md`](../tactics/performance/evidence/FOLLOWUP.md).

The bounded local-cost criterion is resolved by the original implementation
and exact emitted local work, **not** by calling uncertain timing a pass.
The follow-up finds no stable additional ordinary-work signal requiring a
TASK18 repair. Numerical whole-callgraph/GC/storage parity is not established
here; it was never this task's bounded acceptance criterion. No ordinary body,
callback-staging repair or newly discovered reproducible local regression is
being deferred. Existing independent-build/expanded final plan gates remain
separate, unchanged requirements, not substitutes for unfinished TASK18 work.

## Changed files / API boundary

- `src/simp/src/Holmakefile`: `ordinary-tactics` at selftest level 1 and log
  cleanup; no new ordinary import or library dependency.
- `tests/compatibility/Holmakefile`: `staging-contracts` now explicitly requires
  baseline behavior and passing legacy signature, rather than diagnostic reds.
- `STAGING_CONTRACTS.md`: distinguish historical reds from current acceptance;
  all fixture bytes, sealed expectations and historical evidence are unchanged.
- `tests/tactics/{selftest.sml,run_behavior.py,test_behavior.py,Holmakefile}`:
  supplemental paired suite, eleven fail-closed controls, ordinary-only traced
  loading, strict original/expanded staging and offline performance/codegen
  controls in normal integration.
- `tests/tactics/performance/`: consumed-result matrix, isolated runners,
  calibrated schedules, strict protocols/inference, codegen adapter, longer
  GC investigation and losslessly compacted unique evidence.
- `tests/tactics/{AUDIT.md,README.md,record_evidence.py,audit_evidence.py}`:
  source correspondence, reproducible commands and source-tied receipt audit.
- This handoff and actual `.agent-files/tasks/PROGRESS.md` status.

No public develop API, production source/signature, generic marker/postkernel
service, extension type/quota/identity contract, registry or external consumer
changed. `Split`, `ExclX`, configured solvers/loopers and recursive extension
argument handling remain only in explicit `simpExtLib`/`simpMarkerLib` paths.
Their existing native marker, extension and replay tests still execute. TASK20
retains its pre-existing configured migration scope; no new follow-up or repair
was discovered. Ordinary clients need no migration, option, preload or warm-up.

## Fresh final validation

Commands/exits/source seals and logs:
[`../tactics/evidence/task18/validation.json`](../tactics/evidence/task18/validation.json).
All commands below exit **0**, and executable launchers actually run.

| Check | Fresh result |
| --- | --- |
| `run_paired.py --candidate HEAD --candidate-signature pass --candidate-behavior baseline --public-contracts --prior-contracts --staging-contracts --negative-controls --output /tmp/task18-final/paired` | 44 receipts; both original callback reproducers, ABI/public clients, frozen 73/47/929/limits suites, strict 60-check staged proofs and rejection controls |
| `run_prior_native.py --output /tmp/task18-final/native` | 14 receipts; 642 native checks, traversal/exclusion, marker recursion, registration/replay, clean-load syntax and split persistence |
| `run_behavior.py --output /tmp/task18-final/behavior-final` | 307 checks / 116 validations each baseline/current |
| Same with pinned develop candidate, `behavior-control-final` | 307 / 116 each baseline/control |
| `bin/build -t --seq=tools/sequences/upto-parallel` | Complete final routine build; new integrated ordinary-tactics gate executes |
| `bin/Holmake --holstate="$PWD/bin/hol.state0" --no-project --no-cache -C src/simp/src -j1 HOLSELFTESTLEVEL=1 all` | Final integrated ordinary/extension/marker/staging/other existing gates |
| Python behavior / timing / codegen / compatibility controls | 11 / 14 / 3 / 135 pass |
| Immutable verifier; coverage ledger | All 37 preserved inputs / 2,153 source-tied cases intact |
| Offline evidence audits; performance archive recovery/inference/codegen/GC rechecks; h4pedant; diff check | Pass |

A final supplemental-fixture line wrapping and documentation/integration
cleanup was followed by fresh behavior/control, routine, integrated Holmake
and Python checks. Production/measured workload sources remain unchanged;
subsequent changes are handoff/status and offline evidence packaging only.
Historical performance fixture revisions (before optional diagnostic filtering)
remain sealed in unique source blobs. Nothing is silently relabeled final.

## Cleanup

Private source trees, heaps, launchers, diagnostic products and temporary
campaign outputs are removed after retaining unique source-tied receipts and
compact raw evidence. Initial fixture/elaboration failures remain in the
performance archive; corrections were diagnosed against baseline, not hidden
candidate exemptions. Supplemental early attempts are summarized in evidence
notes, with no changed develop expectation. Redundant worker handoffs/receipt
copies, task-created Holmake caches/locks and scratch theory exports are
removed. No copied build tree, generated executable or heap is committed.
Unrelated files and the nested repository's pre-existing changes are preserved.

**TASK19 is next. No TASK18 work remains.**
