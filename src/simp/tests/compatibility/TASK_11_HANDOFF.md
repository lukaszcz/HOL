# TASK_11 handoff — original Traverse and ordinary congLib

Landing identifier: **TASK_11-legacy-traverse-v1** (commit containing this file).
Start HEAD: `459512593b50387a137f09ab42e68f95e97f6dc2`.
Pinned develop: `cccaa27d7099cbadc886983020cbe745db7793f3`.
Measured implementation snapshot: `evidence/task11/validation.json`.
Runtime: Linux/aarch64, Poly/ML 5.9.2, configured hol.state0, one GC thread
in paired processes. The main worktree started clean; unrelated nested
`.agent-files` state was preserved.

## Bounded acceptance

**All TASK_11 criteria are satisfied. No TASK_11 blocker remains.** This is not
legacy storage/loading/tactic-stage restoration, whole-plan performance
acceptance, an independent clean build, or certification of other platforms.

- **All four complete `Traverse.{sig,sml}` / `congLib.{sig,sml}` files are
  byte-identical to pinned develop.** This restores the entire signature,
  single REDUCER datatype, records/destructors/collectors and native engine.
  There is no compatibility wrapper, eligibility/projection/dispatch scan or
  extension import in Traverse. The restored source includes eager factory
  evaluation, reusable private contexts, exact exception handlers and limit
  rollback, not a newly generalized implementation with similar results.
- The original ascription, complete-signature functor, datatype replication,
  exhaustive match, every reducer/traversal field and interoperation clients
  actually execute successfully. No original source fixture/signature changed.
  All nine public clients and the original ABI fixture pass on both sides.
- Paired original **73**, traversal **47 / 273 observations**, exclusion
  **929 / 2,703 observations**, and **six** targeted limit checks pass with
  their frozen complete ordered observations. Callback staging, factory
  failures, context reuse, warning/error provenance and rollback match develop.
- Native **642** checks retain all 630 original case IDs plus twelve registry
  checks. The separate **131 TraverseExt** checks retain explicit ordinary
  lifting, collector/apply callback, exception and proof contracts. The
  **88 simpExtLib** checks retain tracked/configured capabilities and eight
  actual static cross-type rejections. None is replaced by a stub or a count.
- `congLib` again projects `traversedata_for_ss`, wraps ordinary equation
  reducers and calls native TRAVERSE exactly as develop does. Explicit
  configured callers use the already-extracted `congExtLib.CONGRUENCE_*`
  entry points with extension-owned congsets and simpsets. Existing tests
  exercise actual configured subgoaler/solver calls, depth/order forwarding
  and collector lifetimes. Shared congruence primitives remain real current
  implementations until TASK_13; no duplicate exception/preorder/control
  identity was introduced.

## Types, changed files and temporary cooperation

`Traverse` and `congLib` are exact restorations. `simpLib.{sig,sml}` now qualify
surviving branch-only solver/configuration/root/context/child-first machinery
with `TraverseExt`. Public ordinary SSFRAG/dproc/weakener/projection types stay
baseline Traverse types. The configured getter alone explicitly lifts stored
ordinary dprocs. There is no reverse adapter or extension reducer implicitly
installed in a legacy API. Ordinary reducer inspection uses `dest_reducer`.

`selftest.sml` adjusts the ordinary mixed-strategy solver annotation, removes
an impossible extra-constructor pattern and strengthens the one-way projection
pin (payload identity, fields and zero callbacks). The existing additive
`task10-relocation.json` overlay records only current anchors/hash/decision;
all frozen cases, original inputs, assertion labels/order and current event
stream remain intact. The obsolete mixed-refresh diagnostic route is removed;
remaining ordinary/default/refreshing extension diagnostics keep all assertions.

New `performance/TraversalPerformance.sml`, suite-aware runner/schema/summary/
audit support and 10 Python protocol tests isolate traversal from mixed net
costs. Default performance validation is unchanged. Missing events, wrong
counts/consumption, wrong source paths, missing footer and wrong fixture binding
are rejected. `audit_task11.py` rechecks source identity, current source seals,
original client/trace/native receipts and all 80 archived timing receipts.

[migration/TASK11.md](migration/TASK11.md) closes **M0**, updates **M1/M6** and
retains **M2–M5, X1/X2** with their existing removal owners. In particular,
temporary TraverseExt dependencies in simpLib signature/storage/tactics are
explicitly owned by **TASK_16**, not hidden inside Traverse. TASK_12/13 own
paired/threaded primitive separation. No new unbounded follow-up was added.

## Fresh commands and evidence

From repository root. Full commands/exits, implementation/input/runtime hashes,
executed load paths, observations and source correspondence are under
[`evidence/task11/`](evidence/task11/). `commands.json` records command boundaries;
paired/native manifests retain individual launcher/build commands and exits.
The validation snapshot is a Git object, not an additional branch landing;
source seals independently bind all its production files to this landing.
Reproduction may use the landing commit as `--candidate`.

| Check | Exit / result |
| --- | --- |
| `run_paired.py --public-contracts --prior-contracts --negative-controls --candidate <snapshot> --candidate-signature pass --output <fresh>` | 0; all original public/ABI clients, exact prior observations, 12 intended fail-closed controls; final harness rerun |
| `run_prior_native.py --output <fresh>` | 0; 642 native, all focused marker/registration/replay and exact fresh-load streams; eight freshly rebuilt persistence/heap scenarios |
| `Holmake --holstate="$PWD/bin/hol.state0" --no-project --no-cache -C src/simp/tests/simp-ext -j1 check` | 0; 88, including eight static rejections |
| Same explicit `check`, `-C src/simp/tests/traverse-ext` | 0; 131, including two static rejections |
| Paired broad and direct traversal timing runs, ten pairs each; baseline/baseline controls first | 0; 80 fresh measured processes; full per-sample CPU/wall/GC, calibration, consumption and raw observations |
| Compatibility / performance unittest discovery | 0 / 0; 62 / 18 tests |
| `coverage_ledger.py`; `verify_evidence.py` | 0 / 0; 2,153 cases and 37 immutable inputs intact |
| `bin/build -t --seq=tools/sequences/upto-parallel` | 0; Hol built successfully after final SML addition; earlier complete rebuild also passes |
| h4pedant on production/compatibility/performance/traverse-ext directories; `git diff --check` | 0 / 0 |
| `audit_task11.py evidence/task11` and performance archived-provenance negative controls | 0; exact restored bytes, fresh executed clients, 80 source-bound timing receipts |

An initial routine build was interrupted by the tool's 120-second timeout;
it is retained as interrupted evidence, not a pass. The unrestricted rerun
completed, and the final post-fixture routine run also completed. A one-pair
focused smoke run was used only to validate ML elaboration/consumption, not
acceptance. Only final useful receipts are retained. No production edits were
made after the measured snapshot. All measured runtime/tool seals and **66,624**
shared-product references still match after the final routine build.

## Construction/reuse gate and attribution

Each timing experiment uses ten alternating AB/BA pairs, five calibrated
samples per fresh process, no outlier removal, one GC thread, consumed escaping
construction results and checked proofs/hypotheses. Direct batches target
0.25 seconds; broad batches target 0.2 seconds. CPU includes GC; GC and wall
are also reported separately, never added again. Summaries contain all raw
per-operation samples, paired ratios and fixed-seed 20,000-resample median CIs.

Direct ordinary reducers use **no simpLib net, Cond_rewr or extension module**
in the measured process. They exercise empty/nonempty-context construction,
saved hit/miss conversions, complete construction/application and a 64-deep
congruence factory/depther. Exact collector/factory totals enter the checked
sink; proofs and hypotheses are verified, not ignored.

| Direct workload | Baseline/control CPU ratio | Candidate CPU ratio [95% CI] |
| --- | ---: | --- |
| Construct empty context | 1.0085 | 0.9978 [0.9853, 1.0070] |
| Construct supplied context | 1.0310 | 1.0277 [0.9870, 1.1102] |
| Reuse hit | 1.0491 | 1.0382 [0.9794, 1.3157] |
| Reuse miss | 1.0049 | 0.9689 [0.9513, 1.0207] |
| Complete contextual operation | 1.0412 | 1.0279 [0.9834, 1.1165] |
| Deep congruence factories | 1.0020 | 1.0121 [0.9784, 1.0502] |

Wall ratios track CPU; raw GC measurements remain separate in each summary.
These noisy intervals alone are **not statistical equivalence or a regression
allowance**. Attribution is resolved by inspecting the *entire unchanged
implementation*: all original allocation expressions, closures, call paths,
factory evaluations, context records, exception scopes and limit operations
are exactly restored, with no extra work anywhere in Traverse or congLib.
The fresh direct probes confirm execution without mixed sources; the paired
traces confirm its scheduling. Together these close the bounded traversal gate;
no unresolved additional work is attributable to traversal. No general total-
allocation, retained-simpset-storage or other-platform claim is made.

The broader fixture is deliberately retained, not averaged away. Native
construction on a 1,000-rule projection is 1.0053 [0.9946, 1.0176]. Mixed raw
reuse is 1.0192 [1.0058, 1.0606]; projection/application is 1.0401
[1.0165, 1.0543]. Their additional work is in still-mixed net/conditional
runners and projection, not the restored traversal body. Broad creation,
merge, compile, missing deletion, projection, empty add, SIMP and compile/apply
ratios respectively are **1.8101, 3.0695, 1.1372, 2.5670, 1.0675, 1.1854,
1.0156, 1.1080**. They remain real whole-plan blockers, explicitly owned by
TASK_12/15–18 and later gates. Restoring traversal does not claim to fix them.

## Cleanup and next task

Task-created private paired source trees are removed by the runner. Temporary
pilot/final output copies, logs, snapshot reference file and focused test
caches/launchers are removed after archiving compact unique evidence. No heaps,
copied build trees or generated binaries are committed. Normal production build
products and unrelated caller artifacts remain untouched. TASK_12 is next.
