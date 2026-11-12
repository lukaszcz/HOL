# Simplifier performance harness

## Grids and gates

`task29_gate.py run` executes the fixed 27-case, six-size grid, uses the
TASK28 admission/statistics and losslessly archives each cell before cleanup.
`task29_gate.py replay --output ARCHIVE_DIRECTORY` revalidates all archives
and recomputes decisions without live private builds. Neither is an implicit
normal selftest or independent-build measurement.

`task29a_grid.py` runs the same 162 cells under the equivalence policy
(version 2, `PROTOCOL.md`): 3% margin on CPU/wall, B/B validity window, GC
reported. Every process of a cell uses one predeclared count from
`task29a_iterations.json`; pairs and samples are run options.
`task29a_grid.py replay --output DIR` recomputes every decision offline;
`--partial` replays the finished cells of an interrupted run without a grid
decision. `--layout-seed` randomizes each process's code layout, `extend
--grid DIR` runs the predeclared, candidate-blind second stage, `dispose
--output DIR` applies the policy owner's disposition, and `--resume` continues
after an infrastructure failure (`PROTOCOL.md`, "Code-layout randomization").

`timing_grid.py` is the TASK29A grid as a parameterized engine (`PROTOCOL.md`,
"Shared timing grid"); `task29a_grid.py` and `task30_grid.py` are its tables.
`task30_grid.py` covers the 24 exclusion and history cases at six sizes (144
cells): `pilot` and `predeclare` produce the develop-only batch counts, with
the layout seed, pairs and samples of the table, that are committed as
`task30_iterations.json` before any candidate observation (`verify-counts`
checks the file against its pilot), `run`, `extend` and `replay` follow
TASK29A and take the pilot (every run is recorded in the table's attempts
ledger, `.agent-files/evidence/task30/attempts.jsonl`, and a measurement
needs a clean checkout at the candidate, built by `prepare`); `close`
replays this gate and the allocation gate and prints one verdict. A
candidate whose source files on the
path differ from the baseline's is never a pass unless the difference is a
pinned, reviewed one (`task30_pins.PINNED`), and the exit status is zero only
when every cell passes. The exact-allocation counterpart
is `allocation_matrix.py run --task task30` (all 24 cases, 144 cells; in
`history_theory_change` the allocation fixture makes no `new_theory`
transition, see `PROTOCOL.md` and `ALLOCATION_COUNTER.md`).

`task32_downstream.py` (TASK32) times downstream proof-build units in two
independent snapshots; its `--table task33` selects the TASK33 startup and
first-load timing kinds, and `task33_storage.py` (with `task33_offline.py`,
`task33_declared.json` and the probes in `task33/`) decides loading,
retained-storage and release cases on the same snapshots. Procedure, cases,
counts files, ledger, exit codes and snapshot disposal are in `PROTOCOL.md`,
"TASK33 independent loading, storage and release".

Fresh post-workload actual object/code/pool diagnostics are documented in
[`RUNTIME_LAYOUT.md`](RUNTIME_LAYOUT.md) and
[`RUNTIME_POOLS.md`](RUNTIME_POOLS.md).
They are explicitly **not timing acceptance**. The read-only environment
diagnostic cannot certify exclusivity.

## Maintained TASK28 integration

This directory provides acceptance **machinery**, not performance approval.
[`MATRIX.md`](MATRIX.md) describes the frozen `matrix.json` contract: **69
requirements, 107 case bindings**, runnable cases/external checks and seven
explicit prerequisite blockers. [`PROTOCOL.md`](PROTOCOL.md) defines paired
statistics, sealing and independent-build admission;
[`PROTOCOL_LOADING.md`](PROTOCOL_LOADING.md) defines runnable fresh-import timing.

Both matrix fixtures record raw CPU/wall/GC and actual runtime counter/snapshot
records for **every** calibration/sample. The runner and offline auditor validate
source seals, graph arithmetic, ordered runtime records and controlled weak-ref
release. RSS snapshots and process-lifetime VmHWM are not exact temporary peaks;
Poly/ML 5.9.2 lacks a cumulative allocated-byte counter. Weak collection proves
only release of the controlled simpset-ref wrapper, not opaque internal objects
or absence of global retention.

A runnable matrix is not a measured one, and the ten-pair experiment validates
machinery, not matrix-wide performance approval. Shared-heap final-source
isolation is **not independent builds**; independent mode blocks until fresh
independent launchers, inventories and consumed observations exist.

Matrix archives need manifest-bound shared sources/products (`shared_inputs`)
and exact runtime/tool/launcher provenance to be admissible. Storage slopes and
their controls/uncertainty participate in CLI exits, and loading must exercise
positive GC in its accounting control.

### Maintained checks

From the repository root, using new output paths each time:

```sh
# Python-only discovery; real HOL integration tests are opt-in.
python3 -B -m unittest discover -s src/simp/tests/performance -p 'test*.py'
python3 -B -m unittest discover -s src/simp/tests/compatibility -p test_runner.py
python3 -B src/simp/tests/performance/matrix_schema.py --json

# Configured tree, no other build/benchmark running; use an exact candidate pin.
bin/Holmake --no-project --no-cache --no_prereqs \
  --holstate="$PWD/bin/hol.state0" -C src/simp/tests/performance -j1 \
  PERFORMANCE_CANDIDATE=CANDIDATE_FULL_40_HEX_COMMIT \
  PERFORMANCE_CHECK_OUTPUT=/absolute/path/to/new-check-output check
```

`python-tests` discovers all performance tests (real HOL tests are skipped
unless enabled), plus compatibility runner tests. `check`
serially runs discovery, matrix completeness, real Python subprocess controls,
then `smoke_matrix.py` and `smoke_clients.py --scope small`. It does **not** run
performance acceptance,
loading measurements, runtime smoke or expensive full-grid cases implicitly.
Plain Holmake runs the Python tests; `diagnostic` uses six pairs and separate
`PERFORMANCE_OUTPUT` paths.  The targets that write output depend on a guard
that refuses an unset, relative or in-repository output directory before
anything else runs, at any `-j`.

Other explicit targets in `src/simp/tests/performance/Holmakefile`:

| Target | Scope |
| --- | --- |
| `matrix-completeness` | Frozen schema and live source inventories; no measurements |
| `controls` | Actual Python slowdown/allocation/failed/missing subprocess controls; not Poly allocation |
| `smoke` | `smoke_matrix.py`; 51 MatrixSupport cases at 0/1/10 on both selections by default, not all 107 cases |
| `runtime-smoke` | Actual SML GC counts/RSS and controlled-ref collection on both selections, untimed |
| `client-smoke` | All 56 client construction/reuse/complete cases at 0/1/10 on both selections |

Set `PERFORMANCE_BASELINE` (default pinned develop), `PERFORMANCE_CANDIDATE`
(default HEAD, resolved and recorded by smoke drivers), and
`PERFORMANCE_CHECK_OUTPUT` as needed. Prefer full immutable hashes for both.
Set `MATRIX_SMOKE_SCOPE=smoke` for five scalable cases at larger sizes, `grid`
for the non-expensive grid, or `expensive` for the four excluded 10000-rule
single-add/AC cases. Nothing overwrites receipts: controls JSON and smoke JSON/
sibling logs must be new. Do not invoke real targets concurrently; smoke drivers
do not acquire the acceptance frontend's host-wide serial lock. Hosts with a
heap embedding a historical root must use the configured-root wrapper from
`../compatibility/tools/root-wrapper.sh`.

Optional serial real-integration discovery switches are `HOL_CLIENT_REPO` (an
absolute configured tree) and `RUNTIME_METRICS_SML=1`; the latter can retain its
source-tied receipt via `RUNTIME_METRICS_EVIDENCE=/new/path/evidence.json`.
Prefer the explicit `runtime-smoke` target for an archived runtime-only check.
All private smoke trees are automatically removed after use.

### Fresh loading commands

`loading.py` requires **both** `--baseline` and `--candidate` as exact full
commit hashes. A decision run's baseline is the develop pin
(`acceptance.BASE`) and its counts are fixed at 40 pairs of 5 fresh imports
per side, so neither `--pairs` nor `--reps` is given:

```sh
python3 -B src/simp/tests/performance/loading.py \
  --baseline DEVELOP_PIN_FULL_40_HEX_COMMIT \
  --candidate CANDIDATE_FULL_40_HEX_COMMIT --module simpLib \
  --api-audit /absolute/path/to/source-bound/receipt.json \
  --authorize-measurements --output /absolute/path/to/new-loading-simp
```

Repeat for `--module congLib` with a different output directory. When the
B/B control misses its window and nothing failed, `--extend RUN_DIR` runs the
one second stage. An explicit `--smoke` (with `--pairs`/`--reps`) may omit the
semantic receipt but gives no performance decision. The congLib import
includes simpLib, not marginal cost after it.
`success` means protocol completion; inspect every metric's decision. A fresh
semantic receipt alone is not startup timing or independent-build acceptance.

## Review-bundle inputs

`review-20261021/abicheck.sml` is the old-signature elaboration probe. It is
installed into every private tree by the paired runners and sealed by content
in the grid counts files, so it stays at this path, byte for byte.

## Maintained TASK_03 diagnostic harness

From the repository root, with **no other build or benchmark running**:

```sh
bin/Holmake --no-project --no-cache --no_prereqs \
  --holstate="$PWD/bin/hol.state0" \
  -C src/simp/tests/performance -j1 \
  PERFORMANCE_OUTPUT=/tmp/diagnostic-output diagnostic
```

The output directory must not exist from an earlier run. This now executes
maintained Python discovery (see TASK28 above), then six baseline/baseline
fresh-process pairs, their summary, then six baseline/candidate (`HEAD`)
pairs and their summary. Independent signature/staging checks and
all six negative controls execute on both selections before timings. Builds
finish before observations. Launcher/runtime/heap/dependency isolation is
provided by `../compatibility/run_paired.py`; its full schemas still apply.
This is **mixed-source isolation**, not independent clean repository builds.

Defaults: Poly/ML 5.9.2, `--gcthreads=1`, `hol.state0`, identical private-first
module paths/shared libraries, fixed 1,000 boolean assumption rules `ri = T`,
target `r0`, empty supplied assumptions. Every process starts a new theory,
calibrates each workload independently by doubling from one iteration until
wall >= 0.25 seconds, then records five raw batches after full GC outside the
timed region. Pair order is AB/BA alternating; every selection is a fresh
launcher process, not a repeated loop in one shared process. The runner
captures source/input/runtime/library/product hashes, options, loaded paths,
process exits and CPU affinity/load metadata. No outliers are discarded.

`Performance.sml` separates retained construction/projection from reuse and
also times complete operations. Every batch records wall, inclusive CPU
user/system, non-GC user/system, GC user/system and consumption, including all
calibration observations. Five forced GCs independently check timer accounting.
Poly's `checkCPUTimer` includes GC; `checkGCTime` is GC **user only**. Never add
GC to CPU. The validator requires the two timer views to
agree within 20 ms (sequential reads are not atomic); this is an accounting
sanity check, not a performance acceptance allowance.

### Output consumption and timed boundaries

| Label | Timed operation / consumption | Batch-end exercise (outside timing) |
| --- | --- | --- |
| `rewrites_1000` | Build/retain fragment; consume rewrite-list length | Compile retained fragment and verify rewrite |
| `merge_frags_1000` | Merge/retain fragment; consume rewrite-list length | Compile retained merge and verify rewrite |
| `compile_1000` | Compile/retain simpset; consume history length | Apply retained simpset |
| `delete_missing_1000` | Delete literal missing name; retain/consume history | Verify surviving installed rule |
| `project_1000` | Retain traversal data; consume reducer-list length | Construct and apply traversal from retained projection |
| `construct_traverse_1000` | Construct/retain conversion; increment sink | Apply retained closure |
| `empty_add_1000` | Add empty fragment to installed set; retain/consume history | Apply retained simpset |
| `simp_installed_1000` | Ordinary `SIMP_CONV` construction+application; verify theorem | Already checked per iteration |
| `raw_reuse_1000` | Apply saved traversal; verify theorem | Already checked per iteration |
| `projection_apply_1000` | Projection+construction+application; verify theorem | Already checked per iteration |
| `compile_apply_1000` | Compilation+ordinary application; verify theorem | Already checked per iteration |

Every construction result is stored in a typed escaping reference (never an
ignored return value); fragment/simpset/projection outputs additionally feed
a per-iteration checksum. Result slots remain live throughout each batch,
and the last produced output is exercised after **every** calibration/sample.
Closure construction has no portable cheap semantic observer: its checksum
counts constructions, and its retained closure is actually applied after the
batch. There is no claim to invoke every constructed closure in the isolated
construction timing; the complete projection/application workload covers that
boundary too. Timed theorem consumers check the exact conclusion, one expected
hypothesis and consume its length. The final sink must equal all recorded
consumed counts, with exact per-operation counts checked by the validator.
These probes include reference/checksum and theorem-check overhead equally on
both selections; sub-microsecond numbers are not raw API nanosecond costs.

### Retained graph words

Let `base = pureSimps.pure_ss`, `f = rewrites (take rules n)`, `ss = base ++ f`,
and `rs = take rules n`, for n = 0, 10, 100, 1,000. After applying a live rule
when n > 0 and full GC, record standalone sizes and these unions:

- Compiled increment: `objSize (base,f,ss) - objSize (base,f,base)`.
- Historical method: `objSize (ss,base,f) - objSize (base,f)`.
- Fragment increment: `objSize (base,rs,f) - objSize (base,rs,base)`.

`PolyML.objSize` counts reachable graph words with sharing counted once within
each root union; subtraction removes shared base/input objects. Equal-arity
roots remove the historical extra tuple word. Report both methods, n=0,
standalone/union/anchor sizes and all raw process repetitions. Code/closure
and preexisting shared objects can contribute to constant terms. Do not call
these RSS, allocated words, bytes, global roots or exact lifetime/release
measurements. Graphs remain rooted in each process until process exit.

### Statistics and interpretation

`summarize.py` recomputes complete schemas/order and uses a per-process median
of five per-operation batches, then paired candidate/baseline ratios. CPU,
wall and GC remain separate; GC ratios with zero denominators are undefined.
A fixed-seed 20,000-resample percentile bootstrap gives descriptive 95%
intervals for median paired ratios. Six pairs have limited statistical power;
small intervals do not prove universal equivalence. All raw observations and
iteration counts remain available. Baseline/baseline controls use the same
options before reviewed measurements. Noise is uncertainty, **not a pass**.
No aggregate score, fixed regression budget or offsetting fast traversal is
used. Ten or more paired observations and expanded matrices remain required
by final acceptance, not this diagnostic baseline.

The summary program assumes the runner's path validation already succeeded;
it independently revalidates metrics/order, not source provenance. Audit the
source/path bindings of the output directories as well:

```sh
python3 -B src/simp/tests/performance/audit_evidence.py \
  BASELINE_CONTROL_DIR REVIEWED_DIR CURRENT_HEAD_DIR
```

## Focused TASK_11 ordinary traversal diagnostic

`--traversal-performance` selects `TraversalPerformance.sml`, installed as
`Performance.sml` in each private source tree. It requires positive
`--performance-pairs`. The default fixture/schema remain unchanged. Manifest
`performance.suite = "traversal"` selects the six required labels and no storage
rows in validation, summary and offline source audit. Unknown suites fail.
The usual fresh-process ordering, timer control, exact consumption, exits,
source hashes and private path audits still apply; this fixture requires
`Traverse`, not `simpLib`, to be elaborated in its performance process.

All traversal data and input terms are prebuilt outside timing. The reducer
uses a single assumption equation, a private exception context and direct
term comparison. Its collector replaces that equation with the supplied
context equation. There are no simpLib representations/projections, rewrite
nets, Cond_rewr, extension APIs, trace listeners or production instrumentation.

| Label | Timed boundary | Consumed per iteration |
| --- | --- | --- |
| `construct_empty` | Retain raw conversion, empty supplied context | 1 retained output |
| `construct_context` | Retain raw conversion, one supplied equation | 1 output + 1 collector |
| `reuse_hit` | Saved contextual raw traversal, successful atom rewrite | 1 verified theorem |
| `reuse_miss` | Saved contextual traversal, distinct unchanged atom | 1 verified reflexive theorem |
| `complete_context` | Raw construction with context plus atom application | 1 theorem + 1 collector |
| `deep_factory_64` | Saved empty-context traversal of a unary spine | 1 theorem + 1 relation selection + 65 factories |

The miss probe uses a prebuilt `QCONV (TRY_CONV ...)` wrapper to turn raw
no-change failure into a reflexive theorem. Every timed application verifies
exact conclusion and hypothesis set against a kernel-built expected proof.
Construction slots escape and their last closure is applied/verified after
**every** calibration and batch, outside timing. The deep factory uses the
provided depther and `MK_COMB` to construct a genuine proof at every level;
it visits arguments, not function heads. Callback counter increments are
timed, and their batch deltas are folded into the sink after timer reads.
Out-of-timing setup/exercises cannot inflate measured callback consumption.
Schema checks require the exact per-iteration totals above and the complete
final sink. These diagnostics include symmetric checking/counter overhead;
they are not raw API nanosecond estimates. No allocation/graph-size claim is
made by this focused suite.

Run serially from the repository root, with no other build/benchmark active.
`CANDIDATE` must name a **committed** source snapshot: the runner extracts git
objects, not staged/working production files. Use fresh output paths.

```sh
python3 -B -m unittest discover -s src/simp/tests/performance -p 'test*.py'
python3 -B -m unittest discover -s src/simp/tests/compatibility -p test_runner.py
BASELINE=cccaa27d7099cbadc886983020cbe745db7793f3
CANDIDATE=your-committed-candidate-ref
python3 -B src/simp/tests/compatibility/run_paired.py \
  --baseline "$BASELINE" --candidate "$BASELINE" \
  --candidate-signature pass --candidate-behavior baseline \
  --traversal-performance --performance-pairs 10 --samples 5 \
  --batch-seconds 0.25 --timeout 1800 --output /tmp/traverse-control
python3 -B src/simp/tests/compatibility/run_paired.py \
  --baseline "$BASELINE" --candidate "$CANDIDATE" \
  --candidate-signature pass --candidate-behavior baseline \
  --traversal-performance --performance-pairs 10 --samples 5 \
  --batch-seconds 0.25 --timeout 1800 --output /tmp/traverse-candidate
for name in control candidate; do
  python3 -B src/simp/tests/performance/summarize.py \
    /tmp/traverse-$name --output /tmp/traverse-$name-summary.json
done
python3 -B src/simp/tests/performance/audit_evidence.py \
  /tmp/traverse-control /tmp/traverse-candidate
```

This isolates ordinary traversal from the existing `raw_reuse_1000` mixture
(including current net/Cond_rewr costs). It does not measure those costs,
project/compile work, extension performance, or overall simplifier acceptance.
Source identity and real paired receipts, not an assumed performance oracle,
are needed to distinguish unchanged traversal from costs elsewhere.

## Focused ordinary conditional-rewrite diagnostic

`--conditional-performance` selects `ConditionalPerformance.sml` and manifest
`performance.suite = "conditional"`. It requires positive performance pairs
and is mutually exclusive with `--traversal-performance`. Use the commands
above with this flag and fresh output paths. The fixture calls only ordinary
`Cond_rewr.COND_REWR_CONV`: no traversal, simpset/net construction, extension
API, or production instrumentation. Both online and archived inventories
require selected `Cond_rewr`, reject `Traverse` and `simpLib`, and exclude
extension modules identified from the selected source inventory. The fixture,
validator, audit and protocol tests are bound into the runner's input seals.

| Label | Timed boundary | Consumed per iteration |
| --- | --- | --- |
| `conditional_construct` | Retain conditional matcher before solver/stack application | 1 closure |
| `unconditional_construct` | Retain unconditional matcher at the same boundary | 1 closure |
| `conditional_reuse` | Apply saved conditional conversion | 1 verified proof + 1 solver callback |
| `conditional_complete` | Construct and apply conditional matcher | 1 verified proof + 1 solver callback |
| `ac_construct` | Retain variable-permutation matcher, unbounded | 1 closure |
| `ac_reuse` | Apply saved permutation matcher in descending AC order | 1 verified proof |

Every construction slot escapes and is applied after each calibration/sample,
outside timing. The conditional solver checks the instantiated condition and
stack; proof consumers check the exact conclusion and hypothesis set. The AC
setup checks that the opposite direction fails. Timer accounting, callback
deltas, final sink and process/pair auditing follow the traversal conventions.
`storage=False` deliberately omits the standard simpset storage rows. Retained
matcher graph/allocation auditing is separate; these batches make no
allocation or final performance acceptance claim.

## Allocation boundary

`allocation_boundary.json` lists what may differ from the measurement
baseline outside `src/simp/src`: prefixes and individually pinned files
(by blob). `Holmake boundary-tests` here is the cheap explicit check (about
2 s). It is not part of the routine build, because the boundary describes
this branch's measurement baseline. Run it whenever a shared file outside
`src/simp/src` changes; the TASK35 and TASK37 gates run it. It is a
tripwire: it fails on any committed change from the baseline to HEAD
outside `src/simp/src` and the manifest prefixes, including an edit to any
listed file, until the manifest is refreshed. The tests that need a git
work tree skip in a tarball or a checkout nested in another repository.
