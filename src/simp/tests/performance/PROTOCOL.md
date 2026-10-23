# TASK28 acceptance machinery

This is measurement infrastructure, **not final acceptance or independent-build
performance evidence**. Do not label shared `hol.state0` comparisons independent.
TASK29–33 and TASK37 own numerical gates and remaining prerequisites. Finite
measurements also need the corresponding source/layout/callback work audit.

## Isolated-source front end

From the repository root, after an exclusive build/measurement window has been
agreed with the coordinator:

```sh
python3 -B src/simp/tests/performance/acceptance.py run \
  --baseline BASELINE_FULL_40_HEX_COMMIT \
  --candidate CANDIDATE_FULL_40_HEX_COMMIT --case frag_create \
  --size 0 --size 1 --size 10 --size 100 --size 1000 --size 10000 \
  --pairs 10 --samples 5 --batch-seconds 0.2 \
  --authorize-measurements --output NEW_DIRECTORY
```

Repeat `--case` for another case. Sizes must belong to each case's exact grid
in `matrix.json`: rules/assumptions 0/1/10/100/1000/10000; depth 0/1/10/100;
numerals 1/10/100/1000/10000; atomic cases 0. Without `--size`, each case uses
1000 if supported, otherwise its largest grid size. The default baseline is
the pinned develop revision
`cccaa27d7099cbadc886983020cbe745db7793f3`. Both revisions must be exact full
commit IDs, not moving branch aliases. `run_paired.py` extracts those commits,
not uncommitted implementation changes. Its source/product inventories and
hashes remain part of each experiment. Unknown fixture cases fail closed.

The command runs harness-only controls, then **baseline/baseline and
baseline/candidate** for each requested case and size. Each child invocation is:

- the existing `tests/compatibility/run_paired.py`;
- `--matrix-performance --performance-case CASE --performance-size N`;
- `--candidate-signature pass --candidate-behavior baseline`;
- identical samples, batch duration, process timeout, and >=10 pairs.

A baseline control uses the baseline commit in both selection slots. It has the
same sample counts, fresh processes, calibration and AB/BA order as its candidate
comparison. No control costs are subtracted and no baseline variability is a
regression budget. A baseline-control `fail` invalidates a candidate `pass`
(turning it inconclusive); a candidate failure is never excused by control noise.

The SML harness consumes and verifies construction, reuse and complete-operation
results. The Python schema contract is `suite="matrix", case=CASE, size=N`, one
label CASE, consumption 1 per operation, and `storage=False` (not the old fixed
storage-row protocol). Process environment includes `PERF_CASE` and `PERF_SIZE`.
The installed `Performance.sml` must match the recorded MatrixPerformance or
ClientPerformance input hash. Callback/proof verification belongs in the fixture;
a nonzero exit, missing observation or ignored result is not an observation.

Acceptance requires >=10 fresh **process pairs**, not merely ten batches in one
process. Each process calibrates by doubling iterations. Every measured batch
must last at least half the calibration target, with >=3 measured batches.
Process pair order is AB, BA, AB, BA, ... with no missing, duplicate or reordered
receipts. Warm-up/calibration work is recorded separately, not silently counted
as independent samples. Increase the predeclared batch duration for tiny work.

## Runtime, graph and release records

Both matrix fixtures load sealed `RuntimeMetrics.sml`. Every calibration and
sample has exactly one `@@MATRIX_RUNTIME` record matched in order to its stage
and iteration count. Before/after snapshots supply actual full/partial GC and
sharing-pass counts, GC-updated heap/free sizes, allocation-area capacity/free
space and Linux `/proc/self/status` RSS/HWM bytes. Snapshot/record work is outside
timing; counts are batch-boundary counters with small record/timer overhead,
not cycle-exact attribution. `/proc` reads and semantic verification are outside
the counter interval. Missing RSS is explicitly blocked, not zero.
Linux documents these RSS fields as approximate: an observed raw VmHWM
regression blocks RSS/high-water inference for that process. Raw values remain
unchanged, never clamped; valid timing/GC observations remain independent.

`storage_graph` also emits a separate reachable-word `@@MATRIX_STORAGE` record
and a `@@MATRIX_RELEASE` probe. Online runner and archived `audit_evidence.py`
reparse and compare graph/runtime/release records, fixture seals, stage/counts
and arithmetic. Acceptance reports preserve per-pair telemetry and separately
compare compiled/fragment graph increments. `--case storage_graph` with all six
`--size` values additionally compares every adjacent words-per-rule interval,
including 0-to-1, and reports size-zero terms separately. Missing sizes block
slope conclusions; no fitted slope or aggregate hides nonlinear differences.

Scope limits are mandatory:

- Poly/ML 5.9.2 exposes no cumulative allocated-byte counter. Heap/free or
  allocation-area sizes are not total allocation; that field is uncollected.
- VmHWM is the **process-lifetime** maximum including loading and prior batches.
  HWM increases and RSS snapshots are measured, not exact temporary peaks.
  An isolated high-water accounting domain remains unestablished. A zero HWM
  increase is not evidence of zero temporary memory.
- Release checks a live conversion's controlled simpset **ref**, then observes
  actual weak collection after dropping the wrapper and three full GCs.
  `Weak.weak` accepts refs only, not opaque internal simpset/net objects.
  A passing probe cannot exclude independent global roots retaining those
  objects; the stronger lifetime gate remains blocked.

An untimed runtime selftest is separate from acceptance:

```sh
python3 -B src/simp/tests/performance/runtime_metrics.py \
  --baseline BASELINE_FULL_40_HEX_COMMIT \
  --candidate CANDIDATE_FULL_40_HEX_COMMIT --output NEW_RUNTIME_JSON
```

It needs a configured tree and a new sibling `.log` path. Run alone; unlike
`acceptance.py`/`loading.py`, smoke drivers do not take the host-wide serial lock.
They clean private trees automatically, retaining compact source-tied receipts.

## Statistics and decisions

Fixed before candidate results are observed:

1. Discard **no outliers**, batches or process pairs. No trimming or rerunning
   just unfavorable observations. Any rerun is a new whole experiment.
2. Within each process, take the median batch cost per operation separately for
   inclusive CPU, wall, and GC. Poly/ML CPU includes GC; do not add GC again.
   Validate nongc+GC accounting and the positive-GC timer control first.
3. Form candidate/baseline ratios within each process pair. Report raw process
   observations, both medians, every ratio and their median. Do not replace paired
   ratios with a ratio of pooled medians or pool workloads together.
4. Bootstrap the **paired ratios**: 20,000 resamples, deterministic seed 3003,
   percentile ranks 499/19499 (zero-based), the existing `summarize.interval`.
5. For each workload/size/metric: CI lower bound >1 means **fail**; upper bound
   <=1 means **pass**; otherwise **inconclusive**. A reproducible slowdown of any
   size fails. No fixed percent allowance, aggregate mean or compensating speedup.
6. A zero denominator, including GC 0/0, means inconclusive with null ratio/CI;
   keep the pair and raw values. Do not turn undefined GC ratios into parity.

`acceptance.json` records the policy, source-tied raw experiment input hashes,
runner commands/log hashes/exits, controls and per-metric decisions. Archived
results are revalidated through the existing schema and source-binding auditor,
plus ordered heap/search/use/completion/loaded inventories and fixture/options
checks. A precomputed summary is not sufficient evidence.

CLI exit codes: 0 = all reported candidate metrics pass; 1 = at least one fails;
2 = uncertainty, invalid evidence or a blocked prerequisite. `success=true`
means the experiment completed and validated, **not that its metrics passed**.
No overall performance acceptance decision substitutes for per-metric decisions.

## Negative controls

```sh
python3 -B src/simp/tests/performance/acceptance.py controls \
  --output NEW_CONTROL_JSON
PYTHONDONTWRITEBYTECODE=1 python3 -B -m unittest discover \
  -s src/simp/tests/performance -p test_acceptance.py -v
```

Controls are separate real Python subprocesses, never production-source edits:

- slowdown: candidate performs a longer measured CPU loop;
- allocation: candidate retains a larger bytearray, measured by `tracemalloc`;
- failed process: emits a result but exits 7; rejection must be the exit guard;
- missing result: exits 0 without output; rejection must be the missing guard.

The positive baseline worker verifies the allocated bytes and consumed work.
Slowdown/allocation controls use ten paired fresh subprocess observations in
AB/BA order and must produce strict CI failures. The tests execute these real
perturbations, not just construct invented ratios or assert an arbitrary error.
Synthetic statistics and tampered archived/build receipts additionally exercise
thresholds, undefined GC, completeness, provenance and stale-build guards.
`tracemalloc` is **only a Python harness allocation control**, never a measurement
of HOL/PolyML allocation. Bootstrap confidence is not a universal hardware proof.

## Serialization

`run` and `controls` hold nonblocking `flock` locks for their entire experiment:

- `/tmp/hol4-performance-UID.lock` (one per host user, across repositories);
- the repository gitdir inode (compatible with existing exclusions/tactics
  runners), and common gitdir inode (across worktrees).

Descriptors are inherited by the paired runner so it cannot continue unlocked
if its parent exits. A busy lock blocks the invocation. Never unlink a lockfile:
that permits two different inodes to be locked concurrently. Do not relock these
inherited locks in child runners. All invocations of this front end serialize;
the existing gitdir lock also conflicts with older same-worktree runners.
Locks are advisory: they cannot stop unrelated manual `bin/build`, direct older
runners in other worktrees, or other users. Authorization confirms those are
quiescent. Do not use `--authorize-measurements` as permission for concurrent work.
Unit tests acquire the same lock for actual timing controls; other tests create
only tiny temporary synthetic git repositories and remove them immediately.

## Independent-build admission: fail closed

`verify-builds` audits a separately produced clean-build receipt against **live**
roots and logs. It does not build, run proof workloads, or approve performance:

```sh
python3 -B src/simp/tests/performance/acceptance.py verify-builds BUILD_JSON \
  --baseline BASELINE_FULL_40_HEX_COMMIT \
  --candidate CANDIDATE_FULL_40_HEX_COMMIT
```

`run --mode independent --build-manifest BUILD_JSON ...` performs that same
admission and then explicitly reports the independent measurement prerequisite
blocked. It **never runs `run_paired.py` and labels that independent**. Fresh
independent launchers, loaded-path inventories and consumed proof/storage pairs
must be supplied by TASK32/33. No actual independent HOL builds were performed
or claimed while implementing this machinery.

The external receipt producer must run serially under the same locks, in two
new disjoint clean worktrees at the requested pins. Refuse an existing product,
heap, theory cache, ignored or untracked file before configuration; never simply
stamp an old product with a new mtime. Build logs and receipts live outside both
roots. Preserve them until live verification completes. Required commands in
each selected root, using the exact same Poly/ML executable:

```sh
/absolute/path/to/poly < tools/smart-configure.sml
/absolute/selected/root/bin/build -t -F
```

Bare `bin/build` or an inherited partial sequence is insufficient. Record
`git status --porcelain=v1 --untracked-files=all` and the same with
`--ignored=matching` **before** configuration; both must be empty. Record every
command's start/end nanoseconds, cwd, argv, stdin hash, executable hash, log
path/hash, actual exit and timeout status. Hash tools and products while
unchanged; roots must still be at the exact pins with no tracked/untracked
changes during admission (ignored generated products are allowed after building).

### Independent manifest v1

Required top-level fields:

- `schema`: `task28-independent-build-v1`;
- `mode`: `independent`; `success`: true;
- `runtime_options`: `["--gcthreads=1"]`;
- `toolchain`: map including `poly` with absolute `path`, nonempty `version`, and
  `fingerprint: {sha256: HEX, bytes: INTEGER}`. Admission executes
  `poly --version` and requires its successful Poly/ML output to match `version`
  exactly. Include other external tools too;
- `selections`: exactly `baseline` and `candidate`.

Each selection contains:

- `root`: absolute worktree root; `pin`: exact requested commit;
- `fresh_before`: true; `status_before`: ""; `ignored_before`: "";
- `start_ns`, `end_ns`: ordered, nonoverlapping build intervals;
- `commands`: ordered configure/full records as above; fields are `phase`,
  `argv`, `cwd`, `exit`, `timed_out`, `start_ns`, `end_ns`, `executable_hash`,
  `stdin`, `stdin_hash`, `log`, `log_hash`. `stdin` is the absolute
  `tools/smart-configure.sml` for configure, null for full; full stdin hash is
  null. Configure argv is only the recorded poly path; full argv is exactly
  `[ROOT/bin/build, "-t", "-F"]`;
- `products`: map of root-relative logical names to `{path, physical, hash,
  mtime_ns}`. `path` is the absolute logical name, `physical` its resolved file,
  `hash` is `{sha256, bytes}`. Require `bin/hol`, `bin/hol.state0`,
  `bin/hol.state.min`, `bin/Holmake`, `holproject.toml`, plus every generated
  `.uo`/`.ui`/`.dat` reachable under `sigobj/`;
- `dependency_inventory`: exactly those sigobj product names. Source `.sig`
  links are not compiled artifacts and are not subject to the freshness mtime
  check; source pins and the later loaded-source inventory cover those.

A product's current mtime must equal the recorded mtime and lie inside that
selection's fresh build interval. Symlinks are allowed only when their targets
remain inside the selected root; no cross-root product or shared product inode
is accepted. Hashes, required products, tool versions, logs, exits, configure
input and command/options are mandatory. Missing or changed prerequisites reject
admission. Unsupported build recipes/platforms remain blocked until a separately
reviewed manifest schema supports them; do not weaken this verifier to admit an
old heap. A local receipt is a provenance record, not a cryptographic attestation
against a malicious producer. Preserve actual pristine-state evidence too.

## Fresh loading: runnable external gate

`loading.py` now times actual first imports in fresh shared-heap processes,
with one pilot per revision, >=10 AB/BA pairs, baseline/baseline controls and
raw CPU/wall/GC. It requires **both** exact commit options and a source-bound
eight-process API-audit receipt (except explicit non-acceptance smoke):

```sh
python3 -B src/simp/tests/performance/loading.py \
  --baseline BASELINE_FULL_40_HEX_COMMIT \
  --candidate CANDIDATE_FULL_40_HEX_COMMIT --module simpLib --pairs 10 \
  --api-audit /absolute/path/to/receipt.json \
  --authorize-measurements --output NEW_LOADING_DIRECTORY
```

Repeat for `--module congLib` in a different output directory; this includes
its simpLib dependency, not marginal congLib cost. Pilots/empty brackets check
resolution, not a cached same-process import loop. Source paths, completions,
actual successful exits and exact kernel proofs are checked. See
[`PROTOCOL_LOADING.md`](PROTOCOL_LOADING.md). Listing this executable external
gate does not claim a fresh run or independent loading acceptance.

## Matrix boundaries and final evidence

[`MATRIX.md`](MATRIX.md) and the frozen schema cover **69 requirements and 107
case bindings**. Runnable does not mean measured or passed. All named stages
and declared sizes remain distinct; a smoke cannot cover the full matrix.
Graph parsing, batch GC counts, RSS snapshots and controlled-ref release are
integrated, not missing instrumentation. Seven stronger prerequisites remain:
unsupported cumulative allocation counter; unestablished exact temporary-peak
domain; unsupported opaque-object lifetime API; missing independent integer
and real dependencies; independent routine and full clean snapshots/results.

The main ten-pair source-isolation experiment validates end-to-end machinery,
not matrix-wide performance approval. Only current fixture/source-tied manifests
and raw observations count; unused temporary validation or earlier fixture
versions cannot be relabeled final. Independent manifest admission validates
build prerequisites only and `run --mode independent` still blocks pending
fresh independent launchers, path inventories and consumed proof/storage pairs.
No shared `hol.state0` result becomes independent by changing a report label.

Ordinary arithmetic/reduce/boss fixtures are runnable with shared dependencies;
independent downstream proof/build acceptance and migrated-consumer costs remain
separate. Keep normal ordinary/extension suites enabled. Passing Python tests,
smokes or controls establishes machinery behavior, not numerical parity or the
final release gate. See [`README.md`](README.md) for maintained check targets.
