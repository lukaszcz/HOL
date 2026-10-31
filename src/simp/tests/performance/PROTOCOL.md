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
regression budget. A baseline-control `fail` or `inconclusive` prevents a
candidate pass (turning it inconclusive); a candidate failure is never excused
by control noise. This applies to point metrics and retained-storage slopes.

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

### Equal-count attribution

Independent time-based calibration can choose different iteration counts in
paired selections. Per-operation normalization does not remove nonlinear GC
and heap-sizing effects. For a predeclared common operation count, add
`--batch-iterations N` to `acceptance.py run` (or the matrix paired runner).
`N` must be a power of two in 1..1073741824. The front end passes the **same N**
to B/B and B/C; every process performs **all** calibrations 1,2,...,N, even if
an earlier calibration reaches the duration target, then every sample uses N.
This fixes operation counts and calibration history, not the resulting heap
state or GC schedule. Record both; identical GC behavior is not assumed.

The final calibration must still reach `--batch-seconds`; every sample must
still reach half that target. A short fixed experiment fails closed, never
silently recalibrates one side, drops a pair or selects a favorable repetition.
Choose the schedule before observing the new experiment. A new schedule is a
new whole experiment, with prior observations preserved. Fixed mode is matrix
only (both fragment and client fixtures); omitting it retains the historical
adaptive protocol for replay, not proof that its GC comparisons are unconfounded.

The count is bound to the manifest, `PERF_ITERATIONS` environment, complete
ordered calibrations, samples and consumed-result counts by online and offline
validation. Injecting that environment variable into an adaptive archive also
rejects. `analyze(..., iterations=N)` must match the requested schedule; default
analysis cannot silently admit fixed-mode evidence. No timing, GC, control,
confidence-interval or pass/fail threshold changes with this mode. In particular,
equal counts cannot turn uncertain B/B controls or zero/zero GC into passes.
See `TASK_29_HANDOFF.md` for the still-failing ten-pair equal-count experiment.

### Precompiled experiment driver

Both matrix fixtures now compile calibration AND sampling inside `experiment`
before either executes. The calibrated count is a runtime local, not a global
constant available when the compiler subsequently builds `sample`. This also
removes intervening sample-compilation allocations. The workload, complete
calibration history, result checks, timers and decision policy are unchanged.
Earlier fixture receipts remain historical observations, not acceptance for
this changed driver; all affected numerical gates require fresh experiments.
This repair is not a causal explanation or closure of their failures.

`Holmake check` executes `driver-staging-control` before semantic smokes. The
Holmake-built `driver-staging/selftest.sml` compiles the exact live driver
suffixes through the same HOLSource reader as QUse. A compiler-entry serial
must remain fixed from first calibration to last sample. Synthetic durations
exercise adaptive and fixed schedules, complete observation fields and short
calibration rejection. Reinstating the old top-level count must trigger the
serial guard for BOTH fixtures. These 36 assertions are scheduling tests, not
HOL timing or allocation measurements. Run separately from the repository root:

```sh
W bin/Holmake --no-project --no-cache --no_prereqs \
  -C src/simp/tests/performance -j1 driver-staging-control
```

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
slope conclusions and makes the CLI exit 2 unless another metric fails
(exit 1). Measured candidate slopes participate in CLI decisions just like
point metrics, including their baseline controls and uncertainty. No fitted
slope or aggregate hides nonlinear differences.

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

Rule 5 is `POLICY` (version 1). It tests whether the candidate is *faster*:
a candidate with no real difference passes one metric about 3% of the time,
and its B/B control must pass the same way, so a performance-neutral change
cannot pass a grid. Every archive before TASK29A's rerun used it and still
replays under it.

### Equivalence policy (version 2, TASK29A policy-owner disposition)

Decided by the policy owner on 2026-10-26; `acceptance.EQUIVALENCE_POLICY`.
`acceptance.py run` and `task29a_grid.py` record it in every new report, and
offline replay uses the policy a report recorded. Rules 1–4 and 6 are unchanged.

- **Margin** δ = 0.03 on inclusive CPU and wall. Lower bound > 1+δ: **fail**;
  upper bound <= 1+δ: **pass**; otherwise **inconclusive**.
- **Control validity.** The B/B interval for the same metric must lie within
  [1/(1+δ), 1+δ]; otherwise the candidate cannot pass. An invalid control
  never excuses a failure.
- **GC** time is reported with its interval, not gated (decision
  `reported`): inclusive CPU already contains it.
- **Storage** graph words and retained slopes keep the zero-margin rule.
- **Counts and size.** `task29a_grid.py` gives every process of a cell the
  same predeclared batch count, derived only from develop/develop processes of
  the historical grid (`evidence/task29a/iterations.json`). Pairs and samples
  are run options (minimum ten and three), fixed before the run and recorded
  in its inventory.

#### Code-layout randomization and second stage (TASK29A)

Every fresh process compiles its selected sources at startup, so the address
of all later code depends on everything compiled before it. On the measured
host (Linux/aarch64, Neoverse-V2, Poly/ML 5.9.2) this alone moves the
per-operation cost of the large fragment cells by up to ±10%. Develop
processes with the same code-area size run alike, and both B/B sides share
one layout. A source change elsewhere that moves the layout therefore looks
like a slowdown or speedup at a fixed layout (`evidence/task29a/attribution/`).

- `--layout-seed S` (`run_paired.py`, `acceptance.py run`,
  `task29a_grid.py run`) sets `PERF_LAYOUT` for every matrix process to
  `sha256("S:pair:selection") mod 128`. `runner.sml` compiles that many
  one-line padding functions (about 200 code bytes each) before loading any
  dependency, and emits no event. Baseline and candidate draw independently.
  The manifest records the seed and range, and the audit re-derives every
  receipt's value. Without a seed nothing changes, and older archives replay
  as before.
- **Second stage** (`task29a_grid.py extend --grid G`), predeclared with the
  first-stage grid. A cell is measured again when its B/B control misses the
  window for CPU or wall and its candidate did not fail. The pair count is
  `20·(w/0.015)²` rounded up to tens, between twice the first-stage pairs
  and 120, where `w` is half the log-width of the widest such control
  interval. Only develop/develop data choose the cells and counts; a fail is
  final, so the candidate can only add fails. Each remeasurement is a fresh
  experiment with seed `S-ext`. It replaces the first-stage cell, whatever
  its own outcome. `replay` re-derives the plan from the first-stage
  archives and replays both stages.
- `--resume` continues a run or second stage interrupted by an
  infrastructure failure (for example a full disk), with identical settings.
  Recorded cells are replayed and kept; an unrecorded cell is measured
  again from scratch.
- **Disposition** (`task29a_grid.py dispose --output STAGE2`, decided by
  the policy owner on 2026-10-30). It replays both stages and leaves every
  measured decision unchanged. It then classifies each final cell:
  - pass;
  - *unresolvable*: every open metric is inconclusive only because its
    B/B control is still outside the window after the second stage;
  - *attributed*: one of an explicit list of cells, each with a recorded
    reason, which must match the open cells exactly;
  - blocking or fail.

  A fail, a protocol failure, a retained-scaling miss or any other
  inconclusive cell blocks. `--record` writes `disposition.json`, and
  later runs check it.

#### Shared timing grid and the TASK30 table

`timing_grid.py` is the TASK29A grid with the task-specific parts removed.
A task supplies a `Table` (cases, batch seconds, predeclared counts file,
sealed code, historical seals); the policy, the layout randomization, the
second stage, the archives, `--resume` and `replay` are the ones above and do
not change. `task29a_grid.py` is its TASK29A table plus the TASK29A
disposition; `task30_grid.py` is the TASK30 table (24 cases, 144 cells) and
has no disposition.

- **Cells.** The sizes of a case come from the matrix ledger. A cell is
  `case-size`.
- **Predeclared counts.** Every process of a cell runs one batch count,
  chosen before any candidate observation from develop-only processes.
  `pilot` runs, for each cell, a baseline-versus-baseline experiment
  (`--pairs`, `--samples`, default ten and three) with free calibration and
  archives it losslessly; no candidate and no layout seed take part. The
  baseline must be the table's (`task30_grid.py` names it). Beside
  `inventory.json` it publishes `variability.json`: for each cell the median
  and 95% interval of every metric's paired ratio, and for the gated metrics
  whether the interval lies in the equivalence window, so that the host's
  noise is on record before any candidate is measured. A cell that fails is
  kept as `<cell>.json.xz.failed-N` and is measured again by `--resume`.
- **The counts file is the predeclaration.**
  `predeclare --grid PILOT --output FILE --layout-seed SEED --pairs P
  --samples S` (pairs and samples default to the table's; the seed is
  required) writes `HEADROOM * max(final calibration count)` for each cell
  (the calibration counts are powers of two, as a batch count must be;
  `HEADROOM` 2) and refuses to overwrite. The file also carries the baseline,
  the rule, each cell's batch seconds, the layout seed, pairs and samples of
  the run, the seal of the pilot's driver, the seal of the pilot's inventory
  and the seal of every cell's archive. `verify-counts --grid PILOT
  [--counts FILE]` re-derives the file from the pilot's archives and its own
  settings and refuses any difference (the pilot's code need not be the
  current code for that). The file is reviewed and committed before the first
  candidate observation.
- **What `run` takes from the counts file.** The counts must be the table's
  file, byte for byte, and the baseline of the counts, of the table and of
  `--baseline` must agree; a candidate equal to the baseline is refused. The
  layout seed, pairs and samples come from the file, and a different explicit
  `--layout-seed`, `--pairs` or `--samples` is refused (the second-stage
  seed `SEED-ext` must be valid too, so the seed is at most 60 characters).
  The candidate's own tree must hold the file as it is (same git blob), and
  the inventory records the commit that introduced it as `counts_commit`: the
  counts were committed no later than the candidate, and so before it could be
  measured. `inventory["seconds"]` is only the table's default; the seconds of
  a cell are those in `iterations.seconds`. Every replay checks the header
  against the committed counts file.
- **Batch seconds.** A table gives all cells one calibration target and may
  name a longer one for cases whose single operation is tiny, so that a
  batch stands clear of the per-batch overhead (the ten direct deletions of
  TASK30 use 1 s, the others 0.3 s). The seconds are part of the counts
  file, checked by `run`, and used again by `replay`.
- **Source identity.** The operations of TASK30 run through source files
  that the candidate may have changed: `task30_cases.SOURCES` lists them
  (`simpLib`, `Ho_Net`, `BoundedRewrites`, `Traverse`, `Travrules`,
  `Opening`, `Cond_rewr`, `Trace` and `markerLib`, each `.sml` and `.sig`).
  `run` records the git blob of each file at the baseline and at the
  candidate in the inventory and prints every file that differs
  (`SOURCE-DIFFERS path`). Such a grid is never a pass: its decisions name
  the files in `source_identity` and a status that would be `pass` becomes
  `inconclusive`, whatever the cells say. `replay` and the second stage
  re-verify the record against git. This is the evidence for "no extra
  source scan": neither gate sees a scan that allocates nothing and costs a
  few percent, so the identity of the code on the path, not a measurement,
  shows that no scan was added there. A scan elsewhere is outside this list.
- **Decisions.** `run` prints, and the exit status reflects, five separate
  lists: pass; *fail*; *inconclusive*; *control-limited* (every open metric
  is inconclusive only because its B/B control is outside the window);
  *protocol* (no admitted measurement). The exit status is zero only when
  every cell and the retained slope pass, one when anything failed, two
  otherwise. The lists are derived from `decisions.json` and `replay`
  prints them again. No cell is excused: a task that accepts a
  non-passing cell does so in a separate, reviewed table (as TASK29A did),
  outside the engine.
- **Whole operations.** The timed operation is the fixture's complete
  `run`, and its result is verified in the same process, so work cannot move
  into unmeasured preprocessing: a batch contains the construction or call
  being gated and whatever it needs. The fixtures assert the callback
  counts of the maker and collector cases (`history_collectors`,
  `history_makers`) exactly and check the resulting simpset of every
  deletion; `exclude_dproc` and `exclude_mixed` assert that the deletion
  calls no maker and no collector (zero of each: `-*` runs neither). They do
  not count scans, and production records none. The
  allocation matrix (`allocation_matrix.py --task task30`) brackets setup,
  first and steady operation and verification of all 24 cases and compares
  exact allocation words and their size slopes between the sides.
- **`history_theory_change`.** The two gates cover different parts of this
  case. The timing gate runs the real transition: `new_theory` in a `hol run`
  process exports the theory, and the batch includes that cost. The
  allocation gate covers the replay and the reparse under the restored
  context, with no `new_theory`: the export has clock- and pid-dependent
  words and writes below the working directory, which the sealed private
  selection must not see change. The fixture sets `MatrixSupport.theoryChange`
  to a no-op in `MatrixAllocation.sml`; the reparse is driven by the
  `Context.restore` that drops the linked theory, and the verification still
  requires the exact "bad theory name" error. `Globals.interactive` is not
  set (it would delete the constants the fixture uses). So the cost of the
  export itself has no allocation gate, only the timing gate.
- **Pilot method for a new task.**

      python3 -B task30_grid.py pilot --output OUT/pilot \
          --authorize-measurements
      python3 -B task30_grid.py predeclare --grid OUT/pilot \
          --layout-seed SEED --pairs 20 --samples 5 \
          --output OUT/task30_iterations.json
      python3 -B task30_grid.py verify-counts --grid OUT/pilot \
          --counts OUT/task30_iterations.json

  The pilot needs the exclusive measurement window, like `run`.
  `OUT/pilot/inventory.json` lists every archive and its calibration counts.
  Review the counts file, then copy it to `task30_iterations.json` and commit
  it before the candidate is measured; `--resume` continues an interrupted
  pilot as it does a run.
- **Grid.**

      python3 -B task30_grid.py run --candidate SHA --output OUT/grid \
          --authorize-measurements
      python3 -B task30_grid.py extend --grid OUT/grid --output OUT/stage2 \
          --authorize-measurements
      python3 -B task30_grid.py replay --output OUT/stage2

  `run` takes the layout seed, pairs and samples from the counts file and is
  refused without a seed. `--resume` continues an interrupted `run`, `extend`
  or `pilot`; `replay --partial` replays the finished cells of an
  interrupted one. `replay` of a pilot is refused: a pilot is checked by
  `verify-counts`.
- **A cell that is too short.** A cell rejected as "fixed calibration too
  short" is a non-pass and blocks the grid. The only route is a new committed
  counts revision that multiplies that cell's count by 4 for baseline and
  candidate alike, and a full rerun of that cell's pairs; the first result
  stays published. No code changes for it: the ordinary exclusion path
  (`simpLib`) is identical to develop (see source identity), so a candidate
  that runs twice as fast as the baseline is not expected, and a count that
  proves too short is a property of the pilot.
- **Allocation gate prerequisite.** A TASK30 allocation run
  (`allocation_matrix.py run --task task30`) needs a controls receipt taken
  at the candidate: `acceptance.py` and `task30_cases.py` are harness inputs
  of that gate, so a receipt of an earlier harness, or a TASK29B run resumed
  across them, is refused.
- **Cost.** The grid is 144 cells at 20 pairs and two slots per pair, each
  slot a fresh process with its batch (0.3 s, or 1.0 s for the ten direct
  deletions at every size, including 10000): about two to three days of
  exclusive window for the first stage, plus a second stage for the cells the
  control leaves open.
- **Other tables.** `task29a_grid.py` gains `pilot`, `verify-counts` and the
  class report with the engine; its recorded runs and the TASK29B allocation
  schema names (`task29b-*`, kept by the TASK30 gate) are unaffected.

`acceptance.json` records the policy, source-tied raw experiment input hashes,
runner commands/log hashes/exits, controls and per-metric decisions. Archived
results are revalidated through the existing schema and source-binding auditor,
plus ordered heap/search/use/completion/loaded inventories and fixture/options
checks. A precomputed summary is not sufficient evidence.

Matrix manifests require `shared_inputs`: an inventory keyed by canonical
absolute logical source path, with physical path, SHA256, byte count and the
complete related `.uo`/`.ui`/`.dat` product fingerprints. The online runner
checks these against live files and across all accepted processes before
sealing the manifest. Offline admission binds every shared receipt entry to
that inventory, including all related products, and rejects non-normalized or
escaping paths without resolving deleted roots. Private sources and products
remain bound to their selected inventories. Matrix archives predating this
inventory are historical diagnostics only; do not reconstruct a supposedly
independent inventory from the receipts being validated.

Admission also requires exact runtime options (one GC thread and the recorded
repo's `hol.state0`), runtime/heaps/Holmake/configuration fingerprints, a sealed
successful Poly/ML version command, sealed successful dynamic-library discovery
and fingerprints for its libraries. Selected builds must have succeeded, and
each launcher's text, options and product hash must agree. These are local
provenance-consistency checks, not authentication of a malicious producer or
independent-build evidence. Non-matrix historical diagnostic audits retain
their original weaker contract.

CLI exit codes: 0 = all reported candidate metrics/slopes pass; 1 = any fails;
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

- `.agent-files/hol4-performance-UID.lock` in the repository (one per
  user; ignored, and out of reach of shared `/tmp` cleaners, one of which
  deleted the earlier `/tmp` lock during the TASK29A grid);
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
