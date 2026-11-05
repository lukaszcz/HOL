# TASK28 acceptance machinery

This is measurement infrastructure, **not final acceptance or independent-build
performance evidence**. Do not label shared `hol.state0` comparisons independent.
TASK29–33 and TASK37 own numerical gates and remaining prerequisites. Finite
measurements also need the corresponding source/layout/callback work audit.

## Isolated-source front end

From the repository root. The host is shared and no exclusive window is
required; a checkout's own builds and measurements stay serial, under its lock:

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
Under the `ramp` schedule (the default of the option and of a record; the
`warmup` schedule below differs, and is the default of a new table) `N`
must be a power of two in 1..1073741824. The front end passes the **same N**
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

#### The `warmup` schedule

The doubling history costs 20-26% of a process of the TASK30 grid. Add
`--batch-schedule warmup` (with `--batch-iterations N`; the environment
`PERF_SCHEDULE=warmup`, the option `batch_schedule` of the manifest) for a
second fixed-count schedule: a process runs **one warm-up batch of exactly N
iterations** and then the samples of N, instead of the batches 1, 2, ..., N.
`N` is then any integer in 1..1073741824, not only a power of two. Both
selections of every experiment get the same N and schedule.

- **Records.** The warm-up is observed as `warmup.<label>` (the SML drivers
  still write its runtime record under the stage `calibration`), is kept as
  the only entry of the label's `calibration` and the workload says
  `schedule: warmup`. It is not a sample. The warm-up and every sample must
  last at least half of `--batch-seconds`; a short one fails closed, as
  above (the warm-up as "warm-up batch too short; new experiment required",
  a sample as "batch too short; recalibrate"), without recalibrating one
  side. The consumed-result count of the warm-up is checked like a
  sample's.
- **`ramp` is the default of a record and is not written down.** An option,
  environment or event of one schedule in a record of the other is refused,
  and a literal `ramp` in an option or environment is refused too: the
  historical protocol is the absence of the field, so every record made
  before this schedule existed validates, audits and replays byte for byte as
  before.
  `analyze(..., schedule=...)` must match the requested schedule, as
  `iterations` does, and `PERF_SCHEDULE` is bound by `audit_evidence.py` for
  every receipt. One rule for every function that takes a schedule
  (`analyze`, `validate`, `batch_iterations`;
  `performance_schema.named_schedule`): a caller names the ramp as `None`
  or as `"ramp"`, which are the same. On the command lines
  (`--batch-schedule ramp`) `ramp` is normalised to no field after the
  check that a schedule needs `--batch-iterations`, which `ramp` needs
  like `warmup`.
- **The count rule** (`timing_grid.warmup_count`, used by a table of this
  schedule): `N = max over the develop-only pilot processes of
  ceil(HEADROOM * seconds * n / wall)`, where `n` iterations and `wall`
  seconds are the final calibration batch of one process and `seconds` the
  cell's batch seconds, computed in exact arithmetic on the recorded decimals.
  New tables use `HEADROOM` 1, so that a batch lasts about the target: N is
  the count that takes `seconds` in the process of the pilot that was fastest
  per iteration at its final batch, so a batch of any pilot process would
  last at least the target at that speed, and a batch is shorter than half of
  it only if a process (a candidate included) runs more than twice as fast
  per iteration as that fastest pilot process. TASK_30 candidate ratios lie
  in 0.79-1.06, far from 2, and a slower process only lengthens its batches.
  A cell where it does happen fails closed, and the revision path below
  multiplies its count by 4 (reason "fixed batch too short" for this
  schedule). The counts file records the schedule, the rule and the headroom;
  `verify-counts` and every replay derive them again from the pilot.
- **What the count rule assumes.** (1) Time is linear in the iterations of a
  batch: N is extrapolated down from the final batch of the pilot, and with
  headroom 1 and `wall >= seconds` N is never above `n`. A workload whose
  cost per iteration grows inside a batch (state kept until `afterBatch`) has
  a batch of N shorter than `seconds * N / n`: with `wall(n) = 2 * seconds`
  and a quadratic cost, a batch of N = n/2 lasts about `seconds / 2`, the
  edge of the check. (2) The final batch of a pilot process is selected
  because its wall reached `seconds`, which biases that wall up a little (by
  the noise), and N down by as much. Both fail closed (a batch under half the
  target is refused, never used) and the revision by 4 recovers, so the cost
  is a rerun. Load on the host during the pilot can only lengthen a pilot
  batch, so only raise N: the maximum over processes takes the fastest, least
  loaded one. The validation recorded, per cell, the least of (warm-up or
  sample wall) / `seconds`, so that the margin to 0.5 is measured and not
  only argued (below).
- **New tables use `warmup`.** `timing_grid.Table` defaults to `schedule=
  "warmup"` with headroom 1, on the TASK30A validation (2026-11-03, a shared
  host): develop/develop experiments of 12 TASK30 cells, 20 pairs and 5
  samples each, `ramp` with its TASK30 count against `warmup` with the count
  of this rule from the TASK30 pilot. The median over the cells of the ratio
  of the B/B 95% interval widths, warmup over ramp, was 1.005 for CPU and
  1.004 for wall (`R` 1.005; per cell 0.41-3.52, the median being the
  predeclared statistic) and the warmup experiments took 0.383 of the time of
  the ramp ones (3056 s against 7972 s). Decision, by the predeclared rule:
  `R <= 1.10`, adopt `warmup` with unchanged pairs (20 in the first stage,
  the 20 of the second-stage formula). The least warm-up (under `ramp`: final
  calibration) or sample wall over its target was 0.87-1.05 per cell under
  `warmup` (0.866 for `exclude_batch-10000`) and 1.71-3.5 under `ramp`, so
  the half-target check holds with room. The warmup schedule needs fixed
  seconds, so a table without them names `schedule="ramp"` (it is refused
  otherwise: a default never depends on another argument).
- **The TASK30 table keeps `ramp`**, its counts file, pilot, grid and ledger,
  as does the TASK29A grid; both tables say `schedule="ramp"` themselves, and
  their archives replay unchanged at this code (the seals of the files this
  schedule changed are in the table's history). The history seals are
  compared per field, as for TASK29A (each field of the code may be the
  current one or one of its history, so a record may pass with a combination
  of fields that no one commit held), and the only code added to what is
  accepted is the exact blobs of the six files at 63ac28189 (`task30_grid.py`,
  `timing_grid.py`, `acceptance.py`, `MatrixPerformance.sml`,
  `performance_schema.py`, `run_paired.py`). No TASK29A run was recorded
  by the `task29a_grid.py` of 63ac28189, so its history gains nothing.

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
exercise adaptive and fixed schedules, the warm-up schedule (a warm-up of
0.15 s against the target 0.2 s passes, one of 0.09 s is rejected, so that a
test against half the target is told from one against the whole), complete
observation fields and short calibration rejection. The text of each driver
above the suffix that refuses an environment (`PERF_SCHEDULE` other than
unset or `warmup`, `warmup` without `PERF_ITERATIONS`, a count out of bounds
or, for the ramp, not a power of two) is executed too, with accepted and
refused environments. Reinstating the old top-level count must trigger the
serial guard for BOTH fixtures. These 78 assertions are scheduling tests, not
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
  baseline must be the table's (`task30_grid.py` names it, `a.BASE`).
  Beside `inventory.json` it publishes `variability.json`: for each cell the
  median and 95% interval of every metric's paired ratio, and for the gated
  metrics whether the interval lies in the equivalence window, so that the
  host's noise is on record before any candidate is measured. It is the
  noise of a pilot, which has no layout seed and calibrates freely, and is
  not the condition of the run; the run's own develop/develop control of
  each cell, under its layout seed and its fixed count, is that. A cell that
  fails is kept as `<cell>.json.xz.failed-N` and is measured again by
  `--resume`. Before measuring, a resumption compares its settings with the
  inventory, and only then clears what the stop left, under the lock; a
  pilot or run stopped before its first checkpoint says so and is started
  again.
- **The counts file is the predeclaration.** The layout seed
  (`task30-layout-1`), the pairs (20) and the samples (5) are fields of the
  table, sealed with `task30_grid.py`: changing one is a visible commit of the
  table. `predeclare --grid PILOT --output FILE` takes no setting from the
  command line; it writes `HEADROOM * max(final calibration count)` for each
  cell (the calibration counts are powers of two, as a batch count must be;
  `HEADROOM` 2) and refuses to overwrite. It first runs the pilot's analyses
  again on every archive, checks that both sides of every pilot process are
  the baseline and that `variability.json` is what they give. The file
  carries the baseline, the rule, each cell's batch seconds, the table's
  headroom, layout seed, pairs and samples, the target and the cap of pairs
  of the second stage, the seal of the pilot's driver, the seal
  of the pilot's inventory, the seal of every cell's archive and the seals
  of the files the table seals (`sealed`: everything the harness installs
  into the private directories, which is `MatrixPerformance.sml`,
  `MatrixSupport.sml`, `RuntimeMetrics.sml`, the signature fixture, the
  paired sources and `run_paired.py`, and `matrix.json`, besides the case
  list and the schema modules; a test installs the fixtures and compares the
  two lists, so the counts are bound to the fixtures they were measured
  with). The pins (`task30_pins.py`) are not among them: see the route after
  a regression below. `verify-counts --grid PILOT
  [--counts FILE]` derives the file again from the pilot (the pilot's code
  need not be the current code for that) and refuses any difference. The
  file is reviewed and committed before the first candidate observation.
- **What `run`, `extend` and `replay` take.** `run` takes the table's last
  counts file, byte for byte (see revisions below); `extend` and `replay`
  take the file the grid names, which is how a grid made under an earlier file
  replays. The baseline of the counts, of the table and of `--baseline`
  (which defaults to the table's) must agree; a candidate equal to the
  baseline is refused. The layout seed, pairs and samples are the table's at
  `predeclare`, which copies them into the counts file; `run` refuses a file
  that does not say what the table says and a different explicit
  `--layout-seed`, `--pairs` or `--samples` (the second-stage seed `SEED-ext`
  must be valid too, so the seed is at most 60 characters). `replay`,
  `verify-counts` and `extend` read all of these from the counts file the
  grid used, with the seconds of each cell, the headroom, the target and the
  cap of pairs of the second stage, so a later change of the table does not
  make an earlier grid unreplayable (a key a file lacks is read as the
  table's, and the file is refused if it then differs from what it derives
  to, except `schedule`: a file without one is `ramp`, as every file made
  before the field, never the table's, so that a table that changes its
  schedule still replays its earlier grids; `run` requires the file to have
  them, and refuses one of another schedule than the table's). A run
  refuses counts bound to other sealed files than the current ones. All
  three need `--pilot DIR`, the pilot the counts derive from, and derive the
  counts file from it again in full (archives unpacked, analyses rerun, every
  process the baseline, `variability.json` recomputed): counts that no pilot
  made are refused, and so is a pilot that is not the one of the counts.
  The candidate's own history must hold the file as it is (same git blob)
  and exactly one commit of that history may have touched it (merges are
  looked through with `--full-history --simplify-merges`, so an honest merge
  passes and a side branch that committed the file again, or a merge that
  edited it, is refused); that commit is recorded as `counts_commit`, and a
  replay derives it, and the seal of the file, again. `inventory["seconds"]` is
  only the table's default; the seconds of a cell are those in
  `iterations.seconds`. Every replay checks the header against the counts
  file and the table.
- **What the commit claim is.** Git proves the order of the counts file
  relative to the *candidate commit* (the file is in the candidate's history
  and one commit made it), and, with the rule above, that no free count is
  left: the counts are a function of the pilot and the table. It does not
  prove the order relative to any *observation*: the candidate's code can
  have been measured under an earlier commit (TASK28 and TASK29 observed the
  same code). The attempts ledger is what makes a retry visible, as a
  discipline and not as a proof.
- **Attempts ledger.** Each table with fixed seconds has one ledger, at
  `.agent-files/evidence/<table name>/attempts.jsonl` below the root of the
  checkout (`.agent-files/evidence/task30/attempts.jsonl`); `run`, `extend`,
  `pilot` and `prepare` take no option to name another. The directory is
  made when a measurement starts, and `pilot`, `prepare`, `run` and `extend`
  refuse to start unless git ignores the path, so no commit holds or rewrites
  it. A checkout that does not ignore `.agent-files` is told so; the step is
  one line, made once per clone, in the file that git names:

      echo .agent-files >> "$(git rev-parse --git-path info/exclude)"

  (a tracked `.gitignore` is not changed for it). `git clean -x` reaches the
  ignored directory and deletes the ledger, the build stamp and the logs with
  it: never run it in a checkout that holds them. Before the
  first cell `run` and `extend` append a JSON line with the event (`open`, or
  `resume` after an interruption), the stage (`first`, `second`), an attempt
  id (a second stage has its own, and a retry of it another), the candidate,
  the counts file and its seal, the layout seed, the output path, the
  absolute path of the checkout and the UTC time, and at the end a `close`
  line with the status (`pass`, `fail`,
  `inconclusive`, ...; `partial` for a diagnostic subset, `interrupted` when
  it stopped, and `checkout-changed`; see *when the checkout is judged*
  below, for what an `interrupted` line does not say). A close that cannot
  be written is reported on standard error
  (`ATTEMPT-NOT-CLOSED`, with what the close would have added), leaves the
  attempt open in the ledger, which shows it as interrupted, and does not
  replace the outcome of the run.
  The lines form a hash chain: each carries `prev`, the SHA-256 of the line
  before it (64 zeros for the first), so a line removed or changed in the
  middle is refused (`attempts ledger chain broken at line N`), as is a
  malformed line. A crash, a full disk above all, may leave lines at the end
  that are no record: one cut line, or several when the acknowledging append
  was cut too. Any run of them at the very end, however each is ended, is
  tolerated and reported (`LEDGER-TORN-LINE`, once for each); the next append
  ends the last one and writes a `torn` record naming the hash of each, so
  none is lost or silent. The same lines followed by a line that is no
  record of the chain, or in the middle of the file, are refused. A complete
  record without its newline is kept (`LEDGER-UNTERMINATED-LAST-LINE`). A
  resumption (`run --resume`, `extend --resume`) checks that the ledger holds
  its opening before it measures. `replay` needs the ledger and the grid's
  opening line in it, verifies the chain, and prints every attempt of the
  table with its stage, time, resumptions, every status it closed with (in
  order, comma separated; `interrupted` for a stop with no close), candidate
  and the checkouts of its lines, marking the one of the grid replayed and
  those of its candidate (`ATTEMPT id first opened T resumed N status S
  candidate C checkout P (this grid)`), with the counts (`ATTEMPTS of TOY: N
  in the ledger, M of this candidate C`), so a reader of a replay sees each
  retry and each close of it, also of another candidate. `close` replays the
  timing grid, so it prints the same lines, and repeats the counts in its
  line. A rerun under the same
  settings, after a pass or
  a non-pass alike, is a new draw: a new attempt in the same ledger, its
  predecessors stay in it, and the handoff publishes the whole ledger, not
  the line of the grid that passed. **One checkout.** The ledger is of a
  checkout, so a grid and every retry of it, the second stage included, are
  made in the one checkout: a draw made in a second clone is in that clone's
  ledger and the first would not show it. Each line records the absolute path
  of its checkout, so a ledger that holds lines of two paths, in the opening
  of an attempt or in a resumption or close of it, says so
  (`LEDGER-CHECKOUTS: N different checkouts` in a replay), and a clone made
  from the first, with its ledger copied, shows as lines of a path that is not
  the clone's. `replay` and `close` alone take `--ledger FILE`, read-only, to
  replay in another checkout against the ledger of the one that measured
  (a copy of it); `run` and `extend` never take it, and a measurement
  appends only to the ledger of the checkout it runs in. **The ledger is a
  discipline, not a
  proof:** the chain shows that no line was removed from or changed in the
  middle, not that lines after the last one, or the whole file, were not
  removed. That deletion is undetectable here, and what covers it is that the
  handoff names the ledger and that a reviewer asks for it.
- **Revisions.** A counts file is never edited: a changed file is a new file
  at a new path (`task30_iterations_2.json`, ...), listed in order in the
  table's `revisions` (paths absolute or built from `a.HERE`, as the first
  file's is), and every file after the first revises the one before it. There
  are two kinds of link, and `predeclare --revises PREVIOUS` takes one:

      --rescale CELL [CELL ...]   the same pilot: the named cells multiplied
                                  by 4 (reason "fixed calibration too short",
                                  "fixed batch too short" for `warmup`)
      --repilot REASON            a fresh pilot (`--grid` is the new one)
                                  for a change that alters what is measured,
                                  such as a fixture bug, with the stated
                                  reason

  `PREVIOUS` is the table's last file. A rescaling is made after the
  previous file is verified against the pilot; a new pilot must be another
  pilot than that of the previous file and a reason is required. The new
  file records the seal of the previous one and the link (the cells and
  factor, or the reason); `verify-counts --grid PILOT` derives it again from
  its own pilot and refuses a file whose link is not to the file before it in
  the table, a later file without a link, or a first file with one. A
  revision is a whole new grid at a new candidate commit (the file must be in
  the candidate's history): the first grid stays published and replays
  against the file it used (its inventory names it), and `run` uses the last
  file only. Adding a revision changes `task30_grid.py`, so the seals of the
  driver (and of `sealed_history`, for sealed files that moved) that the
  earlier grids recorded must be added to the table's `drivers` for them to
  replay, and `test_task30_grid.py` makes no assertion about the number of
  revisions or drivers. The rescaling route is for cells the first grid
  rejected as "fixed calibration too short" (see below).
- **The route after a regression.** The task asks for a diagnosis, a fix and a
  rerun. A production fix in a pinned file changes the candidate's blob of
  that file, so the pin is stale and `run` refuses (below). The route, in
  order: fix the production code; compute the new blobs and write the new pins
  into `task30_pins.py`, adding the seal of the previous version of that file
  and the pins it held to `PIN_HISTORY`, a dictionary in `task30_pins.py`
  itself (so the grids it judged still replay, and the driver, which every
  grid seals, does not change for it); commit the result as a new candidate
  commit, and run `prepare` at it, for the production fix is a source outside
  the performance area (the
  counts file is already in its history, and the pilot, the counts and the
  sealed files are untouched, because the pins file is not among them); run a
  new complete grid under the same counts file, then the second stage and the
  allocation gate as for any candidate. Every attempt, the regressed grid
  included, is in the ledger, and the handoff publishes the ledger. If the fix
  changes what is measured (a fixture or a sealed file), the counts must be
  derived again: a `--repilot` revision.
- **Batch seconds.** A table gives all cells one calibration target and may
  name a longer one for cases whose single operation is tiny, so that a
  batch stands clear of the per-batch overhead (the ten direct deletions of
  TASK30 use 1 s, the others 0.3 s). The seconds are part of the counts
  file, checked by `run`, and used again by `replay`.
- **Source identity.** The operations of TASK30 run through source files
  that the candidate may have changed: `task30_cases.SOURCES` lists them,
  each `.sml` with its `.sig`: the simplifier (`simpLib`, `Ho_Net`,
  `BoundedRewrites`, `Traverse`, `Travrules`, `Opening`, `Cond_rewr`,
  `SimpTracking`, `Trace`), the marker library (`markerLib`, `markerSyntax`)
  and the modules the cases call through them (`liteLib`, `Theory`,
  `Context`, `Uref`, `Drule`, `Conv`, `Tactical`). `run` records the git
  blob of each file at the baseline and at the candidate in the inventory
  and prints every file that differs (`SOURCE-DIFFERS path`). Such a grid is
  never a pass: its decisions name the files in `source_identity` and a
  status that would be `pass` becomes `inconclusive`, whatever the cells
  say. `replay` and the second stage re-verify the record against git. This
  is the evidence for "no extra source scan": neither gate sees a scan that
  allocates nothing and costs a few percent, so the identity of the code on
  the path, not a measurement, shows that no scan was added there. The
  boundary: what is not listed stays outside the identity (the kernel, the
  parser, `ThmAttribute`, `Lib`, `testutils` and the build files among it:
  every operation and the harness itself go through them, so a change there
  moves both gates and is for review, not for a list of this size), and the
  identity of a file says nothing of the data it works on, such as the size
  of the theory graph; the fixtures fix that. The inventory therefore
  records, besides the listed files, the sorted name-status list of every
  file under `src/` that differs between the baseline and the candidate
  (`source_tree`; `replay` derives it again from git), so everything that
  differs, listed or not, is published: for the present candidate that
  includes `ThmAttribute` (additive accessors), the `rawtheory` tool
  `mktool.ML` and build files, none of them a listed source.
  A reviewed difference may be pinned: `task30_pins.PINNED` maps a path
  of the list to the exact candidate blob and the reason. A file that
  differs is accepted only when its candidate blob is the pinned one; it is
  then published under `source_identity.reviewed` with its reason, prints no
  `SOURCE-DIFFERS` and does not change the status. Any other blob of it, and
  any other file, behaves as above; a pin on a file identical to the
  baseline or outside the list is an error. A file the candidate adds
  (absent at the baseline) is recorded with no baseline blob and is accepted
  only with such a pin; unpinned, or absent at both commits, it is refused.
  `replay` and the second stage re-derive all of it, so the record is not
  trusted. The pins are in a file of their own, whose seal every grid
  records (`pins`) beside the sealed files; a grid replays by the pins it was
  judged by, the current ones or those kept in `PIN_HISTORY` (in
  `task30_pins.py`) under the seal of that earlier version (otherwise
  `changed pins`). `run` refuses, before any
  measurement, a candidate with a source that differs without a current pin
  (a stale pin is one), because that grid could never pass: it prints
  `SOURCE-DIFFERS` and stops. `--only` still measures a diagnostic subset,
  marked `diagnostic` in its inventory, which has no decisions, can never
  complete a grid, and cannot be resumed without `--only`. The reviewed
  differences are `Cond_rewr.sml`/`.sig` (the
  rewrite-tracking helper moves to the new `SimpTracking`, aliased as
  `note_rewrite` and `with_tracking`, which call through its opaque
  signature, and `is_var_perm` is exported; `mk_cond_rewrs` and
  `COND_REWR_CONV` are textually unchanged and no loop is added) and the new
  `SimpTracking.sml`/`.sig` themselves. The pin tests compute the blob of
  each file in the checkout and compare it with the pin, and with the
  baseline's.
- **Theory hooks.** `Theory.register_hook` is the way a module adds work to
  a theory transition. Audit of its callers: the baseline has nine sites in
  seven files (`TexTokenMap`, `markerLib`, `OpenTheoryMap`, `Parse` twice,
  `DB` twice, `ThyDataSexp`, `pred_setScript`), all unchanged in the
  candidate. The candidate adds one ordinary site, `SplitData.ensure_listener`
  (`SplitData.sml:98`), reached through `splitLib.enable_split_attribute`:
  the explicit opt-in of the split tests, and
  `src/simp/src/splitPersistLib.sml` (line 6), a compiled public module that
  calls it when it is loaded. Neither
  is in the ordinary heap (`src/boss/tests/tracked-defaults/ordinary.sml`
  checks that an ordinary load does not hold `SplitData`, `splitLib` or
  `splitPersistLib`), and neither fixture loads them, so the site is not on
  the path of the cases. Test-only registrations are
  `src/simp/tests/split-lifecycle/repair.sml:33` and
  `src/simp/tests/split-registration/selftest.sml:392,413`. A search for the
  text `register_hook` is not enough: `ThyDataSexp.sml:357` registers a hook
  for each data type made by `ThyDataSexp.new`, so a new user of
  `ThmSetData`, `AncestryData` or `ThyDataSexp.new` adds one too. The audit
  therefore covers those names as well, over the ordinary sources and the
  lines changed in them (`git diff BASELINE CANDIDATE -- src` outside the
  tests, and `git grep` of each name at both commits). For the present
  candidate it finds no ordinary file that gains a use of any of the four:
  `SplitData.sml` queries `ThmSetData` (`data_exportfns`, `all_set_types`,
  `toKName`) and names `AncestryData` in a comment, and `splitLib.sig` in a
  comment; the other new users are tests (`split-registration/selftest.sml`
  among them, which also calls `ThyDataSexp.new`). A candidate that
  registered a hook on an ordinary path would not be visible to the source
  identity of the listed files alone; this audit, repeated for a new
  candidate, is what covers it.
- **Decisions.** `run` prints, and the exit status reflects, five separate
  lists: pass; *fail*; *inconclusive*; *control-limited* (every open metric
  is inconclusive only because its B/B control is outside the window);
  *protocol* (no admitted measurement). The exit status is zero only when
  every cell and the retained slope pass, one when anything failed, two
  otherwise. A command that is refused (a check that failed before or while
  it measured, a held lock, a checkout that changed) prints one
  `REFUSED: reason` line on the standard error and exits **3**, a status no
  grid has, so that a wrapper tells "nothing was decided" from a grid that
  failed (1) or was not conclusive (2); any other error that decided nothing
  (a missing file, a full disk, a malformed record, a bug) has the same
  status and the same line, after its traceback; a record that is not valid
  JSON names its file; an interrupt is not caught; a usage error of the
  command line is the parser's 2. The lists are derived from
  `decisions.json` and `replay` prints them again. No cell is excused: a task
  that accepts a non-passing cell does so in a separate, reviewed table (as
  TASK29A did), outside the engine.
- **Whole operations.** The timed operation is the fixture's complete
  `run`, and its result is verified in the same process, so work cannot move
  into unmeasured preprocessing: a batch contains the construction or call
  being gated and whatever it needs (the setup of a case, such as the theory
  transition of `history_theory_change` below, is outside the batch). The
  fixtures assert the callback counts of the maker and collector cases
  (`history_collectors`, `history_makers`) exactly and check the resulting
  simpset of every deletion; `exclude_dproc` and `exclude_mixed` assert that
  the deletion calls no maker and no collector (zero of each: `-*` runs
  neither). Their simpsets are built with the maker and the dprocs first and
  the data after them, so that a rebuild of the history would, by the
  reading of `++` and `build_from_history` in `simpLib.sml`, prime the dprocs
  (`++` passes the rewrites of each later fragment to `Traverse.addctxt`)
  and, where data follows (`exclude_mixed`), run the maker, so the zero
  counts would fail; `exclude_dproc` has no data, so there only the
  collectors would be primed. They are zero because the deletion replays
  nothing. That reading has not been run in HOL, and
  the counts of a rebuild are not asserted. The fixtures do not count scans,
  and production records none. The allocation matrix
  (`allocation_matrix.py --task task30`) brackets setup, first and steady
  operation and verification of all 24 cases and compares exact allocation
  words and their size slopes between the sides.
- **`history_theory_change`.** Neither gate times the theory transition
  (`new_theory`, and with it the export of the theory) or counts its words.
  In both fixtures the transition is part of the case's setup, before any
  measured batch. What both gates cover is the replay of the history
  and the reparse after `Context.restore`: the timed batch replays `from`
  under the changed context and must raise the "bad theory name" error, and
  the verification, outside the batch, restores the earlier context and
  replays again. The timing fixture's real `new_theory` does change the
  state the replay runs in (the current theory); the allocation fixture
  sets `MatrixSupport.theoryChange` to a no-op in `MatrixAllocation.sml`
  because the export has clock- and pid-dependent words and writes below
  the working directory, which the sealed private selection must not see
  change, and the reparse is driven by the `Context.restore` that drops the
  linked theory. `Globals.interactive` is not set (it would delete the
  constants the fixture uses). The export is code of `Theory.sml`, and its
  cost is gated by nothing but the source identity of that file (listed
  above) and the hook audit; a change to the export that is not a change of
  `Theory.sml`, or a hook, would be invisible. Decision: the export is not
  simplifier work and is out of TASK_30's scope, so it has no timed batch
  and none is wanted; the reparse is in scope and is gated by both gates, as
  above.
- **The checkout a measurement runs in.** `prepare` configures and builds,
  `pilot`, `run` and `extend` measure, and each of them refuses to go on
  unless the checkout is the one the measurement names. `prepare` is the one
  command that configures and builds, so the stamp binds executables built
  from this tree: configure makes `bin/hol`, `bin/Holmake` and `bin/build`
  and writes the HOLDIR of the tree into `tools/Holmake/Systeml.sml`, and
  `bin/build` never rebuilds those three, so the operator has no configure
  step, whatever a merge, a switch of branch or a move of the tree did:

      python3 -B task30_grid.py prepare [--repo ROOT] [--timeout SECONDS]

  It needs a clean checkout (`private_runtime.harness_identity`, the check
  the allocation gate uses) and takes the measurement lock for the whole of
  what follows, in the repository root: `poly < tools/smart-configure.sml`
  (the `poly` found on the PATH, with that file as its standard input), then
  the real `bin/build --stdknl --seq=tools/sequences/upto-parallel` with
  `/dev/null` as its standard input, both into one log. Configure writes
  only files that git ignores (`tools/Holmake/Systeml.sml`, `bin`, `sigobj`,
  the generated editor files, and the tools it compiles) and `Systeml.sig` it
  only reads, so the checkout stays clean; measured on a checkout whose
  products were up to date, configure and this build took under five minutes
  together (from nothing the build takes the better part of an hour). The
  real configure script runs under a handler that swallows an exception and
  lets `poly` exit 0, so after configure `prepare` requires the line
  `Finished configuration!` in what this configure wrote (not in an earlier
  run's text, were the log appended to) as well as the exit status 0: without
  that line there is no build and no stamp. It then reads the HOLDIR of
  `tools/Holmake/Systeml.sml` as an assertion about what configure left
  (configure has just written the HOLDIR of the directory it ran in), and
  refuses a checkout that has none, more than one, or another path. The
  standard kernel is fixed on the command line (`bin/build` would otherwise
  take the kernel of the last build), and the allocation gate's toolchain is
  the standard kernel too. The input of the build is closed because
  `bin/build`, when `bin/hol`, `bin/Holmake` or `bin/build` is older than a
  source of it, prints `WARNING! WARNING!` and waits for a line
  (`check_against` in `tools/build/buildutils.sml`, which looks at some of
  those sources only): with an open input the build would sit for the whole
  timeout, with none it goes on. Configure has just made the three
  executables, so the warning is not expected; `prepare` still refuses to
  stamp when the log holds it, whatever the exit status, as an assertion.
  The log is `prepare.log` beside the ledger, replaced by the next `prepare`
  (one file, so the disk use does not grow, and it is not the record of a
  build: the durable record of the build a pilot or a grid ran with is the
  products digest in its inventory, `checkout.products`); the default timeout
  is four hours for each of the two commands. Only if configure and the build
  exit 0, configure prints its last line, and the checkout is clean at the
  same `HEAD` does it write
  `.agent-files/evidence/<table>/build-stamp.json`. A failed, timed out or
  interrupted configure or build writes no stamp and removes the one of an
  earlier `prepare`. The stamp holds `HEAD`, the seal of the tracked tree
  outside the performance area, the build command, and the digest of the
  products: the contents (names and SHA-256, symlinks followed) of `bin/hol`,
  `bin/hol.state0`, `bin/Holmake` (which compiles the fixtures), everything
  below `sigobj`, and the theory data files and theory sources
  `src/**/.hol/objs/*.dat` and `*.sml` (which the theories load; a theory
  that the heap does not hold is read from them). A product, or the target of
  a link, that resolves outside the repository is refused. What the stamp
  does not bind: the Poly/ML runtime and libraries (`poly`, libpolyml), which
  each cell's manifest records among its tools, and the fixtures, which come
  from the checkout's git blobs and are sealed separately. Where each piece
  of a measurement comes from: the code of both sides below `src/simp/src` is
  read from git (the blobs of the baseline and of the candidate), and the
  rest of what it runs with is those products and that runtime. `pilot`,
  `run` and `extend` then require the tree clean, `HEAD` the commit measured
  (the candidate; a pilot has none and is bound to the commit it is made at),
  and the stamp to be there, of the same seal outside the performance area,
  of the same build command and of the same products digest as the checkout
  has now. No file time is read: touching `bin/hol.state0`, or switching to
  another commit and back, changes nothing; editing a product, adding or
  removing one, or changing any tracked source outside the performance area
  (`src/simp/src` included) is refused with "run prepare at this commit"
  (at a fresh start; a `--resume` is told what is safe, below). A
  commit that touches only the performance area (the counts file as Y) needs
  no second `prepare`. The pilot's inventory and a grid's record the
  `checkout` (`head`, the seal of the tree outside the performance area, and
  the `products` digest): a second stage must find the same checkout as its
  first, the products included; a resumed `run`, `extend` or `pilot` finds
  the checkout its inventory recorded. **Every `prepare` makes a new
  products digest**: configure relinks `bin/hol` and `bin/Holmake` and the
  build makes the heap again, and three real `prepare` runs at one commit
  gave the same head and tree and three different digests (2499 files
  each). The digest is not made stable. So **a grid that is stopped, or
  whose attempt ended `checkout-changed`, must not be prepared**: a
  `prepare` between a stop and its `--resume` is refused (`resume with
  different settings`, or `not at the commit measured` where that applies),
  `prepare` is no way back to a stopped grid, and a stamp that is lost comes
  back only from a copy of that same file. A mistaken `prepare`, or a lost
  stamp with no copy, costs the cells of that grid, and the route is a new
  grid. So a refusal of the checkout at a `--resume` of a grid, a second
  stage or a pilot, or at an `extend` (whose first stage has been measured,
  so its record has begun as much as a stopped grid's), does not say `run
  prepare at this commit` or `commit first`, which are for a fresh start: it
  ends with "this grid goes on only at the recorded commit, tree and
  products; remove the change, or restore the stamp from a copy of that same
  file; a prepare ends the grid, and a later commit must be left: go back to
  the recorded commit". A commit that is left (the checkout put back at the
  recorded commit) does not end a grid; a `prepare` does.
  The same words end the text of an end that could not be judged (below).
  A `prepare` between the stages is refused the same way, by `extend`
  (also `extend --resume`) before it replays the first stage (`the checkout
  is not the one the first stage was measured in`). `replay` derives the
  tree seal of the candidate from git again (`changed checkout`) and finds a
  well-formed digest.
  `close` compares the timing grid's head and tree seal with the allocation
  grid's harness, and cannot compare the products: the allocation grid is
  measured with a toolchain of its own (a fresh clone built at the candidate,
  with its own controls receipt), and the timing grid's products are those of
  its own checkout, so the two digests are of different things and a
  comparison would be wrong.
  **When the checkout is judged.** Before the lock, in the binding
  (`bind_checkout`: the first look, where the refusals at a `--resume` or an
  `extend` come from, a stray file and a tracked edit included); under the
  lock, before anything is written (each attempt, a resumption included);
  and at every end of an attempt that the process survives: after the last
  cell; and when an attempt stops early, by a cell that raises, a failure
  inside the measuring or after it (the summary, the decisions), or an
  interrupt or a termination signal (SIGINT, SIGTERM, SIGHUP). The driver
  makes SIGTERM and SIGHUP a `KeyboardInterrupt` in every command (a
  handler put in at `main`, and put back at its exit), so a plain `kill`, a
  `timeout`, an agent's stop and a closed terminal take the path of an
  interrupt: the cell's process group is killed, and the end is judged. A
  signal that is ignored when the driver starts (SIGHUP under `nohup`) stays
  ignored, so a grid under `nohup` survives its terminal. The lock is
  released with the cell, except for a process that `run_paired` started:
  that has a session of its own, is not in the cell's group, and runs to
  its end holding the lock, so a `--resume` may be refused as busy until
  then, and a `simp-paired-*` directory may be left in `TMPDIR`; a process
  that hangs has to be found and killed by hand. The lock staying is
  deliberate: it is what keeps a second measurement out of a window that
  one is still using. A failure after the measuring is judged a second time
  by the same handler. One routine judges the end for a grid, a
  second stage and a pilot, the normal end and the early stop alike, and it
  is the only place that marks. Those are all the moments: nothing else is
  looked at. A checkout that is not as recorded at one of them ends the
  attempt as `checkout-changed` (the closing line of the ledger says so),
  with no pass, and what it leaves behind depends on which of two things was
  found. At an early stop the exception of the stop still propagates, as it
  would without the judgement, and decides the exit status; the judgement
  adds the mark and the close.
  *Known to differ.* The head is not the commit measured, or the tree
  outside the performance area or the products differ from the stamp or from
  the record, or any tracked file differs from `HEAD` (see below). The
  inventory records `checkout_changed` (as a pilot's does) and **such a grid
  is dead**: `--resume`, `replay`, `extend` and `close` refuse its directory
  (`the checkout changed while this grid ran ... it is dead`; a dead pilot is
  refused by `predeclare` and `verify-counts` with `the checkout changed
  while the pilot ran`, and its `--resume` with `resume with different
  settings`), a `prepare` after it cannot make it a pass, and its route is a
  new grid in a new output, a new attempt of the ledger. This holds for an
  early stop as for the last cell: an edit made after cell 3 of a grid whose
  cell 5 raises is found at the stop, the grid is dead, and undoing the edit
  before the `--resume` changes nothing.
  *Not judged.* Only untracked files in the tree (a stray file, an editor's
  swap file), or a stamp that is missing, malformed or of another build
  command, with nothing else known to differ. The attempt closes the same way
  but the inventory carries no mark and the grid is not dead: it has no
  decisions, so a full `replay`, `extend` and `close` have nothing to check
  (`replay --partial` replays its cells), and `--resume` compares the
  checkout with the record as after any stop, so it goes on once the stray
  file is gone and the stamp is there again (the same file, copied back: see
  above), and is refused if the products, the tree or the head are not the
  recorded ones (`resume with different settings`, and before that the
  refusals of the checkout, which end with the words of a resumption, above).
  An attempt that stops early and finds only that closes `checkout-changed`
  as well, with no mark, and the original exception propagates. A pilot
  records `checkout_unjudged` instead;
  `predeclare` and `verify-counts` refuse it until `pilot --resume` has found
  the checkout as recorded. The mark is cleared by that resume, but the text
  of every unjudged end stays in the pilot's `unjudged_ends`, which the
  resume comparison ignores.
  *Nothing found.* An attempt that stops early and finds nothing closes
  `interrupted`, as before.
  *A difference found and not marked.* The end of an attempt that stops
  early finds the checkout known to differ, and the mark cannot be written
  (a full disk, a second interrupt in the writing). The original exception
  still propagates and the attempt closes `checkout-changed`, with the text
  found and the failure of the mark in `found` on its close line. If the
  close cannot be written either (the same full disk), the line
  `ATTEMPT-NOT-CLOSED` on standard error, which carries the `found`, is
  the only record, and the attempt reads as a killed process. Otherwise the
  inventory does not say it, so the ledger is the only record, and **a
  `replay` and a `close` refuse a grid whose own attempts have a `found`**:
  the attempt of the grid replayed or closed and, for a second stage, the
  attempt of its first stage as well (a second stage is an attempt of its
  own, so a `found` on either kills the grid). They refuse it as they refuse
  a dead grid (`the checkout changed while attempt ... ran ... the grid is
  dead`, the exit status of a refusal). A `--resume` or an `extend` does
  not read it: it may run, and the cells it measures stand for nothing,
  since the replay will not pass. The refusal names the attempt and the
  text found.
  The ledger is the table's, shared by every grid, and the difference found
  kills its own grid only. It is published with the ledger and does not
  touch a new grid: the route of a dead grid is a new grid in a new
  output, which `replay` and `close` accept, and whose report of the
  attempts prints every earlier `found` as a line of its own,
  `CHECKOUT-FOUND-NOT-MARKED <attempt> <text>`, so that it is not hidden.
  *The judgement could not be made.* The checkout could not be asked (an
  `OSError`, a second interrupt, git failing), or the mark of an end that
  was only not judged (a pilot's) could not be written. Nothing is marked,
  the original exception still propagates, the attempt closes `interrupted`
  with the reason in `judgement` on its close line, and the exit status is
  that of the original exception. A `--resume` after it is as after a
  killed process (below): the end was not judged, so a change present while
  the attempt ran and undone before the `--resume` is not seen; there is no
  refusal, and the line `JUDGEMENT-NOT-MADE <attempt> <text>` is in what
  `replay` prints. A pilot has no ledger: it keeps the note in the
  inventory, `checkout_changed` for a difference found and `checkout_unjudged`
  with the text added to `unjudged_ends` for a judgement not made, when its
  last checkpoint writes it, so that `predeclare` and `verify-counts` refuse
  the pilot. A judgement not made is lifted by a `pilot --resume`, which
  judges the checkout; a pilot with `checkout_changed` is dead, and its
  `--resume` is refused (`resume with different settings`). If that
  checkpoint fails too, its error is the one shown.
  *A tracked edit found only by `--resume`.* An attempt whose end was
  judged and found nothing, and a tracked file edited after that, with no
  cell run under it: `--resume` refuses it (the tree is not clean) and
  writes no mark, and the edit undone, the resume goes on. The same holds
  after a stray-file end.
  *A process that is killed* (`SIGKILL`, a power cut, the machine; the
  driver has a handler for SIGINT, SIGTERM and SIGHUP only) gets no
  judgement, and the cell of a driver so killed runs on, in a group of its
  own, and keeps the lock until it ends, so that a `--resume` is refused as
  busy until then. Its attempt stays `interrupted` in the ledger, with no
  close line, and its end was not judged: a change present while it ran and
  undone before the `--resume` is not seen, and a change found at the
  `--resume` is refused, not marked. A reader of an `interrupted` line must
  treat it so: the status does not say that the end was judged.
  *What is judged without a clean tree or a stamp*, in this order: the head
  (it must be the recorded one); the products digest, computed from the
  products and compared with `checkout.products` of the inventory (a
  difference is known); then the tree. **No tracked file may change while a
  grid or a pilot runs, not even a documentation file**: the recorded
  identity is a tree, so a change to any tracked file anywhere (any entry of
  `git status --porcelain` but `??`, the performance area included) is a
  different tree and is known to differ, whether the file is undone before
  the next command or not; the grid is dead. An untracked stray file costs a
  resume, nothing more. The same holds for the end of a pilot.
  What is compared is the checkout at the moments listed above (under the
  lock before the first cell, and at each end the process survives), so a
  change made and undone between them is not seen, nor one made and undone
  while a killed attempt ran; and the record proves
  that the checkout holds the recorded tree and products now, not that it
  held them when `prepare` ran. A pilot made at X and a grid at Y are not
  required to have the same tree outside the performance area: a
  production fix between them must stay possible (route after a regression,
  above); it needs a `prepare` at the commit it is committed in.
  **Where the output goes.** The tree must be clean when a measurement is
  over, so an output inside the repository must be ignored by git: `pilot`,
  `run` and `extend` refuse one that is not, before they measure. Put `OUT`
  below `.agent-files/evidence/<table>/` of the checkout, beside the ledger
  and the stamp; an output outside the repository needs nothing.
  Each measured candidate is also kept by a local ref,
  `refs/performance/<table>/<full candidate sha>`, made by `run` and `extend`,
  so that a rebase, a squash into develop and garbage collection cannot make
  the candidate and the counts commit in its history unreachable. The ref
  protects the commits only in the object store that holds it: a checkout
  made by `git clone --shared` (or with alternates) keeps its commits in the
  store of the clone it borrows from and its ref is not the lender's, so a
  `git gc` or a deleted branch there can still remove the candidate X or Y
  that the ref in the borrower did not keep; make the checkouts that measure
  with a plain clone, or fetch the ref where the grids are kept.
- **What a replay needs kept.** The grids (the first stage and the second),
  the pilot directory the counts derive from, every earlier counts file named
  in the table, the attempts ledger, and the `refs/performance/task30/<sha>`
  refs of the measured candidates (or the commits themselves in a clone that
  keeps them; the limit above applies to a shared clone), and the build
  stamp is not needed (it is a check of the run, and no replay reads it).
  Without the commits `replay` fails with "unknown revision";
  without the pilot, the counts are underived; without the ledger, no replay
  passes.
- **Pilot method for a new task.**

      python3 -B task30_grid.py pilot --output OUT/pilot \
          --authorize-measurements
      python3 -B task30_grid.py predeclare --grid OUT/pilot \
          --output OUT/task30_iterations.json
      python3 -B task30_grid.py verify-counts --grid OUT/pilot \
          --counts OUT/task30_iterations.json

  The pilot needs the checkout above and runs serially under its lock, like
  `run`. `OUT/pilot/inventory.json` lists every archive and its
  calibration counts. Review the counts file, then copy it to
  `task30_iterations.json` and commit it before the candidate is measured
  (that commit is the candidate Y); `--resume` continues an interrupted pilot
  as it does a run. The fixtures run only in HOL; the operator runs the fixture
  smoke (`smoke_matrix.py`) on the build before the pilot, because the
  pilot's counts depend on the fixture and the unit tests do not execute SML.
- **Grid.**

      python3 -B task30_grid.py run --candidate SHA --output OUT/grid \
          --pilot OUT/pilot --authorize-measurements
      python3 -B task30_grid.py extend --grid OUT/grid --output OUT/stage2 \
          --pilot OUT/pilot --authorize-measurements
      python3 -B task30_grid.py replay --output OUT/stage2 \
          --pilot OUT/pilot

  `run` takes the layout seed, pairs and samples from the table (through the
  counts file) and is refused without a seed. `--resume` continues an
  interrupted `run`, `extend` or `pilot`; `replay --partial` replays the
  finished cells of an interrupted one. `replay` of a pilot is refused: a
  pilot is checked by `verify-counts`. The attempts ledger is at its fixed
  place; `run`, `extend`, `pilot` and `prepare` take no option for it, and
  `replay` and `close` take `--ledger FILE` for a read-only copy.
- **The sequence, from the pilot to the verdict.** With X the commit the
  pilot is made at and Y the candidate (the commit of the counts file):
  1. at X, a clean checkout: `prepare`, which configures and builds, then
     `pilot`;
  2. `predeclare`, `verify-counts`; review the counts file;
  3. commit the counts file as Y (with any production fix and pins, in the
     order of the route after a regression); `verify-counts` again. Run
     `prepare` once more only if the commit changed a source outside the
     performance area (the driver says "run prepare at this commit" at a
     fresh start);
  4. at Y: build the toolchain at Y, take the controls receipt, then run the
     allocation gate (`allocation_matrix.py run --task task30`), see the
     prerequisite below; the timing grid is run at Y too, in the checkout
     that made the pilot and holds the ledger (a step that rebuilds the
     products of that checkout changes the digest the stamp holds, and the
     driver then says to run `prepare` again, before the grid starts: a grid
     that has started must not be prepared, see above);
  5. `run --candidate Y --pilot OUT/pilot`; `extend` if the control left
     cells open; `replay` of each stage;
  6. `close`:

         python3 -B task30_grid.py close --grid OUT/stage2 \
             --pilot OUT/pilot --allocation OUT/allocation

     (`--grid` is the second stage where there is one, otherwise the first).
     `close` replays the timing grid and the allocation grid, requires that
     they are of one candidate and baseline and that they ran in the same
     harness (the timing checkout's `head` and tree seal equal the allocation
     record's `harness`, which is clean), and prints one line,
     `TASK30 closing verdict: pass|not pass (timing S, allocation S;
     candidate C, harness H; attempts N in the ledger, M of the candidate)`.
     Any status but pass in either gate exits
     non-zero; `close` applies no disposition. It compares the cheap records
     (candidate, baseline, harness) before it replays anything, and needs the
     ledger (`--ledger FILE` for a copy). Because the timing grid is measured
     at `HEAD == Y`, the allocation run must be made in a clean checkout at Y
     too; the grid's record holds the checkout, the same tree as Y, and any
     clean checkout at Y serves: `close` compares the head and the tree seal.
- **A cell that is too short.** A cell rejected as "fixed calibration too
  short" is a non-pass and blocks the grid. The only route is a counts
  revision (above) that multiplies that cell's count by 4 for baseline and
  candidate alike, committed with a new candidate commit, and a complete new
  grid (a cell cannot be merged into another grid, and `--only` decides
  nothing); the first grid stays published and replays against its own
  file (the other link, a fresh pilot, is for a change of what is
  measured). The revision is a reaction to a candidate observation, so it is
  a new draw like any rerun, recorded in the ledger, and the handoff states
  it. The code does not check that the previous grid rejected the cell; the
  reviewer does. No code changes for it: the ordinary exclusion path
  (`simpLib`) is identical to develop (see source identity), so a candidate
  that runs twice as fast as the baseline is not expected, and a count that
  proves too short is a property of the pilot.
- **Allocation gate prerequisite.** A TASK30 allocation run
  (`allocation_matrix.py run --task task30`) needs, in this order: the pilot
  at X; `predeclare`; the counts committed as the candidate Y; the HOL and
  native toolchain built at Y; the controls receipt; then the allocation run.
  The constraint is the toolchain: its build lineage must be at the exact
  candidate commit, and is refused otherwise ("toolchain not built at the
  candidate commit"), so after the counts commit, and again after any
  revision or production fix that makes a new candidate. The refusal comes at
  once, so no measurement is lost. A controls receipt taken at X is accepted
  at Y only because the counts file is inside the performance area: the
  controls compare the tree outside it, and the harness inputs are checked by
  seal. Separately, `task30_cases.py`, `MatrixSupport.sml` and
  `MatrixAllocation.sml` are among the files of the harness the allocation
  run records and compares (`harness_files`), so a TASK29B run resumed
  across them is refused. Nothing in the allocation run itself links its
  candidate to that of the timing grid; `close` does.
- **Cost.** The grid is 144 cells at 20 pairs and two slots per pair, each
  slot a fresh process with its batch (0.3 s, or 1.0 s for the ten direct
  deletions at every size, including 10000): about two to three days for
  the first stage, plus a second stage for the cells the
  control leaves open.
- **Other tables.** `task29a_grid.py` gains `pilot`, `verify-counts` and the
  class report with the engine; its recorded runs and the TASK29B allocation
  schema names (`task29b-*`, kept by the TASK30 gate) are unaffected. The
  TASK29A table is closed: its grid was disposed of by the policy owner, no
  new TASK29A run is made, and so its table keeps `engine=False` (a run of
  it would not seal `timing_grid.py`; the recorded ones predate the engine).
  Its counts take no ledger, pilot or revision: those belong to tables with
  fixed seconds.

##### Structural evidence (allocation work phase)

The allocation fixture has an untimed `work` phase after the `apply` bracket
(`MatrixAllocation.sml`; the code is `MatrixSupport.workPhase`). Nothing of it
is inside a bracket, so it adds no word to any bracket, and the timing fixture
does not run it (it does load `MatrixSupport`, whose hooks the workload
constructors set in every timed process, outside the timed region). It runs
the operation twice, `beforeBatch`, `run`, `afterBatch 1` each, and then a use
of the retained result of the second run, and records for each of the three:

- trace events by exact level and constructor (`trace.L.ACTION`; a TEXT also
  by its message, `trace.L.TEXT:message`): a listener put on
  `Trace.trace_hook`. `Trace.trace` calls every listener on every call
  whatever the trace level (the level is filtered inside the default
  listener), so the counts do not depend on `simplifier` tracing. The level
  is not clamped. A TEXT carries a plain string, so its message is in the key
  (escaped: other than letters, digits, space and ``_.()'/+*-<>[]!?:``
  every byte is `%XX`); an `LZ_TEXT` is a lazy text, which the listener
  never forces, so it is counted by level only;
- kernel inferences by rule (`kernel.RULE`, `kernel.total`):
  `Count.counting_thms` and `Count.thm_count`;
- `maker`, `collector` and `dproc` calls: the counters of `MatrixSupport`
  (a collector's `addcontext`, a dproc's `apply`; the fixture's reducers
  count their own), and for `history_makers`, whose makers count in the
  workload's own two counters, those too (read through the hook
  `localCalls`, the maker bodies and so the timed closures are untouched).
  The fixture's dprocs raise `UNCHANGED`, which leaves no trace event and no
  inference, so the `dproc` counter is the only count of their application.

**The three records.** `work.first` and `work.second` are the first and the
second run of the work phase. They follow every bracketed run (the setup
build, `operation_first`, the steady runs and `verify`), so `work.first` is
not a cold run: an effect that only the very first run has, such as a lazily
built cache, is in the `operation_first` words and not in a work count. The
two rows are the first and second run after all bracketed work.
`work.use` is a client's use of the retained result, under the same listener
and kernel counter. For a simpset (a built simpset, a fragment as a simpset,
the result of a deletion) it has two parts:

- the net conversion of the result (`netconv`: the traversal with the
  rewriter of the simpset and **no dprocs**) is applied to the left side of
  each of the n rules, the same conversion as the fingerprint's REFL set. It
  counts every traced event of the n traversals: one traversal `REDUCE` per
  lookup (whether or not an entry is invoked) and, for each entry invoked,
  the events of its `USER_CONV` (`REDUCE`, then `PRODUCE`, or `TEXT` when
  it fails) and of the rewrite (`REWRITING`, `PRODUCE`), plus the
  inferences; a miss gives a REFL. The rewriter tries the matches of
  a term in order and stops at the first that succeeds (`tryfind`,
  `simpLib.sml`), and a match filtered before its conversion runs emits
  nothing, so a duplicate or stale entry behind a working one, and a
  filtered entry, are not counted. A stale entry that still fires is, as
  `REFL` events and in the REFL set of the digest;
- each dproc the result still holds is applied (the public
  `Traverse.dest_reducer`, with the context it holds) to the left sides of
  the first, the middle and the last rule (the first is the rule the
  deletion cases delete). The fixture's dprocs leave no event, so what is
  counted is `dproc`: the number of dprocs held times the sampled terms
  (n-1 dprocs after a deletion of one, three terms: `3(n-1)`; none when
  every dproc is gone). It equals 3 times the number of dprocs the result
  holds, which is the length of `dpnames` in the digest: the same fact, shown
  as counted applications of each retained dproc. It is the one count that
  sees a dproc deletion, but it is not an independent witness of it.

For a retained conversion (`compile_construct_conv`) the conversion is
applied to the fingerprinted terms; for the tactic whose operation constructs
it (`exclude_tactic_construct`) the tactic is applied; for a theorem or a
tactic result that the operation already applied there is no further use, and
the record is the empty set of counts (`trace=;kernel=;maker=0;collector=0;
dproc=0`).

Not reachable without a production change, and so not counted: the net
candidates of a lookup (`initial_net` is inside the opaque simpset, and the
context of the rewriter reducer is an exception whose constructor is local to
`simpLib`). The count of candidates per lookup, which would include entries a
successful match hides, does not exist in these rows.

Then the fingerprint of the retained result is read, from the hook
`MatrixSupport.fingerprint`, which each workload sets when it is built, with
the use (never inside a timed closure; the text is made when the work phase
reads it). The digest is read before the use, because a use can consume what
it describes: the bounds of a bounded rewrite (`compile_bounded`,
`history_bounded`; not among the 13 cells) are spent by the first lookup, so
the digest describes the retained result and the use runs on one already
consumed by the digest's own lookups (deterministic, and not a claim about
fresh bounds). The inner hashes of the fingerprint (64-bit FNV) are not
cryptographic; they stand for long texts against accident, and the SHA-256
of the parser is of the text as it is.

What the fingerprint holds. For a simpset: the names, the dproc names, the run
length encoded set of installed rules whose left side the net leaves alone and
a hash of the theorems of the others; for a theorem its hypotheses and
conclusion with types shown; for a conversion that of each of its terms; for a
tactic the residual goals (types shown) and the proof; for a fragment its
name, its length and a hash of the printed form of every rule it holds (an AC
fragment: also what it does to the AC input); for the theory change the error
with the function that raised it and its message. The fixture emits
`work.first`, `work.second`, `work.use` and `result.digest` after
`alloc.foreign`; the parser hashes the fingerprint with SHA-256.

**What changes outside the work phase.** The timed closures and the `verify`
closures are textually unchanged, so the operation and apply words of a case
are those of the fixture before the work phase. The setup bracket is not:
building a workload now also sets the hooks of `MatrixSupport` (the
fingerprint, the use, the maker count, and `ruleList := rs`, which shares the
list the workload builds anyway), so the setup words gain the closures of a
few assignments, a small constant that does not grow with the number of rules
and is equal on both sides of a grid. The fixture dprocs share one closure
(`dprocApply`), so the counter adds no words per dproc: a per-reducer closure
over it added about 3 words per reducer to the setup of `exclude_dproc` and
`exclude_mixed` (`PolyML.objSize` of the built workload: 20, 290 and 2990
words more at 10, 100 and 1000 reducers for `exclude_dproc`), which the shared
closure removes; the n reducers cost what they did before the counter. The setup words of a new grid
(`alloc-z/`) therefore do not equal those of an older one (`alloc/`) at any
size, and a comparison across grids (`alloc/` at Y against `alloc-z/` at Z)
uses only the
operation rows (`operation_first`, `operation_steady`, `apply`), never the
setup row.

**Gating by header.** A grid whose header says `structure: "v1"` (every new
run) requires the four records in every process, and a header without the key
forbids them, so every earlier archive (TASK29B, the TASK30 `alloc/` made at
63ac28189) parses and replays to the same decisions and results byte for byte.
The key enters `grid_digest` and the cell binding only when present.

**Rows.** `allocation_analysis.cell` adds `work` to a cell: one row, named as
the events are, for every count that appears in some process (absent on a
side is zero) of each run (`work.first.K`, `work.second.K`, `work.use.K` with
K one of `trace.L.ACTION[:message]`, `kernel.RULE`, `maker`, `collector`,
`dproc`), and
`result.digest` for the digest. A row is `equal` when candidate equals
baseline in every pair, `differs` when some pair does not, `inconclusive`
when the baseline is not one value across all the candidate pairs and the
baseline/baseline control (the control included); `deterministic` says whether
each side reproduces across pairs. There is no allowance and no direction:
fewer events differ too. Work rows are not slopes and not constants and are
never an input of the words' `status`. `decisions.json` gets a separate `work`
section (per cell status; rows that are not reproducible; the cells without
work rows and the unresolved cells) and `work_status` (`equal`, `differs`,
`inconclusive`), only when the archives have work records; `RESULTS.md` gets a
Structural evidence paragraph and table. The words-only `status` and its
`nondeterminism` list are the ones of before.

**Keys that can grow.** A `trace.L.TEXT:message` key carries the message,
and a message may name a rule (`USER_CONV` writes the conversion name), so a
workload whose per-rule conversions fail would give up to n distinct keys,
and up to 3n rows per cell, and `decisions.json` would grow with n. No
current case does that (the rules match their own constant keys, bounded
rules are anonymous, and the 13 cells give a constant number of keys). A new
case with per-rule failures must normalise or drop the message first.

**Per-cell evidence.** `allocation_analysis.work_groups(cell["work"])`
returns, per cell, the names of the count rows that are non-empty (nonzero on
either side) in each of `first`, `second` and `use` (`None` for a cell without
work rows); it only describes, and infers no class. `cells_work_groups`
takes a decisions structure (`decisions["cases"][case]["cells"][size]`, as
loaded from `decisions.json`) and returns `{(case, size): groups}` with the
size an int, the key by which a disposition looks a cell up.

The evidence class of a cell is fixed by its case in the disposition
(`task30_dispose.py`), never read from the rows, since a hook regression
(`useResult` left at `noUse`) would give empty rows that are `equal` on both
sides. The classes and what each must show (and the cell must also be `equal`
and deterministic):

- `deletion`: `work.first` and `work.second` are empty (the operation fires
  nothing) and `work.use` has `work.use.trace.4.REDUCE`;
- `dproc-deletion`: as `deletion`, and `work.use` has `work.use.dproc`;
- `operation`: `work.first` and `work.second` are both non-empty and
  `work.use` is empty.

**Grid status.** `work_status` is `differs` when any resolved cell differs,
`inconclusive` when no cell differs and some cell is not equal, lacks work
rows or is unresolved, and `equal` only when every cell of the grid is equal.
A disposition that cites the work rows still reads the per-cell rows of
exactly its 13 cells (`work.cells`, and `cases[...].cells[...].work`), not the
grid-level `work_status` alone.

**What the counts cover.** A deletion (`-*`, `remove_ssfrags`,
`exclude_ssfrags`) filters the net and the dprocs and runs no simplification,
so the operation itself emits no trace event and no inference: the counts of
`work.first` and `work.second` for those cases are empty (apart from callback
counts that are zero by construction). For such a cell the rows show:

- the operation fires no counted event, no inference, no maker and no
  collector, on both sides;
- `work.use`: through the net only, the events and inferences of the n
  lookups. With the per-index REFL set and the hash of the non-REFL results
  of the digest, that pins which installed left sides still rewrite and to
  what, and the fragment and dproc names. For `exclude_dproc` and the dproc
  half of `exclude_mixed` the net is empty or holds only the data, so the
  lookups find nothing for the dprocs: for `exclude_dproc` all n lookups are
  REFL, for `exclude_mixed` 9999 rewrite and 1 is REFL (the deleted rule).
  They show nothing about the deleted dproc. The dproc deletion is shown
  there by the `dproc` count of the use (the dprocs held, applied directly,
  `3(n-1)`, which restates the `dpnames` of the digest), by the exact
  allocation words and by source identity;
- the records are deterministic across processes, and the same on both sides.

The marker and tactic cases (`operation` class) run one `SIMP_CONV` or
`SIMP_TAC` and give the `REDUCE` event of one traversal of the target and a
handful of inferences in the operation itself. In all four cells
(`exclude_marker`, `exclude_marker_reuse`, `exclude_tactic_reuse`,
`exclude_tactic_complete`) the `-*` of the 10000-entry source runs inside the
timed call: `SIMP_CONV` is curried and runs `process_tags` (with the `-*`) on
every application to a term, and `SIMP_TAC` reaches the same conversion. The
deletion is therefore visible only in the operation words (and the source
identity), as the filtering of the net (`Ho_Net.vfilter` and the name match
per entry) is untraced. The traced work is one `REDUCE` plus a REFL (or the
fixture's ASSUME), and for `exclude_marker` and `exclude_tactic_complete` also
the three inferences that build `Excl`; the reuse cells reuse only the `Excl`
marker theorem and save only that construction, not the deletion.
`work.use` is empty in all four.

**What no row can show.** The following are outside every count:

- CPU work that neither allocates nor traces (an extra `List.exists` or
  length over the history or the net, a non-allocating compare loop);
- net node visits (a lookup counts the entries it invokes, not the nodes it
  visits; a deeper net with the same leaves counts the same), and the net
  candidates a successful match hides;
- live heap and retention: equal allocated words do not mean an equal live
  graph; a result that keeps the old net reachable costs GC time at equal
  words. The candidate's startup heap is about 1.01M words larger in every
  cell, which no work row shows;
- work outside `Trace.trace` and the kernel's primitive-rule counter
  (`Term.match`, `aconv`, `Ho_Net.match`, `Binaryset` and `Binarymap`
  operations, Feedback traces), and any dproc that does not call the
  fixture's counter;
- the context: the work phase runs in the allocation process after all
  bracketed runs, not in the timed process, and not cold;
- code layout and heap differences from the files outside
  `task30_cases.SOURCES` that the candidate changes (the `*Ext` modules,
  `ThmAttribute`, boss), which are timing-only effects.

The case for the 13 cells therefore rests on the source identity of the timed
code (the sources of the listed path are identical between develop and the
candidate except the pinned `Cond_rewr` and `SimpTracking`, a move of
`note_rewrite` and `with_tracking`) and on the exact operation words; the
work rows show the same deterministic behaviour and result, not equal CPU.
Equal rows with develop say that the candidate fired the same counted events
for the operation and for the use of its result and returned the same result,
not that it took the same time.

**Operator smoke.** `smoke_matrix.py` runs `workPhase` twice for every case
and size it covers, requires the second run of the first call, both runs of
the second call, the use and the digest to agree, and records the work
records of each process in its manifest. It then compares the work records of
the baseline and the candidate per case and size (`compare_sides`, in the
manifest under `cross_side`: the number compared and every difference with the
differing counts), and exits non-zero on any difference. `--compare MANIFEST`
makes the same comparison of an earlier manifest without running anything.
The manifest is the full record (the runs with every work record, the head
the fixture was taken from, the sealed inputs); the run also writes
`NAME.summary.json` (`smoke_matrix.summarise`, per side, case and size: the
events, inferences and `maker`, `collector`, `dproc` counts of each record
and the SHA-256 of the digest, and the cross-side comparison), which is
derived from the manifest alone, and `--compare MANIFEST --summary PATH`
derives it again. The retained smoke evidence is such a manifest and
summary.

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
