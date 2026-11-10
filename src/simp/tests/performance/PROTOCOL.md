# Simplifier performance acceptance protocol

This document states the rules of the measurement and gate machinery under
`src/simp/tests/performance/`. It is measurement infrastructure, **not final
acceptance or independent-build performance evidence**. Do not label shared
`hol.state0` comparisons independent. Finite measurements also need the
corresponding source/layout/callback work audit.

## Harness

The front end `acceptance.py`, the paired runner, the matrix fixtures and the
archives they write. The sections below state the protocol of one experiment
(counts, schedules, records, locks); the statistics and decisions follow in
"Statistics and policy", the grids built on them after that.

### Isolated-source front end

From the repository root. The host is shared and no exclusive window is
required; a checkout's own builds and measurements stay serial, under its lock.
`--authorize-measurements` is the explicit authorization to build and measure,
not a claim of exclusive access. Standard input and the compiler version
query are specified in "Standard input and the version query". Run:

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
baseline/candidate** for each requested case and size. Each child invocation
is:

- the existing `tests/compatibility/run_paired.py`;
- `--matrix-performance --performance-case CASE --performance-size N`;
- `--candidate-signature pass --candidate-behavior baseline`;
- identical samples, batch duration, process timeout, and >=10 pairs.

A baseline control uses the baseline commit in both selection slots. It has the
same sample counts, fresh processes, calibration and AB/BA order as its
candidate comparison. No control costs are subtracted and no baseline
variability is a regression budget. A baseline-control `fail` or `inconclusive`
prevents a candidate pass (turning it inconclusive); a candidate failure is
never excused by control noise. This applies to point metrics and
retained-storage slopes.

The SML harness consumes and verifies construction, reuse and
complete-operation results. The Python schema contract is `suite="matrix",
case=CASE, size=N`, one label CASE, consumption 1 per operation, and
`storage=False` (not the old fixed storage-row protocol). Process environment
includes `PERF_CASE` and `PERF_SIZE`. The installed `Performance.sml` must
match the recorded MatrixPerformance or ClientPerformance input hash.
Callback/proof verification belongs in the fixture; a nonzero exit, missing
observation or ignored result is not an observation.

Acceptance requires >=10 fresh **process pairs**, not merely ten batches in one
process. Each process calibrates by doubling iterations. Every measured batch
must last at least half the calibration target, with >=3 measured batches.
Process pair order is AB, BA, AB, BA, ... with no missing, duplicate or
reordered receipts. Warm-up/calibration work is recorded separately, not
silently counted as independent samples. Increase the predeclared batch
duration for tiny work.

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
adaptive protocol for replay, not proof that its GC comparisons are
unconfounded.

The count is bound to the manifest, `PERF_ITERATIONS` environment, complete
ordered calibrations, samples and consumed-result counts by online and offline
validation. Injecting that environment variable into an adaptive archive also
rejects. `analyze(..., iterations=N)` must match the requested schedule;
default analysis cannot silently admit fixed-mode evidence. No timing, GC,
control, confidence-interval or pass/fail threshold changes with this mode. In
particular, equal counts cannot turn uncertain B/B controls or zero/zero GC
into passes.

### The `warmup` schedule

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
  schedule): `N = max over the develop-only pilot processes of ceil(HEADROOM *
  seconds * n / wall)`, where `n` iterations and `wall` seconds are the final
  calibration batch of one process and `seconds` the cell's batch seconds,
  computed in exact arithmetic on the recorded decimals. New tables use
  `HEADROOM` 1, so that a batch lasts about the target: N is the count that
  takes `seconds` in the process of the pilot that was fastest per iteration at
  its final batch, so a batch of any pilot process would last at least the
  target at that speed, and a batch is shorter than half of it only if a
  process (a candidate included) runs more than twice as fast per iteration as
  that fastest pilot process. A slower process only lengthens its batches. A
  cell where it does happen fails closed, and the revision path below
  multiplies its count by 4 (reason "fixed batch too short" for this schedule).
  The counts file records the schedule, the rule and the headroom;
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
  loaded one.
- **New tables use `warmup`.** `timing_grid.Table` defaults to `schedule=
  "warmup"` with headroom 1, with unchanged pairs (20 in the first stage, the
  20 of the second-stage formula). `warmup` is the default because on a
  validation (develop/develop experiments of 12 TASK30 cells, 20 pairs and 5
  samples each) the median over the cells of the ratio of the B/B 95%
  interval widths, warmup over `ramp`, was at most the predeclared 1.10, in
  a fraction of the time. The least warm-up (under `ramp`: final calibration)
  or sample wall over its target stays above one half with room, so the
  half-target check holds. The warmup schedule needs fixed seconds, so a
  table without them names `schedule="ramp"` (it is refused otherwise: a
  default never depends on another argument).
- **The TASK30 and TASK29A tables keep `ramp`**, with their counts files,
  pilots, grids and ledgers; both tables say `schedule="ramp"` themselves,
  and their archives replay unchanged at this code. The history seals are
  compared per field, as for TASK29A (each field of the code may be the
  current one or one of its history, so a record may pass with a combination
  of fields that no one commit held), and the only code added to what is
  accepted is the sealed blobs that the histories list (`DRIVERS`, `ENGINES`,
  `ACCEPTANCE` and `SEALED_HISTORY` of `task30_grid.py`).

### Precompiled experiment driver

Both matrix fixtures compile calibration AND sampling inside `experiment`
before either executes. The calibrated count is a runtime local, not a global
constant available when the compiler subsequently builds `sample`. This also
removes intervening sample-compilation allocations. The workload, complete
calibration history, result checks, timers and decision policy are unchanged
by it.

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
serial guard for BOTH fixtures. These assertions are scheduling tests, not
HOL timing or allocation measurements. Run separately from the repository root:

```sh
W bin/Holmake --no-project --no-cache --no_prereqs \
  -C src/simp/tests/performance -j1 driver-staging-control
```

### Runtime, graph and release records

Both matrix fixtures load sealed `RuntimeMetrics.sml`. Every calibration and
sample has exactly one `@@MATRIX_RUNTIME` record matched in order to its stage
and iteration count. Before/after snapshots supply actual full/partial GC and
sharing-pass counts, GC-updated heap/free sizes, allocation-area capacity/free
space and Linux `/proc/self/status` RSS/HWM bytes. Snapshot/record work is
outside timing; counts are batch-boundary counters with small record/timer
overhead, not cycle-exact attribution. `/proc` reads and semantic verification
are outside the counter interval. Missing RSS is explicitly blocked, not zero.
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
- VmHWM is the **process-lifetime** maximum including loading and prior
  batches. HWM increases and RSS snapshots are measured, not exact temporary
  peaks. An isolated high-water accounting domain remains unestablished. A zero
  HWM increase is not evidence of zero temporary memory.
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
`acceptance.py`/`loading.py`, smoke drivers do not take the host-wide serial
lock. They clean private trees automatically, retaining compact source-tied
receipts.

### Acceptance record, admission and exit codes

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
repo's `hol.state0`), runtime/heaps/Holmake/configuration fingerprints, a
sealed successful Poly/ML version command, sealed successful dynamic-library
discovery and fingerprints for its libraries. Selected builds must have
succeeded, and each launcher's text, options and product hash must agree. These
are local provenance-consistency checks, not authentication of a malicious
producer or independent-build evidence. Non-matrix historical diagnostic audits
retain their original weaker contract.

CLI exit codes: 0 = all reported candidate metrics/slopes pass; 1 = any fails;
2 = uncertainty, invalid evidence or a blocked prerequisite. `success=true`
means the experiment completed and validated, **not that its metrics passed**.
No overall performance acceptance decision substitutes for per-metric
decisions.

### Serialization

`run` and `controls` hold nonblocking `flock` locks for their entire
experiment:

- `.agent-files/hol4-performance-UID.lock` in the repository (one per
  user; ignored, and out of reach of shared `/tmp` cleaners);
- the repository gitdir inode (compatible with existing exclusions/tactics
  runners), and common gitdir inode (across worktrees).

Descriptors are inherited by the paired runner so it cannot continue unlocked
if its parent exits. A busy lock blocks the invocation. Never unlink a
lockfile: that permits two different inodes to be locked concurrently. Do not
relock these inherited locks in child runners. All invocations of this front
end serialize; the existing gitdir lock also conflicts with older same-worktree
runners. Locks are advisory: they cannot stop unrelated manual `bin/build`,
direct older runners in other worktrees, or other users. Authorization confirms
those are quiescent. Do not use `--authorize-measurements` as permission for
concurrent work. Unit tests acquire the same lock for actual timing controls;
other tests create only tiny temporary synthetic git repositories and remove
them immediately.

### Standard input and the version query

Poly/ML enters its top level and reads standard input, so every child that
can start Poly/ML or HOL gets `/dev/null` (`run_paired.execute`,
`loading.execute`, `acceptance.run_logged`, `verify_builds`,
`api-audit/run.py`). The exception is git calls (`acceptance.git`,
`run_paired.git`), which inherit it. The harness's own configure runs are
`poly --error-exit --use tools/smart-configure.sml` through
`loading.execute`, so they get `/dev/null` too (`startup_gate.py`,
`allocator-counter/bootstrap_probe.py`). `verify_builds` nevertheless accepts
an independent build whose configure step has the input file
`tools/smart-configure.sml` (`run_logged` supports `stdin=path`) and checks
its hash; the harness makes no such call. The compiler is queried with
`poly -v`; `poly --version` enters the top level.

The runners `fragments/assembly/run_assembly.py`,
`tactics/performance/run_tactics.py` and
`exclusions/performance/{run_exclusions,gc_run,gc_trace}.py` still call
`poly --version`, through `run_paired.execute`. That is safe because
`execute` gives `/dev/null`: the command reads end of file and prints the
banner `Poly/ML 5.9.2 Release` alone, which `run_assembly.py` checks exactly.
With `-v` the output would carry the RTS line and that check would fail.

- **Version comparison.** `acceptance.poly_version_matches`: a recorded
  version that contains `RTS version` (a `poly -v` record) must equal the
  live `poly -v` output in full once stripped; a legacy record (banner
  alone, made by `poly --version`) is compared with the banner of the live
  output, as is a legacy record against a new probe.
- **`api-audit/run.py`** queries `poly -v` and runs `selftest.exe` with
  `/dev/null` as stdin and timeouts (30 s, 1800 s). No retained receipt or
  manifest seals it other than the receipts' own `sources` entry, which
  `loading.semantic_gate` compares with the api-audit files of the checkout
  being measured, so a receipt made by another version of those files is
  refused and the eight-process receipt a gate needs is made by the current
  `run.py`.
- **Other audits** (`check_task27_docs.py`, `run_task22_negative.py`,
  `audit_task27.py`, `compatibility/interfaces/check_design.py` and
  `native-extension/check.py`) take `stdin=/dev/null`, with a timeout. They
  start Holmake, HOL-compiled executables or a dependency tool, no Poly/ML
  top level. Git calls are left alone.

### Negative controls

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
`tracemalloc` is **only a Python harness allocation control**, never a
measurement of HOL/PolyML allocation. Bootstrap confidence is not a universal
hardware proof.

## Statistics and policy

The rules by which one experiment, and then a grid of them, is decided.

### Statistics and decisions

Fixed before candidate results are observed:

1. Discard **no outliers**, batches or process pairs. No trimming or rerunning
   just unfavorable observations. Any rerun is a new whole experiment.
2. Within each process, take the median batch cost per operation separately for
   inclusive CPU, wall, and GC. Poly/ML CPU includes GC; do not add GC again.
   Validate nongc+GC accounting and the positive-GC timer control first.
3. Form candidate/baseline ratios within each process pair. Report raw process
   observations, both medians, every ratio and their median. Do not replace
   paired ratios with a ratio of pooled medians or pool workloads together.
4. Bootstrap the **paired ratios**: 20,000 resamples, deterministic seed 3003,
   percentile ranks 499/19499 (zero-based), the existing `summarize.interval`.
5. For each workload/size/metric: CI lower bound >1 means **fail**; upper bound
   <=1 means **pass**; otherwise **inconclusive**. A reproducible slowdown of
   any size fails. No fixed percent allowance, aggregate mean or compensating
   speedup.
6. A zero denominator, including GC 0/0, means inconclusive with null ratio/CI;
   keep the pair and raw values. Do not turn undefined GC ratios into parity.

Rule 5 is `POLICY` (version 1). It tests whether the candidate is *faster*:
a candidate with no real difference passes one metric about 3% of the time,
and its B/B control must pass the same way, so a performance-neutral change
cannot pass a grid. Archives made under it replay under it.

### Equivalence policy (version 2)

Decided by the policy owner; `acceptance.EQUIVALENCE_POLICY`. `acceptance.py
run` and `task29a_grid.py` record it in every new report, and offline replay
uses the policy a report recorded. Rules 1–4 and 6 are unchanged.

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
  the historical grid (`task29a_iterations.json`). Pairs and samples
  are run options (minimum ten and three), fixed before the run and recorded
  in its inventory.

### Code-layout randomization and second stage (TASK29A)

Every fresh process compiles its selected sources at startup, so the address of
all later code depends on everything compiled before it. This alone moves the
per-operation cost of the large fragment cells. Develop processes with the same
code-area size run alike, and both B/B sides share one layout. A source change
elsewhere that moves the layout therefore looks like a slowdown or speedup at a
fixed layout.

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
  the policy owner). It replays both stages and leaves every
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

## Seals and seal histories

A record carries the seals (content hashes) of the code that made it, and a
replay accepts it only when each seal is the current one or one that the
history of that file lists. So a change to a file whose seal a record
carries appends the old seal to its history in the same commit, and the test
that pins the history constant is edited with it:

- the TASK30 table (`task30_grid.py`): `DRIVERS`, `ENGINES`, `ACCEPTANCE`
  and `SEALED_HISTORY`, and `task30_pins.PIN_HISTORY` for the pins;
- the follow-up (`task30_followup.py`): `DRIVERS`, `ENGINES`, `ACCEPTANCE`
  and `SEALED_HISTORY`;
- the TASK30 disposition (`task30_dispose.py`): `HISTORY`, and `ADDED` for a
  file added to its `CODE` after records were made;
- the TASK31 timing table (`task31_grid.py`): its own `DRIVERS`, `ENGINES`,
  `ACCEPTANCE` and `SEALED_HISTORY`, empty until its first record; its pins
  are the `history` of `task31_attributed.json`, which `pin_history` reads;
- the TASK31 disposition (`task31_dispose.HISTORY`).

A file whose seal no record carries needs no entry (usage text, style). The
cascade, with a worked example, is in the bullet "Seal histories" of "TASK30
follow-up". The disposition checks (`task30_dispose`, `task31_dispose`) name
every changed file and the entry to paste; the grid's `check_code` names the
changed driver, engine, acceptance or sealed file, or the layout-seed check,
and no entry to paste. The follow-up's and the disposition's histories hold
the seals of `40e176538f`, the code that made their records.

## Timing grids, replay and resume

`timing_grid.py` is the engine: pilot, predeclared counts, run, second stage,
`--resume`, replay and close. The tables built on it follow.

### Shared timing grid and the TASK30 table

`timing_grid.py` is the TASK29A grid with the task-specific parts removed.
A task supplies a `Table` (cases, batch seconds, predeclared counts file,
sealed code, historical seals); the policy, the layout randomization, the
second stage, the archives, `--resume` and `replay` are the ones above and do
not change. `task29a_grid.py` is its TASK29A table plus the TASK29A
disposition; `task30_grid.py` is the TASK30 table (24 cases, 144 cells); its
disposition, with that of its follow-up, is `task30_dispose.py` (below).

#### Cells and predeclared counts

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
  replays. A follow-up table (below) also takes the grid it replaces and that
  grid's pilot: `--replaces GRID --replaces-pilot DIR` for `predeclare`,
  `--replaces GRID` for `verify-counts` and `run`, nothing for `extend`, and
  `--replaces-pilot DIR` alone for `replay`; `extend` and `replay` find the
  grid where their record says it is. `predeclare` and `replay` always
  replay the grid in full and read the pilot (`--replaces-pilot`).
  `verify-counts`, `run` and `extend` bind it by the seals of the counts and
  ignore the pilot while the code of the replay is that of `predeclare`;
  when it changed they replay in full, read the pilot, and refuse without
  `--replaces-pilot DIR` (see "By seals" below). A table that replaces none
  refuses both options. The baseline of the counts, of the table and of
  `--baseline` (which defaults to the table's) must agree; a candidate equal
  to the baseline is refused. The layout seed, pairs and samples are the
  table's at `predeclare`, which copies them into the counts file; `run`
  refuses a file that does not say what the table says and a different
  explicit
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
#### Attempts ledger

- **What the commit claim is.** Git proves the order of the counts file
  relative to the *candidate commit* (the file is in the candidate's history
  and one commit made it), and, with the rule above, that no free count is
  left: the counts are a function of the pilot and the table. It does not
  prove the order relative to any *observation*: the candidate's code can
  have been measured under an earlier commit (the same code can be observed
  under an earlier commit). The attempts ledger is what makes a retry
  visible, as a discipline and not as a proof.
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
  it: never run it in a checkout that holds them. Before the first cell `run`
  and `extend` append a JSON line with the event (`open`, or `resume` after an
  interruption), the stage (`first`, `second`), an attempt id (a second stage
  has its own, and a retry of it another), the candidate, the counts file and
  its seal, the layout seed, the output path, the absolute path of the checkout
  and the UTC time, and at the end a `close` line with the status (`pass`,
  `fail`, `inconclusive`, ...; `partial` for a diagnostic subset, `interrupted`
  when it stopped, and `checkout-changed`; see *when the checkout is judged*
  below, for what an `interrupted` line does not say). A close that cannot be
  written is reported on standard error (`ATTEMPT-NOT-CLOSED`, with what the
  close would have added), leaves the attempt open in the ledger, which shows
  it as interrupted, and does not replace the outcome of the run. The lines
  form a hash chain: each carries `prev`, the SHA-256 of the line before it (64
  zeros for the first), so a line removed or changed in the middle is refused
  (`attempts ledger chain broken at line N`), as is a malformed line. A crash,
  a full disk above all, may leave lines at the end that are no record: one cut
  line, or several when the acknowledging append was cut too. Any run of them
  at the very end, however each is ended, is tolerated and reported
  (`LEDGER-TORN-LINE`, once for each); the next append ends the last one and
  writes a `torn` record naming the hash of each, so none is lost or silent.
  The same lines followed by a line that is no record of the chain, or in the
  middle of the file, are refused. A complete record without its newline is
  kept (`LEDGER-UNTERMINATED-LAST-LINE`). A resumption (`run --resume`, `extend
  --resume`) checks that the ledger holds its opening before it measures.
  `replay` needs the ledger and the grid's opening line in it, verifies the
  chain, and prints every attempt of the table with its stage, time,
  resumptions, every status it closed with (in order, comma separated;
  `interrupted` for a stop with no close), candidate and the checkouts of its
  lines, marking the one of the grid replayed and those of its candidate
  (`ATTEMPT id first opened T resumed N status S candidate C checkout P (this
  grid)`), with the counts (`ATTEMPTS of TOY: N in the ledger, M of this
  candidate C`), so a reader of a replay sees each retry and each close of it,
  also of another candidate. `close` replays the timing grid, so it prints the
  same lines, and repeats the counts in its line. A rerun under the same
  settings, after a pass or a non-pass alike, is a new draw: a new attempt in
  the same ledger, its predecessors stay in it, and the report of the result
  publishes the whole ledger, not the line of the grid that passed. **One
  checkout.** The ledger is of a checkout, so a grid and every retry of it, the
  second stage included, are made in the one checkout: a draw made in a second
  clone is in that clone's ledger and the first would not show it. Each line
  records the absolute path of its checkout, so a ledger that holds lines of
  two paths, in the opening of an attempt or in a resumption or close of it,
  says so (`LEDGER-CHECKOUTS: N different checkouts` in a replay), and a clone
  made from the first, with its ledger copied, shows as lines of a path that is
  not the clone's. `replay` and `close` alone take `--ledger FILE`, read-only,
  to replay in another checkout against the ledger of the one that measured (a
  copy of it); `run` and `extend` never take it, and a measurement appends only
  to the ledger of the checkout it runs in. **The ledger is a discipline, not a
  proof:** the chain shows that no line was removed from or changed in the
  middle, not that lines after the last one, or the whole file, were not
  removed. That deletion is undetectable here, and what covers it is that the
  report of the result names the ledger and that a reviewer asks for it.
#### Revisions and the route after a regression

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
- **The route after a regression.** The task asks for a diagnosis, a fix and
  a rerun. A production fix in a pinned file changes the candidate's blob of
  that file, so the pin is stale and `run` refuses (below). The route, in
  order: fix the production code; compute the new blobs and write the new pins
  into `task30_pins.py`, adding the seal of the previous version of that file
  and the pins it held to `PIN_HISTORY`, a dictionary in `task30_pins.py`
  itself (so the grids it judged still replay, and the driver, which every grid
  seals, does not change for it); commit the result as a new candidate commit,
  and run `prepare` at it, for the production fix is a source outside the
  performance area (the counts file is already in its history, and the pilot,
  the counts and the sealed files are untouched, because the pins file is not
  among them); run a new complete grid under the same counts file, then the
  second stage and the allocation gate as for any candidate. Every attempt, the
  regressed grid included, is in the ledger, and the report of the result
  publishes the ledger. If the fix changes what is measured (a fixture or a
  sealed file), the counts must be derived again: a `--repilot` revision.
- **Batch seconds.** A table gives all cells one calibration target and may
  name a longer one for cases whose single operation is tiny, so that a
  batch stands clear of the per-batch overhead (the ten direct deletions of
  TASK30 use 1 s, the others 0.3 s). The seconds are part of the counts
  file, checked by `run`, and used again by `replay`.
#### Source identity, pins and theory hooks

- **Source identity.** The operations of TASK30 run through source files that
  the candidate may have changed: `task30_cases.SOURCES` lists them, each
  `.sml` with its `.sig`: the simplifier (`simpLib`, `Ho_Net`,
  `BoundedRewrites`, `Traverse`, `Travrules`, `Opening`, `Cond_rewr`,
  `SimpTracking`, `Trace`), the marker library (`markerLib`, `markerSyntax`)
  and the modules the cases call through them (`liteLib`, `Theory`, `Context`,
  `Uref`, `Drule`, `Conv`, `Tactical`). `run` records the git blob of each file
  at the baseline and at the candidate in the inventory and prints every file
  that differs (`SOURCE-DIFFERS path`). Such a grid is never a pass: its
  decisions name the files in `source_identity` and a status that would be
  `pass` becomes `inconclusive`, whatever the cells say. `replay` and the
  second stage re-verify the record against git. This is the evidence for "no
  extra source scan": neither gate sees a scan that allocates nothing and costs
  a few percent, so the identity of the code on the path, not a measurement,
  shows that no scan was added there. The boundary: what is not listed stays
  outside the identity (the kernel, the parser, `ThmAttribute`, `Lib`,
  `testutils` and the build files among it: every operation and the harness
  itself go through them, so a change there moves both gates and is for review,
  not for a list of this size), and the identity of a file says nothing of the
  data it works on, such as the size of the theory graph; the fixtures fix
  that. The inventory therefore records, besides the listed files, the sorted
  name-status list of every file under `src/` that differs between the baseline
  and the candidate (`source_tree`; `replay` derives it again from git), so
  everything that differs, listed or not, is published. A reviewed difference
  may be pinned: `task30_pins.PINNED` maps a path of the list to the exact
  candidate blob and the reason. A file that differs is accepted only when its
  candidate blob is the pinned one; it is then published under
  `source_identity.reviewed` with its reason, prints no `SOURCE-DIFFERS` and
  does not change the status. Any other blob of it, and any other file, behaves
  as above; a pin on a file identical to the baseline or outside the list is an
  error. A file the candidate adds (absent at the baseline) is recorded with no
  baseline blob and is accepted only with such a pin; unpinned, or absent at
  both commits, it is refused. `replay` and the second stage re-derive all of
  it, so the record is not trusted. The pins are in a file of their own, whose
  seal every grid records (`pins`) beside the sealed files; a grid replays by
  the pins it was judged by, the current ones or those kept in `PIN_HISTORY`
  (in `task30_pins.py`) under the seal of that earlier version (otherwise
  `changed pins`). `run` refuses, before any measurement, a candidate with a
  source that differs without a current pin (a stale pin is one), because that
  grid could never pass: it prints `SOURCE-DIFFERS` and stops. `--only` still
  measures a diagnostic subset, marked `diagnostic` in its inventory, which has
  no decisions, can never complete a grid, and cannot be resumed without
  `--only`. The reviewed difference is the one `note_rewrite` spec added to
  `Cond_rewr.sig` (see the next item). The pin tests compute the blob of each
  file in the checkout and compare it with the pin, and with the baseline's.
- **Pins and the sealed source list.** `task30_pins.PINNED` holds only
  `Cond_rewr.sig` (one added spec, `note_rewrite`); `Cond_rewr.sml` is
  develop's and has no pin, since a pin on a file identical to the baseline
  is an error. The earlier pin sets are in `PIN_HISTORY`, and a replay
  judges a record by the pins its pins seal names (`pins_for`), also for a
  file the baseline lacks (`source_record(..., pins)`); a new run is judged
  by the current ones. `task30_cases.SOURCES` is sealed and lists
  `SimpTracking.sml`/`.sig`, which exist at neither commit, so a new TASK30
  run refuses with `source file absent at the baseline and not pinned:
  src/simp/src/SimpTracking.sml`.
- **Theory hooks.** `Theory.register_hook` is the way a module adds work to
  a theory transition. A candidate that registered a hook on an ordinary path
  would not be visible to the source identity of the listed files alone, so
  the candidate is audited: every caller of `register_hook` in the baseline
  and the candidate, ordinary or test-only, is listed, and each caller the
  candidate adds is shown not to be on the path of the cases (for example
  because the module is not in the ordinary heap and no fixture loads it).
  A search for the text `register_hook` is not enough:
  `ThyDataSexp.sml` registers a hook for each data type made by
  `ThyDataSexp.new`, so a new user of `ThmSetData`, `AncestryData` or
  `ThyDataSexp.new` adds one too. The audit therefore covers those names as
  well, over the ordinary sources and the lines changed in them (`git diff
  BASELINE CANDIDATE -- src` outside the tests, and `git grep` of each name
  at both commits). This audit is repeated for a new candidate.
#### Decisions and whole operations

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
- **Whole operations.** The timed operation is the fixture's complete `run`,
  and its result is verified in the same process, so work cannot move into
  unmeasured preprocessing: a batch contains the construction or call being
  gated and whatever it needs (the setup of a case, such as the theory
  transition of `history_theory_change` below, is outside the batch). The
  fixtures assert the callback counts of the maker and collector cases
  (`history_collectors`, `history_makers`) exactly and check the resulting
  simpset of every deletion; `exclude_dproc` and `exclude_mixed` assert that
  the deletion calls no maker and no collector (zero of each: `-*` runs
  neither). Their simpsets are built with the maker and the dprocs first and
  the data after them, so that a rebuild of the history would, by the reading
  of `++` and `build_from_history` in `simpLib.sml`, prime the dprocs (`++`
  passes the rewrites of each later fragment to `Traverse.addctxt`) and, where
  data follows (`exclude_mixed`), run the maker, so the zero counts would fail;
  `exclude_dproc` has no data, so there only the collectors would be primed.
  They are zero because the deletion replays nothing. The counts of a rebuild
  are not asserted. The fixtures do not count scans, and production records
  none. The allocation matrix (`allocation_matrix.py --task task30`) brackets
  setup, first and steady operation and verification of all 24 cases and
  compares exact allocation words and their size slopes between the sides.
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
#### Checkout, resume and replay

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
  only reads, so the checkout stays clean. The
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
  The log is `prepare.log` beside the ledger (`prepare-NAME.log` for a table
  of a family that is not named like it), replaced by the next `prepare`
  (one file, so the disk use does not grow, and it is not the record of a
  build: the durable record of the build a pilot or a grid ran with is the
  products digest in its inventory, `checkout.products`); the default timeout
  is four hours for each of the two commands. Only if configure and the build
  exit 0, configure prints its last line, and the checkout is clean at the
  same `HEAD` does it write
  `.agent-files/evidence/<table>/build-stamp.json` (`build-stamp-NAME.json` for
  such a table). A failed, timed out or
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
  build makes the heap again, and repeated `prepare` runs at one commit
  give the same head and tree and different digests. The digest is not
  made stable. So **a grid that is stopped, or
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
  `interrupted`.
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
#### Method for a new table

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
     non-zero; `close` applies no disposition and keeps reporting "not
     pass" while a cell is not a pass: the final verdict is
     `task30_dispose.py` (see "Structural evidence and the TASK30
     disposition"), which replays this gate, the follow-up and both
     allocation grids. The comparison of the
     two harnesses is `task30_grid.harness_match(timing, allocation)`, which
     a later pairing of another timing grid with its allocation grid uses as
     it is. It compares the cheap records
     (candidate, baseline, harness) before it replays anything, and needs the
     ledger (`--ledger FILE` for a copy). Because the timing grid is measured
     at `HEAD == Y`, the allocation run must be made in a clean checkout at Y
     too; the grid's record holds the checkout, the same tree as Y, and any
     clean checkout at Y serves: `close` compares the head and the tree seal.
  7. After the follow-up (`task30_followup.py`) and its allocation grid at Z:
     `task30_dispose.py --record`, then once more without `--record`, which
     is the final verdict of TASK30 (below).
- **A cell that is too short.** A cell rejected as "fixed calibration too
  short" is a non-pass and blocks the grid. The only route is a counts revision
  (above) that multiplies that cell's count by 4 for baseline and candidate
  alike, committed with a new candidate commit, and a complete new grid (a cell
  cannot be merged into another grid, and `--only` decides nothing); the first
  grid stays published and replays against its own file (the other link, a
  fresh pilot, is for a change of what is measured). The revision is a reaction
  to a candidate observation, so it is a new draw like any rerun, recorded in
  the ledger, and the report of the result states it. The code does not check
  that the previous grid rejected the cell; the reviewer does. No code changes
  for it: the ordinary exclusion path (`simpLib`) is identical to develop (see
  source identity), so a candidate that runs twice as fast as the baseline is
  not expected, and a count that proves too short is a property of the pilot.
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
  candidate to that of the timing grid; `close` does. TASK30 has two
  harness pairs, each timing grid with the allocation grid of its own
  harness, each compared exactly (`harness_match`: head and tree outside the
  performance area, a clean checkout): stages 1 and 2 at Y with the
  allocation grid made at Y (`close`, and the disposition), and the
  follow-up at Z with a full `allocation_matrix.py run --task task30` at Z,
  with its own toolchain and controls receipt (the disposition only). The
  two are never relaxed into one: a Y timing grid with the Z allocation
  grid, or the follow-up with the Y one, is refused.
- **Cost.** The grid is 144 cells at 20 pairs and two slots per pair, each
  slot a fresh process with its batch (0.3 s, or 1.0 s for the ten direct
  deletions at every size, including 10000). A second stage adds the cells
  the control leaves open.
- **Other tables.** The TASK29A table is closed: its grid was disposed of
  by the policy owner, no new TASK29A run is made, and so its table keeps
  `engine=False` (a run of it would not seal `timing_grid.py`). Its counts
  take no ledger, pilot or revision: those belong to tables with fixed
  seconds. The TASK29B allocation schema names (`task29b-*`) are kept by the
  TASK30 gate.

### TASK30 follow-up

A follow-up measures the cells that a grid leaves inconclusive after its second
stage. For the TASK30 grid these are `exclude_partial-1` and
`exclude_tactic_reuse-0`, which get one targeted, decision-grade follow-up
under the `warmup` schedule, with a pilot of those two cells alone. It is the
table `task30_followup.py` (name `task30f`, label `TASK30-FOLLOWUP`), a
complete table of its own on the shared engine, with the following additions to
it.

- **Cells.** `Table(cells=...)` restricts a table to the named cells of its
  cases; `keys()`, the pilot, `predeclare`, `run`, the extension plan and the
  summary then work on that subset and nothing else, and its decision is
  complete for it. The cells of the follow-up are the two above, with the
  seconds of the TASK30 table for their cases (1.0 for `exclude_partial`, 0.3
  for `exclude_tactic_reuse`), 5 samples, the baseline, source list, pins and
  tree of the TASK30 table, its sealed files (and `task30_grid.py`, below),
  the layout seed `task30-followup-1`, and the counts file
  `task30_followup_iterations.json`. `--only` is a diagnostic subset of a
  follow-up as of any table (no decision).
- **Evidence family.** `Table(family=...)` names the directory under
  `.agent-files/evidence/` that holds the ledger, the build stamp and the
  prepare log, and the name in the keep refs (`refs/performance/<family>/
  <sha>`); the follow-up is of the family `task30`, so its attempts go into
  `.agent-files/evidence/task30/attempts.jsonl`, the one hash chain, and
  `replay` lists the attempts of each table. Schemas keep the table's own
  name (`task30f-iterations-v1`, ...).
  - *Lines name their table.* A new line of the ledger carries `table` (the
    table's name). A line without it, as every line written before the field
    existed, is the table that names the family (TASK30). A line is hashed as
    its text, so the lines already written verify byte for byte and nothing
    is rewritten. The attempt report (`ATTEMPTS of TASK30: N ...`), the
    counts of `close` ("attempts N in the ledger, M of the candidate") and the
    search for the opening of a grid read only their own table's lines, so N
    of TASK30 is not raised by a follow-up attempt, and the report of the
    follow-up lists its own. The line ends "(R records of TABLE, F records
    in the family ledger, chain intact)": R the records of that table, F
    those of the whole chain.
  - *Stamp and log per table.* The family shares the directory, so the table
    that names the family keeps `build-stamp.json` and `prepare.log` (the
    TASK30 records replay as before), and any other table of it keeps
    `build-stamp-NAME.json` and `prepare-NAME.log` (`build-stamp-task30f.json`,
    `prepare-task30f.log`). `prepare` of the follow-up neither deletes nor
    overwrites TASK30's stamp or log, and TASK30's does not touch the
    follow-up's. Both stamps describe the one checkout, so a `prepare` of
    either changes its products and each measuring command compares with its
    own stamp: a TASK30 resumption after the follow-up's `prepare` is still
    refused by TASK30's own comparison with its stamp (the tree
    outside the performance area differs from Y's, `run_paired.py` among
    it); the follow-up's tree rule (below) is another thing.
- **What it replaces.** `Table(replaces=Replaces(ENGINE))` makes the table a
  follow-up of the grid that the engine `ENGINE` (the table that measured it
  with the hooks its module gave it) measured: the cells it takes over are
  those whose class (`classify_row`) is `inconclusive` in that grid's final
  decision. `GRID` is the grid's *last* stage: its second stage where it has
  one, and a first stage only when it has no remeasurement plan; a first stage
  whose second stage is still to come is refused (`the replaced grid is not
  final`), for the follow-up replaces the final stage. A Replaces helper
  called before the grid is bound is a refusal naming that, not an
  `AttributeError`. There are two bindings.
  - *Full* (`predeclare`, and the follow-up's own `replay`, always; both need
    `--replaces-pilot DIR`; `verify-counts`, `run` and `extend` too, when the
    code changed since `predeclare`, see below): the grid is replayed in
    full, with the engine of the table that measured it (stage 2 replays
    stage 1), and the pilot of its counts, and these are refused: a grid that
    does not replay; follow-up cells other than the open cells (`follow-up
    cells differ from the open cells`); a baseline or second-stage limits other
    than the grid's, or pairs that are not twice its first stage's.
    `predeclare` records in the counts file a `replaces` block: the path of the
    grid relative to the follow-up's pilot, the SHA-256 seals of every file of
    the replaced grid that the binding reads (the inventory and decisions of
    both stages), and the open cells; and the pairs of each cell
    (`pairs_by_cell`, below).
  - *By seals* (`verify-counts`, `run`, `extend`, while the code of the
    replay is that of `predeclare`): no full replay. Every file
    of the replaced grid that the binding reads is checked against the seals
    of the counts (`replaced grid changed since predeclare: FILE`), the open
    cells are taken from the sealed decision rows by `classify_row` and must
    be the table's and those the counts record, and the pairs are derived
    again by replaying (archive seals and analyses) only the follow-up cells'
    first-stage archives, their develop/develop control; a mismatch with the
    counts is a refusal. This costs two cells instead of the 144 of each of
    two stages. `predeclare` also records, in `replaces.code`,
    the SHA-256 seals of the code it replayed with beyond what the table
    seals itself (`timing_grid.REPLAY_CODE`: `timing_grid.py`,
    `acceptance.py`, `summarize.py`, `audit_evidence.py`,
    `runtime_metrics.py`, `allocator-counter/private_runtime.py` (its
    checkout identity), and the pin file and counts file of the replaced
    table, `task30_pins.py` and `task30_iterations.json`). That block is a
    record of what `predeclare` replayed with: it is never derived again
    from the current code, but it is not trusted either. `verify-counts`,
    `run`, `extend` and `replay` (and `dispose`, through them) require it to
    be well formed and to equal the seals of the same files as they are in
    the git commit that holds the counts file (the commit that introduced
    it, in the history of the candidate; of `HEAD` for `verify-counts`),
    read with git, and that commit must change the counts file alone; a
    counts file not committed yet (the first `verify-counts` after
    `predeclare`), or one outside the repository (`verify-counts` only), is
    compared with the files as they are in the working tree. Otherwise
    they refuse: `the record of the code differs from the commit of the
    counts: FILES; predeclare again at the pilot's code, or commit the code
    change after the counts` (for uncommitted counts: `differs from the
    files as they are in the working tree: FILES; predeclare again at the
    pilot's code`). So the record is bound to the
    commit discipline: the counts are committed with the code `predeclare` ran
    with, and alone. The same commands also require every file of the
    record to be, in the follow-up pilot's recorded checkout head (the
    pilot inventory's `checkout.head`), what the record says, for counts
    not yet committed too (the files at that head are compared); the
    pilot's inventory is first required to be the one the counts seal
    (`--pilot` of another pilot is refused as such, and a pilot head
    the repository lacks as `the pilot head H is not in this
    repository: the pilot must be made at a commit in the candidate's
    history`). Otherwise they refuse `the code changed between the
    follow-up pilot (HEAD) and the counts commit: FILES; pilot again, or
    predeclare at the pilot head's code and commit the code change after
    the counts` (for uncommitted counts: `and the counts`; a file absent at
    the pilot head is marked `(absent)` in FILES). The recorded head is
    itself checked against the pilot, by `check_pilot_cell` (every
    `fixed_seconds` pilot, TASK30's own included; TASK29A's is not): the
    manifest of every control archived in the pilot must carry a `head`
    equal to the inventory's `checkout.head`, and an inventory with no
    checkout head is refused. `predeclare` runs it, and so do
    `verify-counts`, `run`, `extend` and `replay` where they derive the
    counts again (through `check_provenance`), so a head edited in the
    inventory alone, or a manifest without one, is refused. What this does not
    prevent is a forgery that rewrites the pilot (inventory, archived control
    manifests and archive seals) and derives the counts again: the
    guarantee is consistency of the pilot's evidence with the record,
    not authentication of it. The seal binding is valid only while the
    current seals of those files equal it. When they differ, `verify-counts`,
    `run` and `extend` do not refuse: they print one line (`code changed
    since predeclare (FILES): the replaced grid is replayed in full`) and
    bind the grid by the full replay, as `predeclare` and `replay` do,
    which reads the replaced grid's pilot (`--replaces-pilot`; without it
    they refuse, naming the changed files). So a later change to shared
    code costs the full replay, and never makes a finished
    follow-up unreplayable (a later change to `summarize.py`,
    `audit_evidence.py`, `runtime_metrics.py` or
    `allocator-counter/private_runtime.py` needs no history entry, as no
    record carries their seals; one to `timing_grid.py` needs the old
    seal appended to `ENGINES`, one to `acceptance.py` to `ACCEPTANCE`, and one
    to `task30_pins.py` to `PIN_HISTORY`, because every record of the follow-up
    carries those seals and `replay` refuses "changed engine", "changed
    acceptance" or the pins without them; `task30_iterations.json` is never
    changed). While the code is unchanged the sealed commands run
    the cheap header, sources, commit and checkout checks of the full
    replay on both inventories of the replaced grid, through the hooks of
    the replaced engine. What they leave to the full replay (`replay`, and
    the disposition step) is: the provenance of the TASK30 pilot
    (`task30_iterations.json` re-derived from `E/pilot`; its replay also
    requires each control manifest's `head` to equal the pilot
    inventory's `checkout.head`), the re-derivation
    of the extension plan, and the deterministic re-analysis of the
    archives of the other cells of both stages; a refusal there after the
    attempt is recorded would spend it. (`run` and `extend` do make the
    ledger checks of the replaced attempts, `refuse_found` included, below.)
    The code list is a hand list, kept complete by a test that computes the
    static import closure of the replay path, over this directory and
    `allocator-counter/`; the few import edges that are made by code the
    replay does not run are named in the test, each by importer, module and
    function, so that any other new import of a module the list lacks fails
    it.
  Both refuse before an attempt opens, besides: a layout seed that the grid
  drew or its second stage drew (a table refuses the same at its
  construction, for the seed of the table it replaces); candidate sources
  that differ from the grid's source record (`candidate sources differ from
  the replaced grid's`); a candidate that differs from the replaced one
  below the table's tree anywhere but the performance area and the sealed
  files; counts bound to other sealed files; counts of another schedule than
  the table's; counts whose pairs differ from the derivation below; and
  (`run`, `extend`) a ledger that lacks the opening of any attempt of the
  replaced grid, or no ledger at all (below). The
  replaced grid's table, schedule and counts may differ from the follow-up's:
  its own are replayed as they were made (the TASK30 grid is `ramp`; the
  follow-up is `warmup`). `predeclare` and `verify-counts` take `--ledger
  FILE`, like `replay` and `close` (read-only, the ledger of the checkout the
  replaced grid was made in; only the full binding reads it).
  - *One ledger, one checkout.* A follow-up extends the one chain of the
    family and never starts a chain of its own. Before an attempt opens
    (`run`, `extend`, and so `--resume`), the ledger it will be appended to
    (`<--repo>/.agent-files/evidence/task30/attempts.jsonl`) must exist and
    hold the openings of every attempt of the replaced grid (both stages
    through the replaced engine's `check_attempt`, as the full replay does,
    and `refuse_found` on those attempts), recorded from this checkout (a
    copy of the ledger in another checkout is refused); the follow-up table
    must name the family and the ledger of the table it replaces, so that
    this is the file `run` and `extend` append to; otherwise the command
    refuses, naming the ledger path and the missing attempt, before anything
    is measured. So `pilot`, `run` and `extend` of the follow-up are made in
    the checkout that holds the TASK30 ledger (the one the TASK30 grid was
    measured in), and so is `replay`, which reads that one ledger for both
    grids (`--ledger` names it read-only for `predeclare`, `verify-counts`,
    `replay` and `close` elsewhere).
  - *The evidence layout.* The counts record the replaced grid by its path
    relative to the follow-up's pilot (`../stage2`), compared exactly, so
    the follow-up pilot and the replaced grid must stay siblings in the
    evidence layout (`E/followup-pilot`, `E/stage2`, as `stage2/../grid`
    already must be); a copy where they are not is refused ("the counts
    record the replaced grid at ... must stay siblings"), never accepted.
  - *The inventory's record.* An inventory of the follow-up records the
    grid under `replaces` with the replaced grid's fields named as its own
    (`replaced_inventory`, `replaced_decisions`, `replaced_seed`,
    `replaced_counts`: the seals of its inventory and decisions, the layout
    seed and counts seal of its first stage) and the follow-up's beside them
    (`followup_seed`, `followup_counts`), with the grid's path relative to the
    output. `replay` finds the grid there again.
  - *The tree rule.* The candidate may differ from the replaced candidate
    below `src` in any file under `src/simp/tests/performance/` and in any
    sealed file or driver wherever it lies (`run_paired.py` is one). That is
    wider than "only the files the table seals and its driver", on purpose:
    the harness changes between the two commits (tests, documents,
    `MatrixAllocation`, the allocation modules, the engine), and the code that
    measures is covered by the engine, driver, acceptance and sealed seals
    and by the sources record, not by this rule. Any other change under `src`
    refuses the follow-up: a document or test under `src/simp/tests/
    compatibility/`, another task's commit merged between the replaced
    candidate Y and Z. The names of the sealed files are the code's
    repository's (`Table.root`), the same whatever checkout `--repo` names,
    and a sealed file outside that repository is refused.
- **Seal histories.** `task30_followup.py` has `DRIVERS`, `ENGINES` and
  `ACCEPTANCE` and `SEALED_HISTORY`, each with the seals of
  `40e176538f` (see "Seals and seal histories"), passed to
  its table as TASK30's are to its own: `check_code` accepts a record whose
  driver, engine or acceptance seal is the current one or one listed, and a
  sealed file's seal is the current one or one of its history. They are read
  by `replay` only; `run` compares the counts' `sealed` with the current
  seals exactly. So:
  - A change to any sealed file, `task30_grid.py` included, between the
    follow-up's pilot and its `run` is not absorbed by a `SEALED_HISTORY`
    entry: `run` refuses ("the counts are bound to other sealed files") and
    only a fresh pilot (a new counts file) helps. Land the disposition code
    before the pilot, or outside the sealed files: it lives in a module
    of its own, `task30_dispose.py`, in neither table's seals, so that
    `task30_grid.py` stays byte-identical from Z0 on.
  - After follow-up records exist (from its pilot on), a change that must
    not invalidate them appends, in the same commit, the seal the records
    were made by: that of the old `timing_grid.py` to `ENGINES`, of
    `acceptance.py` to `ACCEPTANCE`, of `task30_followup.py` to `DRIVERS`,
    and (a reviewed change that alters nothing measured, only after `run`)
    of `task30_grid.py` to `SEALED_HISTORY["task30_grid.py"]`. The test that
    pins them (`test_task30_grid.py`) is edited with them.
  - `task30_grid.py` is a *sealed file* of the follow-up, not a driver: the
    follow-up imports its constants (`SECONDS`, `PAIRS`, `SAMPLES`, `SEALED`)
    and replays the TASK30 grid through its table, which are inputs of the
    counts, as `task30_cases.py` is. TASK30 treats the same file as its own
    driver, with `DRIVERS`; a change to it needs no TASK30 entry unless a
    new TASK30 record is made.
  - `task30_dispose.py` has `HISTORY` (per file of its `CODE`, the seals
    the disposition was recorded with) and the cascade is longer than the
    others. Worked example: one later edit of `timing_grid.py`, after the
    follow-up's records and the disposition exist, appends in its commit
    (1) the old `timing_grid.py` seal to `task30_followup.ENGINES`; that
    edits `task30_followup.py`, so (2) its old seal goes to
    `task30_followup.DRIVERS`; and (3) both old seals go to
    `task30_dispose.HISTORY` (`"timing_grid.py"` and
    `"task30_followup.py"`); that edits `task30_dispose.py`, which (4) needs
    its own old seal in `HISTORY["task30_dispose.py"]` (the entry is the
    recorded seal, so appending it does not chase the file it edits). An
    edit of `acceptance.py` is the same with `ACCEPTANCE`. The recorded
    seals are in `disposition.json` (`code`), and the check of
    `task30_dispose.py` names every changed file in one refusal with the
    entry to paste into each constant (the literal element of that
    constant, each in backticks: `"timing_grid.py": (SEAL,),` for `HISTORY`,
    `"task30_grid.py": (SEAL,),` for `SEALED_HISTORY` (the same form: a dict
    keyed by file), `SEAL,` for `ENGINES`, `ACCEPTANCE` and `DRIVERS`) and
    the tests that pin those
    constants (`test_task30_dispose.py` for `HISTORY`,
    `test_task30_grid.py` for the follow-up's), which the same commit edits;
    nothing is looked up by hand.
  - A file added to `task30_dispose.CODE` (`void_attempts.py`, the attempt
    rule moved out of `task30_dispose.py`) is absent from the records made
    before it existed. `task30_dispose.ADDED` names, per such file, the file
    that held its code, that file's seals in those records, and the held
    seal; a record may lack the file only when its seal of the host is one
    of the listed, and is then treated as recording the held seal for the
    file. The held seal names the version of the added file reviewed as
    holding exactly the code the older records ran: its moved functions are
    AST-equal to the host's, apart from message strings: docstrings,
    `"..." % (...)` messages that are not the value of an assignment,
    returned string constants, the message argument of `a.require`, and two
    reviewed strings that are not messages (the `prefix=` of
    `tempfile.TemporaryDirectory` and the `what` of `want, what = ...`). A
    test pins the hash of the functions with exactly those blanked; every
    other string (event names, statuses, keys, option and file names) is in
    the hash, so a changed literal of the logic changes it, and so does a
    changed operand of a `%` assigned to a name. A second pinned hash
    covers the rest of the added file (imports, constants, other functions
    and module statements, without the module docstring), normalised by the
    same rules. An edit of the added file is non-behavioural when both
    hashes are unchanged; it then replaces the held seal, after that
    review. A behavioural edit
    is not allowed while a record depends on the held seal: a seal in
    `HISTORY[file]` accepts every later file, so it would bind the record to
    logic it never ran. Where a record lacks the file, `check_code`'s
    refusal of an edit states this rule and names no `HISTORY` entry. A
    record made by the current code carries the file.
  - TASK30's *set* of sealed names is frozen by its Y records: adding a file
    to `task30_grid.INSTALLED` or `SEALED` (which also feeds the
    follow-up's `SEALED`) makes every Y replay refuse "changed sealed
    files".
- **Pairs.** A follow-up has no pairs of its own to declare: the pairs of a
  cell are what the second-stage rule gives for the develop/develop control of
  the replaced grid's *first* stage,
  `min(120, max(2*P, 10*ceil(P*(w/0.015)^2/10)))`, with `P` the pairs of that
  stage (20) and `w` the larger half log-width of the CPU and wall control
  intervals (`Grid.followup_pairs`, from the functions
  `control_half_width` and `second_stage_pairs` that the second stage uses
  too). The floor `2*P`, 40, is the table's `pairs`. `predeclare` records the
  pairs in the counts file as `pairs_by_cell`; `verify-counts`, `run`,
  `extend` and `replay` derive them and the `replaces` block again (from the
  replaced grid, by the seals or in full as above) and refuse a file that
  differs. A run measures each cell with its own pairs, a row records them
  when they are not the table's, and a replay refuses a row whose pairs
  differ from the counts'. The second stage of the follow-up (`extend`, seed
  `SEED-ext`) takes each cell's own pairs as the base of its rule.
- **Decisions.** The follow-up's `decisions.json` is that of its own cells
  (class report `TASK30-FOLLOWUP grid: ...`). A follow-up outcome other than
  pass blocks: a fail is final, and an inconclusive or control-limited cell
  after the follow-up's own second stage blocks too. No further timing retry
  and no automatic attribution follows without a new policy decision. An
  attempt that admitted no measurement (every cell a protocol failure, no
  `protocol` run in its inventory) is void: it is no outcome, took no sample
  and selects nothing, and it is rerun with the same settings as a new attempt
  (a rerun is a new draw; `--resume` cannot redo recorded protocol cells). Both
  stay in the ledger, and `task30_dispose.py` checks and records them
  (`followup_attempts`). The judged attempts are the `attempt` ids in the
  inventory of `--followup` and, where that is a second stage, of its first
  stage, each from the output of that stage (an attempt id is of one output:
  every output its open, resume and close lines name is collected, and more
  than one is refused). Every other attempt of the follow-up's table must be
  shown void from its own output: the directory exists, its `inventory.json` is
  of that attempt id, it has a row for every cell it measures (the follow-up's,
  or for a second stage its own plan's), every row has `protocol` present and
  false, every row's archive exists and is the sealed one (`seal`),
  acceptance's own `success` in it is false, each command acceptance recorded
  did not time out and left a runner manifest in the folder of its `--output`
  (one runner manifest per runner command), and no runner `manifest.json` in an
  archive records an admitted run (`runs` empty and `success` false); and the
  ledger closes the attempt `inconclusive` with exactly one close line and no
  resume line (a resumed attempt may have drawn samples in a cell it cleared),
  which is the status of a grid whose every cell is a protocol failure (no cell
  passes or fails). A second stage closes with the combined status of both
  stages, so a void second stage is accepted only when its first stage has no
  fail; a fail in the first stage is final and the follow-up blocks anyway.
  Anything else is refused (exit 3), naming the attempt, its status, its output
  and the failed condition: an interrupted or resumed attempt, one closed more
  than once, one with missing cells or with no close line, and a runner killed
  while measuring (no manifest) are refused too, as they may have measured.
  This rule is `void_attempts.py`, shared with the TASK31 disposition; both
  seal it in their `CODE`. The follow-up writes no `final.json`: the TASK30
  decision with these two cells in place of the replaced ones is the
  disposition step's (`task30_dispose.py`), which owns `final.json` and builds
  it from the replayed reports of both grids.
- **Sequence.** At the commit Z0 (code and documents; no counts): `prepare`,
  then `task30_followup.py pilot --output OUT/followup-pilot`, `predeclare
  --grid OUT/followup-pilot --output FILE --replaces OUT/stage2
  --replaces-pilot OUT/pilot`, where `FILE` is the table's counts path,
  `src/simp/tests/performance/task30_followup_iterations.json`
  (`task30_followup.py` reads no other), `verify-counts` with `--replaces`; the
  counts file is committed as Z (the candidate), so that Y..Z holds only the
  performance area and sealed files: any other change under `src` refuses the
  follow-up. `verify-counts` again at Z (the counts file as committed, by the
  seals while the code is that of `predeclare`; after a code change it replays
  in full and needs `--replaces-pilot OUT/pilot`). The counts file is committed
  alone: no code change in that commit, and none between `predeclare` and it (a
  replay-code change after `predeclare` is committed after Z, or `predeclare`
  is made again at the pilot head's code, with no replay-code change between
  the pilot and `predeclare`); the pilot is made at a commit of Z's history (a
  pilot head the repository lacks is refused). The engine refuses a commit of
  the counts that touches another file, and a record of the code that differs
  from the pilot's head (pilot again, or predeclare at the pilot head's code),
  at the first `verify-counts` already. Every command that appends is made in
  the checkout that holds the TASK30 ledger (see "One ledger, one checkout").
  `run --candidate Z --pilot OUT/followup-pilot --replaces OUT/stage2 --output
  OUT/followup --authorize-measurements`, `extend --grid OUT/followup --pilot
  OUT/followup-pilot` only if its control left a cell open, `replay` of each
  stage (with `--replaces-pilot OUT/pilot`, which replays the replaced grid in
  full). The checkout, its stamp and its ledger are those of the pilot, as for
  any table, and the measurements run serially under the lock. The follow-up
  pairs with its own allocation grid at Z (`OUT/ALLOC_FOLLOWUP`, a full
  `allocation_matrix.py run --task task30` at Z); neither `close` nor the
  follow-up checks that pairing, the disposition step does (head and tree
  outside the performance area, exactly). The last step is `task30_dispose.py
  --record`, reviewed, and then the same command without `--record` (below).
  `--followup` is the follow-up's final judged stage directory (its second
  stage, where it has one), as `--replaces` is.

## Allocation evidence and disposition

The allocation gate counts exact words with the TASK29B counter; the
disposition combines the gates into a final decision.

### Structural evidence (allocation work phase)

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
  counted is `dproc`: one per retained dproc per sampled term (3 terms for
  n >= 3, fewer below; n-1 dprocs after a deletion of one, so `3(n-1)` at
  n >= 3; none when every dproc is gone). It equals the number of sampled
  terms times the number of dprocs the result holds, which is the length of
  `dpnames` in the digest: the same fact, shown as counted applications of
  each retained dproc. It is the one count that sees a dproc deletion, but
  it is not an independent witness of it.

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

**Outside the work phase.** The timed closures and the `verify` closures do not
contain the work phase, so the operation and apply words of a case do not
depend on it. The setup bracket does: building a workload also sets the hooks
of `MatrixSupport` (the fingerprint, the use, the maker count, and `ruleList :=
rs`, which shares the list the workload builds anyway), so the setup words
include the closures of a few assignments, a small constant that does not grow
with the number of rules and is equal on both sides of a grid. The fixture
dprocs share one closure (`dprocApply`), so the counter adds no words per
dproc. The setup words of grids made with different setup fixtures differ, so a
comparison across such grids uses only the operation rows
(`operation_first`, `operation_steady`, `apply`), never the setup row.

**Gating by header.** A grid whose header says `structure: "v1"` (every new
run) requires the four records in every process, and a header without the key
forbids them, so every archive made without them parses and replays to the
same decisions and results byte for byte.
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
`nondeterminism` list do not depend on the work rows.

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
and deterministic). The conditions apply to the 13 attributed cells only (all
at n = 10000, and `exclude_literal_namespace` at n = 1): they fail by
construction elsewhere, so they are never applied to every cell of a grid. At
n = 0 a deletion case has no rules, so no lookup and no `trace.4.REDUCE`; at
n = 1 the two dproc cases have no dproc left and no `work.use.dproc`.

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

**What the counts cover.** `-*` filters the net (untraced, with
`Ho_Net.vfilter`) and the dprocs, rebuilds nothing and runs no
simplification, so the operation itself emits no trace event and no
inference. `remove_ssfrags` and `exclude_ssfrags` do not only filter: they
rebuild the simpset from the filtered history (`build_from_history`, as on
develop and by the same source), and that rebuild is visible in the counts
only where the remaining fragments carry rules or counted callbacks. In
`history_excluded` the rebuild re-adds only the empty `matrix_drop`
fragment. The workloads of the six `-*` deletion cells install no counted
maker or collector, so the empty `work.first` and `work.second` of those cells
are guaranteed by construction and are not observations: zero maker and
collector counts are no evidence that nothing was replayed. The two dproc
cells do install them (`setup (SOME maker) ds`, checked by `callbacks 0 0`):
in `exclude_dproc` no data follows, so a rebuild of the history would call
every collector and no maker, and in `exclude_mixed` data follows, so it
would call the maker and every collector; no rebuild applies a dproc. For
such a cell the rows show:

- nothing of the operation by itself in the six deletion cells (their rows
  are empty by construction, on both sides); in the dproc cells the zero
  maker and collector counts do show that no rebuild ran;
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
  allocation words and by source identity. What discriminates in the other
  deletion cells is the use rows, the result digest and the exact
  allocation words;
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
  words;
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
candidate except the reviewed pins that the records carry: `Cond_rewr` and
`SimpTracking`, a move of `note_rewrite` and `with_tracking`, as in
`task30_pins.PIN_HISTORY`) and on the exact operation words; the
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
derived from the manifest alone. `--compare MANIFEST --summary PATH`
derives it again and compares it with the stored summary at PATH (exit 1 and
a `DIFFERS summary` line on a difference); `--write-summary PATH` writes it.
The retained smoke evidence is such a manifest and summary.

### Structural evidence and the TASK30 disposition

Policy decision: the 13 cells the TASK30 grid left
control-limited are settled by deterministic structural evidence against
develop, each recorded as *attributed* with a note, and re-derived from the
replayed records every time. Every other class is as the engine has it: a
pass, a fail (final), and a blocking cell. The code is `timing_grid.dispose`
(the generic engine function) and `task30_dispose.py` (`DISPOSITION`, the
evidence and the command).

**Classes** (`timing_grid.dispose(final, attributed, evidence)`, by
`classify_row`):

- pass; fail (stays a fail; the status is fail when any cell fails);
- protocol and inconclusive: blocking;
- control-limited: attributed only if listed **and** `evidence(cell)` holds,
  else blocking, naming the evidence that failed. There is no non-blocking
  class (TASK29A's "unresolvable") for TASK30;
- the retained slope, where measured, is one more entry, as in `classify`.

The control-limited cells of the TASK30 grid, the follow-up's cells aside,
must be exactly the list: otherwise the command refuses ("stale
attribution", naming the listed cells that are not control-limited, with the
class they are in, and the control-limited cells that are not listed). The
evidence is not asked for a stale list. The follow-up's own cells are judged
by the follow-up's outcome (`judged`): a pass or a fail as it is, and a cell
that is control-limited, inconclusive or without a measurement after the
follow-up's own second stage blocks ("follow-up: <class>"); it is never a
stale attribution. The follow-up's status is printed and recorded
(`replaced.followup_status`).

**The list** is `task30_dispose.DISPOSITION["attributed"]`, with the
evidence class and the note of each: `exclude_missing`, `_matching`,
`_batch`, `_qualified`, `_literal_exact`, `_mixed`, `_dproc`, `_marker`,
`_marker_reuse`, `_tactic_reuse`, `_tactic_complete` at 10000,
`history_excluded-10000` and `exclude_literal_namespace-1`. The classes are
fixed per case (see "Per-cell evidence" above): `deletion` (missing,
matching, batch, qualified, literal_exact, literal_namespace,
history_excluded), `dproc-deletion` (dproc, mixed) and `operation` (marker,
marker_reuse, tactic_reuse, tactic_complete). The note of each cell is
qualitative: its class, what its rows show and do not show, and what no row
can show (below). It carries no number (a test pins that, apart from the
name TASK_31; the residual sentence, added by the command, names
the policy's 3% margin): every number of a cell (the work
counts of the first and second run and of the use, the dproc count, the
candidate's and the control's intervals, the GC interval, the digest's
SHA-256, the number of allocation rows) comes from `disposition.json`, which
the command derives from the rows and prints per attributed cell. The
notes of `DISPOSITION` carry no residual text. The command adds the residual
sentence to a cell's note exactly when the cell's recorded candidate CPU or
wall CI upper bound exceeds 1 + the policy's margin
(`acceptance.EQUIVALENCE_POLICY`), and `disposition.json` records whether it
applies (`residual`). The sentence says that the candidate CI upper bound
exceeds the 3% margin; structural equality shows identical work, not
identical timing; the candidate's startup heap is larger, GC reported and not
gated, the attribution in TASK_31.

**Evidence** (`task30_dispose.Evidence.holds(cell)`: four items, `EVIDENCE`;
the first failure is named with the row, the file or the cell that
differs):

1. *sources*: no file of `task30_cases.SOURCES` differs between the
   candidate and develop except the pinned ones (`source_identity` of the
   final decision: `differing` must be empty; the reviewed files are
   recorded in the disposition under `pinned`);
2. *allocation*: every allocation row of the cell passes in `alloc-z/`, and
   its operation rows (`operation_first`, `operation_steady`, `apply`; the
   baseline and candidate words of every metric) equal those of `alloc/`.
   The setup rows are not compared across grids (the fixture's setup
   changed between Y and Z);
3. *work*: the cell's work status in `alloc-z/` is `equal` (candidate =
   baseline = control in every row, deterministic across the pairs), not
   missing, unresolved or non-reproducible, and the per-class non-vacuity
   check holds, applied to the 13 attributed (case, size) cells only: for
   `deletion`, `work.first` and `work.second` empty and `work.use.trace.4.
   REDUCE` present; for `dproc-deletion`, the same and `work.use.dproc`
   present; for `operation`, `work.first` and `work.second` non-empty and
   `work.use` empty;
4. *result*: `result.digest` present and equal, one value on each side.

A work row of a cell that does not reproduce (several values) blocks the
cell with the row and side named, whatever status the row gets (the
nondeterminism list is read first, grouped by row ("work row K is not
reproducible (candidate, baseline)"), then each row that is not equal ("differs
from develop" or "is inconclusive"), with the distinct candidate, baseline and
control values, and the cell's status last); it is
never an exception, and the counts and the digest recorded for the cell keep
every value. A record that lacks a phase
or a metric the comparison needs is named too.

**The allocation grids are gated too.** The disposition is a pass only if both
`alloc/` (the `--allocation` grid, made at Y) and `alloc-z/` (the
`--followup-allocation` grid, made at Z) pass: each is replayed and its status
(the status code of `allocation_matrix.replay`) is read. An allocation `fail`
makes the disposition `fail` (exit 1); any other status but pass (inconclusive,
too few pairs, a baseline other than the pinned one, non-reproducible rows)
makes it `blocked` (exit 2). The grid and the reason are printed
(`ALLOCATION-FAIL`, `ALLOCATION-BLOCKED`), recorded under `allocation` in
`disposition.json`, and the outcomes are in the final line. An incomplete
allocation grid has only `decisions-partial.json` and is refused before any
replay ("is not a complete grid"). A grid with a `decisions-partial.json`
beside a complete `decisions.json` is refused too: the partial file is stale
(an earlier `--only` run left it; a complete write by `allocation_matrix.py`
removes it) and may be removed by hand; the disposition never deletes it.

What no row can show is the list under "What no row can show" above (CPU
that neither allocates nor traces, net node visits and hidden candidates,
live heap and retention, work outside `Trace` and the kernel counter, the
timed process's context, the layout effects of other files); every note
says so, and equal rows show equal work and result, not equal time.

**Command.**

    python3 -B task30_dispose.py --grid E/stage2 --pilot E/pilot \
        --allocation E/alloc --followup E/followup-FINAL \
        --followup-pilot E/followup-pilot \
        --followup-allocation E/alloc-z [--ledger FILE] [--record]

It first makes the cheap refusals, before any replay: the pairing of each
timing grid with the allocation grid of its own harness
(`task30_grid.harness_match`; TASK30 at Y with `alloc/`, the follow-up at Z
with `alloc-z/`, each also of one candidate, one baseline and the task
`task30`), `--grid` the grid the follow-up records as replaced, the two
allocation grids different, every attempt of the follow-up's table in the
ledger (judged, by the attempt ids of `--followup` and its first stage, or
void as defined in the follow-up's Decisions above; a second stage named by
nothing, or a first stage named while a second exists, is refused here
(the second, measured, is not void) or, when the second is void, by the
replay as a second stage still to come; each refusal says to name the final
stage), and in check mode the recorded files and the code seals (below). It
then replays the follow-up in full (which replays the TASK30 grid in full with
`--pilot`, by its own table, and requires that the follow-up replaced exactly
the cells that grid left inconclusive and that its candidate sources equal
that grid's), and the two allocation grids (`allocation_matrix.replay`). It
prints the replays' reports (every attempt of both tables), the class report
of the final decision (`TASK30 final grid: ...`), the follow-up's status,
one `FOLLOW-UP-ATTEMPT ID status S output O: judged|void (no measurement
admitted)` line per attempt of the follow-up's table, each allocation gate,
per attributed cell (`ATTRIBUTED` or `BLOCKING`, its class and what failed)
its numbers from `disposition.json`, and
`TASK30 disposition: pass|fail|blocked {counts, "allocation": {"alloc":
OUTCOME, "alloc-z": OUTCOME}}`. The status is 0 for pass, 1
for fail, 2 for blocked and 3 for a refusal (one `REFUSED` line on the
standard error); neither this command nor `close` appends to the ledger.

**`final.json`** is the TASK30 decision with the follow-up's cells in place
of the cells they replaced: the summary over the reports of stage 1, stage 2
and the follow-up (a follow-up row replaces its cell, whichever stage of the
follow-up it comes from), with the source identity of the TASK30 grid, the
`remeasured` block of its second stage kept, and a `replaced` block: the
replaced cells, both layout seeds (and the follow-up's own second-stage seed,
`followup_second_seed`, when it has a second stage), both counts seals, both
candidates and the follow-up's status. Its `status` is the measured one
(nothing is excused: it is `inconclusive` while the control-limited cells
are open); the disposition
is in `disposition.json`. `dispose` owns it: the follow-up writes none, and
it is written in the follow-up's output directory (`--followup`), beside
`disposition.json`, because that is where the follow-up's evidence is.

**`disposition.json`**: `followup_attempts` (every attempt of the
follow-up's table in the ledger, as {attempt, status, output, judged, void}),
the schema, the decision date, the evidence names,
the status, the counts and the class lists, the blocking cells with their
reasons, the reviewed (pinned) source files, the `replaced` block, and per
listed cell: the evidence class, the note (the only free text), the decision
and what failed, the candidate's decision, median and 95% interval for CPU,
wall and GC, the control's interval beside, its `control_decision` (the
candidate rule applied to the control, not its validity) and `control_valid`
(for CPU and wall, the gated metrics: whether the control's interval lies
within the window `[1/(1+margin), 1+margin]`, as acceptance computed it,
and a refusal when an archive lacks it; null for GC, which has no window),
the work counts
(`first`, `second`, `use`, the count rows of the candidate that are not zero
throughout, each with all its distinct values), the result digest (likewise
a list of the distinct values) and the number of allocation rows of the
cell; the status of each allocation grid and its reasons (`allocation`);
and `code`, the seals of the code that derived it
(`task30_dispose.CODE`).

**`--record`** writes `final.json` and `disposition.json` and refuses to
replace either if it exists (remove it to record again; this too is checked
before any replay). Without it the
command derives both again and refuses any difference from the files
(`changed TASK30 disposition: FILE`), and refuses to run without them. The
recorded `code` is held to the append rule of the other records: each seal
must be that of the file now or one `task30_dispose.HISTORY` lists for it, so
a change to any of those files after the disposition was recorded appends
the old seal to `HISTORY` in the same commit (the check names the file and
prints the entry).
`task30_dispose.py` is on neither table's seals and nothing on the replay
path imports it, so a fix to it after the follow-up's records exist asks
nothing of `task30_grid.py` or `task30_followup.py` (a test keeps it out of
the import closure of the replay, and every module it imports beyond that
sealed by `CODE` or named as the allocation matrix's toolchain building).

### TASK31 allocation gate (gate 2)

`allocation_matrix.py run --task task31` counts the allocation of the
ClientPerformance cells of TASK31 with the TASK29B counter, under the
TASK29B/TASK30 decision rule unchanged: exact equality of every field of the
steady, first-operation and structural records, GC reported and not gated, the
baseline/baseline control identical, the candidate equal to the baseline
(`pass`), different (`fail`) or not decidable (`inconclusive`).

**One mechanism, the fixture chosen by the case.** The `fixture` a case has in
`matrix.json` selects a family (`allocation_matrix.FAMILIES`): the
`MatrixPerformance.sml` cases keep `MatrixAllocation.sml`; the
`ClientPerformance.sml` cases use `ClientAllocation.sml`. A task whose cases
span two families is refused. Both are installed in the private directory as
`Performance.sml` with `MatrixSupport.sml`, so the protocol checks, the
brackets and the work phase are the same.

**ClientAllocation.sml** has the workloads of `ClientPerformance.sml` verbatim
(`conversion`, `traversal`, `tacticWork`, `dependencyWork`, `choose`, without
the downstream cases) inside the driver of `MatrixAllocation.sml` word for
word; `test_allocation_client.py` pins both. The only additions are the lines
that end in a comment saying `alloc`: each workload keeps its result and
fingerprints it (`MatrixSupport.thmText`, with the residual goals for tactics),
and the use phase re-applies the conversion or tactic. The structural work row
(`work.first`, `work.second`, `work.use`, `result.digest`) is therefore the
same kind of evidence as for the matrix cells, and is `equal`, `differs` or
`inconclusive` beside the words, never in place of them.

**No shared closure.** A process of either family loads the selected
simplifier sources, the installed fixtures and the shared heap, so no closure
of shared modules is recompiled in the private directories. A module that the
fixture would load outside those is refused as a shared input.

**Cells.** The `traversal_*` and `tactic_*` cells of the table: every size up
to 1000 (the depth cases 0, 1, 10 and 100, the singletons 0), and 10000 only
for the supplied, installed and asm families. The 33 heavy tactic cells at
10000 are `task31_cases.INFEASIBLE`: not run, listed as such, never a pass.
The same cases, in the order of the matrix ledger, are those of the identity
and timing gates (`task31_cases.py`); the matrix takes the infeasible cells
as `(case, size)` pairs (`INFEASIBLE_CELLS`).

**Iterations** are predeclared in `allocation_iterations_task31.json`, written
by `task31_iterations.py`: the TASK30 rule (32 steady iterations to size 100,
16 at 1000 and 8 at 10000), with the reuse and complete stages of the
families in `CUT_8` halved to 8 and those of `CUT_4` to 4 at 1000
assumptions, to fit the process timeout. The file is bound by digest like the
others.

**decisions.json** has, for the TASK31 disposition, the top-level fields of
TASK29B (`status`, `complete`, `acceptance_pairs`, `acceptance_baseline`)
and

    {"candidate": REV, "baseline": REV, "infeasible": [NAME, ...],
     "rows": [{"case": CASE, "size": N, "pairs": P,
               "decision": "pass" | "fail" | "inconclusive",
               "work": "equal" | "differs" | "inconclusive" | null}, ...]}

`candidate` and `baseline` are those of the grid's inventory. A row is `pass`
only when every gated phase and metric of its cell passes, the cell has at
least 10 pairs, the baseline is the pinned develop commit and no row of the
cell is nondeterministic; `fail` when one fails; `inconclusive` otherwise,
so a smoke or a grid against another baseline has no passable row, and its
`complete` is false (it is written to `decisions-partial.json`). `rows` lists
the cells that were measured or tried, in the order of the cases and sizes;
`infeasible` is the sorted names of the cells not run. TASK29B and TASK30
results have none of these keys.

**Sealed code.** `allocation_matrix.py` is in the TASK30 seal
(`task30_dispose.CODE`): changing it adds the previous seal to
`task30_dispose.HISTORY`, pinned by `test_task30_dispose.py`.

## Independent builds and fresh loading

Admission of externally produced builds and the runnable fresh-import gate.

### Independent-build admission: fail closed

`verify-builds` audits a separately produced clean-build receipt against
**live** roots and logs. It does not build, run proof workloads, or approve
performance:

```sh
python3 -B src/simp/tests/performance/acceptance.py verify-builds BUILD_JSON \
  --baseline BASELINE_FULL_40_HEX_COMMIT \
  --candidate CANDIDATE_FULL_40_HEX_COMMIT
```

`run --mode independent --build-manifest BUILD_JSON ...` performs that same
admission and then explicitly reports the independent measurement prerequisite
blocked. It **never runs `run_paired.py` and labels that independent**. Fresh
independent launchers, loaded-path inventories and consumed proof/storage pairs
must be supplied separately.

The external receipt producer must run serially under the same locks, in two
new disjoint clean worktrees at the requested pins. Refuse an existing product,
heap, theory cache, ignored or untracked file before configuration; never
simply stamp an old product with a new mtime. Build logs and receipts live
outside both roots. Preserve them until live verification completes. Required
commands in each selected root, using the exact same Poly/ML executable:

```sh
/absolute/path/to/poly < tools/smart-configure.sml
/absolute/selected/root/bin/build -t -F
```

Bare `bin/build` or an inherited partial sequence is insufficient. Record `git
status --porcelain=v1 --untracked-files=all` and the same with
`--ignored=matching` **before** configuration; both must be empty. Record every
command's start/end nanoseconds, cwd, argv, stdin hash, executable hash, log
path/hash, actual exit and timeout status. Hash tools and products while
unchanged; roots must still be at the exact pins with no tracked/untracked
changes during admission (ignored generated products are allowed after
building).

#### Independent manifest v1

Required top-level fields:

- `schema`: `task28-independent-build-v1`;
- `mode`: `independent`; `success`: true;
- `runtime_options`: `["--gcthreads=1"]`;
- `toolchain`: map including `poly` with absolute `path`, nonempty `version`,
  and `fingerprint: {sha256: HEX, bytes: INTEGER}`. Admission executes `poly
  -v` (stdin is /dev/null) and requires its successful Poly/ML output to match
  `version`. A `version` that contains `RTS version` (made by `poly -v`) must
  equal the output in full once stripped, so another RTS build (architecture,
  interpreter) is refused. A legacy `version` (made by `poly --version`, the
  banner alone) is compared with the banner of the output, the text before `RTS
  version`; that is also how a legacy record meets a new probe. Include other
  external tools too;
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
  mtime_ns}`. `path` is the absolute logical name, `physical` its resolved
  file, `hash` is `{sha256, bytes}`. Require `bin/hol`, `bin/hol.state0`,
  `bin/hol.state.min`, `bin/Holmake`, `holproject.toml`, plus every generated
  `.uo`/`.ui`/`.dat` reachable under `sigobj/`;
- `dependency_inventory`: exactly those sigobj product names. Source `.sig`
  links are not compiled artifacts and are not subject to the freshness mtime
  check; source pins and the later loaded-source inventory cover those.

A product's current mtime must equal the recorded mtime and lie inside that
selection's fresh build interval. Symlinks are allowed only when their targets
remain inside the selected root; no cross-root product or shared product inode
is accepted. Hashes, required products, tool versions, logs, exits, configure
input and command/options are mandatory. Missing or changed prerequisites
reject admission. Unsupported build recipes/platforms remain blocked until a
separately reviewed manifest schema supports them; do not weaken this verifier
to admit an old heap. A local receipt is a provenance record, not a
cryptographic attestation against a malicious producer. Preserve actual
pristine-state evidence too.

### Fresh loading: runnable external gate

`loading.py` times actual first imports in fresh shared-heap processes,
with one pilot per revision, 40 AB/BA pairs of 5 fresh imports per side,
baseline/baseline controls and raw CPU/wall/GC. It requires **both** exact
commit options (the baseline is the develop pin `acceptance.BASE`) and a
source-bound eight-process API-audit receipt (except explicit non-acceptance
smoke):

```sh
python3 -B src/simp/tests/performance/loading.py \
  --baseline DEVELOP_PIN_FULL_40_HEX_COMMIT \
  --candidate CANDIDATE_FULL_40_HEX_COMMIT --module simpLib \
  --api-audit /absolute/path/to/receipt.json \
  --authorize-measurements --output NEW_LOADING_DIRECTORY
```

Repeat for `--module congLib` in a different output directory; this includes
its simpLib dependency, not marginal congLib cost. Pilots/empty brackets check
resolution, not a cached same-process import loop. Source paths, completions,
actual successful exits and exact kernel proofs are checked. See
[`PROTOCOL_LOADING.md`](PROTOCOL_LOADING.md).

## Ordinary startup allocation gate (TASK31)

`startup_gate.py` (client `StartupGate.sml`, `StartupGateUse.sml`, unit
tests `test_startup_gate.py`) measures, in exact words of the TASK29B private
runtime counter (all fields: total, native, rts, interpreter, code, and
heap = total - code), what an ordinary process pays before and when it first
uses the simplifier. One fresh process measures one kind:

  - `hol-startup`: `hol` on `hol.state`, the absolute counter at the first
    user code (a minimal prologue: FFI setup and one snapshot);
  - `hol-first-use`: the first and second `SIMP_CONV` / `SIMP_TAC` call
    (`pure_ss`, `AND_CLAUSES`) on `hol.state`;
  - `load-simpLib`, `load-congLib`: from `hol.state0`, a fresh
    `load "simpLib"` (then `load "pureSimps"`, then the same calls) and a
    fresh `load "congLib"`;
  - `files-simpLib`, `files-congLib`: the same loads with a bracket around
    every `use` the loader makes (`Meta.loadPlan`), for attribution to
    files. They take part in the decision (R2, R3).

Every bracket is the TASK29B one (counter read from C storage after the
bracket; nothing is decoded or printed inside it). An `empty` bracket is
recorded in every process. The words of a load that no file bracket covers
are the loader gap: the load brackets minus the sum of the file brackets of
the same image and sources.

### Trees and images

`startup_gate.py build` repeats the `bootstrap_probe.build_native_hol`
procedure: one native Poly/ML, the private runtime and shim, and then one
fresh `git clone --shared` per tree (`label=rev[+mktool]`):
`poly-includes.ML`, `smart-configure`, then `bin/build --no-cache -jN
--seq=tools/sequences/upto-parallel` with an `env -i`-style environment
(PATH, HOME=/nonexistent, TERM=dumb, LC_ALL=C, TZ=UTC, CONFIG_SITE=/dev/null,
CC, CXX, HOLDIR). Everything is recorded in `lineage.json`. The develop
`mktool` fix is applied to a baseline that lacks it (`+mktool`) as one
counted text replacement in a private tree (`useB "theoryfiles"` before
`useB "theorystats"` in `src/portableML/rawtheory/mktool.ML`), build tooling
that no client loads; the lineage records the seal of the resulting diff.

Independent clean builds are separate images: the exported `hol.state0` and
`hol.state` of two builds of one revision are not byte-identical, so an
image is a unit of the experiment. The optional edits of a private tree that
aim at identical exports (`GATE_BUILD_DETERMINISTIC=1`: one GC thread for
`buildheap`, full collections before the export, `setarch -R`) are off
unless set; they touch the private tree only and are recorded in the lineage
(`hol_build_deterministic`, `hol_determinism_diff`, `hol_polyc_seal`).

### Source exchange over a fixed image

`Overlay` writes, before each process, the files of `src/simp/src` (sources
and `.ui`/`.uo` load plans) in which the first baseline image and the first
candidate image differ into the tree that the process uses, so that baseline
and candidate simplifier sources are compiled over the same image and the
same `HOLDIR`. Every image must hold the sources of its own side first; the
trees are restored at the end. A file that only one side has is written for
that side and removed for the other, so its bracket is measured: R2 takes
its whole bracket as its delta (negative for a baseline-only file), and it
needs a declaration like any other. The blobs of every exchanged file and of
every file the declaration names are recorded in `header.json`.

The source-compiling kinds (`load-*`, `files-*`) first reset the four
readings of `Globals.hol_clock`, the CPU timer that every image stores,
to constants, after the `startup` record and outside every bracket: the
words that compiling `Trace.sml` costs depend on those stored readings,
which differ from image to image. The `hol-*` kinds leave the image as it
is. The absolute figures of the source-compiling kinds are therefore under
that reset and are not client figures (only their deltas are); `gate`
refuses to run, and `replay` refuses an archive, when an exchanged or
declared file mentions `hol_clock` or `checkCPUTimer`, since a reset could
hide a difference that goes through the timer.

### Decision

`startup_gate.py gate --base L1 L2 ... --candidate M1 M2 ...` runs, per
kind, `--pairs` (10) rounds in AB/BA order over every image and both source
variants. With at least two images per side and ten pairs:

  - R1 (image content). `hol-startup`, `hol-first-use` and the `startup` /
    `empty` brackets of every `hol.state0` process are identical on every
    image of both sides, in every field.
  - R2 (sources, image fixed). On every image, candidate sources minus
    baseline sources: the bracket of every file that is not declared is
    exactly 0; each declared file's delta is exact and the same on every
    image; the per-file deltas plus the loader gap equal the load delta,
    with the loader gap exactly 0; every other bracket (the post-load
    `SIMP_*` calls) is exactly 0. A declared entry that measures 0 fails.
    This holds for `load-simpLib` and `load-congLib` alike.
  - R3 (image content, sources fixed). With the baseline sources, every
    bracket is identical across all images of both sides except the files of
    the declared noise set. Such a file must be byte-identical between the
    sides, must have an R2 delta of exactly 0 and must name a mechanism;
    a noise file without a mechanism makes the decision `blocked`.
  - Every process of a cell gives the same record; the foreign-thread
    counters read 0,0; the simplifier results are correct.
  - A module, structure or registered file that the candidate images or
    sources load and the baseline never does fails, unless `candidate_only`
    declares it. Names ending in `Ext` and the extension modules are only a
    label. The absence of the extension modules from an ordinary process is
    checked by the API audit, not here (`ordinary_only` and `forbidden_names`
    in `api-audit/selftest.sml`).
  - A file that only the candidate compiles needs both declarations: an
    `entries` item (null baseline blob) pays for its words in R2, and
    `candidate_only` entries (`module X`, `file X`) allow it in the
    extension rule. Neither implies the other.

Decisions: `pass` (all rules hold, nothing declared carries words),
`attributed` (all rules hold and the declared files carry exact words; it
needs the sha256 of the not-client-visible record, `--record`), `blocked`
(a noise file has no mechanism), `smoke` (fewer than two images per side or
fewer than ten pairs; never a pass) and `fail` (with every reason). There is
no tolerance, subtraction, envelope or outlier removal. `--null` runs the
same rules for two sets of baseline images (the sides must have the same
revision and patch); declared entries are ignored there.

`gate` refuses a setup with repeated image labels, HOLDIR lengths that
differ, more than one revision or patch on a side, or different build flags
between images.

### Declaration

`startup_gate_declared.json` (reviewed data, never the command line, copied
into `header.json` with its sha256) holds:

  - `entries`: a repository path, the exact baseline and candidate blob
    (`null` for the side that lacks the file), the load kinds the file may
    affect, a reason and a mechanism. A different
    blob makes the file undeclared. An entry whose source is byte-identical
    on both sides is allowed only because R2 measures a non-zero exact delta
    on it, and its mechanism says why (signature matching, `open`);
  - `noise`: a path, its blob, a reason and a mechanism or `null`;
  - `candidate_only`: `module X` / `structure X` / `file X` names that the
    candidate alone may load.

A `mechanism` may be a list of lines, joined with spaces. It states the
cause only; measured figures belong to the sealed record and the archive.

### Archive and replay

`gate` writes `records.json.gz` (one record per process), `header.json`
(images and their seals, revisions, patch seals, determinism flags, HOLDIR
and TMPDIR lengths, the lineage sha256, the runtime and shim seals, the
controls receipt, the harness blobs, the declaration text and sha256, the
exchanged blobs, the not-client-visible record sha256), `decisions.json`,
`RESULTS.md` and `receipt.json` (the sha256 of each). The header carries a
schema version (v4); `replay` refuses an archive of another version,
naming it.
`replay --output DIR` checks the receipt and the declaration seal and
recomputes `decisions.json` and `RESULTS.md` from the records alone. An
archive sealed to a not-client-visible record is replayed only with
`--record` of that record.

The `load-*` kinds end with one unbracketed reading of the heap after three
full collections (`sizeHeap`, `sizeHeapFreeLastFullGC`, `sizeAllocation`,
`sizeAllocationFree`, all in bytes; `sizeHeap` includes the allocation area).
The reading is refused unless `sizeAllocationFree` equals `sizeAllocation`:
the formula below is exact only when the allocation area is the fresh one
that the collections leave, not a surviving allocation space.
`RESULTS.md` and `decisions.json` give, per image and kind, the live words
`(sizeHeap - sizeHeapFreeLastFullGC - sizeAllocation) / 8` of each variant
and the candidate-minus-baseline difference of the smallest and of the
largest reading, with the allocation-area sizes seen and `comparable`
(false when more than one allocation-area size is seen in the cell,
in either variant or across the two; the difference is then not
comparable).  Live words are live data of the local heap.  Compiled code
lives in code spaces, outside `sizeHeap`, so it is not in the figure: the
standalone `note_rewrite` code object is not counted, and a near-zero live
difference says nothing about whether it is retained.  The reading is
measured and sealed in the archive, and is no decision input.

`cell` repeats the TASK29B startup bracket of two revisions under chosen
path lengths (TMPDIR, HOLDIR, runtime and shim paths); it measures how the
TASK29B startup delta depends on the image and on path lengths. Every line
names its tree; `--fixtures-rev` takes the paired and matrix fixtures from a
past revision, which a past run carried (that revision's own
`run_paired.py` installs them). `--tmpdir-length N` pads `--tmpdir`, resolved,
with `x` to exactly N characters; the private directories live under it.

`who_pays.py HOLDIR` counts, on a built tree, the executables of the build
sequence that run over `hol.state0` and whose real dependency closure holds
simpLib: for a plain build (scripts, the `selftest.exe` that `all` links,
src/simp/src's own selftest, numheap builds) and what `-t` adds (the `!`
directories). It exits 2 listing any module it cannot resolve, any dangling
`sigobj` link and any payer whose heap is not pinned. Its structural
assumptions are checked, each exiting 2 with a message when it fails: `all`
links `selftest.exe` (read from an unconditional `all:` rule) in every
non-`!` directory whose selftest reaches simpLib; no theory script of
src/simp/src reaches simpLib; no directory after src/boss runs over
`hol.state0`. The `selftest.exe` links of the `!` directories are counted
without the `all:` check: every `selftest.sml` there that reaches simpLib
counts as a link. That holds today because both such directories link it
(src/simp/tests/native-extension directly, cv_compute/soundness_check through
its `.log` target); a new `!` directory that does not link it would be
over-counted. The allowlist `NOT_MODULES` (basis and qualified names that
are no module) is minimal, and a name on it that is also a module of the
directory is refused. `congLib_plain` and `congLib_tflag` split the congLib
payers by build mode.

## TASK31

TASK31 gates the traversal and tactic cases of the matrix (11 `traversal_*`
cases and 42 `tactic_*` cases, 278 cells; `downstream_*` belongs to later
tasks). The case ledger has six singleton traversal cases (size 0) and five
depth cases; the code follows the ledger, whose order (`task31_cases.CASES`)
is the canonical order of every gate. Gate 1 is `task31_identity_grid.py`,
gate 2 is described in "TASK31 allocation gate (gate 2)", and gate 3
`task31_grid.py` (the timing driver; the identity module imports it, not the
reverse), the decision per cell in `task31_dispose.py`; the cases, the sample,
the infeasible set and the list of sources are data in `task31_cases.py`,
which holds no measured number. The reviewed differences of the candidate are
the data of `task31_attributed.json` (read by `task31_pins.py`, which the
timing grid seals; the accounting is `task31_attribution.py`).

The controls receipt seals the files of `allocator-counter/` and those named
in `private_runtime.PERFORMANCE_INPUTS`, `loading.py` among them, so
`loading.py` is a performance input: the controls receipt must be made at the
measured candidate, after its last change.

### Gate 1: source identity, every cell

`task31_identity_grid.py identity --output DIR --candidate COMMIT
--authorize-measurements` runs, for each feasible cell, the real paired
runner (`run_paired.py --matrix-performance`) once: one fresh process for
the baseline and one for the candidate, the runner's own loaded-source audit,
one pair of three samples, free ramp calibration of 1 s batches (nothing is
timed for a decision, but the runner accepts a process only if every sample
lasts at least half the batch seconds; a major collection of about 0.1 s in
the last calibration batch of a cell of about 80 ns per iteration stopped a
0.1 s ramp at a count whose samples were too short, systematically for
`tactic_dependency_reverse_construct-1000`, so the target is well above twice
a collector pause). A refused cell is set aside as `<cell>.json.xz.failed-N`
and measured again by `--resume`; the refusal names the runner's failure.
The runner is started through `task31_snapshot.py`, which runs it
unchanged (`runpy`, the same arguments and exit status) and, just before
the runner deletes its private trees, records every file of them as
`private-snapshot.json`: its size, its sha256, its sha256 with the
directory of the side replaced by `<PRIVATE>`, and for a file of at most
256 KiB its text. A loader product (`.uo`, `.ui`) names the directory of its
side, so the raw hashes of two sides always differ; the normalized ones
differ only if the compiled content does. The row derivation checks the
snapshot against the runner's own hashes and derives the normalized digest
again from the stored text. The files of `.hol/locks/` (named after process
ids) are never part of a closure.

`task31_identity.py` derives the row of a cell from the archived folder:

- the closure: every source the process elaborated (`use`), private (the
  simplifier sources and the relocated shared modules) or shared, with its
  sha256 and, for a private source, the normalized digests of its products;
  the elaboration order; the files of the initial heap (the `heapfile`
  events). A source or product that one side lacks or that differs, a
  different order (the first position where they part is named), or a
  different heap list is a difference, listed by file;
- the work: the ordered checks of the fixture (each proof is compared inside
  the process with an independently built expected theorem), the keys of the
  observations, the expected test count, the outcome, the samples, schedule
  and result consumption of each timed workload, and the storage rows.
  Counts that depend on the host (the calibration batches and their times)
  are not part of it. This is a check of the protocol shape: the matrix
  schema fixes every one of these fields for an accepted process, so two
  accepted processes of a cell always agree. The behavioural evidence of the
  work (stages, counts and the result digest) is the work row of the
  allocation gate, which the disposition requires;
- the tracked file behind each private file (a generated theory file maps to
  its script); a private file that maps to none is refused;
- the head and dirty state of the checkout, the inputs and the tools.

A cell is `identical` when both lists of differences are empty. It is
`attributed` when every difference is of a `source` entry of the reviewed
table whose two git blobs are exactly the cell's, the elaboration order is
equal and the shape of the work is equal; the entry records the sha256 of
the file on each side. Any other difference makes it `different`: it is not
passed by identity.

Reviewed table. `task31_attributed.json` holds `{"schema", "entries",
"history"}`. An entry is `{path, kind, baseline_blob, candidate_blob,
reason, gate}`, `kind` being `source` (a simplifier source whose private
copy differs), `heap` (a file of the shared heap) or `build` (a Holmakefile,
manifest, tool script or project file of a loaded directory, or a file
of a name Holmake reads beside its build directories, see "The tree");
`gate` says what measures the difference. A `candidate_blob` of `null` is
a placeholder that `identity` refuses (it names the blob git has, to be
filled at integration); the filled entries that are sources of the timing
table are its pins (an entry of kind `heap` or `build` is no source of the
table and pins nothing).
The file is outside the seals of the counts; every record carries its sha256
and the entries it was judged by, and `history` maps the sha256 of an
earlier file to its entries, so that an old grid still replays. A full
identity grid and the disposition use the committed file only;
`--attributed PATH` names another file in a diagnostic (`--only`) and is
refused otherwise. The disposition binds the gates to the committed file
through the pins, not through the whole table:

- the identity grid's recorded table has the sha256 of the committed
  `task31_attributed.json` (an identity grid made by an earlier file is run
  again), and its seal is recorded as the `attribution` input;
- the pins of the timing grid and of the follow-up (its inventory, each
  resumption and, for an extension, the first stage and its resumptions)
  are the committed table's projection onto the sources the grid measures
  (`task31_pins.pins` over `task31_cases.SOURCES`, the function the driver
  uses), by the pins the seal of the file stands for (the file itself, or
  its `history`); they are recorded as the `pins` input. So adding an entry
  of kind `heap` or `build`, or for a file that is no measured source (with
  the sha256 of the file it replaces in `history`), voids no timing grid,
  and any change to the entry of a measured source does.

The tree. The runner takes only `src/simp/src` from each commit; the shared
sources, the heap, the build tools, the fixtures and the launcher come from
the one checkout, so differences there are invisible to the closure
comparison. The grid therefore lists every tracked file that differs between
the commits (`src/`, `tools/`, `tools-poly/`, `bin/` and the rest of the
repository) and classifies each one from the git blobs and from the files
the receipts show were loaded (elaborated, found loaded, or in the initial
heap, over all measured cells and both sides):

- `attributed`: an entry names exactly its two blobs;
- `mismatch`: an entry names other blobs;
- `unattributed`: loaded, no entry;
- `unattributed-build`: a file of the build tools, their prelude or the
  build sequences (`tools/`, `tools-poly/`, `bin/`, which the receipts do
  not record), a build file of a directory that a loaded file comes from,
  or a file of a name Holmake reads beside the directories it builds in
  (`task31_attribution.UPWARD`: `holproject.toml`,
  `holproject.local.toml`, `.holpath`, `.hol_preexec`) anywhere in the
  repository that is not `EXCLUDED`, no entry. The last rule is general and
  conservative on purpose: Holmake looks for these files in the ancestors
  of every directory it visits, and it also follows `INCLUDES`,
  `PRE_INCLUDES` and the external directories of a project, so the loaded
  directories and their ancestors are not the whole set. No include closure
  is computed; a file that cannot matter is attributed with its reason;
- `excluded`: on the reviewed list `task31_attribution.EXCLUDED` of paths
  that are no part of any build a cell measures, each with its reason (the
  measuring harness and paired runner, installed from the checkout; `help/`,
  read only by the help-database step of the build, which runs after the
  sources are built and makes nothing a cell loads; `CLAUDE.md`,
  documentation), and not loaded;
- `unloaded`: no receipt shows it loaded on either side and it is no build
  file.

The first, fifth and sixth pass; the others make the grid `different`, with
the file and the reason in the decisions and the report. A grid whose loaded
closure is not the same in every measured cell, whose cells ran in different
checkouts, or that has an uncovered or unused source is `inconclusive`. A
cell, and the grid, are `attributed` when a reviewed difference is present,
else `identical`.

Infeasible cells. The 33 cells of the eleven heavy families at 10000
assumptions (`task31_cases.INFEASIBLE`) do not fit the process timeout of
the grid (1800 s). They still get a row, whose route says so: the worst
identity of the measured cells of the same case, valid only if the loaded
closure is the same in every measured cell of the grid (it is built from one
fixture text; the closure digest is one per side over all measured cells,
else the row is `unresolved`). The work is recorded as "not run:
infeasible".

Checks beside the cells: `uncovered` lists the tracked files the baseline
elaborated that `SOURCES` lacks; `candidate_only` the files only the
candidate elaborates; `unused_sources` the files of `task31_cases.SOURCES`
that no cell elaborated; `git_differing` the files whose git blobs differ.
`task31_identity_grid.py sources --output DIR [--heap]` prints the files the
cells elaborated (with the heap files) from a grid; `task31_cases.SOURCES`
is the sorted union of the elaborated files.

Records. `DIR/inventory.json` (baseline, candidate, the cell list, the seals
of the identity code, the attribution table and its seal, the git blobs of
the sources, of the entries and of every file that differs, the checkout
record, one run per cell with the archive and its seal) and
`decisions.json`; each cell's folder is packed to `NAME.json.xz`. The
attempts ledger of the checkout records the opening and the close of each
identity grid (table `task31-identity`, stage `identity`).
`identity-replay --output DIR` verifies the seals of the code (the grid's
modules, the timing engine and the runner), the checkout, the attribution
table, the source blobs and the tree, unpacks every archive, derives every
row and every decision again from the bytes, and requires them equal to the
records; `--ledger FILE` also requires the opening in a ledger. The grid is
made in the checkout of the candidate (`prepare` as for the timing tables;
the stamp and `recheck` bind the head, the tree and the products, and the
grid is dead if the checkout changes); `--only CELL ...` is a diagnostic, in
any checkout, never a grid decision. The exit status is 0 when the grid is
identical or attributed, 1 when it is different, 2 when it is not
conclusive, 3 when refused.

### Gate 3: the stratified timing table

`task31_grid.TABLE` (`task31`) is a `timing_grid.Table` over the 28 cells of
`task31_cases.SAMPLE`: the six singleton traversal cases at size 0, the five
depth cases at depth 100, the `complete` stage of each of the 14 tactic
families at 100 assumptions, and `tactic_supplied_complete-1000`,
`tactic_asm_complete-1000` and `tactic_installed_reuse-1000`. Schedule
`warmup`, headroom 1, 20 pairs of 5 samples per cell in the first stage,
batch seconds 0.3 (1.0 for the six singleton traversal cases, whose
operations are sub-microsecond), layout seed `task31-layout-1`, and
TASK30's equivalence policy and second stage (3% margin on inclusive CPU and
wall, GC reported, no outlier removal, the pair counts of the second stage
from the develop/develop control).

The table names `sources` (the elaborated sources) and pins the blobs of
the filled entries of the reviewed table that are among them, with the
reason of each and the sha256 of `task31_attributed.json`: a source that
differs without a current pin never passes, and `run` refuses to measure
it. The code that computes the pins is `task31_pins.py`, one of the sealed
files of the table. Adding an entry for another file changes that sha256 and
no pin; the grid replays by the pins of the file it was made with
(`pin_history`). The driver has its own history (`DRIVERS` and the others,
as TASK30's), empty until a grid is recorded; a change to the identity
module, to `task31_identity.py` or to `task31_attribution.py` alters no
seal of a timing grid. Every timing record carries the pins, the projection
of the reviewed table onto the measured sources: a change to the entry of a
measured source voids the grid, and adding or changing a heap or build
entry does not. The identity module offers
the identity commands only (`prepare`, `identity`, `identity-replay`,
`sources`). The difference below `src` is published by `tree`. The counts file
`task31_iterations.json` does not exist until `pilot` and `predeclare` make
it; the commands are the engine's:

    task31_grid.py prepare
    task31_grid.py pilot --output DIR --authorize-measurements
    task31_grid.py predeclare --grid DIR --output task31_iterations.json
    task31_grid.py verify-counts --grid DIR
    task31_grid.py run --output DIR --candidate COMMIT --pilot PILOT \
        --authorize-measurements
    task31_grid.py extend --grid DIR --output DIR2 --pilot PILOT \
        --authorize-measurements
    task31_grid.py replay --output DIR --pilot PILOT

A batch must last at least half its seconds (`performance_schema.validate`)
and a warmup count is ceil(seconds * n / wall) of the calibration, never
below one.

Follow-up. `task31_followup.py` is the table of the cells that the first
grid and its second stage left open (`CELLS`: `traversal_reuse_hit-0`,
`traversal_weakening-0` and `traversal_side_conditions-100`; with `CELLS`
empty the module has no engine and refuses every command). It takes the
policy, the batch seconds, the samples, the baseline, the sources and the
pins of the TASK31 table, twice its pairs, its own layout seed and counts
file; the first grid is replayed in full by its own table before the counts
are derived. Its commands are the engine's, and its attempts go into the
TASK31 ledger.

### The decision per cell

`task31_dispose.py --identity DIR --grid DIR --pilot PILOT --allocation DIR
--survey PATH` replays the identity grid (with its opening line in the
ledger) and the timing grid in full (and a
follow-up with `--followup DIR --followup-pilot PILOT`, whose cells replace
the first grid's) and decides every cell:

- **pass** iff its identity is `identical` or `attributed`, AND its
  allocation row has the decision `pass` and the work row `equal` where the
  allocation gate measures it (every cell but the infeasible ones), AND the
  timing class is `pass` where the cell is sampled (and a cell outside the
  sample has no timing row);
- an infeasible cell passes by identity alone and is recorded as "untimed,
  unallocated: infeasible". When its identity is `attributed`, the record
  names the attribution and the cells of its family that measured it
  (allocation cells of at most 1000 assumptions that passed with equal work
  and an attributed identity, and the family's passing cells of the timing
  sample);
  with none of either it is `incomplete`;
- a gate that decided against a cell makes it `fail` (allocation words
  that fail, or a work row that `differs`); a gate with no decision for a
  cell it must decide leaves it `incomplete`, which includes an allocation
  row that is `inconclusive` or whose work row is `inconclusive` or missing,
  a timing class that is not a decision (`inconclusive`, `control_limited`,
  `protocol`) and an identity grid that is inconclusive; a file below `src/`
  that the grid could not account for fails the whole.

The cost survey is an input of the command, not of the repository: `--survey`
is a JSON file `{"schema": "task31-cost-survey-v1", "process_timeout": N,
"cells": {CELL: {op1000, setup1000, check1000, op10000, setup10000,
check10000}}}` with one entry per infeasible cell. Its numbers and its
sha256 are recorded, and `--check` reads it again.

The allocation gate is replayed, not trusted: the command requires the
directory of a complete (not partial) allocation grid of task `task31`, with
the candidate and baseline of the other two gates and the harness of the
timing grid, replays it with `allocation_matrix.py` (every archive, every
decision) and then reads its `decisions.json` (see "TASK31 allocation gate"
above): `candidate` and `baseline` equal to the grids', `complete` true,
`infeasible` the infeasible set, and exactly one row for every other cell,
none repeated, a row with the decision `pass` having at least 10 pairs (an
unresolved row may have `"pairs": null`). A row of any other shape is
refused.

One rule for every judged TASK31 timing table, the first stage's `task31`
and the follow-up's `task31f` alike: at most one attempt that is not void
per table and stage. Every attempt of either table in the ledger that the
command does not judge (the final stage named by `--grid` or `--followup`,
and the first stage of an extension) must be void, as in the TASK30
disposition (`void_attempts.py`, sealed into both `CODE`s): no cell of it
admitted a measurement, it has no resume line and one close line,
`inconclusive`. A void attempt may be redrawn; an attempt that measured, may
have (left open, resumed, closed more than once) or ran in more than one
output is refused. The attempts are recorded (`timing_attempts`,
`followup_attempts`) and printed.

The record carries the seals of the code (`task31_dispose.CODE`, every
module the decision takes from, `task30_grid.py` for the harness match and
`task31_pins.py` included, with `HISTORY` for earlier versions) and of every
input it read, and the attempts
the ledger holds for the timing table and for identity (all, and the
candidate's). The command prints one line per cell that did not pass and
every infeasible cell, then the verdict line (status, counts, the identity
status and attributed files, allocation, timing, the infeasible count,
candidate, harness, attempts), and exits 0, 1, 2 (3: refused).
`--record FILE` writes the disposition, `--check FILE` requires that it
derives again.

Tests: `test_task31_cases.py`, `test_task31_attribution.py`,
`test_task31_identity.py`, `test_task31_identity_grid.py`,
`test_task31_grid.py`, `test_task31_followup.py`,
`test_task31_attempts.py`, `test_task31_dispose.py`.

## Matrix boundaries and final evidence

[`MATRIX.md`](MATRIX.md) and the frozen schema define the requirements and
case bindings. Runnable does not mean measured or passed. All named stages
and declared sizes remain distinct; a smoke cannot cover the full matrix.
Graph parsing, batch GC counts, RSS snapshots and controlled-ref release are
integrated instrumentation. MATRIX.md lists the blocked prerequisites.

Only current fixture/source-tied manifests and raw observations count; unused
temporary validation or earlier fixture versions cannot be relabeled final.
Independent manifest admission validates build prerequisites only and `run
--mode independent` still blocks pending fresh independent launchers, path
inventories and consumed proof/storage pairs. No shared `hol.state0` result
becomes independent by changing a report label.

Ordinary arithmetic/reduce/boss fixtures are runnable with shared
dependencies; independent downstream proof/build acceptance and
migrated-consumer costs remain separate. Keep normal ordinary/extension
suites enabled. Passing Python tests, smokes or controls establishes
machinery behavior, not numerical parity or the final release gate. See
[`README.md`](README.md) for maintained check targets.
