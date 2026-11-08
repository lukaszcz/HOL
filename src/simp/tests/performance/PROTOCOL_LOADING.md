# Fresh ordinary first-import timing

`loading.py` measures the first ordinary import of `simpLib` or `congLib`,
not steady-state simplification, not process creation, and not
independent-build or release acceptance. It reuses
`compatibility/run_paired.py` extraction, fixture bootstrap, trace
validation, and path/source fingerprinting. No production code is
instrumented.

## Invocation

Stop unrelated builds, HOL processes and performance runners first. The
serial frontend takes the same host-wide and git-directory advisory locks as
`acceptance.py`; child processes inherit them. Explicit authorization is
needed for even a smoke run. Do not run concurrently with builds or
telemetry probes.

A decision run has fixed settings, so it takes neither `--pairs` nor
`--reps`:

```
python3 src/simp/tests/performance/loading.py \
  --baseline DEVELOP_PIN_FULL_COMMIT --candidate CANDIDATE_FULL_COMMIT \
  --module simpLib \
  --api-audit /absolute/path/to/api-audit/evidence/RUN/receipt.json \
  --authorize-measurements --output /absolute/path/to/new-loading-simp
```

Repeat with `--module congLib` and a different output directory. Each
import starts from a fresh `hol.state0` process. The congLib case includes
its ordinary simpLib dependency; this is **not** congLib marginal cost after
simpLib. Separate results must not be added together as a two-import
estimate. Only full immutable commit IDs are accepted, and the baseline of
a decision run is the develop pin `acceptance.BASE`. Worktree edits are not
selected implementation sources. Output directories must not already exist.

Other modes:

- `--smoke --pairs P --reps R`: protocol check of the harness, at most 2
  pairs of 1 import (`loading.SMOKE_PAIRS`, `SMOKE_REPS`). No statistics;
  the audit receipt may be omitted. Never performance evidence. A smoke run
  may not use the layout seed of a decision run or of its second stage
  (default `loading.SMOKE_SEED`). Every smoke run is recorded in the
  attempts ledger before its first process, and its end is recorded
  whatever its outcome (see Attempts ledger).
- `--calibrate --pairs P --reps R`: pilots and the B/B phase only
  (P >= 10). It measures the develop pin against itself: the baseline and
  the candidate are both `acceptance.BASE` (`--candidate` may be
  omitted), and anything else is refused before any process runs. Reports
  the jitter quantities below. No candidate phase, no audit receipt, no
  decision.
- `--layout-seed S`: the layout seed of a smoke or calibration run (a
  smoke run: neither of the decision seeds). A decision run uses
  `loading.LAYOUT_SEED`. At most 58 characters.
- `--extend RUN_DIR --output DIR`: the one second stage of a first-stage
  decision run (see Counts and the second stage).
- `--replay RUN_DIR`: recompute a finished run from its receipts (see
  Replay). It takes only `--expect-seal`, `--first-stage` and `--ledger`.
- `--ledger-status`: list the attempts of the ledger (see Attempts
  ledger).

Exit status of a decision run: 0 only if every gated metric passes, 1 if
any gated metric fails, 2 for an inconclusive or blocked result.

## Timed boundary and proof check

The generated private runner is based on `paired/runner.sml`. Only
runner.uo is linked; proof selftest dependency metadata is built, not
linked. The runner records the initial heap/map, activates exactly
private-first plus shared sigobj search paths, applies the layout padding
(see below), and dynamically loads CheckSupport before timing. Neither
ordinary library may already be present. There are no static simplifier
references in the runner or its linked dependencies.

The timer wraps the **actual** `Meta.loadPlan tracedUse module` call,
including source elaboration, transitive dependencies, ordinary
initialization and trace I/O. Each traced source must have a matching
completion; the target's completed source must be inside
`loading.begin`/`loading.end`. The loading call is a top-level runner
operation: a traced selftest cannot encapsulate it, because that would
produce nested pending `use` events, which the validator rejects.

After the timer stops, the proof selftest is dynamically loaded. It
consumes a real `simpLib.SIMP_CONV` result, checking the exact closed kernel
equality `(T /\ p) = p` and absence of hypotheses. The congLib fixture also
checks the corresponding `CONGRUENCE_EQ_SIMP_CONV` result. Additional
proof-only dependencies, including pureSimps, are outside the timer.
Missing checks, observations, source completion, final inventory or exact
successful exit reject the process. The full initial/final map and actual
paths/hashes are retained per process.

## Measurements

Every process is fresh: a module is never loaded twice in one process,
because Meta would cache it and the second load would measure a no-op.
Before each import the runner measures forced-GC timer accounting and an
empty bracket. Raw fields, in order, are:

```
wall,nongc_usr,nongc_sys,gc_usr,gc_sys,cpu_usr,cpu_sys,gc_user_only
```

`cpu_usr/sys` include GC. `gc_user_only` is `Timer.checkGCTime`, **not**
total GC CPU and must not be added to inclusive CPU. Sequential snapshots
are checked for agreement within 0.02s. Reported metrics are wall, inclusive
CPU, and GC CPU (`gc_usr+gc_sys`). Process-launch wall time is archived
separately; it is not an import metric. All fields must be finite and
nonnegative. The forced-GC control must additionally show positive GC CPU
and positive GC-user time; an all-zero or otherwise vacuous control rejects
the process. Zero GC in the actual import is allowed after that positive
accounting control, but undefined paired GC ratios are inconclusive.

One pilot per selected revision precedes the phases. Each pilot and each
measured import must exceed 100 times both its own empty-bracket overhead
and the nominal 1us time representation granularity, for wall and inclusive
CPU. Failure gives an inconclusive measurement, not batching or dropped
samples. The forced-GC bracket checks accounting; it is not import latency.
This is warm-filesystem, fresh-runtime loading, not a cold-cache or
cold-machine claim.

### Unit, schedule and layout

A **pair** has two sides, baseline and candidate. The sample of a side is
the **mean** of its R = `loading.REPS` first imports, each in its own fresh
process, with no sample removed. The processes of a pair are interleaved
(`A B A B ...` in AB pairs, `B A B A ...` in BA pairs); pair 0 is AB, pair 1
BA, and so on (`loading.schedule`). The timing grid takes the median batch
within one process instead; here a process holds one import, so the mean of
the R processes plays the part of that batch statistic. Pilots are excluded
from the statistics. In the B/B phase both labels execute the same private
baseline launcher but stay distinct fresh processes.

Code layout: every process compiles its sources at startup, so the address
of later code depends on what was compiled before it. Each process sets
`PERF_LAYOUT` to `performance_schema.layout_units(seed + "-r" + rep, pair,
side)` (pilots: seed `seed-pilot`), the number of padding functions
`paired/runner.sml` compiles before any dependency. The B/B and candidate
phases use the same draws for the same (pair, side, rep); baseline and
candidate draw independently. The seed is recorded in `loading.json` and the
value in every process receipt, and replay re-derives each.

### Decision

The decision is the timing grid's, from one place:
`loading.POLICY` is `acceptance.EQUIVALENCE_POLICY` itself.

- 3% margin on inclusive CPU and wall (`gated_timing`). GC CPU is reported,
  not gated, because inclusive CPU already contains GC time.
- Per metric `acceptance.timing_rule` gives `(margin, gated)` and
  `acceptance.paired_statistics` the median paired candidate/baseline ratio
  with its deterministic 20,000-resample paired bootstrap 95% interval.
  `low > 1.03` fails, `high <= 1.03` passes, otherwise inconclusive. Any
  zero denominator is inconclusive without dropping pairs.
- `acceptance.apply_control` applies the B/B control: its whole interval
  must lie in `[1/1.03, 1.03]`, otherwise the comparison is not admissible
  and a non-fail becomes inconclusive. A candidate fail is never excused.
  Controls are never subtracted as a noise budget.
- `success` means protocol completion, **not** that performance passed;
  inspect every candidate metric decision.

The control phase runs before the candidate phase, so the two measure
different time windows. Drift between them is not corrected, and a control
and a comparison that disagree because the host changed are not told apart.

## Counts and the second stage

A decision run is exactly `loading.PAIRS` = 40 pairs of `loading.REPS` = 5
fresh imports per side. Any other count is refused, so the count cannot be
chosen after seeing candidate data.

Model: let `unit_sd` be the sd of the paired log ratio of two R-means times
sqrt(R). The 95% half width of the median of n paired log ratios is about
`1.96 * sqrt(pi/2) * unit_sd / sqrt(n * R)`, so a half width of at most
`timing_grid.TARGET` (0.015, half the margin) needs

    n * R  >=  (1.96 * sqrt(pi/2) * unit_sd / TARGET)^2

(`loading.required_units`). The first stage is sized for
`loading.UNIT_SD_BOUND`: `PAIRS * REPS >= required_units(UNIT_SD_BOUND)`.
`--calibrate` reports, per metric, `process_log_sd` (the sd s1 of one
import, pooled within a side of a pair), `paired_log_ratio_sd`, `unit_sd`,
its one-sided 95% chi-square upper bound `unit_sd_upper` for the n pairs
(`unit_sd * sqrt(df / chi2_0.05(df))`), and `required_units` for that
bound. One rule accepts a calibration (`loading.covered`, printed by
`--replay` of a calibration): every gated metric has `unit_sd_upper` at most
`UNIT_SD_BOUND`. Otherwise the constants are too small for the host.

**Second stage.** It is allowed only when the B/B control missed its window
for a gated metric and no gated candidate metric failed. Its pair count
comes from the B/B data only: `timing_grid.second_stage_pairs(
timing_grid.control_half_width(...), PAIRS, timing_grid.TARGET,
timing_grid.MAX_PAIRS)`, the grid's rule (twice the first-stage pairs at
least, `MAX_PAIRS` at most). `--extend RUN_DIR` replays the first stage,
refuses unless the rule allows it, and runs a new complete run (pilots, B/B,
candidate) of that many pairs at the same R, the same revisions, module and
sources, with layout seed `loading.EXTENSION_SEED`. The new `loading.json`
records the first stage's `loading.json` seal, and its decision replaces
the first stage's. A first-stage fail, a valid control and every other
inconclusive result are final; so is the second stage's own result. A
candidate-limited inconclusive is resolved structurally, not by rerunning.

**Attempts ledger.** Every decision run and every `--extend` is one draw,
and the draws are recorded in the timing grid's attempts ledger
(`timing_grid.Ledger`, a hash chain) under the table name
`loading.TABLE`: `.agent-files/evidence/task31-loading/attempts.jsonl`
below the root of the checkout, which git must ignore (the run refuses
otherwise). The run appends an `open` line before its first process, with
the stage (`first`, `second`), a fresh attempt id, the candidate, module,
baseline and layout seed, `source_key` and `baseline_key` (below) and, for a
second stage, the attempt id of its first stage; and after the run a `close`
line with the seal of its `loading.json` (the value `--expect-seal` takes)
and its status: `pass`, `fail` or `inconclusive` for a decision; `blocked`
for a run stopped by a rejection of an extension or of a new stem in a
candidate process; `failed` for any other run with `success` false,
a rejection of a baseline process included. Everything before the first
line of the run (the keys, the ledger check) happens before the output
directory is created, so a refusal leaves nothing behind.

The draw key is the extracted inventory: the SHA-256 of the sorted
`(git_path, git_blob)` pairs of the sources `rp.extract` takes from the
revision (`loading.extracted_files`: sources and signatures of
`src/simp/src` and `src/simp/src/poly`, without `selftest.sml` and
`mosml/`). A commit that changes only a file that is not extracted (notes,
Holmakefiles, the self-test, `mosml/`), or only its message, has the same
key. The measuring checkout's own files (`src/1`, `bin/hol.state0`, the
fixtures, the timing template) are the environment: sealed in `inputs`, and
no part of the key. A run checks the key against what it extracted, and
`--replay` recomputes it from the report's `sources` and compares it with
the report and the ledger's opening.

The rules:

- for one module, a first stage is refused when the ledger holds a judged
  first-stage attempt of the same candidate commit or of the same
  `source_key` (whatever the commit), and an `--extend` when it holds a
  judged second-stage attempt, so there is at most one `--extend` per first
  stage;
- an attempt is void only when all of these hold: it has exactly one close
  line, with status `failed`; the `loading.json` in its output exists and has
  the seal of that close line, the attempt's id and stage, `success` false
  and no `blocked`; the control and candidate receipts in the output folder
  are exactly those the report lists, each with its seal, and not admitted
  (`accepted` false in the receipt itself). Every other attempt, closed or
  not, is judged: a pass, fail, inconclusive or `blocked` close, a `failed`
  close that admitted a measured process or whose output is missing or
  differs from its seal, and an attempt opened and never closed (a crash, a
  kill);
- two points are looser than TASK30's void rule, as current rules. The two
  pilots (one baseline and one candidate import, single and uncalibrated,
  never entering a decision) are exempt: an attempt that fails after its
  pilots and before the first control or candidate process is void. A
  process that is rejected counts as not admitted even if it printed its
  timer fields; the first control process is baseline against baseline, so
  such data can only be baseline data;
- `blocked` is a finding about the candidate and is always judged. A
  baseline process that loads an extension (the baseline `acceptance.BASE`
  has none, so this is a harness or environment defect) is rejected but
  not `blocked`: the run closes `failed` and follows the void rule, so it
  is void when no control or candidate process was admitted (the baseline
  pilot is process 1, and pilots are exempt) and judged when one was;
- a void attempt may be redrawn, and stays in the ledger;
- the outputs of all attempts, void ones included, stay at their recorded
  paths and are published with the ledger: a void attempt is void only while
  its output can be read there, and the replay of a later judged run refuses
  with the name of the attempt whose output is missing or changed;
- a judged attempt that decided nothing (killed, interrupted, failed after
  measuring, blocked) blocks the gate for that candidate, source key and
  module and stage;
- an attempt with more than one close line or without exactly one opening,
  a line of the table with an event other than `open`, `close`, `smoke` or
  `smoke-end`, a line that lacks a field its event has in
  `loading.EVENT_FIELDS` or holds a value of another type, a smoke with
  two start lines, and a `smoke-end` with no start or a second end, is a
  corrupt ledger, refused for a new run (a smoke run included), in
  `--ledger-status` and in replay. That one table is what the readers and
  the validator both use;
- a smoke run is recorded by two lines. Under the serial lock, after the
  check that the ledger is excluded from git, after the whole ledger was
  read and validated (as `--ledger-status` does), and before the output
  directory is created or any process starts, a `smoke` line is appended:
  attempt id, candidate, baseline, both source keys, module, seed, pairs,
  repetitions, output and checkout. When the line cannot be appended,
  nothing runs. When the run ends, whatever its outcome, a `smoke-end` line
  names the attempt, its `success` and, if its `loading.json` was saved, the
  seal of it. A smoke never saves into an output directory it did not create.
  A smoke with no end line (its run was killed, or the end line could not be
  written) is listed as `unfinished`. A smoke is information only: it is no
  attempt, never judged or void, and blocks no draw. `--ledger-status`
  lists every smoke (those of `--module` when given). The replay of a
  decision run lists the smokes of its module in which its candidate commit
  or extracted-source key is the candidate or the baseline. A smoke replay
  does not consult the ledger, and an archive with no ledger line replays
  without a ledger. The outputs of smoke runs are published with the
  ledger;
- `--extend` replays its first stage against the ledger before it runs;
- `--replay` checks the run against the ledger and prints every attempt of
  the table (id, stage, candidate, source key, module, statuses, void and,
  when judged, why, output and checkout), and the checkouts when there are
  several;
- the ledger is a discipline and not a proof: a deleted ledger, or a ledger
  of another checkout, cannot be detected, so the handoff publishes the
  whole ledger, `failed` attempts included, and any earlier judged line for
  the same key blocks a redraw.

The tool has no override for a judged attempt. A new draw of the same key
after one that decided nothing needs two things: a written policy decision,
kept with the evidence outside git, and a reviewed harness change
that implements it (as TASK30's follow-up table did). A changed candidate
inventory is a new draw anyway.

`loading.py --ledger-status [--module M] [--repo R] [--ledger FILE]` prints
the table (every attempt, void or why it is judged) without
replaying a run, for a gate that is blocked, failed or unclosed.

## Extension absence

Extension modules must be absent from every ordinary process. After the
timed import, outside the timer, the runner emits `loading.extensions`:
every loaded module (`Meta.loaded`), file in the final file map, and
structure of `#allStruct PolyML.globalNameSpace ()` that is an extension, in
order of first occurrence (`none` if empty). Extension names are the API
audit's `forbidden_names` (read from `api-audit/selftest.sml`, the one
definition: `loading.EXTENSION_NAMES`) and the audit's patterns `*Ext`,
`*ExtLib` and `simpMarker*`. The observation may hold only extension names
or `none` alone. The validator also scans the used, heap and loaded file
paths for the same names. Any finding rejects the process and stops the
run. This is enforced for every process of the candidate and, because a
decision run's baseline is the develop pin which has none, of the baseline
too.

Name-independent rule: the stems (`use`, `used`, `loaded`, `heapfile`
paths) of each candidate process, minus the stems of the baseline
processes of the same run, must be empty, except for stems in
`loading.STEM_ALLOWANCE` (a reviewed list, empty). It is checked as
processes finish and again in replay, and it catches a helper of an
extension whose name matches no pattern.

"Caches" here are the files and modules that hold or persist extension
state (for instance `splitPersistLib`, `SplitData` and `simpMarkerTheory`
in the audit's list). Whether registered extension state, foreign registry
ownership or listeners exist is the API audit's job; this gate checks the
loaded names and file stems above.

## Separate eight-process semantic gate

Ordinary initialization callbacks, foreign registry ownership, exact
listener identities and absence of extension modules are checked by
`api-audit/run.py` in eight fresh processes (both import orders, attribute /
exporter ownership, installation before / after). Timing does not replace
this gate. A decision run requires its successful receipt, eight distinct
cases, sealed logs and actual-files inventory, source-sealed gate fixtures,
exact process exits and final observations. The sealed sources, the
per-case check counts and the native modules that must be loaded all come
from the audit's own `audit_constants.py` in the audited tree, never from a
copy. The actual native ordinary and extension imports must match the
selected candidate git bytes. The gate need not share the same commit label
when irrelevant files changed, but the loaded simplifier bytes must match.

The audit is run outside the timing window:

```
bin/Holmake --holstate=$PWD/bin/hol.state0 \
  -C src/simp/tests/api-audit check
```

Use that run's unique receipt. Evidence for different source bytes is
rejected. This is an external semantic gate ledger, not timing
instrumentation inside the audit and not a claim that the audit ran on the
baseline.

## Provenance and failures

`loading.json` (schema `task31-loading-v4`) records exact revisions and
immutable extracted source/git-blob seals, private generated
fixtures/products, launcher text/options, interpreter/runtime versions and
hashes, environment, layout seed, calibration, ordered runs, shared actual
source/product seals, paired statistics, the stage and gate identity. Git
extraction seals remain authoritative through fixture installation, builds,
actual source validation and the final unchanged-input check. Generated
fixtures are sealed before building too. Post-build product hashes cannot
replace either input seal; a build that changes even an unloaded selected
signature is rejected.

On supported Linux dynamic runtimes, `ldd` discovers the libraries linked
by **the actual `bin/hol`**, not PATH's `poly`. Discovery runs with the
sanitized launch environment, timeout and inherited serial locks. Its
command, output, exit and timeout are archived. Every file-backed
dependency, including the loader, has a logical path, resolved target and
content seal; the kernel VDSO is not a file. These hashes are included in
`inputs`. Missing libraries, partial/unresolved output, failed/empty
discovery and unsupported discovery formats block the run. Before success
the original file seals are rechecked and discovery is repeated; changed
mappings or same-byte symlink retargeting also reject. ASLR addresses are
not identities. PATH's `poly -v` is separately archived compiler
provenance, queried under the same environment/timeout; it is not proof of
HOL's linked runtime version. This is local consistency checking, not
hostile producer authentication or protection against concurrent changes
restored between checks.

Compressed unique process receipts retain raw output, complete ordered
protocol and actual loaded paths. Inputs are checked again before success;
shared actual inputs remain identical across processes. Processes use one
GC thread. Timeouts kill/reap the whole process group; an absent launcher,
timeout, nonzero exit, wrong path, mutated source or incomplete output
cannot count as a successful sample. Private build trees are automatically
removed after their final use. Failed runs retain compact diagnostic
receipts and a failure report, never a success inferred from .uo creation.

This harness uses one existing shared heap and dependency tree, with
isolated selected simplifier sources. It does **not** satisfy a separate
clean independent baseline/candidate build gate. The main matrix/acceptance
frontend may invoke it serially; it must preserve these limitations and must
not relabel isolated results independent.

## Replay

`loading.py --replay RUN_DIR` recomputes a finished run from its process
receipts and fails on any difference. It checks:

- each receipt against its seal and label (file name, phase, pair,
  selection, rep);
- the order of all processes (pilots, B/B, candidate);
- each `actual_selection` (the baseline launcher in the B/B phase, the
  selection otherwise), the extension enforcement flag and the recorded
  `PERF_LAYOUT`;
- every observation, including extension absence and the stem rule;
- the calibration list, the statistics and control decisions under the
  recorded policy, the jitter of a calibration run, and the control width
  and second-stage count of a decision run;
- the settings of a decision run (exactly `PAIRS` x `REPS`, the develop
  pin, `LAYOUT_SEED`);
- the semantic gate: the receipt's and its inventory's seals, when the
  receipt still exists;
- the launcher of each process: the command, working directory and
  `PAIR_PRIVATE` are the private launcher of the actual side, and
  `LOADING_MODULE` is the run's module;
- for a decision run, the attempts ledger (the checkout's own, or
  `--ledger FILE`, a copy of it): this run is the recorded attempt of its
  stage, its close names this `loading.json` seal and decision, and no
  other judged attempt of the same candidate, module and stage exists. The
  attempt counts are printed.

It prints the exit status the CLI gave and the seal of `loading.json`;
`--expect-seal SHA256` fails unless that seal matches, so the report cannot
be swapped after the seal is recorded. A second stage is replayed against
its first stage (`--first-stage DIR` names it if it moved): the recorded
seal, the first stage's own replay (against the ledger too), the
eligibility rule, the count, the seed, the attempt of the first stage and
the sources must all agree. A report that is not well formed is refused
with a message.

Non-timing regressions (no HOL imports or benchmarks):

```
python3 -B -m unittest discover -s src/simp/tests/performance \
  -p 'test_loading*.py' -v
```
