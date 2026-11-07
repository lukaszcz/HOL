# TASK28 fresh ordinary STARTUP timing

`loading.py` measures first ordinary import, not steady-state simplification,
not process creation, and not independent-build/release acceptance. It reuses
`compatibility/run_paired.py` extraction, fixture bootstrap, trace validation,
and path/source fingerprinting. No production code is instrumented.

## Invocation

Stop unrelated builds, HOL processes and performance runners first. The serial
frontend takes the same host-wide and git-directory advisory locks as
`acceptance.py`; child processes inherit them. Explicit authorization is needed
for even a smoke run. Do not run concurrently with builds or telemetry probes.

```
python3 src/simp/tests/performance/loading.py \
  --baseline BASELINE_FULL_COMMIT --candidate CANDIDATE_FULL_COMMIT \
  --module simpLib --pairs 10 \
  --api-audit /absolute/path/to/api-audit/evidence/RUN/receipt.json \
  --authorize-measurements --output /absolute/path/to/new-loading-simp
```

Repeat with `--module congLib` and a different output directory. Each imports
from a fresh `hol.state0` process. The congLib case includes its ordinary
simpLib dependency; this is **not** congLib marginal cost after simpLib.
Separate results must not be added together as a two-import estimate.
Only full immutable commit IDs are accepted. Worktree edits are not selected
implementation sources. Output directories must not already exist.

An explicitly non-acceptance protocol smoke is available with `--smoke
--pairs 1`; the API audit receipt may be omitted only in this mode. All
receipts/report labels then say smoke; no confidence interval is produced.
Do not use a smoke run as performance evidence.

## Timed boundary and proof check

The generated private runner is based on `paired/runner.sml`. Only runner.uo
is linked; proof selftest dependency metadata is built, not linked. The runner
records the initial heap/map, activates exactly private-first plus shared
sigobj search paths, and dynamically loads CheckSupport before timing. Neither
ordinary library may already be present. There are no static simplifier
references in the runner or its linked dependencies.

The timer wraps the **actual** `Meta.loadPlan tracedUse module` call, including
source elaboration, transitive dependencies, ordinary initialization and trace
I/O. Each traced source must have a matching completion; the target's completed
source must be inside `loading.begin`/`loading.end`. A traced selftest cannot
encapsulate this operation: that would produce nested pending `use` events,
which the original fail-closed validator intentionally rejects.

After the timer stops, the proof selftest is dynamically loaded. It consumes a
real `simpLib.SIMP_CONV` result, checking the exact closed kernel equality
`(T /\ p) = p` and absence of hypotheses. The congLib fixture also checks the
corresponding `CONGRUENCE_EQ_SIMP_CONV` result. Additional proof-only
dependencies, including pureSimps, are outside the timer. Missing checks,
observations, source completion, final inventory or exact successful exit
reject the process.
The full initial/final map and actual paths/hashes are retained per process.

## Calibration and design

There is no same-process repeated import: Meta would cache the module and
measure a no-op. Instead every pilot and measurement starts a new executable
process. Before each import the runner measures forced-GC timer accounting and
an empty bracket. Raw fields, in order, are:

```
wall,nongc_usr,nongc_sys,gc_usr,gc_sys,cpu_usr,cpu_sys,gc_user_only
```

`cpu_usr/sys` include GC. `gc_user_only` is `Timer.checkGCTime`, **not** total
GC CPU and must not be added to inclusive CPU. Sequential snapshots are checked
for agreement within 0.02s. Reported metrics are wall, inclusive CPU, and GC
CPU (`gc_usr+gc_sys`). Process-launch wall time is archived separately; it is
not an import metric. All fields must be finite and nonnegative. The
forced-GC control must additionally show positive GC CPU and positive GC-user
time; an all-zero or otherwise vacuous control rejects the process. Zero GC
in the actual import is allowed after that positive accounting control, but
undefined paired GC ratios remain inconclusive.

One pilot per selected revision precedes measurements. Each pilot and each
measured import must exceed 100 times both its own empty-bracket overhead and
the nominal 1us time representation granularity, for wall and inclusive CPU.
Failure gives an inconclusive measurement, not batching or dropped samples.
The forced-GC bracket checks accounting; it is not import latency. This is
warm-filesystem, fresh-runtime loading, not a cold-cache or cold-machine claim.

Both baseline/baseline controls and baseline/candidate comparisons are
mandatory. Each has at least ten fresh process pairs. Pair 0 is AB, pair 1 BA,
and so on. In the B/B phase both labels execute the same private baseline
launcher, but remain distinct fresh processes. Pilots are excluded from paired
statistics. No sample/outlier is removed. Controls are never subtracted as a
noise budget. A failed or uncertain control prevents a candidate pass,
while a reproducible candidate slowdown remains a failure.

Statistics reuse `acceptance.paired_statistics`: median paired candidate /
baseline ratios, deterministic 20,000-resample paired bootstrap, 95% interval.
Strict rule: lower bound >1 fails; upper bound <=1 passes; otherwise
inconclusive. Any zero denominator (including zero GC / zero GC) is
inconclusive without dropping pairs. `success` means protocol completion,
**not** that performance passed; inspect every candidate metric decision.
CLI exits are 0 only when all reported candidate metrics pass (or explicit
smoke completes), 1 for any reproducible failure, and 2 for inconclusive or
blocked protocol/measurement results.

## Separate eight-process semantic gate

Ordinary initialization callbacks, foreign registry ownership, exact listener
identities and absence of extension modules are already checked by
`api-audit/run.py` in eight fresh processes (both import orders, attribute /
exporter ownership, installation before / after). Timing does not replace this
gate. A non-smoke run requires its successful receipt, eight distinct cases,
sealed logs and actual-files inventory, source-sealed gate fixtures, exact
process exits/check counts and final observations. The actual native ordinary
and extension imports must match the selected candidate git bytes. The gate
need not share the same commit label when irrelevant files changed, but the
loaded simplifier bytes must match. Historical baseline semantics are not
required to satisfy the candidate's extension split.

The audit can be run beforehand, outside the timing window:

```
bin/Holmake --holstate=$PWD/bin/hol.state0 \
  -C src/simp/tests/api-audit check
```

Use that run's unique receipt. Old evidence for different source bytes is
rejected. This is an external semantic gate ledger, not timing instrumentation
inside the semantic audit and not a claim that the audit ran on the baseline.

## Provenance and failures

`loading.json` (`task28-loading-v2`) records exact revisions and immutable
extracted source/git-blob seals,
private generated fixtures/products, launcher text/options, interpreter/runtime
versions and hashes, environment, calibration, ordered runs, shared actual
source/product seals, paired statistics, and gate identity. Git extraction
seals remain authoritative through fixture installation, builds, actual source
validation and the final unchanged-input check. Generated fixtures are sealed
before building too. Post-build product hashes cannot replace either input
seal; a build that changes even an unloaded selected signature is rejected.

On supported Linux dynamic runtimes, `ldd` discovers the libraries linked by
**the actual `bin/hol`**, not PATH's `poly`. Discovery runs with the sanitized
launch environment, timeout and inherited serial locks. Its command, output,
exit and timeout are archived. Every file-backed dependency, including the
loader, has a logical path, resolved target and content seal; the kernel VDSO
is not a file. These hashes are included in `inputs`. Missing libraries,
partial/unresolved output, failed/empty discovery and unsupported discovery
formats block the run, rather than admitting a partial runtime inventory.
Before success the original file seals are rechecked and discovery is repeated;
changed mappings or same-byte symlink retargeting also reject. ASLR addresses
are not identities. PATH's `poly -v` is separately archived compiler
provenance, queried under the same environment/timeout; it is not proof of
HOL's linked runtime version. This is local consistency checking, not hostile
producer authentication or protection against concurrent changes restored
between checks.

Compressed unique
process receipts retain raw output, complete ordered protocol and actual loaded
paths. Inputs are checked again before success; shared actual inputs remain
identical across processes. Processes use one GC thread. Timeouts kill/reap the
whole process group; an absent launcher, timeout, nonzero exit, wrong path,
mutated source or incomplete output cannot count as a successful sample.
Private build trees are automatically removed after their final use. Failed
runs retain compact diagnostic receipts and a failure report, never a success
inferred from .uo creation.

This harness intentionally uses one existing shared heap and dependency tree,
with isolated selected simplifier sources. It does **not** satisfy the separate
clean independent baseline/candidate build gate or close overall TASK28
acceptance. The main matrix/acceptance frontend may invoke it serially; it must
preserve these limitations and must not relabel isolated results independent.

Non-timing regressions (no HOL imports or benchmarks):

```
python3 -B -m unittest discover -s src/simp/tests/performance \
  -p 'test_loading*.py' -v
```

## Amendment 2026-11-07 (TASK31 gate 4): equivalence margin and loading unit

The text above is kept as the TASK28 history. Where it conflicts, this
amendment governs the `task31-loading-v3` schema; older `task28-loading-v2`
archives keep their recorded zero-margin policy and are not replayed here.

### Decision policy: the timing grid's, from one place

TASK28 loading was inconclusive because the zero-margin rule asked a
~1 s process to resolve 0%. The decision now uses
`acceptance.EQUIVALENCE_POLICY` itself (`loading.POLICY` is that object, never
a copy of its constants), exactly as `timing_grid.py` does:

- 3% margin on inclusive CPU and wall (`gated_timing`); GC CPU is reported,
  not gated (inclusive CPU already contains GC time).
- Per metric `a.timing_rule` gives `(margin, gated)`; `a.paired_statistics`
  gives the median paired candidate/baseline ratio and the 20000-resample
  bootstrap interval; `low > 1.03` fails, `high <= 1.03` passes, else
  inconclusive.
- `a.apply_control` applies the B/B control as the grid does: the control's
  whole interval must lie in `[1/1.03, 1.03]`; otherwise the comparison is
  not admissible and a non-fail becomes inconclusive ("baseline-control
  outside equivalence window"). A candidate fail is never excused.
- Exit status: 0 only if every gated metric passes, 1 on any fail, 2
  otherwise. `reported` metrics do not affect it.
- The pair count is read the grid's way: `pairs_for_target` in the report is
  `pairs * (control half log-width / timing_grid.TARGET)^2`, rounded up to
  tens (`TARGET` = 0.015, half the margin). It is computed from the control
  interval only and is advice for a rerun; the run never changes its own
  count.

### Unit: more fresh processes per sample, never repeated loads

A module is imported once per process (a second load measures a cache hit).
The unit is lengthened by `--reps R`: each side of a pair is R fresh
processes, interleaved (`A B A B ...` in AB pairs, `B A B A ...` in BA
pairs), and the sample is the **mean** of the R first imports of that side
(no sample removed). `schedule(pairs, reps)` is the order; `plan` is its
`reps = 1` case. Every process keeps the fresh-process contract, pilots
included, and every one is archived (`phase-pair-side-rep`).

### Calibration and the derived counts

`--calibrate` runs the two pilots and the B/B phase only (no candidate, no
audit receipt, not evidence) and reports per metric the sample log
standard deviation and the grid's `pairs_for_target`.

Model: a single import has log standard deviation s1, so the paired log
ratio of two R-means has `sd = sqrt(2/R) * s1`; the 95% interval half width
of the median of n ratios is about `1.96 * 1.2533 * sd / sqrt(n)`. Requiring
it to be at most `TARGET`:

    n * R  >=  (1.96 * 1.2533 * sqrt(2) * s1 / 0.015)^2  =  (231.6 * s1)^2

Calibration on 2026-11-07 (develop baseline against itself, shared host,
`--repo` = the t31-src build, scratch only):

| library | R | pairs | median import | s1 (log sd) | sd of paired log ratio | B/B 95% interval (wall) |
|---|---|---|---|---|---|---|
| simpLib | 1 | 20 | 0.875 s | 0.0205 | 0.033 | [0.9814, 1.0088] |
| congLib | 1 | 20 | 1.161 s | 0.0093 | 0.013 | [0.9951, 1.0086] |
| simpLib | 3 | 12 | 0.863 s | 0.0109 | 0.012 | [0.9903, 1.0064] |
| congLib | 3 | 12 | 1.162 s | 0.0204 | 0.031 | [0.9989, 1.0061] |

The worst per-unit spread is the congLib R=3 run: `0.0314 * sqrt(3) = 0.054`
(equivalently s1 = 0.038, heavier-tailed than the iid model), so
`n * R >= (2.457 * 0.054 / 0.015)^2 = 78`. The constants keep a factor of
2.5 over that. TASK28's reported 10-30% jitter on a busier host would need
`n * R` of 540 and up and is not covered; it would end inconclusive:

    R = 5, n = 40 pairs  ->  n * R = 200  (covers a unit spread up to 0.061)

`--pairs 40 --reps 5` are the acceptance floor (`loading.PAIRS`,
`loading.REPS`; smaller values only with `--smoke` or `--calibrate`). If the
host is noisier, B/B is wide, the comparison is inconclusive by the rule
above and `pairs_for_target` says by how much. A larger R also averages out
slow drift inside a pair.

Cost per library: 2 pilots + 2 phases * 2 sides * 40 * 5 = 802 processes at
about 1.2 s (simpLib) and 1.7 s (congLib) each, i.e. about 16 and 23
minutes plus two builds: well under an hour for both, inside the 2 h target.

### Extension absence in every process

After the timed import, and outside the timer, the runner emits
`loading.extensions`: the names (in order of first occurrence, `none` if empty)
of every loaded module (`Meta.loaded`), file in the final file map, or
structure bound in the global name space that is an extension: `*Ext`,
`*ExtLib`, `simpMarker*`, `SimpTracking`, `trackedSimpDefaults`, `SplitData`,
`splitLib`, `splitPersistLib` and the API audit's other forbidden names
(`EXTENSION_NAMES`; extension caches are the persistence modules in that
list). The validator additionally scans the used, heap and final file paths.
The assertion is enforced for processes that run the **candidate** and is
recorded, never rejected, for the historical baseline, which need not satisfy
the split. A candidate process with a loaded extension is rejected, which
stops the run.

### Receipt binding and replay

Non-smoke runs still require the fresh eight-process API-audit receipt
(`bin/Holmake -C src/simp/tests/api-audit check`) bound to the candidate's
git bytes; `--calibrate` does not. `loading.py --replay RUN_DIR` recomputes
every observation (including extension absence) from the sealed process
receipts, rebuilds the statistics and control decisions under the recorded
policy, and fails on any difference; with a decision run it prints the exit
status the CLI gave.
