# TASK18 longer follow-up — 2026-10-22

**Executed, investigated, and archived; no task-completion/parity claim.**
Only the performance subtree changed; no commit. The parent-authorized
exclusive build/measurement window can now be released.

## Answer

The seven GC-slower rows / three control contrasts and the individual
`no_strip_full_complete.0` CPU observation are **not statistically reproduced**
in the predeclared longer campaign. Every longer current GC individual and
66-row family interval, and every independent GC contrast, spans one. None
of the target CPU/wall/non-GC rows has a longer slower interval. This is
unresolved timing, **not demonstrated equality**. In particular, the new
GC intervals still include the original roughly 2–4% effects: failure to
reproduce is not statistical exclusion of those effects. Original observations
remain
valid and visible in `ROWS.md`, `RESULTS.md`, and their unchanged archives.

The concern that these observations demonstrate **stable additional ordinary
algorithm work is not supported by this follow-up**: no stable slower signal
remains, exact staged-work/proof gates pass, and separate dynamic diagnostics
show large adaptive GC-frequency differences without a corresponding increase
in rounded collected nursery volume. This resolves the *repeatability
investigation*, not a universal absence-of-extra-work or cost-parity gate.
Exact allocation equality and historical GC causation are not established.
The filtered campaign changes heap history; it cannot rule out regressions
specific to the original full-matrix environment or other workloads.

## Predeclared execution

See `FOLLOWUP_PLAN.md`, written before measurement, and `run_followup.sh`.
All eight target counts multiplied by **16** in the common
`../followup-iterations.json`; unselected schedule entries unchanged.
**10 alternating fresh AB/BA pairs current, then 10 baseline-control pairs**,
three samples plus calibration. Both launchers built serially before each
campaign's measurements. Then **two fresh AB/BA diagnostic pairs each** current
and control, with GC snapshots outside timers and private-only
`--debug=gc,heapsize`. No diagnostic timings mixed into inference.

The explicit row filter preserves selected order and every selected batch's
protocol, exact construction/application/reconstruction counts, consumption,
full hypotheses, ordered residuals, genuine kernel proofs and oracle checks.
All original workloads for each scenario are constructed; unselected batch
execution is skipped. Thus retained fixtures are preserved but preceding
adaptive heap-policy history differs. No samples/rows/early attempts removed.
The family correction stays **66**, not eight. Independent control contrasts
remain separate; no zero replacement, outlier deletion, or acceptance budget.

Current sampled wall min/median/max: **0.963323 / 1.210765 / 1.395841 s**.
Control: **0.954458 / 1.218812 / 1.385711 s**. Calibration minima 0.926776 /
0.943450 s. All 1,280 ordinary calibration/sample batches pass; 960 samples.
Host load was nonzero/variable (one-minute load roughly 6.3–17.8 at campaign
boundaries), despite exclusive HOL build/benchmark authorization. These are
shared-dependency/private-source runs, not independently clean-built trees.

## Repeatability

GC ratios are geometric means of paired process-sample-median ratios.
Original seven rows were family-slower; original contrasts marked `*` were
also family-slower. All longer current and contrast GC individual/family
intervals are unresolved; all pair ratios are retained in `FOLLOWUP_ROWS.md`.

| Key | Original GC | Longer GC | Longer control GC |
| --- | ---: | ---: | ---: |
| full_complete.0 | 1.022645 | 0.944502 | 0.953532 |
| rev_complete.0 * | 1.039658 | 0.947445 | 1.059886 |
| simp_complete.8 | 1.029387 | 0.949749 | 0.988858 |
| rev_reuse.8 | 1.037449 | 0.998383 | 0.823093 |
| no_strip_full_reuse.8 * | 1.042695 | 1.008437 | 1.000339 |
| no_strip_full_complete.8 | 1.033184 | 0.935765 | 0.925435 |
| no_strip_rev_reuse.8 * | 1.041467 | 0.906046 | 0.907930 |

Each target's longer-current GC pair ratios occur on both sides of one.
Even the unchanged-source control has individually resolved faster GC for
`rev_reuse.8`; no control GC family interval resolves. Do not use that faster
observation to cancel another row's slower observation.

`no_strip_full_complete.0` CPU: original **1.013473**, individual
[1.001039, 1.026062]; longer **1.007597**, [0.986327, 1.029326], family
[0.961350, 1.056070]; control **0.997746**. Longer independent contrast
individual [0.984607, 1.035789]. Its non-GC CPU ratio is 1.004247,
individual [0.995143, 1.013434]. The positive point estimate remains visible,
not interpreted as proven extra work or proven parity. Longer `simp_complete.8`
CPU/wall/non-GC are individually faster (including contrasts), but family
intervals remain unresolved. No all-row speedup/parity claim follows.

## Dynamic GC, work and retained environment

Adapted TASK17's maintained `gc_trace.py`, `GCTracePerformance.sml` and
`gc_summary.py` approach: the same 10 statistics fields, separate debug
processes, and cumulative full/partial counters map logs to batch boundaries.
Full-process log totals match the last snapshot for **all eight** diagnostic
processes; exact stage/consumption/proof gates pass in diagnostics too.

- A full GC does **not** reset adaptive nursery-policy history. In the first
  current-baseline process, identical `full_complete.0` sampled batches have
  **48,104,141 partial GCs**, with nursery-capacity ranges **48–95,22–44,
  13–35 MiB**, despite a full GC immediately before each batch. Candidate:
  **48,104,173** partial GCs, the last range **11–52 MiB**. Logs explicitly
  adjust allocation areas, e.g. baseline's first sampled collection
  **47.35→94.69 MiB**. Rounded collected-nursery sums remain about **4.4 GiB**
  per sample, rather than tripling with the collection count.
- Aggregate two-pair sampled current counts for `rev_complete.0`:
  baseline **2 full / 845 partial**, candidate **3 / 739**; rounded nursery
  sums **27,350 / 27,287 MiB**. `no_strip_full_reuse.8`: **2 / 840 → 5 / 913**,
  but nursery sums **34,229 / 34,224 MiB**. Thus additional collections in a
  diagnostic row do not establish additional algorithm allocation/work.
- The **unchanged-source control** also differs substantially:
  `rev_complete.0` **4 / 844 → 2 / 583**, nursery sums
  **27,315 / 27,193 MiB**; `no_strip_full_complete.8` **3 / 802 → 4 / 652**,
  sums **34,368 / 34,306 MiB**. This directly measures runtime-policy
  variability; it is not an assumed source-based noise exemption.
- Across current diagnostic target rows, six-sample nursery sums differ by
  at most about **0.24%** candidate versus baseline. **These are not exact
  allocation totals**: rounded logs omit the uncollected final tail, include
  a small pre-timer prefix and diagnostic overhead, and are separate from
  the inference campaign. They support comparable large allocation volume,
  not a bound on an allocation regression. `sizeAllocationFree` is GC-updated;
  it is never subtracted as a cumulative allocated-byte counter.
- Candidate's occupied heap after the preceding full GC is consistently
  **27,456–27,544 bytes larger** at the first sampled batch of these rows
  (about 8.7 MiB baseline live heap). This is real retained-environment
  difference, **not equality**, and is the opposite direction from TASK17's
  large exclusion fixtures. Control deltas are −352 to −416 bytes. Actual
  loaded paths show candidate additionally loads **SimpTracking.sig/.sml**;
  no extension engine or extension tactic is loaded by these ordinary runs.
  `Cond_rewr` now aliases the relocated tracking implementation. Module-load /
  namespace/closure retention is a plausible source of the constant offset,
  but the trace does not isolate its exact object-level cause. We do not
  attribute the entire difference to smaller closures or claim a production
  memory fix. Recorded code-region size is 888,832 bytes on both sides.
- Longer default-timing GC CPU share is much larger than in short original
  batches: sample medians about **6.65% baseline / 6.57% candidate**, versus
  roughly half a percent originally. This, plus strongly changing collection
  counts, demonstrates that 16× execution and filtered history alter GC
  exposure. The earlier tiny absolute GC share was not used to waive it.

Prior entire-source/local-native correspondence remains useful **only as a
local staging argument**. It is not substituted for the dynamic evidence.
The inspected runtime environment is measurably different; no stable added
ordinary-work signal survives the independent longer experiment. There is
no remaining reproducible slower interval here requiring a speculative
production fix. Parent retains TASK18/whole-plan acceptance ownership.

## Evidence, recheck, cleanup

- `FOLLOWUP_ROWS.md`: all eight rows, all six metrics, original/current/control
  individual/family intervals, independent contrasts, durations and raw ratios.
- `followup-receipts.tar.xz`, `followup-index.json.gz`: all 48 fresh-process
  receipts, eight build receipts, manifests and exact full inference; lossless
  recovery verifies original compressed receipt hashes.
- `followup-sources.tar.xz`: unique new sealed inputs; unchanged selected/input
  blobs are referenced in the original `sources.tar.xz`, not copied again.
- `followup-diagnostic.json.gz`: every sampled diagnostic counter/snapshot,
  collection counts, nursery summaries and selected exact adjustment records.
  Full raw GC/heap logs remain in archived process receipts.
- `followup-recheck.log`, `followup-checks.log`, `FOLLOWUP_SHA256SUMS`:
  reproducibility checks. A postprocessing exponent-format fix and JSON
  tuple/list normalization affected only offline reporting; no measurement
  attempt failed or was removed.

```sh
P=src/simp/tests/tactics/performance
python3 -B "$P/evidence/followup.py" --archive
python3 -B "$P/evidence/followup_report.py"
python3 -B "$P/evidence/recheck.py"
python3 -B -m unittest discover -s "$P" -p 'test_*.py'
python3 -B -m unittest discover -s "$P/assembly" -p 'test_*.py'
tools/h4pedant/h4pedant "$P"
(cd "$P/evidence" && sha256sum -c SHA256SUMS &&
  sha256sum -c FOLLOWUP_SHA256SUMS)
```

Private build trees removed automatically. Unpacked campaign duplicates and
analysis removed only after archived byte/protocol/inference recheck. No
agent-created heaps, executables, copied trees or caches retained.
