# TASK17 GC follow-up — 2026-10-22

**Finished; exclusive build/measurement window released. No commit.**
Only new local files under `src/simp/tests/exclusions/performance/` were
created during the measurement follow-up. Subsequent offline compaction
relocated duplicate codegen/exploratory files and refreshed archive reports
and checksums; final timing/GC receipts, analyses and collection manifests
remain unchanged. Pre-compaction inventories are retained separately.

## Exact conclusion

The original four GC-slower intervals remain valid observations of that
campaign, **not waived or replaced**. They do not reproduce as a stable
four-row slowdown in fresh, 16-times-longer batches. Direct collection counts
and a separate heap trace show that default adaptive allocation-area sizing
changes GC frequency substantially even at identical operation counts.
Candidate live heap is smaller, not identical to baseline. Unchanged ordinary
source/native bodies therefore do not imply identical GC costs.

There is no demonstrated added deletion/replay algorithm work: the prior
whole-source/native correspondence stands, and exact maker/collector counts,
proofs, names, persistence and result consumption pass again. This is **not**
a claim of runtime parity, exact cumulative-allocation equality, or a proof
that smaller COND_REWR closures alone caused every historical timing delta.
No production change or flag is proposed. No whole-plan gate was attempted.

## Fresh reproduction

Current then baseline-vs-baseline control: **four alternating fresh AB/BA
pairs each**, three samples plus calibration. Both launchers finish building
before measurement. The full original 44-key matrix/order/preparation and
checks remain; only `replay.1000`, `missing.10000`, `matching.10000` and
`qualified.10000` have iteration counts multiplied by 16, identically on
both sides and in control (`../gc-iterations.json`). This preserves matrix
context rather than comparing newly isolated, differently retained inputs.

Target sampled wall batches: current min/median/max
**2.137146 / 3.017907 / 4.285520 s**; control
**2.187126 / 2.983684 / 3.639347 s**. Nothing discarded. Statistics snapshots
bracket the timer outside it; pre-batch full GC and verification are untimed.
Default heap policy and the existing one-GC-thread setting are unchanged.

Ratios below are geometric means of paired process-sample-median GC ratios.
Counts sum all **12 sampled batches per side**, excluding calibration and
untimed full GCs. `F` = full; `P` = partial/minor.

| Key | Original final GC ratio | Longer current | Longer control | Current counts baseline -> candidate |
| --- | ---: | ---: | ---: | --- |
| replay.1000 | 1.203343 | 1.071002 | 0.956502 | F 0->0; P 218->221 |
| missing.10000 | 1.222414 | 0.842539 | 1.115986 | F 2->0; P 231->207 |
| matching.10000 | 1.328003 | 0.805009 | 1.060463 | F 6->6; P 518->456 |
| qualified.10000 | 1.068908 | 1.075881 | 1.200019 | F 0->0; P 151->192 |

Each longer-current key has both above- and below-one pair ratios. All four
individual 95% intervals span one; at four pairs these are deliberately
bounded diagnostics, **not an acceptance test**. In particular, qualified's
point ratio remains similar to its old ratio, but varies across pairs from
0.800 to 1.685, while unchanged-source control reaches 1.200 geometrically.
Total-CPU point ratios also vary (0.968908, 1.057665, 1.050260, 1.055940 in
table order); no total-time parity conclusion follows. Host load remained
nonzero/variable despite the exclusive HOL build/benchmark window.

## What the counters/trace explain

- In default long-current baseline, replay's identical 2,048-operation
  samples have minor counts **11,14,23** in pair 0, despite an untimed full GC
  before each. Candidate has **11,17,27**. A full GC is not a reset of adaptive
  heap-policy history.
- A **separate fresh pair** with private-only `--debug=gc,heapsize` records
  heap policy, not inference-quality timings. Replay baseline's three sample
  nursery-occupancy ranges are **437–872, 250–498, 144–285 MiB**, with **11,
  19,35** minor collections. Candidate: **407–812,326–649,235–468 MiB**,
  **11,14,20** collections. The log explicitly records allocation-area
  adjustments, e.g. **436.62->871.39 MiB** versus **143.10->284.50 MiB** on
  baseline's first collections in samples 0 and 2. Missing's baseline nursery
  ranges reach **1.04 GiB**; qualified reaches **1.32 GiB**.
- Trace events are mapped to sample boundaries using cumulative full/partial
  counters. Full-process log totals match the final statistics counters
  exactly on both sides. Raw trace diagnostics and selected adjustments are
  retained. Debug results are **not mixed** into the default-policy ratios.
- Post-full-GC occupied heap (`sizeHeap-sizeHeapFreeLastFullGC`) is smaller
  on candidate in all four pairs: replay first samples by **9,008–10,736
  bytes**; the three 10,000-rule target rows by **307,504–623,584 bytes**.
  This is direct retained-heap evidence compatible with changed closure
  storage/shared tracking, not a counterfactual isolation of that change.
- Allocation statistics need care: `sizeAllocationFree` is GC-updated, not
  a cumulative bytes-allocated counter (a no-GC allocation probe leaves it
  unchanged). Do **not** subtract endpoint values to claim allocation totals.
  The trace's rounded filled-nursery sums are about **8.3–9.9 GiB per target
  sample** on both sides, but omit the uncollected final tail (up to roughly
  a GiB) and include the first nursery's small pre-timer prefix. They establish
  substantial allocation with dynamically changing collection frequency,
  **not exact equality or an allocation regression estimate**.
- Original final baseline median GC cost was only **0.81–1.05%** of total
  CPU. Median-of-process-median GC differences were **2.609,2.375,3.346,
  0.584 microseconds/operation** in table order, about **0.158,0.235,0.339,
  0.054 percentage points** of baseline total CPU. Large relative GC ratios
  thus need not yield resolved total-CPU intervals. These are descriptive
  original-receipt calculations, not a reason to erase their GC intervals.

## Evidence / rerun

New only:
- `gc-long-current/`, `gc-long-control/`: 16 accepted fresh-process receipts;
  manifests contain commands, source/product/fixture seals and environments.
- `gc-trace-current/`: two accepted diagnostic receipts and GC/heap logs;
  same schedule; only these private launchers add debug logging.
- `gc-diagnostic-summary.json.gz`: every target sample's raw counters,
  snapshots, CPU/GC/wall data, paired ratios and selected trace records.
- `../gc_run.py`, `../GCPerformance.sml`, `../gc-iterations.json`;
  `../gc_trace.py`, `../GCTracePerformance.sml`; `../gc_summary.py`.
- `gc-checks.log`, `GC_SHA256SUMS` (new follow-up files only).
  `gc-checks-wrong-cwd.log` retains an initial checksum invocation from the
  wrong directory; rerunning from the performance directory passes all
  original checksum entries. No measurement was affected.

Offline recheck/regenerate diagnostic summary:

```
python3 -B src/simp/tests/exclusions/performance/gc_summary.py
python3 -B src/simp/tests/exclusions/performance/evidence/recheck.py
```

The updated recheck verifies all 40 final and 20 exploratory timing receipts,
exact final analysis, both losslessly compacted codegen archives and all 18 GC
diagnostic receipts. Current `SHA256SUMS` and `GC_SHA256SUMS` check physical
files; their originals survive in `previous-inventories.json.gz`. Existing 13
offline performance tests pass. Private build trees/heaps were automatically
removed after each campaign. No agent cache, copied build tree or launcher
remains.
