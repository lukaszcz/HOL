# TASK29 — fragment/compiler/storage isolated gate

## Status: BLOCKED, not complete

### Executed allocator-profiler falsification (after `70d82d40e`)

TASK29 is **not complete**. A fresh full-grid offline replay re-admits all
162 archives/6,480 timed receipts and reproduces the original **43 failed /
119 inconclusive cells**, exit **2**. The equal-count archive replay also
passes admission and reproduces collector CPU **[1.032421, 1.052741]**, wall
**[1.032385, 1.052508]**, both failures. These are replays, not new performance
observations or a replacement grid. No production repair has been justified.

The proposed `ProfileAllocations` shortcut is now falsified by execution on
HOL's **actual linked** libpolyml, not just inspection of potentially different
Isabelle sources. New `allocation_profiler_probe.py` and the private
`allocator-probe/selftest.sml`/C++ shim inject synthetic unknown-PC profiler
events through the binary's exported private symbol. Admission requires the
exact reviewed Linux/aarch64 library hash before compiling/loading the shim.
The launcher is Holmake-built and executed with testutils and `hol.state0`.

One synthetic event requesting 1 word and one requesting 1048576 words both
produce `UNKNOWN=1`; seven large requests produce `UNKNOWN=7`, including after
full GC. Empty/reset controls give zero. All **six cases / five assertions**
pass. The preserved installed-symbol disassembly independently shows literal
`+1` on that path. These are **profiler arguments, not actual allocations**;
the shim does not allocate the requested memory. Displayed totals include
bracket costs and are not relabelled allocation. Summing profiler entries
cannot recover lost word counts. This does not prove real workload incidence,
solve other coverage gaps, or supply TASK29B's counter.

`ALLOCATION_PROFILER.md` documents the optional explicit
`profiler-loss-control` Holmake target, private-ABI limits and reproducible
command. Eight Python regression tests cover exact binary admission, explicit
authorization, all expected counts and missing/duplicate/reordered/malformed
or semantically changed observations. No threshold, zero-GC policy, B/B policy,
workload, ordinary API, extension, tracking identity or production source
changed. No profiler runs inside an acceptance timing process.

New durable evidence: `evidence/task29/profiler-loss/`:

- `receipt.json.gz`: final six-case runtime control, all commands/exits,
  source/heap/tool/library seals, loaded-library discovery, native disassembly,
  generated-shim/launcher seals and all outputs. `development.json.gz` retains
  the preliminary diagnostic before final tool/copied-input guards.
- `grid-replay.log.gz`: all 162 cells replayed, exit **2** (blocked).
- `equal-count-replay.json.gz`: complete fresh recomputation, exit **0**,
  preserving the collector failures and zero-GC/short-count controls.
- `performance-tests.log.gz`: **263 tests**, two unchanged optional skips,
  exit **0**; `compatibility-tests.log.gz`: **196 tests**, exit **0**.
- `routine.log.gz`: fresh
  `bin/build -t --seq=tools/sequences/upto-parallel`, exit **0**, after the
  diagnostic. Fresh eight-process API receipt:
  `../api-audit/evidence/20261024T040100Z-dacf103f/receipt.json`.
  This is not a final-build-product performance parity claim.
- `validation.json`: commands, statuses, source/evidence seals and exact
  outstanding counts. Pedant and whitespace checks pass.

Commands from repository root, using the existing `W` wrapper below:

```sh
W bin/Holmake --no-project --no-cache --no_prereqs \
  --holstate=CONFIGURED_ROOT/bin/hol.state0 \
  -C src/simp/tests/performance -j1 \
  PERFORMANCE_CHECK_OUTPUT=NEW_DIRECTORY profiler-loss-control
# exit 0: diagnostic reproduced, NOT allocation acceptance
python3 -B src/simp/tests/performance/task29_gate.py replay \
  --output src/simp/tests/performance/evidence/task29/full-grid
# exit 2: complete replay, gate still blocked
python3 -B src/simp/tests/performance/evidence/task29/equal-count/replay.py
# exit 0: original failures reproduced
```

TASK29B still requires a reviewed complete counter, with allocation/no-allocation
and GC controls, and the full paired allocation matrix. The ratio-only 0/0
and equality-straddling B/B policy issues below also remain; silently changing
those gates would violate this task. TASK29A is still the next unblocked work.
All task-created private source/build/DSO trees and scratch outputs were removed
after preserving compact evidence. Caller-owned review files, caches and
pre-existing nested planning changes were preserved. No completion-log line
is warranted for TASK29, TASK29A or TASK29B.

### Equal-count investigation (after `e86df07bf`)

TASK29 is **still blocked**. The complete original grid below is preserved;
no failure or uncertain cell is replaced by this targeted diagnostic. TASK29A
is in progress, not complete; TASK29B remains blocked. No production source,
public simplifier API, representation, control identity or extension changed.

A concrete measurement confound was reproduced from the sealed archives:
`compile_collector/10000` chose **32 baseline versus 16 candidate iterations**
in every B/C pair. B/B also chose both counts. Normalizing time per operation
cannot remove nonlinear collection/heap-sizing effects. The new
`--batch-iterations N` option fixes the full doubling history and sample count
identically across both selections and B/B versus B/C. It does **not** fix
heap state or claim identical collections. It is optional for old-archive
replay; the historical default and all numerical thresholds remain unchanged.
A short fixed calibration rejects rather than silently recalibrating one side.
Manifest, requested count, environment, observations, consumption and source
bindings are checked online and offline.

A **predeclared N=64** complete local experiment (twice the largest original
collector count, chosen before its new observations) ran ten fresh B/B and ten
fresh B/C alternating pairs, three samples, 0.3-second target. All **40 timed
processes / 120 samples** pass semantic, callback, source/path and runtime
admission. Every process calibrates 1/2/4/8/16/32/64 and samples at 64.
The candidate remains slower:

| Metric | B/B 95% ratio interval | B/C 95% ratio interval | Gate |
| --- | --- | --- | --- |
| CPU | [0.990465, 1.016269] | **[1.032421, 1.052741]** | fail |
| Wall | [0.990407, 1.016490] | **[1.032385, 1.052508]** | fail |
| GC | [0.818452, 1.100784] | [0.810305, 1.311080] | inconclusive |

This removes unequal counts **without closing the regression**. The difference
from the original interval is not attributed solely to iteration counts;
these are separate experiments, not control-subtracted estimates. Load averages
changed during the run (recorded raw); the cooperating-runner lock establishes
serialization, not host exclusivity or a causal noise explanation. No sample,
pair, metric, original grid cell or outlier was dropped.

New durable evidence: `evidence/task29/equal-count/`:

- `collector-10000.json.xz`: lossless complete ten-pair B/B and B/C experiment;
  actual runner commands, loaded paths, tools/libraries, proofs, callbacks,
  raw observations, heaps, GC counts, ratios and unrounded intervals.
- `client-smoke.json.xz`: two real client-fixture processes with the common
  1..1048576 history/count; protocol/semantic smoke only, not acceptance.
- `short-negative.json.xz`: real count=1 collector experiment exits nonzero;
  independently replayed rejection is `fixed calibration too short; new
  experiment required`. No rejected observation is counted in the above run.
- `replay.py` / `replay.json.gz`: freshly re-admit both original collector and
  zero-rule single-addition archives, re-admit all 40 equal-count processes,
  recompute unchanged strict statistics/controls, audit both client processes,
  and reproduce the actual short-count rejection. All three new bundles also
  roundtrip byte-for-byte (57/9/8 files) before removing scratch trees.
- `validation.json`: source/evidence seals, commands and exits. Fresh performance
  discovery: **255 tests**, two unchanged optional skips; compatibility:
  **196 tests**; routine `bin/build -t --seq=tools/sequences/upto-parallel`:
  **exit 0**. Eight new fixed-mode tests cover dispatch, both experiment counts,
  early time-target crossings, calibration history, durations, consumption,
  invalid types/bounds, environment/archive/request mismatches and CLI misuse.
  Routine build follows the experiment; no final-build-product parity claim.
  Its fresh eight-process, 1,374-check API audit is retained at
  `../api-audit/evidence/20261024T031714Z-c5555d9a/receipt.json`.

Commands use `W` as defined below and candidate
`e86df07bf` (full pin in the archive); new evidence outputs must not exist:

```sh
W python3 -B src/simp/tests/performance/acceptance.py run \
  --candidate FULL_E86DF07BF_PIN --case compile_collector --size 10000 \
  --pairs 10 --samples 3 --batch-seconds 0.3 --batch-iterations 64 \
  --timeout 1800 --authorize-measurements --output NEW_DIRECTORY
# exit 1: protocol complete, CPU/wall fail
python3 -B src/simp/tests/performance/evidence/task29/equal-count/replay.py
# exit 0: diagnostics reproduced; explicitly NOT TASK29 approval
```

Two policy/coverage concerns were also made precise, **not waived**:

1. `apply_control` demands B/B's CI upper bound <=1, not merely a sufficiently
   precise measurement of equality. A noisy equal baseline normally has an
   interval straddling 1; this alone does not prove an unstable host. The current
   policy still calls it inconclusive. More repetitions or a quieter machine
   cannot be promised to make every unchanged-baseline control pass. Changing
   that policy requires explicit review; no tolerance or parity shortcut was
   introduced here.
2. Original `compile_single/0` has zero GC in every measured batch on both
   sides; its operation folds an empty list. The ratio-only policy cannot pass
   0/0. No collection was inserted into its timed body to manufacture a ratio.
   Exact zero observations and the original blocked decision are replayed.

Cumulative allocation remains unmeasured. Inspection found the supported
`PolyML.Profiling.ProfileAllocations` interval profiler, but it is **not yet a
validated cumulative total**: per-function extraction can omit unnamed or
reclaimed code, and unknown-PC events need not retain requested-word counts.
It cannot simply replace the missing counter by summing displayed entries.
The local Poly/ML source under Isabelle's `polyml-5.9.2-2` includes later fixes
(commit `ccd3e3717f72`), not proven matching configured libpolyml bytes. No
instrumented runtime was installed, no profiler numbers are claimed, and no
heap-capacity value is relabelled allocated bytes. TASK29B's reviewed,
version-pinned instrument and executed coverage/GC controls remain required.

Changed files: `run_paired.py`, both matrix SML fixtures, `performance_schema.py`,
`acceptance.py`, `audit_evidence.py`, new `test_fixed_batches.py`, protocol and
this handoff, plus narrow equal-count evidence. The optional harness API is
additive; ordinary clients need no migration. All task-created private builds,
unpacked receipts, raw scratch/logs were removed after sealing. Caller-owned
review trees, caches and unrelated nested planning changes remain untouched.
There is **no production performance repair**, full-grid rerun, cumulative
allocation result, TASK29A completion, or TASK29 completion claim.

### Original complete-grid observations

Starting/measured candidate: `18e4a1ecb624b9b13bb9a0f3ba3caf8c189bdff8`.
Develop: `cccaa27d7099cbadc886983020cbe745db7793f3`.
No production SML, signature, build manifest, representation, callback order,
API/control identity or extension capability changed. No compiled-source edit
requires a routine rebuild. This is **source isolation** on the configured
shared heap/dependencies, not independent clean builds or final TASK37 evidence.

All **27 cases × six sizes (0/1/10/100/1000/10000)** were executed. Each of the
162 cells has ten fresh B/B and ten fresh B/C AB/BA process pairs, three
measured batches per process and a 0.3s calibrated target: **6,480 timed fresh
processes / 19,440 measured batches**, plus recorded calibrations. All process,
source/path/runtime, consumption, kernel-proof and exact callback checks pass.
No sample, pair or outlier was removed. All 324 paired runners exit 0; their
numerical decisions are separate. The experiment ran serially over roughly
11 hours, with the host/repository lock held across the complete batch. No
other agent benchmark or build ran concurrently.

**No complete workload/size passes every timing metric.** Forty-three cells
have a timing/GC failure; the other 119 remain inconclusive. Per-metric results:

| Metric | Pass | Fail | Inconclusive |
| --- | ---: | ---: | ---: |
| Inclusive CPU | 1 | 22 | 139 |
| Wall | 1 | 23 | 138 |
| GC | 0 | 31 | 131 |

The CPU/wall passes are `compile_excluded/1` only. B/B controls have respectively
10/8/2 failures and 143/145/159 inconclusive decisions. Two GC ratios are
undefined. These are **not** noise budgets and do not excuse candidate failures.
The existing fixed 20,000-resample paired bootstrap policy is unchanged.

Exact unresolved cases, their metrics, both control and candidate intervals,
raw observations and uncertainty are published in:

- [`evidence/task29/RESULTS.md`](evidence/task29/RESULTS.md): all 162 rows,
  separate CPU/wall/GC and B/B decisions/intervals, including tiny constants.
- `evidence/task29/full-grid/decisions.json`: machine-readable exact blockers,
  every point decision and all adjacent graph-slope decisions.
- `evidence/task29/full-grid/CASE-SIZE.json.xz`: lossless raw receipts,
  calibrations, batches, medians, paired ratios, unrounded intervals, full GC
  counts, RSS/HWM snapshots, input/source/product/runtime/library hashes,
  actual exits and ordered loaded paths. Each archive retains both controls
  and comparison; `inventory.json` seals all 162 archives.

Examples of unresolved CPU intervals (candidate/baseline): `frag_record/0`
**[1.120192, 1.143916]**, `compile_collector/10000`
**[1.174579, 1.232252]**, `storage_graph/10` **[1.044647, 1.085472]**,
`storage_graph/10000` **[1.063493, 1.191384]**. These are failures, not waived
because code is unchanged or graphs are smaller. Construction, merge, complete
operations and ordinary application all have their own rows, not an aggregate.

## Local retained-graph closure (not allocation or overall performance)

Ten control and ten candidate adjacent graph-slope comparisons **all pass**.
All twelve point graph-increment comparisons pass, including size-zero terms.
These are equal-arity reachable graph **words**, not bytes or RSS:

| Rules | Baseline compiled increment | Candidate compiled increment | Fragment increment, both |
| ---: | ---: | ---: | ---: |
| 0 | 21 | 21 | 9 |
| 1 | 4728 | 4728 | 15 |
| 10 | 5446 | 5437 | 69 |
| 100 | 12628 | 12529 | 609 |
| 1000 | 84494 | 83495 | 6009 |
| 10000 | 803165 or 803175 | 793166 | 60009 |

All ten fresh observations per selection are retained, not replaced by this
range table. Fragment slope is exactly six words/rule. Compiled adjacent slopes
are identical for 0→1; thereafter candidate slopes improve by approximately
one word/rule (all corresponding 95% ratio bounds <1). At 1000 rules the graph
reduction is 999 words, consistent with the known removed per-conversion key
capture, not a new optional extension cell.

The no-rule base and simpset roots are **349219 / 349234 words on both sides**;
fragment root is nine words on both sides. The 0→1 compiled increment includes
a 4707-word first-rule step. Do not extrapolate a large-rule linear fit across
that constant step. At 10000 rules raw base/fragment/simpset roots vary across
fresh processes, and one baseline increment differs by ten words; the exact
roots and intervals are retained in `telemetry.json` and original receipts.
The experiment does not identify the cause of this raw-root variability; it
neither discards it nor claims absolute graph identity. Every adjacent
increment comparison, including these observations, passes without filtering.

GC counts/times were measured separately. Snapshot ranges and sample GC counts
for every side/cell are in `evidence/task29/telemetry.json`; all 6,480 timed
processes have actual path evidence excluding simplifier extension modules.
Linux RSS/HWM are approximate **bytes**, not graph words: **18,105 of 19,440**
sample records explicitly block RSS/peak inference after nonmonotonic raw HWM.
Other snapshots remain process-level observations, not exact batch peaks.
The stronger exact-peak/lifetime gates belong to TASK33. The existing controlled
ref-release probe passes in graph processes; no opaque-global-root lifetime
claim is inferred.

**Cumulative HOL allocation remains blocked.** Poly/ML 5.9.2 exposes capacity
and GC-updated free-space fields, not a cumulative allocated-byte counter.
No allocation-per-rule slope is manufactured from them or from Python controls.
A supported/version-pinned allocator instrument is a required input. Structural
reservation-site evidence below is useful but not a measured allocation total.

## Structural work, layouts and constant-size attribution

Fresh `evidence/task29/source-audit.json.gz` reexecutes TASK27's live byte-exact
478-input source/control audit and fresh dependency analyzer on live/reference
snapshots: **231 modules / 446 ordinary defining inputs**, no extension import.
This is a current run of the maintained checker, not a historical pass label.
The six shared-input differences from develop remain explicitly described:
`Cond_rewr.{sml,sig}`, new `SimpTracking.{sml,sig}`, and additive read-only
`ThmAttribute.{sml,sig}` lookups over its original registry.

- **Whole `simpLib.{sml,sig}` is byte-identical to develop.** Fragment creation,
  naming/update/duplicates/merge, AC/TypeBase, empty/excluded additions, compiler
  and complete/application routes use the original bodies.
- Fragment has the original eight fields with ordinary rewrite/AC lists.
  Simpset has seven fields; history its three original constructors; net
  payload is `{thypart,ci}` with `ci={name,conval}`. No source slot/serial,
  origin/inventory, optional configured companion, adapter or discriminator.
- Compilation retains decode-all-tags → AC → all makers → conversions/net
  insertion → existing collectors. The direct ordinary conditional compiler
  does not prepare and discard a configured runner.
- Shared tracking is one extracted original TLS extent, not a second registry.
  It does alter fixed module/code/literal layout and closure capture. Existing
  source-tied `../compiled-core/assembly/RESULTS.md` reports 43 native bodies
  and 29 optimized trees matching under its documented relocation rules;
  `../compatibility/allocation/ASSEMBLY.md` records 72→64, 80→72, 88→80-byte
  closure reservations and 805→809 static application instructions. An existing
  TLS key containing `NONE` has a real extra address instruction, even with
  tracking off. These are **historical source-tied emitted-work evidence**,
  not fresh product equality or dynamic allocation/time proof.

Corresponding source bytes still match those source seals. Fixed code/pool
placement, public helper emission and shared tracking behavior cannot be
accepted merely as constant overhead. The full-grid timing failures above
remain unresolved. No causal performance fix has been identified or applied;
therefore no production evidence was invalidated by a claimed repair.

Historical TASK15/16 standalone audits freeze older extension bytes and do not
pass on today's migrated extensions; they are not cited as current passes.
The fresh TASK27 closure checker admits precisely the reviewed later migration.

## Maintained driver and validation

Changed files: new `task29_gate.py`, `test_task29_gate.py`, this handoff, bounded
follow-up definitions, and the narrow `evidence/task29/` reports/archives.
The driver enumerates the exact 27-case/six-size scope, uses TASK28's unchanged
runner/admission/statistics, archives every cell before replay/cleanup, verifies
lossless transport and never turns failed or uncertain controls into parity.
Six unit tests cover scope, missing/extra cells, failed processes, wrong binding,
uncertain/failing results and live-versus-JSON runtime-key replay.

A **development preflight failed** after its first cell because the new driver
compared integer runtime keys with JSON-stringified keys. Its temporary raw
receipts were lost in cleanup; they cannot be admitted or reconstructed.
`development-failed.log.gz`, `.exit` and the empty inventory retain that defect.
The driver was repaired to compare canonical JSON and, importantly, archive
**before** replay, with a regression test. The **entire** 162-cell experiment
was then started fresh on the repaired sealed driver; no earlier observation
was reused or counted. This is not a selected favorable rerun.

Commands are from repository root; `W` is the existing
`sh src/simp/tests/compatibility/evidence/task26/root-wrapper.sh`. It binds the
configured historical `/home/lukasz/dev/HOL/worktrees/simplifier` root to this
exact checkout, not another source tree. Use new output paths when reproducing.

| Command | Exit / evidence under `evidence/task29/` |
| --- | --- |
| `W python3 -u -B src/simp/tests/performance/task29_gate.py run --candidate 18e4a1ecb624b9b13bb9a0f3ba3caf8c189bdff8 --batch-seconds 0.3 --timeout 1800 --authorize-measurements --output NEW_GRID` | **2**, blocked; `full-grid.log.gz`, `.exit`, 162 archives |
| `python3 -u -B src/simp/tests/performance/task29_gate.py replay --output src/simp/tests/performance/evidence/task29/full-grid` | **2**, all 162 archives/6,480 receipts and decisions replay identically; `replay.log.gz`, `.exit`; exit 2 deliberately preserves blocked gate status |
| `python3 -B src/simp/tests/performance/evidence/task29/report.py` | **0**; all tables, telemetry, extension-absence and graph roots |
| `python3 -B src/simp/tests/compatibility/audit_task27.py` | **0**; `source-audit.json.gz`, `.exit` |
| `python3 -B -m unittest discover -s src/simp/tests/performance -p 'test*.py'` | **0**, 247 tests, two unchanged optional runtime/path skips; `performance-tests.log.gz` |
| `python3 -B -m unittest discover -s src/simp/tests/compatibility -p 'test_*.py'` | **0**, 196 tests; `compatibility-tests.log.gz` |
| `matrix_schema.py`, `verify_evidence.py`, `coverage_ledger.py` | **0** each; full 69-requirement/107-case matrix, 37 immutable inputs, 2,153 coverage IDs |
| `W tools/h4pedant/h4pedant --nolinelen --unicodeok src/simp/tests/performance`, `git diff --check` | **0** each; pedant/whitespace logs |

Lossless archive inspection without live private trees:

```sh
python3 -B src/simp/tests/performance/evidence_bundle.py unpack \
  src/simp/tests/performance/evidence/task29/full-grid/frag_merge-1000.json.xz \
  /tmp/task29-review
python3 -B src/simp/tests/performance/audit_evidence.py \
  /tmp/task29-review/frag_merge-1000-control \
  /tmp/task29-review/frag_merge-1000-candidate
# Remove only this newly created inspection directory when finished.
```

`validation.json` pins commands/exits, new sources, source-tied structural
inputs and evidence. Linux/aarch64, Poly/ML 5.9.2, one GC thread; actual linked
libraries and heap/tool options are retained per experiment. Unsupported
runtime/platform scope, independent builds and future final revision remain
unmeasured. All task-owned copied sources, builds, unpacked receipts and
roundtrip scratch trees were removed after sealing. Caller-owned TASK28
`review/`, `review-v2/`, pre-existing caches and dirty nested planning files
were preserved. No ordinary or extension suite was disabled.

## Exact blockers and next step

- [TASK29A](TASK_29A_numerical_attribution_closure.md): resolve the exact failed
  and inconclusive timing cells and unstable controls enumerated above, with
  fresh local generated-work/layout attribution and complete affected-grid
  reruns after any fix. Source equality or smaller retained graphs cannot close
  these findings. A sufficiently stable exclusive environment plus a verified
  attribution/repair is required; host noise is not an accepted explanation.
- [TASK29B](TASK_29B_allocation_counter.md): supply/review a supported cumulative
  HOL allocator instrument and measure the full increasing-rule allocation
  matrix; current snapshot fields cannot satisfy it.

TASK29 is **not complete**; TASK30 and later dependent gates remain blocked.
No TASK29 completion-log line is added. The original fragment/merge slowdown
findings do not have full timing closure; retained-graph slope alone is closed
locally. There is no percentage budget, deferred favorable subset or claim
that final legacy performance has passed.
