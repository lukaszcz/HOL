# TASK29 — fragment/compiler/storage isolated gate

## Status: BLOCKED, not complete

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
