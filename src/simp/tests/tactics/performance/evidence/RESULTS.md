# TASK18 execution results

Exclusive window explicitly authorized by parent. All builds/measurement
processes serial, private launchers built before measurement. No production
or shared files changed; no commit. This completes the requested measurement
work, **not cost-parity/TASK18 acceptance**.

## Executed

- Offline controls: 12 timing/harness tests; 3 codegen-adapter tests.
- Native elaboration and all 66 row proof/hypothesis/residual/oracle checks.
- Initial complete current campaign: 10 fresh AB/BA pairs, 3 samples per row,
  plus one same-count calibration per row/process.
- Lengthened common schedule, then **10 current pairs + 10 baseline-control
  pairs** under that identical schedule; 40 fresh final timing processes.
- Final campaigns each contain 5,280 checked batches including calibration,
  3,960 timed samples. No outliers, rows, or early attempts discarded.
- Current and independent baseline-control targeted codegen collections;
  69 native occurrences each match modulo constant-pool relocation only.
- Offline lossless-archive/protocol/inference/codegen recheck and h4pedant pass.

## Harness fixes before final measurement

1. Wrapped the long residual-goal equality line in `TacticInputs.sml`.
2. Added the missing `structure TacticInputs = struct ... end`; its dependency
   had loaded but `open TacticInputs` could not elaborate.
3. Exact expected hypotheses now retain all extra assumptions for
   full/reverse/no-strip tactics, but not global variants. Diagnosed on pinned
   baseline with explicit actual/expected theorem output. No check removed.
4. Codegen adapter initially required optimized-tree output unavailable for
   local declaration blocks. It now records the actual backend trees, with a
   synthetic fail-closed selection test. Failed initial collection retained.

All four fixture attempts before the initial complete campaign and the failed
codegen attempt remain archived with failed manifests and raw diagnostics.

## Calibration and observations

The initial campaign exposed construction batches down to 0.000280 s.
For **each row**, multiply its initial count by
`max(1, ceil(0.12 / minimum_of_all_initial_samples_on_both_sides))`.
The resulting `final-iterations.json` is common to current and control.
Final batches including calibration range **0.078829–0.828066 s**; the typical
short construction batches were lengthened hundreds of times. Per-row minima
and complete raw calibration/sample observations are retained, not assumed.
The initial campaign uses the original `fixed-iterations.json` schedule.

- CPU geometric-mean ratios span **0.963185–1.015494**.
- All 66 CPU/wall/non-GC/user/system family intervals in current, control and
  their independent contrasts span one: **unresolved, not parity**.
- `no_strip_full_complete.0` is individually slower for CPU, wall and non-GC
  CPU. CPU ratio 1.013473; individual interval [1.001039, 1.026062]; family
  interval [0.986292, 1.041404]. Do not erase the individual observation.
- **Seven GC family intervals are slower:** `full_complete.0`,
  `rev_complete.0`, `simp_complete.8`, `rev_reuse.8`,
  `no_strip_full_reuse.8`, `no_strip_full_complete.8`,
  `no_strip_rev_reuse.8`.
- **Three remain slower in independent control contrasts:**
  `rev_complete.0`, `no_strip_full_reuse.8`, `no_strip_rev_reuse.8`.
- Nine GC rows are unresolved due to zero timers. No zeros replaced.
- GC in the seven slower rows is roughly 0.41–0.54% of total CPU, with
  descriptive candidate-baseline median GC differences of about 0.5–26 ns/op.
  These small absolute amounts do **not** waive a slower interval. No GC cause
  or allocation-equivalence claim is made from this evidence.

`ROWS.md` covers all 66 rows. `receipts.tar.xz:final-analysis.json` retains
all six metrics, process medians, paired ratios, individual/family intervals,
independent contrasts and sample durations. The raw process receipts also
retain every calibration and exact stage/consumption/proof/provenance gate.

## Source/codegen result and blocker

See `LOCAL_COSTS.md`. Entire ordinary source/signature bytes match the pinned
baseline, and 53 named simpLib native occurrences (69 including selected
library/top-level bodies) recover their original local instructions, calls
and static allocation sites. No local extension dispatch or moved stage is
introduced. Current has five non-native aggregate export records differing
only in the symbolic `track` target, `Cond_rewr.with_tracking` to
`SimpTracking.with_tracking`; all differences are retained. Independent
control trees/ICode are exactly equal. Full compiler extents are archived.

This supports **local baseline staging costs**, not whole-runtime parity.
The changed lower-level tracking environment and GC observations prevent any
blanket numerical parity acceptance. GC investigation or a production fix
requires parent-owned scope; this worker modified performance files only.

## Commands (repository root)

```sh
P=src/simp/tests/tactics/performance
python3 -B -m unittest discover -s "$P" -p 'test_*.py'
python3 -B -m unittest discover -s "$P/assembly" -p 'test_*.py'
python3 -B "$P/audit_sources.py" --output "$P/evidence/final-source.json"

# Initial fixture failures used /tmp/task18-tactic-initial{,2,3,4}; then:
python3 -B "$P/run_tactics.py" --authorize-measurements \
  --pairs 10 --samples 3 --timeout 1800 \
  --fixed-iterations "$P/fixed-iterations.json" \
  --output /tmp/task18-tactic-initial5
# Derive final schedule by the all-sample formula above.
python3 -B "$P/run_tactics.py" --authorize-measurements \
  --pairs 10 --samples 3 --timeout 1800 \
  --fixed-iterations "$P/final-iterations.json" \
  --output /tmp/task18-tactic-current
python3 -B "$P/run_tactics.py" --authorize-measurements --baseline-control \
  --pairs 10 --samples 3 --timeout 1800 \
  --fixed-iterations "$P/final-iterations.json" \
  --output /tmp/task18-tactic-control
python3 -B "$P/summarize.py" --candidate /tmp/task18-tactic-current \
  --control /tmp/task18-tactic-control \
  --output /tmp/task18-tactic-analysis.json

# First native attempt /tmp/task18-codegen-current failed closed; corrected:
python3 -B "$P/assembly/run_assembly.py" --authorize-measurements \
  --output /tmp/task18-codegen-current2
python3 -B "$P/assembly/run_assembly.py" --authorize-measurements \
  --baseline-control --output /tmp/task18-codegen-control

python3 -B "$P/evidence/recheck.py"
python3 -B "$P/evidence/report.py"
tools/h4pedant/h4pedant "$P"
git diff --check
```

## Retention / cleanup

`receipts.tar.xz` is a lossless cross-record archive of 132 unique members,
including failed attempts and full compiler extents; `archive-index.json.gz`
seals both stored bytes and original gzip bytes. `recheck.py` recovers those
exact compressed receipts, verifies all final source inventories agree with
codegen, replays all 60 complete timing-process protocols/inference, and
re-extracts both codegen selections. `sources.tar.xz` stores 90 unique sealed
input/selected-source blobs, not duplicate build trees. Historical inputs
include the exact pre-documentation-update README and harness bytes used.

Temporary private builds were removed by runners on success/failure; all
agent-created `/tmp/task18-*` campaign outputs were removed after archiving
and recheck. No heaps, executables, caches or copied build trees retained.
The parent may release the exclusive window after this worker's report.
