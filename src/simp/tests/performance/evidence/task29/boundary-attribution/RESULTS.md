# TASK29A ordinary-process boundary attribution

**BLOCKED; not TASK29A completion.** This is an offline analysis of existing
ordinary-process observations, NOT fresh timing, a repaired-driver grid,
object-address/layout identity, pool/indirect-target attribution or a repair.
No workload, production source, runtime, driver or numerical gate changed.
No exclusive measurement environment is inferred from an offline replay.

## Coverage and admission

`heap_attribution.py` re-admits both selections of every complete experiment
using `acceptance.analyze`: source/runtime/product/path bindings, ordered fresh
processes, raw proof/callback/consumption checks, telemetry/timing alignment,
paired statistics and unchanged B/B admission. It compares the recomputed
workloads, policy AND retained-scaling result with the archived report before
publishing the exit status. Every archive seal is checked before unpacking.

- `historical-grid/`: **all 162 cells**, 6,480 timed processes and **136,960
  batches**, including calibration. No earlier cell is removed or replaced.
- `repaired-driver/`: both complete experiments, **80 timed processes / 1,560
  batches**. These are the previously published fragment/0 and collector/10000
  observations, not newly measured processes or a substitute grid.

Each compressed per-cell report preserves the original inclusive CPU/wall/GC
observations, intervals and gates; both B/B and B/C process-pair identities;
all calibration/sample counts; the initial raw runtime snapshot; every batch's
GC counts and untimed inter-batch counter increments; and every sample's
signed B-minus-A capacity/counter differences at both boundaries. Missing RSS
remains null/blocked. Unequal histories/counts are explicitly flagged rather
than silently aligned or repaired.

`baseline` and `candidate` mean A and B within a selection. In `control`, both
are develop. In `candidate`, B is the selected implementation. A signed
capacity difference is B minus A, never candidate minus a control-noise budget.
All original raw snapshots and independently recorded timers remain in the
source archives. Each process references its exact sealed receipt rather than
duplicating that raw archive. Its stage/index identifies each original batch.

Per-cell `nongc_diagnostic` also retains every process-pair operand and the
unchanged bootstrap's interval for independently recorded `nongc_usr` plus
`nongc_sys` seconds per operation. It does NOT subtract GC from inclusive CPU,
subtract B/B noise, or introduce a new acceptance gate. A diagnostic decision
is not permission to override any inclusive timing or control decision.

## Repaired-driver findings

All 20 B/B and B/C pairs in each case have identical declared calibration
histories and sample counts. Those controls do not yield equal boundary state.
Each selection compares 30 sample pairs / 60 before-and-after boundaries.

| Case | B/B non-GC ratio CI | B/C non-GC ratio CI |
| --- | --- | --- |
| frag_record/0 | [0.984485, 1.002099] | [1.009594, 1.019958] |
| compile_collector/10000 | [0.993050, 1.002648] | [1.003961, 1.039454] |

These diagnostic non-GC intervals are above equality in B/C, even though the
collector's inclusive CPU remains inconclusive. This is evidence against
simply declaring equal work or treating the inclusive result as exclusively
GC timer cost. It is NOT causal isolation: GC/cache/scheduling effects can
also affect independently timed non-GC execution.

For BOTH cases, every B/C sample boundary has **+4,096 bytes of code
capacity**, whereas every B/B sample boundary has zero code-capacity
difference. The first calibration snapshots record baseline 1,036,288 versus candidate 1,040,384
bytes. This is a runtime capacity observation, not a byte count of emitted
instructions, proof of an extra ordinary-path instruction, literal equality,
or executed-target identity. No padding/cache/layout fix is selected.

- **Fragment/0:** partial-GC counts differ in all **30/30** B/C sample pairs
  (B/B: 28/30). Across the three samples, each baseline process observes
  85–110 partial collections, each candidate 112–181; neither side observes
  a full collection within a sample. Heap/allocation-area capacity differs at
  30/60 B/C boundaries (B/B: 29/60). The B/C heap-capacity differences range
  from -65,011,712 to 0 bytes; B/B from -26,214,400 to +14,680,064. Identical
  counts demonstrably do not imply identical GC or resizing histories.
- **Collector/10000:** full-GC counts differ in **18/30** B/C sample pairs
  (B/B: 4/30); partial-GC counts in **27/30** (B/B: 6/30). Heap capacity
  differs
  at **56/60** B/C boundaries (B/B: 18/60), with B/C differences ranging from
  -12,582,912 to +331,350,016 bytes. Both selections also have
  allocation-area capacity differences. Snapshot capacities cannot identify allocated bytes,
  live-object topology, or the cause of those schedules.
- All 80 processes have blocked RSS inference because their raw Linux VmHWM
  series is nonmonotonic. Raw values are retained; no clamping or invented
  temporary peak is used. Independent GC/capacity observations remain valid.

The original repaired-driver inclusive outcomes remain exactly: fragment/0
CPU **[1.014519, 1.032057]**, wall and GC **fail**; collector/10000 CPU
**[0.988111, 1.032104]**, wall and GC **inconclusive**. No diagnostic interval
admits a control or closes a gate.

## Full historical grid and no-rule cases

All six sizes for every historical case are retained individually in
`historical-grid/inventory.json` and its sealed per-cell reports, not averaged
across workloads. All **43 failed / 119 inconclusive** CPU/wall/GC cells remain
unresolved. This replay is against the historical fixture; those observations
cannot supply acceptance for the repaired driver.

For historical `compile_single/0`, all **120 measured samples** still have
zero GC timer operands, and the corresponding boundary full/partial/share
counter increments are all zero. B/C heap and allocation-area capacities have
zero difference at all 60 measured boundaries, yet last-GC free sizes differ
at all 60. Equal capacity and no measured collection therefore cannot certify
heap identity or turn the undefined GC ratios into passes. The per-cell
non-GC B/C interval **[0.999969, 1.000372]** also remains inconclusive. Other
size-zero/constant cases are included, not excused because no rules are used.

## Reproduce and inspect

From the repository root (no measurement authorization or wrapper is needed):

```sh
P=src/simp/tests/performance
E=$P/evidence/task29
python3 -B "$P/heap_attribution.py" generate \
  --inventory "$E/full-grid/inventory.json" --output NEW_HISTORICAL_DIRECTORY
python3 -B "$P/heap_attribution.py" generate \
  --inventory "$E/experiment-driver/validation.json" \
  --output NEW_DRIVER_DIRECTORY
# Each returns 2 after successful diagnostics: NOT numerical acceptance.
python3 -B "$P/heap_attribution.py" replay \
  --inventory "$E/full-grid/inventory.json" \
  --output "$E/boundary-attribution/historical-grid"
python3 -B "$P/heap_attribution.py" replay \
  --inventory "$E/experiment-driver/validation.json" \
  --output "$E/boundary-attribution/repaired-driver"
# Each replay also returns 2 deliberately; any exception is a replay failure.
python3 -B -m unittest discover -s "$P" -p test_heap_attribution.py -v
HEAP_ATTRIBUTION_REAL_INVENTORY="$PWD/$E/experiment-driver/validation.json" \
  python3 -B -m unittest discover -s "$P" -p test_heap_attribution.py -v
```

Read a per-cell report with Python `gzip.open` and `json.load`. The diagnostic
inventories bind the source inventory, admission inputs and every derived
report. Replay recomputes from original archives, not just report seals.
Existing output paths are refused; interrupted reports remain explicitly
incomplete. Temporary unpack trees are removed on success and failure. Numeric
JSON types are significant: resealed `false` is not accepted as index/size 0.
Tests also cover changed scope, missing admission dependencies,
retained-scaling mutation and partial/mutated inventories. Synthetic controls
are not timings.

Final validation: **25 attribution tests pass**, including real archive
re-admission. The complete performance Python suite runs **379 tests, four
optional skips, no failures**. Exact commands, exits, compact logs and seals
are in `commands.json`, `tests.json` and `validation.json`. Both complete
inventories were generated AND independently replayed without timeout. No
compiled source changed; these are Python/doc checks, not a new HOL build.

## Remaining acceptance requirements

This is boundary-state attribution, NOT complete ordinary-process heap/code/
literal layout attribution. Fresh pools, indirect targets, live object graphs,
a causal source/layout repair and the **entire repaired-driver 162-cell grid**
remain missing. No exclusive stable measurement window has been established by
this work. Required explicit policy-owner disposition remains
`../../../TASK29A_POLICY_REVIEW.md`: exact zero/zero GC and directional B/B
admission. No rule is chosen or waived here. TASK29B's separate allocation
coverage/lineage/matrix requirements are unchanged. TASK29A is **not done**;
there is no completion-log entry.
