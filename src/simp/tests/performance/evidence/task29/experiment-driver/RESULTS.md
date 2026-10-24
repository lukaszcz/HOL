# TASK29 — precompile calibration and sampling together

**BLOCKED, not complete.** Starting/selected candidate:
`40f2189c3e4bd5c22c374e996e0d4831509b20de`; develop:
`cccaa27d7099cbadc886983020cbe745db7793f3`. Live fixture hashes, runtime,
loaded paths, options and products are bound in the archives/validation.
No production source, ordinary representation, shared control, extension
assertion, numerical policy or allocator patch changed.

## Concrete repair

Both matrix fixtures previously executed calibration in a top-level value
binding, THEN compiled `sample`, embedding the chosen count. Compiler work
therefore intervened after calibration. They now compile the whole
`experiment` function first; its calibrated count is a runtime local. No
workload, result verification, calibration doubling, timed batch, metric or
size was removed. This removes a demonstrated experimental confound; it does
not prove the cause of earlier timing differences.

The new Holmake/testutils fixture reads the exact live driver suffixes and
uses **HOLSource.stringToReader**, the same translator family as QUse, around
real PolyML.compiler calls. A compiler-entry serial must not change from first
calibration to last sample. For BOTH fixtures it checks adaptive calibration,
fixed counts 2/4/16 even after early duration crossings, exact observation
fields/indices, consumption and all result checks, and short-count rejection.
Reinstating the top-level-count driver actually triggers the compiler-entry
guard. All **36 assertions pass**. Synthetic durations are scheduling controls,
not workload timing or allocation data. `Holmake check` now includes this
control before semantic smoke.

Development checks found a wrong launcher cwd, a wrong Portable.finally cleanup
arity and an absent identity binding in the synthetic environment. A plain SML
reader then correctly exposed that it did NOT reproduce HOL's declaration
boundaries: the old-code negative control failed. Switching to the actual
HOLSource reader makes both old-code controls reject. The quiet-open option
also requires HOL_Interactive, so the final test uses QUse's ordinary false
setting. None of those development runs is timing evidence or admitted as a
passing control. The final recorded target builds AND executes the launcher.

## Fresh ordinary-runtime observations

Counts were chosen before these experiments: the preceding fixed-count
fragment diagnostic's 33,554,432, and preceding collector experiment's 64.
Both run three samples, 0.3s target, ten B/B then ten B/C fresh alternating
pairs. All **80 timed processes / 240 samples** pass source/runtime/path,
proof, callback and consumption admission. Calibration histories match within
each experiment. No pair, metric or observation was filtered.

| Case / metric | B/B 95% ratio interval | B/C 95% ratio interval | Adjusted gate |
| --- | --- | --- | --- |
| frag_record/0 CPU | [0.985707, 1.000342] | [1.014519, 1.032057] | **fail** |
| frag_record/0 wall | [0.985158, 1.003321] | [1.014511, 1.032081] | **fail** |
| frag_record/0 GC | [1.015502, 1.220624] | [1.321131, 1.633900] | **fail** |
| compile_collector/10000 CPU | [0.985258, 1.002203] | [0.988111, 1.032104] | inconclusive |
| compile_collector/10000 wall | [0.985231, 1.002168] | [0.988116, 1.032226] | inconclusive |
| compile_collector/10000 GC | [0.989343, 1.117547] | [0.786938, 0.807983] | inconclusive |

The collector's raw GC interval is below one, but its B/B control is uncertain;
it is NOT a pass. Its CPU/wall now straddle equality: NOT closure of the prior
failure, a causal attribution, or permission to replace the full grid with a
favorable subset. Fragment CPU/wall/GC still reproducibly fail. Changed fixture
code invalidates earlier timing for acceptance on this driver. The original
**43 failed / 119 inconclusive** grid and equal-count failures remain immutable
historical observations. Every affected cell still requires a new full-grid
experiment; none is declared closed by these two experiments.

Additional fixed/adaptive client and adaptive fragment one-pair smokes execute
**six real timing processes** and pass strict archive admission. They are
protocol controls, not ten-pair numerical acceptance. All five runtime bundles
roundtrip byte-for-byte. `replay.py` independently re-admits all 86 timed
processes, recomputes both complete paired analyses with unchanged control
rules, binds the repaired fixture hashes and preserves failures/uncertainty.

## Commands, validation and cleanup

`commands.json` retains exact argv/exits and log names. W is the existing
`compatibility/evidence/task26/root-wrapper.sh`. Core commands from root:

```sh
W bin/Holmake --no-project --no-cache --no_prereqs \
  -C src/simp/tests/performance -j1 driver-staging-control
W python3 -B src/simp/tests/performance/acceptance.py run \
  --candidate 40f2189c3e4bd5c22c374e996e0d4831509b20de \
  --case frag_record --size 0 --pairs 10 --samples 3 \
  --batch-seconds 0.3 --batch-iterations 33554432 --timeout 1800 \
  --authorize-measurements --output NEW_DIRECTORY
# exit 1: protocol complete, numerical failure
# Repeat as a separate whole experiment for compile_collector/10000, N=64:
# exit 2: protocol complete, inconclusive, NOT acceptance.
python3 -B src/simp/tests/performance/evidence/task29/experiment-driver/replay.py
# exit 0: reproduces blocked outcomes, NOT TASK29 approval
W bin/build -t --seq=tools/sequences/upto-parallel
```

- **328 performance Python tests** pass (three optional skips outside W;
  four inside W, whose private /home hides the pristine runtime source).
  These are the existing explicit real-codegen/client/runtime opt-ins and,
  inside W only, the pristine-source-dependent allocator patch check. No
  assertion was disabled or changed. Compatibility: **196 pass**.
- Normal `Holmake check`: **exit 0**, 328 tests plus 13 runner tests, 36 new
  staging assertions, unchanged matrix and real negative controls, all
  **306 fragment / 336 client** semantic smoke checks. Compact smoke inputs
  and receipts are in `check-results.json.xz` (five-file lossless transport).
- Routine selftest-enabled build: **exit 0**, after both ten-pair experiments;
  ordinary/extension/API suites remain enabled. Fresh eight-process API audit:
  `src/simp/tests/api-audit/evidence/20261024T080434Z-a4dbc9dc/receipt.json`
  (repository-relative).
  This is not independent-build or final-build-product timing acceptance.
- Pedant and whitespace checks: **exit 0**. `validation.json` seals sources,
  archives, checks and the API receipt. All task-created copied source/build,
  unpacked/roundtrip and check-output trees are removed after sealing. Existing
  caller-owned review directories, caches and nested planning edits remain.

## Exact blockers / required policy input

The full-grid unresolved inventory remains
`../full-grid/decisions.json`, all 162 cases/sizes; the current two-cell results
above do not replace it. Ordinary-process heap/pool/indirect-target attribution
is still unresolved. Allocation branch/failure coverage, native compiler/image
lineage and the full **162-cell ten-pair B/B and B/C allocation matrix** remain
missing. No retained-graph or static reservation number substitutes for them.

Two unchanged policy rules additionally prevent a completion claim:

1. The original compile_single/0 has zero GC in every one of its 120 measured
   sample records. Ratio-only 0/0 is always inconclusive. No amount of repeating
   that zero-work GC comparison can make it pass under the current rule.
2. B/B requires its upper ratio bound <=1. A precise interval straddling true
   equality is not, by itself, evidence of an unstable environment. This is a
   directional no-slowdown decision, not an independently defined control-
   validity test. A quieter host cannot be promised to satisfy it everywhere.

**Explicit review is needed** to define the zero-GC and B/B-control acceptance
contracts. No budget, control subtraction, zero/zero shortcut or silent
uncertainty-to-pass conversion was introduced. TASK29, TASK29A and TASK29B
remain incomplete; no completion-log line is warranted.
