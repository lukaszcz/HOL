# TASK29A post-workload runtime objects — NOT closure

**TASK29A remains incomplete.** Candidate:
`7b6a7d7ddf8ffcb31938694acb3b583f70a4bb07`; pinned develop:
`cccaa27d7099cbadc886983020cbe745db7793f3`.
No production, ordinary workload fixture, tracking identity, numerical policy
or allocator file was changed. Existing allocator working-tree work is separate.

## Fresh structural observations

`record.json.xz` and `collector.json.xz` retain **eight fresh diagnostic
processes**: one B/B and B/C pair for each repaired-driver case, counts
33,554,432 and 64 respectively, three samples, 0.1s target. All pass the paired
source/runtime/path/proof/callback/consumption checks. Compiler printing is off.
A newly compiled postlude dumps actual objects only after Performance returns.
All timings are retained, but the diagnostic suite is inadmissible for timing.
Host-wide exclusivity is NOT established by the sandbox/advisory locks.

| Case / selection | Baseline words / objects | Other words / objects |
| --- | --- | --- |
| frag_record/0 B/B | 412,600 / 34,858 | 412,600 / 34,858 |
| frag_record/0 B/C | 412,600 / 34,858 | 412,599 / 34,858 |
| compile_collector/10000 B/B | 2,780,452 / 617,010 | 2,780,452 / 617,010 |
| compile_collector/10000 B/C | 2,780,452 / 617,010 | 2,397,860 / 506,216 |

These are graphs reachable from four driver/workload functions, **not** live
heap, allocated bytes or matched-shape proofs. The collector's differing
retained graph is concrete further attribution input, not a beneficial-cost
claim or an explanation of the historical slowdown.

Every process has **213 split code pools with unprinted slots**. There are no
runtime bad-address warnings or unresolved *printed* pointer slots. Neither
fact supplies the omitted pool values. B/B raw-slot correspondence leaves
769 objects unmatched and has eight byte-object differences per case (private
source names and mutable runtime output-buffer contents), with zero native-word
differences among corresponding objects. B/C correspondence retains all 118
fragment and 172,806 collector differences, including pool-order and aliasing
mismatches; it is not a canonical semantic graph match.

## Actual caller/pool bindings

`attribution.json` is derived by `replay.py` **after** full diagnostic
re-admission, selecting code by actual root addresses, never just its name.
It retains exact root alignment, sizes, raw ADRP/LDR operands, pool slot and
concrete referent address/type/code-name for every decoded reference.

- Fragment `run` is the 3-word callable object for
  `MatrixSupport.fragwork(4)(1)` (two captured words) on both sides. Its native
  object is 15 words and its pre-pool words are exactly equal. The captured
  build closure has one captured word; its actual
  `MatrixSupport.workload(2)(1)` code object is 34 words on both sides. All
  three decoded loads resolve to actual `List.map(2)()` code objects, retaining
  their distinct addresses (a repeated name does not prove identity).
- Collector `run` is the 4-word callable object for
  `MatrixSupport.sswork(2)(1)` (three captured words) on both sides. The native
  object is 16 words on both sides. Its offset-40 ADRP/LDR resolves to the
  actual `simpLib.++(2)` code object on each side, not a compiler placeholder.
- `step` has five resolved loads on both sides; offsets 36/48 bind its actual
  callable `run` object and corresponding code entry. `measured` has one;
  `experiment` has three, binding actual calibration/list/sample code objects.
- All selected root/build native words become equal after masking **only**
  decoded ADRP/LDR address immediates. Every selected pattern resolves inline;
  no extra pattern/instruction or larger selected object is observed. This
  says nothing about dynamic executions, omitted split pools or full captured
  object equivalence. The raw native words differ in B/C except fragment run.
- B/B root code alignments and native words match. B/C fragment run alignment
  changes from 16 to 40 mod 64; collector run from 8 to 16; step from 48 to 0
  in both cases. This is a fresh address/layout observation, **not** causal
  cache attribution. Postlude compilation may have moved code after timing.

No extra ordinary-path cost or its absence has been proved. No padding,
tracking relocation, constructor representation change or other production
repair is justified by these correlations alone.

## Reproduction, tests, development observations and cleanup

See `../../../RUNTIME_LAYOUT.md` for collection commands. Final offline replay:

```sh
python3 -B src/simp/tests/performance/evidence/task29/runtime-layout/replay.py
# Exit 0 = diagnostics replay; explicitly NOT TASK29A acceptance.
```

`validation.json` seals code, bundles and test logs. Both final bundles are
unpacked and re-admitted by replay. The 13-test real-archive suite passes on
**each** final case, including coherent mutation rejection and B/C-for-B/B
substitution rejection. Full current-working-tree discovery: **392 performance
tests** pass with five explicit opt-in skips; **196 compatibility tests** pass.
The new real-archive opt-in is separately executed above, not left untested.
SML postlude compilation/execution is exercised by all eight final processes.
No compiled production source was edited.

Development observations are also retained, never favorable-rerun selected:

- `development-untraced.json.xz`: one process rejected by the existing loaded
  source inventory because the postlude initially used untraced `Meta.qquse`.
  The correction is `tracedUse`, not an auditor waiver. Its raw dump remains.
- `development-slot-only.json.xz`: four provisional structural processes from
  the earlier raw-slot-only parser. They are not timing acceptance and are not
  replayed against final diagnostic-input seals: the diagnostic implementation
  changed. Final collection reruns the entire two-case B/B+B/C diagnostic set,
  rather than selecting individual favorable processes from that set.
- The first direct wrapper launch exited 126 (file not executable); collection
  invokes the unchanged wrapper with `sh`. Synthetic test development exposed
  a wrong hand-written fixture count/total, corrected before real collection.

All four bundles roundtrip with exact original file hashes. Task-created
private source/build trees are removed by the paired runner; unpack/roundtrip,
validation and raw collection directories are removed after sealing. Caller
caches, allocator controls and unrelated evidence are untouched.

## Acceptance blockers remain exact and unchanged

- Repaired-driver fragment/0 CPU **[1.014519, 1.032057]**, wall and GC still
  **fail**. Collector/10000 CPU **[0.988111, 1.032104]**, wall and GC remain
  **inconclusive**. No new admissible ten-pair timing is supplied here.
- All 162 historical cells remain 43 failed / 119 inconclusive. Full fresh
  repaired-driver grid, every scoped passing gate/control, and attribution of
  all failed/uncertain/no-rule cells remain missing. Two structural cases do
  not replace any grid cell.
- Measurement-boundary object/layout, omitted pool slots, actual executed
  indirect targets and a causal repair remain unresolved.
- A sufficiently stable **exclusive** environment must be supplied/verified;
  this PID-isolated sandbox cannot establish host quiescence. No claim that
  host noise caused a slowdown, and no numerical budget, follows.
- Explicit policy-owner disposition of zero/zero GC and directional B/B
  upper-CI<=1 is still required (`../../../TASK29A_POLICY_REVIEW.md`). The
  user's completion instruction does not specify a replacement contract.
- TASK29B allocation coverage/lineage/full matrix is separate and not closed.

There is no task-completion entry or waiver. Diagnostic progress cannot satisfy
those external prerequisites or silently redefine their gates.
