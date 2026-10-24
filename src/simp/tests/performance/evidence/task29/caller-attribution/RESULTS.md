# Fresh caller attribution — TASK29 remains blocked

Candidate: `90e528c41` (full pin in each manifest). Reference:
`cccaa27d7099cbadc886983020cbe745db7793f3`. Linux/AArch64, Poly/ML 5.9.2,
one GC thread, common configured `hol.state0` and shared dependencies.
No production simplifier/runtime source, representation or public API changed.

## Final complete diagnostics

`record-zero.json.xz` and `collector-large.json.xz` each contain 24 original
files, losslessly transported and independently replayed after unpacking.
Each has fresh B/B and B/C processes: **eight final compiler-printing processes**
in total, plus sixteen ordinary legacy signature/selftest fixture processes.
Every process, proof, callback, path and source/runtime protocol check passes.

The fixed counts are 33,554,432 for `frag_record/0` and 64 for
`compile_collector/10000`, including identical doubling histories on both
selections. Three measured samples are preserved per printing process, but
**none is acceptance timing evidence**. There is one structural process pair
per comparison, not the ten pairs required for performance acceptance.

Native-body results are the same in BOTH targeted experiments:

| Source | B/B bodies matching after pool relocation | B/C matching |
| --- | ---: | ---: |
| MatrixSupport | 885/885 | 885/885 |
| Performance (actual fixture/loops) | 68/68 | 68/68 |
| simpLib | 668/668 | 668/668 |
| Traverse | 106/106 | 106/106 |
| Cond_rewr | 116/116 | 108/117 union entries |
| SimpTracking | absent | five candidate-only bodies |

The core/caller counts include inlined specializations and repeated names,
not just public function roots. The actual `SSFRAG` body reserves 72 bytes and
has 59 static instructions on both sides; `simpLib.++(2)` has 336 on both.
`repeat(1)(1)` and `step(1)` have 40 and 32 respectively, with no direct static
reservation. These are static observations, not dynamic allocation totals.

Fresh Cond_rewr output reconfirms reduced constructor reservations (72 to 64
bytes in `COND_REWR_CONV(3)`, 80 to 72 in its next curried closure). The union
also includes removed `with_tracking` bodies, candidate-only `is_var_perm`,
changed application closures and module initialization. All original trees,
ICode, native operands, line offsets and hashes remain archived. No different
function is silently paired with a missing same-name body.

**This does not resolve the slowdown.** Pool contents/indirect targets remain
unbound by this diagnostic; exact pool operands are not discarded. Even B/B
has exact printed-text differences in otherwise matching native bodies.
Printing/loader changes alter layout and heap state. Neither normalized native
matches nor smaller closure reservations prove equal ordinary-runtime cost.
The data do not justify restoring tracking ownership as a repair for the
no-tracking fragment constructor or collector construction.

## Preserved development outcomes

- `development-optional-form.json.xz`: the first whole diagnostic rejected
  SimpTracking because it has backend/ICode/native output but no `fn(...)`
  optimized-lambda printer form. Complete failed stdout was saved before the
  guard. The optional module now reports actual forms without inventing one;
  mandatory caller/core forms are still required.
- `development-calibrated-count.json.xz`: complete automatic-count diagnostic.
  It exposed an additional genuine confound: `sample` is compiled after
  calibration and captures the selected count as an immediate. Its B/C code
  differs at four immediate operands. The new final whole experiments use
  fixed counts; no unfavorable observation was selected out of a timing gate.
- `development-test-guard-*.json.xz`: earlier whole fixed-count diagnostics,
  superseded after a real mutation test expected a later guard than the one
  correctly rejecting a changed fixture. All runtime observations, proofs,
  source/transport stamps and comparison metadata are retained. Redundant
  compiler dumps were removed, explicitly listed in `SUPERSEDED.json`; these
  are not complete replayable codegen archives. Final complete diagnostics
  were rerun after correcting only the test's expected error.
- `development-real-tests.log.gz`: that failed assertion; final
  `real-tests.log.gz` passes all twelve tests and all seven real mutations.

No production source was repaired and no ordinary-runtime acceptance result
is replaced by these diagnostics.

## Numerical evidence remains blocked

A full-grid offline replay reached 135 complete cells before the caller's
900-second process timeout. `grid-prefix.log.gz` preserves that prefix.
`resume_grid_replay.py` verifies its exact inventory prefix and original driver
seal, checks all 162 archive seals, analyses the remaining 27 cells with the
unchanged checker, and verifies the aggregate original decisions. Its receipt
is `grid-resumed.json`. This is a **two-stage locally trusted replay**, not a
claim of one uninterrupted successful process or new timing observations.
The timeout's temporary unpacked tree was removed after confirming no child
process remained. Prefix/suffix logs and exit statuses are retained.

All original decisions remain **43 failed / 119 inconclusive** cells. The
separate equal-count replay again retains collector CPU
**[1.032421, 1.052741]** and wall failure. No B/B, zero-GC, interval, workload,
allocation or extension rule changed. TASK29A and TASK29B are not complete.
The full allocation matrix and the existing allocator coverage/compiler-image
lineage gaps remain missing. No instrumentation was run in these processes.

## Validation

- Final diagnostic commands: exits **0**, both cases, B/B and B/C.
- Raw bundle roundtrip plus replay: exits **0**, 24 exact files each.
- Real archive tests: **12 pass**, including seven coherent mutations.
- Performance discovery with the real archive enabled: **328 tests**, two
  unchanged optional skips, exit **0**.
- Compatibility discovery: **196 pass**, exit **0**.
- `W bin/build -t --seq=tools/sequences/upto-parallel`: exit **0**. New API
  audit: `../../../../api-audit/evidence/20261024T070025Z-929ee34d/receipt.json`
  (path from this directory). The build follows diagnostics; this is not a
  final-build-product performance claim.
- Pedant and whitespace checks: exits **0**, recorded in `validation.json`.

`validation.json` seals sources, compact evidence, commands and statuses.
All task-owned private builds, source copies, unpacked/roundtrip trees and
scratch logs were removed after sealing. Caller-owned review directories,
pre-existing caches and unrelated planning state are untouched.
