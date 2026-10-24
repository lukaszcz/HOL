# TASK29A — close the isolated fragment/compiler numerical gate

## Context and dependency

Bounded follow-up to TASK29, after TASK28. TASK29 is **blocked**, not landed
as complete. Ordinary `simpLib` is byte-identical to pinned develop; this is
not permission to waive measured costs. No production fix has been selected
or made. This follow-up owns numerical/code-layout attribution only; it does
not absorb TASK30 exclusions, TASK31 loading/tactics, or independent builds.

Inputs: `TASK_29_HANDOFF.md`, `evidence/task29/RESULTS.md`,
`evidence/task29/full-grid/decisions.json`, and sealed per-cell archives.
The exact 162 cells and their CPU/wall/GC decisions are enumerated there:
22 CPU failures, 23 wall failures, 31 GC failures; 139/138/131 respective
inconclusive decisions. The two CPU/wall passes are both `compile_excluded/1`.
There are **43 distinct failed cells and 119 uncertain cells**, not passes.
Ten CPU, eight wall and two GC baseline controls also fail; uncertain controls
are not parity and do not excuse candidate failures.

## Investigation after `e86df07bf` — not closure

`TASK_29_HANDOFF.md` and `evidence/task29/equal-count/` record a reproduced
calibration confound and the new optional `--batch-iterations` mode. All B/B
and B/C processes now can use a predeclared common calibration history and
sample count without changing any numerical gate. Eight new controls and
real fragment/client/short-batch processes validate the mode.

The ten-pair collector/10000 experiment at common N=64 **still fails** CPU
(CI [1.032421, 1.052741]) and wall; GC and all B/B metrics are inconclusive.
No original grid cell is replaced or closed. Equal counts do not establish
identical heaps, GC schedules or generated code. No production repair is
selected; fresh generated-work/layout closure and the full affected grid
remain unsatisfied requirements, not deferred completion claims.

The unchanged B/B rule also requires an upper ratio bound <=1; an interval
straddling equality is not by itself evidence of host instability. The original
compile_single/0 has all 120 measured GC values exactly zero, which cannot
pass a ratio-only 0/0 policy. These policy concerns require explicit review,
not silently accepting uncertainty, adding a budget or manufacturing GC work.

## Work and acceptance

- Diagnose all failed and inconclusive cells, including the no-rule constant
  cases. Keep all original observations. Do not select favorable repetitions,
  remove outliers, subtract control noise, add a percentage budget, reduce the
  matrix, or accept unchanged source as a runtime proof.
- Inspect fresh generated work and runtime/heap/code/literal layout against
  the baseline and B/B controls. Existing source-tied assembly evidence is
  structural input, not fresh generated-product equality. In particular the
  shared tracking extraction changes closure capture and some TLS-path
  instructions; it must not introduce an extra ordinary-path cost.
- If a repair is justified, keep ordinary records/compiler schedules exactly
  develop-compatible. Preserve the one shared public tracking extent/control
  identities and all explicit extension functionality. Never introduce a
  configured companion, source inventory, warmed cache or migration flag.
- Invalidate every affected earlier measurement after a source/build change;
  rerun the **entire affected grid**, all sizes, complete/construction/reuse
  stages, baseline controls and at least ten B/B and B/C fresh AB/BA pairs.
  Use the unchanged fail-closed protocol. Publish raw observations, intervals,
  constant-size differences and local attribution, not an overall average.
- Every scoped timing gate must pass with admissible controls. Otherwise
  TASK29 remains blocked with exact cases. This follow-up does not complete
  TASK29B's cumulative-allocation prerequisite.

Required input before claiming closure: a reproducible, sufficiently stable
exclusive measurement environment and source/layout attribution/repair that
resolves these observations. No hypothesis about host noise is accepted as a
fix. Linux/aarch64 Poly/ML 5.9.2 is the measured platform; no universal or
independent-build claim follows.
