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

## Fresh caller diagnostics after `90e528c41` — still not closure

`CALLER_CODEGEN.md` and `evidence/task29/caller-attribution/RESULTS.md` now
supply actual caller/loop optimized/backend/ICode/native output, with fresh
B/B controls and all raw operands retained. Both targeted cases use fixed
counts. All 885 MatrixSupport, 68 Performance, 668 simpLib and 106 Traverse
native bodies match after pool relocation in B/B and B/C. Fresh Cond_rewr
constructor output reconfirms smaller captures; its union still differs and
SimpTracking has five separate candidate-only bodies. The data do not establish
literal identity or a causal explanation for the slower ordinary workloads.

A new concrete caller confound is recorded, not waived: `sample` is compiled
after calibration and captures its actual selected count as immediate operands.
The initial automatic-count diagnostic had four different operands; final
fixed-count diagnostics remove that difference. Printing changes heap/layout,
so their sample times are deliberately inadmissible for acceptance. These
single structural pairs do not replace ten-pair ordinary-runtime evidence.

The full-grid decisions remain 43 failed / 119 inconclusive after a documented
two-stage offline replay (135 cells before a 900s timeout; original checks for
the remaining 27; all archive seals and aggregate decisions rechecked). The
equal-count collector CPU/wall failure is also replayed unchanged. No source
repair, numerical-policy change or TASK29A completion is claimed. Required
next attribution is pool/indirect-target and ordinary-process heap/layout,
not another assumption that matching instruction text proves equal cost.

## Precompiled driver repair after `40f2189c3` — not closure

Both matrix fixtures now compile calibration and sampling together inside
`experiment`, rather than executing a global calibration binding before
compiling `sample`. The chosen count is a runtime local. This removes a real
compiler-staging confound without changing any workload or numerical rule.
Thirty-six executable HOLSource/compiler scheduling assertions cover both
fixtures, including actual old-driver negative controls, and are integrated
into `Holmake check`.

Two complete fresh ten-pair B/B and B/C experiments retain fragment/0 CPU
**[1.014519, 1.032057]**, wall and GC failures. Collector/10000 CPU
**[0.988111, 1.032104]**, wall and GC are all inconclusive after unchanged
control admission. Neither result closes a historical cell or proves causation.
The complete earlier 43-failed/119-inconclusive grid remains preserved; changed
fixture code requires an entire affected-grid rerun before acceptance. The two
new experiments are not a replacement subset. Details and complete replays:
`evidence/task29/experiment-driver/RESULTS.md`.

The all-zero GC and equality-straddling B/B policy issues above require explicit
review, not silent threshold changes. Attribution/repair, the complete fresh
grid and TASK29B's allocation coverage/lineage/matrix are still unresolved.

## Explicit policy review — input required, not closure

`TASK29A_POLICY_REVIEW.md` and `evidence/task29/policy-review/review.json`
record a reproducible review of the unchanged executable contract. The new
`policy_review.py` fully re-admits the original `compile_single/0` B/B and B/C
archive and retains all 120 zero-GC samples plus positive-GC timer controls.
Synthetic contract examples and regression tests distinguish undefined ratios,
precise equality-straddling controls and passing exact positive equality.

The analysis is now recorded; policy-owner disposition is still required:
confirm whether exact zero/zero must remain nonpassing and whether B/B is
intended as a directional upper-CI<=1 requirement. No alternative contract is
selected or implemented. Repetitions that remain zero cannot resolve the first
obstruction; a narrow straddling interval alone does not prove instability.
This review is NOT a repair, fresh grid, heap/pool attribution or task
completion. All numerical failures, uncertainty and other requirements remain.

## Ordinary-process boundary attribution — not closure

`heap_attribution.py` and
`evidence/task29/boundary-attribution/RESULTS.md` re-admit all 162 historical
cells (6,480 processes / 136,960 batches) and both repaired-driver experiments
(80 processes / 1,560 batches). They preserve raw-archive/receipt bindings,
every calibration/sample count, boundary GC schedules, untimed counter gaps,
signed capacity differences and the original unchanged numerical decisions.
This is offline attribution of existing observations, not fresh timing.

The two repaired-driver cases have equal counts but different GC schedules and
heap capacities; every B/C sample boundary has +4,096 bytes of code capacity,
versus zero B/B difference. Independently recorded non-GC B/C intervals are
[1.009594, 1.019958] for fragment/0 and [1.003961, 1.039454] for
collector/10000.
These are diagnostic decompositions, not replacement gates or causal proofs.
Capacity does not bind instruction identity, live objects, pools or targets.
All original failures/uncertainty remain; no production repair is selected.

Full ordinary-process heap/pool/indirect-target attribution, the complete
fresh repaired-driver grid, an exclusive stable measurement environment and
explicit zero-GC/B/B policy-owner disposition remain unsatisfied. TASK29A is
NOT done.

## Fresh post-workload object/pool inspection — not closure

`RUNTIME_LAYOUT.md` and `evidence/task29/runtime-layout/RESULTS.md` now
retain actual instantiated object/code/capture/inline-pool dumps, rather than
only compiler text. Eight final structural processes cover fresh B/B and B/C
for both targeted repaired-driver cases. The private runner's original target
executes before a separately compiled postlude; ordinary sources/fixtures and
compiler printing are unchanged. Raw operands, aliasing, graph differences,
source/proof/runtime admission and complete rejected development output remain
available. The diagnostic suite cannot enter timing acceptance.

Actual `run` callable capture counts remain two words for fragment and three
for collector; selected root/build code sizes and address-immediate-masked
words match. Decoded inline loads bind actual caller/build/compiler targets,
not opaque printed names. B/C code alignment and collector reachable graphs
differ. Every process still has 213 split pools whose slots `showSize` omits.
Postlude compilation may move objects after timing: these are not boundary
snapshots, executed-target traces, complete graph equivalence or causation.
No production repair is selected, nor extra ordinary-path cost ruled out.

Both final archives replay and their real 13-test mutation suites pass.
Current-tree discovery passes 392 performance tests (five opt-in skips) and
196 compatibility tests. These checks do not close a numerical cell. All
historical/repaired-driver failures and uncertainty remain; a fresh passing
full grid, complete attribution, verified exclusive measurement environment
and explicit zero-GC/B/B policy-owner disposition are still required.
TASK29A is NOT complete; TASK29B remains separate.

## Complete post-workload pools — still not closure

`RUNTIME_POOLS.md` and `evidence/task29/runtime-pools/RESULTS.md` extend the
actual-object diagnostic without changing the sealed v1 tool or old archives.
Eight final fresh B/B and B/C structural processes supply and validate every
CODE object's actual inline/split pool. All 213 formerly omitted split pools
per process now have concrete owner/address/count/raw-slot records; their
1,326 words including headers are accounted separately from `showSize`.
Dummy split trailers are excluded from native reference scanning. Root/slot
paths retain object and pool alias mismatches rather than matching by name.

Native preload is limited to diagnostic workload processes and enabled only
around post-workload traversal. It changes layout; these are neither ordinary
measurement-boundary snapshots nor executed-target traces. Fourteen tests
including actual native controls and coherent archive mutations pass against
each real experiment; 421 performance tests (seven opt-in skips) and 196
compatibility tests pass. No timing observation is promoted or replaced.

A reproducible read-only environment capture explicitly reports
`exclusive_not_verified` and observes non-session concurrent CPU activity.
The sandbox has no enforceable exclusive host reservation; advisory locks
are not an exclusivity certificate. A quiet repetition would not certify one.
The required zero-GC/B/B policy-owner disposition also remains absent; no
contract change is authorized by these diagnostics.

The complete fresh passing repaired-driver grid, ordinary boundary and
executed-target/causal attribution, compatible repair if needed, verified
exclusive measurements and explicit policy disposition remain required.
`frag_record/0` still fails CPU/wall/GC; `compile_collector/10000` remains
inconclusive. TASK29A is NOT complete; TASK29B remains separate.

## Why every attempt failed, and the policy-owner disposition

The v1 rule (pass iff upper CI <= 1) tests whether the candidate is
measurably *faster*. With the actual `summarize.interval`/`decision`, ten
pairs of a candidate with no real difference (1% lognormal noise) give
pass 2.8%, fail 2.7%, inconclusive 94.5%. The B/B control is itself such a
comparison and must pass, and every cell needs CPU, wall and GC, so a
performance-neutral change cannot pass 162 cells; all-zero GC never can.
The historical grid agrees: B/B CPU passed in 9 of 162 cells. Every
earlier session could only add diagnostics, because the requirement it was
asked to meet was unreachable by construction and it could not change it.

The two open questions of `TASK29A_POLICY_REVIEW.md` were answered by the
policy owner on 2026-10-26: B/B is a control-validity window, not a
directional test, and GC is reported but not gated. The resulting contract
is `PROTOCOL.md`'s equivalence policy (version 2): δ = 3% on inclusive CPU
and wall, B/B intervals within [1/1.03, 1.03]. The historical grid,
replayed offline under it, would still show 8 CPU failures and about 47
inconclusive cells, so the rule change alone does not close anything.

The remaining historical failures were measurement artefacts of the
harness, not candidate cost:

- **Self-selected counts.** Each process calibrated its own batch count.
  In `compile_collector/10000`, candidate processes chose 16 and baseline
  processes 32, so fixed per-batch GC work was spread over half as many
  operations: CPU 1.20, GC 1.58. `task29a_grid.py` now gives every process
  of a cell one count, predeclared from develop/develop processes only.
- **GC-phase bimodality.** With short batches, per-op cost is bimodal
  (about 14.4 or 17 ms for the collector) depending on whether a major GC
  falls inside a batch. Startup GC histories differ deterministically
  between sides (15 vs 16 full GCs before the first batch) because the
  candidate loads one extra module (`SimpTracking`); the candidate process
  builds no extension module. Three samples per process let each median
  land on either mode.
- **Shared host.** Other HOL builds keep the load average at 17–25 on 32
  cores. An exclusive window is not available. The B/B validity window is
  the stability criterion: a cell is admitted only if its own develop/develop
  control resolves the margin.

A two-cell pilot with predeclared counts at the protocol minimum (10 pairs,
3 samples) was inconclusive on noise alone (fragment CPU [0.969, 1.035]
with a valid control; collector B/B [0.958, 1.089]). At 20 pairs and 5
samples both cells pass with valid controls: `frag_record/0` CPU
[0.984, 1.001], `compile_collector/10000` CPU [1.005, 1.022] (a real but
within-margin 1.4%; GC 1.16, reported). These pilots are design evidence
only (`evidence/task29a/pilot/`); the grid is rerun in full at 20 pairs and
5 samples.

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
