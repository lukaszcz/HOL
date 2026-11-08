# TASK29A — close the isolated fragment/compiler numerical gate

**Outcome (2026-10-30): complete by policy-owner disposition.** See
"Attribution and policy-owner disposition" near the end. The earlier
sections are kept as recorded.

**Amendment (2026-11-05):** the exclusive-environment requirement named in
the earlier sections' lists of what remains required was waived by the
policy owner; the host is shared. The waiver changes no recorded text,
number or measurement below.

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

## Equivalence-policy grid at `6f62229c0` — interrupted, FAIL, not closure

`task29a_grid.py run --candidate 6f62229c0 --pairs 20 --samples 5` started
2026-10-26 08:25 UTC. It died at 12:31 in cell 21 of 162
(`frag_record/10`). The host's shared root filesystem filled up (726 GB,
almost all of it other projects' build trees), and `OSError: [Errno 28]`
was raised while the driver round-tripped that cell's archive. The 20
completed cells are in `evidence/task29a/grid-partial/`. That directory
holds their sealed archives, the inventory, `run.log.gz` (including the
failing cell's traceback) and `replay.log`. Every one of the 20 cells was
protocol-complete, and `task29a_grid.py replay --partial --output
evidence/task29a/grid-partial` recomputes each decision exactly; it exits
2 because there is no grid decision. The truncated `frag_record/10`
archive was never verified and is not retained. Disk pressure did not
reach a completed cell: each one passed the in-run recomputation and the
offline replay.

Offline replay first found a driver defect. Analyses key pair rows by
integer, while an archived report stores them as strings. With more than
ten pairs, `json.dumps(sort_keys=True)` orders the two differently
(`"10" < "2"`), so `replay` rejected every 20-pair archive with "changed
point analysis". The in-run check compared in-memory objects and so did
not notice; ten-pair historical archives are unaffected. `check_report`
now compares both sides as stored (`canonical`). A regression test using
real string keys fails on the `6f62229c0` driver. `replay` accepts that
driver's seal (`DRIVERS`), because only the comparison and `--partial`
changed.

| Cell | N | CPU 95% CI | Wall 95% CI | B/B CPU CI | GC median | Decision |
|---|---:|---|---|---|---:|---|
| frag_create-0 | 67108864 | 0.753-0.899 | 0.753-0.899 | 0.943-1.039 | 0.93 | inconclusive (B/B outside window) |
| frag_create-1 | 33554432 | 0.985-0.998 | 0.987-0.998 | 0.995-1.014 | 1.01 | pass |
| frag_create-10 | 4194304 | 0.979-1.009 | 0.979-1.010 | 0.988-1.012 | 0.94 | pass |
| frag_create-100 | 1048576 | 0.951-1.027 | 0.951-1.027 | 0.945-1.005 | 1.01 | inconclusive (B/B outside window) |
| frag_create-1000 | 131072 | 0.992-1.022 | 0.992-1.022 | 0.980-1.007 | 1.01 | pass |
| frag_create-10000 | 16384 | 1.094-1.110 | 1.093-1.110 | 1.007-1.045 | 1.00 | **fail** |
| frag_named-0 | 67108864 | 0.884-1.081 | 0.885-1.081 | 0.909-1.018 | 1.06 | inconclusive (B/B outside window) |
| frag_named-1 | 33554432 | 0.990-1.011 | 0.990-1.012 | 0.991-1.014 | 0.99 | pass |
| frag_named-10 | 8388608 | 0.970-1.010 | 0.970-1.008 | 0.996-1.023 | 0.99 | pass |
| frag_named-100 | 1048576 | 0.985-1.061 | 0.987-1.061 | 0.985-1.048 | 1.00 | inconclusive (B/B outside window) |
| frag_named-1000 | 131072 | 0.995-1.027 | 0.995-1.027 | 0.974-1.013 | 1.00 | pass |
| frag_named-10000 | 16384 | 1.069-1.096 | 1.069-1.097 | 0.985-1.037 | 1.00 | **fail** |
| frag_named_rules-0 | 33554432 | 1.014-1.024 | 1.014-1.024 | 0.993-1.011 | 1.07 | pass |
| frag_named_rules-1 | 8388608 | 1.053-1.064 | 1.051-1.064 | 0.994-1.002 | 0.63 | **fail** |
| frag_named_rules-10 | 2097152 | 1.066-1.092 | 1.066-1.092 | 0.994-1.007 | 2.11 | **fail** |
| frag_named_rules-100 | 131072 | 0.973-1.002 | 0.973-1.002 | 0.995-1.009 | 1.11 | pass |
| frag_named_rules-1000 | 16384 | 0.995-1.000 | 0.993-1.000 | 0.996-1.002 | 0.93 | pass |
| frag_named_rules-10000 | 1024 | 0.995-1.005 | 0.995-1.005 | 0.994-1.005 | 1.19 | pass |
| frag_record-0 | 33554432 | 1.000-1.016 | 1.001-1.014 | 0.987-1.001 | 0.95 | pass |
| frag_record-1 | 33554432 | 0.990-1.009 | 0.990-1.008 | 0.986-1.008 | 1.01 | pass |

Ratios are candidate/develop per operation; GC is reported, not gated.
Of the 20 cells, 11 pass, 4 fail and 5 are inconclusive. A fail is final
for the run, so this grid is a **FAIL** whatever the remaining 142 cells
would show. `frag_named_rules/0` (+1.4–2.4%) and `frag_record/0`
(+0–1.6%) pass with real, within-margin slowdowns.

What the archives show about each class. Production `src/simp` at
`6f62229c0` is byte-identical to the historical candidate `18e4a1ecb`.
The harness differences are the predeclared count and the driver body
moved into `experiment()`.

- **Inconclusive cells.** In every one, the cell's own develop/develop
  control lies outside the window. In `frag_create/0` each fresh process
  settles at about 20, 24 or 28 ns/op, with 5–15% spread inside a process.
  The historical grid measured the same cell at 16.0–16.9 ns with 1–4%
  spread. The host load during this run was 10–27. The candidate's 0.84 in
  that cell is the same noise (historically it was 1.015), not a speedup.
- **`frag_create/10000`.** Per-op cost rises about 25% over the five
  batches inside every process, on both sides. 19 of 20 candidate-selection
  candidate processes start about 12% slower. They began their batches with
  a 16 MB heap after 31 full GCs, against the baselines' 16 MB after 30.
  The one candidate process at develop speed began with a 22 MB heap.
  Historically (N = 8192, self-selected) this cell was [0.949, 0.993].
  This is the startup-GC-history class seen in `compile_collector/10000`,
  but it is unproven. The B/B control is outside the window too, which
  never excuses a fail.
- **`frag_named/10000`.** It also failed historically ([1.038, 1.065],
  valid control). This is consistent across runs and is the most likely
  genuine candidate cost.
- **`frag_named_rules/1` and `/10`.** These are clean fails with tight
  valid controls. Every candidate process runs about 67 ns/op against
  develop's 63 ns in `/1`, and both sides start from an identical heap
  state (10 MB, 39 full GCs). The historical runs at half the present
  count were neutral ([0.983, 1.013] and [0.985, 1.008]). Whether the
  doubled count exposes a real cost or a count-dependent artefact has not
  been tested.

The predeclared diagnostics that followed are in the next section.

## Fail attribution: code layout (2026-10-26) — diagnostic, not closure

Four predeclared runs on the four failing cells, at 20 pairs and 5
samples (`evidence/task29a/attribution/`, with `PLAN.md` and a README):

- **R1** (same candidate, fixed layout) reproduces all four fails.
- **R2** uses probe `8d4a84417`, which restores develop's `Cond_rewr.sml`
  byte for byte. `frag_named_rules/1` and `/10` pass, while
  `frag_create/10000` (1.17–1.20) and `frag_named/10000` (1.23–1.26) fail
  by a larger margin. Those two cells execute an ordinary path identical
  to develop's: `simpLib` is byte-identical and the fragment constructors
  never reach `Cond_rewr`. Their user time per operation still differs by
  36%, with equal system and GC time.
- **R3** (historical half count) still fails `frag_named_rules/10`, so the
  doubled count is not the cause.
- **R4** randomizes each process's code layout (seed `task29a-r4`).
  `frag_named_rules/1` [1.004, 1.016] and `/10` [0.985, 1.015] pass, as
  does the sanity cell `frag_record/0` [0.993, 1.013].
  `frag_create/10000` [0.956, 1.052] and `frag_named/10000` [0.952, 1.069]
  are inconclusive: under randomization their B/B controls (0.977–1.060
  and 0.965–1.071) are outside the window at 20 pairs.

The code-area size at batch start tracks speed. One develop process in R1
had a different code size from the other develop processes, and it is an
outlier too. Under randomization, develop processes that get the same
padding count mostly run within 1–2% of each other, while different counts
spread them by about 8%. The fixed-layout fails are therefore layout
artefacts: any source change that moves later code shifts these cells by
several percent either way. They are not an ordinary-path cost of the
candidate.

**Method change.** This amends the measurement method, not the policy:
seeded per-process layout randomization, plus a predeclared second stage
that adds pairs where the develop-only control is too wide (`PROTOCOL.md`,
"Code-layout randomization and second stage"). The policy owner should
confirm the amendment. The work list below asks for "the unchanged
fail-closed protocol", and an unchanged fixed-layout protocol cannot
separate a candidate from its layout on this host.

**Full rerun (predeclared before it starts).** The first stage is
`task29a_grid.py run --candidate 6f62229c0 --pairs 20 --samples 5
--layout-seed task29a-grid-1` over all 162 cells. The second stage is
`task29a_grid.py extend` on that grid (seed `task29a-grid-1-ext`). Both
use `--resume` only after an infrastructure failure. The final decision
is the second stage's `decisions.json`, whatever it shows. Results are
added below when the run completes.

## Layout-randomized two-stage grid (2026-10-30) — INCONCLUSIVE, disposed

The predeclared rerun is complete (`evidence/task29a/grid/`, with a
README). It ran from 2026-10-26 17:14 to 2026-10-30 09:42 UTC. Infrastructure
interrupted it four times: the shared root disk filled twice, another host
process deleted the `/tmp` lock, and there was one planned stop to move that
lock into `.agent-files/` (`9ee8d00bd`). Each resume replayed every recorded
cell exactly. Unrecorded cells were measured again from scratch; no cell was
selected, dropped or repeated. From cell 11 on, scratch trees lived in the
sandbox's `/dev/shm`. That is a storage location only. Both stages replay
offline, and their logs are in the evidence directory.

- **Stage 1** (162 cells, 20 pairs): 124 pass, 38 inconclusive, 0 fail.
- **Stage 2** remeasured the 35 cells whose develop/develop control was
  outside the window. Each got the pair count computed from its control
  alone: 40–120 pairs, 3200 pairs in all.
- **Grid decision** (`stage2/decisions.json`): **144 pass, 18
  inconclusive, 0 fail**. Its status is `inconclusive`.

No cell fails. Inconclusive is not pass, so the gate is not met. The 18
cells (CPU ratio candidate/develop and B/B CPU interval, final stage):

| Cell | Pairs | CPU 95% CI | B/B CPU CI | Why inconclusive |
|---|---:|---|---|---|
| frag_create-0 | 120 | 0.933-1.029 | 0.951-1.030 | B/B outside window |
| frag_create-10000 | 100 | 0.965-1.021 | 0.991-1.039 | B/B outside window |
| frag_named-0 | 120 | 0.943-1.020 | 0.966-1.040 | B/B outside window |
| frag_record-10000 | 120 | 0.964-1.018 | 0.968-1.023 | B/B outside window |
| frag_update-1000 | 120 | 0.988-1.034 | 0.989-1.035 | B/B outside window |
| frag_update-10000 | 120 | 0.985-1.047 | 0.968-1.044 | B/B outside window |
| frag_duplicate-10000 | 80 | 0.984-1.018 | 0.988-1.031 | B/B outside window |
| frag_ac-0 | 120 | 0.923-1.002 | 0.947-1.041 | B/B outside window |
| frag_ac-1 | 120 | 0.958-1.023 | 0.970-1.033 | B/B outside window |
| frag_ac-10 | 120 | 0.930-1.041 | 0.921-1.028 | B/B outside window |
| frag_ac-100 | 120 | 0.975-1.039 | 0.939-1.045 | B/B outside window |
| frag_ac-1000 | 120 | 0.968-1.052 | 0.950-1.041 | B/B outside window |
| compile_bounded-10000 | 80 | 0.936-0.979 | 0.990-1.031 | B/B outside window |
| frag_named_merge-10000 | 120 | 1.021-1.067 | 0.984-1.030 | CI crosses 1.03 |
| frag_merge-100 | 20 | 1.002-1.037 | 0.995-1.010 | CI crosses 1.03 |
| frag_typebase-0 | 20 | 0.988-1.037 | 0.981-1.011 | CI crosses 1.03 |
| frag_update-0 | 90 | 0.992-1.032 | 0.984-1.016 | CI crosses 1.03 |
| frag_create-10 | 20 | CPU pass; wall 0.986-1.030 | 0.998-1.016 | wall CI crosses 1.03 |

There are two classes.

- **Control-limited (13 cells).** Even at the 120-pair cap, the cell's own
  develop/develop interval stays outside [1/1.03, 1.03]. Under layout
  randomization, the process-to-process spread in these fragment cells,
  mostly `frag_ac` and size 0 or 10000, is wider than the margin. More
  pairs on this host cannot resolve them. None shows a candidate cost:
  every candidate interval contains 1 or lies below it.
  `compile_bounded/10000` is 2–6% faster.
- **Valid control, CI crossing the margin (5 cells).** These cells can be
  measured at the margin, but their intervals cross 1.03.
  - `frag_named_merge/10000` is the only cell with a measurable slowdown:
    1.021–1.067 (median about 1.04) at 120 pairs, with a valid control.
    Its 20-pair stage-1 interval was 0.987–1.117.
  - `frag_merge/100` (1.002–1.037) is also wholly above 1, but at only 20
    pairs.
  - The others contain 1.

  The predeclared extension rule only remeasures cells with an invalid
  control. So `frag_merge/100`, `frag_typebase/0` and `frag_create/10`
  stayed at 20 pairs. That is a gap in the rule; it was noticed during
  stage 1 and deliberately not changed mid-run.

None of the four fixed-layout fails of the earlier grid fails under
randomization. `frag_named_rules/1` and `/10` pass in stage 1, and
`frag_named/10000` passes after more pairs. `frag_create/10000` (formerly
1.094–1.110) is now 0.965–1.021, inconclusive only because its control is
too wide. This matches the layout attribution above.

**Status when recorded.** TASK29A was **not complete**; the disposition
below closes it. The predeclared measurement is
finished and its decision is final for this candidate and method. Closing
the gate now needs a decision from the policy owner that measurement alone
cannot supply:

1. confirm the layout-randomization/second-stage amendment;
2. decide how cells whose own develop/develop noise exceeds the margin on
   the available host are treated. Either they stay blocking, or an
   exclusive, quieter environment is provided;
3. decide on the five valid-control cells, above all `frag_named_merge/10000`.
   One option is a predeclared further stage for valid-control cells that
   cross the margin. Another is source attribution of a possible 2–7%
   cost in named merges at size 10000.

## Attribution and policy-owner disposition (2026-10-30) — COMPLETE

The policy owner answered the three questions above on 2026-10-30:

1. The layout-randomization/second-stage amendment is **confirmed** as the
   TASK29A measurement method.
2. **Control-limited cells do not block.** A cell whose own develop/develop
   interval is still outside the window after the second stage is listed as
   unresolvable on the measuring host, with its intervals, as long as it
   has no fail. This applies to 13 cells.
3. The five valid-control margin cells were **attributed first, then
   accepted** as attributed. The attribution is below.

The executed source is identical on both sides: production `simpLib.sml`
is byte-identical between baseline `cccaa27d7` and candidate `6f62229c0`.
`named_merge_ss` and `merge_ss` live there. All figures come from the
archived process records (`stage2/frag_named_merge-10000.json.xz` and the
other cells' archives).

- **`frag_named_merge/10000`** (1.021–1.067 at 120 pairs). Each timed
  batch starts from a collected 23 MB heap, and Poly/ML grows the
  allocation area during the batch. User time steps with that growth:
  batches whose area stays below 600 MB run at about 38 µs/op of user
  time with many partial collections. Batches that reach 600 MB or more
  run at about 29 µs/op, with system time rising with the area. Matching
  batches by band (median CPU µs/op, batches):

  | Band | Experiment | Baseline slot | Candidate slot | Ratio |
  |---|---|---|---|---|
  | < 600 MB | develop/candidate | 40.67 (147) | 41.15 (221) | 1.012 |
  | ≥ 600 MB | develop/candidate | 36.84 (453) | 37.78 (379) | 1.025 |
  | < 600 MB | develop/develop | 40.24 (138) | 40.40 (194) | 1.004 |
  | ≥ 600 MB | develop/develop | 37.61 (462) | 37.78 (406) | 1.004 |

  Most of the cell's ratio is the band mix: 37% of candidate batches stay
  below 600 MB, against 25% of develop batches in the same pairs. At
  process level, 60 of 120 candidate processes are in the slow mode
  against 38 of 120 (Fisher p = 0.006). The B/B control leans the same
  way with develop in both slots: 32% against 23% of batches, and 54
  against 41 processes (p = 0.11). The mode is a runtime heap-growth
  outcome and is not fixed by the layout padding: 36 of the 85 develop
  padding counts that occur more than once produce both modes. The
  remaining within-band difference (1–2.5%) is below the 3% margin. The
  merge code is unchanged, so no ordinary-path source change explains
  it.
- **`frag_merge/100`, `frag_typebase/0`, `frag_update/0`,
  `frag_create/10`.** There is no bimodality, and the final allocation area
  does not track CPU (|Spearman| ≤ 0.3). Median per-process CPU changes by
  +1.2%, +1.2%, +0.6% and −0.5%. The intervals cross 1.03 only through
  sampling noise; three of these cells had 20 pairs.

`task29a_grid.py dispose` implements the disposition. It replays the
two-stage grid, then classifies each final cell: pass; unresolvable (all
open metrics are inconclusive only because of the B/B control);
attributed (an explicit list of five cells with reasons, checked against
the open cells); fail; or blocking. A fail, a protocol failure, a
retained-scaling miss, or any other inconclusive cell still blocks.
`evidence/task29a/grid/stage2/disposition.json` records the result, and
`dispose.log` shows it was replayed:

    python3 -B task29a_grid.py dispose --output evidence/task29a/grid/stage2

**TASK29A gate: PASS by policy-owner disposition.** The tally is 144 pass,
0 fail, 13 unresolvable on this host and 5 attributed, with the retained
slope passing. This closes the isolated fragment/compiler timing gate
for Linux/aarch64 Poly/ML 5.9.2 on this shared host. It is not a
universal or independent-build claim. It supersedes the acceptance text
below wherever that text asks every cell to pass with admissible controls
or asks for an exclusive host. TASK29B's cumulative-allocation
prerequisite remains separate and open, so TASK29 stays blocked on it.

## Work and acceptance

Amended on 2026-10-30 by the policy owner: see "Attribution and
policy-owner disposition" above. The original text follows unchanged.


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
