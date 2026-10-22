# TASK17 authorized focused campaign — 2026-10-22

**Completed; exclusive build/benchmark window released after final checks.**
No production/existing-runner edits and no commit. All task changes/evidence
are in `src/simp/tests/exclusions/performance/`.

## Final observations

- Current **then** pinned-baseline control, serially: **10 fresh AB/BA pairs
  each**, 20 processes each, three samples plus one fixed-count calibration
  for each of 44 workload/size keys. Both manifests have `success=true`;
  all 40 receipts are accepted, with exact proofs/hypotheses, ordered names,
  persistence, consumption, callbacks, footer/exit and loaded-path checks.
- Same `../final-iterations.json` on both campaigns/sides. All 7,040 timed
  calibration/sample batches retained. Wall batch duration min/median/max:
  current **0.125099 / 0.204305 / 0.926873 s**; control
  **0.128578 / 0.2072535 / 0.734381 s**. No sample/outlier removal.
- Per-process sample medians, paired log ratios, Student individual and
  44-key family intervals; independent control contrast. Metrics stay
  separate: inclusive CPU, wall, non-GC CPU, GC CPU, user CPU, system CPU.
  Family coverage is per metric/analysis, not joint over all metrics.
- CPU/wall: **43/44 current family intervals unresolved**, one strictly below
  one (`empty_list.1000`: CPU ratio 0.997425, interval
  [0.994940, 0.999918]). Control CPU/wall: **44/44 unresolved**.
  Current CPU point ratios range **0.971773–1.020229**. These are **not parity
  or an acceptance tolerance**. Independent contrasts are also unresolved
  for 43/44 CPU/wall keys; the empty-list key remains below one.
- **GC-only slower family intervals remain visible**, including after the
  independent control contrast. They are NOT waived by source/codegen
  correspondence or by unresolved total-CPU intervals:

| Workload | Current GC ratio | Current GC family95 interval | Control-contrast interval |
| --- | ---: | --- | --- |
| `replay.1000` | 1.203343 | [1.124123, 1.288145] | [1.084813, 1.275250] |
| `missing.10000` | 1.222414 | [1.195981, 1.249431] | [1.192655, 1.260411] |
| `matching.10000` | 1.328003 | [1.297735, 1.358976] | [1.296252, 1.386855] |
| `qualified.10000` | 1.068908 | [1.036566, 1.102259] | [1.035487, 1.105006] |

  There are also four current GC intervals below one, 31 unresolved and
  five unresolved-zero-timer GC keys. System CPU has four zero-timer keys.
  Control user CPU resolves slower at `empty_list.1000` (ratio 1.003104,
  family95 [1.000068, 1.006148]); control GC has no resolved slower key.
  All rows, including all individual intervals, are in the compact summary.

## Source and compiler correspondence

Pinned develop: `cccaa27d7099cbadc886983020cbe745db7793f3`.
Current selected revision: `ba366bcae12c373cdfadcc982ac0319f08045a05`
with working sources snapshotted/sealed. Whole ordinary source/signature
bytes match pinned develop, not just selected textual extracts:

- `simpLib.sml`: 44,419 bytes,
  `ee324439ac66cd14858d6ea5dc45a867d44fa6762298f1cf7df45b13aed6c3cd`.
- `simpLib.sig`: 10,369 bytes,
  `d1979668da105341e6e97e900848a2d382eaac3a50650c89bbdeae8ee3689666`.

Fresh source-tied codegen current **then** baseline-control inspections use
the maintained compiled-core/fragments assembly infrastructure unchanged,
with a new local adapter/trigger. Both final collections pass provenance,
fixture and artifact checks. Full compiler extents, source bytes, selected
optimized/backend/ICode records and native bodies are retained.

Exact source/codegen links (pinned source line numbers):

- 291–307: name matching; emitted `simpLib.name_match(3)` and its `check1`.
- 309–323: literal parser + one net filter; emitted
  `filter_net_by_names(2)`, `munge_pat` specializations and predicate closure.
- 325–327: dproc matching/filter, inlined into deletion/replay callers;
  no invented standalone body or zero-work charge.
- 329–342: `-*` and reverse-order `DELETE_EVENT` recording, emitted `-*(1)`
  (optimized stdout lines 86512–86639 in final baseline extent).
- 646–682: replay fragment addition/maker compilation, emitted `++(2)` and
  `++(1)`, with `mk_named_rewrs`/`reduce` bodies retained.
- 686–718: history fold/filter and replay/restoration, inlined history build
  inside emitted `remove_ssfrags(2)` (optimized stdout lines 190140–190773),
  plus its curried wrappers. Its optimized tree names `++(2)` and
  `filter_net_by_names(2)`, retaining replay's deletion path.

**All 25 selected native occurrences** (19 `simpLib` bodies plus selected
library/initializer bodies) are identical after only adjacent ADRP/LDR
pool-relocation normalization in current and control. Raw machine words and
pool operands are retained; this is not exact raw-byte identity. All 17
selected optimized trees agree exactly in current; 129/133 ICode and 14/15
backend records agree exactly. The five differing non-native records are
whole-initializer records changing the named reference
`Cond_rewr.with_tracking(1)` to `SimpTracking.with_tracking(1)`, not differences
in delete/replay function bodies. They remain exact diffs, not normalized
away. Control non-native records all agree. Some raw assembly records differ
by pool relocation even in control.

Optional standalone bodies not emitted on either side:
`build_from_history`, `dphas_name_from`, `filter_dprocs_by_names`, `setexcluded`.
Their callers/full extent remain archived. Static local correspondence is
not cumulative allocation, dynamic instruction counts, identical runtime
state, timing parity, or an explanation dismissing the GC-only slower rows.

## Failures, corrections and reruns (nothing cherry-picked)

1. `initial-current/`: rejected first baseline process, before measurement
   rows. The proof fixture used raw `TRAVERSE`, which may fail with `NO_CONV`
   for unchanged terms. Fixed the fixture with public conversion combinators
   `TRY_CONV (QCONV ...)`, as used by normal simplification. Exact expected
   theorem/hypothesis checks remain, so missed required rewrites still fail.
   No production change or assertion removal.
2. `second-current/`: complete passing 10-pair exploratory current campaign
   with the initial schedule. Small batches (as short as 3 ms) prompted a
   common longer fixed schedule; this run is not mixed into final inference.
   No exploratory control was run: both final campaigns were run fresh under
   the revised common schedule instead. All exploratory raw receipts now live
   losslessly in `second-current/receipts.tar.xz`; the manifest is unchanged.
3. `codegen-current/`: first codegen attempt rejected the assumption that
   `build_from_history` has a standalone emitted tree. Compact unique failure
   metadata/protocol is retained in `codegen-current/failure.json.gz` beside
   the original failing manifest. Redundant bulk compiler diagnostics,
   failed derived native output and duplicate products were removed offline;
   the original receipt/stdout seals
   and exact rejection survive, but that failed raw receipt is deliberately
   not reconstructible. Both compaction stages are recorded in
   `archive-compaction.json` and `previous-inventories.json.gz`. Changed only
   the local adapter to report the helper as optional/inlined, retaining the
   required replay caller and its
   exact trees. Both final codegen inspections were rerun after that change.
4. Final timing and codegen campaigns all pass after their respective fixture/
   runner fixes. Final offline suites: **13 performance + 2 adapter tests**.
   Source audit, archive recheck and whitespace checks pass.

## Archive / reproduction

- `final-current/`, `final-control/`: compact compressed raw receipts and
  provenance manifests. These are the only final timing inputs.
- `final-analysis.json.gz`: losslessly compressed full analysis, all process
  medians/paired ratios/raw sample durations and independent contrasts.
- `compact-summary.json.gz`: every workload/metric's ratios and individual/
  family intervals for current, control and contrast, without duplicate raw
  process data. Unresolved and zero-timer statuses retained.
- `codegen-*-final/`: final codegen artifacts and unchanged compressed
  manifests; source spans, exact record diffs, normalization/static counts.
  Exact duplicate source/selected-record copies resolve through aliases in
  `archive-compaction.json`. No selected native/tree record is dropped.
- `compiler-extents.tar.xz`: all four full final compiler extents, lossless
  solid compression (652,824 bytes instead of 8,054,036 bytes of separate
  gzip files). Members are the original *uncompressed* text, with original
  paths minus `.gz`; recheck reconstructs original gzip bytes/seals in memory.
- `second-current/receipts.tar.xz`: all 20 exploratory raw timing receipts
  plus both build receipts, likewise lossless shared compression (246,344
  bytes). No exploratory observations are discarded or mixed into finals.
- `archive-compaction.json`: original/compressed/uncompressed hashes, archive
  member mappings, exact aliases and the failed-bulk removal/replacement.
  `previous-inventories.json.gz` retains both pre-cleanup checksum inventories
  and the earlier failed-extent compaction receipt.
- `final-source-correspondence.json`, `final-tests.log`, `recheck.log`.
- Reproduction commands are in each timing manifest's `command` and
  `../assembly/README.md`; use new output directories. Recheck archived raw
  timing protocols and codegen artifacts offline from repository root:

  ```sh
  python3 -B src/simp/tests/exclusions/performance/evidence/recheck.py
  ```

Lossless gzip was applied to the full analysis and codegen manifests after
collection. The later offline compaction preserves every final raw timing,
GC diagnostic and selected codegen observation, all four full final extents,
and all exploratory timing. Only rejected bulk compiler output was pruned. Collection manifests remain unchanged; their old paths/seals resolve
via the explicit compaction receipt, not silently edited collection claims.
`SHA256SUMS` inventories current physical files; `GC_SHA256SUMS` inventories
follow-up files. Run either from the performance directory with `sha256sum -c`.
See `COMPACTION_REVIEW.md` for the independent bounded-acceptance assessment.
Private trees/heaps were removed by the runners on success/failure; no agent
caches or launchers are retained.

Scope: shared `hol.state0` and non-simplifier dependencies, private selected
simplifier sources, one GC thread; **not independent clean repository builds**.
Affinity/load are recorded, not controlled beyond the authorized serial
window (load averages changed materially). The endpoint/callback fixture is
focused coverage, not the separate full TASK17 semantic suite. **No uncertain
parity, whole-plan acceptance or whole-TASK17 completion is claimed.**
