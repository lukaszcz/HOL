# Final simplifier compatibility report — TASK_17

**Accepted for the repaired contracts and required validation gates.**
All **58** plan items are mapped to code/docs and receipts in
[PLAN_AUDIT.md](PLAN_AUDIT.md). All twelve original regressions pass against
fixed develop. No missing required gate, open legacy-reachable divergence
or acceptance blocker was found. This is not universal equivalence.

## Repaired contracts and final opt-in boundary

- `traversedata_for_ss` again returns the unconditional legacy projection
  with a native `Traverse.REDUCER`, unchanged supplied dproc constructors,
  rules/relation/limit and no simpset traversal configuration. Legacy
  clients need no migration. Native traversal/rewrite runners remain native;
  no extra preparation/collector calls or installed-quota resets were added.
- Every `Excl` string uses strict develop literal deletion, like `-*`:
  prefixes and missing names never select a strategy namespace. Ordered
  history retains unmatched deletions and reparses strict names in the
  current theory. Split/case extended suppression now survives replay.
- Ordinary `simpLib`/`splitLib` loading leaves persistent `split` ownership
  unclaimed and preserves foreign attributes, theorem sets and syntax.
  Context-aware ownership and theory-data dispatch survive replay/reload.
  Private allocations remain; namespace neutrality does not mean no state.

Final extension APIs (see [API_MIGRATION.md](API_MIGRATION.md)):

- `xtraversedata_for_ss` supplies the configured data/configuration pair;
  normally use the complete pair with `Traverse.XTRAVERSE`. Child-first and
  explicit depth/order/subgoaler/solver behavior remain available.
- `simpLib.ExclX` / `markerLib.ExclX`, `destExclX` and `DExclX`, backed by
  distinct `marker$ExcludeX`, explicitly select rule/solver/looper/split/case
  targets and diagnose unmatched/ambiguous targets. No Excl sentinel exists.
- `splitLib.enable_split_attribute ()` explicitly enables persistent
  registration. Producers load and export dependency `splitPersistLib`
  before the **earliest** split-bearing theory's replay; ordinary simpLib
  is not that dependency. `splitLib.exclude_split` persistently retracts a
  named rule. Pure/local/TypeBase splitting does not need registration.
  After restoring a pre-opt-in Context, explicitly initialize again.

## Commands and outcomes

Exact expanded argv, timestamps, hashes, exits and raw logs are retained in
`results/task14/`, `results/task15/`, `results/task16/`, and the final audit
`results/task17/checks.json`. Reports below explain scope and failed-attempt
triage; no required failure is ignored or counted as a pass.

| Gate / command | Outcome |
| --- | --- |
| Pinned `run.py`, `fresh_load.py`, `paired_report.py` | All 17 ordinary inputs and five clean-load scenarios pass; 3251 equal ordered observation pairs. Original unchanged develop suite: 73 OK/lane. |
| Normal Holmake `marker-selftest.log`, `simp-selftest.log` (early `bin/hol.state0`) | Fresh execution: 72 / 630 OK, including migrated extension assertions. |
| Holmake `traversal-contracts exclusion-contracts fresh-load-regressions split-registration split-persistence` | Fresh execution: 1345 OK; six clean-load scenarios, registration, six import/owner cases and actual heap-save/reload. |
| Eight normal downstream Holmake selftest log targets | Marker, simp, arithmetic, reduction, boss, integer, integer/testing and real all pass freshly. |
| `bin/build -t --seq=tools/sequences/upto-parallel` | Exit 0; routine selftest-enabled gate. |
| `bin/build -t -F` | Exit 0; all 87 expected visits in order, 34 fresh selftest logs, 650 theory timing entries; full incremental level-1 sequence. |
| `PYTHONDONTWRITEBYTECODE=1 python3 src/simp/compatibility/results/task17/check.py` | Exit 0; gate/input integrity, paired-report reproduction and negative controls, frozen inputs, whitespace and cleanup checks. |
| `git diff --check`; project `h4pedant` on affected source/probe directories | Exit 0; explicit changed-text scan also covers tests/docs/JSON omitted by pedant. |

Detailed results: [PAIRED_VALIDATION.md](PAIRED_VALIDATION.md),
[DOWNSTREAM_VALIDATION.md](DOWNSTREAM_VALIDATION.md),
[FULL_REGRESSION.md](FULL_REGRESSION.md).

## Final-candidate continuity

Entry HEAD: `bc05969beb79cf2cefa76a260da01b0729628388`.
Differential implementation pin: `5b5f07df2`; fixed reference:
`cccaa27d7099cbadc886983020cbe745db7793f3`. TASK_14's added probes/helpers
were included in its successful tests. TASK_15 tested `4d7bf126d`;
TASK_16 tested `34ba6e174`. Later commits changed only evidence/docs/metadata,
not library behavior, probes or build recipes. T17 rechecked all **7924**
T16 candidate-file hashes, all **118** T15 input hashes and both T14
manifests' branch-source/input inventories. Required results apply to this final
implementation; no late change invalidated a gate. This final landing adds
only reports/audit evidence and index/progress, not compiled sources/tests.

## Provenance limits and untested scope

- Differential lanes are **mixed-source**: private pinned simplifier/marker
  libraries, shared host kernel/early heap/generated markerTheory and other
  dependencies. They are not independent clean repository builds. The
  uninstrumented original suite supplies assertions/raw output, not a trace
  of every internal callback. Only documented export timings and lane-local
  load paths differ in final raw paired logs; relevant warnings/exceptions/
  callback staging/order/frequency are not normalized away.
- Routine/full builds are incremental Linux aarch64 Poly/ML 5.9.2 stdknl
  level-1 builds, not clean builds, higher test levels or other ML/kernel
  configurations. Existing non-fatal virtual-target and HolSmt compiler
  diagnostics are documented. Unconfigured external cvc5/Yices/Z3 cases
  did not run. Optional pandoc/dot rendering was skipped in the full build;
  T13 separately evaluated/rendered the 15 API docfiles with a temporary
  Pandoc. Ignored generated help text may remain stale when rendering is
  skipped; corrected tracked doc sources are authoritative.
- Arbitrary user callbacks, all parser/strategy combinations, runtime I/O,
  concurrent initialization and arbitrary asynchronous rollback are not
  exhaustively tested. Finite green suites do **not** prove universal
  observational or callback equivalence.
- No concrete new-only splitter algorithm issue was identified here.
  Exhaustive splitter correctness/cache-retention bounds are separate
  untested extension scope, not open legacy compatibility findings.

## Cleanup and handoff

No task-owned copied trees, caches, temporary heaps, downloads or scratch
outputs remain; compact unique inputs/receipts are retained. Normal checkout
build products and unrelated/caller-owned artifacts (including the original
`/tmp/hol-simp-compat.H6G7y2/` investigation) are untouched. TASK_17 adds the
ledger, this report and reproducible final checks; all prior APIs/assertions
remain unchanged. Progress/index identify this report and one TASK_17
completion-log line. **All tasks landed; next unblocked task: none.**
