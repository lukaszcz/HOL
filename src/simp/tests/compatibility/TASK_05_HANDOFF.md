# TASK_05 handoff — tactic construction, callback and proof contracts

Landing source identifier: **TASK_05-staging-contracts-v1** (this commit).
Starting/measured HEAD: `54c4882ba04dd788bc6fee104e68b2f5c0335ce2`.
Develop: `cccaa27d7099cbadc886983020cbe745db7793f3`.
Reviewed: `cf1f863b4e5a9712ce1b179f18274eb3451f3954`.
No production simplifier sources differ between reviewed and measured HEAD;
no production sources/API/control were changed in this task. The final source
commit changes tests/harness/docs/evidence only. Exact selected Git blobs,
input hashes, private source/products, actual loaded paths, shared dependency
hashes, runtime/heap/tool hashes, options and exits are in each manifest/receipt.
The preserved TASK_03 handoff was the dependency input; its results were not
substituted for this task's fresh observations.

## Acceptance receipt

**All bounded TASK_05 acceptance criteria are satisfied.** This is executed
contract capture, **not a repair or a compatibility pass**. TASK_18 still owns
the intentional current-source reds and legacy tactic repair. Generic
`markerLib`, `markerSyntax`, `Ho_Rewrite` and `BoundedRewrites` were inspected
read-only and match the pinned develop source bytes.

- Added an independent 43-scenario SML suite, separate from the immutable
  compact reproducer. Each saved tactic separates construction, first use,
  second use, and every returned proof reconstruction. Prebuilt arguments and
  between-stage hooks stay outside measured stages.
- Develop's 57 real reconstructions, 60 checks and 726 ordered result events
  pass exact sealed expectations. Reviewed/current have 54 reconstructions,
  57 checks and 718 events, classified **expected-candidate-red**. Across eight
  new-suite executions, **447 real validation calls** ran with kernel-proved
  residual goals; neither pretty goals nor `VALID` oracle surrogates suffice.
- Primitive counts and ordered printer logs are recorded for construction,
  each use and reconstruction. Exceptions preserve full HOL provenance/message,
  exact arbitrary-printer exception constructor/payload-reference identity, and
  exact Basis `Option` identity. An unavailable tactic is not reapplied.
- Structural ordered subgoals/assumptions, full reconstructed hypotheses and
  conclusions, and oracle tags are retained. Controls reject wrong conclusion,
  foreign hypothesis and deliberate oracle proof. Both two-subgoal orders,
  unchanged goals, nontrivial hypotheses and zero-subgoal proofs execute.
- Unmarked/empty arguments, `Req0`, `ReqD`, both tagging orders, requirements
  before/after other arguments, zero/one/two bounds, two redexes, wrapped bounds,
  installed spent quotas versus freshly supplied quotas and saved tactic reuse
  all have exact observed baseline outcomes.
- Printers throwing initially, only after construction, or only before second
  use freeze construction failure and saved-tactic success separately. A
  grammar replacement plus a context-backed printer cell freezes early-captured
  diagnostics; candidate wrongly captures the changed use-time environment.
- Late label and fragment lookup remain explicit, including missing labels
  silently omitted, duplicate/distinct label ordering, absent/replaced/rewound
  fragments, abbreviation expansion/missing-abbreviation errors, and malformed
  bounds. Negative argument-bound construction is separately measured.
- Develop's requirement-list quirk is preserved, not fixed: only the last
  item's checks survive, but every wrapper still strips, prints, infers and can
  throw. Both-wrapper failure provenance is fixed too. The matrix also shows
  why blindly moving all processing earlier would introduce new regressions.
- Baseline/baseline observations agree exactly. Reviewed and current match the
  same sealed red stream. A **standalone strict baseline-contract execution**
  passes develop and rejects current `Staging`, without running either original
  behavior/signature reproducer. The driver exits 1; this is durable red evidence.

[STAGING_CONTRACTS.md](STAGING_CONTRACTS.md) contains the full stage matrix,
proof outcomes, early/late obligations, source paths and repair command. Exact
expectations are in `staging/{baseline,reviewed}.json`, sealed with the fixture
hash in `staging/references.json`. Do not regenerate develop expectations to
make the candidate pass. The default diagnostic run checks the complete known
red stream, not merely that the candidate differs somehow.

## Commands, exits and evidence

All commands run from the repository root. Every output path below is under
`src/simp/tests/compatibility/evidence/task05/`; use new paths to reproduce.
Full commands/exits and retained artifact hashes are in `validation.json`.

| Check | Exit | Evidence |
| --- | ---: | --- |
| `bin/build -t --seq=tools/sequences/upto-parallel` | 0 | `routine.log.gz`, after final SML edits |
| documented Holmake `staging-contracts`, current HEAD | 0 | `current.log.gz`, `current-head/manifest.json` |
| documented Holmake `staging-baseline-control` | 0 | `control.log.gz`, `baseline-control/manifest.json` |
| `run_paired.py --staging-contracts --staging-only --candidate cf1f863b4e5a9712ce1b179f18274eb3451f3954 --output .../reviewed` | 0 | `reviewed.log.gz`, `reviewed/manifest.json` |
| `run_paired.py --staging-contracts --staging-only --candidate HEAD --candidate-behavior baseline --output .../strict-red` | **1 expected red** | `red.log.gz`, `strict-red/manifest.json` |
| 34 Python validator tests via both Holmake targets | 0 | `current.log.gz`, `control.log.gz` |
| `tools/h4pedant/h4pedant src/simp/tests/compatibility/staging` | 0 | `pedant.log.gz` (empty output) |
| immutable verifier and `sha256sum -c .../SHA256SUMS` | 0 | `validation.json`, `immutable.log.gz`; 37 unchanged artifacts |
| `git diff --check`, staged diff check | 0 | `validation.json` |

The first Holmake invocation runs 18 fixture/control processes, including the
new suite, original behavior/signature probes and all six executable failure
controls on each selection. The other three experiments each execute the new
suite twice, so there are **26 fixture/control launches plus eight launcher
builds**. All expected-positive processes and all requested rejection controls
meet their exact expectations. A deferred `.uo` build alone is never a pass.

`observations-summary.json` indexes every new-suite result, stage count,
validation count, footer, exit/classification and selection. A final offline
recheck binds all **11 accepted receipts** to manifest source/fixture hashes,
rechecks selected Git bytes and shared source hashes, and verifies all eight
new-suite streams equal their sealed expectations. All harness inputs remained
stable. The strict-red candidate is intentionally rejected at the footer-count
guard (57 observed versus 60 required); its complete stream also has the exact
known moved callbacks/exceptions and is byte-for-event equal to reviewed.
It does not acquire an accepted online path-audit result after that rejection;
the separately accepted current candidate receipt supplies the full path/hash
audit for the same selected implementation. No failed receipt is relabeled pass.

Eight development-only attempts are summarized in `development.json`, not used
as acceptance: two fixture import/qualification errors, then dependency-tag
handling and captures while the fixture/expectations were still being completed.
No production source was instrumented or repaired. Only final sealed fixture
executions supply the acceptance receipts.

## Changed files and decisions

- `staging/Staging.sml`: independent genuine-proof stage/callback/exception suite.
- `staging/{baseline,reviewed,references}.json`: exact ordered expectations,
  immutable-by-policy fixture/golden seals and pinned reference identities.
- `staging_contracts.py`, `test_staging.py`: full stage-shape and real-validation
  counts, sealed inputs, explicit diagnostic reds; eleven new Python tests
  include missing proof/use, changed callback/count, exception identity, oracle,
  subgoal/hypothesis mutations and independent baseline-versus-red rejection.
- `run_paired.py`: optional staged fixture using existing path/exit/hash checks;
  standalone mode proves independence from the original compact reproducer.
  Default old behavior/signature/public/performance contracts are unchanged.
- `Holmakefile`: maintained diagnostic/control targets and 34 Python tests.
- README/schema, matrix, handoff and evidence directory: reproducible contracts,
  observations, limitations and source-tied results. No old test was weakened.
- `.agent-files/tasks/PROGRESS.md`: actual task status and one landing entry;
  unrelated existing contents/files in that separate ignored repository remain.

No public API/type/control scheduling decision was made for production. The
fixture uses only baseline-reachable APIs; its own context slot and printer
callbacks are process-local test instrumentation, not legacy allocations.
No changes to `mk_require_tac`, generic markers or extension tactic semantics.
No new out-of-scope repair/follow-up is needed: the observed repair obligation
already belongs to TASK_18.

No blocker remains for TASK_05. TASK_06 is the next ready task; TASK_07 still
requires it. These results cover configured Linux/aarch64 Poly/ML 5.9.2, state0,
one GC thread and mixed-source isolation only. They are not performance gates,
independent clean builds, downstream/full regressions or cross-platform claims.
Agent-created private trees/products were automatically removed; development
scratch directories/inputs/logs and the two new Holmake lock files were removed
after compact evidence capture. Preexisting unrelated build artifacts and
caller-owned historical inputs were preserved.
