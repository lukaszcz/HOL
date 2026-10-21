# TASK_06 handoff — prior traversal, exclusion and load contracts

Landing source identifier: **TASK_06-prior-contracts-v1** (this commit).
Starting/measured HEAD: `cab2d3b7e8b57f90de4b7943e0c3ded001f2cc2f`.
Develop: `cccaa27d7099cbadc886983020cbe745db7793f3`.
Reviewed: `cf1f863b4e5a9712ce1b179f18274eb3451f3954`.
The production simplifier source diff from reviewed to measured HEAD is empty.
This landing changes tests/harness/docs/evidence only, not production APIs,
representations, mutable controls, loading or callback scheduling. TASK_03's
handoff and TASK_05's immediate handoff supplied context, not fresh evidence.

## Bounded acceptance receipt

**All TASK_06 acceptance criteria are satisfied.** This is coverage capture,
not implementation repair, final compatibility, or performance acceptance.

- A durable **2,153-case** ledger maps actual ordered checks and parameters
  to 23 sealed maintained source files. It retains duplicate labels and
  source/table/expression anchors, full assertion-source hashes and ordered
  OBS streams. `PRIOR_CONTRACTS.md` gives explicit family/matrix arithmetic and
  native source blocks. Missing cases, stale sources/anchors, changed IDs and
  reordered labels fail verification. Relocation must preserve assertions,
  matrix rows and IDs, not just counts; no bulk test move was made.
- The immutable original **73** assertions, original **47 traversal checks /
  273 observations**, and original **929 exclusion checks / 2,703 observations**
  execute freshly against both selected source versions and in a baseline/
  baseline control. All complete streams match their immutable review inputs.
  No old assertion or observation was edited. Only process-ending driver calls
  become paired completion checks, with `failcount = 0` still mandatory.
- Added six baseline-only targeted limit pins without modifying the old
  47-case input. A failed solver actually consumes a side rewrite then fails
  EQT_ELIM; restored allowances permit two subsequent root rewrites. Zero/one/
  two limits, exact attempt ordering and enclosing sibling rollback execute on
  both source selections. All **4,220** old/new shared assertion executions
  (four selections across two experiments) pass, excluding wrapper checks.
- The ledger freezes construction/use contexts, live depth, ordered collectors,
  factory rejection/eagerness/refresh, weakener ordering, failed candidates,
  foreign payload/Interrupt identity, warnings, maker/tag staging, installed
  bounded-control sharing, literal/strict exclusion parsing and theory/context
  history reparsing. Supplementary limit rollback is now differential too.
- All **630 native assertions** execute, retaining extension capabilities and
  embedded legacy pins, including source/view/bundle identities, quotas,
  child-first private scopes, generic facts, configured contexts/controls and
  preserving replay. Their complete ordered assertion stream matches the
  preserved native reference. They are **not claimed baseline APIs**.
- All focused marker, registration and replay tests execute unchanged. All
  **six fresh-load scenarios** run as distinct clean processes. Both first-owner
  scenarios really execute all four exact handler/listener pointer/order/list
  assertions, not merely their launcher or `.uo` generation. Foreign attribute,
  set and syntax before/after loading remain executable.
- Parent/child/descendant exports are built freshly in a temporary directory;
  all **eight persistence/heap scenarios** execute, including a separate saved
  heap reload. Exact imported theorem/handler identity, ownership conflicts,
  private ordered replay, no ordinary simp load during import and context rewind
  assertions remain intact. Temporary sources/products/heap are removed.
- Legacy streams agree exactly; raw exclusion successful output differs only
  in theory build times. Native monitor serials/testutils timing/color/padding
  are presentation, not cross-version observations. OBS callback/warning/error
  payloads are never normalized. Raw diagnostics remain in receipts.
- Initial reds remain explicit: current's original signature fixture has
  **process exit 1**, both added-constructor diagnostics and expected-candidate-red
  classification. Its original staging probe still has printers **0/1/2** and
  saved `PrinterFailure` (develop **1/1/1**, remaining goal). A fresh standalone
  strict TASK_05 staging run has **driver exit 1**, rejecting 57 observed checks
  versus the baseline's 60 and retaining the exact known moved-stage stream.
  No expected-failure mode exists for any prior-contract suite. TASK_11/18 own
  the already-planned repairs; the performance findings also remain open.

The old starting inventory misstated one aggregate: the preserved focused log's
1,440 checks do **not** include the separately logged 630 native checks. Fresh
exports additionally execute four script assertions (1,444 focused + 630 native
+ 73 original + 6 supplementary = 2,153 ledger occurrences). This source/case
reconciliation corrects documentation, not test expectations or failing counts.

## Commands, exits and evidence

Paths below are under `evidence/task06/`. Full commands/exits and artifact/input
hashes are in `validation.json`, manifests, `commands.json` and `checks.json`.
Runtime: configured Linux/aarch64 Poly/ML 5.9.2, state0, one GC thread. Paired
manifests retain selected Git blobs/source bytes, private fixture/product hashes,
actual elaborated paths, shared dependencies, tools/heaps/options and exits.
Native manifests seal source inputs, native products, launcher text, runtime
and command environments. Neither kind is an independent clean repository build.

| Check | Exit | Evidence |
| --- | ---: | --- |
| `bin/build -t --seq=tools/sequences/upto-parallel` after final SML edit | 0 | `routine.log.gz`, `routine-command.json` |
| documented Holmake `prior-contracts`, current HEAD | 0 | `current.log.gz`, `current-head/manifest.json`; 24 fixture/control launches |
| documented Holmake `prior-baseline-control` | 0 | `control.log.gz`, `baseline-control/manifest.json`; 12 launches |
| `run_prior_native.py --output .../native` | 0 | `native/manifest.json`; actual native/focused/fresh-load launches and fresh exported-theory/heap matrix |
| standalone `--staging-contracts --staging-only --candidate HEAD --candidate-behavior baseline` | **1 expected red** | `strict-red/manifest.json`, `strict-red.log.gz`; two executed fixtures |
| 48 Python validator tests via both Holmake targets and independent discovery | 0 | `current.log.gz`, `control.log.gz`, `python-tests.log.gz` |
| `audit_prior.py .../task06` and `coverage_ledger.py` | 0 | `observations-summary.json`, `ledger.log.gz` |
| `tools/h4pedant/h4pedant src/simp/tests/compatibility/paired` | 0 | `pedant-directory.log.gz` (empty) |
| immutable verifier and `sha256sum -c .../SHA256SUMS` | 0 | `immutable.log.gz`, `sha256.log.gz`; all 37 artifacts unchanged |
| `git diff --check`, staged diff check | 0 | `checks.json`, `validation.json` |

The 38 paired/control/stage launches plus six launcher builds are distinct from
native commands; negative controls hit their intended guards, not arbitrary
failure. The archived source audit rechecks all selected Git bytes, all accepted
path inventories against source/fixture/product manifests, runtime/input seals,
all four strictly equal prior streams, every native ledger stream and the exact
strict-red event sequence. A rebuilt ledger from final receipts is identical
to the committed seal. See `SCHEMA.md` for transport/presentation distinctions.

Development-only issues are retained compactly in `development.json`: an early
attempt to run the whole native suite in the mixed private source tree failed
when current later theory products required matching generated ancestry. No
assertion was omitted/normalized: the full unchanged native launcher instead
runs against its current native products; only the baseline-reachable suites
are paired. The first parser correctly failed a 630-count guard at 602 because
28 monitor-interrupted labels needed pending-OK handling; a unit control and
full historical/fresh agreement now protect that case. A file-path h4pedant
invocation returned 1 without diagnostics (the tool expects a directory); the
correct directory invocation passes. Failed attempts are not acceptance passes.

## Changed files and decisions

- `paired/PriorLimits.sml`: six new baseline-only assertions; no new production
  theorem/module/API or changed old contract.
- `prior_contracts.py`, `run_paired.py`: optional strict prior suites, original
  body/driver integrity, exact old streams/counts and source-path audits. All
  old default/public/staging/performance modes retain their expectations.
- `run_prior_native.py`: maintained executable native/cleanup matrix; explicitly
  separate native extension semantics and fresh private persistence products.
- `coverage-ledger.json.gz`, `coverage_ledger.py`: source-tied stable case IDs,
  exact matrix occurrences/observations, navigation anchors and verification.
- `test_prior.py`: 14 added Python tests, including count-preserving wrong-case,
  reordered-callback, changed-warning, missing-completion, interleaved-monitor,
  assertion-failure and stale/lost-ledger negative controls (48 total tests).
- `audit_prior.py`: offline archived source/observation/red recheck, with no
  regeneration of passing expectations.
- `Holmakefile`, README/schema, coverage inventory, `PRIOR_CONTRACTS.md`, this
  handoff and compact evidence: maintained commands, coverage map, observations
  and limits. `.agent-files/tasks/PROGRESS.md` has actual status and one landing
  entry; unrelated contents of that separate ignored repository are preserved.

No blocker remains for TASK_06. TASK_07 is now the next ready task. TASK_26
still owns the later coverage-preserving split, not unfinished work here.
No out-of-scope implementation repair or new deferred follow-up was introduced.
Only configured Linux/Poly execution is measured; no performance, full-build,
downstream, independent-clean-build or other-platform acceptance is claimed.
Agent-created pilot trees/logs/index files and two new Holmake lock files were
removed after retaining compact evidence. Caller-owned historical inputs and
preexisting native products/caches/locks were preserved.
