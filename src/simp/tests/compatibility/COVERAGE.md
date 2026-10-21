# Maintained coverage inventory at the starting revision

Inventory revision: `cf1f863b4e5a9712ce1b179f18274eb3451f3954`.
This is a source/coverage inventory, not a fresh test receipt. Exact file
identities are in `initial-state.json`. All paths below are repository-relative.
Existing generated executables/logs are caller-owned and are not evidence of
fresh execution. No old `src/simp/compatibility` archive was restored or used
as the inventory source.

## Current tests and integration

| Location | Coverage and normal entry point |
| --- | --- |
| `src/simp/src/selftest.sml` | Expanded native suite: legacy rewriting, bounds, abbreviations, requirements, tactic dispatch, configured solver/depth/order controls, child-first traversal, safe/unsafe solvers and loopers, splitter integration, source identities, rewrite views, prepared bundles, suspension/removal, quota sharing and replay. `selftest.exe` / `simp-selftest.log`. Not the unchanged develop input. |
| `src/simp/tests/contracts/TraversalContracts.sml` | Legacy-only ordered callback/factory traces, initial/recursive/private contexts, reuse, live default depth, exception boundaries, maker staging, warnings and installed quota sharing. `RunTraversalContracts.sml` invokes `run`; `traversal-contracts.exe`. |
| `src/simp/tests/contracts/LegacyFailures.sml` | Shared legacy observations/assertions; literal namespace-looking rewrite/dproc names, direct exclusion and tactic-marker routes, installed/missing cases, projection shape and control simplification. |
| `src/simp/tests/contracts/ExclusionHistory.sml` | Repeated/unmatched deletions, interleaved additions, retained history, direct/replayed results, ancestor/context restoration and strict dotted-name failures. |
| `src/simp/tests/contracts/ExclusionParsing.sml` | Literal/qualified/malformed names, dproc callback ordering, exception provenance, and replay reparsing after theory/context changes. `RunExclusionContracts.sml` runs ten literal-prefix installed/missing cases plus both exclusion modules; `exclusion-contracts.exe`. |
| `src/simp/tests/fresh-load/` | Dynamic loading in a clean initial heap, foreign attribute/set ownership before and after loading, foreign syntax, warnings and handler behavior. Six scenarios in `selftest.sml`; `control.ML`, `syntax.ML`, `identity-before.ML`, `identity-after.ML` are dynamic checks. Native identity checks compare exact handler records, preexisting listener functions/order and the precise permitted legacy listener additions. `fresh-load-regressions`. |
| `src/simp/tests/markers/` | Simplifier-owned directives, disjoint recognizers, literal string round trips (all byte values), bounds/requirement wrapper precedence, recursion/assumption preprocessing and develop ordering quirks. `selftest.sml`; `simp-marker-tests`. |
| `src/simp/tests/split-registration/` | Explicit opt-in, no generic set or ordinary-load listener, preflight failures with exact Context rollback, private ADD/REMOVE data, listener identity/order, idempotence, rewind/reinitialization, foreign ownership, invalid declarations, stale bindings/types/constants, replay failure/retry, listener conflicts and pinned contexts. `selftest.sml`; `split-registration`. |
| `src/simp/tests/split-persistence/` | Fresh exported parent/child/descendant loads, already-owned and foreign-attribute/set scenarios, exact theorem/handler identity, no ordinary simp load during persistent import, private replay and save/reload lifecycle. Three `*Script.sml` inputs, `verify.ML`, `optIn.ML`, `heapSave.ML`, `heapVerify.ML` and scenario launcher `selftest.sml`; `check` / `split-persistence`. |
| `src/simp/tests/replay-order/` | Synthetic diamond ancestry order, repeated `TheoryLoaded`, equal-theorem aliases, sibling removals, private split replay versus generic characterized ordering, REMOVE writing theory. `selftest.sml`; `replay-order`. |
| `src/marker/selftest.sml`, `src/1/selftest.sml` | Shared marker behavior and theorem-attribute inspection remain separately owned native coverage. Do not move extension behavior back into these shared layers. |

`src/simp/src/Holmakefile` wires the native selftest and all focused targets
above into `all` when `HOLSELFTESTLEVEL` is set. Contract Holmakefiles resolve
private simplifier modules via `INCLUDES = ../../src`, with `hol.state0`.
Fresh-load/persistence launchers deliberately avoid static extension imports.
The preserved historical inputs are **not** wired into this build by TASK_01;
TASK_02 owns executable differential integration.

## Prior cleanup boundary retained

The immediate starting commit contains the previous cleanup, rather than a
new repair by TASK_01:

- Generic `src/marker`, `src/1/ThmSetData.{sig,sml}` and `src/postkernel`
  match pinned develop exactly (checked with `git diff --exit-code`, exit 0).
- `src/1/ThmAttribute.{sig,sml}` retains read-only inspection additions and
  `src/1/selftest.sml` their checks. These are intentional baseline differences.
- Simplifier markers are owned by `simpMarker`/`simpMarkerLib`.
  `SplitData` owns private persistence, `splitLib` owns explicit initialization,
  and `splitPersistLib` is the opt-in import. Ownership/rollback/listener/replay
  assertions remain in the maintained suites above.
- The starting commit also contains the rawtheory prerequisite ordering fix
  (`src/portableML/rawtheory/mktool.ML`); no such source was touched here.

The prior cleanup task set's PROGRESS and starting commit message record
historical full/routine successes. They are context only: they do not complete
any task or performance gate in the new plan. There is no immediate
predecessor handoff in the new task set because TASK_01 has no dependencies.

## Positive historical observations preserved

The supplied review JSON and logs report, for each source version:

- Original develop selftest: 73 checks, identical raw logs.
- Traversal contracts: 47 checks, 273 observations, identical raw logs.
- Exclusion contracts: 929 checks, 2,703 observations; only theory build timing
  output differed.
- Candidate native selftest: 630 checks; combined native log: 1,440 checks
  including the native selftest and focused suites (not 1,440 additional checks).

The integrity verifier checks these against the supplied compact logs. It does
not rerun them. The old-signature and printer-staging failures demonstrate why
these positive observations are not universal compatibility evidence.

## Missing contracts and explicit ownership in the new task set

- TASK_02: fail-closed paired runner and true signature elaboration.
- TASK_03: fresh four-finding reproduction, variability, consumed benchmark
  results, calibrated timing and retained-memory baselines.
- TASK_04/05: complete public signature clients and expanded tactic
  construction/application/exception/proof-stage matrix.
- TASK_06: freeze traversal/exclusion and exact fresh-load identity contracts
  above without weakening assertions.
- TASK_26: coverage-preserving extension/legacy test separation and normal
  selftest integration, including the immutable original develop selftest.

These are planned dependencies, not deferred TASK_01 acceptance criteria.
No tests were removed, migrated, weakened or declared newly passing here.
