# Compatibility implementation task index

Source of truth: [PLAN_compatibility.md](../PLAN_compatibility.md).
Progress: [PROGRESS.md](PROGRESS.md).

## Objective and task boundaries

Restore develop's observable legacy simplifier behavior without requiring
client migration; preserve extended features through explicit opt-in APIs.
Observables include failures, warnings, callback staging/frequency, reducer
shape, context lifetime, rule ordering, quotas, history, and load-time state.
Equal final conclusions alone are insufficient.

Every task has a Context section distinguishing that overall objective from
its own acceptance criteria. These files specify future work: none of the
implementation or validation tasks is complete just because it is listed.

## Tasks and dependencies

IDs below mean `TASK_nn`. Dependencies are mandatory completion prerequisites,
not merely a suggested reading order. Use links for the full instructions.
The context estimates include targeted source reading, implementation, tests,
and handoff; they are planning estimates, not token budgets or guarantees.

| ID | Task | Depends on | Context estimate |
| --- | --- | --- | --- |
| 01 | [Baseline and harness](TASK_01_baseline_and_harness.md) | none | 40–80k |
| 02 | [Freeze legacy failures](TASK_02_freeze_legacy_failures.md) | 01 | 30–70k |
| 03 | [Fresh-load regressions](TASK_03_fresh_load_regressions.md) | 01, 02 | 40–90k |
| 04 | [Restore traversal projection](TASK_04_restore_traversal_projection.md) | 02 | 60–120k |
| 05 | [Traversal lifetime contracts](TASK_05_traversal_lifetime_contracts.md) | 04 | 50–110k |
| 06 | [Extended exclusion marker](TASK_06_extended_exclusion_marker.md) | 01 | 35–75k |
| 07 | [Separate exclusion routes](TASK_07_separate_exclusion_routes.md) | 02, 05, 06 | 60–130k |
| 08 | [Exclusion history replay](TASK_08_exclusion_history_replay.md) | 07 | 60–130k |
| 09 | [Exclusion contract matrix](TASK_09_exclusion_contract_matrix.md) | 08 | 45–100k |
| 10 | [Explicit split registration](TASK_10_explicit_split_registration.md) | 03 | 70–140k |
| 11 | [Split persistence and clients](TASK_11_split_persistence_and_clients.md) | 10 | 60–130k |
| 12 | [Split lifecycle and load audit](TASK_12_split_lifecycle_and_load_audit.md) | 09, 11 | 50–110k |
| 13 | [Documentation/migration sweep](TASK_13_documentation_and_migration_sweep.md) | 05, 09, 12 | 35–80k |
| 14 | [Paired differential validation](TASK_14_paired_differential_validation.md) | 13 | 45–100k |
| 15 | [Downstream/routine validation](TASK_15_downstream_and_routine_validation.md) | 13 | 40–90k |
| 16 | [Full regression gate](TASK_16_full_regression_gate.md) | 14, 15 | 30–80k |
| 17 | [Final acceptance/report](TASK_17_final_acceptance_and_report.md) | 16 | 30–70k |

Each task is intended for one agent with a 200k-token context window, with
headroom below that limit. Read the plan, this index, the task, and immediate
predecessor handoffs, then only relevant source slices and test summaries.
Do not load entire historical artifact directories or full build logs into
context. Large exclusion work is split into marker, routing, replay, and
matrix tasks; persistent splitting into core ownership, replay/client
integration, and lifecycle validation. Build gates are separate from repairs.

If a newly discovered defect requires a larger redesign, write a bounded
follow-up task with its own Context, dependencies, and acceptance criteria;
add it here and in progress and leave the affected gate blocked. Do not
weaken assertions, silently drop required scope, or consume the entire
window attempting an unrelated subsystem repair.

A simple safe order is numerical. Dependencies permit earlier independent
work, but overlapping edits to `simpLib.sml`, `selftest.sml`, marker generated
sources, or Holmake files must be serialized/coordinated. Never run competing
builds against shared products; isolate or serialize reference/branch builds.
An initial red-regression task can land with precisely documented expected
failures; a repair or validation gate cannot call those failures successful.

## Plan coverage

- Phase 1: 01–03 (pins, unchanged reference input, all failure classes).
- Phase 2: 04–05 (projection repair, configured callers, staging/lifetimes).
- Phase 3: 06–09 (distinct opt-in marker, literal legacy path, history,
  parser/namespace coverage, extension migrations).
- Phase 4: 03 and 10–12 (fresh loading, explicit ownership, Context lifetime,
  export/import, ancestor replay, heap reload, registrations audit).
- Phase 5: API docs accompany each change; 13 completes the repository sweep,
  14 differential evidence, 15 downstream/routine builds, 16 full build,
  17 completion audit, whitespace checks, cleanup, and qualified reporting.

## Shared implementation and validation rules

- Follow `CLAUDE.md`; branch new work from `origin/develop` if needed and
  explicitly carry relevant implementation. Do not reset unrelated work.
- Use `selftest.sml`, `testutils`, and Holmake-built executables. Do not
  validate by piping SML into `bin/hol`.
- For `src/marker` and `src/simp/src`, use the early-directory
  `<repo-root>/bin/hol.state0` heap (their Holmake configuration also selects
  it). Document exact targets/commands, exit statuses, and source revisions.
- After compiled-source changes, run and record
  `bin/build -t --seq=tools/sequences/upto-parallel`. Report exact blockers;
  never equate an incomplete check with a pass. A repair may be handed off
  with a documented external validation blocker, but required validation
  tasks and final sign-off remain blocked until their criteria are met.
- The final full gate is `bin/build -t -F`, explicitly including `-F`.
- Keep native legacy traversal/rewrite dispatch. No extra preparations,
  collector calls, quota resets, or unnecessary removal of branch APIs.
- Keep original develop expectations unchanged; migrate only branch-only
  extension expectations to explicit APIs and preserve their assertions.
- Run `git diff --check` and appropriate project whitespace checks on changes.
  No tabs/trailing whitespace; prefer source lines below 80 columns.
- Keep compact uniquely useful evidence and runnable inputs. Clean only
  agent-created copied trees, caches, and scratch files after their last
  required use, not caller-owned or unrelated artifacts.
- Tests cannot establish equivalence for every callback. Report verified
  contracts, provenance limitations, untested scope, and open blockers.

## Progress and handoff protocol

`PROGRESS.md` has exactly three sections. Keep it concise:

1. One status line per task: `done`, `blocked` (with prerequisite/blocker),
   or `unblocked (not started)` / `unblocked (in progress)`.
2. The next unblocked task, or `none` plus the blocking reason/all-done state.
3. Completion log: **ONE line per task as each task lands**. Include task ID,
   landing commit or equivalent identifier, and a compact evidence pointer.
   Do not add per-attempt/build entries or log unfinished tasks as complete.

On landing, update the status, unblock satisfied dependencies, choose the
next unblocked task (lowest ID by default), and add exactly one completion
line. Put detailed commands, results, failure triage, and scope in evidence
records rather than expanding progress. No completion line exists initially.

Each task handoff must identify changed files, finalized API decisions,
test commands/results (including expected red probes), remaining blockers,
and evidence paths. Read predecessor handoffs rather than reproducing their
whole investigations.

## Evidence locations

TASK_01 evidence and handoff: `src/simp/compatibility/BASELINE.md`.
Harness instructions/isolation: `src/simp/compatibility/README.md`.
TASK_06 marker/API handoff:
`src/simp/compatibility/EXTENDED_EXCLUSION_MARKER.md` and `results/task06/`
under that directory. Final names: `markerLib.ExclX`, `destExclX`, `DExclX`,
backed by `marker$ExcludeX`; simplifier routing belongs to TASK_07.
TASK_09 coverage/handoff for TASK_13/TASK_14/TASK_17:
`src/simp/compatibility/EXCLUSION_MATRIX.md` and `results/task09/`.

- Fixed reference: `cccaa27d7099cbadc886983020cbe745db7793f3`.
- Initial implementation: `62a6bdc3453c29e8f31faa72f2b70a245f44840d`
  (audited HEAD; initial tracked/untracked status clean).
- Unchanged original selftest: `src/simp/compatibility/inputs/develop/`;
  hashes: `src/simp/compatibility/inputs/SHA256SUMS`.
- Historical reproducers: `src/simp/compatibility/inputs/investigation/`.
- Maintained legacy differential inputs:
  `src/simp/compatibility/probes/legacy/`; branch-only APIs:
  `src/simp/compatibility/probes/branch/`; fresh-load fixtures:
  `src/simp/compatibility/probes/fresh-load/`.
- Initial paired results: `src/simp/compatibility/results/task01/`;
  later task records: `src/simp/compatibility/results/taskNN/`.

From the repository root (output must be a new directory):

```sh
python3 src/simp/compatibility/run.py \
  --branch 62a6bdc3453c29e8f31faa72f2b70a245f44840d \
  --output /tmp/compat-new-results
(cd src/simp/compatibility && sha256sum -c inputs/SHA256SUMS)
bin/build -t --seq=tools/sequences/upto-parallel
```

The paired harness uses `bin/hol.state0`, private per-revision products and
shared host dependencies/generated markerTheory: **mixed-source**, not
independent repository builds. Control builds/runs exited 0 on both; the
unchanged develop suite exited 0 with 73 OK on both. The routine build
completed with exit 0. No compatibility repairs, full-build gate, or broad
observational equivalence are claimed. TASK_17 will add the final report.
