# TASK_17: plan-to-evidence audit

**Accepted within the tested scope. No missing required item or open
legacy-reachable divergence was found.** This is the completion ledger for
all **58** unchecked boxes in `.agent-files/PLAN_compatibility.md`, in their
original order. `P2.8` means the eighth checkbox in Phase 2, including its
regression subsection. `C1`–`C5` are the completion criteria. The original
planning file is caller-owned/ignored; it is not rewritten as evidence.
The final qualified summary is [FINAL_REPORT.md](FINAL_REPORT.md).

## Evidence key and interpretation

Paths below are relative to the repository root unless abbreviated:

- `S` = `src/simp/src/`; `M` = `src/marker/`;
  `P` = `src/simp/compatibility/probes/`.
- `Tnn` = `src/simp/compatibility/results/tasknn/`. A receipt means
  `validation.json`, except T01–03 use `manifest.json`.
- T14 final differential receipts are `paired-verified/manifest.json`,
  `fresh-verified/manifest.json` and `comparison/matrix.json.gz`.
  T15 freshly executed normal and focused suites supersede earlier native
  runs; T16 is the full gate. T17 `checks.json` independently rechecks
  their input/log integrity and reproduces the retained paired comparison.
- Implementation landings and detailed commands/triage are linked in
  `.agent-files/tasks/PROGRESS.md` and the named handoff reports here.
  Historical expected failures are not passing repair gates.

## Phase 1 — freeze contracts (5/5)

| ID | Change / maintained input | Validation receipt / outcome |
| --- | --- | --- |
| P1.1 | `BASELINE.md`: audited HEAD `62a6bdc34`, fixed develop `cccaa27d7`, clean initial implementation, no intervening changes or new branch required. | T01 pins/status/source hashes; original existing branch retained, no reset/rebase. |
| P1.2 | `P/legacy/`, shared `P/support/`, fresh launcher and `S/Holmakefile`: testutils assertions and Holmake executables. | T02/T03 independent red inputs; T14 all maintained legacy inputs; T15 normal focused targets pass. |
| P1.3 | Constructor plus all five prefixes, unmatched and installed literal conversions; ordinary controls. | T02: eleven expected branch failures, all reference cases/control pass; T14: repaired cases pass unchanged legacy contracts. |
| P1.4 | `P/fresh-load/selftest.sml`: custom attribute/exporter before dynamic simpLib loading, absent ML structures and loader entries asserted. | T03 independently reproduces collisions; T14 five clean paired scenarios; T15 six native scenarios pass. Set-first also installs an attribute via the public exporter API. |
| P1.5 | `inputs/develop/selftest.sml` unchanged from the pinned git object. | T14: 73 assertions per lane and identical raw output; T17 checks git-byte identity and frozen input hashes again. |

Phase acceptance: all three failure classes independently reproduced with
explicit preconditions and passing ordinary-simplification controls.

## Phase 2 — traversal projection (11/11)

| ID | Change / code contract | Validation receipt / outcome |
| --- | --- | --- |
| P2.1 | `S/simpLib.sml`: `default_traversedata_for_ss` uses `legacy_rewriter_for_ss_prepared ss []`, equality, original rules/dprocs/limit. | T04 receipt; T14 reducer-shape and traversal-lifetimes; T15 native suite. |
| P2.2 | Public `traversedata_for_ss` directly calls the unconditional default builder, not `valOf` optional dispatch. | `S/selftest.sml` constructor/configured-input assertions; T04, T14, T15 pass. |
| P2.3 | Default projection omits traversal settings and forwards dproc representations unchanged. | Native pointer/constructor/purity and actual configuration-omission tests; T04/T15. |
| P2.4 | `configured_traversedata_for_ss_prepared` and `xtraversedata_for_ss` retain the configured path. | Migrated configured depth/order/subgoaler/solver/child-first assertions; T15 simplifier 630 OK. |
| P2.5 | Optional `legacy_traversedata_for_ss` tests eligibility purely, then shares default builder; SIMP_QCONV/congLib retain native dispatch. | T05 staging/purity tests; T14 273 equal ordered lifetime observations; T15. |
| P2.6 | Extraction caller audit: congLib optional/native fallback already correct; prepared/child-first consumers explicit extended; no missed production client. | `TRAVERSAL_PROJECTION.md` caller audit, T13 search dispositions, T15 downstream consumers. |
| P2.7 | `S/selftest.sml` pure_data/bool_data/configured quota/fallback expectations migrated to explicit extraction, not discarded. | T04 caller/test inventory; T15 unchanged native assertions including quota/callback checks. |
| P2.8 | REDUCER for empty_ss, bool_ss and ordinary custom dproc. | T14 reducer-shape: 7 OK and 15 equal observations per lane; T15 normal constructor tests. |
| P2.9 | `appconvs` shares installed bound refs across both ABIs; selftest exercises both orders, late extraction/exhaustion, views/replay and compile counters. | T05/T14 lifetime receipts; T15 shared-control assertions pass without quota refresh/recompile. |
| P2.10 | Native context reuse, factory staging, live stack limit, trace order and exception identity. | `P/support/TraversalContracts.sml`: T14 47 OK / 273 equal observations per lane, raw output identical; T15 fresh traversal-contracts. |
| P2.11 | Explicit configured depth/order/subgoaler/unsafe solvers and child-first retained. | `S/selftest.sml` configured/child-first assertions; T15 simplifier 630 OK and downstream consumers. |

Phase acceptance: no legacy constructor migration required; native and
configured lifetime/shared-control assertions retained and passing.

### Native-runner and ambient-strategy review

`Traverse.TRAVERSE` still selects `ORIGINAL_TRAVERSE_IN_CONTEXT` for ordinary
reducers; its mixed-representation legacy adapter is not the configured
engine. `Cond_rewr.COND_REWR_CONVS` retains one prepared matcher with separate
native/configured runners; native applications read the live stack limit.
`SIMP_QCONV`, congLib and `strategy_free` preserve ordinary native dispatch;
tactic-only loopers/safe solvers do not change raw conversion lifetime.
The default projection builds an empty prepared context, not new installed
rewrite matchers; collectors run at their original consumption stage.
`Traverse.sml`, `Cond_rewr.sml`, `congLib.sml` and core `Rewrite.sml` are
unchanged since the audited implementation. No added preparation, collector
call, installed-control reset or legacy ambient opt-in was found. This is
code review plus finite callback tests, not universal callback equivalence.

## Phase 3 — literal and extended exclusions (13/13)

| ID | Change / code contract | Validation receipt / outcome |
| --- | --- | --- |
| P3.1 | `S/simpLib.sml`: `LiteralExclusion`, `munge_simpset_name`, `delete_exclusions`; ordered batches and DELETE_EVENT even for absence. | T07/T09; T14 prefix/history/parser probes; T15 exclusion-contracts 929 OK. |
| P3.2 | DExcl never calls `resolve_exclusion`; no prefix or bare strategy fallback. | Native collisions preserve strategy targets while deleting literal stores; T09/T14/T15. |
| P3.3 | Distinct `marker$ExcludeX`, markerLib/simpLib.ExclX, destExclX and DExclX; not an Excl string encoding. | T06 marker/API receipt; T15 marker 72 OK and actual simplifier routing. |
| P3.4 | `resolve_exclusion` only processes explicit ExclX: five namespaces, relaxed qualified rules, ambiguity and unmatched errors; explicit deletion functions retained. | T09 extended matrix in native selftest; T15 630 OK. |
| P3.5 | `rule_exclusion.strict` distinguishes legacy reparsing from resolved extended history; directive order retained. | T08; T14 history 72 and parser 1378 equal ordered observations, including genuinely changed current theories and Context restore. |
| P3.6 | `EXCLUDE_LOOPER_EVENT` records split/case suppression; replay/filter/remove cannot silently re-enable it. | T08 negative control without recording fails 30 assertions; repaired replay/filter/Context tests pass again in T15. |
| P3.7 | DExclX/bounded processing and pure strategy inspection; branch extension assertions/examples migrate, legacy assertions stay literal. | T06/T07/T09; T13 migration/search/example receipts; T15 suites. |
| P3.8 | All ten prefix inputs, installed deletion and silent unmatched names. | T14: each input 41 OK / 133 equal observations per lane, zero warning observations; see twelve-case table below. |
| P3.9 | Literal conversion, named rewrite and dproc stores, overlapping names and namespace collisions. | `P/support/LegacyFailures.sml`, native collision assertions; T09/T14/T15. |
| P3.10 | Excl and `-*` same strict interpretation/deletion, including errors/replay (not identical history packaging). | Shared prefix/parser/history fixtures; T14 paired equality, T15 exclusion-contracts. |
| P3.11 | Dotted/numeric/empty suffixes, unknown ancestors, literal bare Thy$Name, repetition, history and Context. | `ExclusionParsing.sml` / `ExclusionHistory.sml`; T14 535 / 28 OK per lane. |
| P3.12 | ExclX selects all namespaces, diagnoses typos/ambiguities, survives unrelated fragment removal. | Native extended matrix, resolved-rule and split/case replay tests; T09/T15. |
| P3.13 | Distinct construction/recognition, arbitrary names, malformed markers, requirement/bounded interactions and unchanged legacy markers. | `M/selftest.sml`, `S/selftest.sml`; T06/T15 marker 72 OK, simplifier 630 OK. |

Phase acceptance: no old Excl string selects an extension namespace;
ExclX remains a distinct opt-in, including replay semantics.

## Phase 4 — explicit split persistence (15/15)

| ID | Change / code contract | Validation receipt / outcome |
| --- | --- | --- |
| P4.1 | `S/splitLib.sml`: no top-level collision/exporter setup; exporter is inside enable_split_attribute. | T10 code/ownership receipt; T14 paired and T15 fresh loading pass. |
| P4.2 | Explicit enable_split_attribute; pure conversions/local Split/TypeBase split_ss independent. | T10 registration fixture's pre-opt-in behavior; T15 101 registration OK. |
| P4.3 | Ownership-gated snapshot queries return [] before initialization/under foreign ownership without adopting or registering. | Registration fixture covers foreign/replaced/pinned contexts and empty queries; T15. |
| P4.4 | Identity of both attribute and exporter; full public-name/listener preflight before mutation; owned repeated init no-op. | Whole-Context nonmutation, pointer identity and error assertions; T10/T12/T15. |
| P4.5 | Private Context registration handle, not global initialized bool; Context-selected theory-data instance hooks. | Context rewind/reinit/restore and foreign witness tests; T12/T15. |
| P4.6 | `splitPersistLib` explicit dependency before earliest split-bearing theory decoding; no simpLib dependency on it. | T11 generated replay/dependency ordering; T12/T15 actual fresh parent/child/descendant imports. |
| P4.7 | Earliest producer fixture loads/exports opt-in; documented API/ownership/replay migration. | T11; T13 complete producer search finds no other production [split] client; examples validated. |
| P4.8 | Other registration/syntax changes inventoried, including removing only marker ExcludeX's own unqualified mapping. | `LOAD_AUDIT.md` R01–R05, S01–S03; T12/T15 foreign syntax test. |
| P4.9 | Attribute-first preserves foreign handler and arguments/order/identity. | T14 paired attribute-first; T15 fresh-load-regressions. |
| P4.10 | Set-first preserves foreign data, callbacks, hypotheses/exporter identity. | T14 paired set-first; T15 native. Public exporter also installs attribute (not a set-only test). |
| P4.11 | simpLib-first leaves both names free; later custom registration silent. | T14 attribute-after/set-after; T15 fresh processes. |
| P4.12 | Conflict-free explicit opt-in and real [split] declarations. | T15 registration and exported persistence fixtures. |
| P4.13 | Foreign attribute/exporter/listener conflicts rejected without partial mutation. | T15 registration; foreign import errors are asserted expected outcomes. Exporter-only ownership mismatch also tested. |
| P4.14 | Repeated opt-in, Context restore, export/import, ancestor additions/removals and real saved-heap reload. | T12/T15 six import/owner plus separate heap-save/reload processes, registration 101 / persistence 161 OK. |
| P4.15 | Local Split and TypeBase split_ss work pre-opt-in while registries remain unclaimed. | T10/T15 registration fixture's positive controls and registry assertions. |

Phase acceptance: ordinary load is neutral to the public split registries
and foreign Split/ExcludeX syntax; persistence is explicitly reproducible.
It is **not** a claim that loading allocates no private state. In particular,
`ThyDataSexp` dispatch is an intentional shared-infrastructure change for all
its clients, not a split-only shim; full-build coverage applies to it.
Serialized setup, initialization before replay, and explicit reinitialization
after pre-opt-in Context restore remain documented API constraints.

## Phase 5 — integration and documentation (9/9)

| ID | Change / validation | Receipt / outcome |
| --- | --- | --- |
| P5.1 | Signatures, public docfiles and notes distinguish native projection, strict Excl and opt-in APIs. | T04–13 changes; T13 validation and naming-validation receipts: 15 entries evaluated/rendered, updated parser examples pass. |
| P5.2 | Branch-only migration to xtraversedata_for_ss, ExclX and explicit persistence documented; legacy clients do not migrate. | `API_MIGRATION.md`, docfiles/notes; T13 examples and T15 extension assertions. |
| P5.3 | Whole tracked-repository search reviews each extraction/exclusion/registration hit, plus ignored historical plans. | T13 search.json (277 files) and naming-validation follow-up; no later active client/source changes. Historical red inputs deliberately not migrated. |
| P5.4 | Normal early-heap marker and simplifier Holmake log targets freshly regenerated. | T15 validation.json: 72 / 630 OK, exit 0. |
| P5.5 | Unchanged develop suite and every legacy probe on fixed develop/repaired pins; complete raw results, hypotheses, warnings, exceptions, ordered callbacks and executed tactic validations. | T14 all 17 ordinary + five fresh pairs pass, 3251 equal ordered observations; narrow raw timing/path differences retained. T17 reporter recheck passes. |
| P5.6 | bin/build -t --seq=tools/sequences/upto-parallel. | T15 routine.log.gz / validation.json: exit 0, Hol built successfully; same implementation/input hashes at T17. |
| P5.7 | Arithmetic, custom reducers, congruence, fragment replay, quotas, ordinary/full simplification downstream consumers. | `DOWNSTREAM_VALIDATION.md` eight-suite matrix; T15 fresh targets and focused checks all exit 0. |
| P5.8 | Explicit bin/build -t -F, actual full sequence and fresh selftests audited. | T16 validation/scope audit: exit 0, 87 ordered visits, 34 fresh selftest logs, 650 theory timing entries. Current 7924 candidate hashes unchanged. |
| P5.9 | Diff whitespace, h4pedant, additional all-changed-text checks and task-owned temporary artifact cleanup. | T17 checks.json and check.py; prior T13–16 cleanup receipts; no task-owned copied tree/cache/heap/scratch remains. |

## All twelve original regressions

These are independent paired inputs in T14; the original constructor
assertion's intent is unchanged. The exhaustive list-match fixture form
avoids a datatype compiler warning on either lane, and its original-branch
negative control still fails. Every row passes on both final paired lanes.

| # | Input (under P) | Final evidence |
| --- | --- | --- |
| 1 | legacy/reducer-shape | T14 7 OK, native REDUCER; original branch still red. |
| 2 | legacy/excl-rule-unmatched | T14 41 OK, literal silent no-op. |
| 3 | legacy/excl-rule-installed | T14 41 OK, literal target removed. |
| 4 | legacy/excl-solver-unmatched | T14 41 OK, literal silent no-op. |
| 5 | legacy/excl-solver-installed | T14 41 OK, literal target removed. |
| 6 | legacy/excl-looper-unmatched | T14 41 OK, literal silent no-op. |
| 7 | legacy/excl-looper-installed | T14 41 OK, literal target removed. |
| 8 | legacy/excl-split-unmatched | T14 41 OK, literal silent no-op. |
| 9 | legacy/excl-split-installed | T14 41 OK, literal target removed. |
| 10 | legacy/excl-case-unmatched | T14 41 OK, literal silent no-op. |
| 11 | legacy/excl-case-installed | T14 41 OK, literal target removed. |
| 12 | fresh-load/attribute-first | T14 19 OK, clean dynamic load preserves handler/callbacks. |

## Completion criteria (5/5)

| ID | Evidence-backed disposition |
| --- | --- |
| C1 | All twelve rows above match pinned develop without legacy client migration. |
| C2 | Original develop suite unchanged, 73 OK/lane; T15 normal legacy+extension suites 630/72 OK; configured/extended expectations migrated, not deleted (P2.7, P3.7, P4.7). |
| C3 | Code review plus literal/constructor/load/foreign-syntax tests: no old string, constructor assumption, ambient strategy or ordinary module order silently selects extensions (P2.2–6, P3.1–4, P4.1–8). |
| C4 | Native staging, live defaults, exact exception boundaries, history/current-theory replay and installed shared controls covered and passing (P2.9–10, P3.5–6, P4.14). |
| C5 | Required routine/full gates pass on identical implementation bytes; no discovered legacy-reachable divergence remains open. T17 verifies gate continuity rather than rerunning unaffected builds. |

## Audit closure

T17 changes only this ledger, the final report, reproducible audit evidence
and task index/progress. No implementation/test/recipe/optional dependency
changed. No invalidated gate requires a rerun. The pre-existing caller's
TASK_16 progress/commit-ID corrections are preserved. Each of TASK_01–17
has exactly one completion-log line; next task is none.

No concrete new-only splitter algorithm defect was established in this
audit. Algorithm completeness, every possible strategy combination and
cache-retention bounds are separate untested extension scope, not claimed
legacy divergences or silently deferred acceptance work. Universal callback
equivalence, independent clean repository builds, other ML systems/kernels,
higher selftest levels and unconfigured external solver cases remain
unverified; see FINAL_REPORT.md for the complete qualification.
