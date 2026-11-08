# TASK28 P09 workload and prerequisite ledger

`matrix.json` is the machine-readable coverage ledger. **Runnable is not
measured, passing, or release-approved.** Each stable `cases` key names exactly
one `PERF_CASE`, its fixture, and a named `size_sets` grid. Each `requirements`
key covers one P09 requirement with runnable cases, an executable external
check, or an explicit prerequisite blocker. External checks and blockers retain
a reason/scope, concrete commands, and task gate owner. A missing fresh receipt
alone does not make an existing check prerequisite-blocked. No blocked
loading/storage/downstream case is represented by a fake benchmark.

`matrix_schema.py` independently freezes all **69 requirement keys**, their
coverage (including construction/reuse/complete stages), **107 case bindings**,
and exact size grids. It rejects deletions, extras, unknown fields, duplicate
JSON keys/list members, wrong references and fixture/source-inventory drift.
Changes to the contract require an explicit schema review, not just ledger edits.

```sh
python3 -B src/simp/tests/performance/matrix_schema.py
python3 -B src/simp/tests/performance/matrix_schema.py --json
python3 -B -m unittest discover -s src/simp/tests/performance -p test_matrix.py
```

Both report formats list every gate as `runnable_case`, `runnable_external`, or
`prerequisite_blocked`, with workload grids or prerequisite/external commands.
An invalid matrix exits nonzero without issuing a completeness report. A valid
matrix may contain explicit blocks and is **not** performance acceptance.
Integration API: `load_matrix()` and `validate_matrix(data)` return the validated
ledger; `get_case(case, size)` returns the fixture basename and rejects unknown
cases or sizes outside that case's grid (no bool/float/string coercion).
`report()` returns the machine-readable completeness report. All entry points
validate live sources and the frozen contract; no stale validation cache.

Reference: `.agent-files/PLAN_performance.md`, complete P09 matrix;
`.agent-files/tasks/TASK_28_expanded_acceptance_harness.md`. API/coverage inputs:
`../compatibility/migration/final-apis.tsv`, `migration/TASK27.md`,
`COVERAGE.md`, TASK26 relocation and TASK27 handoffs. Actual final signatures
are authoritative; the historical API table is not a runtime inventory.
Ordinary clients use `simpLib`/`Traverse`; there is no implicit extension
promotion or disabling of extensions to obtain ordinary performance numbers.

## Shared fixture protocol

- One case and one size per fresh process: `PERF_CASE`, `PERF_SIZE`.
- Existing `Paired` protocol, exactly one label equal to `PERF_CASE`:
  `labels=[case], consumed={case:1}, storage=False` when validating.
- `PERF_SAMPLES` and `PERF_SECONDS` retain the calibrated doubling schedule.
  Calibration starts at one; each raw sample uses the calibrated count.
- Both fixtures emit the existing forced-GC `timer.accounting` control,
  `workload inputs`, ordered calibrations/batches/result checks, and `sink`.
- Raw timing order is wall, non-GC user/system, GC user/system, inclusive CPU
  user/system, `checkGCTime` GC-user, consumed count. Inclusive CPU already
  contains GC: never add GC again. Sequential timer reads allow the existing
  20 ms accounting tolerance; that is not a regression allowance.
- Every iteration retains a typed result and consumes exactly one. The final
  retained output is semantically exercised after **every** calibration and
  sample, not just at process exit. Construction-only results are applied
  outside timing; reuse and complete include actual application. Tactic
  application includes proof reconstruction through the returned validation.
- Both fixtures use `RuntimeMetrics.sml`: exactly one `@@MATRIX_RUNTIME`
  before/after record for every calibration and sample, including actual full/
  partial GC and sharing-pass counters, heap/allocation-area sizes, and Linux
  RSS/HWM snapshots. Counters bracket batches, not cycle-exact timer regions;
  verification and `/proc` reads are excluded, small record/timer overhead is
  not. Allocation-area capacity/free space is not cumulative allocated bytes.
- `storage_graph` additionally emits `@@MATRIX_STORAGE` (reachable words) and
  `@@MATRIX_RELEASE` (controlled weak-ref collection). The runner and archived
  auditor validate these separate records, telemetry ordering/counts and source
  seals. They are not extra Paired observations. A graph row is neither RSS nor
  allocation nor a collection proof. Process-lifetime HWM and its increase are
  not an exact temporary batch peak; zero increase does not mean zero peak.

Acceptance runs remain serialized, source/input/path/options sealed, fresh
AB/BA processes with at least ten pairs, baseline/baseline controls, raw CPU,
wall and GC, paired ratios, medians and confidence intervals. No outliers are
removed. Decisions are per workload: pass/fail/inconclusive; an absent
prerequisite is blocked, never pass. Tiny semantic smoke runs do not meet
these timing criteria. See `acceptance.py` and the runner integration.

Example, after committing/sealing the candidate and stopping other builds:

```sh
python3 src/simp/tests/performance/acceptance.py run \
  --mode isolated --baseline BASELINE_FULL_40_HEX_COMMIT \
  --candidate CANDIDATE_FULL_40_HEX_COMMIT \
  --case traversal_deep --size 100 --pairs 10 --samples 5 \
  --batch-seconds 0.2 --authorize-measurements --output FRESH_OUTPUT
```

Case selection must choose the ledger's fixture, not blindly copy the fragment
fixture for every ID. Independent mode requires its separately validated build
manifest; a common `hol.state0`/`sigobj` run is explicitly **source isolation**.

## Runnable fragment, compiler, exclusion, history and graph cases

Owner: `MatrixPerformance.sml` plus `MatrixSupport.sml`. Every rule-count grid
is **0, 1, 10, 100, 1000, 10000**; zero genuinely tests the empty case.

| P09 requirement | Stable cases (see JSON for every exact ID) |
| --- | --- |
| Empty/scaled, named/anonymous creation | `frag_create`, `frag_named`, `frag_named_rules`, `frag_record` |
| Update, duplicates, merge | `frag_update`, `frag_duplicate`, `frag_merge`, `frag_named_merge` |
| AC and TypeBase | `frag_ac`, `frag_ac_merge`, `frag_typebase`, `frag_type_lookup` |
| Small/large batches and repeated single adds | `compile_batch`, `compile_single` |
| Empty/excluded additions | `compile_empty`, `compile_excluded` |
| Conditional/bounded/AC compilation | `compile_conditional`, `compile_bounded`, `compile_ac` |
| Stateful makers, user conversions, collectors | `compile_maker`, `compile_user`, `compile_collector` |
| Construction/reuse/complete, supplied rules | `compile_construct_conv`, `compile_reuse`, `compile_complete`, `compile_supplied` |
| Empty/missing/matching/batched/qualified/partial names | `exclude_empty`, `exclude_missing`, `exclude_matching`, `exclude_batch`, `exclude_qualified`, `exclude_partial` |
| Literal namespace-looking names | `exclude_literal_namespace`, `exclude_literal_exact` |
| Dproc/mixed deletion | `exclude_dproc`, `exclude_mixed` |
| Markers and replay | `exclude_marker`, `exclude_marker_reuse`, `exclude_replay` |
| Tactic markers: construction/reuse/complete | `exclude_tactic_construct`, `exclude_tactic_reuse`, `exclude_tactic_complete` |
| History removal/force/excluded fragments | `history_remove`, `history_force`, `history_excluded` |
| Theory-change exclusions/bounds/limits/collectors | `history_theory_change`, `history_bounded`, `history_limit`, `history_collectors` |
| Replay with changing custom makers | `history_makers` |
| Retained reachable graph and rule-count slope | `storage_graph` |

These fixtures verify complete theorem conclusions/hypotheses, ordered history
and relevant callback counts. Tactic marker stages use `SIMP_TAC` with `Excl`
and require exactly the unchanged residual `([],target)`, reconstructed with
`ASSUME target` through the returned validation. Construction retains a tactic
checked after the batch; reuse saves it outside timing; complete constructs,
applies and validates inside. `history_makers` replays both filter changes and
the named late fragment: the first maker runs `2*n` times and the later maker
`n` times per replay (exactly `3*n` callbacks), with full proof/history checks. They do not create extension source inventories.
Graph slope requires comparing all sizes, not just accepting one graph row.
The separate release probe exercises a live conversion wrapper and full-GC
retention control, drops the wrapper and observes collection of its controlled
simpset **ref** after three full collections. Poly/ML's weak API accepts refs,
not opaque internal simpset/net objects: this does not rule out their independent
global retention. That stronger lifetime gate remains blocked below.

## Runnable traversal and client cases

Owner: `ClientPerformance.sml`. All use original ordinary types/APIs.

| Requirement | Stable IDs and actual workload |
| --- | --- |
| Construction/private-context setup | `traversal_construct`, `traversal_context_construct`; retain closure, exercise it after every batch |
| Complete context operation | `traversal_complete`; construction plus contextual application |
| Reuse/lookup hit/miss | `traversal_reuse_hit`, `traversal_reuse_miss`; miss totalized to reflexivity |
| Deep terms and congruences | `traversal_deep`, `traversal_congruence`; unary spine with actual depther and `MK_COMB` proof; reuse versus complete |
| Weakening | `traversal_weakening`; genuine weakener factory, no successful high/low-priority reducer |
| Repeated side conditions | `traversal_side_conditions`; two calls to the traversal's solver continuation for the same condition, retained condition hypothesis |
| Failed candidates | `traversal_failed_candidates`; solver fails on an unprovable condition before the successful candidate |
| Saved conversion | `traversal_saved`; retained closure applied repeatedly, exact kernel proof/hypotheses |

Depth grids are **0, 1, 10, 100**. Atomic construction/hit/miss/weakening cases
use size 0: size does not secretly mean a rule count for an atomic fixture.

Every tactic family below has **three exact IDs**, ending in `_construct`,
`_reuse`, `_complete`. All IDs are explicitly enumerated in JSON, not regex
promises. Size is additional assumption count, **0/1/10/100/1000/10000**.

| Family prefix | Operation and verification |
| --- | --- |
| `tactic_supplied`, `tactic_installed` | Same rewrite supplied to `SIMP_TAC` or already installed; identical ordered residual goal |
| `tactic_asm` | `ASM_SIMP_TAC` with scaling assumptions |
| `tactic_full`, `tactic_reverse` | Full/reverse-full passes; exact reconstructed hypothesis set |
| `tactic_no_strip_full`, `tactic_no_strip_reverse` | Corresponding no-strip passes |
| `tactic_dependency_full`, `tactic_dependency_reverse` | Nonclosing ordered residual dependency propagation; full retains `p=q,q=r`, reverse produces `p=r,q=r` |
| `tactic_global` | Original global repeated `CHANGED_TAC (allasms ...)` fixpoint followed by assumption simplification |
| `tactic_req0`, `tactic_reqd` | Requirement wrappers and saved-tactic reuse |
| `tactic_req0_reqd`, `tactic_reqd_req0` | Both nested requirement-wrapper orders |

Every returned validation receives genuine residual proofs. Exact conclusion,
complete hypothesis set, oracle-free tags, residual goal/assumption order are
checked. Construction is not silently charged to reuse, nor reconstruction
omitted from the application measurement. These are performance inputs, not a
replacement for the richer callback/throwing-printer behavioral contracts in
`../compatibility/staging` and `../tactics`.

| Downstream case | Scope |
| --- | --- |
| `downstream_arithmetic` | Ordinary `numLib.arith_ss` construction/application on `n+0=n` |
| `downstream_reduce` | Actual `reduceLib.REDUCE_CONV` on `n+0` |
| `downstream_boss` | Actual `bossLib.boss_ss` and assumption tactic, validated proof |

Arithmetic/reduce size is numeral value (1/10/100/1000/10000), **not** a claim
of linear proof-workload scaling. Boss uses size 0. The client fixture's
static ordinary num/reduce/boss dependency closure is available on the shared
baseline environment, and intentionally outside its workload timer. This
fixture therefore makes no first-load/extension-absence measurement.

## Seven explicit prerequisite blockers (never synthetic fixtures)

The JSON stores exact reasons and prerequisite commands. These are actual
runtime/environment limitations, not missing rows or absence-as-pass:

| Blocker | Missing prerequisite / gate owner |
| --- | --- |
| `allocation_prerequisite` | Poly/ML 5.9.2 has no cumulative allocated-byte counter; need a supported counter or version-pinned allocator instrument. Heap/free snapshots and Python controls cannot supply it; TASK29/33. |
| `rss_prerequisite` | RSS and process-lifetime HWM snapshots exist, but an isolated exact temporary-peak accounting domain is unestablished; TASK33. |
| `lifetime_prerequisite` | Controlled simpset-ref wrapper collection exists; opaque internal-object/global-root lifetime needs a stronger supported weak/finalizer or live-heap API; TASK33. |
| `integer_prerequisite` | Independent ordinary integer exports; shared `sigobj` lacks intReduce/intLib. Candidate-only local products are not baseline dependencies; TASK32. |
| `real_prerequisite` | Independent ordinary real exports; shared `sigobj` lacks realSimps; TASK32. |
| `independent_routine_prerequisite` | Fresh independently configured baseline/candidate snapshots, routine builds and sealed results; TASK32. |
| `independent_full_prerequisite` | The same clean snapshot prerequisites plus full builds with explicit `-F`; TASK32/36. |

Loading startup is now runnable externally, and actual batch GC counts are
required by both fixtures. Neither remains a prerequisite blocker. Runnable
source-isolated loading is still not independent-build loading acceptance.

## Runnable external checks (fresh execution required, not blocked fixtures)

| External check | Executable coverage / task owner |
| --- | --- |
| `loading_audit` | TASK27's eight fresh-process simpLib/congLib order/path/callback/extension-absence scenarios. TASK28/31/33; semantic checks only, not startup timings. |
| `loading_timing` | `loading.py` first-import CPU/wall/GC timings, two fresh pilots, baseline controls and 40 AB/BA pairs of 5 fresh imports, bound to the candidate semantic receipt; TASK28/31/33. Source isolation, not independent-build acceptance. |
| `extension_consumer` | Existing TASK25 isolated migration driver with the sealed patch against the final candidate; TASK28/32. Does not itself supply paired independent proof-performance acceptance. |
| `independent_build_mode` | Existing strict independent-build manifest verifier; TASK28/32/33. Actual clean snapshot prerequisites remain at the blocked downstream build gates. |
| `extension_suite` | Normal-level ordinary/extension integration and strict post-list native suite; TASK28/35/36. Suites remain enabled; no fresh receipt is claimed by listing a command. |

For the runnable fresh-load gate, use TASK27's configured-root-aware command:

```sh
sh src/simp/tests/compatibility/evidence/task26/root-wrapper.sh \
  bin/Holmake -C src/simp/tests/api-audit check
```

Existing TASK27 instrumentation checks actual imports, defining paths,
initialization callbacks, and extension absence. Use a receipt bound to the
selected candidate's actual source bytes. Startup timing is implemented in
`loading.py`; unlike `acceptance.py`, it requires explicit `--baseline`.
The ledger's command templates must be completed with that option:

```sh
python3 -B src/simp/tests/performance/loading.py \
  --baseline DEVELOP_PIN_FULL_40_HEX_COMMIT \
  --candidate CANDIDATE_FULL_40_HEX_COMMIT --module simpLib \
  --api-audit /absolute/path/to/receipt.json \
  --authorize-measurements --output NEW_LOADING_DIRECTORY
```

Repeat with `--module congLib` and a different output. See
[`PROTOCOL_LOADING.md`](PROTOCOL_LOADING.md): the latter includes simpLib's
first import, not its marginal cost. `success` is completion, not a metric pass.

The fresh extension commands are deliberately **external to the ordinary
performance process**, not replaced by an extension-disabled build:

```sh
bin/Holmake --holstate="$PWD/bin/hol.state0" \
  -C src/simp/src -j1 HOLSELFTESTLEVEL=1 all
bin/Holmake --holstate="$PWD/bin/hol.state0" \
  -C src/simp/tests/native-extension -j1 check-full
bin/build -t --seq=tools/sequences/upto-parallel
bin/build -t -F
python3 src/simp/tests/compatibility/run_task25_consumer.py \
  --consumer-patch \
  src/simp/tests/compatibility/evidence/task25/consumer.patch \
  --simplifier-revision CANDIDATE --output FRESH_CONSUMER_OUTPUT
```

Use fresh output locations. `CANDIDATE`/`BASELINE` placeholders must resolve to
sealed commit/tree identities, not a moving HEAD. The consumer driver uses a
private checkout; the caller-owned external worktree is read-only input.

## Maintained validation, not performance approval

`Holmake check` runs Python discovery, matrix completeness, real Python negative
controls, then `smoke_matrix.py --scope small` serially. The default smoke
executes the 51 MatrixSupport cases at 0/1/10 on both selected implementations;
it is not all 107 client/fragment cases or the full grid. `--scope smoke` adds
five scalable cases at larger sizes; `grid` excludes four costly 10000-rule
single-add/AC cases, which require explicit `--scope expensive`. All outputs
are source-tied, exclusive-created JSON/logs; use new paths for each run.
`Holmake runtime-smoke` separately checks actual GC/RSS/controlled-ref release.
See [`README.md`](README.md) for target commands and optional real client tests.

The main ten-pair experiment validates the integrated measurement machinery,
not performance approval for the entire matrix. Earlier temporary validation
on non-ledger sizes or superseded fixture versions is not final source-tied
evidence. Final observations must match the selected committed source, current
fixture/input seals and declared grid. No smoke, manifest admission or isolated
experiment closes the independent-build observations and seven blockers.
