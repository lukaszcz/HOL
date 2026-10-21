# TASK_03 handoff — initial failure/performance baselines

Source/evidence identifier: **TASK_03-baselines-v1**, the landing commit.
Starting and measured current HEAD:
`46c57b3e6972833a8ce483c82b970394e9561494`.
Exact resolved selections and checkout identity are recorded in manifests.
Baseline: `cccaa27d7099cbadc886983020cbe745db7793f3`.
Reviewed candidate: `cf1f863b4e5a9712ce1b179f18274eb3451f3954`.
No production simplifier change exists between reviewed and current HEAD;
both recorded Git diffs against `src/simp/src` and working sources are empty.
The separate current-HEAD observation explicitly resolves `--candidate HEAD`.
This landing commit changes only the harness/docs/evidence, not those sources.

## Bounded acceptance receipt

All TASK_03 criteria are satisfied: all four findings have fresh reproducible
controls on reviewed sources, current-HEAD observations, baseline variability,
retained/exercised outputs, raw calibrated timing batches and retained-storage
baselines. This is **diagnostic reproduction, not a production repair or final
performance acceptance**. No production source/API/control was changed.

- Independent baseline signature execution succeeds; reviewed/current reject
  both added datatype constructors with the exact expected static diagnostics.
- Independent baseline staging observes printers **1/1/1**, saved tactic
  **goals=1**. Reviewed/current observe **0/1/2**, saved **PrinterFailure**.
  These run separately from timings; no timing threshold establishes behavior.
- Six baseline/baseline fresh-process pairs execute before six baseline/
  reviewed pairs. Each process records five samples per eleven workloads,
  plus every calibration batch. AB/BA order alternates without overlap.
- All six existing executable failure controls are rejected on both selections
  in both six-pair experiments, including byte-identical wrong-tree loading.
- One additional baseline/current-HEAD pair observes the unchanged implementation
  explicitly; it is not presented as statistical acceptance.
- Result-consuming probes cover creation, merge, missing exclusion, compilation,
  projection, traversal construction, empty addition, ordinary/reused traversal,
  complete projection/application and complete compilation/application.
- Every storage process observes 0/10/100/1,000 rules. Equal-arity graph roots
  and the original historical method are both recorded. Exact historical
  1,000-rule increments reproduce **83,071 versus 125,096 words**.
- Eight new validator tests, thirteen existing validator tests, complete
  source-path/exit/footer checks and an offline source-binding audit succeed.
  The offline audit additionally rejects wrong selection and changed hashes.

## Timing observations and variability

CPU columns are medians of the six per-process medians, **microseconds per
operation**, including GC. Ratios are medians of six paired ratios, not ratios
of aggregate medians. Brackets are fixed-seed 20,000-resample percentile 95%
bootstrap intervals. No outlier is discarded. CPU, wall, GC and non-GC raw
fields remain separate in receipts and JSON summaries; GC is never added to CPU.

| Workload | Baseline / reviewed CPU us | Paired CPU ratio [interval] | Wall ratio | Baseline/control CPU ratio [interval] |
| --- | ---: | ---: | ---: | ---: |
| `rewrites_1000` | 12.324 / 22.452 | 1.816 [1.753, 1.877] | 1.816 | 0.989 [0.977, 1.014] |
| `merge_frags_1000` | 8.403 / 23.529 | 2.791 [2.673, 2.893] | 2.791 | 0.998 [0.970, 1.012] |
| `compile_1000` | 2077.160 / 2357.934 | 1.135 [1.092, 1.177] | 1.135 | 0.978 [0.905, 1.002] |
| `delete_missing_1000` | 85.618 / 237.194 | 2.771 [2.690, 3.032] | 2.771 | 0.976 [0.925, 1.022] |
| `project_1000` | 0.060 / 0.066 | 1.107 [1.092, 1.274] | 1.107 | 0.848 [0.836, 1.070] |
| `construct_traverse_1000` | 0.133 / 0.168 | 1.255 [1.240, 1.300] | 1.255 | 0.949 [0.914, 1.060] |
| `empty_add_1000` | 0.260 / 0.314 | 1.199 [1.157, 1.238] | 1.199 | 0.960 [0.915, 1.036] |
| `simp_installed_1000` | 1.699 / 1.873 | 1.085 [1.004, 1.126] | 1.085 | 1.125 [0.930, 1.209] |
| `raw_reuse_1000` | 1.613 / 1.645 | 1.012 [0.985, 1.053] | 1.012 | 0.964 [0.947, 1.046] |
| `projection_apply_1000` | 1.875 / 1.928 | 1.024 [0.986, 1.097] | 1.024 | 1.028 [0.949, 1.111] |
| `compile_apply_1000` | 2122.488 / 2157.188 | 1.022 [0.994, 1.045] | 1.022 | 1.020 [0.999, 1.078] |

**Decisions per workload:** creation, merging and missing exclusion reproduce
large diagnostic regressions, independently of the exact historical ratios.
Compile-only, traversal construction and empty addition also show diagnostic
increases on this fixture. No cost-equivalence conclusion is made for any
workload. Projection attribution and ordinary/reused traversal, complete
projection/application and complete compilation/application comparisons are
**unresolved/blocked as cost conclusions**, not passes: baseline process
variability is substantial and/or candidate intervals include one. There is
no task completion dependency on declaring performance equivalence here.

In particular the identical-source control's projection medians vary roughly
0.051–0.061 us, and ordinary simplification roughly 1.63–2.01 us. CPU and wall
both change, so these are not merely wall-clock preemption observations. Their
cause is not established: do not assert a specific code-layout, cache or host
frequency explanation. Host load averages were about 6.5–8.3 over 32 available
CPUs; this task did not run concurrent builds or benchmarks, but did not obtain
exclusive host ownership or pin a CPU. No provenance/path/hash failure occurred
in the final experiments. Small results must not be relabeled as acceptance.

The original four findings are recovered despite that uncertainty: deterministic
behavior/signature controls, clearly separated construction/exclusion costs,
and exactly repeatable storage deltas. Required measured batches range
0.232–0.553 seconds in the reviewed experiment (0.244–0.536 in the control).
Counts vary per process/workload and are retained, not inferred from medians.
A development pilot is not included in these statistics.

## Storage observations

All repetitions agree exactly within each implementation, including the
baseline/baseline control. The table uses equal-arity root subtraction:

| Rules | Compiled baseline | Compiled reviewed/current | Fragment baseline | Fragment reviewed/current |
| ---: | ---: | ---: | ---: | ---: |
| 0 | 21 | 35 | 9 | 14 |
| 10 | 4,022 | 6,447 | 69 | 104 |
| 100 | 11,204 | 17,229 | 609 | 914 |
| 1,000 | 83,070 | 125,095 | 6,009 | 9,014 |

Historical compiled deltas are exactly one word higher because its roots have
unequal tuple arity; see README for all expressions. Base standalone graphs
are 674,393 versus 675,599 words. Raw fragment/simpset/anchor/union sizes are
retained for every process, not just the subtracted totals. These are reachable
graph words, not bytes, allocation, RSS, global-root graphs or lifetime tests.

Structural anchors on reviewed/current sources: `simpLib.sml:24–25,339–343`
creates source slots on ordinary fragment construction; `415–422` creates
slots during merging; `624` starts the exclusion path that also scans source
inventories; `3057` retains goal-application staging. `Traverse.sig:91,103`
contains the two added constructors. Source inventories/blobs/hashes in the
manifests, not mutable line numbers, pin these observations. No production
repair or final representation audit is claimed.

## Commands, exits and evidence

All paths below are under `src/simp/tests/performance/evidence/task03/` unless
specified otherwise. `validation.json` records commands/exits/hashes and exact
input/runtime/source identities. Manifests pin all benchmark/validator sources,
Git blobs, private products, launchers, actual loaded paths, shared dependency
hashes, Poly executable and dynamic runtime libraries, heap/options and machine.

| Command/check | Exit | Evidence |
| --- | ---: | --- |
| `bin/build -t --seq=tools/sequences/upto-parallel` | 0 | `routine.log.gz`; after final SML edits, before measurement |
| README Holmake `diagnostic` command, durable output path | 0 | `diagnostic.log.gz`; 21 Python tests, 56 process/control launches |
| Explicit `--candidate HEAD --performance-pairs 1 --samples 5 --batch-seconds 0.25` | 0 | `current-head/manifest.json`, `current-head.log.gz`; six launches |
| Offline archived source-binding audit | 0 | `validation.json`; 26 performance receipts, six rejected mutation controls |
| Recompute both six-pair summaries | 0 | `baseline-summary.json`, `reviewed-summary.json`; raw receipt hashes |
| Immutable verifier / SHA-256 checks | 0 | `validation.json`; all 37 original artifacts unchanged |
| `git diff --check`, staged whitespace check | 0 | `validation.json` |

Reproduce via README's maintained Holmake command with a **new** output path.
`baseline-control/` and `reviewed/` each have complete manifests, two build
receipts, sixteen independent behavior/signature/control receipts, and twelve
performance receipts. `current-head/` contains the same independent positive/
expected-red controls without negative controls, plus two timing receipts.
Build exit 0 alone is never counted as signature success. Expected signature
process exit 1 is explicitly labeled expected-candidate-red, not a passing
compatibility result. Deferred launchers are actually executed.

Timer attribution: archived upstream `polyml-v5.9.2-Timer.sml.gz`, original
bytes from `https://raw.githubusercontent.com/polyml/polyml/v5.9.2/basis/Timer.sml`,
SHA-256 `e68d88cb8d14479806ddc540571dc5924e5756478f01ffe775fe74be5f503fd2`.
Its original copyright/license are retained. `checkCPUTimes` subtracts GC from
inclusive CPU; `checkGCTime` reports GC user only. Empirical five-full-GC controls
observe about 0.100–0.126 CPU user seconds in the two main experiments. Maximum
sequential user-accounting difference in measured batches is 21 microseconds,
well inside the documented 20 ms sanity guard. The upstream tag is corroboration,
not a claim of independently certified provenance for the installed binary.

A first pilot failed at executed elaboration due to SML `:=`/`++` precedence;
explicit parentheses repaired the fixture and its second pilot succeeded.
`pilot-receipt.json` preserves the unique failure/status. Neither pilot enters
final summaries; no failed observation was turned into an inconclusive pass.

## Changed files, API decisions and scope

- `Performance.sml`, `performance_schema.py`: output-retaining probes and strict
  complete calibration/batch/consumption/accounting/storage schemas.
- `Holmakefile`, `.gitignore`: serial maintained diagnostic command and cache/
  default-output exclusions; compiled fixture built only in private trees.
- `summarize.py`: per-process medians, separate CPU/wall/GC, paired intervals,
  raw receipt hashes. It validates metrics/order; source binding is separately
  checked by the online runner and `audit_evidence.py`.
- `test_performance.py`, `audit_evidence.py`: malformed metrics and archived
  selection/hash negative controls without production instrumentation.
- `../compatibility/run_paired.py`, `SCHEMA.md`: optional performance fixture,
  identical options, AB/BA fresh processes, actual dynamic-runtime fingerprints,
  and end-of-experiment input-mutation checks. Existing behavior contracts are
  unchanged; default non-performance runner still works.
- `README.md`, this handoff, evidence directory, and task progress: durable
  methodology, observed findings/uncertainties, commands/exits and actual status.

No production API, compiler, mutable control, loading boundary or scheduling
change. Baseline immutable probes/signature/selftest remain byte-identical.
Only Linux/aarch64, configured Poly/ML 5.9.2 and mixed-source isolation are
measured; shared heaps/libraries are prebuilt, not certified clean builds.
No total-allocation, release, downstream, full-build or cross-platform claim.
Final performance acceptance and expanded matrices remain explicitly separate
plan tasks; their original assertions/gates are not weakened here.

No blocker remains for the bounded TASK_03 diagnostic baseline. TASK_04–06 are
now ready. No new out-of-scope production repair was attempted. Agent-created
private trees/products are automatically removed; pilot directories, downloaded
scratch input, logs and the local performance Holmake cache were removed after
retaining compact evidence. Unrelated preexisting ignored artifacts and the
separate `.agent-files` repository's unrelated files were preserved.
