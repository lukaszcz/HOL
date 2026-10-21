# TASK_02 handoff — isolated runner and failure detection

Source/evidence identifier: **TASK_02-paired-v1**, the commit adding this file.
Starting HEAD: `0ff88e4171cf3178d81ba263901c608b3aeb3c93` (TASK_01).
Exact baseline: `cccaa27d7099cbadc886983020cbe745db7793f3`.
Exact reviewed candidate: `cf1f863b4e5a9712ce1b179f18274eb3451f3954`.
There are no production simplifier changes between reviewed and starting HEAD.
Pre-existing ignored `.agent-files` edits/untracked files were preserved.

## Acceptance receipt

All bounded TASK_02 criteria are satisfied; no blocker remains for TASK_03.

- `run_paired.py` extracts exact Git source bytes into separate private trees,
  including Poly BloomApprox and generated simplifier theories. Both sides
  use identical shared dependencies, state0 heap and one-GC-thread launchers.
  Each fixture/control executes in a fresh process. No SML is piped to HOL.
- `paired/runner.sml` imports no simplifier before recording its initial heap;
  it sets an explicit private-first search path and traces actual elaboration.
  Complete initial/final source inventories, physical/HFS paths, source/input/
  runtime/product hashes, options, commands and process exits are retained.
- The complete old signature/ascription is executed as SML through a real
  Holmake launcher. `SignatureCheck.sml` is mechanically derived from the
  immutable review `abicheck.sml`: only its last process exit is replaced by
  a counted `testutils` assertion so the runner can issue its mandatory footer.
  The complete signature and ascription are unchanged. The immutable input is
  verified against the exact baseline Git signature before building.
- Baseline signature succeeds (exit 0, one check). Candidate signature rejects
  BOTH added constructors at elaboration (exit 1, zero checks), explicitly
  labeled expected-candidate-red. Arbitrary static errors do not count.
- Baseline staging observes printer counts **1/1/1**, saved outcome **goals=1**;
  candidate observes **0/1/2**, saved outcome **PrinterFailure**, explicitly
  expected-red. Both execute three testutils checks. These are bounded controls,
  not replacements for the larger original/native/traversal/exclusion suites.
- All six executable negative controls are rejected on BOTH selections:
  missing observation, missing footer, complete output with failed exit,
  other tree's loaded source paths, deferred int/string elaboration error,
  and an unexecuted launcher (`true` instead). Control-specific failure
  reasons are checked; the deferred control verifies its actual static error.
- Baseline-versus-baseline repeats all 16 launches successfully, including
  rejecting wrong paths when their source bytes and behaviors are identical.
- Thirteen Python validator tests additionally reject transport corruption,
  incomplete inventories, mutated sources, unrelated static errors and other
  malformed receipts. Timeout tests prove descendants cannot outlive cleanup.
- `Holmakefile` provides maintained `python-tests` and `check` targets;
  `paired/Holmakefile` is installed only inside private source trees. Behavioral
  fixtures use `testutils.tprint/OK/die` and executable Holmake conventions.

## Changed files / decisions

- `run_paired.py`, `test_runner.py`, `SCHEMA.md`, `Holmakefile`, `.gitignore`,
  `paired/{Holmakefile,Paired.sml,runner.sml,selftest.sml,Deferred.sml}`:
  maintained runner, strict complete ordered schemas, test fixtures/controls.
- `README.md`: reproducible commands, explicit expectations and limitations.
- `evidence/task02/`: compact manifests, gzip process receipts and validation
  logs. These are source-tied isolation evidence, not independent builds.
- Root `holproject.toml`: only the immutable review directory's line-length
  limit is disabled, following existing per-directory conventions. The first
  required sanity build exposed 20 historical long lines there. Reformatting
  would corrupt pinned evidence; all other style checks remain enabled and
  the repeated required sanity build passes. No originals were modified.
- No production API, representation, control-cell, callback scheduling or
  shared-infrastructure change. No new compatibility/performance pass claimed.

The signature failure is an intentionally unresolved production regression,
not an acceptance blocker for this runner task. Defaults reproduce the reviewed
pin. Future repair gates must explicitly select their revision and passing
expectations, never silently retain the expected-red policy.

## Validation / durable evidence

Full commands, exits and log hashes: [`evidence/task02/validation.json`](evidence/task02/validation.json).
Every run manifest includes actual Git blobs, source/input/runtime hashes and
resolved loaded paths. All accepted run inputs/products are rechecked at pair
end. Gzip receipts keep the complete parsed ordered event stream and unique
compiler diagnostics without retaining build trees or heaps.

| Check | Exit | Evidence |
| --- | --- | --- |
| Holmake `check`, with negative controls | 0 | `evidence/task02/paired/manifest.json`; 13 Python tests, 16 launches, all expected outcomes |
| Baseline-versus-baseline, explicit passing modes | 0 | `evidence/task02/baseline-control/manifest.json`; 16 launches |
| `bin/build -t --seq=tools/sequences/upto-parallel` | 0 | `evidence/task02/routine-final.log.gz` |
| Immutable integrity verifier | 0 | 37 artifacts; baseline signature and ABI derivation unchanged |
| `git diff --check`, staged whitespace check | 0 | `evidence/task02/validation.json` |

Reproduce the maintained integration from repository root (new output path):

```sh
bin/Holmake --no-project --no-cache --no_prereqs \
  --holstate="$PWD/bin/hol.state0" \
  -C src/simp/tests/compatibility -j1 \
  PAIRED_OUTPUT=/tmp/task02-fresh check
```

The baseline-control command is recorded in the README and validation JSON.
Both sides used the configured Linux/aarch64 Poly/ML **5.9.2**, one GC thread.
The source pins and all fresh runtime/heap identities are in the manifests;
no historical exit or heap provenance was invented.

## Isolation limitations / next task

This is **mixed-source isolation**, not independent repository builds. Shared
runtime/heaps/libraries are prebuilt; initial source maps do not certify the
source provenance of those heaps. The driver rejects any preloaded simplifier,
checks exact loaded paths and fails closed on untraced source-map additions,
but it is not an OS sandbox or a lock against concurrent filesystem mutation.
Do not run builds concurrently. Other runtimes/platforms are unmeasured.

TASK_03 owns timing calibration, result-consuming performance probes, fresh
four-finding samples and baseline variability, as already bounded in the plan.
There is no timing/performance or independent-clean-build claim in TASK_02.
Later tasks retain the original 73/47/929 contract coverage; it has not been
silently replaced by these small runner controls.

All agent-created copied source/product trees, development outputs, caches and
scratch logs were removed after retaining compact unique evidence. Existing
caller-owned build products and historical `/tmp` review inputs were untouched.
The routine build's normal repository products remain normal build products,
not copied evidence. Progress is updated only for this completed task and its
newly unblocked dependent, with one completion-log line.
