# Pinned simplifier review inputs

TASK_04's complete public-interface inventory, sealed baseline clients,
expected initial reds and reproduction commands are in
[`PUBLIC_CONTRACTS.md`](PUBLIC_CONTRACTS.md). Its coverage includes all six
changed baseline signatures and unchanged `congLib` interoperability; these
are diagnostic contracts, not claims that source compatibility is restored.

TASK_01 preserves inputs and observations, **not a compatibility or performance
pass**. Starting HEAD is the reviewed candidate; see
[`initial-state.json`](initial-state.json) for the actual checkout, dirty-state,
runtime, build, environment, source identities and drift snapshot.

- Develop: `cccaa27d7099cbadc886983020cbe745db7793f3`.
- Reviewed candidate: `cf1f863b4e5a9712ce1b179f18274eb3451f3954`.
- Review date and original directory: 2026-10-21,
  `/tmp/simplifier-review-20261021/`.
- Evidence identifier: `TASK_01-pins-v1` (the commit adding this directory).
- No predecessor in this task set. Prior cleanup is inventoried in
  [`COVERAGE.md`](COVERAGE.md), not imported as acceptance evidence.

## Immutable inputs and provenance

[`evidence-manifest.json`](evidence-manifest.json) maps every preserved file
back to its original path or Git revision/blob and gives its SHA-256 and size.
[`SHA256SUMS`](SHA256SUMS) uses repository-relative paths.

`inputs/develop/selftest.sml` is the **unchanged original** develop selftest,
recovered directly with `git show <develop>:src/simp/src/selftest.sml`.
It is not today's expanded native selftest or a replacement fixture.
`inputs/develop/Traverse.sig` is likewise the exact original public signature.
Keep both immutable; add new contracts alongside them, not inside them.

The compact original review bundle lives at
[`../performance/review-20261021/`](../performance/review-20261021/).
Its five SML probes and `reproduce.py` are byte-for-byte copies. They remain
colocated because the original script resolves all five via its own directory.
In particular, `abicheck.sml` is real SML: the complete baseline signature
renamed to `LegacyTraverse`, preceded by `open Traverse` and followed by a
structure ascription and success/exit markers. Its exact relationship to the
baseline signature is checked by `verify_evidence.py`.

All 35 supplied review files were small (about 110 KiB combined); preserving
these compact inputs, JSON, raw samples and compressed unique contract/native
observations avoids regenerating historical evidence. No build trees, heaps,
binaries or old `src/simp/compatibility` archive were copied. Nothing in the
caller-owned `/tmp` bundle was changed or deleted.

## Integrity check (from repository root)

```sh
sha256sum -c src/simp/tests/compatibility/SHA256SUMS
python3 src/simp/tests/compatibility/verify_evidence.py
```

The verifier checks preservation, baseline Git objects, signature derivation,
JSON/log agreement and original Python syntax. It does **not** execute any
HOL probe, claim elaboration success or assess benchmark acceptance. It reads
only tracked inputs; it creates no caches or build products.

## Reproduction checklist

Tooling prerequisites: local Git objects for both pins, Python 3.9 or newer,
`sha256sum`, and the configured Poly/ML/HOL tools and dependencies below.

1. Verify the hashes above and availability of both pinned Git commits.
   Record any intentional change as a new fixture, never an overwritten
   historical input.
2. Use Poly/ML 5.9.2 and the configured repository's `bin/Holmake`, `bin/hol`
   and `bin/hol.state0`; record fresh binary/heap hashes. The snapshot hashes
   identify current products only, not missing historical binary hashes.
   Fresh setup, if necessary: `poly < tools/smart-configure.sml` and build
   prerequisites using `CLAUDE.md`'s heap bands. Do not copy build trees.
3. Do not rely on inherited `HOLDIR` (it points elsewhere in this environment).
   Use absolute tool, heap and include paths. The original experiment used
   `HOLHEAP = <repo>/bin/hol.state0`,
   `INCLUDES = <repo>/src/simp/src/poly`, `--no-project`, and `-j1`.
   The current Holmake launcher emits `bin/hol --gcthreads=1 run`.
   Pin all compiler/runtime/heap options identically for both versions.
4. Extract each revision's exact simplifier sources into separate task-owned
   temporary directories. Supply the same original develop selftest and
   maintained `tests/contracts` modules to both. Do not let candidate `.uo`,
   theory products or stale launchers leak into the baseline. Record effective
   loaded module paths, not merely intended search paths.
5. Build executable Holmake fixtures and **execute their launchers**. A `.uo`
   or successful Holmake invocation alone does not establish SML elaboration.
   Observe process exits and complete ordered output. Use selftest/testutils
   conventions; never pipe SML into `bin/hol` as a regression test.
6. Original expected outcomes: baseline ABI success marker versus candidate
   static-error rejection; staging construction printer count 1 versus 0,
   repeated count 1 versus 2, and saved valid tactic `goals=1` versus
   `PrinterFailure`. These are historical expectations, not fresh TASK_01
   results. The original script expects exit 1 only for candidate ABI and 0
   for its other behavioral/storage probes. Historical actual process exit
   codes were not supplied. Do not manufacture them from those expectations.
7. TASK_02 owns the fail-closed paired runner, path verification, result
   schemas and failed/missing/deferred-elaboration negative controls. The
   historical `reproduce.py` is an input to inspect, **not an acceptance
   runner**: it checks exits but not completeness or loaded paths. Its default
   output is next to the originals; always select a task-owned output path.
8. TASK_03 owns fresh initial failures, result-consuming benchmark revisions,
   calibrated counts and baseline/baseline variability. Preserve historical
   probes unchanged: `bench.sml` ignores projection/construction return values,
   so those measurements cannot establish acceptance. Serialize measurements
   against builds/other benchmarks; use fresh ABBA processes and verify outputs.
9. Keep isolated-source comparisons distinct from independent clean builds.
   Record raw CPU, wall and GC observations separately; first verify timer
   accounting. Graph-size results are reachable words, not RSS or byte counts.
10. Remove only task-created temporary sources/products after their last use.
    Leave these immutable inputs and caller-owned artifacts alone. Put fresh
    observations in a new source-tied results directory.

## Maintained executable paired gate (TASK_02)

Use a **new** output directory on every invocation. From the repository root:

```sh
bin/Holmake --no-project --no-cache --no_prereqs \
  --holstate="$PWD/bin/hol.state0" \
  -C src/simp/tests/compatibility -j1 \
  PAIRED_OUTPUT=/tmp/my-paired-evidence check
```

This runs 13 Python validator tests, then private Holmake-built SML launchers
for both exact pinned source revisions, including all six negative controls.
No SML is piped to `bin/hol`. Expected reviewed-candidate staging/signature
regressions are explicitly **expected-red**, not compatibility passes.

Direct driver and baseline-versus-baseline control:

```sh
python3 -B src/simp/tests/compatibility/run_paired.py \
  --negative-controls --output /tmp/my-paired-run
python3 -B src/simp/tests/compatibility/run_paired.py \
  --candidate cccaa27d7099cbadc886983020cbe745db7793f3 \
  --candidate-signature pass --candidate-behavior baseline \
  --negative-controls --output /tmp/my-baseline-control
```

For future repairs explicitly select `--candidate HEAD` (or another Git ref)
and choose `--candidate-signature pass` / `--candidate-behavior baseline` only
when those contracts are intended to pass. Defaults reproduce the reviewed
candidate, NOT an implicit dirty-worktree snapshot. Dirty sources are never
silently substituted for a selected Git object. Resolved revisions, exact
Git blobs/source bytes, generated products, inputs, runtime/heap/config
fingerprints, commands, exits and complete ordered source/observation streams
are retained in compact JSON/gzip receipts. The output folder is never reused.

See [`SCHEMA.md`](SCHEMA.md) for ordered event/result contracts and controls,
[`TASK_02_HANDOFF.md`](TASK_02_HANDOFF.md) for acceptance/commands, and
[`evidence/task02/`](evidence/task02/) for fresh paired and baseline-control
receipts. `paired/Holmakefile` is an installation template, not a standalone
source tree: the driver adds the exact Git modules and signature fixture to
private directories before invoking it. `paired/selftest.sml` follows the
normal testutils convention; the deliberately ill-typed `Deferred.sml` is a
harness-only control, never a production import.

### Isolation limits

These are **mixed-source isolation experiments**, not independent repository
builds. Both sides use today's same prebuilt HOL runtime, state0/min heaps and
shared libraries. Initial heap source maps are metadata, not proof that current
source bytes built those heaps. The driver rejects preloaded simplifier modules,
forces identical private-first search paths, traces actual source elaboration,
audits complete source inventories, and checks source/product hashes again
before cleanup. Shared products are not rebuilt. Undeclared dynamic loads fail
closed if they extend the source map without a traced use.

This is not an OS security sandbox, a certified clean build, a downstream
loading test, or a performance measurement. Do not mutate dependencies or run
builds concurrently; fingerprints detect changes but do not provide filesystem
locking against malicious transient edits. Launcher/compiler/runtime are
trusted. Tested scope is the configured Linux/Poly/ML runtime only. Timing
calibration, output-consuming performance probes and samples belong to TASK_03;
independent clean builds remain separate later gates.

See [`../performance/README.md`](../performance/README.md) for the historical
findings and limitations, and [`TASK_01_HANDOFF.md`](TASK_01_HANDOFF.md) for
this task's validation and acceptance receipt. No production API changes.
