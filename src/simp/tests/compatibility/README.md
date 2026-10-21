# Pinned simplifier review inputs

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

See [`../performance/README.md`](../performance/README.md) for the historical
findings and limitations, and [`TASK_01_HANDOFF.md`](TASK_01_HANDOFF.md) for
this task's validation and acceptance receipt. No production API changes.
