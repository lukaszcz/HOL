# TASK29 caller-codegen diagnostic

`caller_codegen.py` collects fresh compiler output for the actual matrix
callers, rather than treating an older simpLib-only listing as their code.
It does **not** approve timing, cumulative allocation or TASK29.

From the repository root, with no other build or measurement in this checkout
(W is the existing `compatibility/tools/root-wrapper.sh`):

```sh
W python3 -B src/simp/tests/performance/caller_codegen.py \
  --candidate COMMIT --case frag_record --size 0 \
  --batch-iterations 33554432 --authorize-diagnostic --output NEW_DIRECTORY
W python3 -B src/simp/tests/performance/caller_codegen.py \
  --candidate COMMIT --case compile_collector --size 10000 \
  --batch-iterations 64 --authorize-diagnostic --output OTHER_NEW_DIRECTORY
python3 -B src/simp/tests/performance/caller_codegen.py --replay NEW_DIRECTORY
```

Both selections must meet the runner's 0.1-second minimum at the declared
count; a short count rejects, not silently recalibrates. Historical fixtures
compiled `sample` AFTER calibration and embedded the selected count, so the
common count also fixed that literal. The current fixtures precompile the
complete driver (see `PROTOCOL.md`); common counts still control calibration
history and operation counts, not heap state, pool identity or GC scheduling.

## Isolation and interpretation

Each invocation collects fresh B/B and B/C private-source processes using the
unchanged paired runner's build, library/tool/source/path, proof, callback and
output-consumption checks. The private loader includes `CallerCodegen.sml`;
original workload sources are copied byte-for-byte. The printing bracket
covers `Cond_rewr`, `Traverse`, `simpLib`,
`MatrixSupport` and the installed `Performance` fixture. It restores all three
compiler switches after success or an exception. It does not inspect closures,
read process memory, cast runtime values or modify production modules.

Full stdout is archived **before** parsing, including a failed process. Native,
ICode, backend and optimized-lambda records retain emission order, repeated
names, exact text hashes and original line offsets. Every target must emit
its optimized-lambda form; a missing form is a failure, not fabricated.

The exact dump is retained once. Paired receipts retain all original protocol,
raw telemetry, measurements, proof checks and the complete stdout's hash/length
and archive binding, not another copy of the compiler dump. Reports retain
record metadata and comparison decisions; raw bodies are in stdout.

The manifest suite is deliberately `caller-codegen-diagnostic`, rejected by
timing admission. Printing and the new loader change layout/heap state. The
single process pair is structural evidence, **not** ten-pair acceptance, and
its timings must not replace ordinary-runtime observations. Replays recheck
source Git bytes, diagnostic-loader construction, transport, paths, proofs,
callbacks, telemetry and every comparison without accepting timing results.

The AArch64 comparison preserves every instruction/offset except the two
operands of adjacent `adrp; ldr` pool materializations. Exact bytes and
operands remain available. Equal normalized instruction text does **not**
bind pool contents, indirect targets or opaque printed constants. Neither it
nor static reservation instructions proves equal allocation or runtime cost.

## Tests and transport

```sh
python3 -B -m unittest discover -s src/simp/tests/performance \
  -p test_caller_codegen.py -v
CALLER_CODEGEN_EVIDENCE=UNPACKED_DIRECTORY python3 -B -m unittest discover \
  -s src/simp/tests/performance -p test_caller_codegen.py -v
```

The optional real-archive test executes seven coherent mutations, including
source/loader/fixture changes, missing proof traces, altered compiler markers,
inventory loss and changed comparison decisions. It rejects each at its
intended guard. Default tests cover synthetic parser/loader/transport faults;
synthetic listings are not measurement evidence.

A collected directory can be packed into the lossless `evidence_bundle.py`
transport and unpacked later for inspection:

```sh
python3 -B src/simp/tests/performance/evidence_bundle.py unpack \
  BUNDLE.json.xz NEW_SCRATCH_DIRECTORY
python3 -B src/simp/tests/performance/caller_codegen.py \
  --replay NEW_SCRATCH_DIRECTORY
# Remove only this newly created scratch directory when finished.
```

Use the containing source revision for input-seal replay. Scope is the local
Linux/AArch64 Poly/ML 5.9.2 runtime/shared HOL heap, not clean independent
builds, a compiler-lineage proof or another platform.
