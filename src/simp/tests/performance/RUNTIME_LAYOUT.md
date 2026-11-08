# TASK29 actual runtime-object diagnostic

`runtime_layout.py` inspects instantiated objects, not compiler-printer names.
It does **not** approve timing, allocation, heap parity or TASK29A.

## Collection and replay

From the repository root (W is the configured-root wrapper described in
`README.md`), using new output directories:

```sh
W python3 -B src/simp/tests/performance/runtime_layout.py \
  --candidate FULL_COMMIT --case frag_record --size 0 \
  --batch-iterations 33554432 --authorize-diagnostic --output NEW_DIRECTORY
W python3 -B src/simp/tests/performance/runtime_layout.py \
  --candidate FULL_COMMIT --case compile_collector --size 10000 \
  --batch-iterations 64 --authorize-diagnostic --output OTHER_DIRECTORY
python3 -B src/simp/tests/performance/runtime_layout.py --replay NEW_DIRECTORY
```

Both commands collect one fresh B/B and B/C structural pair, with a common
predeclared calibration history/count. Ordinary sources and workload fixtures
are copied unchanged by `run_paired.py`; compiler printing remains disabled.
The only runner change is a separate declaration **after** the unmodified
`val result` declaration returns. It then compiles/loads `RuntimeLayout.sml`,
which calls the supported `PolyML.showSize` on the actual `run`, `step`,
`measured` and `experiment` functions. No unsafe casts, unchecked memory reads
or explicit collections are added. Online source inventories include the
postlude's own traced use/completion. All raw output, including a rejected
process, is saved before parsing.

The host/user/gitdir advisory locks serialize cooperating tools. Diagnostic
authorization is **not** a claim of host exclusivity. These outputs use
`suite="runtime-layout-diagnostic"`, which timing admission rejects. Neither
recorded times nor the single structural pairs may replace ten-pair gates.

## What is bound

The full-64 Arm64 decoder retains concrete object addresses, sizes, mutable
flags, code words, closure/capture slots, byte objects and inline code pools.
It checks object lengths, unique addresses, exact total-word accounting and
root-tuple inventory. Tagged values are not mistaken for pointers. Instruction
words are not scanned as object edges. Adjacent ADRP/LDR64 patterns are decoded
against the actual PC and this code object's inline slots; opcode/register
bits and target values survive immediate masking. Raw operands remain intact.
Other ADRP uses remain unresolved. Patterns can occur in non-address data;
this is not a disassembler or an execution trace.

The format follows Poly/ML 5.9.2 `libpolyml/objsize.cpp` (`ShowWords`, `ShowCode`,
`ShowObject`), `libpolyml/arm64.cpp` (`GetConstSegmentForCode`) and
`mlsource/MLCompiler/CodeTree/Arm64Code/Arm64Assembly.sml` (`copyCode`).
Installed runtime/library fingerprints are bound by the paired manifests;
inspecting those source files is not proof of compiler/runtime build lineage.
Other architectures and 32-in-64 representations are rejected.

Replay rechecks the diagnostic input inventory, Git source bytes, exact private
loader/postlude construction, B/B role/revisions, B/B versus B/C schedules,
output transport, source/proof/runtime admission, traced post-workload extent,
root graph and every comparison. Raw-slot graph correspondence preserves
aliasing, repeated code names and every mismatch. It intentionally does not
solve pool permutation by pretending that equal function names prove identity.

## Limits that prevent closure

- **Post-workload is not measurement-boundary layout.** Compiling the postlude
  and walking objects can allocate, collect or move objects after timing.
- `showSize` traverses split pools' referents but does not print their slots.
  Every omitted pool is explicit; zero reported pointer gaps does not bind
  omitted slots or imply a complete graph.
- Root/capture counts, masked words and matching target names are structural
  observations, not proof of equal live objects, dynamic work or cost.
- Reachability includes mutable runtime/I/O state and retained workload results;
  graph size is neither cumulative allocation nor total live/process memory.
- Available indirect targets are not evidence that a particular call executed.
  No repair is selected from address alignment or graph-size correlation.

## Regression tests

```sh
python3 -B -m unittest discover -s src/simp/tests/performance \
  -p test_runtime_layout.py -v
RUNTIME_LAYOUT_EVIDENCE=UNPACKED_DIRECTORY python3 -B -m unittest discover \
  -s src/simp/tests/performance -p test_runtime_layout.py -v
```

Tests cover actual pool addressing (including negative page displacement),
register/slot guards, aliasing, zero-length objects, unresolved pointers,
split-pool omissions, truncation/accounting/marker errors, post-workload source
binding, retained rejected output, authorization, timing rejection, real replay
and coherent source/loader/postlude/proof/inventory/comparison mutations. The
real B/C archive also rejects substitution into the B/B role.

Bundles use the lossless `evidence_bundle.py` transport; its unpack command
produces a new directory for direct inspection.

A separate subsequent diagnostic, [`RUNTIME_POOLS.md`](RUNTIME_POOLS.md),
supplies all actual split-pool slots with a sealed native interposer. It leaves
this v1 tool unchanged and still does not establish measurement-boundary
layout, executed targets, causation or TASK29A completion.
