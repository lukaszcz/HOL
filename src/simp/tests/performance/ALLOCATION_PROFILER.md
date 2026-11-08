# TASK29 allocation-profiler negative control

`allocation_profiler_probe.py` demonstrates an information-loss path in the
**actual linked HOL runtime**, not an inferred source-tree version. It is a
negative control for a proposed `ProfileAllocations`-sum counter, **not an
allocation instrument or performance experiment**.

## Reproduce

From a configured checkout, with no concurrent benchmark/build:

```sh
python3 -B src/simp/tests/performance/allocation_profiler_probe.py \
  --authorize-runtime-probe --output NEW_RECEIPT.json
```

The checkout must be bound at its configured path (on hosts where it is
mounted elsewhere, run the command through the host's binding wrapper).
Alternatively, explicitly run `profiler-loss-control` in the performance
`Holmakefile` with a new `PERFORMANCE_CHECK_OUTPUT` directory. This target is
not implicit in `check`: invoking a private runtime ABI requires the exact
reviewed binary. The receipt is written to the output path the caller gives;
nothing is written into the repository.

## What executes

The driver records `ldd bin/hol`, seals every linked library, and requires
Linux/aarch64 and this libpolyml SHA-256 **before compiling/loading the shim**:

```text
8e39afa6fd362322a6e19b16e0055c39a6b3f8aae67d3fb04191feec4961fd7d
```

It builds a temporary C++ shared library, verifies its libpolyml resolution,
then builds and **executes** `allocator-probe/selftest.sml` using Holmake,
`hol.state0`, and testutils. `PolyML.Profiling.profileStream` brackets six
controls. A C shim calls the binary's exported `addSynchronousCount` with a
null (non-code) PC and known synthetic request sizes/event counts. It does
**not** allocate the requested memory. No closure casts, object-layout reads,
production edits, interposition or replacement runtime are used.

| Control | Synthetic words/event | Events | Observed UNKNOWN |
| --- | ---: | ---: | ---: |
| Empty | 0 | 0 | 0 |
| Small | 1 | 1 | 1 |
| Large | 1048576 | 1 | 1 |
| Repeated | 1048576 | 7 | 7 |
| Repeated, then full GC | 1048576 | 7 | 7 |
| Reset | 0 | 0 | 0 |

These are **injected profiler arguments**, not measured allocated words. Both
1 and 1048576 produce the same unknown count. The installed disassembly
independently shows the unknown-PC branch adding literal 1, discarding the
original `incr`. Full GC and extraction cannot recover discarded information.
The displayed entry sum also includes bracket/runtime allocations, so it is
retained only as diagnostic output, never labelled workload allocation.

Thus summing the profiler's displayed entries cannot generally give cumulative
allocated words. This does not establish how frequently real workloads
hit that path, nor validate the other profile-coverage issues. No partial
instrument or guessed correction factor is accepted as a counter.

## Receipt and limitations

The receipt retains the execution, all six outputs, the testutils checks,
compiler version, runtime/tool/fixture seals, installed-symbol disassembly,
command lines and exits. The driver keeps failed command receipts before
rejecting them. Missing, duplicate, reordered, malformed or semantically
different controls fail closed; the Python tests exercise those guards and
the exact-library admission rule on synthetic data. Final linked
library resolutions/bytes and source/heap/tool seals are rechecked. Temporary
sources, executables and DSO are removed on success or failure.

This is local non-hostile-producer provenance, not authentication against
transient malicious tool/runtime changes. The private ABI is reviewed only
for the pinned binary, not all Poly/ML 5.9.2 builds. It adds no ordinary-client
cost and is not run in any acceptance timing process. This test supplies
none of the allocator counter's coverage requirements; see
`ALLOCATION_COUNTER.md`.
