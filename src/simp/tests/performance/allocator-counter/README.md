# Experimental Poly/ML managed allocation counter

**Experimental runtime, not TASK29B acceptance.** A private runtime build and
HOL launcher executed 34 brackets successfully in the development run. Native
known-size slopes, real RTS bignum allocation, code allocation and GC controls
passed. Steady no-op FFI brackets cost four native words, not zero. The full
paired allocation matrix and remaining coverage checks are still unsatisfied.
Nothing replaces the installed runtime or changes production HOL.

## Deliverables

- `managed-allocation.patch.gz`: seven runtime-source patch targets (six
  existing files and one new header), for a **separate copy** of the pinned
  source. Gzip transport preserves upstream CRLF/tab context byte-exactly
  without introducing those foreign-source whitespace bytes into HOL sources.
- `managed_alloc_counter.h`: C snapshot ABI and internal allocator-hook API.
- `counter_impl.inc`: implementation embedded in `run_time.cpp` by the patch;
  not an extra translation unit or generated build dependency.
- `SOURCE_SHA256.json`: all 857 pristine source-file hashes, not a claim that
  every file was read. Its canonical inventory SHA-256 is
  `6e4db7267c688624c92baed3d4968b0680fdf8163f06b77c73c6391304582020`.
- `PATCHED_SHA256.json`: expected bytes of every patched target.
- `prepare_patch.py`: verify the pristine inventory and reproduce the patch.
- `check_patch.py`: strict in-memory patch replay and static coverage checks.
- `DESIGN_REVIEW.md`: semantics, source-path audit, limitations, and handoff.
- `STATIC_REVIEW.json`: initial static-check receipt, **not runtime evidence**.
- `run_controls.py`: authorized private build/execution driver; removes its
  source/build/fixture copies on success or failure and preserves receipts.
- `selftest.sml`, `bracket.c`, `control_schema.py`: real allocator controls,
  raw C-buffer endpoints, actual symbol/mapping identity and strict admission.
- `arithmetic_test.cpp`: separately executed synthetic overflow/concurrency
  tests of the exact implementation; not allocated HOL words.

The patch deliberately fails compilation outside native Linux/aarch64 with
64-bit C pointers. It covers ordinary 64-bit PolyWords and compact32 PolyWords,
including the bytecode interpreter hosted in that native runtime. A separately
configured interpreter-only runtime is intentionally rejected, not partially
instrumented. No counter enable/disable switch or reset can silently lose work.

## Reproduce the static artifacts

From the HOL repository root:

```sh
python3 -B src/simp/tests/performance/allocator-counter/prepare_patch.py --check
python3 -B src/simp/tests/performance/allocator-counter/check_patch.py
```

Both tools accept `--source PATH` for an identical pristine source copy. The
preparation tool checks the complete file inventory; run it before configuring
or building that copy. Without `--check` it writes only the patch and patched
hash manifest in **this directory**, never the input source. Neither tool builds
or executes Poly/ML. `-B` avoids creating Python cache directories.

## Execute the narrow runtime controls

```sh
python3 -B src/simp/tests/performance/allocator-counter/run_controls.py \
  --authorize-experimental-runtime --source PRISTINE_SOURCE \
  --output NEW_RECEIPT.json
```

The driver copies the fully sealed source, replays the patch, builds only its
shared runtime, and runs a Holmake/testutils launcher against the existing
sealed `hol.state0`. Both actual loaded process maps and the snapshot symbol's
DSO must identify that private runtime. No second libpolyml is permitted.
Compiler/linker tools, effective sanitized environments, configuration/build
inputs, linked libraries, generated fixture products, raw commands/exits and
endpoints are retained. This is a local source-instrumentation experiment,
not an independently rebuilt HOL/compiler or fully hermetic toolchain.

On this host use `evidence/task26/root-wrapper.sh` under compatibility to bind
the configured historical HOL root. Its private `/home` hides the pristine
Poly/ML distribution: supply an identical, sealed copy under `/tmp` via
`--source`, then remove that input copy immediately after the run. The driver
never writes to the supplied pristine source. Do not run alongside benchmarks.

Durable results are in `../evidence/task29/managed-counter/`. Read the actual
receipt outcome; a completed control run is **not** TASK29B matrix acceptance.
Native eight-byte-word controls do not validate compact32, foreign-created
thread callbacks, all interpreter/failure paths or every prebuilt image.
The original ordinary-runtime timing failures remain unchanged.

## Remaining validation

1. Review `DESIGN_REVIEW.md` and the patch. Create a separate runtime-source
   copy and verify its pristine seal. Do not patch the installed source path.
2. In that authorized copy only, decompress `managed-allocation.patch.gz`
   and apply with `-p1`; verify the seven result hashes before configuration/
   build. Existing ARM64 source CRLF bytes are intentionally preserved.
3. Configure/build native aarch64 with the intended compact32 setting. Both
   `Makefile.am` and distributed `Makefile.in` include the new private header;
   no regeneration is required just for this patch.
4. Seal compiler/linker/bootstrap inputs, options, generated configuration,
   dependencies, binary/shared-library hashes, and the actual loaded runtime.
   Verify the C symbol in the library actually used by HOL. Do not load a second
   libpolyml merely to find the symbol: its counters would be the wrong ones.
5. Execute the controls and path coverage in the design review before using
   any deltas. Only then undertake the full TASK29B baseline/candidate matrix.

The API writes a coherent eight-uint64 snapshot into preallocated **C** memory.
It is not a Poly/ML RTS-call ABI and must not be invoked via unsafe ML closure
casts. Executed controls distinguish the allocation-free direct C snapshot
from the allocating generic ML FFI bracket. Never subtract four words from
arbitrary workloads or assume a warmup-free measurement from these controls.
