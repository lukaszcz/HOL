# Experimental Poly/ML managed allocation counter

**Experimental runtime, not TASK29B acceptance.** Seven private
Holmake/testutils launcher processes execute 233 brackets: 34 original
native/RTS/code/GC, 22 allocating ML worker/retirement, 47 hybrid bytecode
(31 original plus 16 branch controls), 35 native failure/recovery, and three
lower-level path launchers: 22 native/RTS refill, large-object (RTS only)
and success-after-GC, 33 bytecode (refill and success-after-GC plus real
exhaustion failures), and 40 RTS, native and code-space failures with
recovery (eight of them are failing requests: four RTS, two native, two
code-space).
Steady native no-op brackets cost four words; native-bracketed interpreted
declaration entries cost 31 native words. Neither is zero or subtracted from
workloads. The full paired allocation matrix is a separate requirement.
compact32 and callbacks from foreign-created threads are out of scope (see
below). Nothing replaces the installed runtime or changes production HOL.

## Deliverables

- `managed-allocation.patch.gz`: eight runtime-source patch targets (seven
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
- `private_runtime.py`: source seal, patched-runtime build and process-binding
  checks shared by `run_controls.py` and the TASK29B matrix driver.
- `run_controls.py`: authorized private build/execution driver; removes its
  source/build/fixture copies on success or failure and preserves receipts.
- `selftest.sml`, `bracket.c`, `control_schema.py`: original allocator
  controls, raw C-buffer endpoints, actual symbol/mapping identity and strict
  admission.
- `worker_selftest.sml`: four real ML workers, precreated/parked outside
  allocation brackets, exact aggregate escaping-ref slopes, actual
  `isActive=false` retirement, and retained-data GC. No synthetic increments.
- `interpreter_selftest.sml`, `interpreter_body.sml`, `interpreter_host.sml`:
  bootstrap the sealed bytecode compiler/basis, precompile declaration-entry
  closures, and bracket their execution with native FFI. Compilation and
  declaration installation are outside brackets; fixed native result packaging
  remains counted. No interpreted generic FFI or unsafe bridge/cast is used.
- `interpreter_branch_host.sml`, `../interpreter_branch_schema.py`: additional
  retained large-array/ref controls with separately observed successful fast
  and slow bytecode allocations. Their words sum exactly to the original
  interpreter category, including at cumulative endpoints. Branch schedules
  may vary; total allocations must repeat exactly. No workers execute here.
  Slow-bytecode success is NOT proof of lower-level refill or GC retry; the
  path launchers below observe those directly.
- `failure_selftest.sml`, `failure_limit.c`: separate capped process, real
  OS-address-space exhaustion, prebuilt-interrupt comparison and allocation
  recovery. `--maxheap` alone permits oversized objects, so a one-shot
  verified `RLIMIT_AS=current virtual bytes+64MiB` limit is essential. It
  never increases an existing soft limit. Failed 128/192MiB requests must
  emit actual RTS diagnostics and leave the rooted sentinel unchanged.
  Limitation: the failures rely on the runtime's own exhaustion handling
  under the OS limit. A request that did not fail where expected could retry
  without end, so every launcher runs under a process-group timeout.
- `../{worker,interpreter,failure}_schema.py`: separate strict protocols,
  complete endpoints/raw categories/results, and fault/receipt controls.
- `path_selftest.sml`, `interpreter_path_selftest.sml` (with
  `interpreter_path_body.sml` and `interpreter_path_host.sml`),
  `failure_path_selftest.sml`, `PathThreads.sml`, `../path_schema.py`: the
  three path launchers and their shared OS thread inventory.
  The third snapshot ABI `PolyManagedAllocPathSnapshotV1` (256 bytes: version,
  word bytes, its own overflow mask, 28 counters at words 3..30 and one
  reserved zero word 31; original ABIs untouched) records each non-zero-word
  `Processes::FindAllocationSpace` outcome per caller (native, RTS,
  bytecode): within segment, large-object area or refill, first attempt or
  after a GC, plus failed reservations, `QuickGC` results,
  `MemMgr::AllocCodeSpace` failures, and (counter 27) entries of a thread the
  runtime did not create into `PolyArm64GetThreadData`. A thread-local caller
  tag is set at the three call sites; an untagged event aborts. Executed
  branches are read from these counters, never inferred from request size.
  Schemas require exact structural identities (RTS path words equal raw RTS
  words; one RTS success per operation of a known RTS loop; path interpreter
  events equal the branch slow counters; the large-object cells of the native
  and bytecode callers, which pass `alwaysInSeg`, are zero; counter 27 is
  zero) and branch presence (at least one), not GC schedules. The after-GC
  cells cover a retry after this call's `QuickGC` succeeded or after it
  waited for another thread's pending GC request.
  Failed requests carry exactly one failure counter, no success counters and
  the raw vector of the no-allocation control; recovery is an exact slope or
  an unchanged compiler raw vector. The failing kinds are RTS (`IntInf.<<`),
  native (`Array.array`) and bytecode requests under the one-shot
  `RLIMIT_AS` of `failure_limit.c`, and code-space requests.
  Code-space failure passes `PolyCopyByteVecToClosure` an uncleared byte
  vector larger than the reserved 2 GiB AArch64 code region; one size, since
  any request beyond the region fails alike. `AllocCodeSpace` returns 0
  because of the region, not the OS limit. The `Fail "Insufficient memory"`
  that ML then sees additionally needs the `QuickGC` to fail under
  `RLIMIT_AS`; were it to succeed the runtime would retry, possibly without
  end, so the driver's process-group timeout is the guard. What is proved is
  one failed `AllocCodeSpace` per failed attempt and no charge: the raw
  vector equals that of a control raising an exception packet of the same
  size through the same runtime call (a word object where a byte vector is
  required), which asks for no code space. It does not prove that a code
  request succeeds after a GC. Do not feed such a vector to a successful
  copy. The failure launcher builds the fake closure and word-object vector
  with `RunCall.allocateWordMemory` and `allocateByteMemory` and types them
  as a closure and byte vector: these casts are control-only, confined to
  that isolated process, and only given to the copy call, which fails first.
  The bytecode failure's Interrupt is caught inside interpreted code, because
  hybrid-mode exceptions cannot cross into native frames.
- `../test_allocator_paths.py`: negative-control unit tests of `path_schema`
  on in-test synthetic data only; every rejection names its reason.
- `../test_allocator_path_guards.py`: one test per guard of `path_schema`,
  each corruption built to be caught by that guard alone and pinned to its
  message (record shapes, endpoints, monotonicity, structural identities,
  per-control branch requirements, receipt checks).
- `../test_allocator_counter.py`: the same for the driver's guards (shim
  import allowlist, counter exports, compact32, seal checks before and after
  the temporary tree is deleted, harness identity in a throwaway repository).
- `arithmetic_test.cpp`: separately executed synthetic overflow/concurrency
  tests of the exact implementation, and death tests (a forked child must die
  by SIGABRT) of the abort on an unidentified `FindAllocationSpace` caller,
  an invalid kind and an invalid outcome; not allocated HOL words.

The patch deliberately fails compilation outside native Linux/aarch64 with
64-bit C pointers. The measured configuration is 64-bit PolyWords, including
the bytecode interpreter hosted in that native runtime. compact32 is out of
scope: the driver rejects a compact32 configuration and never measures it. A
separately configured interpreter-only runtime is intentionally rejected, not
partially instrumented. No counter enable/disable switch or reset can silently
lose work.

## Reproduce the static artifacts

From the HOL repository root:

```sh
cd src/simp/tests/performance/allocator-counter
python3 -B prepare_patch.py --check
python3 -B check_patch.py
```

Both tools accept `--source PATH` for an identical pristine source copy. The
preparation tool checks the complete file inventory; run it before configuring
or building that copy. Without `--check` it writes only the patch and patched
hash manifest in **this directory**, never the input source. Neither tool
builds or executes Poly/ML. `-B` avoids creating Python cache directories.

## Execute the runtime controls

```sh
python3 -B src/simp/tests/performance/allocator-counter/run_controls.py \
  --authorize-experimental-runtime --bootstrap-hol --output NEW_RECEIPT.json
```

`--output` is required and exclusive-create: nothing defaults into the
repository, and a receipt is never committed. `--source PATH` names an
identical pristine source copy (default: the pinned local distribution);
`--timeout SECONDS` bounds every command and launcher process;
`--reference REV` (default `simplifier`) is the revision the harness may
differ from only below `src/simp/tests/performance`.

The controls always run from the checkout that contains the script, never
from `$HOLDIR`. That checkout must be clean and committed (apart from the
top-level `.agent-files/` directory, which holds the serial lock). The
receipt records its head, its dirty state (always false) and a digest of its
committed tree outside the performance area, which must equal the
reference's. The driver
then builds a native Poly/ML and HOL from the sealed source at that head
(`--bootstrap-hol` is required: the build is the receipt's lineage, and the
lineage products are re-sealed at the end), copies the sealed runtime source,
replays the patch, builds only its shared runtime, compiles `bracket.so`, and
runs each launcher against the sealed `hol.state0`: counter, worker,
interpreter, failure, and the three path launchers. Each has a finite
process-group timeout, stderr merged into stdout, and its own strict schema.
Both the actual loaded process maps and the snapshot symbol's DSO must
identify the private runtime; no second libpolyml is permitted.
Compiler/linker tools, effective sanitized environments, configuration and
build inputs, linked libraries, generated fixture products, raw
commands/exits and endpoints are retained in the receipt, which is the only
evidence; a completed run is **not** TASK29B matrix acceptance. All source,
build and fixture copies are deleted afterwards, and the seals of inputs
outside the temporary tree are rechecked after that. The driver never writes
to the supplied pristine source, takes the performance/build serial lock, and
must not run alongside benchmarks.

Scope: compact32 (refused by `private_runtime.reject_compact32` and
`path_schema.reject_compact32`) and callbacks from threads not created by the
runtime are out of scope. The measurement shims may import only an exact
allowlist of symbols (`private_runtime.SHIM_IMPORTS`, plus the limit
functions for the failure shim), so they import no thread or process creation
symbol; each path launcher records the OS thread inventory before and after;
the runtime counts entries of a foreign-created thread and the schemas
require that count to be zero. Arbitrary prebuilt ML images are not
validated.

## Reproduce the unit tests

```sh
python3 -B -m unittest discover -s src/simp/tests/performance \
  -p 'test_allocator*.py'
```

These are protocol tests with synthetic data, not runtime evidence.

## Before using the counter for the TASK29B matrix

1. Review `DESIGN_REVIEW.md` and the patch. Work on a separate runtime-source
   copy and verify its pristine seal. Do not patch the installed source path.
2. In that copy only, decompress `managed-allocation.patch.gz` and apply with
   `-p1`; verify the eight result hashes before configuration and build.
   Existing ARM64 source CRLF bytes are intentionally preserved.
3. Configure and build native aarch64 with `--disable-compact32bit`. Both
   `Makefile.am` and distributed `Makefile.in` include the new private
   header; no regeneration is needed for this patch.
4. Seal compiler/linker/bootstrap inputs, options, generated configuration,
   dependencies, binary/shared-library hashes, and the actual loaded runtime.
   Verify the C symbol in the library actually used by HOL. Do not load a
   second libpolyml merely to find the symbol: its counters would be the
   wrong ones.
5. Run `run_controls.py` and read its receipt. The matrix driver accepts only
   a receipt whose runtime seal is its own private runtime and whose harness
   is clean and equal to the candidate outside the performance area.

The original API writes the same eight-uint64 snapshot into preallocated
**C** memory. A second diagnostic ABI exposes fast/slow success counts and
words with independent saturating overflow bits under the same mutex, and the
third path ABI above exposes lower-level events. Each bytecode success updates
both original counters and diagnostics in one critical section; this replaces
its former original hook, never double-counting it. Each snapshot is
coherent, but two sequential ABI calls are not atomic together. The
single-controller fixture reconciles them with no concurrent mutator. All
snapshot symbols must bind to the same runtime DSO instance; direct C buffer
and no-allocation checks cover all three. Synthetic concurrency/overflow
tests are executed separately and are not actual allocated HOL words.

None of these is a Poly/ML RTS-call ABI; never invoke them via unsafe ML
closure casts. Executed controls distinguish the allocation-free direct C
snapshot from the allocating generic ML FFI bracket. Never subtract four
words from arbitrary workloads or assume a warmup-free measurement from these
controls.
