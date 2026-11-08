# Design and source review: cumulative allocator words

## Status and scope

This is an experimental patch derived from the local Isabelle2025-2
`polyml-5.9.2-2/src` distribution named in `SOURCE_SHA256.json`. The audit
covers the allocator, ARM64 trap/entry mechanisms, native allocation
emitters, interpreter allocator, code allocator, relevant GC/image paths,
native pointer conventions and ordinary FFI paths. The driver runs its
brackets across several Holmake/testutils launcher processes (controls, ML
workers, hybrid bytecode, native failures and lower-level path launchers).
This is not independent maintainer approval or executed proof of
completeness. Static analysis and runtime receipts are kept distinct. It does
not replace the paired allocation matrix (`../ALLOCATION_COUNTER.md`) or
lifetime and peak-memory accounting.

The supported and measured target is the native Linux/aarch64 runtime with
64-bit PolyWords, including the hybrid bytecode interpreter inside it.
**compact32 (32-bit PolyWords in the 64-bit process) and callbacks from
threads not created by the runtime are out of scope**, not pending work: the
driver refuses a compact32 configuration (`path_schema.reject_compact32`),
the C shim loaded into every measured process may import only an exact
allowlist of symbols (`private_runtime.SHIM_IMPORTS`; thread and process
creation are not on it), each path launcher records the process's OS thread
inventory before and after its measurements, and the runtime counts entries
of a thread it did not create (see the path diagnostics). Remarks below about
compact32 describe source reading only; nothing executes them. Other native
targets, interpreter-only configurations, arbitrary handwritten machine-code
heap allocators, signal-handler queries, and fork-without-exec are not
supported. Compile-time guards reject the other configured runtime backends.

## Precisely what is counted

The metric is **cumulative successful mutator managed storage reservations**,
in PolyWords. A reservation commits when the allocator has obtained its object
space and records the success, before handing that reservation back to its
caller. This is allocator work, not final object graph size or object count.
Native allocations can reserve storage for several objects together.

For each successful reservation count its header(s), payload, and per-request
alignment actually consumed. One PolyWord is the snapshot's word-byte field
(4 or 8), not necessarily a C machine word. A byte object consumes its rounded
word payload, not merely the useful byte length. Allocated objects subsequently
shrunk (notably bignum canonicalization), immediately abandoned, overwritten,
made unreachable, or collected remain counted at their original reserved size.

Four mutually exclusive **allocator-path** categories are maintained:

- **native:** final `Arm64TaskData::SetMemRegisters` reservation; count
  `allocWords`.
- **RTS:** successful `alloc` in `run_time.cpp`; count `data_words + 1`,
  rounded even in compact32.
- **interpreter:** successful `ByteCodeInterpreter::allocateMemory`, fast or
  slow; count requested payload + header, rounded even in compact32.
- **code:** successful `MemMgr::AllocCodeSpace` object reservation; count
  `next - pt`, including actual code alignment.

The total is the sum of these categories until any relevant overflow. Category
means allocator path, not semantic ownership: a bignum requested by interpreted
ML but allocated by the RTS belongs to RTS. A compiler's staging bytevector is
counted in the heap; the subsequent executable/code-space copy is a separate
code allocation, counted too. Heap constant vectors are heap reservations;
code payload includes whatever instruction/constants bytes the allocator puts
in that code object. Reporting heap and code separately prevents the copy from
being hidden or mislabeled as double counting.

Not counted:

- Failed requests or failed GC/retry attempts; allocations that succeed while
  constructing an exception are counted normally, independently of the failed
  original request.
- Zero-word segment acquisition, unused segment capacity, abandoned segment
  tails, arena/page rounding, free-area fillers, initial alignment at arena
  creation, or shadow executable mappings. These are capacity/housekeeping,
  not successful object reservations.
- GC evacuation/compaction/sharing copies, marking metadata, stack growth,
  C/C++ allocation, GMP's C memory, FFI malloc, OS mappings, RSS/HWM, or peaks.
- Initial imported image objects or saved-state import/export relocation
  copies. This is not an image-loader traffic counter. Ordinary allocator
  calls made during loading/export are still counted in their respective
  category. Keep image loading outside measured operations.

Counters start at zero when this runtime DSO/process instance is initialized;
there is no reset, enabling period, GC reset, thread-exit reset, or heap-state
persistence. Imported images do not restore a prior process's counters.
Startup/compilation costs are separated using snapshots, not guessed away.
This definition does not measure all host allocations or a live-heap total.

## Why the hooks are here, not in the profiler or arena allocator

All source line references below refer to the **pristine** pinned files.

### Native aarch64

`mlsource/MLCompiler/CodeTree/Arm64Code/Arm64PreAssembly.ML:807-877`
emits fixed/variable allocation checks. Both subtract the requested bytes into
a separate destination register, compare to X25, and update X27 only after the
trap continuation. Variable compact32 allocation includes the header and rounds
the resulting pointer down to an 8-byte boundary. Fixed allocation sizes arrive
from the code generator; the trap observes the actual reserved distance,
including grouping/alignment, instead of reconstructing object sizes.

`Arm64Assembly.sml:153-154,181-183` identifies the assembly-interface offsets,
X25 as the heap limit, and X27 as the allocation pointer. The full compiler
search for `X_MLHeapAllocPtr` and `X27` found the two allocation emitters plus
entry/FFI save/restore paths, not another heap bump allocator. Boxing helpers
in `Arm64PreAssembly.ML:1064-1098` use the same allocation operations.

`libpolyml/arm64assembly.S:86-88,126-150` saves/reloads the allocation register
and limit on entry/traps. `arm64.cpp:613-640` decodes the allocation
destination register from the continuation and computes `allocWords =
allocPointer - destination + 1`. The `+1` corrects the saved register's
object-pointer/header-pointer convention. This is a **request**: counting at
`HandleTrap`, or beside `addProfileCount`, would charge failed allocations and
was rejected.

`arm64.cpp:787-839` performs the reservation. If there is insufficient room it
calls `FindAllocationSpace(..., true)`, then undoes that temporary decrement
before making the final decrement. Failure clears `allocWords`, preserves the
exception path, and skips that final allocation. The hook is at the final
`allocPointer -= allocWords`, before clearing the request. Thus fast trap
recovery, segment replacement, and successful post-GC retry count once; the
intermediate reserve/undo is not counted. Zero-word initialization is skipped.

Every `SetMemRegisters` now sets the **assembly** lower bound equal to its
allocation pointer unconditionally. The next positive native decrement must
trap, irrespective of `profileMode`. The real `TaskData::allocLimit` is
unchanged so C allocators still use the real segment. Native entry, trap
continuation, and normal RTS return use this setup. FFI save/restore and
callbacks load the same assembly-interface limit
(`Arm64ForeignCall.sml:75-86,415-460,680-714`). The patch does not rewrite
generated ML code or require enabling profiling.

The existing native allocation profiler may still record request attribution
when explicitly enabled, but that neither updates nor supplies this counter.
The lossy unknown-PC bucket, profile tables, display units, and profiler thread
behavior cannot drop these success-hook increments. Profile mode changes cannot
disable forced traps. Prefer profiling disabled for measurement controls.

### RTS heap

`libpolyml/run_time.cpp:71-100` is the common `alloc` implementation. Its
`data_words` limit check and null/IOException failure branch precede the new
hook, which runs after length/data initialization and before return.
`alloc_and_save` delegates to it; string, real, bignum, exception,
thread-object, and other RTS object constructors reach it. Bignum shortening in
`arb.cpp:345-394` does not refund an earlier allocation.

`processes.cpp:947-1060` rounds heap reservations even in compact32, reuses a
segment, obtains a separate large-object area when allowed, or refills/retries
through GC. The caller hook covers all its successful RTS branches without
charging the entire segment. The helper rounds the original word request to
match this allocator (the ordinary header + MAX_OBJECT_SIZE range cannot
approach uint64 overflow).

### Hybrid bytecode interpreter

`libpolyml/bytecode.cpp:171-193` is the common object allocator, used by all
the bytecode allocation/boxing sites found in the file. Its fast path already
rounds compact32 words before decrementing; count those words directly. Its
slow path saves interpreter roots, calls `FindAllocationSpace(..., true)`,
restores state, and checks for null; only success counts, with the same
rounding as the RTS.
Do not count in both `allocateMemory` and `FindAllocationSpace`.

The two success hooks now call `RecordManagedInterpreterAllocation` with an
explicit fast/slow selector. Under one lock it updates the original total and
interpreter words AND a separate diagnostic success-count/word pair. It
replaces the previous hook, not adding another allocation increment. Diagnostic
count/word saturation has four independent sticky bits; its separate snapshot
ABI leaves the original eight-word ABI unchanged. Sequential snapshots are not
atomic together; only a quiescent single-controller process reconciles them.
Both exported snapshot symbols must resolve into the same DSO instance.

**Branch distinction:** bytecode.cpp:175 requires one MORE available word than
processes.cpp:958's within-segment test. Consequently a bytecode slow success
can still be satisfied within the current segment. A large-array request alone
also does not prove which bytecode branch ran. The interpreter fast/slow
diagnostics therefore observe actual bytecode branches, and say nothing about
the lower level: refill, large-object area and success-after-GC are observed
only by the separate path diagnostics described next.

### Lower-level path diagnostics (third ABI)

`PolyManagedAllocPathSnapshotV1(void *, size_t)` writes 256 bytes (32
uint64 words: version, bytes per word, an independent sticky overflow mask
with one bit per counter, 28 counters, one reserved zero word). It leaves the
original eight-word and interpreter-branch ABIs, their counters and their
saturation bits untouched; the counters are updated under the same mutex but
never feed back into the original totals. It records, per caller (native
`SetMemRegisters`, RTS `alloc`, bytecode `allocateMemory`), the outcome of each
non-zero-word `Processes::FindAllocationSpace` call: success within the
segment, in a separate large-object area, or after obtaining a new segment
(refill), each split by whether a garbage collection happened first for that
call; failed reservations per caller; `QuickGC` results inside it; and the
words of successful calls. `MemMgr::AllocCodeSpace` returning 0 has its own
counter. The caller is a thread-local set immediately before each of the three
call sites; a non-zero-word call with no caller aborts rather than guessing
(an abort that cannot occur in the built runtime, since every call site tags,
so `arithmetic_test.cpp` executes it in forked children that must die by
SIGABRT, beside positive controls that must not). Native calls include
reservations that `SetMemRegisters` later undoes, so these are lower-level
events, not counted allocations.

Three details of the counters limit what they can show.

- The native (`arm64.cpp`) and bytecode (`bytecode.cpp`) callers pass
  `alwaysInSeg`, so `FindAllocationSpace` never takes its large-object-area
  branch for them. Those cells are asserted zero; only RTS requests exercise
  that branch.
- The after-GC flag is set when this call's `QuickGC` returned true, or when
  the call waited for another thread's pending GC request. The GC that made
  room may therefore be another thread's.
- Counter 27 counts entries into `PolyArm64GetThreadData` that find no task
  data for the calling thread: the one place the native backend creates task
  data for a thread the runtime did not create (`check_patch.py` asserts it is
  the only such site). It must be zero at every endpoint of every launcher,
  and the matrix fixture reads it after its last bracket. It detects such an
  entry in the executed region; it does not make that path correct, and it
  is no substitute for the OS thread inventory, which sees only threads that
  exist when it is read.

The path controls assert structural identities, never GC schedules (which
legitimately vary): RTS path words equal raw RTS words; interpreter path
success events equal the branch slow count and its words equal the branch slow
words; the RTS success events of a loop of known RTS operations equal the
number of operations (each retry success counted exactly once); native and
interpreter loops keep their exact raw slopes while the refill and
success-after-GC counters are non-zero (a retry does not double-count); and a
failed request has exactly one failure counter, no success counters and the
same raw vector as the control with no allocation. After a native failure
the thread's next small native allocation may need one segment refill, which
is charged like any other native reservation; the schema admits exactly that
one refill and its words, nothing else.

`libpolyml/interpreter.cpp` is the separate machine-dependent interpreter-only
backend, not selected in the supported build. The shared `bytecode.cpp`
allocator is still required because the native backend can execute interpreted
code, including bootstrap phases. `CODEISNOTEXECUTABLE` in `Makefile.am`
selects the interpreter-only configuration; the counter rejects that build
rather than advertising unreviewed native coverage.

### Code-space allocator

`libpolyml/poly_specific.cpp:180-225` copies compiler staging bytevectors into
`gMem.AllocCodeSpace(requiredSize)`, retrying on GC. Counting at entry would
charge failures. Counting only heap storage would omit code reservations.

`memmgr.cpp:820-895` searches the free list, optionally creates an area, and
claims the object under `codeSpaceLock`. The hook follows the successful code
length-word write. `next` begins at `pt + requiredSize + 1`; in compact32 it
advances by another word exactly when the alignment branch actually consumes
one. `next - pt` therefore includes the header and actual padding but excludes
the remaining free-area filler. If no spare word exists, no imaginary padding
is charged. Merely creating a code arena, a failed search, and the GC retry do
not count. Locking a mutable code object later is not another allocation.

### Lower-level searches and excluded copies

The complete C/C++ source search found `FindAllocationSpace` callers only in
`run_time.cpp`, `bytecode.cpp`, and the x86/ARM64 native trap recovery paths.
The x86 backend is outside scope and is rejected by the build guard.
`MemMgr::AllocHeapSpace` is used by segment/large-object allocation and the
`CheckForAllocation` GC capacity probe (`memmgr.cpp:665-759,937-940`). None of
these lower-level calls is a safe object-event hook. `AllocCodeSpace` has one
mutator caller in `poly_specific.cpp`.

GC copying paths (`quick_gc.cpp`, `gc_copy_phase.cpp`, `gc_update_phase.cpp`)
and export/import paths (`pexport.cpp`, `savestate.cpp`) manipulate memory
spaces/header words directly for relocation, not via these mutator success
hooks. Header rewriting in sharing/marking is not allocation. The patch leaves
those paths untouched and does not count bytes copied by GC as new work.

## Concurrency, snapshots, overflow, and failure

A statically initialized pthread mutex protects five uint64 counters (total and
four categories) and their sticky overflow mask. This avoids constructor-order
issues, per-thread list enumeration, dead-thread loss, torn 64-bit reads, and
C++ atomic-library/toolchain assumptions. It serializes **all** increments and
snapshots. Each update changes total/category/mask under one lock; each
snapshot copies the complete state under that lock, then copies its local
C-stack record to the caller's C buffer after unlocking. The buffer may be
unaligned.

There are no GC, scheduler, profile, ML allocator, logging, or callback calls
inside the critical section. Code allocation takes `codeSpaceLock` then the
counter lock; no counter-lock path acquires any runtime lock, so no inverse
lock order is introduced. Mutex operation failure aborts instead of silently
returning a plausible but corrupt measurement. The normal snapshot path
performs only locking, scalar arithmetic, stack writes and memcpy, not managed
allocation. This is not async-signal-safe. Fork can inherit a locked mutex and
copied counts: fork-without-exec, DSO unload/reload, and mixing multiple
runtime instances are outside this ABI's process-lifetime contract.

A successful allocator call has updated the counter before returning its
reservation. Native code updates before resuming its initializer. The counter
update is the accounting linearization point. A concurrent snapshot can be
before or after an in-flight reservation's hook; it does not stop all mutators
or promise that every thread has completed initialization. For an operation
including workers, join/quiesce them before the end snapshot. Thread
termination never subtracts prior increments. Other threads' real allocations
remain in the global metric; thread safety is not per-operation attribution.

Overflow uses `increment > UINT64_MAX - current` before addition. On overflow
that component saturates and its mask bit is permanently set. Total has its own
bit: it can overflow before any individual category. Exact equality to the
maximum is representable; the next positive increment sets overflow. Neither
thread/GC activity nor snapshots clear the flag. Reject measurements with any
nonzero overflow mask in either endpoint; never subtract saturated counters as
if they were exact. Subtract endpoints in a wide unsigned host type, check
monotonicity, and multiply words by word bytes in arbitrary precision or with a
separate checked multiplication. Word-counter overflow checking does not make
a host's word-to-byte multiplication safe automatically.

The API checks null output and the supplied byte length; it cannot validate an
arbitrary C pointer's mapping/lifetime. The caller owns 64 writable C bytes and
must not concurrently read/reuse/free the same output buffer during the call.
Copies to separate caller-owned buffers are independent. Metadata is uint64,
host-endian, not an ML tuple, PolyWord array, network packet, or serialized
heap. The versioned C symbol is exported with default ELF visibility and needs
no Poly/ML `entrypts` registration: use the supported foreign C ABI, not
`RunCall` RTS conventions or closure representation casts. Actual symbol
reachability in the built/linked runtime remains a required executed check.

## What the controls establish, and what they do not

All numbers below are produced by `run_controls.py` and checked by the strict
schemas; the receipt is the only evidence. Nothing here is a claim about code
that no launcher executes.

Original controls (`selftest.sml`, `control_schema.py`, 34 brackets):
known-size native word/byte arrays, escaping ref lists, RTS bignum
multiplication, retained-data GC, compiler code allocation and no-op FFI
repeats with exact slopes; the driver additionally checks the actual process
mappings, the snapshot-symbol binding, the direct C ABI and synthetic
overflow/concurrency arithmetic (`arithmetic_test.cpp`, never allocated HOL
words).

Worker controls (`worker_selftest.sml`, 22 brackets): four precreated ML
workers with exact aggregate escaping-ref slopes, no-op/retirement/retained-GC
deltas of four native words, and actual retirement (`isActive=false`).

Hybrid bytecode controls (`interpreter_selftest.sml`, 47 brackets): a freshly
source-bootstrapped bytecode compiler and basis (RootInterpreted.ML,
BuildAll.sml recipe); typed `CompilerBody.compiler` entries compiled before
measurement and run inside native FFI brackets. Native result packaging costs
31 words and stays visible. Exact interpreter words are 5*n for retained ref
lists and n+1 for arrays; repeated full GC does not recount retained objects;
fast and slow bytecode successes sum to the original interpreter category.

Native failure controls (`failure_selftest.sml`, 35 brackets): `--maxheap`
alone is soft (memmgr.cpp lets a large object exceed it), so a one-shot
verified `RLIMIT_AS = current virtual bytes + 64 MiB` is set after every
closure exists. 128/192 MiB native requests then fail with the actual RTS
exhaustion line, the Interrupt is caught, attributes are restored, the rooted
sentinel is unchanged, each failed bracket equals the prebuilt manual
interrupt's raw vector (the requested object is not counted), and exact
successful-array slopes recover.

Path controls (this section's subject; `path_selftest.sml`,
`interpreter_path_selftest.sml` with `interpreter_path_body.sml` and
`interpreter_path_host.sml`, `failure_path_selftest.sml`, `PathThreads.sml`;
schema
`../path_schema.py`; unit tests `../test_allocator_paths.py` and
`../test_allocator_path_guards.py`, which use only in-test synthetic
fixtures):

- `path-controls.exe` (22 brackets): loops of native arrays, RTS big-integer
  shifts and 8 MiB RTS shifts, two rounds each, with no-op warmups. Exact raw
  slopes (native k*(s+1) words, RTS k*(limbs+2)) while the path counters show
  the native and RTS refill branches, success-after-GC, and the large-object
  area (every 8 MiB shift is exactly one large-object reservation). Native
  FAS-level counts are not per-operation (native code allocates inline), so the
  native exactness is the raw slope, the branch presence is the path counters.
- `interpreter-path-controls.exe` (33 brackets): the same for the bytecode
  interpreter (retained arrays of 0 to 2M words), with the path counters equal
  to the branch slow count/words; then, under the verified RLIMIT_AS, two
  16M/24M-word interpreted array requests, two rounds, that fail with the
  actual RTS exhaustion line. An exception raised by the bytecode interpreter
  cannot propagate into the native frames above it (a pre-existing hybrid-mode
  limit noted in bytecode.cpp), so the Interrupt is caught inside interpreted
  code by a wrapper whose exact cost is measured by its own no-allocation
  bracket; each failed request must equal that wrapper's raw vector and
  branch vector and have exactly one interpreter FAS failure and one failed
  QuickGC. Recovery brackets equal the wrapper plus exactly n+1 words.
- `failure-path-controls.exe` (40 brackets, `-H 32 --gcthreads=1`): three
  failing kinds, each twice, followed by exact recovery.
  - RTS: `IntInf.<<` of 2^30 and 1.5*2^30 bits (128/192 MiB of limbs) fails
    with the RTS exhaustion line, exactly one RTS FAS failure, a failed
    QuickGC, no success counters and the manual-interrupt raw vector. Each
    is followed by exact recovery shifts (3 and 130 RTS words).
  - Native: `Array.array (16777216, _)` (128 MiB) fails likewise with exactly
    one native FAS failure, then an exact 1000-element recovery. This
    executes counter 18 of the path ABI.
  - Code space: on AArch64 the code area is a reserved 2 GiB region, so
    RLIMIT_AS cannot fail it. Instead `PolyCopyByteVecToClosure` receives an
    *uncleared* (never touched) byte vector of 2.5 GiB allocated before the
    limit, one size because any request beyond the region fails the same way.
    `MemMgr::AllocCodeSpace` returns 0 because the request exceeds the
    region, not because of the OS limit, and the dedicated path counter is
    exactly one with every FAS failure counter and both QuickGC counters
    zero. The `Fail "Insufficient memory"` that ML then sees additionally
    depends on the following `QuickGC` failing under RLIMIT_AS; were it to
    succeed the runtime would retry, possibly without end, and only the
    process-group timeout would stop it. What is proved: one hooked failed
    code-space request per failed attempt, and no charge for it. It is not
    shown that a code request succeeds after a GC.
    The vector is never copied and no code object is installed; do not pass
    such a vector to a successful copy (a zero-filled code object crashes
    the next full GC). The no-allocation control raises an exception packet
    through the same runtime call with a word object where a byte vector is
    required (`Fail "Not byte data area"`), measured before the limit and
    under it. Every failed code request must have exactly that control's raw
    vector, which has no code words, so the requested 335 million words are
    not charged. Recovery is a real compiler run whose raw vector must equal
    the pre-failure vector, repeated after every failure.
  - Everything the fake closure and vectors need is created before any
    bracket, including the runtime call's entry point (its first use
    allocates code), so no bracket contains a successful code allocation.
    The fake closure and the word-object vector are made with
    `RunCall.allocateWordMemory`/`allocateByteMemory` and typed as a closure
    and byte vector, as the compiler's own `CodeArray.ML` does. These casts
    are control-only, confined to this isolated failure process, and the
    objects only reach the copy call, which fails before using them.

Each path launcher also records the OS thread inventory before and after
(count and sorted names, which must be identical). The sealed shims'
undefined imports are checked against an exact allowlist, so they import no
thread or process creation symbol.

Not established: compact32 and callbacks from foreign-created threads (out of
scope, see above; the latter follow a separate initialization path,
`processes.cpp:1166-1232`, `arm64.cpp:1053-1072`, with a pre-existing null
`proc` dereference that this experiment deliberately does not repair; the
foreign-thread counter only reports an entry); arbitrary prebuilt ML images
(they must use the reviewed native allocation convention; this driver builds
its own compiler and HOL from the sealed source); a general claim that every
allocation path was executed; and any timing. Forcing every native allocation
through a trap and the lock change performance and scheduling: this is an
allocation experiment, not timing evidence interchangeable with an
uninstrumented runtime.

The C snapshot functions perform no managed allocation. Generic ML FFI
construction, argument packing, result conversion and printing may allocate:
construct wrappers and C buffers before the bracket, decode after it. A start
call's return glue and an end call's argument glue can fall inside the
interval; the steady native no-op bracket measures four native words, its first
warmup eight. Never subtract these from arbitrary workloads.

## Validation checklist for the TASK29B matrix

1. Verify pristine seals; apply only to an authorized separate source tree;
   verify patched seals; seal configuration (compact32 refused), tools,
   linker commands, libraries, runtime binary and actual process maps.
   Run the controls from a clean committed checkout that equals the
   candidate outside the performance area; the receipt records it.
2. Check the exported snapshot symbols come from the same runtime instance
   executing HOL; ABI/version, word bytes, layout, null/short buffer.
3. Run every launcher above; admit only a receipt whose exits are zero, whose
   timeouts are finite and unexpired, and whose schemas pass.
4. Only then run every TASK29B case and size, baseline-baseline controls and
   at least ten fresh paired AB/BA observations on the same sealed runtime.
   Preserve raw words and bytes, code/heap splits, flags, endpoints, adjacent
   slopes and zero-size constants. Do not mix instrumented and uninstrumented
   evidence.

The acceptance gap is not repaired by profiler sums, live-graph words, RSS,
synthetic counter increments, or a successfully replayed source patch.
