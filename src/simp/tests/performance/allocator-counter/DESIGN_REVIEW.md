# Design and source review: cumulative allocator words

## Status and scope

This is an experimental patch derived from the local Isabelle2025-2
`polyml-5.9.2-2/src` distribution named in `SOURCE_SHA256.json`. It has been
reviewed by inspection of the allocator, ARM64 trap/entry mechanisms, native
allocation emitters, interpreter allocator, code allocator, and relevant
GC/image paths. A second source review checked native pointer conventions and
ordinary FFI paths. Private runtime controls now execute 138 brackets across
four Holmake/testutils launchers (original, ML workers, hybrid bytecode, native
failures). This is not independent maintainer approval or executed proof of
completeness. Static and runtime receipts are kept distinct. Nothing here
closes TASK29B's full coverage or matrix requirements, TASK29's comparison, or
TASK33's lifetime/peak requirements.

The supported target is the native Linux/aarch64 runtime, with either 64-bit
PolyWords or compact32 (32-bit PolyWords in the 64-bit process). The hybrid
bytecode interpreter inside that runtime is included. Other native targets,
interpreter-only configurations, arbitrary handwritten machine-code heap
allocators, signal-handler queries, and fork-without-exec are not supported.
Compile-time guards reject the other configured runtime backends.

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
and limit on entry/traps. `arm64.cpp:613-640` decodes the allocation destination
register from the continuation and computes
`allocWords = allocPointer - destination + 1`. The `+1` corrects the saved
register's object-pointer/header-pointer convention. This is a **request**:
counting at `HandleTrap`, or beside `addProfileCount`, would charge failed
allocations and was rejected.

`arm64.cpp:787-839` performs the reservation. If there is insufficient room it
calls `FindAllocationSpace(..., true)`, then undoes that temporary decrement
before making the final decrement. Failure clears `allocWords`, preserves the
exception path, and skips that final allocation. The hook is at the final
`allocPointer -= allocWords`, before clearing the request. Thus fast trap
recovery, segment replacement, and successful post-GC retry count once; the
intermediate reserve/undo is not counted. Zero-word initialization is skipped.

Every `SetMemRegisters` now sets the **assembly** lower bound equal to its
allocation pointer unconditionally. The next positive native decrement must
trap, irrespective of `profileMode`. The real `TaskData::allocLimit` is unchanged
so C allocators still use the real segment. Native entry, trap continuation,
and normal RTS return use this setup. FFI save/restore and callbacks load the
same assembly-interface limit (`Arm64ForeignCall.sml:75-86,415-460,680-714`).
The patch does not rewrite generated ML code or require enabling profiling.

The existing native allocation profiler may still record request attribution
when explicitly enabled, but that neither updates nor supplies this counter.
The lossy unknown-PC bucket, profile tables, display units, and profiler thread
behavior cannot drop these success-hook increments. Profile mode changes cannot
disable forced traps. Prefer profiling disabled for measurement controls.

### RTS heap

`libpolyml/run_time.cpp:71-100` is the common `alloc` implementation. Its
`data_words` limit check and null/IOException failure branch precede the new
hook, which runs after length/data initialization and before return.
`alloc_and_save` delegates to it; string, real, bignum, exception, thread-object,
and other RTS object constructors reach it. Bignum shortening in
`arb.cpp:345-394` does not refund an earlier allocation.

`processes.cpp:947-1060` rounds heap reservations even in compact32, reuses a
segment, obtains a separate large-object area when allowed, or refills/retries
through GC. The caller hook covers all its successful RTS branches without
charging the entire segment. The helper rounds the original word request to
match this allocator (the ordinary header + MAX_OBJECT_SIZE range cannot
approach uint64 overflow).

### Hybrid bytecode interpreter

`libpolyml/bytecode.cpp:171-193` is the common object allocator, used by all the
bytecode allocation/boxing sites found in the file. Its fast path already rounds
compact32 words before decrementing; count those words directly. Its slow path
saves interpreter roots, calls `FindAllocationSpace(..., true)`, restores state,
and checks for null; only success counts, with the same rounding as the RTS.
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
also does not prove which bytecode branch ran. New diagnostics observe actual
success branches, not request-size guesses, and do NOT claim refill/GC-retry
coverage of the lower-level allocator.

`libpolyml/interpreter.cpp` is the separate machine-dependent interpreter-only
backend, not selected in the supported build. The shared `bytecode.cpp` allocator
is still required because the native backend can execute interpreted code,
including bootstrap phases. `CODEISNOTEXECUTABLE` in `Makefile.am` selects the
interpreter-only configuration; the counter rejects that build rather than
advertising unreviewed native coverage.

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
snapshots. Each update changes total/category/mask under one lock; each snapshot
copies the complete state under that lock, then copies its local C-stack record
to the caller's C buffer after unlocking. The buffer may be unaligned.

There are no GC, scheduler, profile, ML allocator, logging, or callback calls
inside the critical section. Code allocation takes `codeSpaceLock` then the
counter lock; no counter-lock path acquires any runtime lock, so no inverse
lock order is introduced. Mutex operation failure aborts instead of silently
returning a plausible but corrupt measurement. The normal snapshot path performs
only locking, scalar arithmetic, stack writes and memcpy, not managed allocation.
This is not async-signal-safe. Fork can inherit a locked mutex and copied counts:
fork-without-exec, DSO unload/reload, and mixing multiple runtime instances are
outside this ABI's process-lifetime contract.

A successful allocator call has updated the counter before returning its
reservation. Native code updates before resuming its initializer. The counter
update is the accounting linearization point. A concurrent snapshot can be
before or after an in-flight reservation's hook; it does not stop all mutators
or promise that every thread has completed initialization. For an operation
including workers, join/quiesce them before the end snapshot. Thread termination
never subtracts prior increments. Other threads' real allocations remain in the
global metric; thread safety is not per-operation attribution.

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
host-endian, not an ML tuple, PolyWord array, network packet, or serialized heap.
The versioned C symbol is exported with default ELF visibility and needs no
Poly/ML `entrypts` registration: use the supported foreign C ABI, not `RunCall`
RTS conventions or closure representation casts. Actual symbol reachability in
the built/linked runtime remains a required executed check.

## Outstanding validation and interpretation limits

No known unhooked **ordinary mutator allocation path in the supported source
configuration** was found in this inspection. That is a source-review finding,
not a runtime completeness claim. The first development execution built the private DSO, linked it to HOL and
passed 34 brackets: known-size native word/byte arrays, escaping ref lists,
RTS bignum multiplication, retained-data GC, compiler code allocation and
no-op FFI repeats. Native array slopes include the million-word case exactly.
The hardened driver additionally checks the actual process's mappings and
snapshot-symbol binding, the direct C ABI, and synthetic overflow/concurrency
arithmetic. Consult the corresponding receipt for executed outcomes.

The extended receipt in `../evidence/task29/managed-coverage/` adds:

- Four precreated ML workers, two rounds at 0/256/512 escaping refs each:
  native totals 4/5124/10244 words. Mutex gates exclude worker allocation
  outside the designated rounds. No-op, retirement, and retained-data GC
  deltas are each four words. `isActive=false` establishes actual retirement;
  acknowledgement alone is not used. Errors are published, not discarded by
  Thread.fork. These controls do not validate foreign-thread attachment.
- A freshly source-bootstrapped bytecode compiler and basis, following
  RootInterpreted.ML/BuildAll.sml. Typed `CompilerBody.compiler` entries are
  compiled before measurement, then invoked inside native FFI brackets.
  No unsafe closure cast or interpreted-to-native FFI call is used. Native
  declaration-result packaging costs 31 words and remains visible. Exact
  additional interpreter words are 5*n for retained ref/cons lists and n for
  arrays, including their separate one-word header. Repeated full GC does not
  recount retained interpreted objects. That historical run has no branch
  diagnostics and cannot prove coverage of both interpreter branches.
- Actual native allocation failures in a separate process. `--maxheap=96`
  alone is NOT a hard limit: memmgr.cpp explicitly allows a large object to
  exceed the target. The final fixture additionally sets/rechecks a one-shot
  RLIMIT_AS at current virtual bytes + 64MiB, outside the bracket, never
  increasing an existing soft limit. Dynamic 128/192MiB requests then fail
  twice each, with actual RTS exhaustion output and Thread.Interrupt caught
  only after action entry. Attributes are restored and a rooted sentinel is
  unchanged. Each failed bracket equals the prebuilt manual-interrupt
  control's four native words; the requested object is not counted. Exact
  successful-array slopes recover after every failure. This does not validate
  RTS, interpreter or code-space failure branches.

Development receipts retain static-loading/bootstrap errors, a crashing
interpreted generic-FFI attempt, and the rejected maxheap-only oversized
success. They are not admitted allocation controls. Using native-bracketed
precompiled bytecode entries avoids the unsupported hybrid-FFI path without
changing the runtime or production HOL.

The separate `../evidence/task29/managed-branches/` receipt adds 16 brackets
without replacing those 31 small bytecode brackets. Both retained-ref and array
series at 65536/131072 elements execute BOTH successful bytecode branches.
Every diagnostic endpoint reconciles with the original interpreter category;
all original raw vectors repeat exactly, despite different branch schedules.
Ref storage is exactly 5*n interpreter words, arrays n+1; 31 native entry-result
words remain counted. No-op and empty/live GC controls have zero interpreter
increments. Large retained results are consumed before and after GC. Synthetic
C tests separately cover diagnostic coherence/concurrency, all saturation bits,
independence from original overflow, and both snapshots' buffer/no-allocation
contracts. Those synthetic increments are not allocated HOL words.

Coverage is still incomplete: RTS/interpreter/code failures, foreign-thread
attachment, lower-level refill/GC-retry and remaining slow paths, compact32
and prebuilt compiler/image lineage are not established.
These remain explicit prerequisite checks before full matrix acceptance,
not claims inferred from successful narrower controls.

In particular:

- Standard Poly/ML-created threads enter via `EnterPolyCode`/`SetMemRegisters`.
  Foreign-created-thread callback attachment follows a separate pre-existing
  initialization path (`processes.cpp:1166-1232`,
  `arm64.cpp:1053-1072`). Source review found a pre-existing null `proc`
  dereference via `InitStackFrame(taskData, 0)` and no `SetMemRegisters`
  before callback assembly reloads the heap registers on that path.
  Foreign-created-thread attachment is explicitly unsupported, not merely
  presumed safe because the counter uses a mutex. It needs a separate runtime
  repair and controls if used. No callback initialization fix is smuggled into
  this allocator experiment.
- Arbitrary prebuilt ML images must use the reviewed native allocation-check
  convention. A matching version string alone does not prove that. Seal their
  provenance and check representative allocation disassembly. The supplied
  source manifest does not prove installed binary provenance.
- The C snapshot function performs no managed allocation. Generic ML FFI
  construction, argument packing, result conversion, tuples, pointer boxing,
  reading uint64 into large integers, and printing may allocate. Construct
  wrappers and C buffers before the bracket; decode/format after it. A start
  call's return-glue costs and an end call's argument-glue costs can still fall
  inside the interval. The actual steady no-op FFI bracket measured four
  native words; the first warmup measured eight total words. Both raw results
  are preserved. This is not a universal calibration or zero-overhead wrapper.
  The direct C ABI's no-allocation control is a separate check.
- Forcing every native allocation through a trap changes performance and can
  change scheduling, asynchronous activity and GC behavior. The lock is also
  intentionally expensive. All real mutator allocations caused by the
  instrumented process count. This is an allocation experiment, not timing
  evidence interchangeable with an uninstrumented runtime.

## Validation checklist (only executed receipt checks are established)

1. Verify pristine seals; apply only to an authorized separate source tree;
   verify patched seals. Seal build configuration, compact32 selection,
   bootstrap compiler/images, tool versions, linker commands/options, libc,
   dependency hashes, runtime binary/library hashes and actual process maps.
2. Check the exported `PolyManagedAllocSnapshotV1` symbol comes from the same
   runtime instance executing HOL. Test ABI/version, word bytes, byte layout,
   null/short-buffer rejection, unaligned buffer, and unchanged buffer on error.
3. Test known retained native records/refs, bytevectors/strings of both payload
   parities, boxed real/word values, grouped allocations, variable-size and
   large-object allocations, and both within-segment/refill/GC-retry paths.
   Consume results; prevent optimization from removing temporary allocations.
4. Exercise RTS bignums/strings/reals/exception construction and interpreter
   allocations (both fast and slow). Assert exact physical reservation formulas
   per allocator path, not just positivity or profiler displayed totals.
5. Compile known functions to exercise staging heap plus code space, code-area
   reuse/new-area/retry and compact32 alignment. Separate code and heap deltas;
   observe already allocated mutable code locking does not reserve it again.
6. Force minor/full GC with retained/dead results; verify existing allocations
   are not recounted. Account for any actual ML/RTS allocations of the GC-call
   wrapper rather than requiring its entire bracket to be magically zero.
   Fail allocation in a bounded throwaway process: the failed request must not
   count, but any successful exception allocations must. Check that trap recovery
   did not count the reserve/undo twice.
7. Join multiple allocating ML threads and compare deterministic aggregate
   known-size totals; exercise simultaneous snapshots, worker exit, and GC.
   Check every overflow-free snapshot has total = category sum. Validate
   foreign-created-thread callbacks separately if they are in scope.
8. Exercise saturation boundary arithmetic and total-only overflow in a private
   C/RTS test harness. Such injected arithmetic tests are **not actual allocator
   evidence**. No public injection/reset FFI is included. Check sticky flags and
   host byte-conversion overflow rejection.
9. Test the real preconstructed HOL/ML FFI bracket with no operation, known
   escaping allocations, and GC controls. Keep startup, rule construction,
   complete operation and ordinary application brackets distinct. Both compared
   versions must use the same sealed runtime/options/dependencies.
10. Only after those pass, run every TASK29B case and size, baseline-baseline
    controls, and at least ten fresh paired AB/BA observations. Preserve raw
    words and bytes, code/heap splits, flags, endpoints, adjacent slopes and
    zero-size constants. Do not mix instrumented and uninstrumented evidence.

The acceptance gap is not repaired by profiler sums, live-graph words, RSS,
synthetic counter increments, or a successfully replayed source patch.
