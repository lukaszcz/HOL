/* Experimental Poly/ML 5.9.2-2 allocator counter ABI, version 1.
 * This header is added to libpolyml/ by managed-allocation.patch.
 * No Poly/ML object, thread id, or managed pointer crosses this ABI.
 */
#ifndef POLY_MANAGED_ALLOC_COUNTER_H
#define POLY_MANAGED_ALLOC_COUNTER_H

#include <stddef.h>
#include <stdint.h>

#define POLY_MANAGED_ALLOC_SNAPSHOT_WORDS_V1 8
#define POLY_MANAGED_ALLOC_SNAPSHOT_BYTES_V1 64
#define POLY_MANAGED_INTERPRETER_ALLOC_SNAPSHOT_WORDS_V1 8
#define POLY_MANAGED_INTERPRETER_ALLOC_SNAPSHOT_BYTES_V1 64
#define POLY_MANAGED_PATH_ALLOC_SNAPSHOT_WORDS_V1 32
#define POLY_MANAGED_PATH_ALLOC_SNAPSHOT_BYTES_V1 256

#ifdef __cplusplus
extern "C" {
#endif

/* out must name at least 64 writable C bytes, not managed ML memory.
 * bytes < 64 or out == NULL: return -1, write nothing.
 * Otherwise return 0 and write eight host-endian uint64_t values:
 *   [0] ABI version (1)
 *   [1] bytes per PolyWord (4 or 8)
 *   [2] sticky overflow mask: bit 0 total, 1 native, 2 RTS,
 *       3 interpreter, 4 code
 *   [3] total committed allocation words (all four categories)
 *   [4] native heap words
 *   [5] RTS heap words
 *   [6] interpreter heap words
 *   [7] code-space words
 * Counts saturate at UINT64_MAX; overflow invalidates exact deltas.
 * No reset. Process/DSO lifetime, not a per-thread counter.
 * Coherent under concurrent updates. Not async-signal-safe or fork-safe.
 * The function itself allocates no managed memory; FFI glue might do so.
 */
int PolyManagedAllocSnapshotV1(void *out, size_t bytes);

/* Private interpreter branch diagnostics; NOT a coverage guarantee.
 * Same buffer, lifetime, locking and saturation rules as above, but an
 * independent overflow mask and no change to the original snapshot ABI:
 *   [0] version (1), [1] bytes per PolyWord, [2] sticky overflow mask
 *   [3] fast success count, [4] fast committed words
 *   [5] slow success count, [6] slow committed words, [7] reserved (0)
 * Overflow bits 0..3 correspond to fields 3..6 respectively.
 * Only the two instrumented bytecode success branches contribute here.
 * Each snapshot is coherent; two different snapshot calls are not atomic
 * together. In particular, concurrent updates can separate their views.
 */
int PolyManagedInterpreterAllocSnapshotV1(void *out, size_t bytes);

/* Private lower-level allocation-path diagnostics; NOT a coverage guarantee.
 * Same buffer/lifetime/locking/saturation rules, independent overflow mask,
 * and no change to either snapshot ABI above. 256 writable C bytes:
 *   [0] version (1), [1] bytes per PolyWord, [2] sticky overflow mask
 *   (bit i for counter i below), [3 + i] counter i (0..27), [31] reserved (0)
 * Counters, from Processes::FindAllocationSpace (FAS), whose caller is one of
 * native (n=0), RTS (n=1) or bytecode interpreter (n=2). FAS requests of
 * zero words (pure segment acquisition) are not recorded:
 *   i = 6n + 2o + g (0..17): successful FAS returns for caller n, where
 *       o = 0 within the current segment, 1 a separate large-object area,
 *       2 a newly obtained segment (refill); o = 1 can only happen for
 *       n = 1, since the native and bytecode callers pass alwaysInSeg;
 *       g = 0 on the first attempt,
 *       1 after this call's QuickGC returned true, or after it waited for
 *       another thread's pending GC request (so the GC may be another
 *       thread's, not one this call performed)
 *   18 + n: FAS returned 0 (failed reservation) for caller n
 *   21 / 22: QuickGC inside FAS returned true / false
 *   23: MemMgr::AllocCodeSpace returned 0 (code-space reservation failed)
 *   24 + n: words in the successful FAS returns of caller n (all o, g)
 *   27: PolyArm64GetThreadData found no task data for the calling thread
 *       (a thread not created by the runtime entered it); expected zero
 * Native FAS calls include reservations that SetMemRegisters immediately
 * undoes before its final counted decrement; these are lower-level events,
 * not counted allocations. Two different snapshot calls are not atomic.
 */
int PolyManagedAllocPathSnapshotV1(void *out, size_t bytes);

#ifdef __cplusplus
}

/* Internal RTS API. Caller passes actual committed words, including
 * header and allocation alignment, excluding segment capacity/filler.
 * Do not call this on requests, failed reservations, or GC copies.
 */
enum ManagedAllocKind {
    ManagedAllocNative = 1,
    ManagedAllocRTS = 2,
    ManagedAllocInterpreter = 3,
    ManagedAllocCode = 4
};
void RecordManagedAllocation(ManagedAllocKind kind, uint64_t words);

/* Successful bytecode allocation only: atomically add the original total
 * and interpreter words plus this branch's diagnostic count and words.
 * slow selects the successful FindAllocationSpace path. Zero words is a
 * no-op, just as for RecordManagedAllocation. Never call both for one event.
 */
void RecordManagedInterpreterAllocation(bool slow, uint64_t words);

/* Lower-level diagnostics only (see PolyManagedAllocPathSnapshotV1); none of
 * these touches the original counters. The caller of FindAllocationSpace is
 * identified by a thread-local set immediately before each supported call.
 * An unidentified non-zero-word FindAllocationSpace outcome aborts.
 */
enum ManagedFindOutcome {
    ManagedFindSegment = 0,
    ManagedFindLargeObject = 1,
    ManagedFindRefill = 2
};
void ManagedSetFindCaller(ManagedAllocKind caller);
void RecordManagedFindSuccess(ManagedFindOutcome outcome, uint64_t words,
                              bool afterGC);
void RecordManagedFindFailure(uint64_t words);
void RecordManagedQuickGC(bool succeeded);
void RecordManagedCodeFailure();
void RecordManagedForeignThread();

/* FindAllocationSpace rounds heap reservations to even PolyWords in
 * compact32 mode. Native traps already report that rounded distance.
 */
inline uint64_t ManagedHeapReservationWords(uint64_t words)
{
#ifdef POLYML32IN64
    return words + (words & 1);
#else
    return words;
#endif
}
#endif
#endif
