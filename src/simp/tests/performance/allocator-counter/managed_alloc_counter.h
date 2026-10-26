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
