/* Runtime controls, NOT synthetic counter injection.
 * Link against the very libpolyml used by the HOL launcher.  The caller must
 * seal/check its actual process mappings; a second runtime DSO is invalid.
 * Single controlling ML thread only: these buffers are not a concurrent API.
 * The runtime snapshot, not this shim, provides coherent counter reads.
 */
#define _GNU_SOURCE
#include "managed_alloc_counter.h"

#include <dlfcn.h>
#include <stdio.h>
#include <string.h>
#include <stdlib.h>

_Static_assert(sizeof(uint64_t) == 8, "snapshot requires uint64_t");
_Static_assert(POLY_MANAGED_ALLOC_SNAPSHOT_WORDS_V1 == 8,
               "unexpected snapshot layout");
_Static_assert(POLY_MANAGED_ALLOC_SNAPSHOT_BYTES_V1 == 64,
               "unexpected snapshot size");

_Static_assert(POLY_MANAGED_INTERPRETER_ALLOC_SNAPSHOT_WORDS_V1 == 8,
               "unexpected interpreter snapshot layout");
_Static_assert(POLY_MANAGED_INTERPRETER_ALLOC_SNAPSHOT_BYTES_V1 == 64,
               "unexpected interpreter snapshot size");

static uint64_t endpoints[2][POLY_MANAGED_ALLOC_SNAPSHOT_WORDS_V1];
static uint64_t interpreter_endpoints[2]
    [POLY_MANAGED_INTERPRETER_ALLOC_SNAPSHOT_WORDS_V1];
static int phase; /* 0 = unused, 1 = started, 2 = ended/decodable */

static void fail(const char *message)
{
    fputs(message, stderr);
    fputc('\n', stderr);
    abort();
}

/* Identity is queried outside the measured bracket. Do not load a second
 * runtime to obtain the symbol: dladdr reports its actual resolved binding.
 */
const char *task29_alloc_runtime(void)
{
    Dl_info info, branch;
    if (!dladdr((void *)&PolyManagedAllocSnapshotV1, &info) || !info.dli_fname ||
        !dladdr((void *)&PolyManagedInterpreterAllocSnapshotV1, &branch) ||
        !branch.dli_fname || branch.dli_fbase != info.dli_fbase)
        fail("task29 allocator bracket: missing/different snapshot runtime");
    return info.dli_fname;
}

/* Direct C ABI/no-allocation controls, not a claim about generic FFI glue.
 * A successful result has bits 0..3 set. Never mutate runtime counters.
 * Apply the same synthetic C buffer tests to both snapshot entry points.
 */
static int snapshot_abi_check(int (*snapshot)(void *, size_t))
{
    unsigned char buffer[66], before[66];
    uint64_t a[8], b[8], unaligned[8];
    memset(buffer, 0x5a, sizeof(buffer));
    memcpy(before, buffer, sizeof(buffer));
    int result = 0;
    if (snapshot(NULL, 64) == -1)
        result |= 1;
    if (snapshot(buffer + 1, 63) == -1 &&
        memcmp(buffer, before, sizeof(buffer)) == 0)
        result |= 2;
    if (snapshot(a, sizeof(a)) == 0 &&
        snapshot(buffer + 1, 64) == 0 &&
        snapshot(b, sizeof(b)) == 0)
    {
        memcpy(unaligned, buffer + 1, sizeof(unaligned));
        if (buffer[0] == 0x5a && buffer[65] == 0x5a &&
            memcmp(a, unaligned, sizeof(a)) == 0)
            result |= 4;
        if (memcmp(a, b, sizeof(a)) == 0)
            result |= 8;
    }
    return result;
}

int task29_alloc_abi_check(void)
{
    uint64_t before[8], after[8];
    int have_before = PolyManagedAllocSnapshotV1(before, sizeof(before));
    int original = snapshot_abi_check(PolyManagedAllocSnapshotV1);
    int interpreter = snapshot_abi_check(PolyManagedInterpreterAllocSnapshotV1);
    int have_after = PolyManagedAllocSnapshotV1(after, sizeof(after));
    int result = original & interpreter;
    /* Diagnostic stability alone cannot detect an RTS/native allocation by
     * its snapshot function. Check original allocation words around both.
     */
    if (have_before != 0 || have_after != 0 ||
        memcmp(before, after, sizeof(before)) != 0)
        result &= ~8;
    return result; /* Preserve the successful result of 15. */
}

/* No arguments, results, callbacks, malloc, or ML pointers in the bracket.
 * cVoid FFI return/entry glue can still allocate: measure it with no-ops.
 */
void task29_alloc_start(void)
{
    if (phase == 1)
        fail("task29 allocator bracket: nested start");
    if (PolyManagedAllocSnapshotV1(endpoints[0], sizeof(endpoints[0])) != 0)
        fail("task29 allocator bracket: start snapshot failed");
    if (PolyManagedInterpreterAllocSnapshotV1(interpreter_endpoints[0],
            sizeof(interpreter_endpoints[0])) != 0)
        fail("task29 allocator bracket: interpreter start snapshot failed");
    phase = 1;
}

void task29_alloc_end(void)
{
    if (phase != 1)
        fail("task29 allocator bracket: end without start");
    if (PolyManagedAllocSnapshotV1(endpoints[1], sizeof(endpoints[1])) != 0)
        fail("task29 allocator bracket: end snapshot failed");
    if (PolyManagedInterpreterAllocSnapshotV1(interpreter_endpoints[1],
            sizeof(interpreter_endpoints[1])) != 0)
        fail("task29 allocator bracket: interpreter end snapshot failed");
    phase = 2;
}

/* Decode ONLY after end: 0..7 = start, 8..15 = end.  Conversion to ML
 * LargeInt may allocate, but cannot alter the already stored endpoints.
 * Out-of-range/early reads abort instead of returning plausible evidence.
 */
uint64_t task29_alloc_get(int index)
{
    if (phase != 2 || index < 0 || index >= 16)
        fail("task29 allocator bracket: invalid decoder access");
    return endpoints[index / 8][index % 8];
}

/* Same indexing/lifetime as task29_alloc_get. The original and diagnostic
 * snapshots are sequential, not one atomic cross-ABI snapshot pair.
 */
uint64_t task29_alloc_interpreter_get(int index)
{
    if (phase != 2 || index < 0 || index >= 16)
        fail("task29 allocator bracket: invalid interpreter decoder access");
    return interpreter_endpoints[index / 8][index % 8];
}
