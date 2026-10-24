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

static uint64_t endpoints[2][POLY_MANAGED_ALLOC_SNAPSHOT_WORDS_V1];
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
    Dl_info info;
    if (!dladdr((void *)&PolyManagedAllocSnapshotV1, &info) || !info.dli_fname)
        fail("task29 allocator bracket: no runtime symbol identity");
    return info.dli_fname;
}

/* Direct C ABI/no-allocation controls, not a claim about generic FFI glue.
 * A successful result has bits 0..3 set. Never mutate runtime counters.
 */
int task29_alloc_abi_check(void)
{
    unsigned char buffer[66], before[66];
    uint64_t a[8], b[8], unaligned[8];
    memset(buffer, 0x5a, sizeof(buffer));
    memcpy(before, buffer, sizeof(buffer));
    int result = 0;
    if (PolyManagedAllocSnapshotV1(NULL, 64) == -1)
        result |= 1;
    if (PolyManagedAllocSnapshotV1(buffer + 1, 63) == -1 &&
        memcmp(buffer, before, sizeof(buffer)) == 0)
        result |= 2;
    if (PolyManagedAllocSnapshotV1(a, sizeof(a)) == 0 &&
        PolyManagedAllocSnapshotV1(buffer + 1, 64) == 0 &&
        PolyManagedAllocSnapshotV1(b, sizeof(b)) == 0)
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

/* No arguments, results, callbacks, malloc, or ML pointers in the bracket.
 * cVoid FFI return/entry glue can still allocate: measure it with no-ops.
 */
void task29_alloc_start(void)
{
    if (phase == 1)
        fail("task29 allocator bracket: nested start");
    if (PolyManagedAllocSnapshotV1(endpoints[0], sizeof(endpoints[0])) != 0)
        fail("task29 allocator bracket: start snapshot failed");
    phase = 1;
}

void task29_alloc_end(void)
{
    if (phase != 1)
        fail("task29 allocator bracket: end without start");
    if (PolyManagedAllocSnapshotV1(endpoints[1], sizeof(endpoints[1])) != 0)
        fail("task29 allocator bracket: end snapshot failed");
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
