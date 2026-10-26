/* Synthetic arithmetic/concurrency test of the exact counter implementation.
 * NOT allocator coverage or allocated HOL words. Never linked into HOL.
 */
#include "managed_alloc_counter.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <thread>
#include <vector>

typedef uint64_t PolyWord;
#include "counter_impl.inc"

static void require(bool yes, const char *what)
{
    if (!yes) { fprintf(stderr, "FAIL: %s\n", what); exit(1); }
}
static void read(uint64_t *out)
{
    require(PolyManagedAllocSnapshotV1(out, 64) == 0, "snapshot");
}
static void read_interpreter(uint64_t *out)
{
    require(PolyManagedInterpreterAllocSnapshotV1(out, 64) == 0,
            "interpreter snapshot");
}

/* Synthetic C ABI buffer tests; no managed pointers or FFI glue involved.
 * Each entry point must itself leave counters unchanged. This is not a
 * claim about allocation by an ML caller's foreign-call glue.
 */
static void test_snapshot_abi(int (*snapshot)(void *, size_t))
{
    unsigned char buffer[82], before[82];
    uint64_t a[8], b[8], unaligned[8], original_before[8], original_after[8];
    read(original_before);
    memset(buffer, 0x5a, sizeof(buffer));
    memcpy(before, buffer, sizeof(buffer));
    require(snapshot(NULL, 0) == -1 && snapshot(NULL, 64) == -1,
            "C ABI null output");
    for (size_t bytes = 0; bytes < 64; bytes++)
        require(snapshot(buffer + 1, bytes) == -1 &&
                memcmp(buffer, before, sizeof(buffer)) == 0,
                "C ABI short buffer is untouched");
    require(snapshot(a, sizeof(a)) == 0 &&
            snapshot(buffer + 1, 80) == 0 &&
            snapshot(b, sizeof(b)) == 0, "C ABI buffer acceptance");
    memcpy(unaligned, buffer + 1, sizeof(unaligned));
    require(buffer[0] == 0x5a &&
            memcmp(buffer + 65, before + 65, sizeof(buffer) - 65) == 0,
            "C ABI writes exactly 64 bytes");
    require(memcmp(a, unaligned, sizeof(a)) == 0 &&
            memcmp(a, b, sizeof(a)) == 0,
            "C ABI unaligned snapshot and no counter allocation");
    read(original_after);
    require(memcmp(original_before, original_after,
                   sizeof(original_before)) == 0,
            "C ABI diagnostic reads allocate no original category words");
}

/* Test-only injection, with no live workers. Never part of the runtime ABI. */
static void reset_synthetic_counters()
{
    LockManagedAllocation();
    memset(managedAllocCounts, 0, sizeof(managedAllocCounts));
    memset(managedInterpreterAllocCounts, 0,
           sizeof(managedInterpreterAllocCounts));
    managedAllocOverflow = managedInterpreterAllocOverflow = 0;
    UnlockManagedAllocation();
}

static void test_interpreter()
{
    uint64_t s[8], d[8];
    const uint64_t maximum = (uint64_t)-1;
    reset_synthetic_counters();
    read_interpreter(d);
    require(d[0] == 1 && d[1] == 8 && d[2] == 0 && d[7] == 0,
            "diagnostic metadata and reserved word");
    for (unsigned i = 3; i < 7; i++)
        require(d[i] == 0, "initial diagnostic fields");
    RecordManagedInterpreterAllocation(false, 0);
    RecordManagedInterpreterAllocation(true, 0);
    read(s);
    read_interpreter(d);
    require(s[3] == 0 && d[3] == 0 && d[5] == 0,
            "zero words is not a successful counted allocation");
    RecordManagedInterpreterAllocation(false, 3);
    RecordManagedInterpreterAllocation(false, 7);
    RecordManagedInterpreterAllocation(true, 5);
    read(s);
    read_interpreter(d);
    require(s[2] == 0 && s[3] == 15 && s[6] == 15 &&
            s[4] == 0 && s[5] == 0 && s[7] == 0,
            "branch hooks preserve original interpreter word semantics");
    require(d[2] == 0 && d[3] == 2 && d[4] == 10 &&
            d[5] == 1 && d[6] == 5 && d[7] == 0,
            "separate fast and slow success counts and words");
    test_snapshot_abi(PolyManagedAllocSnapshotV1);
    test_snapshot_abi(PolyManagedInterpreterAllocSnapshotV1);
    // Other original API calls must not masquerade as bytecode branches.
    RecordManagedAllocation(ManagedAllocInterpreter, 9);
    RecordManagedAllocation(ManagedAllocRTS, 2);
    uint64_t unchanged[8];
    read_interpreter(unchanged);
    require(memcmp(d, unchanged, sizeof(d)) == 0,
            "diagnostics are private to instrumented interpreter branches");

    reset_synthetic_counters();
    std::thread fast([]() {
        for (unsigned i = 0; i < 10000; i++)
            RecordManagedInterpreterAllocation(false, 3);
    });
    std::thread slow([]() {
        for (unsigned i = 0; i < 10000; i++)
            RecordManagedInterpreterAllocation(true, 5);
    });
    for (unsigned i = 0; i < 10000; i++) {
        read_interpreter(d);
        require(d[2] == 0 && d[4] == 3 * d[3] &&
                d[6] == 5 * d[5] && d[7] == 0,
                "coherent concurrent diagnostic snapshot");
        // Separate ABI snapshots cannot promise a cross-snapshot invariant.
        // Inspect both sets under their shared lock to test atomic updates.
        LockManagedAllocation();
        require(managedAllocCounts[0] == managedAllocCounts[3] &&
                managedAllocCounts[3] == managedInterpreterAllocCounts[1] +
                                         managedInterpreterAllocCounts[3],
                "original and diagnostic updates share one critical section");
        UnlockManagedAllocation();
    }
    fast.join();
    slow.join();
    read(s);
    read_interpreter(d);
    require(s[3] == 80000 && s[6] == 80000 &&
            d[3] == 10000 && d[4] == 30000 &&
            d[5] == 10000 && d[6] == 50000,
            "retired fast and slow thread counts");

    // Isolate every diagnostic overflow bit, including count overflow.
    for (unsigned index = 0; index < 4; index++) {
        reset_synthetic_counters();
        managedInterpreterAllocCounts[index] = maximum - 1;
        RecordManagedInterpreterAllocation(index >= 2, 1);
        read_interpreter(d);
        require(d[2] == 0 && d[index + 3] == maximum,
                "diagnostic exact maximum is representable");
        RecordManagedInterpreterAllocation(index >= 2, 1);
        read(s);
        read_interpreter(d);
        require(d[2] == ((uint64_t)1 << index) &&
                d[index + 3] == maximum && s[2] == 0 && s[6] == 2,
                "diagnostic saturation independent of original overflow");
        RecordManagedInterpreterAllocation(index < 2, 7);
        read_interpreter(d);
        require(d[2] == ((uint64_t)1 << index) &&
                d[index < 2 ? 5 : 3] == 1 &&
                d[index < 2 ? 6 : 4] == 7,
                "sticky diagnostic bit does not stop other branch");
    }
    reset_synthetic_counters();
    managedAllocCounts[0] = managedAllocCounts[3] = maximum;
    RecordManagedInterpreterAllocation(true, 5);
    read(s);
    read_interpreter(d);
    require(s[2] == 9 && s[3] == maximum && s[6] == maximum &&
            d[2] == 0 && d[5] == 1 && d[6] == 5,
            "original overflow does not contaminate diagnostics");
    reset_synthetic_counters();
    RecordManagedInterpreterAllocation(false, maximum);
    RecordManagedInterpreterAllocation(false, 1);
    read(s);
    read_interpreter(d);
    require(s[2] == 9 && d[2] == 2 && d[3] == 2 && d[4] == maximum,
            "word saturation preserves exact success count");
}

int main()
{
    uint64_t s[8];
    read(s);
    require(s[0] == 1 && s[1] == 8 && s[2] == 0 && s[3] == 0,
            "initial state");
    RecordManagedAllocation(ManagedAllocNative, 0);
    read(s);
    require(s[3] == 0 && s[2] == 0, "zero increment");
    std::vector<std::thread> threads;
    for (unsigned k = 1; k <= 4; k++)
        threads.emplace_back([k]() {
            for (unsigned i = 0; i < 10000; i++)
                RecordManagedAllocation((ManagedAllocKind)k, 3);
        });
    for (auto &thread: threads) thread.join();
    read(s);
    require(s[2] == 0 && s[3] == 120000, "joined-thread total");
    for (unsigned k = 4; k < 8; k++)
        require(s[k] == 30000, "joined-thread category");
    // Snapshot concurrently with updates; total/category relation must hold.
    std::thread worker([]() {
        for (unsigned i = 0; i < 10000; i++)
            RecordManagedAllocation(ManagedAllocRTS, 1);
    });
    for (unsigned i = 0; i < 10000; i++) {
        read(s);
        require(s[2] == 0 && s[3] == s[4]+s[5]+s[6]+s[7],
                "coherent concurrent snapshot");
    }
    worker.join();
    read(s);
    require(s[3] == 130000 && s[5] == 40000, "retired-thread total");
    // Inject arithmetic boundary state privately, not into the runtime DSO.
    const uint64_t maximum = (uint64_t)-1;
    managedAllocCounts[0] = maximum - 2;
    managedAllocCounts[1] = maximum - 2;
    managedAllocCounts[2] = managedAllocCounts[3] = managedAllocCounts[4] = 0;
    RecordManagedAllocation(ManagedAllocNative, 2);
    read(s);
    require(s[2] == 0 && s[3] == maximum && s[4] == maximum,
            "exact maximum is representable");
    RecordManagedAllocation(ManagedAllocNative, 1);
    read(s);
    require(s[2] == 3 && s[3] == maximum && s[4] == maximum,
            "native/total saturate with sticky flags");
    RecordManagedAllocation(ManagedAllocCode, 1);
    read(s);
    require(s[2] == 3 && s[3] == maximum && s[7] == 1,
            "other category still counts after total overflow");
    managedAllocOverflow = 0;
    managedAllocCounts[0] = maximum - 1;
    managedAllocCounts[1] = maximum - 1;
    managedAllocCounts[2] = managedAllocCounts[3] = managedAllocCounts[4] = 0;
    RecordManagedAllocation(ManagedAllocCode, 2);
    read(s);
    require(s[2] == 1 && s[3] == maximum && s[7] == 2,
            "total-only overflow");
    test_interpreter();
    puts("@@TASK29_ALLOC_ARITHMETIC_V1\tpass\tsynthetic-only");
}
