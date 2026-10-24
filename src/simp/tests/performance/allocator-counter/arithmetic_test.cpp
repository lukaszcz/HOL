/* Synthetic arithmetic/concurrency test of the exact counter implementation.
 * NOT allocator coverage or allocated HOL words. Never linked into HOL.
 */
#include "managed_alloc_counter.h"
#include <stdio.h>
#include <stdlib.h>
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
    puts("@@TASK29_ALLOC_ARITHMETIC_V1\tpass\tsynthetic-only");
}
