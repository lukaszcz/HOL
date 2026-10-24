// Experimental managed allocation counter. Embedded in run_time.cpp.
// Deliberately refuse unsupported targets rather than expose a partial total.
#if !defined(__linux__) || !defined(__aarch64__) || \
    !defined(HOSTARCHITECTURE_AARCH64) || defined(CODEISNOTEXECUTABLE)
#error "Managed allocation counter requires native Linux/aarch64 Poly/ML"
#endif
#if SIZEOF_VOIDP != 8
#error "Managed allocation counter requires 64-bit C pointers"
#endif

#include <pthread.h>
#include <stdlib.h>
#include <string.h>

namespace {
// Static initialization: no C++ constructor-order dependency or ML allocation.
pthread_mutex_t managedAllocMutex = PTHREAD_MUTEX_INITIALIZER;
uint64_t managedAllocCounts[5] = { 0, 0, 0, 0, 0 };
uint64_t managedAllocOverflow = 0;

void LockManagedAllocation()
{
    if (pthread_mutex_lock(&managedAllocMutex) != 0) abort();
}

void UnlockManagedAllocation()
{
    if (pthread_mutex_unlock(&managedAllocMutex) != 0) abort();
}

void AddManagedAllocation(unsigned index, uint64_t words)
{
    const uint64_t maximum = (uint64_t)-1;
    if (words > maximum - managedAllocCounts[index])
    {
        managedAllocCounts[index] = maximum;
        managedAllocOverflow |= (uint64_t)1 << index;
    }
    else managedAllocCounts[index] += words;
}
}

void RecordManagedAllocation(ManagedAllocKind kind, uint64_t words)
{
    if (words == 0) return;
    if (kind < ManagedAllocNative || kind > ManagedAllocCode) abort();
    LockManagedAllocation();
    AddManagedAllocation(0, words);
    AddManagedAllocation((unsigned)kind, words);
    UnlockManagedAllocation();
}

extern "C" __attribute__((visibility("default")))
int PolyManagedAllocSnapshotV1(void *out, size_t bytes)
{
    if (out == 0 || bytes < POLY_MANAGED_ALLOC_SNAPSHOT_BYTES_V1) return -1;
    uint64_t snapshot[POLY_MANAGED_ALLOC_SNAPSHOT_WORDS_V1];
    LockManagedAllocation();
    snapshot[0] = 1;
    snapshot[1] = sizeof(PolyWord);
    snapshot[2] = managedAllocOverflow;
    for (unsigned i = 0; i < 5; i++) snapshot[i + 3] = managedAllocCounts[i];
    UnlockManagedAllocation();
    // memcpy permits unaligned C buffers. No managed allocation or callback.
    memcpy(out, snapshot, sizeof(snapshot));
    return 0;
}
