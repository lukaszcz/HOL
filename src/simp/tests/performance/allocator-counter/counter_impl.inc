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
// Fast count/words, slow count/words. Independent saturation and flags.
uint64_t managedInterpreterAllocCounts[4] = { 0, 0, 0, 0 };
uint64_t managedInterpreterAllocOverflow = 0;
// Lower-level path diagnostics: see PolyManagedAllocPathSnapshotV1.
const unsigned managedPathCounters = 28;
uint64_t managedPathCounts[managedPathCounters];
uint64_t managedPathOverflow = 0;
// Constant-initialised: no dynamic TLS constructor or ML allocation.
thread_local unsigned managedFindCaller = 0;

void LockManagedAllocation()
{
    if (pthread_mutex_lock(&managedAllocMutex) != 0) abort();
}

void UnlockManagedAllocation()
{
    if (pthread_mutex_unlock(&managedAllocMutex) != 0) abort();
}

void AddSaturating(uint64_t *counts, uint64_t &overflow,
                   unsigned index, uint64_t increment)
{
    const uint64_t maximum = (uint64_t)-1;
    if (increment > maximum - counts[index])
    {
        counts[index] = maximum;
        overflow |= (uint64_t)1 << index;
    }
    else counts[index] += increment;
}

void AddManagedAllocation(unsigned index, uint64_t words)
{
    AddSaturating(managedAllocCounts, managedAllocOverflow, index, words);
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

void RecordManagedInterpreterAllocation(bool slow, uint64_t words)
{
    if (words == 0) return;
    const unsigned index = slow ? 2 : 0;
    LockManagedAllocation();
    AddManagedAllocation(0, words);
    AddManagedAllocation(ManagedAllocInterpreter, words);
    AddSaturating(managedInterpreterAllocCounts,
                  managedInterpreterAllocOverflow, index, 1);
    AddSaturating(managedInterpreterAllocCounts,
                  managedInterpreterAllocOverflow, index + 1, words);
    UnlockManagedAllocation();
}

void ManagedSetFindCaller(ManagedAllocKind caller)
{
    managedFindCaller = (unsigned)caller;
}

static unsigned ManagedFindCallerIndex()
{
    if (managedFindCaller < ManagedAllocNative ||
        managedFindCaller > ManagedAllocInterpreter) abort();
    return managedFindCaller - ManagedAllocNative;
}

void RecordManagedFindSuccess(ManagedFindOutcome outcome, uint64_t words,
                              bool afterGC)
{
    if (words == 0) return;
    if (outcome < ManagedFindSegment || outcome > ManagedFindRefill) abort();
    const unsigned n = ManagedFindCallerIndex();
    LockManagedAllocation();
    AddSaturating(managedPathCounts, managedPathOverflow,
                  6 * n + 2 * (unsigned)outcome + (afterGC ? 1 : 0), 1);
    AddSaturating(managedPathCounts, managedPathOverflow, 24 + n, words);
    UnlockManagedAllocation();
}

void RecordManagedFindFailure(uint64_t words)
{
    if (words == 0) return;
    const unsigned n = ManagedFindCallerIndex();
    LockManagedAllocation();
    AddSaturating(managedPathCounts, managedPathOverflow, 18 + n, 1);
    UnlockManagedAllocation();
}

void RecordManagedQuickGC(bool succeeded)
{
    LockManagedAllocation();
    AddSaturating(managedPathCounts, managedPathOverflow,
                  succeeded ? 21 : 22, 1);
    UnlockManagedAllocation();
}

void RecordManagedCodeFailure()
{
    LockManagedAllocation();
    AddSaturating(managedPathCounts, managedPathOverflow, 23, 1);
    UnlockManagedAllocation();
}

void RecordManagedForeignThread()
{
    LockManagedAllocation();
    AddSaturating(managedPathCounts, managedPathOverflow, 27, 1);
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

extern "C" __attribute__((visibility("default")))
int PolyManagedInterpreterAllocSnapshotV1(void *out, size_t bytes)
{
    if (out == 0 || bytes < POLY_MANAGED_INTERPRETER_ALLOC_SNAPSHOT_BYTES_V1)
        return -1;
    uint64_t snapshot[POLY_MANAGED_INTERPRETER_ALLOC_SNAPSHOT_WORDS_V1];
    LockManagedAllocation();
    snapshot[0] = 1;
    snapshot[1] = sizeof(PolyWord);
    snapshot[2] = managedInterpreterAllocOverflow;
    for (unsigned i = 0; i < 4; i++)
        snapshot[i + 3] = managedInterpreterAllocCounts[i];
    snapshot[7] = 0;
    UnlockManagedAllocation();
    memcpy(out, snapshot, sizeof(snapshot));
    return 0;
}

extern "C" __attribute__((visibility("default")))
int PolyManagedAllocPathSnapshotV1(void *out, size_t bytes)
{
    if (out == 0 || bytes < POLY_MANAGED_PATH_ALLOC_SNAPSHOT_BYTES_V1)
        return -1;
    uint64_t snapshot[POLY_MANAGED_PATH_ALLOC_SNAPSHOT_WORDS_V1];
    memset(snapshot, 0, sizeof(snapshot));
    LockManagedAllocation();
    snapshot[0] = 1;
    snapshot[1] = sizeof(PolyWord);
    snapshot[2] = managedPathOverflow;
    for (unsigned i = 0; i < managedPathCounters; i++)
        snapshot[i + 3] = managedPathCounts[i];
    UnlockManagedAllocation();
    memcpy(out, snapshot, sizeof(snapshot));
    return 0;
}
