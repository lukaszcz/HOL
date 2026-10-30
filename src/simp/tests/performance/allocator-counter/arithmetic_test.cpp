/* Synthetic arithmetic/concurrency test of the exact counter implementation.
 * NOT allocator coverage or allocated HOL words. Never linked into HOL.
 */
#include "managed_alloc_counter.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <signal.h>
#include <sys/wait.h>
#include <unistd.h>
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

static void read_path(uint64_t *out)
{
    require(PolyManagedAllocPathSnapshotV1(out, 256) == 0, "path snapshot");
}

/* One event that adds exactly one to counter index (and, for a success
 * cell, one word to that caller's word counter).
 */
static void path_event(unsigned index)
{
    if (index < 18) {
        ManagedSetFindCaller((ManagedAllocKind)(index / 6 + 1));
        RecordManagedFindSuccess((ManagedFindOutcome)((index % 6) / 2), 1,
                                 index & 1);
    } else if (index < 21) {
        ManagedSetFindCaller((ManagedAllocKind)(index - 18 + 1));
        RecordManagedFindFailure(1);
    } else if (index < 23) {
        RecordManagedQuickGC(index == 21);
    } else if (index == 23) {
        RecordManagedCodeFailure();
    } else if (index == 27) {
        RecordManagedForeignThread();
    } else {
        ManagedSetFindCaller((ManagedAllocKind)(index - 24 + 1));
        RecordManagedFindSuccess(ManagedFindSegment, 1, false);
    }
}

static void test_paths()
{
    uint64_t p[32], q[32], s[8], before[8], original[8];
    const uint64_t maximum = (uint64_t)-1;
    const unsigned counters = 28;
    read(original);
    LockManagedAllocation();
    memset(managedPathCounts, 0, sizeof(managedPathCounts));
    managedPathOverflow = 0;
    UnlockManagedAllocation();
    read_path(p);
    require(p[0] == 1 && p[1] == 8 && p[2] == 0 && p[31] == 0,
            "path metadata and reserved word");
    for (unsigned i = 3; i < 31; i++)
        require(p[i] == 0, "initial path counters");
    // Zero-word acquisition is not an event; unidentified callers abort.
    ManagedSetFindCaller(ManagedAllocRTS);
    RecordManagedFindSuccess(ManagedFindRefill, 0, true);
    RecordManagedFindFailure(0);
    read_path(p);
    for (unsigned i = 3; i < 31; i++)
        require(p[i] == 0, "zero-word path events are ignored");
    // Every caller/outcome/GC cell is distinct and records exact words.
    for (unsigned n = 0; n < 3; n++) {
        ManagedSetFindCaller((ManagedAllocKind)(n + 1));
        for (unsigned o = 0; o < 3; o++)
            for (unsigned g = 0; g < 2; g++)
                RecordManagedFindSuccess((ManagedFindOutcome)o,
                                         10 + 100 * n + o, g);
        RecordManagedFindFailure(5);
    }
    RecordManagedQuickGC(true);
    RecordManagedQuickGC(false);
    RecordManagedQuickGC(false);
    RecordManagedCodeFailure();
    read_path(p);
    require(p[2] == 0, "path counters did not overflow");
    for (unsigned n = 0; n < 3; n++) {
        for (unsigned o = 0; o < 3; o++)
            for (unsigned g = 0; g < 2; g++)
                require(p[3 + 6 * n + 2 * o + g] == 1, "path success cell");
        require(p[3 + 18 + n] == 1, "path failure cell");
        require(p[3 + 24 + n] == 2 * (30 + 300 * n + 3), "path word cell");
    }
    require(p[3 + 21] == 1 && p[3 + 22] == 2 && p[3 + 23] == 1,
            "QuickGC and code failure cells");
    require(p[3 + 27] == 0 && p[31] == 0, "foreign-thread cell is separate");
    // The path hooks never touch either original counter.
    read(s);
    require(memcmp(original, s, sizeof(s)) == 0,
            "path hooks leave original counters");
    // The ABI leaves the original and interpreter views alone.
    read(before);
    test_snapshot_abi(PolyManagedAllocSnapshotV1);
    read(s);
    require(memcmp(before, s, sizeof(s)) == 0, "original ABI unchanged");
    unsigned char buffer[258], saved[258];
    memset(buffer, 0x5a, sizeof(buffer));
    memcpy(saved, buffer, sizeof(buffer));
    require(PolyManagedAllocPathSnapshotV1(NULL, 256) == -1,
            "path ABI null output");
    for (size_t bytes = 0; bytes < 256; bytes += 8)
        require(PolyManagedAllocPathSnapshotV1(buffer + 1, bytes) == -1 &&
                memcmp(buffer, saved, sizeof(buffer)) == 0,
                "path ABI short buffer is untouched");
    require(PolyManagedAllocPathSnapshotV1(buffer + 1, 256) == 0 &&
            buffer[0] == 0x5a && buffer[257] == 0x5a, "path ABI unaligned");
    read_path(q);
    require(memcmp(buffer + 1, q, sizeof(q)) == 0 &&
            memcmp(p, q, sizeof(p)) == 0,
            "path snapshot is stable and allocates nothing");
    // The foreign-thread counter is its own cell: it moves nothing else.
    RecordManagedForeignThread();
    RecordManagedForeignThread();
    read_path(q);
    require(q[3 + 27] == 2 && q[2] == 0 && q[31] == 0 &&
            memcmp(p, q, 30 * sizeof(p[0])) == 0,
            "foreign-thread count moves only its own cell");
    // Concurrent success, failure and GC events remain coherent.
    LockManagedAllocation();
    memset(managedPathCounts, 0, sizeof(managedPathCounts));
    UnlockManagedAllocation();
    std::thread a([]() {
        ManagedSetFindCaller(ManagedAllocRTS);
        for (unsigned i = 0; i < 10000; i++)
            RecordManagedFindSuccess(ManagedFindLargeObject, 7, i & 1);
    });
    std::thread b([]() {
        ManagedSetFindCaller(ManagedAllocInterpreter);
        for (unsigned i = 0; i < 10000; i++) {
            RecordManagedFindSuccess(ManagedFindRefill, 3, false);
            RecordManagedQuickGC(true);
        }
    });
    for (unsigned i = 0; i < 10000; i++) {
        read_path(p);
        require(p[2] == 0 &&
                p[3 + 24 + 1] == 7 * (p[3 + 6 + 2] + p[3 + 6 + 3]) &&
                p[3 + 24 + 2] == 3 * p[3 + 12 + 4], "coherent path snapshot");
    }
    a.join();
    b.join();
    read_path(p);
    require(p[3 + 8] == 5000 && p[3 + 9] == 5000 && p[3 + 16] == 10000 &&
            p[3 + 21] == 10000 && p[3 + 25] == 70000 && p[3 + 26] == 30000,
            "retired path thread counts");
    // Each path overflow bit is independent of every other counter.
    for (unsigned index = 0; index < counters; index++) {
        LockManagedAllocation();
        memset(managedPathCounts, 0, sizeof(managedPathCounts));
        managedPathOverflow = 0;
        managedPathCounts[index] = maximum - 1;
        UnlockManagedAllocation();
        path_event(index);
        read_path(p);
        require(p[2] == 0 && p[3 + index] == maximum,
                "path exact maximum is representable");
        path_event(index);
        read_path(p);
        require(p[2] == ((uint64_t)1 << index) && p[3 + index] == maximum,
                "path saturation sets only its own sticky bit");
    }
}

/* Death tests of the exact implementation. Every supported caller of
 * FindAllocationSpace is tagged, so an unidentified caller cannot occur in
 * the built runtime; the abort is therefore executed here, in a forked child
 * whose process must die by SIGABRT (and whose positive control must not).
 */
static int child_status(void (*action)())
{
    fflush(stdout);
    fflush(stderr);
    pid_t pid = fork();
    require(pid >= 0, "fork");
    if (pid == 0) {
        action();
        _exit(0);
    }
    int status = 0;
    require(waitpid(pid, &status, 0) == pid, "waitpid");
    return status;
}

static void expect_abort(void (*action)(), const char *what)
{
    int status = child_status(action);
    require(WIFSIGNALED(status) && WTERMSIG(status) == SIGABRT, what);
}

static void expect_survival(void (*action)(), const char *what)
{
    int status = child_status(action);
    require(WIFEXITED(status) && WEXITSTATUS(status) == 0, what);
}

/* A thread that never called ManagedSetFindCaller sees the constant-
 * initialised tag zero.
 */
static void untagged(void (*event)())
{
    std::thread thread(event);
    thread.join();
}

static void success_event()
{
    RecordManagedFindSuccess(ManagedFindSegment, 1, false);
}
static void failure_event()
{
    RecordManagedFindFailure(1);
}
static void tagged_success()
{
    ManagedSetFindCaller(ManagedAllocRTS);
    success_event();
    ManagedSetFindCaller(ManagedAllocInterpreter);
    failure_event();
}
static void untagged_success() { untagged(success_event); }
static void untagged_failure() { untagged(failure_event); }
static void code_tagged_success()
{
    ManagedSetFindCaller(ManagedAllocCode);
    success_event();
}
static void cleared_failure()
{
    ManagedSetFindCaller(ManagedAllocRTS);
    ManagedSetFindCaller((ManagedAllocKind)0);
    failure_event();
}
static void invalid_kind_low()
{
    RecordManagedAllocation((ManagedAllocKind)0, 1);
}
static void invalid_kind_high()
{
    RecordManagedAllocation((ManagedAllocKind)5, 1);
}
static void invalid_outcome()
{
    ManagedSetFindCaller(ManagedAllocRTS);
    RecordManagedFindSuccess((ManagedFindOutcome)3, 1, false);
}
static void zero_words_untagged()
{
    untagged([]() {
        RecordManagedFindSuccess(ManagedFindSegment, 0, false);
        RecordManagedFindFailure(0);
    });
}

static void test_unidentified_callers()
{
    expect_survival(tagged_success, "tagged callers do not abort");
    expect_survival(zero_words_untagged,
                    "zero-word events need no caller");
    expect_abort(untagged_success, "untagged success event aborts");
    expect_abort(untagged_failure, "untagged failure event aborts");
    expect_abort(code_tagged_success,
                 "the code kind is not a FindAllocationSpace caller");
    expect_abort(cleared_failure, "cleared caller tag aborts");
    expect_abort(invalid_kind_low, "invalid allocation kind below range");
    expect_abort(invalid_kind_high, "invalid allocation kind above range");
    expect_abort(invalid_outcome, "invalid FindAllocationSpace outcome");
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
    test_paths();
    test_unidentified_callers();
    puts("@@TASK29_ALLOC_ARITHMETIC_V1\tpass\tsynthetic-only");
}
