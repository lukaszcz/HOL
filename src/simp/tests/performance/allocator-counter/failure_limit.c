/* Actual OS address-space limit for the separate failure-controls process.
 * Link INTO bracket.so, not a second runtime/shim. Call only outside measured
 * brackets, after building every FFI closure and warming a full GC. The
 * Poly/ML --maxheap switch alone is soft: AllocHeapSpace permits oversized
 * objects.
 * No allocator counter access, runtime patches, or requested-size allocation.
 * Single controlling thread; this API is deliberately one-shot.
 */
#define _POSIX_C_SOURCE 200809L
#include <fcntl.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <sys/resource.h>
#include <unistd.h>

#define HEADROOM UINT64_C(67108864)

_Static_assert(sizeof(rlim_t) <= sizeof(uint64_t), "rlim_t too wide");

/* vsize_before, applied_soft, hard (UINT64_MAX = unlimited), headroom. */
static uint64_t values[4];
static int attempted, ready;

/* Read only the first statm field; stack storage, no malloc/stdio buffering.
 * Reject truncation/overflow rather than reporting a plausible limit.
 */
static int virtual_bytes(uint64_t *bytes)
{
    char buffer[64];
    uint64_t pages = 0;
    long page_size = sysconf(_SC_PAGESIZE);
    if (page_size <= 0)
        return 0;
    int fd = open("/proc/self/statm", O_RDONLY | O_CLOEXEC);
    if (fd < 0)
        return 0;
    ssize_t count = read(fd, buffer, sizeof(buffer));
    int closed = close(fd);
    if (count <= 0 || closed != 0)
        return 0;
    ssize_t i = 0;
    for (; i < count && buffer[i] >= '0' && buffer[i] <= '9'; ++i)
    {
        uint64_t digit = (uint64_t)(buffer[i] - '0');
        if (pages > (UINT64_MAX - digit) / 10)
            return 0;
        pages = pages * 10 + digit;
    }
    if (i == 0 || i == count || buffer[i] != ' ' || pages == 0 ||
        pages > UINT64_MAX / (uint64_t)page_size)
        return 0;
    *bytes = pages * (uint64_t)page_size;
    return 1;
}

/* Noarg Foreign call: 1 only after setrlimit AND independent re-read succeed.
 * Failure invalidates the fixture; it must not proceed to measured requests.
 */
int task29_failure_limit(void)
{
    struct rlimit before, verified;
    uint64_t vsize, bound, hard;
    if (attempted)
        return 0;
    attempted = 1;
    if (!virtual_bytes(&vsize) || getrlimit(RLIMIT_AS, &before) != 0 ||
        vsize > UINT64_MAX - HEADROOM)
        return 0;
    bound = vsize + HEADROOM;
    hard = before.rlim_max == RLIM_INFINITY ? UINT64_MAX :
           (uint64_t)before.rlim_max;
    rlim_t soft = (rlim_t)bound;
    if (bound > hard || (uint64_t)soft != bound || soft == RLIM_INFINITY ||
        (before.rlim_cur != RLIM_INFINITY && bound > before.rlim_cur))
        return 0;
    struct rlimit applied = { soft, before.rlim_max };
    if (setrlimit(RLIMIT_AS, &applied) != 0 ||
        getrlimit(RLIMIT_AS, &verified) != 0 ||
        verified.rlim_cur != soft || verified.rlim_max != before.rlim_max)
        return 0;
    values[0] = vsize;
    values[1] = (uint64_t)verified.rlim_cur;
    values[2] = hard;
    values[3] = HEADROOM;
    ready = 1;
    return 1;
}

uint64_t task29_failure_limit_get(int index)
{
    if (!ready || index < 0 || index >= 4)
    {
        fputs("task29 failure limit: invalid getter access\n", stderr);
        abort();
    }
    return values[index];
}
