// Diagnostic-only Poly/ML 5.9.2 full-64, little-endian Linux Arm64 hook.
// No runtime headers, invented virtual classes, or managed allocations.
// See README.md for the source/ABI audit and required extent controls.
#ifndef _GNU_SOURCE
#define _GNU_SOURCE
#endif
#include <atomic>
#include <climits>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <dlfcn.h>
#include <limits>

#if !defined(__aarch64__) || !defined(__LP64__) || defined(__AARCH64EB__)
#error "runtime-pools requires little-endian Linux Arm64 LP64"
#endif
#if !defined(__linux__)
#error "runtime-pools requires Linux ELF LD_PRELOAD"
#endif
static_assert(CHAR_BIT == 8 && sizeof(void*) == 8 &&
              sizeof(unsigned long) == 8,
              "only the audited full-64 ABI is supported");

namespace {
// These functions have ordinary AAPCS64 entry points, including the hidden
// member-function `this` argument. Objects stay opaque; no vtable is read.
using Word = unsigned long;
using ShowCode = void (*)(void*, void*);
using GetPool = void (*)(const void*, void*, Word, void*&, Word&);
using Architecture = int (*)(void*);
using Version = Word (*)();
constexpr Word lengthMask = 0x00ffffffffffffffUL;
constexpr const char* showSymbol =
    "_ZN21ProcessVisitAddresses8ShowCodeEP10PolyObject";
constexpr const char* poolSymbol =
    "_ZNK14Arm64Dependent22GetConstSegmentForCodeEP10PolyObjectmRP8PolyWordRm";
constexpr const char* archSymbol =
    "_ZN14Arm64Dependent19MachineArchitectureEv";

[[noreturn]] void fail(const char* why)
{
    // Never produce a success marker on failure. stderr is not evidence.
    std::fputs("runtime-pools: ", stderr);
    std::fputs(why, stderr);
    std::fputc('\n', stderr);
    std::abort();
}

void* resolve(const char* name)
{
    void* symbol = dlsym(RTLD_NEXT, name);
    if (!symbol) fail(name);
    return symbol;
}

void* image(void* symbol)
{
    Dl_info info{};
    if (!dladdr(symbol, &info) || !info.dli_fbase)
        fail("cannot identify runtime DSO");
    return info.dli_fbase;
}

struct Bindings {
    ShowCode show;
    GetPool pool;
    Architecture architecture;
    Version version;
    void** machine;
    FILE** output;

    Bindings()
    {
        void* s = resolve(showSymbol);
        void* p = resolve(poolSymbol);
        void* a = resolve(archSymbol);
        void* v = resolve("PolyGetPolyVersionNumber");
        void* m = resolve("machineDependent");
        void* o = resolve("polyStdout");
        void* base = image(s);
        if (image(p) != base || image(a) != base || image(v) != base ||
            image(m) != base || image(o) != base)
            fail("runtime symbols do not belong to one DSO");
        show = reinterpret_cast<ShowCode>(s);
        pool = reinterpret_cast<GetPool>(p);
        architecture = reinterpret_cast<Architecture>(a);
        version = reinterpret_cast<Version>(v);
        // machineDependent is a DATA SYMBOL holding a base singleton pointer,
        // not the singleton itself. Arm64Dependent has one nonvirtual base.
        machine = static_cast<void**>(m);
        output = static_cast<FILE**>(o);
    }

    void validate() const
    {
        // PolyGetPolyVersionNumber returns TAGGED(POLY_version_number).
        // MA_Arm64 == 4; MA_Arm64_32 == 5, MA_Interpreted == 0.
        if (version() != ((592UL << 1) | 1) || !*machine ||
            architecture(*machine) != 4 || !*output)
            fail("requires Poly/ML 5.9.2 native Arm64 full-64");
    }
};

Bindings& bindings()
{
    // Native loader work only, never ML allocation. Begin resolves this before
    // the diagnostic showSize. An unrelated hook may resolve it first.
    static Bindings value;
    return value;
}

// Exactly one explicitly bracketed extent per process. The controlling ML
// task may migrate between OS threads, so these are not thread-local flags.
std::atomic<int> phase{0}; // 0 unused, 1 active, 2 finished
std::atomic<bool> admitted{false};
std::atomic_flag inHook = ATOMIC_FLAG_INIT;

Word readWord(const void* pointer)
{
    Word value;
    std::memcpy(&value, pointer, sizeof(value));
    return value;
}

void emit(Bindings& b, void* owner)
{
    b.validate();
    const auto start = reinterpret_cast<std::uintptr_t>(owner);
    if (start < 8 || start % 8) fail("unaligned code owner");
    const Word header = readWord(reinterpret_cast<void*>(start - 8));
    const Word length = header & lengthMask;
    if (((header >> 56) & 0x83) != 2 || length == 0 ||
        length > (std::numeric_limits<std::uintptr_t>::max() - start) / 8)
        fail("invalid full-64 code object header");
    const auto end = start + length * 8;
    const bool isInline =
        (readWord(reinterpret_cast<void*>(end - 8)) >> 56) == 0xff;

    void* pool = nullptr;
    Word count = 0;
    // Direct exported helper, NOT MachineDependent's default implementation
    // and NOT a virtual call through a guessed class/vtable declaration.
    b.pool(*b.machine, owner, length, pool, count);
    const auto address = reinterpret_cast<std::uintptr_t>(pool);
    if (address < 8 || address % 8 || count < 2 ||
        count > (std::numeric_limits<std::uintptr_t>::max() - address) / 8)
        fail("invalid constant segment");
    const bool within = address > start && address < end;
    if (isInline != within ||
        (isInline && count > (end - 8 - address) / 8))
        fail("constant segment disagrees with Arm64 code trailer");
    const Word poolHeader = readWord(reinterpret_cast<void*>(address - 8));
    if (count != (isInline ? poolHeader : poolHeader & lengthMask))
        fail("constant count disagrees with runtime helper");

    FILE* out = *b.output;
    if (!admitted.exchange(true))
        std::fputs("@@RUNTIME_POOL\tloaded\tarm64-full64-v1\n", out);
    std::fprintf(out, "@@RUNTIME_POOL\tbegin\t0x%lx\t0x%lx\t%lu\t%s\n",
                 start, address, count, isInline ? "inline" : "split");
    // Raw full-width words, including tagged integers and nonpointer bits.
    // No names, dereferencing of pool entries, callbacks, or ML conversions.
    for (Word i = 0; i < count; ++i) {
        std::fprintf(out, "0x%016lx%s",
                     readWord(reinterpret_cast<void*>(address + i * 8)),
                     (i % 4 == 3 || i + 1 == count) ? "\n" : "\t");
    }
    std::fprintf(out, "@@RUNTIME_POOL\tend\t0x%lx\n", start);
    if (std::ferror(out)) fail("runtime output failed");
}
} // namespace

// Call AFTER writing/flushing @@RUNTIME_LAYOUT begin and BEFORE showSize.
// No output here: admission is emitted only by the first actual code hook.
extern "C" void runtime_pools_begin()
{
    bindings().validate();
    int expected = 0;
    if (!phase.compare_exchange_strong(expected, 1))
        fail("nested/repeated extent");
}

// Call AFTER showSize returns and BEFORE writing @@RUNTIME_LAYOUT end.
extern "C" void runtime_pools_end()
{
    int expected = 1;
    if (!phase.compare_exchange_strong(expected, 2))
        fail("end without active extent");
    if (inHook.test_and_set()) fail("end during ShowCode");
    inHook.clear();
    if (std::fflush(*bindings().output)) fail("runtime flush failed");
}

extern "C" void runtime_pools_show_code(void*, void*)
    asm("_ZN21ProcessVisitAddresses8ShowCodeEP10PolyObject");

extern "C" void runtime_pools_show_code(void* visitor, void* owner)
{
    Bindings& b = bindings();
    if (phase.load() != 1) {
        b.show(visitor, owner);
        return;
    }
    if (inHook.test_and_set())
        fail("concurrent/reentrant diagnostic ShowCode");
    // Preserve the original code record verbatim and in its original position.
    // Everything goes to the runtime FILE*, not ML TextIO or raw fd writes.
    b.show(visitor, owner);
    emit(b, owner);
    inHook.clear();
}
