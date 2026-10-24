// Harness-only negative control, NOT an allocation counter/interposer.
// The Python driver admits one exact libpolyml binary before loading this.
// Simulate allocation-profiler events with a PC outside all ML code objects.
// No memory allocation is requested by this function.
#include <cstdint>

static_assert(sizeof(std::uintptr_t) == 8, "requires 64-bit PolyWords");
extern void addSynchronousCount(unsigned char *, std::uintptr_t);

extern "C" void task29_unknown_pc(std::uint64_t words,
                                  std::uint64_t events)
{
    for (std::uint64_t i = 0; i < events; ++i)
        addSynchronousCount(nullptr, words);
}
