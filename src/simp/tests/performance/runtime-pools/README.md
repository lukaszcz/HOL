# Actual runtime constant pools (diagnostic only)

`runtime_pools.cpp` is an `LD_PRELOAD` interposer for **Poly/ML 5.9.2,
Linux ELF, little-endian Arm64, full 64-bit ML words, native execution**.
It is not a portable runtime extension, timing probe, or heap-size correction.
It does not change the sealed `runtime_layout.py` format or old archives.

## Build and admission

From the repository root:

```sh
c++ -std=c++17 -O2 -fPIC -shared -Wall -Wextra -Werror \
  src/simp/tests/performance/runtime-pools/runtime_pools.cpp \
  -o /tmp/runtime_pools.so -ldl
LD_PRELOAD=/tmp/runtime_pools.so RUNTIME_POOLS_LIBRARY=/tmp/runtime_pools.so \
  /usr/local/bin/poly --script /tmp/selftest.sml
```

Preload into the actual process, not just a launcher that strips its
environment. Use the same absolute library path for `Foreign.loadLibrary`;
do not load another copy of the interposer or another `libpolyml`.

The diagnostic driver must bind these two no-argument, `void` C functions:

```sml
val library = Foreign.loadLibrary
  (valOf (OS.Process.getEnv "RUNTIME_POOLS_LIBRARY"))
val beginPools = Foreign.buildCall0
  (Foreign.getSymbol library "runtime_pools_begin", (), Foreign.cVoid)
val endPools = Foreign.buildCall0
  (Foreign.getSymbol library "runtime_pools_end", (), Foreign.cVoid)
```

After the workload has returned:

1. Write `@@RUNTIME_LAYOUT\tbegin\tArm64\t...\n` with ML TextIO and flush it.
2. Call `beginPools ()`.
3. Call the diagnostic `PolyML.showSize` on the chosen roots.
4. Call `endPools ()` (also flushes runtime `polyStdout`).
5. Write/flush the layout end marker.

One extent per process; repeated/nested begin or unmatched end aborts.
Use a single controlling ML task, with no concurrent `showSize` traversals.
The extent flag is process-wide because an ML task can migrate OS threads.
The controls do not discover TextIO markers: their placement is the driver's
responsibility. They never print admission themselves. An exception must
invalidate the capture, not synthesize a successful end marker.

On the **first actual ShowCode hook inside the active extent**, after the
unchanged original `CODE` record, the hook emits exactly once:

```text
@@RUNTIME_POOL\tloaded\tarm64-full64-v1
```

Here and below `\t` denotes an actual tab. Loading, unrelated ShowCode calls,
and an active extent without a code object do not emit this handshake.
A consumer must reject a missing/duplicate/out-of-extent handshake. Mere
presence of `LD_PRELOAD`, a successful `dlopen`, or `beginPools` is not proof
that ELF interposition actually happened.

## Records and ordering

The hook calls the original `ProcessVisitAddresses::ShowCode(this, owner)`
with unchanged arguments, then immediately writes to the **same runtime
`FILE *polyStdout`**, without redirecting, normalizing, buffering a separate
capture, or using raw file-descriptor output:

```text
@@RUNTIME_POOL\tbegin\t0xOWNER\t0xPOOL\tCOUNT\tinline|split
0x0000000000000001\t0x0123456789abcdef
@@RUNTIME_POOL\tend\t0xOWNER
```

`COUNT` is decimal. Exactly that many raw, full-width, lower-case hex words
follow, at most four per line, each with `0x` and 16 digits. Zero count means
no raw-word lines. Tagged integers, raw bits, and pointers are not interpreted.
The owner is the code data address, not its header or closure; pool is the
first constant word, not the preceding count/header. No truncation or
sampling. Both inline and split pools are emitted, even when inline words
already occur in the original CODE dump. Shared split pools can therefore
have multiple owners: records describe owner edges, not unique objects.

No hook-side managed allocation, ML callbacks, GC requests, FFI calls,
object mutation, names lookup, or dereferencing of constant entries occurs.
The original runtime function still does its ordinary work. Native loader
resolution and C stdio may use native allocations/locks; no claim is made
about generic FFI glue allocating before/after the traversal. This is
post-workload diagnostic evidence only.

## Exact source/ABI audit

Audited source input (read in place, not copied):

```text
/home/lukasz/.local/opt/Isabelle2025-2/contrib/polyml-5.9.2-2/src
```

Relevant source SHA-256 (`libpolyml/`):

```text
objsize.cpp
315bae531607c6d2e6c66bac4183e0aaae80db426f86d6eff33e06e6510dcc3c
arm64.cpp
0e677e650520a986c1bedc25fc103727c618a441c3d6149b871211d32e76da77
machine_dep.h
e36ee0a7c30630b9f408102b08c2bf094faf234537626d91e15d8012a33ad394
globals.h
5bf05d42dec9b2687864c2e85dc9e359a5fc162af213dd47e629253e258bdb43
process_env.cpp
c8e074cd341368a5adadc2e4b208c6a0fa4aae2de8173d4982a4107a4cb3c6a8
```

Exact dynamic symbols (no default base helper fallback):

```text
_ZN21ProcessVisitAddresses8ShowCodeEP10PolyObject
_ZNK14Arm64Dependent22GetConstSegmentForCodeEP10PolyObjectmRP8PolyWordRm
_ZN14Arm64Dependent19MachineArchitectureEv
machineDependent
polyStdout
PolyGetPolyVersionNumber
```

`machineDependent` is a **data symbol holding a MachineDependent pointer**
to the static `arm64Dependent` singleton. It is dereferenced once, not passed
as the singleton's address. The audited Arm64 class has one nonvirtual base;
the base singleton pointer is the correct `this` for the direct Arm64 helper.
There are no invented virtual classes, vtable slots, or guessed offsets into
the singleton/visitor.

AAPCS64 helper call: x0 = const singleton `this`, x1 = code data pointer,
x2 = unsigned-long word length, x3 = address of the pool-pointer output,
x4 = address of the unsigned-long count output. The exported mangling's `m`
means unsigned long. `PolyWord`, `POLYUNSIGNED`, pointers, and unsigned long
are eight bytes in this build. Code length is header at owner minus eight,
masked to its low 56 bits. The code type/tombstone bits and bounds are checked.

The **direct Arm64 helper** handles both real encodings: a trailer whose top
byte is `ff` holds a negative byte offset to inline constants; otherwise dummy
ADRP/LDR instructions encode a split pool. Inline count is the raw preceding
word; split count is the separate object's masked length. The hook delegates
decoding to the runtime helper and checks the result, rather than using the
default `MachineDependent::GetConstSegmentForCode` or reimplementing
relocation.

All resolved symbols must belong to one DSO. Admission checks the direct
no-allocation version result `TAGGED(592)` and direct architecture result
`MA_Arm64 == 4` (not interpreted or `MA_Arm64_32 == 5`). Compilation rejects
non-Linux, non-Arm64, big-endian, and non-LP64 targets. This is an ABI-specific
adapter, not a memory-safe decoder for hostile pointers or a proof that every
custom DSO calling itself 5.9.2 has identical internals. Seal the actual
executable, runtime DSO, interposer and capture in the diagnostic receipt.

## Smoke test

Tested with ordinary `/usr/local/bin/poly --script selftest.sml`,
not a patched runtime or `bin/hol`.

The installed runtime's disassembly agrees with the audited helper's
full-64 loads, `ff` test, ADRP/LDR decoder call, and 56-bit split length mask.
This is not a claim that the installed DSO's entire build source is sealed
by the source hashes above.

Smoke input, saved as `selftest.sml`:

```sml
val _ = let
  val _ = if PolyML.architecture () = "Arm64" then ()
          else raise Fail "requires native Arm64 full64"
  val lib = Foreign.loadLibrary
    (valOf (OS.Process.getEnv "RUNTIME_POOLS_LIBRARY"))
  val beginPools = Foreign.buildCall0
    (Foreign.getSymbol lib "runtime_pools_begin", (), Foreign.cVoid)
  val endPools = Foreign.buildCall0
    (Foreign.getSymbol lib "runtime_pools_end", (), Foreign.cVoid)
  fun candidate x = x * 37 + 19
  fun marker text = (print text; TextIO.flushOut TextIO.stdOut)
  val _ = marker "OUTSIDE_BEFORE\n"
  val _ = PolyML.showSize candidate
  val _ = marker
    "@@RUNTIME_LAYOUT\tbegin\tArm64\trun,step,measured,experiment\n"
  val _ = beginPools ()
  val words = PolyML.showSize (candidate, Int.toString)
  val _ = endPools ()
  val _ = marker ("@@RUNTIME_LAYOUT\tend\t" ^ Int.toString words ^ "\n")
  val _ = marker "OUTSIDE_AFTER\n"
  val _ = PolyML.showSize candidate
in marker "SMOKE_OK\n" end;
```

Expected: exit 0, empty stderr and `SMOKE_OK`, with every pool record, the
single handshake and the owning CODE records inside the extent, exact word
counts and full-width hex, and inline words matching their offsets in that
CODE. Keeping all calls in one ML phrase avoids intervening compiler GCs that
can legitimately relocate pointer-valued constants between snapshots.

Negative controls exit 0 with empty stderr and **no pool markers**:
(1) the same script with both extent-control calls replaced by `()`;
(2) an active extent calling `PolyML.showSize 7` instead of the function pair.

Limitations: admission does not prove traversal completeness, root identity,
absence of concurrent mutations, temporal measurement-boundary identity,
or that a static pool entry was used during execution. A layout consumer
must validate those separate protocol claims and fail closed on malformed,
aborted, duplicate, or unadmitted captures.
