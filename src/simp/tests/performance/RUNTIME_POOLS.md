# TASK29 complete post-workload constant pools (diagnostic only)

`runtime_pools.py` closes the **pool-slot instrumentation omission**, not
TASK29A. It leaves `runtime_layout.py` and its sealed v1 archives unchanged.
No production simplifier, ordinary fixture or numerical policy is changed.

## Collection

Using the configured-root wrapper W described in `README.md`, choose new
output directories:

```sh
W python3 -B src/simp/tests/performance/runtime_pools.py \
  --candidate FULL_COMMIT --case frag_record --size 0 \
  --batch-iterations 33554432 --authorize-diagnostic --output NEW_DIRECTORY
W python3 -B src/simp/tests/performance/runtime_pools.py \
  --candidate FULL_COMMIT --case compile_collector --size 10000 \
  --batch-iterations 64 --authorize-diagnostic --output OTHER_DIRECTORY
python3 -B src/simp/tests/performance/runtime_pools.py --replay NEW_DIRECTORY
```

Each experiment retains one fresh B/B and B/C structural pair. The paired
runner's ordinary environment sanitization is unchanged. A scoped wrapper
adds an exact private `LD_PRELOAD` only to its diagnostic Performance
processes; no builds, compatibility processes or ordinary timing tool receive
it. Native code is built with the recorded command and copied identically
into both private selections. Source, compiler, binary, fixtures, runtime
libraries, actual added environment, raw output and receipts are sealed.

After the unchanged workload returns, a separate top-level declaration loads
`RuntimePools.sml`. FFI setup occurs before the layout marker, then the
postlude enables the hook around `PolyML.showSize` of the actual four roots.
The native hook prints the original CODE record unchanged, then its complete
inline or split constant pool through the same runtime `FILE*`. It neither
mutates objects nor requests ML allocation/collection. Native resolution and
stdio can allocate. See `runtime-pools/README.md` for the audited, deliberately
nonportable ABI and extent controls.

**Preloading itself changes the diagnostic process.** Postlude compilation,
FFI and traversal can allocate or move objects. Neither these times nor these
addresses can enter numerical acceptance or identify earlier timed targets.

## Admission and comparison

The parser requires one actual-hook handshake inside the traced post-workload
extent and exactly one immediately ordered pool record per completed CODE
record. Counts, raw full-width slots, owner, ending owner and pool addresses
are checked. Inline slots must match the independently printed CODE bytes;
split addresses must match the independently decoded dummy Arm64 trailer.
Shared pools must have consistent contents. A split pool already in the
object inventory must match that object. Missing, truncated, empty,
duplicate, wrong-owner and unadmitted pools reject, not compare equal.

The split trailer is metadata, not executed instructions; it is excluded from
native reference scanning. Adjacent ADRP/LDR64 loads resolve only inside that
owner's validated pool. Signed pages, alignment, base registers and XZR/SP
semantics are checked. Non-address data may still contain instruction-looking
bits. Raw words and every unresolved reference remain available.

Root/slot-anchored graph traversal reports paths to mismatches and preserves
object and pool-owner alias correspondence. It does not pair objects by name
or conceal pool permutation. Native-word differences, raw slot differences,
unresolved addresses and unmatched objects are distinct observations.

The original `showSize` total still counts only its printed objects. Unique
split-pool storage (including headers) and storage already printed through
other graph edges are reported **separately**, never silently added to that
total or presented as cumulative allocation/process memory.

Replay checks the exact input inventory, Git source bytes, loader/postlude,
native build recipe/output receipt, binary and fixture fingerprints, actual
preload environment, B/B roles, source/proof/runtime admission, raw capture
transport and every derived comparison. These are consistency checks of a
trusted producer, not authentication of a maliciously rewritten archive or
proof of installed-runtime build lineage.

## Tests and retained evidence

```sh
python3 -B -m unittest discover -s src/simp/tests/performance \
  -p test_runtime_pools.py -v
RUNTIME_POOLS_NATIVE=1 python3 -B -m unittest discover \
  -s src/simp/tests/performance -p test_runtime_pools.py -v
RUNTIME_POOLS_EVIDENCE=UNPACKED_DIRECTORY RUNTIME_POOLS_NATIVE=1 \
  python3 -B -m unittest discover -s src/simp/tests/performance \
  -p test_runtime_pools.py -v
python3 -B src/simp/tests/performance/evidence/task29/runtime-pools/replay.py
```

The native control executes ordinary Poly/ML, not a patched runtime or an
SML pipe into HOL. Positive inline/split capture and absent-extent,
non-code-root and absent-preload negative controls are executable. Real
archive mutations cover source, loader, postlude, interposer, actual preload,
build recipe/output, proof, inventory and comparisons. Rejected diagnostic
output **and its process receipt** are retained; hooks restore on failure.
The distinct `runtime-pools-diagnostic` suite is rejected by timing admission.

`evidence/task29/runtime-pools/RESULTS.md` describes all eight final processes,
the retained development experiment, raw operands and unresolved acceptance.

## Environment diagnostic, not an exclusivity certificate

```sh
python3 -B src/simp/tests/performance/measurement_environment.py \
  --output NEW_ENVIRONMENT.json
```

This read-only two-second observation retains visible cgroups, counters,
limits, namespace/capability/affinity information, load and storage. Ancestor
CPU deltas subtract the enclosing session scope, not merely this Python
process; overlapping ancestors are never summed. Missing/regressing counters
are not treated as quiet. Its status is always `exclusive_not_verified`:
quiet observations cannot prove host exclusivity, and this sandbox cannot
reserve or see the whole host. The retained sample observes concurrent work.

## Still required for TASK29A

Complete ordinary-process measurement-boundary and executed-target/causal
attribution, a justified compatible repair if needed, an exclusive stable
measurement environment, the entire fresh passing 162-cell repaired-driver
grid with admissible controls, and explicit zero-GC/B/B policy-owner
disposition. None is replaced by supplying static pool slots. Historical and
repaired-driver timing failures/uncertainty remain unchanged; TASK29B remains
separate. No host-noise hypothesis, waiver or completion is claimed.

Amendment (2026-11-05): the exclusivity requirement was waived by the
policy owner; the host is shared. "An exclusive stable measurement
environment" above is no longer required.
