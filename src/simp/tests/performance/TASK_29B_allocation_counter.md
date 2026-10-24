# TASK29B — supported cumulative HOL allocation measurement

## Context and dependency

Bounded prerequisite follow-up to TASK29, after TASK28. This follows the
existing `allocation_prerequisite` row, not a new exemption. TASK29 measured
reachable graph words, GC and approximate RSS/HWM. None is cumulative
allocation. Poly/ML 5.9.2's `sizeAllocation`/`sizeAllocationFree` fields report
allocation-area capacity/free space updated by GC, not an allocated-byte total.
Python `tracemalloc` negative controls do not measure HOL allocations.

## Executed profiler negative control

`ALLOCATION_PROFILER.md` and `evidence/task29/profiler-loss/receipt.json.gz`
now demonstrate loss in HOL's actual hash-pinned linked runtime. Injecting
one synthetic unknown-PC request of 1 or 1048576 words produces the same
`UNKNOWN=1`; seven large requests produce 7, including after full GC. Five
selftest/testutils assertions and eight Python guards pass. These are injected
profiler arguments, **not actual allocated words or an allocator instrument**.
The installed disassembly confirms that `incr` is discarded on this path.
A displayed-entry sum is therefore not a general cumulative allocator total.
This does not establish incidence in TASK29's workloads or validate all other
coverage paths. Required counter construction and the full allocation matrix
remain unsatisfied; this task is not complete.

## Experimental successful-reservation counter (not closure)

`allocator-counter/` now provides a fully source-pinned experimental patch,
private build driver and real HOL/testutils controls. Unlike the lossy profiler,
it counts successful native/RTS/interpreter/code reservations at their actual
commit sites, with separate categories, coherent C-buffer snapshots and sticky
overflow flags. Native checks deliberately trap on every allocation. It is a
separate runtime, never installed into the ordinary checkout.

The private eight-byte-word development run passed 34 brackets; the final
source-bound receipt is `evidence/task29/managed-counter/controls.json.gz`.
Read that receipt for its actual outcome and seals. Known native array/ref
slopes, RTS bignum multiplication, code-space allocation and retained-data GC
are exercised. The steady FFI no-op bracket allocates four native words; it is
not allocation-free and is not subtracted from arbitrary workload results.
Direct C ABI/no-allocation and separate synthetic concurrency/overflow tests
are distinct controls, not workload measurements.

This is not a supported full-matrix instrument yet. Actual interpreter/failure
paths, allocating ML worker retirement, slow-path coverage and prebuilt native
compiler/image lineage still need validation. Foreign-created-thread callbacks
are expressly excluded after source review found pre-existing initialization
defects; compact32 is untested. The entire 27-case/six-size paired allocation
matrix is still missing. No TASK29B completion or ordinary timing claim follows.

## Required input

A supported cumulative allocator counter or a reviewed, version-pinned Poly/ML
allocator instrument with documented semantics, units, overflow/thread/GC
accounting, and reproducible build/tool fingerprints. Authorization and a
compatible toolchain/runtime are needed for measurements on that instrumented
runtime; do not relabel the configured uninstrumented shared heap.

## Acceptance

- Validate the actual HOL counter with executed known allocation/no-allocation
  and GC controls. Allocation escaping to retained results must be consumed;
  distinguish code/heap and measured-operation versus process-startup costs.
- Make both baseline/candidate use the same sealed runtime/options/dependencies
  and bracket construction, complete operations and ordinary application
  separately. No production-source instrumentation or unsafe closure casts.
- Run every TASK29 fragment/compiler/storage case at 0/1/10/100/1000/10000,
  with baseline-baseline controls and at least ten paired fresh AB/BA process
  observations. Publish raw allocated bytes (or explicitly documented words),
  all adjacent allocation-per-rule slopes and size-zero constants.
- Per-rule and constant work must match or improve develop without hidden
  extension costs. Failure or uncertainty blocks TASK29; there is no regression
  allowance. Invalidate affected runtime/timing evidence rather than mixing
  instrumented and uninstrumented observations.

Independent lifetime and exact temporary-peak accounting remain TASK33; this
follow-up does not claim those gates or substitute a live-heap snapshot.
