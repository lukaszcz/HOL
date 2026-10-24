# TASK29B — supported cumulative HOL allocation measurement

## Context and dependency

Bounded prerequisite follow-up to TASK29, after TASK28. This follows the
existing `allocation_prerequisite` row, not a new exemption. TASK29 measured
reachable graph words, GC and approximate RSS/HWM. None is cumulative
allocation. Poly/ML 5.9.2's `sizeAllocation`/`sizeAllocationFree` fields report
allocation-area capacity/free space updated by GC, not an allocated-byte total.
Python `tracemalloc` negative controls do not measure HOL allocations.

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
