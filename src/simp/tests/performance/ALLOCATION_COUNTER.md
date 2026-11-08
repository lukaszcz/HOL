# Cumulative HOL allocation: counter and paired matrix

## Why a counter

Reachable graph words, GC counts and approximate RSS/HWM are not cumulative
allocation. Poly/ML 5.9.2's `sizeAllocation`/`sizeAllocationFree` fields
report allocation-area capacity/free space updated by GC, not an
allocated-byte total, and Python `tracemalloc` does not measure HOL
allocations.

## The allocation profiler is not a counter

`ALLOCATION_PROFILER.md` and `make profiler-loss-control` describe a negative
control run against HOL's actual hash-pinned linked runtime. A synthetic
unknown-PC request of any size lands in a single `UNKNOWN` count of one per
event: the installed disassembly shows the `incr` argument discarded on that
path. A displayed-entry sum is therefore not a cumulative allocator total. The
control injects profiler arguments; it neither allocates the requested memory
nor is an allocator instrument, and it says nothing about how often the
measured workloads reach that path.

## Experimental successful-reservation counter (not closure)

`allocator-counter/` provides a source-pinned experimental patch, a private
build driver and real HOL/testutils controls. Unlike the profiler, it counts
successful native, RTS, interpreter and code reservations at their commit
sites, in separate categories, with coherent C-buffer snapshots and sticky
overflow flags. Native checks deliberately trap on every allocation. It is a
separate runtime, never installed into the ordinary checkout.
`allocator-counter/README.md` says how to run it; the receipt of a run, not
this text, is the evidence of what executed.

One driver run (`run_controls.py --authorize-experimental-runtime
--bootstrap-hol`) requires a clean, committed harness checkout that differs
from the reference revision only below `src/simp/tests/performance`. It builds
a native Poly/ML and HOL from sealed source at that head, builds the patched
runtime and executes **233 brackets** in seven launcher processes. Each
process has a finite process-group timeout, merged stderr, a strict schema
and a check of the actual mapped runtime. The launchers are:

- counter (34): known native word/byte arrays, escaping ref lists, RTS bignum
  multiplication, code allocation through the compiler, retained-data GC and
  no-op FFI repeats with exact slopes.
- worker (22): four precreated ML workers, exact aggregate slopes and actual
  retirement.
- interpreter (47): source-bootstrapped bytecode compiler and basis; 31 small
  controls and 16 retained-ref/array controls whose fast and slow bytecode
  successes both execute and sum to the original interpreter category.
- failure (35): native reservation failures under a verified `RLIMIT_AS`
  (`--maxheap` alone permits oversized objects), comparison with a prebuilt
  interrupt, and exact recovery.
- path (22): native and RTS loops that take the refill and success-after-GC
  branches of `Processes::FindAllocationSpace` (and, for RTS only, the
  large-object area), observed by a third diagnostic ABI; the retries leave
  the exact raw slopes unchanged.
- interpreter-path (33): the refill and success-after-GC branches for
  bytecode allocations, plus interpreter reservation failures under
  `RLIMIT_AS` with the exhaustion line, one failure counter, no charge and
  exact recovery.
- failure-path (40): RTS and native reservation failures under `RLIMIT_AS`
  and code-space failures (a request larger than the reserved AArch64 code
  region). Failed requests are uncounted; recovery is by exact RTS and native
  slopes and by unchanged compiler raw vectors. A failed code request is
  compared with a control raising a same-size exception packet through the
  same runtime call, which asks for no code space.

Semantics of the path counters. The native and bytecode callers pass
`alwaysInSeg`, so the large-object-area cells of those callers are asserted
zero; only RTS requests can reach that branch. The after-GC cells count a
retry after this call's `QuickGC` succeeded or after it waited for another
thread's pending GC request. The code-failure control proves exactly one
failed `MemMgr::AllocCodeSpace` per failed attempt; it does not prove that
a code request succeeds after a GC. A counter in the path ABI counts entries
of a thread the runtime did not create into `PolyArm64GetThreadData` and must
be zero at every endpoint; the matrix fixture reads it once more at process
end.

`arithmetic_test.cpp` executes synthetic overflow and concurrency arithmetic
for all three snapshot ABIs, and death tests of the abort on an unidentified
caller or invalid kind and outcome; none of these are allocated HOL words. The
steady FFI no-op bracket allocates four native words and a native-bracketed
interpreted entry 31; neither is subtracted from workload results.

Pre-existing runtime behaviours that shape the controls (not counter
defects): an exception raised by bytecode cannot propagate to native frames,
so the interpreted failure controls catch the Interrupt inside interpreted
code; and the AArch64 code area is a reserved 2 GiB region that `RLIMIT_AS`
cannot fail, so the code-space failure uses an oversized uncleared byte
vector.

Out of scope, by decision rather than remaining work: compact32 (the driver
refuses such a configuration) and callbacks from threads not created by the
runtime. The sealed shim may import only allowlisted symbols (so no thread
or process creation), each path launcher records the OS thread
inventory before and after, and the foreign-thread counter must stay zero.
Arbitrary prebuilt native compilers and images are not validated; the driver
builds its own.

The harness head and the build lineage are recorded in the receipt, not
pinned in the repository.

This is not a supported full-matrix instrument: the paired allocation matrix
below needs a controls receipt of this driver and a full run. No ordinary
timing claim follows from the controls alone.

## MATRIX: paired allocation matrix method

Method only; this section records no result. Evidence is never committed:
`allocation_matrix.py` writes everything below `--output`, which has no
default and is chosen by the caller outside the repository.

- **Lineage.** `allocation_matrix.py toolchain` builds, once, a source-built
  native Poly/ML (the stock sealed source, no counter) that compiles HOL at the
  candidate commit. Its `lineage.json` is written only when the whole build
  succeeded and carries `success: true`; a failed build leaves
  `lineage-failed.json`, which is never read back. `run` requires a successful
  toolchain at the candidate commit (and a candidate different from the
  baseline), builds the patched runtime with
  `allocator-counter/private_runtime.py` (shared with `run_controls.py`), and
  swaps only the DSO: `LD_LIBRARY_PATH` names the patched `libpolyml.so.16`;
  `ldd`, the symbol's `dladdr` and the process maps must all name exactly that
  library. Baseline and candidate share the heap, options and dependencies.
  Compact32 is rejected at configuration and by the snapshot word-size field.
- **Isolated-source boundary.** Only `src/simp/src` differs between the two
  sides of a cell. Everything else a matrix process loads (the HOL heap
  `bin/hol.state0`, the libraries `sigobj` gives the fixture, the fixtures)
  comes from the one toolchain built at the candidate and is shared, so a
  baseline..candidate difference outside `src/simp/src` would change both
  sides alike and be invisible. The run therefore refuses, before any
  build, every differing path that the reviewed manifest
  `allocation_boundary.json` does not cover (`allocation_boundary.py`). The
  manifest has two kinds of entry only: a directory prefix, which may not
  contain or lie inside any directory the sequence
  `tools/sequences/upto-parallel` builds (without `-t`) up to and including
  `src/simp/src`, nor `tools/`, `tools-poly/` or `bin/` (computed from the
  candidate's own sequence files); and an exact file with its candidate git
  blob, for anything else, so a changed file demands a new review. The walk
  ends at `src/simp/src`, a constant of the module and not a manifest value:
  whatever the subject loads is built before it, so the bound is structural
  and covers what is loaded after the heap (`src/marker`, `src/combin`,
  `src/compute/src`, ...) as well as the heap's own inputs. The module
  also requires that `src/proofman`, which deposits `bin/hol.state0`, is
  built at or before `src/simp/src`. A prefix is a claim that no process
  loads from it, and each process checks that claim: a shared file whose
  logical path (the name it was loaded by, normalized), physical path or
  related product (`.uo`, `.ui`, `.dat`) lies under a manifest prefix
  rejects the process, at run time and on replay. All of them must lie
  inside the toolchain; one outside it is refused, not taken to be under no
  prefix. The
  fixtures are not exempt because they are not shared: they are loaded from
  the private directories, bound to their candidate blobs by the harness. The
  resolved boundary (changed files per entry, the list of manifest prefixes,
  the digest of all changed paths, the manifest digest) is recorded in the
  inventory and checked on resume. `subject_changed` counts all changed files
  below `src/simp/src`, among them files no process loads (`Holmakefile`,
  `MANIFEST`, `notes.md`). The manifest is a reviewed input of the driver,
  not evidence.
- **Harness.** The checkout the driver runs from must be clean (the top-level
  `.agent-files/` directory, which holds the serial lock a fresh clone
  creates before the check and is agent state by repository convention, is
  the one thing ignored), equal to the
  candidate outside `src/simp/tests/performance`, and every harness file (the
  driver and helpers, the boundary manifest, the iteration counts, the
  allocator-counter sources, `run_paired.py` and the paired fixtures) must
  be its committed blob. The fixtures installed in every private directory
  must be the candidate's own committed blobs: a fixture changed after the
  candidate commit is refused, not sealed as given. The harness head, tree
  and blobs are part of the grid digest.
- **Controls receipt.** `run` and `check-jobs` require
  `--controls-receipt PATH`, a successful `task29-managed-counter-controls`
  receipt (`.json` or `.json.gz`) from `allocator-counter/run_controls.py`
  whose runtime seal (sha256 and bytes) equals this grid's own private DSO.
  Every harness input of the receipt (the allocator-counter directory and
  the performance files that decide the controls) must be sealed in the
  receipt exactly as in this checkout; its instrumented libraries (by name
  and seal) and native Poly/ML configuration must equal this matrix
  toolchain's; and its three path-launcher process receipts are validated
  again by the current `path_schema`, so a receipt of the same patch and
  tree made under weaker path checks is refused. The receipt must record a
  clean,
  committed harness whose head is the receipt's head and whose tree outside
  `src/simp/tests/performance` equals the candidate's, and the HOL and
  native build lineage of that head. Any missing field or seal difference is
  a rejection, never a weaker check. The receipt is copied into the output
  (`controls-receipt.json[.gz]`) and `replay` re-verifies the copy from the
  archives alone: its seal, its runtime against the grid's, and every fact
  the inventory recorded. The runtime build is deterministic, so a receipt
  produced by `run_controls.py` from the same sources and toolchain matches.
- **Toolchain seals.** Besides the HOL and native products, the tracked HOL
  sources as the build left them and `sigobj` are sealed by the toolchain
  lineage (`hol_source_inputs`, `hol_source_changes`, `hol_sigobj`), must be
  those of the candidate snapshot, are checked at the start and sealed again
  at the end. A lineage without these records is refused: rebuild the
  toolchain.
- **Fixture.** `MatrixAllocation.sml`, installed as `Performance.sml`, reuses
  `MatrixSupport.sml` unchanged, one case and size per fresh process. Each
  bracket is its own record: `startup` (counter value at the first probe,
  i.e. process load; published, not gated), `empty` (no-op; published, never
  subtracted), `canary` (an array of known length; published), `setup`
  (`workload label size`), `operation_first`, `operation_steady` (a fixed
  batch of `run ()`, repeated at least three times) and `apply` (`verify ()`,
  which consumes the retained result). `fullGC` and the
  `beforeBatch`/`afterBatch` assertions are outside brackets; FFI closures
  are built before and endpoints decoded after. Counts come from
  `allocation_iterations.json`, identical for both sides, never calibrated.
  Two consequences of reusing `MatrixSupport.sml` unchanged are part of the
  method. The workload builders run `build ()` once inside `setup`, so
  `operation_first` is the second execution of the operation in the process
  (the name is kept). And `setup` nets the builder's allocation within that
  one phase; it cannot be split further while `MatrixSupport.sml` stays
  unchanged.
- **Startup.** `startup` is published for baseline, candidate and control, and
  the candidate-minus-baseline and control-minus-baseline differences are
  published per pair, but it is not gated: work moved into module load is
  caught by the lifetime and peak accounting, not here. All three selections
  use equal-length labels and directory names so that the label cannot change
  the startup words.
- **Canary.** The parser requires the `canary` bracket to cost exactly the
  known words per category beyond the no-op `empty` bracket, and a nonzero
  `startup` total. A dead or under-reporting counter therefore rejects every
  process instead of passing with all-zero deltas. The foreign-thread counter
  and the reserved path word, read after the last bracket, must both be zero.
- **Metrics.** Raw endpoints and overflow masks per bracket, then deltas of
  total, native, rts, interpreter, code and heap (total minus code) in words,
  and the same distinct values in bytes (words times the snapshot's word-byte
  field, with checked arithmetic), both published per gated and published
  row. A nonzero overflow mask, a non-monotonic endpoint, a malformed field,
  a missing or duplicated bracket or a wrong case/size/count binding rejects
  the process (kept with its reason), never aborts the run. The code category
  stays visible and is listed whenever nonzero.
- **Decision, no allowance.** Per cell, phase and metric: if the baseline is
  not exactly identical (repeat by repeat, across all processes) over the
  baselines of the candidate pairs together with both sides of the
  baseline/baseline control pairs, the result is inconclusive; otherwise pass
  iff every paired candidate-minus-baseline difference is <= 0, else fail.
  Steady repeats that differ from each other but reproduce in every process
  are deterministic; a repeat that differs between processes is listed as
  nondeterminism and downgrades an otherwise passing grid to inconclusive.
  Adjacent per-rule slopes are exact rationals (steady batches are
  normalized per `run ()`), computed for both sides across all processes,
  and the size-zero constants are published; both follow the same rule. An
  improvement that exists at one size only therefore fails on the adjacent
  slope that crosses it: that follows from the rule and is not an error.
  Nothing is thresholded, removed or subtracted. A definite fail is reported
  as fail even when the grid is incomplete; a pass needs every cell and
  slope, at least ten pairs, no unresolved cell and no nondeterminism.
- **Replay.** Every archived process is replayed offline: the protocol
  (loader header, preloaded modules, heap files, search paths, completed
  `use` inventory, fixture completion, and the elaboration of the selected
  `Traverse.sml` and `simpLib.sml` in every process), the exact whole
  environment (not a filtered subset: every variable and its value), the
  selected sources and fixtures against the sealed inventory, shared inputs
  inside the toolchain and identical across all cells, AB/BA order, and the
  case, size, steady count, revisions and grid digest against the run's
  manifest. A replay failure of one cell rejects that cell (kept with its
  reason, status unresolved); it never aborts the run.
  Resuming refuses any change of a shared input, including the driver files,
  the toolchain products and sources, the environment, the boundary and the
  harness, and re-replays the kept cells first. The driver files are keyed
  by path relative to the harness checkout, so the same commit checked out
  elsewhere resumes. Every process runs under the one `PATH` constant of
  `allocator-counter/private_runtime.py` (`/usr/local/bin:/usr/bin:/bin`),
  not the caller's: the entry points of the matrix driver and of
  `run_controls.py` make it `os.environ["PATH"]` before anything else, so
  `git` (which extracts the measured sources) and every other subprocess
  resolve their programs there. The compilers and build tools it resolves to
  (`gcc`, `g++`, `make`, `ldd`, `nm`, `ld`, `as`, `git`, and the compiler
  programs behind the drivers) are sealed with the other tools.
  What a resume ignores is only where things stand (`PLACE_KEYS`:
  `shim_path`, `library` and `aliases` of this session's private runtime and
  shim, and `tmpdir`): each kept cell records the places it was measured at
  and is replayed against them, while the contents (the runtime and shim
  seals, the libraries and tools by seal) stay in the grid digest. `TMPDIR`
  is a place because the runtime reads it to choose where the backing file
  of its memory mappings lives (`tools-poly/poly/Mosml.sml` reads it too, to
  name temporary files), and the counter counts requested reservations, not
  where they are backed. A place has a length, though. The scratch tree
  stands below `TMPDIR`, so `PAIR_PRIVATE`, `LD_LIBRARY_PATH` and
  `TASK29_ALLOC_SHIM` change length with it, and path length can change
  startup words (hence the equal-length selection labels). A resume under a
  `TMPDIR` of another length would give cells of one grid private paths of
  different lengths, and published startup could differ between cells. A
  resume therefore requires `len(tmpdir)` equal, and the length of the
  resolved private runtime path too, which a symlinked `TMPDIR` can change
  alone; the final replay refuses cells recorded at lengths that differ. The
  reason this holds is that no gated bracket (the 27 cases of
  `task29_gate.CASES` and the 24 cases of `task30_cases.CASES`) reads an
  environment variable or a path. The one call that would is `new_theory` in
  the `history_theory_change` case of `MatrixSupport.sml`: in a `hol run`
  process (`Globals.interactive` is false) it exports the current theory,
  which writes the `*Theory` files below the working directory (the sealed
  private selection, which must not change during a cell) and builds
  documentation paths (`parent_doc_url`) from it, and its export has words
  that depend on the clock and on the process id. The allocation fixture
  therefore makes no transition there: `MatrixAllocation.sml` sets
  `MatrixSupport.theoryChange` to a no-op, and the reparse the case verifies
  comes from the `Context.restore` that drops the theory the case linked
  (`filter_net_by_names` then raises "bad theory name"). The timing gate
  keeps the real `new_theory`, in setup and outside any batch. The rest of
  the environment is content, `HOLDIR` included: it names the toolchain,
  which `--toolchain` identifies by path and whose products are sealed by
  that path. A changed `PATH`, compiler path or toolchain is a different
  grid.
- **Acceptance baseline.** `decisions.json` records `acceptance_baseline`,
  true only when the `--baseline` of the run is the pinned develop commit of
  `acceptance.py`; any other baseline is measured and published, a definite
  fail is still a fail, but a pass is reported as inconclusive.
- **Candidate startup.** The startup words of the candidate are published by
  the startup bracket and deliberately not gated here; the lifetime and peak
  accounting own them.
- **Concurrency.** Counting is not timing, so cells run in parallel
  (`--jobs`, default 8) while the whole run holds the serial lock; each worker
  has its own private selection directories, a pair keeps its AB/BA order, and
  every observation is a fresh process. An error or interrupt cancels queued
  cells. Parallelism changing any count is a defect: the control divergence
  rule would expose it, and `check-jobs` compares serial against parallel raw
  counts directly over at least two distinct cells, failing unless the
  parallel run really used several workers.
- **End seals.** At the end of a clean run the inputs, tools (including the
  heap, project file, compiler products and every library), extracted
  sources, the private DSO, the shim and the `ldd` linkage of both are
  sealed again; any drift fails the run.
- **Commands.** `run` (with `--resume`, `--only`, exclusive-create output,
  per-cell lossless archives verified before scratch is removed, and the
  private build commands persisted in `build-N.json.gz`), `replay`
  (recomputes every decision from the archives alone),
  `check-jobs` and `toolchain`. `python3 -B -m unittest discover -s
  src/simp/tests/performance -p 'test_allocation_*.py'` runs the negative
  controls over synthetic fixtures; no runtime, toolchain or receipt is
  needed.
