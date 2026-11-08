# TASK15 fragment probes

New fixtures only; no production instrumentation or changes to older harnesses.
The runner imports `../compatibility/run_paired.py` for source extraction,
launcher installation, execution, protocol/footer/exit validation and complete
loaded-source/path auditing. `selftest.sml` uses its `testutils` reporter.
Both source selections elaborate from private `.sml`/`.sig` files in fresh
`hol.state0` processes with identical one-GC-thread launchers. Shared libraries
come from this repository; these are **not independent clean builds**.

From the repository root:

```sh
python3 -B -m unittest discover -s src/simp/tests/fragments -p 'test_*.py'
python3 -B src/simp/tests/fragments/run_fragments.py \
  --output /tmp/fragment-behavior
# Run only when builds and other benchmarks are idle:
python3 -B src/simp/tests/fragments/run_fragments.py \
  --performance-pairs 10 --samples 5 --seconds .2 \
  --output /tmp/fragment-performance
# Baseline/baseline variability control, with the same batch options:
python3 -B src/simp/tests/fragments/run_fragments.py \
  --candidate cccaa27d7099cbadc886983020cbe745db7793f3 \
  --performance-pairs 10 --samples 5 --seconds .2 \
  --output /tmp/fragment-control
```

Default baseline is the pinned develop commit. Default candidate `worktree`
seals a private snapshot of current simplifier sources, including new root/poly
modules, without building or modifying any production file. Use `--candidate
<commit>` for committed-source reproducibility. Worktree source drift, changed
shared products, harness inputs or tools fail the run. Output directories must
not exist. Temporary source/build trees are removed on success and failure;
keep selected compact receipts/manifest if useful, then remove scratch output.

## Matrix and consumption

At **0, 1, 10, 100, 1000, 10000** input rules/pairs:

- Anonymous/named rewrites, individually named rules, public `SSFRAG`.
- `ssf_upd_rewrs` reversing order, `add_named_rwt` adding one rule.
- Anonymous merge, duplicate merge, named merge and explicit name override.
- AC construction and duplicate AC merge (counts refer to AC pairs).
- `tyi_to_ssdata` and `type_ssfrag`; an isolated child's bool TypeBase info
  receives exactly the requested number of simplification rules outside timing.
  Both paths must preserve develop's reversed order and datatype fragment name.
  A public TypeBase update hook removes automatically added standard rules after
  `TypeBase.write`'s tweak stage, so lookup counts are exact even at zero.

Every result is inspected for its complete ordered list of theorem conclusions
**and hypothesis sets**, name and a compiled `SIMP_CONV` kernel proof. AC
results are exercised in the descending permutation direction. Duplicate
fragments are not silently deduplicated. Additional behavior checks cover empty
merge, callback count/exception identity, persistent input after update,
anonymous registration rejection, named registration/replacement, partition
order and duplicates, surviving rewrite names after update/merge, and missing
TypeBase.

Timing measures only construction/update/merge, not downstream rule compilation.
Results escape through a ref on every iteration; complete inspection and proof
application consume the final saved result after **every** calibration/sample,
outside the construction timer. The sink counts timed iterations exactly.
Input generation, TypeBase updates, full GCs and proof validation are untimed.
This keeps compiler costs from concealing fragment costs.
Both selections build before measurements start; paired process order alternates
AB/BA. By default calibration doubles until the requested wall duration is
reached, independently in each process (adaptive mode is unchanged).
CPU, non-GC CPU, GC CPU and wall remain distinct; inclusive CPU is not added to
GC again. `user_cpu` and `system_cpu` are separately reported **inclusive of
GC**, using non-GC plus GC user/system respectively. This separates system
costs such as page mapping from user computation. All metrics are seconds per
iteration; the eight original raw timer values remain unchanged and ordered:
wall, non-GC user, non-GC system, GC user, GC system, inclusive user, inclusive
system, GC user (the last is Poly/ML's `checkGCTime`). Reported paired ratios
use a median per process for every metric, never pool workloads. Raw batches
and calibration counts survive in compressed protocol receipts.

### Matched fixed iteration schedules

Use `--fixed-iterations /path/to/schedule.json` with `--performance-pairs` to
remove independently chosen batch sizes as a source of allocator asymmetry:

```sh
python3 -B src/simp/tests/fragments/run_fragments.py \
  --performance-pairs 10 --samples 5 \
  --fixed-iterations /tmp/schedule.json \
  --output /tmp/fragment-fixed
```

The JSON must be a complete object mapping **all 90** `label.n` keys to positive
integer counts: each of the 15 `LABELS` in `run_fragments.py` at each of the six
sizes above, e.g. `"ac_create.1000": 65536`. Missing, unknown or duplicate keys,
booleans, strings, fractional or nonpositive counts are rejected before output
creation. Choose one schedule before the run (for example from prior pilot
receipts); do not derive separate schedules for baseline and candidate.

The runner passes the identical schedule to every process as `PERF_FIXED`, a
comma-separated `label.n=count` list. In fixed mode the SML fixture performs
exactly **one calibration at that count**, then every sample uses the same
count, regardless of `--seconds`. It never doubles or independently chooses a
count. An absent `PERF_FIXED` selects the original adaptive mode; an empty or
partial value is invalid, not an adaptive fallback. The accounting control
still consumes five iterations independently of the schedule.

The manifest seals the original JSON file's absolute path, SHA-256 and byte
length in `inputs`, plus its parsed counts in `performance.fixed_iterations`
and path in `performance.fixed_iterations_path`. Input drift fails the run.
Each receipt also records the process environment. The Python validator checks
the scheduled calibration and every sample count, result consumption, timer
accounting, event order and total sink; extra calibrations are rejected.
Matched counts control batch-size asymmetry, not all process/allocator noise.

### Matched ambient-module diagnostic (not production evidence)

`--matched-environment` is an **opt-in attribution diagnostic**. It does not
change default extraction, production code or any default fast path. Ordinary
baseline `.sml`/`.sig` files are extracted unchanged from the selected commit.
Only missing files from this explicit current-worktree dependency closure are
supplemented: `TraverseExt`, `simpMarkerTheory`, `simpMarkerLib`,
`SplitData`, `splitLib`. Existing selected files are **never
replaced**, even if a helper's historical API is incompatible. Such an
incompatibility fails elaboration; there is no source transformation or fallback
to current ordinary sources. `simpExtLib` is not supplemented or loaded.

The dependency snapshot is captured once before either selection builds.
`simpMarkerTheory.sml`, `.sig` and required `.dat` are copied byte-for-byte from
existing current `.hol/objs` products; this is explicitly **not** regeneration
from pinned baseline sources. Other supplemented files are current root
sources. Required ordinary dependencies still use each selection's own files;
shared non-simplifier dependencies still come from this repository. Any future
missing extension closure must be explicitly reviewed and added to the list,
not discovered by blindly copying all current modules.

Only the private runner is adjusted: after `CheckSupport`, before the target,
it calls `Meta.loadPlan tracedUse` for each named module in the order above in
**both** selections. Private build prerequisites create each helper's `.uo`
dependency metadata, preventing fallback to shared simplifier paths. Explicit
input-only rules prevent Holmake regenerating the sealed theory products.
Dependency planning loads implementations once; the trace
validator requires each helper exactly once between support and target, and
rejects `simpExtLib`. Candidate dependencies already selected from the worktree
are not overwritten or elaborated a second time. This matches ambient loading
of extension helpers and the `simpMarker` theory/DB effects; it does not make
the two complete runtimes identical.

`--heap-mb N` independently sets identical `--minheap=N --maxheap=N` Poly/ML
runtime options in both private launchers (positive integer MB). Without it the
original launcher is unchanged. The manifest records `environment.heap_mb`,
each selection's exact `runtime_options`, launcher text and launcher seal.
All options precede `run`. Heap settings control one allocator variable, not
all allocator state or OS effects.

Example single pilot with a fixed schedule:

```sh
python3 -B src/simp/tests/fragments/run_fragments.py \
  --matched-environment --heap-mb 256 \
  --performance-pairs 1 --samples 3 --seconds .03 \
  --fixed-iterations /tmp/schedule.json \
  --require-baseline-graphs --output /tmp/matched-pilot
```

Audit provenance is separate: `selections.*.sources` remains the ordinary
selected inventory, `environment.supplement_snapshot` records current physical
source paths, snapshot paths, SHA-256, byte lengths and generated-product tags;
`selections.*.supplement_sources` lists only added private files with the same
provenance. Supplement source, snapshot and installed-file drift fail the run,
including theory data drift. Supplements are not mislabelled as pinned git
blobs or fixture products. Temporary snapshots are removed on all exits.

This mode is **not a pinned-baseline full-source production runtime** and
cannot establish that default overhead is fixed. Its purpose is to attribute
remaining default full-module ambient effects versus exact local fragment work.
Compiler dependencies/imports are not attributed here (see `../compiled-core`).
Compare individual CPU, non-GC, GC, user, system and wall rows against
unmodified-default observations; do not substitute matched timings for default
acceptance. One pair is only a pilot: report raw batches separately from the
median-per-process paired statistic, without a confidence/acceptance claim.
Matching modules and heap simultaneously also cannot distinguish their separate
causal contributions.

`Cond_rewrExt` is deliberately not preloaded: that helper needs
`Cond_rewr.is_var_perm`, absent from pinned `Cond_rewr.sig`, and the pinned
ordinary implementation is never replaced or transformed.
Consequently this is a **matched registry/context** diagnostic, not a claim
that the complete compiled-module environments match. Candidate's remaining
paired-compiler dependency is not attributed here (see `../compiled-core`).

## Allocation scope and decisions

The behavior fixture records incremental **reachable graph words**, subtracting
equal-arity roots that retain each workload's inputs, source fragments, callback
closures and static dependencies. It reports each count, the intercept delta,
and every adjacent finite-difference slope, not an average fitted slope. A fresh
ref/list positive control must measure five words per element on this Poly/ML.
These are allocation/storage probes of retained fragments, **not cumulative
transient allocation**, bytes, process RSS or compiled-simpset storage. Source
shape/allocation auditing remains necessary; no graph result proves absence of
short-lived allocations. No closure-layout casts or source-token inspection.

By default a successful runner exit means complete valid **observations**, not
a timing or allocation acceptance verdict. Add `--require-baseline-graphs` to
fail on any retained-word increase at any count, with no tolerance. This exact
graph gate is not a cumulative-allocation or timing acceptance gate.
The manifest exposes every graph delta and each
workload's timing ratios separately. It grants no fixed regression allowance,
no averaged score and no automatic pass for noise. Final acceptance still needs
source inspection, baseline/baseline variability, at least ten paired process
observations, confidence analysis, and independent builds under the plan.
Synthetic tests remove every required observation in turn and exercise wrong
counts, bad timers/sinks, allocation sensitivity, process failure, stale paths
and footer failure. Synthetic slowdown/allocation increases remain visible in
their individual output rows; they are not treated as production regressions.
