# TASK16 compiled core

`run_core.py` uses the maintained `run_paired` launcher/validator and
`run_fragments.snapshot`; neither maintained runner is modified. Both sides
elaborate selected sources in fresh processes from `hol.state0`, private-first
search paths. Baseline is always `cccaa27d7099cbadc886983020cbe745db7793f3`.
Candidate defaults to the working sources, including uncommitted changes.
These are isolated-source comparisons, **not independent repository builds**.
The manifest records whether simpLib.sml/.sig match the pinned bytes.

Behavior/graph only (safe before timing is appropriate):

```
python3 -B src/simp/tests/compiled-core/test_core.py
python3 -B src/simp/tests/compiled-core/run_core.py \
  --output src/simp/tests/compiled-core/evidence/behavior
python3 -B src/simp/tests/compiled-core/run_core.py --baseline-control \
  --output src/simp/tests/compiled-core/evidence/control
```

Every output directory must be new; failures retain complete compressed
receipts. Temporary source trees are automatically removed. Existing source,
heap, dependency-product and runner inputs are fingerprinted and rechecked;
concurrent rebuilds/source edits can correctly invalidate a run.

## Coverage

* CoreGraph: 0, 1, 10, 100, 1000, 10000 distinct constant rewrites; first/last
  exact conclusions **and hypotheses** through compile, merge, and projection.
  Equal-arity anchored object graphs report fragment, incremental compiled
  simpset, merged fragment and projection words. Fresh cons/ref cells establish
  the expected 5 words/input sensitivity. Adjacent slopes and paired word
  differences are in the manifest; `--require-baseline-graphs` disallows any
  increase (no tolerance). This measures retained graphs, not total allocation,
  RSS, or standalone heap size. Inputs/static closures are subtracted.
* CoreBehavior: maker-expanded source-name suffixes and qualified deletion,
  persistent originals, shared bounded allowance across uses/recompilation,
  empty history,
  limit/unlimit, exact paired simpset rendering, direct/fragment/merged
  relational simplification, TypeBase data and lookup compilation.
* Unchanged maintained fragment Routes fixture: makers/conversion/collector
  ordering, AC, malformed tags, exclusions/force-add, duplicate history,
  exception identities, exact full fragment printing and proof hypotheses.
* Unchanged PriorLimits fixture: spent allowance rollback and failed solvers.

Exact ordered behavior is compared between sides, including printer bytes.
Graph words may differ, but arithmetic/order/sensitivity are strictly checked.
No production instrumentation or extension APIs are used.

## Timing: run ONLY after all main builds cease

Do not run these two commands concurrently with each other or with builds:

```
python3 -B src/simp/tests/compiled-core/run_core.py --performance-pairs 10 \
  --samples 3 --batch-seconds .2 --timeout 1200 \
  --output src/simp/tests/compiled-core/evidence/timing
python3 -B src/simp/tests/compiled-core/run_core.py --baseline-control \
  --performance-pairs 10 --samples 3 --batch-seconds .2 --timeout 1200 \
  --output src/simp/tests/compiled-core/evidence/timing-control
```

Reuses unmodified `performance/Performance.sml` (1000 rules),
`performance_schema.validate` and `performance/summarize.py`. Each workload
calibrates doubling batches, verifies/consumes results, then takes >=3 samples;
10 AB/BA alternating fresh-process pairs, no discarded outliers. Workloads
include fragment creation/merge, compilation, projection, stored application,
and compile+application. Full CPU, wall, nongc user/system and GC user/system
are separately retained (GC is **not** added twice). `performance-summary.json`
contains paired CPU/wall/GC ratios and bootstrap intervals;
`nongc_seconds_per_operation_by_pair` in the manifest supplies separate nongc
process medians. Recompute the maintained summary with:

```
python3 -B src/simp/tests/performance/summarize.py \
  src/simp/tests/compiled-core/evidence/timing \
  --output src/simp/tests/compiled-core/evidence/timing/recomputed.json
```

Timing is diagnostic, not an acceptance claim; the 10000-rule graph closes the
storage slope, not a claim of 10000-rule timing coverage. Baseline controls
quantify noise; graph baseline controls require exact zero paired differences.
