# TASK16 compiled core: bounded acceptance evidence

Runtime: Linux/aarch64, Poly/ML 5.9.2, one GC thread. Pinned develop:
`cccaa27d7099cbadc886983020cbe745db7793f3`. Both ordinary compiler files
are byte-identical to this pin; extension compilation remains unchanged.
These are isolated-source comparisons sharing sealed dependencies/hol.state0,
not independent repository builds or final whole-plan performance acceptance.

## Behavior, import and storage gates

Each final experiment executes 20 focused behavior/proof checks, 41 reused
route checks, six reused limit checks and 36 graph checks **per selection**.
The ordered route events match exactly, including decode-all-tags -> AC ->
all makers -> conversions -> existing collectors, foreign exception identity,
malformed tags, empty/excluded additions, history, registration and printing.
The focused supplement covers shared persistent bounds, named conjuncts,
limits, relsimp and TypeBase compilation and complete proof hypotheses.
`CoreBehavior` also loads ordinary simpLib, boolSimps and congLib in a fresh
process and rejects loaded/bound extension engines, marker theory/services,
split stores or persistence modules. It uses no extension preload.

Every retained graph point **and every adjacent slope** is no larger than
develop. Equal-arity roots retain the shared base and input fragment once.
Compiled incremental retained words (identical in both final current runs):

| Rules | Develop | Restored ordinary core |
| ---: | ---: | ---: |
| 0 | 21 | 21 |
| 1 | 3305 | 3305 |
| 10 | 4023 | 4014 |
| 100 | 11205 | 11106 |
| 1000 | 83071 | 82072 |
| 10000 | 801752 | 791753 |

Last adjacent compiled slope: **79.853444 vs 78.853444 words/rule**.
Fragment growth is exactly six words/rule; retained merge results are exactly
baseline. Projection increments improve by one/two words. The five-words-per-
cell sensitivity control is exact. Baseline-versus-baseline differences are
zero for every graph point and slope. These are reachable graph words, not
cumulative allocation, byte counts or RSS. The one-word/rule improvement is
consistent with TASK12's measured removal of the tracking-key closure capture;
it is not attributed to a new representation optimization in simpLib.

## Compilation cost attribution

The structural cost gate is stronger than removing the observed mixed costs:
all ordinary source bodies, records and constructor schedules are baseline,
with no conditional extension path. `assembly/RESULTS.md` establishes that
**all 43 selected native bodies and 29 optimized trees** match, including
`++`, rewrite conversion construction, bound wrappers, net insertion's
specialized folds, USER_CONV, AC derivation, makers, empty initialization and
limit updaters. Emission multiplicity, reservation sizes, calls, field/stack
loads and branch operands are retained. No added local compiler instruction,
allocation reservation, adapter or traversal survives. The only selected
backend/ICode difference is the previously extracted tracking function's
exported constant. TASK12 separately establishes its constructor's smaller
closure reservation, rather than an added pair/configured runner.

This emitted-work/layout evidence resolves the **bounded compiler work**
question; noisy timing intervals are not declared numerical equivalence.
It does not establish equality of transitive callees on every platform or
satisfy the later independent-build/final performance matrix.

## Fresh timing experiments

Commands (run serially, without builds or other task benchmarks):

```
python3 -B src/simp/tests/compiled-core/run_core.py \
  --require-baseline-graphs --performance-pairs 10 \
  --output src/simp/tests/compiled-core/evidence/timing
python3 -B src/simp/tests/compiled-core/run_core.py \
  --baseline-control --performance-pairs 10 \
  --output src/simp/tests/compiled-core/evidence/timing-control
```

Repeat both with `--samples 5 --batch-seconds .5` into `long-timing` and
`long-control`. All four commands exit **0**. Each has ten fresh AB/BA process
pairs. First campaign: three measured batches/process/workload, >=0.2-second
calibration; second: five batches, >=0.5 seconds. All 11 workloads retain or
consume outputs and verify proofs. No outliers are discarded. CPU, wall,
non-GC CPU, GC CPU and the raw user/system fields remain separate; GC is not
added again to inclusive CPU. Full iteration counts and timings are retained.

CPU median paired ratios and 95% paired-median bootstrap intervals:

| Workload | Initial current | Longer current |
| --- | --- | --- |
| rewrites | 0.9969 [0.9899,1.0032] | 0.9953 [0.9788,1.0299] |
| merge | 0.9931 [0.9670,1.0066] | 1.0016 [0.9746,1.0440] |
| compile | 0.9986 [0.9738,1.0143] | 1.0104 [0.9851,1.0389] |
| missing deletion | 1.0009 [0.9766,1.0166] | 1.0086 [0.9932,1.0425] |
| projection | 0.9889 [0.9490,1.0155] | 0.9962 [0.9724,1.1637] |
| traversal construction | 0.9905 [0.9608,1.0232] | 1.0134 [0.9863,1.0541] |
| empty addition | 0.9828 [0.9549,1.0337] | 1.0020 [0.9820,1.0492] |
| installed SIMP_CONV | 0.9939 [0.9700,1.0361] | 0.9762 [0.9187,1.0251] |
| saved reuse | 0.9879 [0.9751,1.0190] | 1.0185 [0.9900,1.0574] |
| projection + application | 1.0053 [0.9880,1.0288] | 1.0129 [0.9841,1.0600] |
| compile + application | 1.0004 [0.9650,1.0298] | 0.9722 [0.9606,1.0055] |

Wall follows CPU; all per-workload intervals, non-GC and GC decisions are in
`evidence/analysis.json`. No current CPU/wall/non-GC interval is significantly
slower in either campaign. **The numerical parity result is inconclusive,
not pass**: overlapping one is not an equivalence test. Local work recovery
instead has the independent exact source/emitted-work/retained-layout proof.

Initial current GC has two slower intervals: saved reuse and compile+apply
(the latter median 1.0998 [1.0938,1.1071]). They do **not** reproduce in the
longer campaign: reuse 0.9947 [0.9807,1.0060], compile+apply 0.9593
[0.8294,1.1169]. Pure compilation GC improves in both campaigns. Controls
also expose layout/runtime variability: initial identical-source compile+
apply CPU is 1.0296 [1.0063,1.0669], while longer identical-source saved reuse
is 1.0265 [1.0103,1.0549]. These observations are retained, not filtered or
averaged against a faster row. No reproducible current slowdown or new local
compiler work was found. No default heap-matching flag or client opt-in was
used to obtain these results.

The earlier TASK15 full-module red rows remain historical evidence. This
bounded restoration adds ordinary-module import separation and exact compiler
work; it does not silently reclassify all 90 old fragment timings or claim
TASK29/37's expanded, final-revision statistical acceptance.

## Recheck and scope

```
python3 -B src/simp/tests/compiled-core/audit_core_evidence.py
python3 -B -m unittest discover -s src/simp/tests/compiled-core
```

The offline analyzer rechecks all sealed runtime/tool/input/shared-product
hashes and selected production sources, reparses graph receipts, rejects a
worse adjacent slope even under a lower intercept, recomputes the stored
performance summaries and adds separate non-GC intervals. Its new analysis
and test files do not alter the original sealed measurement inputs. Nine
core/evidence validator tests and ten assembly tests pass. Frozen fixtures
and their assertions were not rewritten. Normal `HOLSELFTESTLEVEL=1` includes
the private compiled-core behavior/storage gate. Measurement launchers/trees
are temporary and removed; only compact source-tied evidence remains.
