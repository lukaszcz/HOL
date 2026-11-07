# TASK28 — expanded acceptance machinery

## Current completion: loading provenance repair v3

Landing identifier: **TASK28-loading-provenance-v3** (containing commit).
Starting HEAD and selected candidate simplifier sources:
`859be8ed7672d6c319e231d18b3d5cbfcda34b30`.
Develop remains `cccaa27d7099cbadc886983020cbe745db7793f3`.

**All bounded TASK28 machinery criteria are verified.** The two review-v2
loading provenance defects are repaired, and the prior six regression repairs
still pass. TASK29 is ready. This does not declare numerical P09 acceptance:
new loading failures below remain published inputs to TASK31, alongside the
existing TASK29 storage/timing findings. The seven explicit prerequisite
blocks in the unchanged 69-requirement/107-case matrix retain their scope.
No production SML, signature, layout, control, extension assertion or normal
extension test integration changed.

### Repair and runtime admission

- `loading.py` retains extraction's original Git seals as validation authority.
  They are checked before/after fixture installation, after each build (also
  checking the earlier selection), during actual loaded-source validation, and
  before success. Generated fixture inputs are sealed before building. Neither
  a new post-build hash nor an unloaded selected signature can hide a mutation.
- Loading schema `task28-loading-v2` adds actual `bin/hol`-linked library
  discovery, not inference from PATH's compiler. Successful Linux `ldd` output
  must be complete/resolved/nonempty. Every file-backed library and the loader
  has a logical path, resolved target and content seal in the report/inputs.
  Final checks verify original bytes and rediscover resolution, rejecting even
  same-byte symlink retargeting. ASLR addresses and the kernel VDSO are not
  file identities. Unsupported discovery blocks; no other platform is claimed.
- Both discovery commands and the separate compiler-version command run under
  the sanitized launch environment, timeout and inherited serial locks. Their
  complete receipts are archived **before validation**, including failures.
  `PROTOCOL_LOADING.md` documents this contract and its local-consistency,
  exclusive-window/non-hostile-producer limitations.
- `test_loading_provenance.py` adds 17 maintained tests. Real local Git
  extraction, installation, source/path validators and statistics run around
  explicitly synthetic build/process/timer events. Cases cover baseline and
  candidate build mutation, installation mutation, unloaded signatures,
  deletion, later-build mutation of the earlier selection, generated fixtures,
  post-build mutation, missing/partial/failed/unsupported library discovery,
  changed library bytes/resolution, same-byte symlinks, and failure receipts.

### Fresh verification and retained decisions

All new evidence is under `evidence/task28/loading-repair/`. `validation.json`
records commands, exits and source/evidence seals. Caller-owned `review/` and
`review-v2/` were read unchanged and remain caller-owned/untracked.

- Caller review-v2 probe: **exit 0**. Its unmodified control still admits all
  **42 synthetic observations** with the real source-bound semantic receipt.
  Candidate build mutation now rejects before any observation, with the exact
  original/mutated fingerprints retained. `review_probe.py` only adapts the old
  mock's command dispatch to let the newly added compiler/library discovery
  commands execute for real; it changes no supplied probe file or validator.
- Prior supplied review regressions: **6/6 pass**, exit 0.
- Final maintained `Holmake check`: **exit 0**, **241 Python tests** (two
  unchanged optional runtime/path tests skipped), **13 runner tests**, complete
  matrix validation, real slowdown/allocation/missing/failed controls, **306
  fragment-grid** and **336 client-stage** semantic smoke checks. Compatibility
  discovery: **196 pass**. Its first attempt hit transient ENOSPC; the complete
  retry passed, with the failure log retained and no unrelated files deleted.
- Final simpLib and congLib runs: **42 actual fresh processes each**, pilots
  plus ten B/B and ten B/C AB/BA pairs. Both bind the existing eight-process
  API-audit receipt to unchanged candidate Git bytes. All 84 processes pass
  proof/path/source/timer protocol checks; both runs seal **six actual linked
  libraries**, including libpolyml and the dynamic loader. Positive forced-GC
  minima are **0.002990s / 0.003219s**.
- Final simpLib: CPU/wall/GC **fail**. CPU ratio interval
  **[1.010233, 1.034799]**. Final congLib: CPU/wall **fail**, GC inconclusive;
  CPU interval **[1.004567, 1.015052]**. All final B/B metric decisions are
  inconclusive. CLIs correctly exit **1**, while protocol `success` is true.
  Failed/uncertain controls do not excuse candidate failures. These numerical
  findings are not waived, averaged, or claimed fixed by this machinery task.
- `replay.py`: independently recomputes all loading observations/statistics,
  checks every actual source/product against immutable Git/product/shared
  inventories, binds both library-discovery receipts and compiler provenance,
  rejects source/product and missing-library archive mutations, and rejects
  zero-GC substitutions in **all 84** real receipts. Lossless pack/unpack and
  a second replay agree exactly: **101 files**, both commands exit 0.
- An earlier whole 84-process experiment gave inconclusive timing decisions.
  After review found that failed discovery receipts were lost, archive-before-
  validation was repaired and the **whole** experiment rerun on final harness
  bytes. `development.json.xz` retains the earlier observations unchanged;
  no sample was discarded or reused in the final experiment.
- Coverage **2,153 IDs**, immutable **37 inputs**, pedant and whitespace checks
  pass. No compiled-source edit was made, so another routine build was not
  required; the preceding repair's routine/extension evidence is unchanged.

Runtime scope: Linux/aarch64, Poly/ML 5.9.2, one GC thread, configured shared
`hol.state0`. Commands use the existing `root-wrapper.sh` to bind the configured
historical root to this checkout. This is source isolation, not independent
clean-build evidence. Older loading archives without these runtime seals and
immutable build-stage binding are historical diagnostics, not v2 admission.
The previous repair's unrelated matrix/provenance gates retain their evidence.
Task-owned source/build/receipt/roundtrip scratch trees were removed immediately
after sealing. No caller-owned caches, review files or build products changed.

## Historical review repair v2 (loading completion invalidated by review-v2)

Landing identifier: **TASK28-harness-review-repair-v2** (containing commit).
Repair start and measured implementation: `c5595b85d7b1f5f7cfe4da6840fba773c166fa54`.
Develop remains `cccaa27d7099cbadc886983020cbe745db7793f3`.

The v2 landing reported completion after the six supplied review regressions
passed. Review-v2 subsequently invalidated its loading provenance claim; the
v3 section above supersedes that claim and the affected loading admission.
The six repairs and unrelated matrix evidence below remain valid.
The unchanged 69-requirement/107-case matrix still has seven explicit
prerequisite blocks for later gates. No production SML, API, layout, mutable
control, test assertion or extension capability changed in this repair.

### Repairs and admission contract

- `acceptance.py` includes every requested retained-storage slope in its CLI
  decision, not just point metrics. Missing size grids, undefined/nonmonotonic
  slopes and uncertainty cannot exit zero. Failed **or uncertain** baseline
  controls prevent candidate parity claims for both point metrics and slopes;
  neither can excuse a candidate failure. Protocol `success` remains distinct
  from per-workload pass/fail/inconclusive decisions.
- `run_paired.py` seals shared logical/physical source and related-product
  inventories, checks live bytes and consistency across processes, then runs
  strict manifest admission. `audit_evidence.py` binds archived shared sources
  and complete related products to that inventory, validates normalized paths
  without touching deleted roots, and checks private product completeness too.
  Matrix runtime admission requires exact one-GC-thread/heap options, required
  runtime/tool fingerprints, sealed successful compiler-version/library
  discovery commands and library hashes, successful selected builds, and
  matching launcher text/options/product hashes. These are local provenance
  consistency checks, not hostile-producer authentication or clean builds.
- `loading.py` rejects forced-GC controls without positive GC CPU **and**
  GC-user evidence. Zero-GC actual imports remain valid observations, with
  undefined paired ratios inconclusive. Loading uses the same strict control
  uncertainty policy as the point/slope gates.
- `test_acceptance_decisions.py`, `test_archive_provenance.py`, and existing
  acceptance/loading tests preserve all six review cases plus product deletion,
  path normalization, runtime/launcher/tool faults and every CLI outcome.
  The original review directory is caller-supplied, unchanged input.

**Historical matrix bundles below are no longer admissible for acceptance:**
without a manifest-level `shared_inputs` inventory they fail closed. Their
original observations/seals remain unchanged historical diagnostics; the
inventory is never manufactured retrospectively from the receipts. Legacy
non-matrix diagnostic audits retain their original contract. The fresh repair
bundles use the new schema and replay through the current strict validator.

### Fresh validation and exact scope

All paths here are relative to `evidence/task28/repair/`. `validation.json`
records exact commands/exits/input hashes; `replay.json.gz` records individual
metric/slope decisions and real archive mutations. `replay.py` revalidates
complete archives and recomputes statistics after lossless bundle unpack.

- Supplied `review/review_regressions.py -v`: **6/6 pass**, exit 0.
- Maintained `Holmake check`: exit 0; **224 Python tests**, two optional
  real-runtime skips separately executed below; **13 runner tests**, real
  slowdown/allocation/missing/failed controls, all **306 fragment-grid** and
  **336 client-stage** smoke checks. Compatibility discovery: **196 pass**.
- Full six-size `storage_graph` experiment: **240 timed fresh processes**,
  ten B/B and ten B/C AB/BA pairs per size, three samples, 0.3s calibration.
  Every receipt passes current strict admission. All ten candidate and ten
  control adjacent graph slopes pass; all point graph increments pass.
  CPU/wall fail at sizes 10 and 10000; other timing/GC decisions are
  inconclusive. CLI correctly exits **1**, protocol complete. These timing
  regressions remain published inputs to TASK29, not waived or declared fixed.
- The earlier **whole** 0.1s six-size attempt correctly failed on a too-short
  batch at size 1000, CLI **2**. `rejected-short-batch.json.xz` keeps every
  observation, including completed earlier sizes. No favorable subset was
  reused in the separate, predeclared 0.3s whole-experiment rerun.
- Fresh downstream-boss client: both source versions pass with **799/801**
  actual source paths and **12 executable fault controls** rejected. Its two
  timing processes are protocol checks, not ten-pair performance acceptance.
  Optional real client tests: **9/9 pass**, rebuilding 122/121 shared dependent
  modules; real runtime/release/count/RSS tests: **23/23 pass**.
- Fresh congLib loading: **42 processes**, pilots plus both ten-pair AB/BA
  experiments, source-bound eight-process semantic prerequisite, all metrics
  inconclusive, CLI **2**. SimpLib smoke: **6 processes**, CLI **0**, explicitly
  not statistical acceptance. Forced-GC CPU minima: **0.003294/0.003398s**.
  Replacing the accounting control with zero rejects **every one of the 48**
  archived processes. Loading statistics are independently replayed.
- `replay.py`: **242 strict source-bound matrix receipts**, all **48 loading
  receipts**, source/product/path/tool/runtime mutations rejected on real
  fragment and client archives. The final private-product-completeness guard
  was added after measurement, then all archives were revalidated with it;
  benchmark fixture/implementation bytes did not change.
- Routine `bin/build -t --seq=tools/sequences/upto-parallel`: exit 0; ordinary,
  extension, strict post-list native and fresh API-audit suites stay enabled.
  Fresh eight-process receipt:
  `../api-audit/evidence/20261023T134511Z-2d38606e/receipt.json`.
- Completeness ledger, **2,153 coverage IDs**, **37 immutable inputs**, pedant
  and whitespace checks all pass. No compiled-source edit required the build;
  it was additionally rerun to verify normal integration. It occurred after
  experiments; no final-revision performance/build-product parity is claimed.

Linux/aarch64, Poly/ML 5.9.2, one GC thread, configured shared `hol.state0`.
Commands used the existing `root-wrapper.sh` to bind the recorded historical
configured root to this exact checkout. Inputs, actual process exits, options,
raw timings, graphs and telemetry remain in the lossless XZ bundles. All
agent-created scratch trees, unpacked bundles and temporary logs were removed
once sealed; caller-owned review files, old caches and ordinary build products
were preserved. No TASK28 machinery blocker remains; stronger unsupported
allocation/peak/lifetime/independent-build prerequisites remain explicit at
the affected later gates, as allowed by this task.

## Original v1 handoff (historical; review invalidated completion claim)

Landing identifier: **TASK28-expanded-harness-v1** (containing commit).
Starting/measured candidate: `c2d8fb1c37e8920b35d4ffc23a7b5cce3d6c08e9`.
Develop: `cccaa27d7099cbadc886983020cbe745db7793f3`.
Starting main worktree was clean; unrelated nested `.agent-files` state was
preserved. Linux/aarch64, Poly/ML 5.9.2, one GC thread, configured `hol.state0`.

The original completion claim was invalidated by six review regressions.
The v2 repair and evidence above supersede that claim and archived admission
results below. The original workload fixtures and prerequisite ledger remain
unchanged. None of TASK29–33's numerical performance gates is declared passed.

## Catalog and verified outputs

`matrix.json`, `matrix_schema.py` and `MATRIX.md` define **69 requirements and
107 cases**. The schema independently freezes the requirements, bindings,
construction/reuse/complete stages and size grids. It checks live SML dispatch,
rejects deleted/unknown/duplicate rows and cannot report incomplete coverage as
complete. There are 53 runnable-case requirements, nine runnable-external
requirements and seven explicitly prerequisite-blocked requirements.

- `MatrixSupport.sml` / `MatrixPerformance.sml`: **51 cases**, all at
  **0/1/10/100/1000/10000** rules. Named/anonymous/record fragments, updates,
  duplicates/merges, AC/TypeBase, batch/single/empty/excluded compilation,
  conditions/bounds, makers/collectors/user conversions, construction/reuse/
  complete/supplied rules, direct and marker exclusions, dprocs, strict literal
  and partial/qualified names, replay, theory changes, limits and maker changes.
  Exclusion **tactics** have separate construction/reuse/complete stages and
  actual residual-goal proof validations, not just conversion-route proxies.
- `ClientPerformance.sml`: **56 cases**. Real reducer/congruence/weakening,
  repeated solver conditions and failed candidates, saved conversions, 14
  tactic families with construction/reuse/complete stages, supplied versus
  installed rules, scaling assumptions, full/reverse dependency order,
  requirements and global fixpoints. Actual arithmetic/reduce/boss workloads.
- Every result escapes through a typed reference; the final result is exercised
  after every calibration and sample. Proofs compare kernel conclusions and
  complete hypotheses; tactics reconstruct proofs using returned validations
  and check ordered residual goals/assumptions. Makers/collectors have exact
  per-batch callback assertions. Complete operations include construction and
  application; costs cannot simply be moved outside every timer.
- `smoke_matrix.py`, `smoke_clients.py` are maintained untimed, exact-source,
  private Holmake/selftest/testutils drivers. Final matrix grid: **604 + 8 =
  612 checks**, exactly 2 revisions × 51 cases × six sizes. Client smoke:
  **358 checks**, all 56 at 0/1/10 plus depth 100, selected assumption 1000,
  supplied/ASM assumption 10000. This is not every tactic at every size.
  A full-simplification 10000-assumption smoke exceeded its explicit 300-second
  limit; its failure is retained, not counted as success. That expensive
  endpoint needs a longer `--timeout`; smaller endpoints and other large
  families are verified. No performance pass follows from semantic smoke.

The final API/coverage/migration ledgers and TASK27 handoff were read. No
production signature, implementation, layout, control identity, callback stage
or generic marker/theorem-set/postkernel code changed. Extensions remain
separately enabled through normal-level suites, not loaded into ordinary
performance processes to obtain results.

## Protocol, controls and provenance

`acceptance.py` provides serialized, parameterized acceptance orchestration:
mandatory baseline/baseline controls before baseline/candidate, at least ten
fresh AB/BA pairs, calibrated batches, raw CPU/wall/GC, medians, paired ratios
and fixed-seed 20,000-resample 95% intervals. No outliers are removed. Lower
ratio bound >1 fails; upper bound <=1 passes; otherwise inconclusive. Zero
baseline metrics are inconclusive, including 0/0. No regression allowance,
control subtraction, fitted workload average or aggregate budget exists.

CLI exits: 0 only for reported passes, 1 for a metric failure, 2 for uncertainty
or blocked/error results. Protocol completion is recorded separately from
performance decisions. Missing sizes explicitly block retained-slope inference.
All adjacent storage intervals, including 0-to-1, are supported, with size-zero
terms separate. Unit controls reject even arbitrarily small reproducible costs.

The existing runner now accepts `--matrix-performance --performance-case CASE
--performance-size N`. It selects the correct fixture, seals its support files,
validates every result/stage/count and audits actual loaded sources/products.
The archived audit revalidates graph, runtime, release, option and fixture
bindings. Private builds finish before paired observations. Host/user and Git
common/worktree directory locks serialize cooperating runners; inherited file
handles keep locks in launcher descendants. Noncooperating external builds
still require explicit measurement authorization (no exclusive window
is required; the host is shared).

Actual client integration exposed absolute shared `.uo/.ui` paths bypassing
private simplifier sources. `client_dependencies.py` traces both dependency
kinds and privately rebuilds the affected shared-source reverse slice. Generated
theory loader descriptors/data are relocated and sealed; explicit custom recipe
dependencies are preserved. Real baseline/candidate path tests rebuild 122/121
shared dependent modules and audit **799/801 actual source paths**. No shared
simplifier path is allowed. These dependencies come from the common configured
checkout, not a claim of independent pinned-develop dependency builds.

`loading.py` adds separate first-import simpLib/congLib experiments. Each has
fresh calibration pilots, empty-bracket/forced-GC accounting, ten-pair AB/BA
controls/comparison, raw import timings and full path/exit/proof checks.
congLib includes its simpLib dependency; these costs must not be added.
Process-launch wall is retained separately, not called import CPU. Non-smoke
runs bind TASK27's eight-process callback/dependency/extension-absence receipt
to the candidate's actual Git source bytes. Full startup/cold-cache and clean
independent loading are not inferred from first-import isolation.

The harness-only controls use **real fresh subprocesses**: deliberate CPU
slowdown, retained allocation via tracemalloc, valid output followed by exit 7,
and exit 0 with missing output. Both regressions are detected as fail; both
process/result faults hit their intended rejection guards. Python allocation
controls validate detector machinery, not HOL allocated-byte measurements.
The six existing executable runner fault controls also reject on both sides.

## Runtime/storage units and real prerequisites

`RuntimeMetrics.sml` / `runtime_metrics.py` record every calibration/sample's
full/partial GC and sharing-pass counters, GC-updated heap/free/stack/code and
allocation-area sizes, and Linux RSS/HWM snapshots **in bytes**. Measurement
brackets exclude snapshot/proc/printing/verification work. Timer accounting
retains inclusive CPU, non-GC CPU and GC separately: **never add GC to inclusive
CPU**; `checkGCTime` reports GC user time only. Forced full-GC controls exercise
both timer and count accounting. Timer reads are sequential, not atomic.

`storage_graph` records equal-arity reachable graph **words**, not allocation
or RSS. A separate release control keeps a conversion's simpset ref live,
validates its proof, drops the holder and observes actual weak collection after
three full GCs, with a positive live-holder control.

Real runs exposed decreasing raw Linux VmHWM across GC unmaps. These approximate
snapshots are preserved unchanged; nonmonotonic HWM **blocks RSS/high-water
inference**, never clamps it or discards valid independent timing/GC data.

The seven prerequisite-blocked gates are explicit, never fake fixtures:

1. Cumulative HOL allocation: Poly/ML 5.9.2 exposes GC-updated allocation-area
   space, not a cumulative allocated-byte counter. A supported/instrumented
   allocator is needed; native reservation-site audits remain structural input.
2. Exact temporary peaks: per-process HWM/RSS exists, but a supported isolated
   high-water accounting domain for precise batch peaks is unestablished.
3. Strong internal lifetime/global retention: `Weak.weak` accepts refs only,
   not opaque simpsets/net objects. The actual wrapper-root collection probe
   cannot establish collection of independently globally retained internals.
   No unsafe casts or closure introspection were introduced.
4–5. Integer and real proof environments: shared exports lack intLib/intReduce/
   realSimps. Candidate-only local products are not baseline dependencies.
6–7. Independent routine/full builds: immutable clean snapshots and complete
   fresh products/manifests are prerequisites, not the shared heap used here.

`acceptance.py verify-builds` and `run --mode independent` have a documented,
negative-tested manifest contract: exact clean pins, disjoint roots/inodes,
matching live tool hashes/version/options, pristine prebuild receipt,
configure plus explicit `bin/build -t -F`, command/log/exits/time seals, fresh
runtime/heaps/Holmake/configuration and complete dependency inventory. Missing,
stale, cross-root or shared-inode products fail closed. Verified prerequisites
never relabel `run_paired` observations as independent: fresh independent
launchers/path/proof/storage observations remain blocked until those real
build inputs exist. Synthetic manifest tests are not actual HOL clean builds.

## Fresh evidence and decisions

`evidence/task28/observations.json` publishes each experiment's metric decisions.
Final 107-case-catalog validation has ten B/B and ten B/C pairs for each of
`frag_create` and `storage_graph` at size 10: **80 timed fresh processes**.
CPU/wall/GC conclusions are inconclusive; graph increments pass their bounded
comparison. Missing grid sizes correctly block slope conclusions. First-import
congLib adds **42 fresh timed processes** (two pilots plus both ten-pair
experiments); its metrics are inconclusive. Both CLIs exit **2**, not pass.
SimpLib loading also has a separate accepted protocol smoke.

An earlier fixed experiment produced a storage compilation CPU/wall **fail**
(CPU interval [1.002854, 1.046324]); it is fully retained in
`prior-experiment.json.xz`. The later inconclusive repetitions do not erase that
observation or close a regression. TASK29 must investigate the unresolved costs
with longer/stronger measurements and structural evidence; TASK28 does not
require final performance acceptance. No observation from either fixed
experiment was filtered or pooled selectively into another experiment.

Each paired experiment retains exact source Git blobs, fixture/tool/heap/
dynamic-library hashes, runtime options, calibrated counts, raw timings,
consumption, source paths, actual exits and complete ordered observations.
The final direct tactic client and tactic exclusion routes additionally execute
fresh timed/verified fixtures. Normal routine builds retain all legacy and
extension suites, including strict native post-list coverage and fresh API audit.

## Commands, exits and durable receipts

From repository root. `W` is
`sh src/simp/tests/compatibility/evidence/task26/root-wrapper.sh`.
It binds the configured historical `/home/lukasz/dev/HOL/...` path to this
exact `/home/lukasz/work/HOL/...` checkout, not another source/build tree.
Use new output paths when reproducing.

| Command | Exit / observation |
| --- | --- |
| `python3 -B -m unittest discover -s src/simp/tests/performance -p 'test*.py'` | 0; **191 tests**, two optional real-runtime skips separately executed below |
| Compatibility discovery `-p 'test_*.py'` | 0; **196 tests** |
| `W env HOL_CLIENT_REPO=CONFIGURED_ROOT python3 -B -m unittest discover -s src/simp/tests/performance -p test_client_dependencies.py -v` | 0; all **9 tests**, full actual path/edge/leak controls |
| `W env RUNTIME_METRICS_SML=1 RUNTIME_METRICS_EVIDENCE=NEW_JSON python3 -B src/simp/tests/performance/test_runtime_metrics.py` | 0; all **23 tests**, both real release/count/RSS probes |
| `W bin/Holmake --no-project --no-cache --no_prereqs --holstate=CONFIGURED_ROOT/bin/hol.state0 -C src/simp/tests/performance -j1 PERFORMANCE_CHECK_OUTPUT=NEW_DIR check` | 0; maintained controls, completeness, private fragment/client smoke entries |
| `W python3 -B .../smoke_matrix.py --scope grid --candidate CANDIDATE --timeout 900 --output NEW_JSON` and `--scope expensive` | both 0; **604 + 8** final-source checks |
| `W python3 -B .../smoke_clients.py --scope scaling --candidate CANDIDATE --output NEW_JSON` | 0; **358** semantic checks |
| `W python3 -B .../acceptance.py run --candidate CANDIDATE --case frag_create --case storage_graph --size 10 --pairs 10 --samples 3 --batch-seconds 0.1 --authorize-measurements --timeout 300 --output NEW_DIR` | **2**, complete protocol / inconclusive final decisions; `paired.json.xz` |
| `W python3 -B .../loading.py --baseline BASELINE --candidate CANDIDATE --module congLib --pairs 10 --api-audit RECEIPT --authorize-measurements --output NEW_DIR` | **2**, complete protocol / inconclusive; `loading.json.xz` |
| `W bin/build -t --seq=tools/sequences/upto-parallel` after final SML changes | 0; `routine.log.gz`, fresh API-audit receipt `../api-audit/evidence/20261023T121652Z-d08b8d83/receipt.json` |
| Archived audit after lossless bundle roundtrip | 0; every retained timed matrix receipt source-bound; mutation guards reject |
| `verify_evidence.py`, `coverage_ledger.py` | both 0; **37 immutable inputs / 2,153 coverage IDs** unchanged |
| `W tools/h4pedant/h4pedant --nolinelen --unicodeok src/simp/tests/performance`, `git diff --check` | both 0 |

The 191-test log includes source/receipt mutations, every missing required
matrix field, process/timeout/lock controls, bootstrap/no-budget tests,
independent-manifest faults and lossless evidence transport failures. Deliberate
faults are not silently relabelled successful samples.

`evidence_bundle.py` stores repeated receipt inventories together using XZ;
roundtrip verifies **every original byte/hash**, including original gzip
headers. It is transport, not a replacement for source/measurement validation:

```sh
python3 -B src/simp/tests/performance/evidence_bundle.py unpack \
  src/simp/tests/performance/evidence/task28/paired.json.xz /tmp/task28-review
python3 -B src/simp/tests/performance/audit_evidence.py \
  /tmp/task28-review/frag_create-10-control \
  /tmp/task28-review/frag_create-10-candidate \
  /tmp/task28-review/storage_graph-10-control \
  /tmp/task28-review/storage_graph-10-candidate
```

`validation.json` and `evidence-seal.json` pin the final files, commands,
statuses, evidence and limitations. No cross-platform, independent-build,
full-distribution or final performance claim is made. Private copied trees,
products, scratch outputs and newly created caches are removed after sealing;
pre-existing caches and ordinary repository build products are preserved.
