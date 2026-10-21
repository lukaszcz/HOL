# Simplifier performance evidence

`review-20261021/` preserves the compact original review bundle unchanged.
It is historical evidence tied to:

- develop `cccaa27d7099cbadc886983020cbe745db7793f3`;
- candidate `cf1f863b4e5a9712ce1b179f18274eb3451f3954`.

Provenance, hashes, current-state fingerprints, coverage inventory and
reproduction prerequisites are in
[`../compatibility/`](../compatibility/README.md).
The original behavior/ABI probes are colocated here solely to preserve
`reproduce.py`'s relative input paths. This is a small evidence bundle, not
an imported compatibility archive. The maintained diagnostic harness below
is separate from these immutable historical inputs.

## Bundle map

| Files | Purpose |
| --- | --- |
| `staging.sml`, `abicheck.sml` | Callback/exception staging and old-signature elaboration probes |
| `bench.sml` | 17 calibrated CPU workloads; five samples per workload |
| `detail.sml` | Eight focused CPU/GC/wall workloads and graph-size report |
| `memory.sml` | Incremental retained graph words at 0/10/100/1,000 rules |
| `reproduce.py` | Original paired reconstruction script, preserved unchanged |
| `review-results.json` | Original review summary, medians, behavior and storage observations |
| `detailed-benchmarks.json` | Original focused CPU/GC/wall medians and iteration counts |
| `validation-summary.json` | Original positive contract/native count summary |
| `*-timings-*.log` | Five raw CPU samples, repetition counts and sink per workload |
| `*-detail-*.log`, `*-memory.log` | Focused medians, counts, sink and graph words |
| `*-staging.log`, `*-abicheck.log` | Unique callback stages and actual elaboration diagnostics |
| `*-legacy.log`, `*-traversal.log.gz`, `*-exclusion.log.gz` | Original positive assertions and ordered observations |
| `native*.log.gz` | Native expanded selftest and focused cleanup-suite observations |
| `*-build.log`, `*-bench-build.log` | Original isolation/build context, not a build acceptance receipt |

## What the review reported (not remeasured by TASK_01)

The review shared the candidate heap/libraries between exact simplifier source
versions on Poly/ML 5.9.2 with one GC thread. Timing processes ran in
baseline/candidate/candidate/baseline order, with calibration and five measured
samples per workload. These were not independent whole-repository builds.

- Requirement callbacks/inferences moved from tactic construction to use;
  a saved valid tactic returned one goal on develop but raised `PrinterFailure`
  on the reviewed candidate after the printer began throwing.
- The unchanged old reducer datatype signature accepted develop and rejected
  the candidate's additional constructors. The log contains the actual SML
  static error, not just a dependency-scan outcome.
- 1,000-rule fragment creation was roughly 1.8–1.9x and merging 2.9–3.1x
  develop cost in the original CPU batch. Missing-name deletion was roughly
  3x; the separate focused wall-time batch was about 83 versus 245 us.
- Incremental 1,000-rule retained storage was 83,071 versus 125,096 reachable
  words after subtracting shared base and fragment graphs. This is neither
  process RSS nor a byte count nor total allocation.
- Positive evidence: 73 original selftests, 47 traversal checks (273 `OBS`
  lines) and 929 exclusion checks (2,703 `OBS` lines) per implementation;
  630 native selftest and 1,440 combined native checks. Traversal output was
  identical, exclusions matched after removing theory build-timing lines.
  `native` includes `native-selftest`; these counts are not additive.

## Historical limitations (not repaired in immutable inputs)

No repair, performance pass, independent build, fresh runtime measurement or
complete source-compatibility claim follows from copying these files.
There is no supplied historical exit-status manifest, loaded-path transcript,
or binary hash record; missing provenance is explicitly recorded, not invented.
Current fingerprints must not be relabeled as historical fingerprints.

`reproduce.py` is not fail-closed on missing observations and does not record
loaded paths. `bench.sml` discards projection/conversion construction results;
its existing sink does not fix those probes. `detail.sml` prints only the
per-field medians, not its five raw samples. These limitations remain visible
in the originals; the new probes below do not alter historical inputs.

## Maintained TASK_03 diagnostic harness

From the repository root, with **no other build or benchmark running**:

```sh
bin/Holmake --no-project --no-cache --no_prereqs \
  --holstate="$PWD/bin/hol.state0" \
  -C src/simp/tests/performance -j1 \
  PERFORMANCE_OUTPUT=/tmp/task03-fresh diagnostic
```

The output directory must not exist from an earlier run. This executes eight
performance validator tests and thirteen compatibility validator tests, then
six baseline/baseline fresh-process pairs, their summary, then six baseline/
reviewed pairs and their summary. Independent signature/staging checks and
all six negative controls execute on both selections before timings. Builds
finish before observations. Launcher/runtime/heap/dependency isolation is
provided by `../compatibility/run_paired.py`; its full schemas still apply.
This is **mixed-source isolation**, not independent clean repository builds.

Defaults: Poly/ML 5.9.2, `--gcthreads=1`, `hol.state0`, identical private-first
module paths/shared libraries, fixed 1,000 boolean assumption rules `ri = T`,
target `r0`, empty supplied assumptions. Every process starts a new theory,
calibrates each workload independently by doubling from one iteration until
wall >= 0.25 seconds, then records five raw batches after full GC outside the
timed region. Pair order is AB/BA alternating; every selection is a fresh
launcher process, not a repeated loop in one shared process. The runner
captures source/input/runtime/library/product hashes, options, loaded paths,
process exits and CPU affinity/load metadata. No outliers are discarded.

`Performance.sml` separates retained construction/projection from reuse and
also times complete operations. Every batch records wall, inclusive CPU
user/system, non-GC user/system, GC user/system and consumption, including all
calibration observations. Five forced GCs independently check timer accounting.
Poly's `checkCPUTimer` includes GC; `checkGCTime` is GC **user only**. Never add
GC to CPU. Runtime-version source attribution and the empirical timer control
are retained with evidence. The validator requires the two timer views to
agree within 20 ms (sequential reads are not atomic); this is an accounting
sanity check, not a performance acceptance allowance.

### Output consumption and timed boundaries

| Label | Timed operation / consumption | Batch-end exercise (outside timing) |
| --- | --- | --- |
| `rewrites_1000` | Build/retain fragment; consume rewrite-list length | Compile retained fragment and verify rewrite |
| `merge_frags_1000` | Merge/retain fragment; consume rewrite-list length | Compile retained merge and verify rewrite |
| `compile_1000` | Compile/retain simpset; consume history length | Apply retained simpset |
| `delete_missing_1000` | Delete literal missing name; retain/consume history | Verify surviving installed rule |
| `project_1000` | Retain traversal data; consume reducer-list length | Construct and apply traversal from retained projection |
| `construct_traverse_1000` | Construct/retain conversion; increment sink | Apply retained closure |
| `empty_add_1000` | Add empty fragment to installed set; retain/consume history | Apply retained simpset |
| `simp_installed_1000` | Ordinary `SIMP_CONV` construction+application; verify theorem | Already checked per iteration |
| `raw_reuse_1000` | Apply saved traversal; verify theorem | Already checked per iteration |
| `projection_apply_1000` | Projection+construction+application; verify theorem | Already checked per iteration |
| `compile_apply_1000` | Compilation+ordinary application; verify theorem | Already checked per iteration |

Every construction result is stored in a typed escaping reference (never an
ignored return value); fragment/simpset/projection outputs additionally feed
a per-iteration checksum. Result slots remain live throughout each batch,
and the last produced output is exercised after **every** calibration/sample.
Closure construction has no portable cheap semantic observer: its checksum
counts constructions, and its retained closure is actually applied after the
batch. There is no claim to invoke every constructed closure in the isolated
construction timing; the complete projection/application workload covers that
boundary too. Timed theorem consumers check the exact conclusion, one expected
hypothesis and consume its length. The final sink must equal all recorded
consumed counts, with exact per-operation counts checked by the validator.
These probes include reference/checksum and theorem-check overhead equally on
both selections; sub-microsecond numbers are not raw API nanosecond costs.

### Retained graph words

Let `base = pureSimps.pure_ss`, `f = rewrites (take rules n)`, `ss = base ++ f`,
and `rs = take rules n`, for n = 0, 10, 100, 1,000. After applying a live rule
when n > 0 and full GC, record standalone sizes and these unions:

- Compiled increment: `objSize (base,f,ss) - objSize (base,f,base)`.
- Historical method: `objSize (ss,base,f) - objSize (base,f)`.
- Fragment increment: `objSize (base,rs,f) - objSize (base,rs,base)`.

`PolyML.objSize` counts reachable graph words with sharing counted once within
each root union; subtraction removes shared base/input objects. Equal-arity
roots remove the historical extra tuple word. Report both methods, n=0,
standalone/union/anchor sizes and all raw process repetitions. Code/closure
and preexisting shared objects can contribute to constant terms. Do not call
these RSS, allocated words, bytes, global roots or exact lifetime/release
measurements. Graphs remain rooted in each process until process exit.

### Statistics, interpretation and evidence

`summarize.py` recomputes complete schemas/order and uses a per-process median
of five per-operation batches, then paired candidate/baseline ratios. CPU,
wall and GC remain separate; GC ratios with zero denominators are undefined.
A fixed-seed 20,000-resample percentile bootstrap gives descriptive 95%
intervals for median paired ratios. Six pairs have limited statistical power;
small intervals do not prove universal equivalence. All raw observations and
iteration counts remain available. Baseline/baseline controls use the same
options before reviewed measurements. Noise is uncertainty, **not a pass**.
No aggregate score, fixed regression budget or offsetting fast traversal is
used. Ten or more paired observations and expanded matrices remain required
by later final-acceptance tasks, not this diagnostic baseline.

The summary program assumes the runner's path validation already succeeded;
it independently revalidates metrics/order, not source provenance. Audit the
archived source/path bindings as well (including wrong-selection and mutated
source negative controls):

```sh
python3 -B src/simp/tests/performance/audit_evidence.py \
  src/simp/tests/performance/evidence/task03/baseline-control \
  src/simp/tests/performance/evidence/task03/reviewed \
  src/simp/tests/performance/evidence/task03/current-head
```

TASK_03 source-tied results, commands, exits, uncertainties and reproduction
receipt are in [`TASK_03_HANDOFF.md`](TASK_03_HANDOFF.md) and
[`evidence/task03/`](evidence/task03/). Immutable input integrity remains checked
by `../compatibility/verify_evidence.py`.
