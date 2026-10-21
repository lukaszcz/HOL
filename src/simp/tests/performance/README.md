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
an imported compatibility archive or executable acceptance harness.

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

## Limits and next measurement prerequisites

No repair, performance pass, independent build, fresh runtime measurement or
complete source-compatibility claim follows from copying these files.
There is no supplied historical exit-status manifest, loaded-path transcript,
or binary hash record; missing provenance is explicitly recorded, not invented.
Current fingerprints must not be relabeled as historical fingerprints.

`reproduce.py` is not fail-closed on missing observations and does not record
loaded paths. `bench.sml` discards projection/conversion construction results;
its existing sink does not fix those probes. `detail.sml` prints only the
per-field medians, not its five raw samples. These limitations remain visible
in the originals. Revise new probes and record fresh complete observations in
TASK_02/03, without altering the historical inputs. Establish baseline/baseline
variability before interpreting small differences. Retain compilation,
projection, empty additions and ordinary simplification in the workload gate
even where review costs were small or variable. Never average regressions away.
