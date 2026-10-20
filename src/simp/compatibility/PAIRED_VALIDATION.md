# TASK_14: pinned paired differential validation

## Pins, environment and result

**PASS for this bounded gate; no unexplained contract divergence remains.**
Repaired implementation: `5b5f07df2510f8ca73d3cc3c1a2c8c99199de06a`.
Fixed develop reference: `cccaa27d7099cbadc886983020cbe745db7793f3`.
No library implementation/API changed in this task. New/updated probe bytes
are working-tree inputs snapshotted identically into both lanes, not
uncommitted implementation sources. The original develop selftest remains
byte-for-byte identical to its pinned git source; its original 73 assertions
pass in both lanes. `inputs/SHA256SUMS` also passes unchanged.

Evidence root: [`results/task14/`](results/task14/).
`paired-verified/manifest.json` and `fresh-verified/manifest.json` record
exact source revisions, every staged source/input/support hash, runner,
Holmake/launcher/`hol.state0` hashes, working-tree state, exact commands,
exits and load-recipe dependencies. Shared inventories contain **1072 / 944**
files respectively, checked again after execution. `validation.json`
records native/routine commands and compressed-log receipts; supplemental
checks and environment/source hashes are in `final-checks.json`.

These are **mixed-source** tests. Each revision has private staged
simplifier, marker library and Q sources/products. Host kernel, early heap,
generated markerTheory and other dependency sources/recipes/theories are
shared. Recipe audits reject host fallback for staged library modules.
Hashes identify the actual inputs, not independent clean builds of either
repository revision. Runtime/native libraries are not exhaustively traced.

## Per-input contract matrix

Every row expects equality of its legacy contract observables. Both lanes
build and execute every input with exit **0**. Counts are **per lane**.
`comparison/matrix.json.gz` additionally records an indexed result for each
of the **3251 ordered observation pairs**, their expected relationship and
outcome, plus raw-log hashes/difference classifications. Values remain in
the manifests and original compressed logs, without term, exception,
warning or callback normalization. The input rows below map to filenames
in `probes/legacy/`, except fresh rows in `probes/fresh-load/`.

| Paired input | Verified contracts | OBS | OK | Outcome |
| --- | --- | ---: | ---: | --- |
| control | Full conclusion/hypotheses, callbacks, closed tactic validation | 8 | 4 | equal |
| develop-selftest | All original assertions; complete raw output | 0 | 73 | equal assertions/output |
| reducer-shape | Public projection's first reducer is REDUCER | 15 | 7 | equal |
| excl-rule-unmatched | Silent literal absence; conversion/rewrite/dproc, overlap/replay | 133 | 41 | equal |
| excl-rule-installed | Actual literal deletion; conversion/rewrite/dproc, overlap/replay | 133 | 41 | equal |
| excl-looper-unmatched | Silent literal absence; conversion/rewrite/dproc, overlap/replay | 133 | 41 | equal |
| excl-looper-installed | Actual literal deletion; conversion/rewrite/dproc, overlap/replay | 133 | 41 | equal |
| excl-solver-unmatched | Silent literal absence; conversion/rewrite/dproc, overlap/replay | 133 | 41 | equal |
| excl-solver-installed | Actual literal deletion; conversion/rewrite/dproc, overlap/replay | 133 | 41 | equal |
| excl-split-unmatched | Silent literal absence; conversion/rewrite/dproc, overlap/replay | 133 | 41 | equal |
| excl-split-installed | Actual literal deletion; conversion/rewrite/dproc, overlap/replay | 133 | 41 | equal |
| excl-case-unmatched | Silent literal absence; conversion/rewrite/dproc, overlap/replay | 133 | 41 | equal |
| excl-case-installed | Actual literal deletion; conversion/rewrite/dproc, overlap/replay | 133 | 41 | equal |
| traversal-lifetimes | Contexts, quotas, factories, defaults, traces/exceptions/staging | 273 | 47 | equal |
| exclusion-history | Strict replay, additions/deletions, ancestry/Context restoration | 72 | 28 | equal |
| exclusion-parsing | Suffixes, exact names, strict errors/warnings, current-theory replay | 1378 | 535 | equal |
| tactic-validations | Six nonempty tactic validations with independently proved subgoals | 55 | 24 | equal |
| fresh/control | Clean heap, dynamic load, ordinary simplification, free registries | 19 | 11 | equal contracts |
| fresh/attribute-first | Original load-order collision; foreign handler arguments/order | 25 | 19 | equal contracts |
| fresh/set-first | Foreign exporter callbacks, stored theorem/hypothesis/data preserved | 27 | 22 | equal contracts |
| fresh/attribute-after | Load leaves registries free; later foreign registration silent | 24 | 17 | equal contracts |
| fresh/set-after | Load leaves registries free; later exporter/data/callbacks work | 25 | 19 | equal contracts |

The original twelve regressions are the constructor, all ten prefix rows,
and fresh/attribute-first. Set-first and both owner-after cases broaden
load coverage. All maintained legacy inputs are executed, not selected
subsets. The unchanged develop suite has no OBS instrumentation: raw-byte
equality and its assertions are recorded, **not** a claim that every internal
operation has been traced.

### Observable details

- Prefix fixtures check full conclusions and hypothesis sets, literal
  conversion/rewrite/dproc deletion, overlapping-name survival, `Excl`/`-*`
  agreement and replay, with ordered callback records and warning capture.
- Traversal fixtures compare ordered entry/exit/collector/trace events,
  construction versus repeated application, recursive context lifetime,
  congruence/weakener factories, live stack defaults and shared bounded
  controls. They assert foreign exception payload identity, Interrupt,
  UNCHANGED boundaries and structured HOL_ERR wrapping.
- Parser/history fixtures check strict dotted, numeric and empty suffixes,
  unknown ancestry, bare kernel strings, repeated and interleaved deletion,
  restored and genuinely changed current theories. Parser dproc observations
  now include **unsorted actual callback order**, in addition to the existing
  membership assertion; the previous sorted records alone were insufficient.
- `tactic-validations.sml` supplements rather than edits the original suite.
  SIMP, ASM_SIMP, full, reverse-full and both global assumption orders run
  through `VALID`, retain a nonempty subgoal, prove it by kernel tactics,
  and invoke the returned validation. Reconstructed conclusions and exact
  hypothesis sets are asserted and paired. No `mk_thm`/cheat proof is used.
  The control separately covers closed `validation []`.
- Fresh processes assert missing loader entries **and** missing ML structures
  for simpLib/splitLib/splitPersistLib, unclaimed attribute/set registries
  and enabled warnings before emitting `precondition=clean`. Launcher recipe
  closures exclude simpLib/splitLib; dynamic-load closures resolve locally.
  Foreign callback arguments, theorem hypotheses/data and ordering survive.
  Set-first necessarily installs an attribute too (public exporter API);
  it is not represented as an independent set-only ownership test.

## Raw output, bounded adjustments and retests

`paired_report.py` rejects any unexplained raw build/runtime difference,
compares the full ordered observation lists, and retains exact differing
lines in `comparison/raw-differences.diff`. On the final run:

- **All build logs are byte-identical**, as are 16 of 17 ordinary run logs.
- The parser fixture differs only in two printed theory-export durations:
  `0.00096s / 0.00088s` and `0.00078s / 0.00077s`. Both values are retained;
  wall-clock export timing is not a simplifier contract.
- Each fresh pair differs only in its intentionally distinct absolute
  lane-local `load.path`. Both paths are checked against the actual staged
  library path before comparing every other observation in original order.
- No warning, exception, callback frequency/order or operation-stage
  difference is removed or permitted. Warnings are enabled and observed
  sinks forward to the normal sink. There is no compiler diagnostic left
  in either final lane's runtime logs.

The first run exposed a **fixture compiler diagnostic**, not an implementation
failure: its `val REDUCER _ = ...` binding is non-exhaustive with the branch's
extended datatype. A naive exhaustive reducer-only case then warned about
a redundant wildcard on develop. The final list match accepts only
`REDUCER _ :: _`; the failure arm also handles the empty list on both
revisions. It preserves the original constructor assertion without
compiler warnings or warning suppression. Retained unique diagnostic logs
and hashes are in `fixture-retests.json` and `*-constructor-diagnostic.log.gz`.
A negative-control paired rerun at original audited implementation
`62a6bdc3453c29e8f31faa72f2b70a245f44840d` still fails exactly at that assertion,
while reference/control pass (`constructor-red-*`). Thus the fixture repair
does not weaken or xfail the regression. Historical red inputs are unchanged.

The new tactic fixture initially used an unavailable tactic name, corrected
to `FIRST_ASSUM ACCEPT_TAC`; its initial typecheck diagnostic is retained.
The routine gate first caught an overlong new fixture line (wrapped), then
a stale native fresh-load launcher whose `.ui` had previously disappeared.
Rebuilding that launcher's `selftest.uo` restored its declared runtime
input; no library or build-system repair was needed. Both failed attempts
and the successful rerun have separate receipts/logs. Final routine build
ends `Hol built successfully.` No failed attempt is counted as a pass.

## Branch-only checks and reproducible commands

These checks are **separate** from legacy differential equality:
normal branch simplifier/marker selftests pass (**630 / 72 OK**), preserving
configured traversal, ExclX and extension assertions. Native focused tests
also pass: traversal/exclusion contracts, six fresh scenarios (including
native-only foreign syntax and handler-record pointer checks), split
registration, six persistence import/owner scenarios and real heap-save/
reload processes. Foreign-owner import rejection remains an asserted
expected error, not a swallowed failure.

From the repository root, choose new output directories for paired/report
commands. Exact commands and working directories for the retained runs
are in the manifests/validation receipts. `$HOLDIR` is the absolute root:

```sh
bin/build -t --seq=tools/sequences/upto-parallel
(cd src/simp/src && "$HOLDIR/bin/Holmake" --no-project --no-cache -j1 \
  --holstate="$HOLDIR/bin/hol.state0" selftest.exe fresh-load-regressions \
  split-registration split-persistence traversal-contracts exclusion-contracts)
(cd src/simp/src && ./selftest.exe)
(cd src/marker && "$HOLDIR/bin/Holmake" --no-project --no-cache -j1 \
  --holstate="$HOLDIR/bin/hol.state0" selftest.exe && ./selftest.exe)
PYTHONDONTWRITEBYTECODE=1 python3 src/simp/compatibility/run.py \
  --branch 5b5f07df2510f8ca73d3cc3c1a2c8c99199de06a \
  --output /tmp/compat-task14-new-paired
PYTHONDONTWRITEBYTECODE=1 python3 src/simp/compatibility/fresh_load.py \
  --branch 5b5f07df2510f8ca73d3cc3c1a2c8c99199de06a \
  --output /tmp/compat-task14-new-fresh
PYTHONDONTWRITEBYTECODE=1 python3 src/simp/compatibility/paired_report.py \
  --paired /tmp/compat-task14-new-paired --fresh /tmp/compat-task14-new-fresh \
  --output /tmp/compat-task14-new-comparison
PYTHONDONTWRITEBYTECODE=1 python3 src/simp/compatibility/paired_report_test.py
(cd src/simp/compatibility && sha256sum -c inputs/SHA256SUMS)
tools/h4pedant/h4pedant src/simp/src src/marker
git diff --check
```

All final commands exit 0. Reporter negative controls reject changed callback
order, exception, warning counts, missing observations, raw diagnostics,
wrong lane paths and dirty load preconditions. It also reads compressed
logs: retained run logs use `.run.log.gz`; manifest log names identify their
uncompressed logical names. Private staged sources, products/executables,
superseded result copies and task-owned scratch outputs were deleted after
use. Normal checkout products and unrelated/caller-owned artifacts remain.

## Handoff to TASK_16 / TASK_17

Changed files: the new legacy tactic probe, two shared assertion/observation
helpers, fresh-load paired comparison, standalone evidence reporter/tests,
this report, README/index/progress and compact `results/task14/` evidence.
No new API decision or implementation change. No TASK_14 blocker remains.

Verified: the bounded matrix above, including runtime warnings, hypotheses,
failures, callback order/frequency/staging and concrete tactic validation
functions. Untested: arbitrary clients/callbacks, every possible strategy or
parser combination, exhaustive compiler diagnostic compatibility, independent
repository builds and the full repository regression gate. Finite probes
and green selftests do **not** establish universal observational equivalence.
TASK_15 owns downstream validation; TASK_16 still requires explicit
`bin/build -t -F` after TASK_15; TASK_17 owns final qualified sign-off.
