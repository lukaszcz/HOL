# Paired evidence schema v1

`run_paired.py` is the executable validator for these schemas. Unknown protocol
kinds, wrong arities, reordered/missing/duplicate events, mismatching source
paths/hashes, wrong process exits and timeouts are errors. `test_runner.py`
mutates valid receipts to exercise the validator independently of HOL.
All counts are exact, not minima. TASK_03 adds the optional performance
fixture; TASK_04 adds frozen public clients; TASK_05 adds independent staged
proof contracts. TASK_02 observations are unchanged.

## Ordered process protocol

Each flushed line is `@@PAIR<TAB>N<TAB>kind<TAB>fields...<LF>` with contiguous
zero-based decimal N. Other stdout/stderr lines are diagnostics, not success
signals. String exception messages use SML `String.toString` escaping. Paths
are absolute logical HOL/HFS paths; the receipt also records physical paths
(`.hol/objs` for generated files). Tabs/newlines in checkout paths are unsupported.

The complete ordered stream is:

1. `begin selection fixture control` (exact requested values).
2. `cwd private-directory`.
3. `holdir environment-HOLDIR Systeml.HOLDIR` (both must equal requested repo).
4. `preloaded comma-separated-module-names` (no simplifier module may be baked
   into the initial state or loaded by the launcher).
5. One or more unique `heapfile path` events: initial `Meta.fileDirMap` source
   map, including the launcher imports. These are **metadata from the heap**,
   not claims that today's file bytes built that heap.
6. Exactly two `search path` events: private directory, shared repo `sigobj`.
7. `use path`, followed by `used path` after successful elaboration. Uses are
   sequential, not nested. Observations/checks may occur between them. The
   only permitted unfinished use is the explicitly selected expected-red
   signature/ascription/functor fixture.
8. Unique `loaded path` events in `Meta.fileDirMap` order. The set must equal
   initial heapfiles union successfully elaborated files. Untraced additions
   or missing inventory entries fail closed. Every source is path-audited,
   fingerprinted, and checked for mutation before deleting the private tree.
9. Exactly one `end pass|error test-count`. No event may follow it.

Protocol events `observation key value` and `check label pass` must match
**the whole ordered array**, including repeated check labels:

| Event | Baseline selftest | Reviewed selftest |
| --- | --- | --- |
| observation construction.printers | 1 | 0 |
| check requirement failure | pass | pass |
| observation first.printers | 1 | 1 |
| check requirement failure | pass | pass |
| observation second.printers | 1 | 2 |
| observation saved.outcome | goals=1 | PrinterFailure |
| check ordinary simplification | pass | pass |

Selftest count is **3**, exit **0**, footer **pass** in either mode. The
reviewed behavior mode is labeled `expected-candidate-red`, NOT compatibility
success. Checks use `testutils.tprint/OK/die`; unexpected exceptions fail.
These deliberately small staging controls do not replace the original 73
selftests, 47 traversal contracts, 929 exclusions or later proof-stage tests.

Passing signature: exactly `check legacy signature pass`, count **1**,
exit **0**, footer **pass**; the complete unchanged old signature/ascription
must elaborate. Rejecting signature: exactly `exception Fail` with escaped
message `Fail \"Static Errors\"`, count **0**, exit **1**, footer **error**;
the unfinished use must be SignatureCheck.sml and diagnostics must independently
contain BOTH exact CONFIG_REDUCER and CONTEXT_REDUCER constructor mismatches.
A different static error, failed launcher or exception is not expected-red.

## Result files

UTF-8 JSON; SHA-256 values are lowercase hexadecimal over file bytes. All
sizes are bytes. Receipts use deterministic gzip (`mtime=0`), not copied build
trees. `manifest.json` is always written for runs that enter the driver, even
when validation fails; a failed driver exits nonzero. Existing output
folders are refused, not overwritten. An invalid repo/CLI may fail before a
manifest can be created. Private temporary inputs/products are removed on
success and failure, after processes terminate.

### manifest.json

- `schema_version`: 1; `evidence_id`: TASK_02-paired-v1.
- `scope`: explicitly mixed-source isolation, not independent builds.
- `command`, `repo`, `head`, `dirty`: exact invocation/checkout provenance.
- `runtime_options`: common launcher options; `environment`: effective HOLDIR,
  PATH, TERM, LC_ALL, TZ. Inherited HOL*, POLY*, ML*, PAIR_* are stripped.
- `tools`: path → `{sha256, bytes}` for runtime, heaps, Holmake, poly executable
  and project config; `poly_version`: captured process receipt of `poly -v`
  (the banner and `RTS version: ...`; records made before 2026-11-05 hold
  the output of `poly --version`, the banner alone).
- `inputs`: maintained fixture/driver/schema path → `{sha256, bytes}`.
- `selections`: baseline/candidate → requested ref, resolved revision, private
  path, exact Git source inventory (`git_path`, `git_blob`, `private_path`,
  sha256, bytes), generated fixture hashes, build exit, launcher text and
  product path → fingerprint. Sources are exact selected Git bytes, including
  Poly BloomApprox and theory scripts, excluding native selftest/mosml files.
- `runs`: ordered `{receipt, accepted, expected_acceptance, exit}` objects.
  Acceptance means the selected contract was observed, NOT a production repair.
- `success`: true only when all positives and requested negative controls
  meet their expectations. On failure `failure` gives the reason; fields
  not reached may be absent. Subsequent tasks must not treat false as done.

### Process receipts (*.json.gz)

All receipts: `command` (argv), `cwd`, `exit` (integer or null), `timed_out`,
`stdout_sha256`, `stdout_bytes`, `diagnostics` (non-protocol lines in order).
Build receipts have just these fields. Both builds must exit 0; .uo generation
is never a test result. `poly_version` additionally retains stdout inline:
`Poly/ML ... Release    RTS version: ...` for `poly -v`, the banner alone in
the legacy `poly --version` records.

Test receipts additionally contain `selection`, `fixture`, `control`, effective
PAIR_* `environment`, `accepted` and either:

- `result`: `outcome` (pass or expected-candidate-red), `expected_test_count`,
  complete ordered `observations`, complete ordered parsed `events` (transport
  N is checked before removal), and `paths`: logical path → physical path,
  sha256, bytes, `origin` (elaborated or initial-map), `related_products`
  (existing sibling .ui/.uo/.dat fingerprints, including HFS products).
- `rejection` plus parsed `events`, or `malformed_stdout` if transport parsing
  itself failed. Invalid output is preserved, never reparsed into success.

Every accepted run's source/product fingerprints are rechecked at pair end;
all runtime/config hashes are rechecked too. No shared library rebuild is
allowed (`--no_prereqs`); initial heap provenance remains an isolation limit.

## Harness-only executable controls

Each runs on BOTH selections, with source manifests untouched:

| Control | Exit | Required rejection/evidence |
| --- | --- | --- |
| missing | 0 | Missing second.printers, otherwise complete stream; observation guard |
| truncated | 0 | Launcher omits footer; completion guard |
| failed | 1 | Full successful transcript, failing process; exit guard |
| wrong-path | 0 | Other selection's fixture/dependencies; wrong simplifier path guard |
| deferred | 1 | Deferred.uo/launcher build succeeds; executed int/string mismatch in Deferred.sml, exact Static Errors exception; completion guard |
| unexecuted | 0 | Execute `true`, not built launcher; begin/header guard |

Control-specific guards are asserted, not just any failure. Parser unit
controls additionally cover dropped/reordered transport events, no final LF,
incomplete loaded inventories, source mutations, arbitrary static errors,
wrong-but-byte-identical source paths and killing descendants on timeout.
Baseline-versus-baseline executes the wrong-path control too: rejecting it
cannot depend on a behavioral difference between the two revisions.

## TASK_04 optional public clients

`--public-contracts` additionally extracts exact selected
`src/1/ThmAttribute.{sig,sml}` and installs the nine sealed baseline-only
`public/*.sml` clients plus complete original renamed `Legacy*.sig` inputs.
`public_contracts.py` defines each exact ordered check array and required
implementation/signature elaborations; `PUBLIC_CONTRACTS.md` maps all exports.
Every changed baseline-existing signature must appear in this inventory.

`PublicTraverseAscription` and `PublicTraverseFunctor` use the existing
`--candidate-signature reject|pass` choice. Reject means the same mandatory
exception, BOTH constructor errors, exit 1, zero checks and error footer as the
old signature fixture, but in the exact selected new client. Exactly those
TWO compiler error lines are permitted; additional static errors fail validation
even when both constructor errors are present. Pass requires one check, exit 0
and no unfinished source. `PublicTraverseClient` always
executes three checks; reject additionally requires exactly one nonexhaustive
match warning attributed to that client's source path. Its outcome is then
`expected-candidate-red`, despite exit 0. Other public clients require all
checks, complete frozen-signature elaboration, exit 0 and pass footer.

The bootstrap no longer imports testutils/HolKernel before tracing.
`CheckSupport.sml` installs the unchanged testutils reporting behavior after
recording the initial heap and setting private-first paths. The ordinary
launcher still uses state0. For the early `PublicThmAttribute` fixture,
Holmake builds a second `attribute.exe` launcher using **state.min on both
selections**, with one GC thread. Its source must NOT be preloaded and both
selected implementation and reference must actually elaborate. Every source
map/path/hash/exit guard still applies; no shared ThmAttribute is allowed in
that fixture. Other fixtures use the normal preloaded early libraries.

The manifest uses `evidence_id: TASK_04-public-contracts-v1`, adds
`public_contracts` (references, fixtures, complete signature diffs and changed/
branch-only/unchanged-dependency inventories per selection), and records each
selection's `attribute_launcher` and `attribute_holmakefile`. There are two
extra `*-attribute-build.json.gz` receipts. Sources/clients/references and
validators are all input-hashed. The transient private Holmakefile's sole heap
change is recorded and then restored before process/path audits. Common
`runtime_options` describe the normal launcher; the early launcher's actual
options are explicitly retained in its text and process command.

## TASK_03 optional performance fixture

`--performance-pairs N` installs `../performance/Performance.sml` into both
private trees. It is a deferred `.uo`, actually elaborated in a fresh launcher
process for each selection of each pair, after both builds and the independent
behavior/signature/control runs. Process order alternates AB/BA. The same full
source/path/exit/footer validation applies; there is no expected-red timing
mode. The driver checks that fixture/driver inputs do not change during runs.
Both sources use identical `PERF_SAMPLES` and `PERF_SECONDS` options. Counts are
calibrated separately per workload/process with all calibration batches saved.

`performance_schema.py` validates the entire ordered observation/check stream:

- `timer.accounting`: forced five-full-GC batch, then `check timer accounting`.
- `check workload inputs` (1,000 independent boolean rewrite assumptions).
- `storage`: exactly 0/10/100/1,000 rules, each followed by a retained-graph check.
- Each label in the fixed `LABELS` list: calibration events starting at one
  iteration and doubling until requested wall duration; then exactly the
  requested sample count of batch events followed by result checks.
- One final `sink`: exact sum of all timed consumed counts, not just nonzero.

All observations have three fields: `observation key comma-separated-numbers`.
Timing payload order is wall, non-GC user/system, GC user/system, inclusive
CPU user/system, `checkGCTime` user, and consumed count. Calibration prefixes
this with iteration count; batch prefixes with sample index then iterations.
All durations are seconds, indices/counts are integers. SML's `~` negative
exponents are normalized to `-` when parsing. NaN/infinity/negative durations,
incorrect consumption, CPU-accounting mismatch, wrong counts/ordering and
measured wall batches below half the target are errors, not noisy passes.
GC is included in CPU: it is **never added to CPU**. `checkGCTime` omits GC
system time; it is checked against GC user, not labeled total GC CPU.

Storage payload: rule count, base words, fragment words, simpset words,
equal-arity anchor words, union words, compiled increment, historical
increment, fragment anchor words, fragment union words, fragment increment.
Subtractions and integral word counts are checked. See the performance README
for exact root expressions and why historical increment differs by one word.

Performance receipts add `pair` and validated `measurements` (raw calibration/
batch metrics and storage). Test-count is 61 at five samples (2 initial,
4 storage, 11 x 5 results); footer pass and exit 0 are mandatory. There is no
outlier exclusion. The manifest adds `performance` options/order/outlier policy,
machine/affinity/load information, exact `ldd` output and runtime-library hashes,
and current-HEAD/working-source diffs against the reviewed implementation.
Inherited `PERF_*` and `LD_*` are stripped as well as existing HOL/Poly settings.
All `.json.gz` receipts keep unique diagnostics, events and path fingerprints.
`summarize.py` revalidates archived metrics, checks complete AB/BA pairs and
reports per-process medians, paired ratios and deterministic percentile
bootstrap intervals. Summaries hash every source receipt. These are diagnostic
intervals from six pairs, not final acceptance or independent clean builds.

## TASK_05 optional staged tactic fixture

`--staging-contracts` adds `Staging.sml`, actually elaborated through the same
Holmake-built state0 launcher on both selections. `--staging-only` executes
only that suite (no historical reproducer or signature probe). It requires
`--staging-contracts` and rejects combinations with the other optional suites
or old negative controls. The selected complete implementation must still
elaborate from its private path; all source/exit/footer checks still apply.

`staging_contracts.py` enumerates 43 cases and validates the shape of sealed
`staging/baseline.json` and `staging/reviewed.json` expectations. The existing
`--candidate-behavior` chooses the candidate expectation; baseline always uses
baseline. The reviewed choice means `expected-candidate-red`, even though the
launcher successfully captures the known wrong behavior and exits 0. Exact
ordered expectations are compared, not just counts or sets of observations.
A strict baseline-contract run on current sources must reject the new suite.
See `STAGING_CONTRACTS.md` for stage meanings and every baseline outcome.

Each scenario has `NAME.construct.{prims,callbacks,outcome}`, followed by either
`NAME.uses = unavailable` (construction raised) or measured `NAME.first` and
`NAME.second` application stages. Returned applications additionally require
`NAME.USE.goals`, `NAME.USE.proof.{prims,callbacks}`, `check NAME.USE proof pass`,
`NAME.USE.theorem` and `NAME.USE.oracles`, in precisely that order. The theorem
is the result of actually calling the returned validation with genuine kernel
subgoal proofs; no `VALID` oracle surrogate is used. Only `DISK_THM` dependency
tags are allowed. Encodings preserve full constant/variable/type identities,
ordered assumptions/goals and reconstructed hypothesis sets/conclusions.
They do not invoke term printers. Metrics are exact nonnegative decimal
integers, callbacks are ordered strings, and exception messages are escaped.
Unexpected exceptions in residual proving or reconstruction fail the process.

After malformed-bound scenarios, the separate `negative_bound.argument` stage
must raise exactly the documented argument-constructor HOL error. After all
scenarios, three validator control checks must reject wrong conclusion, foreign
hypothesis and oracle-tagged theorem; `validations.executed` must equal the
number of successful real reconstructions. Footer counts are 60 develop / 57
initial candidate; real validations are 57 / 54. All stage/proof observations
are mandatory even for unchanged or fully solved goals.

The manifest uses `evidence_id: TASK_05-staging-contracts-v1`, adds
`staging_contracts` with sealed input references, selected expectation and
reviewed-to-selected / working simplifier source diffs. Inputs include the
fixture, both expectations, seals and validator/tests. A standalone strict
red receipt retains the full executed stream and exit 0, with `accepted=false`
and a nonzero driver exit: captured incompatibility is distinct from an
unexpected process failure. No expected static errors are permitted here.

## TASK_06 optional prior contracts

`--prior-contracts` installs the unchanged original selftest assertion body,
unchanged traversal/exclusion modules, and `paired/PriorLimits.sml` into each
private tree. Only final driver exits are replaced by a paired completion
check (including checking original `failcount = 0`). No assertion, callback,
warning, error predicate or observation is edited. Each wrapper's bytes are
in the manifest; the original selftest must still equal pinned Git bytes.

The old suites require 73/47/929 actual OK results, respectively, plus their
additional completion check. `prior_contracts.py` compares every ordered check,
OBS event and warning header with the immutable review input; duplicate cases
are retained. The new six-case limits fixture requires all six exact protocol
checks. Prior receipts have a `prior` field with classification, exact counts
and the full semantic stream. There is **no expected-red mode** for these
suites. The separate original staging/signature probes keep their existing red
classifications and original nonzero signature process exit.

Terminal color/padding, testutils timing/backspaces and theory build times are
presentation/build noise only. Callback/warning/exception OBS payloads are not
normalized. Full diagnostics (including build timing) remain in receipts. The
native suite can interleave monitor output between a test label and its OK;
the parser requires the eventual OK, not merely a displayed test label.

`run_prior_native.py` executes current native/focused launchers and six separate
fresh-load processes, then freshly builds parent/child/descendant exports in a
temporary fixture directory and runs all eight persistence/heap scenarios. It
checks exact identity assertions really ran and compares native/traversal/
exclusion streams to immutable inputs. With `coverage-ledger.json.gz` present,
every native suite additionally requires its complete frozen ordered stream.
Only the fresh-load reported module path is rendered `$REPO` in that ledger;
the actual absolute path stays in raw receipts. Tools, input hashes, launcher
text, native products, commands, environments and process exits are recorded.
These are native current products, not an independent clean repository build.

`coverage_ledger.py` verifies 2,153 stable ordered case IDs, source hashes and
textual source anchors, including parameterized labels and duplicate cases.
Anchors are navigation aids (not an SML parser); whole source hashes bind the
actual assertions. `PRIOR_CONTRACTS.md` disambiguates family scopes, matrices,
legacy-equal contracts, native/branch-only semantics and initial red owners.
Regenerating a ledger is explicit and refuses to overwrite an existing file;
test runs never update it to accommodate changed or missing tests.
