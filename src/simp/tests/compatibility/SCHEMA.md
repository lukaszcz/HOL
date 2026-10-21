# Paired evidence schema v1

`run_paired.py` is the executable validator for these schemas. Unknown protocol
kinds, wrong arities, reordered/missing/duplicate events, mismatching source
paths/hashes, wrong process exits and timeouts are errors. `test_runner.py`
mutates valid receipts to exercise the validator independently of HOL.
All counts are exact, not minima. No timing samples are defined in TASK_02.

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
   only permitted unfinished use is expected-red `SignatureCheck.sml`.
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
  and project config; `poly_version`: captured process receipt.
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
is never a test result. `poly_version` additionally retains stdout inline.

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
