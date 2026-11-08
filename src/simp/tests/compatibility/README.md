# Simplifier compatibility inputs and gates

Tools, pinned inputs and gates that compare the simplifier sources against
pinned Git revisions.  Ordinary develop clients need no migration; tracked
construction is explicit for branch-only extensions.  Receipts and results of
runs are not stored in the repository: every runner takes an explicit
`--output` directory outside the tree, and the Holmakefile has no default for
`PAIRED_OUTPUT`: it refuses an unset, relative or in-repository path.

## Layout

- `run_paired.py`, `paired/`, `SCHEMA.md`: the fail-closed paired runner and
  its result schemas (below).
- `public_contracts.py`, `staging_contracts.py`, `prior_contracts.py`,
  `normal_integration.py`, with `PUBLIC_CONTRACTS.md`, `STAGING_CONTRACTS.md`
  and `PRIOR_CONTRACTS.md`: the public-client, staging and prior contract
  suites run through the paired runner (`public/`, `staging/`, `inputs/`).
- `coverage_ledger.py`, `coverage-ledger.json.gz`: the
  source-tied case ledger; relocations are explicit overlays
  (`task10_relocation.py`, `task26_relocation.py`, `migration/`).
- `audit_task14.py`, `audit_task16.py`, `audit_task27.py`,
  `check_task27_docs.py`: offline source-correspondence and documentation
  gates (`task16-source-manifest.json` is the manifest `audit_task16.py`
  validates and `audit_task27.py` reuses).
- `run_prior_native.py`, `run_task22_negative.py`, `run_task23_lifecycle.py`,
  `run_task24_recipes.py`, `run_task25_consumer.py`: executing drivers; each
  requires `--output`.
- `consumer/consumer.patch`: the patch `run_task25_consumer.py` applies to
  its isolated external consumer checkout (`--consumer-patch`).
- `tools/root-wrapper.sh`: runs a command in a checkout whose configured root
  (`HOLDIR` in `tools/Holmake/Systeml.sml`) differs from its real location,
  using `bwrap` to map the checkout at the configured root.  It needs no
  editing: the checkout is the git work tree containing the script, and
  `HOL_CHECKOUT` and `HOL_CONFIGURED_ROOT` override it and the detected
  configured root.  The command runs from the checkout root (the configured
  root when mapped), directly when the two paths are equal.  Apart from the
  configured root the host is visible, including `/dev/shm`; directories the
  mapping creates on the host are removed afterwards if empty.  Exit status 2
  means no command, no git work tree, no configured root, no `bwrap`, an
  ancestor of the configured root that is not a writable directory, or a
  configured root that exists but is not a directory; otherwise it is the
  command's status.
- `tools/require_output.py`: the Holmakefile's output-directory check.
- `interfaces/`, `migration/`: design prototypes and the API mapping tables
  (`apis.tsv`, `final-apis.tsv`) and relocation overlays; see
  `interfaces/README.md`.

`inputs/develop/prior-streams.json.gz` is the oracle of the prior contracts:
for each prior fixture, the ordered semantic stream (`semantic_stream` in
`prior_contracts.py`) that a complete run keeps.  See `historical` there for
how it is produced.

`inputs/develop/selftest.sml` is the **unchanged original** develop selftest,
recovered with `git show <develop>:src/simp/src/selftest.sml`, and
`inputs/develop/Traverse.sig` is likewise the exact original public signature.
Keep both immutable; add new contracts alongside them, not inside them.

Pins: develop is `cccaa27d7099cbadc886983020cbe745db7793f3`.

## Tests

```sh
cd src/simp/tests/compatibility
python3 -B -m unittest discover
python3 -B -m unittest discover -s interfaces
```

Some tests need a built checkout (`bin/holdeptool.exe`).

## Reproduction rules

Tooling prerequisites: local Git objects for both pins, Python 3.9 or newer,
and the configured Poly/ML/HOL tools.

1. Use the configured repository's `bin/Holmake`, `bin/hol` and
   `bin/hol.state0`, with absolute tool, heap and include paths; do not
   rely on an inherited `HOLDIR`.  Pin all compiler/runtime/heap options
   identically for both versions.  Fresh setup, if necessary:
   `poly < tools/smart-configure.sml` and build prerequisites using
   `CLAUDE.md`'s heap bands.  Do not copy build trees.
2. Extract each revision's exact simplifier sources into separate temporary
   directories.  Do not let candidate `.uo`, theory products or stale
   launchers leak into the baseline.  Record effective loaded module paths,
   not merely intended search paths.
3. Build executable Holmake fixtures and **execute their launchers**.  A `.uo`
   or successful Holmake invocation alone does not establish SML elaboration.
   Observe process exits and complete ordered output.  Use selftest/testutils
   conventions; never pipe SML into `bin/hol` as a regression test.
4. Keep isolated-source comparisons distinct from independent clean builds.
   Graph-size results are reachable words, not RSS or byte counts.
5. Remove temporary sources/products after their last use, and always select
   a fresh output path outside the repository.

The downstream-consumer driver is documented in its module docstring and
`--help`; it is run as

```sh
python3 -B src/simp/tests/compatibility/run_task25_consumer.py \
  --consumer-patch src/simp/tests/compatibility/consumer/consumer.patch \
  --output /path/outside/repo
```

## Executable paired gate

Use a **new** output directory on every invocation. From the repository root:

```sh
bin/Holmake --no-project --no-cache --no_prereqs \
  --holstate="$PWD/bin/hol.state0" \
  -C src/simp/tests/compatibility -j1 \
  PAIRED_OUTPUT=/tmp/my-paired-output check
```

`PAIRED_OUTPUT` is required and must be an absolute path outside the
repository.  This runs the Python validator tests (`checked-tests`, after the
`output-dir` check), then private Holmake-built SML launchers for both exact
pinned source revisions, including all six negative controls. No SML is piped
to `bin/hol`. Expected reviewed-candidate staging/signature regressions are
explicitly **expected-red**, not compatibility passes.

Direct driver and baseline-versus-baseline control:

```sh
python3 -B src/simp/tests/compatibility/run_paired.py \
  --negative-controls --output /tmp/my-paired-run
python3 -B src/simp/tests/compatibility/run_paired.py \
  --candidate cccaa27d7099cbadc886983020cbe745db7793f3 \
  --candidate-signature pass --candidate-behavior baseline \
  --negative-controls --output /tmp/my-baseline-control
```

For future repairs explicitly select `--candidate HEAD` (or another Git ref)
and choose `--candidate-signature pass` / `--candidate-behavior baseline` only
when those contracts are intended to pass. Defaults reproduce the reviewed
candidate, NOT an implicit dirty-worktree snapshot. Dirty sources are never
silently substituted for a selected Git object. Resolved revisions, exact
Git blobs/source bytes, generated products, inputs, runtime/heap/config
fingerprints, commands, exits and complete ordered source/observation streams
are retained in compact JSON/gzip receipts. The output folder is never reused.

See [`SCHEMA.md`](SCHEMA.md) for ordered event/result contracts and controls.
`paired/Holmakefile` is an installation template, not a standalone
source tree: the driver adds the exact Git modules and signature fixture to
private directories before invoking it. `paired/selftest.sml` follows the
normal testutils convention; the deliberately ill-typed `Deferred.sml` is a
harness-only control, never a production import.

### Isolation limits

These are **mixed-source isolation experiments**, not independent repository
builds. Both sides use today's same prebuilt HOL runtime, state0/min heaps and
shared libraries. Initial heap source maps are metadata, not proof that current
source bytes built those heaps. The driver rejects preloaded simplifier modules,
forces identical private-first search paths, traces actual source elaboration,
audits complete source inventories, and checks source/product hashes again
before cleanup. Shared products are not rebuilt. Undeclared dynamic loads fail
closed if they extend the source map without a traced use.

This is not an OS security sandbox, a certified clean build, a downstream
loading test, or a performance measurement. Do not mutate dependencies or run
builds concurrently; fingerprints detect changes but do not provide filesystem
locking against malicious transient edits. Launcher/compiler/runtime are
trusted. Tested scope is the configured Linux/Poly/ML runtime only. Timing
calibration and performance probes live under `../performance`;
independent clean builds are separate gates.
