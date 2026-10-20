# Simplifier compatibility evidence and differential harness

This directory is the maintained evidence location for the compatibility
plan. Start with [BASELINE.md](BASELINE.md) for the pinned revisions,
provenance and initial checks. [LEGACY_FAILURES.md](LEGACY_FAILURES.md)
records TASK_02's eleven red regressions and repair handoff.
[FRESH_LOAD.md](FRESH_LOAD.md) records TASK_03's clean-heap namespace
regressions and explicit red targets. Those baseline tasks do not change
implementation APIs or weaken legacy expectations.
[TRAVERSAL_PROJECTION.md](TRAVERSAL_PROJECTION.md) records TASK_04's restored
public legacy projection, caller audit and passing focused/sanity checks.
[TRAVERSAL_LIFETIMES.md](TRAVERSAL_LIFETIMES.md) records TASK_05's shared
quota, staging, default and exception contracts and pinned differential.
[EXCLUSION_ROUTES.md](EXCLUSION_ROUTES.md) records TASK_07's literal Excl /
explicit ExclX routing, normal prefix coverage and replay handoff.
[EXCLUSION_HISTORY.md](EXCLUSION_HISTORY.md) records TASK_08's replay
representation, split/case restoration tests and strict dotted-name pins.
[EXCLUSION_MATRIX.md](EXCLUSION_MATRIX.md) maps TASK_09's full literal /
explicit namespace contract to native and pinned-develop tests, including
warning-sensitive errors, suffixes and genuine current-theory changes.
[SPLIT_REGISTRATION.md](SPLIT_REGISTRATION.md) records TASK_10's explicit
opt-in, context/registry ownership, passing clean-load probes and replay
ordering contract for TASK_11.
[SPLIT_PERSISTENCE.md](SPLIT_PERSISTENCE.md) records TASK_11's opt-in module,
exported dependency ordering, persistent removals and fresh parent/child/
descendant fixtures.

## Layout

- `inputs/develop/selftest.sml`: **unchanged** pinned develop selftest.
  Never edit it to accommodate the implementation branch.
- `inputs/investigation/`: historical reproducers and selected original
  results from `/tmp/hol-simp-compat.H6G7y2/`. These are archival inputs,
  not new runs or maintained regressions. See BASELINE.md for provenance.
- `inputs/SHA256SUMS`: SHA-256 of every preserved input, relative to here.
- `probes/legacy/*.sml`: maintained, legacy-only differential inputs.
  Each becomes `selftest.sml` verbatim and runs unchanged in both lanes.
  `control.sml` is the ordinary-simplification control. `reducer-shape.sml`
  and `excl-{rule,solver,looper,split,case}-{unmatched,installed}.sml` are
  eleven independent regression executables, not xfails; all are repaired
  by TASK_04/TASK_07. The ten prefix cases also run in normal Holmake tests.
  `traversal-lifetimes.sml` runs the legacy-only `TraversalContracts` fixture
  against both lanes; the same fixture runs in normal Holmake selftests.
  `exclusion-history.sml` runs `ExclusionHistory` in both lanes and normal
  exclusion-contracts coverage: strict dotted replay, context restoration,
  unmatched/repeated deletions and interleaved additions.
  `exclusion-parsing.sml` runs `ExclusionParsing`: Excl / `-*` strict
  parser/error/warning parity, numeric/dotted rewrite suffixes, exact dproc
  spelling, bare kernel strings, repetitions and current-theory replay.
- `probes/support/*.sml`: shared legacy-only assertion helpers, snapshotted
  once, hashed as `support_sha256`, and copied into each suite directory.
  Holmake discovers and builds these modules through ordinary dependencies.
- `probes/branch/`: branch-only API expectations, never differential inputs.
- `probes/fresh-load/`: separately linked fresh-load launcher and deferred
  control. Run with `fresh_load.py`, not the ordinary `run.py`: ordinary
  suite imports preload `simpLib`. See its README for isolated scenarios,
  preloading checks and native Holmake targets.
- `probes/split-persistence/`: real exported theory chain and separately
  linked fresh-process importer. `split-persistence` runs six import/owner
  scenarios under normal Holmake selftests; see SPLIT_PERSISTENCE.md.
- `results/taskNN/`: named result records for subsequent tasks. Keep
  commands, exact revisions, input hashes, exit codes, and compact logs.
  Do not replace historical evidence with a later run under the same name.

## Reproduce

Prerequisites: configured Poly/ML HOL checkout, Python >= 3.9, both git
objects available, and host dependencies built through `src/simp/src`.
This is not a bootstrap tool. Do not run competing builds in the host tree.
From the repository root:

```sh
# If configuration/products do not exist:
poly < tools/smart-configure.sml
# Prepare/check the host dependencies, not an independent develop tree:
bin/build -t --seq=tools/sequences/upto-parallel

(cd src/simp/compatibility && sha256sum -c inputs/SHA256SUMS)
python3 src/simp/compatibility/run.py \
  --branch 62a6bdc3453c29e8f31faa72f2b70a245f44840d \
  --output /tmp/compat-task01-new-results
```

The output directory must not exist. Choose a unique path for each run.
For later implementation commits use `--branch <commit>` (default HEAD).
To select focused legacy probes, repeat `--suite <probe-stem>`; `control`
and the unchanged develop selftest always run. Unknown names are errors.
With no `--suite`, all probes run, including the literal exclusion
regressions. For the focused TASK_05 scope:

```sh
python3 src/simp/compatibility/run.py --branch HEAD \
  --suite traversal-lifetimes --suite reducer-shape \
  --output /tmp/compat-traversal-new-results
(cd src/simp/src && ../../../bin/Holmake --no-project --no-cache -j1 \
  --holstate="$HOLDIR/bin/hol.state0" traversal-contracts)
```

`$HOLDIR` is the absolute repository root. The normal `HOLSELFTESTLEVEL`
build also runs `traversal-contracts` and `exclusion-contracts`, alongside
`simp-selftest.log`. TASK_10 also enables `fresh-load-regressions` and
`split-registration` in normal selftests. TASK_11 adds `split-persistence`.
The exclusion target runs all ten
prefix fixtures, including
silent unmatched names, real conversion/callback preconditions, named
rewrites and dprocs, overlapping names, deletion and direct `-*`
comparisons/replay, plus the legacy-only history and parser fixtures. The
traversal target's
support-directory Holmakefile resolves private simplifier modules before
upload to `sigobj`, and the launcher executes from that directory. It
records all trace actions, ordered callbacks, warnings (also forwarded to
the original sink), and expected exceptions without stripping diagnostics.

Only **committed** library sources are staged; uncommitted library edits
are not tested. Probe bytes are snapshotted once from this directory and
hashed before either lane. The reference is hard-coded to
`cccaa27d7099cbadc886983020cbe745db7793f3`, never a moving branch tip.

`run.py` performs these Holmake commands, sequentially in private directories
under a single `tempfile.TemporaryDirectory` (`$WORK`):

```sh
# In $WORK/{reference,branch}/lib; TARGETS is every staged *.sml -> *.uo:
$HOLDIR/bin/Holmake --no-project --no-cache --no_prereqs -j1 \
  --holstate=$HOLDIR/bin/hol.state0 $TARGETS
# In each lane's control/ and develop-selftest/ (or other legacy probe):
$HOLDIR/bin/Holmake --no-project --no-cache --no_prereqs -j1 \
  --holstate=$HOLDIR/bin/hol.state0 selftest.exe
./selftest.exe
```

The generated library Holmakefile sets
`HOLHEAP = $(HOLDIR)/bin/hol.state0`. Each suite Holmakefile adds
`INCLUDES = ../lib` and the normal target:

```make
selftest.exe: selftest.uo
<TAB>$(HOLMOSMLC) -o $@ $<
```

Replace `<TAB>` with the TAB required by Holmake recipe syntax.
No SML is piped into `bin/hol`. Poly Holmake generates load recipes and an
executable; runtime compilation errors are failures too, so **both build
and executable exit codes matter**.

## Isolation and provenance

The runner stages git-versioned simplifier `.sig`/`.sml` library sources,
including `poly/BloomApprox`, and markerLib/markerSyntax, separately for
each revision. It also stages Q/QLib from each revision: a shared host Q
recipe otherwise names the host markerLib. These Q sources are identical
at the initial pins. Script sources, generated theories, source selftests,
source Holmakefiles and existing products are not copied. Each suite gets
its own unchanged input, Holmakefile, `.hol` products, process and theory.
The two lanes never publish products to `sigobj` or share staged products.
The runner deletes its private copied sources, objects, and executables on
success or exception; only result records survive.

Before running each executable, the runner follows its Poly `.uo`/`.ui`
recipes and rejects references to staged module names outside that lane's
library. It fingerprints the shared recipes, interfaces, named sources and
generated theory data (including shared markerTheory). Some core recipes
name absent old per-directory Overlay/Table paths; these are preloaded
module aliases, recorded explicitly in `installed_recipe_aliases`, with
the installed sigobj recipe fingerprinted instead. Missing other inputs
without an installed recipe are errors. Tool and shared-input hashes are
rechecked at the end to detect changes during the run.

**These are mixed-source tests, not independent repository builds.** Both
lanes still use the host kernel, `hol.state0`, generated markerTheory,
other generated theories, dependencies, executables, and runtime. Hashes
identify that environment, not proof that every generated product was
rebuilt from its claimed git source. The recipe audit is not a dynamic
trace of every loader action or of the already-loaded heap. Native/runtime
libraries and arbitrary callback I/O are not exhaustively inventoried.
The implementation branch's ordinary load-time state can differ from the
reference; separate fresh-process tests must test that, not mask it.

## Observable results and interpretation

`manifest.json` records source revisions/hashes, input hashes, tool hashes,
working-tree state at invocation, exact argv/cwd/exit codes, loader-audit
results and shared-input hashes. `$WORK` and `$HOLDIR` in commands are
substitutions documented above. Each command's `*.log` retains stdout and
stderr combined, in emitted order, without dropping warnings or exceptions.
Some logs contain ANSI colors, backspaces, timing and temporary paths.
Do not claim that differing raw logs are equal after silently normalizing
away relevant output. Successful library builds can have empty logs.

New probes should use testutils (`tprint` with `OK`/`die`, or `convtest`),
fail the process on mismatches, and emit stable `OBS <label>=<value>` lines
for the contracts they expose. The runner compares the complete ordered
OBS lists for each instrumented suite and fails on differences. Empty OBS
lists are recorded as `null` comparisons, **not** observational equality.
It requires a nonempty, equal control trace and all build/run exits zero.
A deliberately red probe therefore makes this runner fail; record its
precise expected failure separately rather than treating that as a pass.
The default run now includes all TASK_02 probes: at the original audited
revision it exits 1 after running every suite on both lanes. This is the
separate pre-repair red-regression target. TASK_04 repairs the constructor
failure and includes it in normal `src/simp/src/selftest.sml` coverage;
TASK_07 repairs the ten exclusion failures and adds their normal coverage
as the `exclusion-contracts` target. Historical red results are unchanged.

Capture each relevant observable, not merely the final RHS:

- **Theorems:** assert and record conclusions and hypotheses (`concl`,
  `hyp`, `aconv`). Pretty printing is human evidence, not alpha-equivalence
  checking. The control checks both and emits their printed forms.
- **Exceptions:** do not swallow unexpected exceptions. Preserve raw
  diagnostics and nonzero exits. For expected failures, record constructor
  identity and HOL_ERR origin/function/message using Feedback's accessors,
  or `Feedback.exn_to_string`; generic `exnMessage` alone can lose detail.
  The control records `exception=none` only after all operations succeed.
- **Warnings:** retain raw combined output, including warnings at module
  load. Where exact frequency/staging matters, wrap and forward
  `Feedback.WARNING_outstream` around the operation, recording each event
  in order, and restore the original sink even on exceptions. Do not turn
  warnings off. The current control emits no warnings; it is not a
  warning-staging regression test.
- **Callbacks:** record ordered entry/exit events, not just a final count;
  distinguish simpset construction, projection and application. The
  control records a simple `std_conv_ss` callback trace (`p`). More complex
  factories, quotas and lifetime contracts need separate maintained probes.
- **Tactics:** compare subgoals/assumptions, then invoke the returned
  validation with proved subgoals and check its theorem and hypotheses.
  Use `VALID` as well. The control closes a goal and checks `validation []`;
  inspecting only the returned subgoal list would be insufficient.

The unchanged develop suite retains its original assertions and exit
behavior (including validation checks). Its green status is not a trace
comparison of every operation. Passing finite probes is not universal
compatibility, nor completion of subsequent repair/validation tasks.
