# Supplemental TASK15 legacy fragment routes

Owns only this directory. No parent fixture, production source, pinned input,
old assertion, or historical evidence is changed. Uses baseline-only public
`simpLib`/`Traverse.REDUCER` APIs and the existing Paired/testutils reporter.

## Commands (run only while benchmarks/builds are idle)

From the repository root, with existing shared build prerequisites available:

```sh
python3 -B src/simp/tests/fragments/routes/run_routes.py \
  --output /tmp/task15-routes-current-UNIQUE
```

The baseline is pinned to compatibility `run_paired.BASE`
(`cccaa27d7099cbadc886983020cbe745db7793f3`); candidate defaults to the actual
worktree, including uncommitted root/poly simplifier modules. For a same-source
harness control (not candidate acceptance):

```sh
python3 -B src/simp/tests/fragments/routes/run_routes.py \
  --candidate cccaa27d7099cbadc886983020cbe745db7793f3 \
  --output /tmp/task15-routes-base-control-UNIQUE
```

Pure Python schema/mutation tests (no build or benchmark; the parent's
nonrecursive discovery does not include this directory):

```sh
python3 -B -m unittest discover \
  -s src/simp/tests/fragments/routes -p 'test_routes.py' -v
```

Standalone Holmake integration (also isolated; no production targets):

```sh
bin/Holmake --no-project --no_prereqs \
  -C src/simp/tests/fragments/routes -j1 python-tests check
```

`--no-project` is required: the root `holproject.toml` sets `holmake = false`.
`--no_prereqs` prevents recursive prerequisite builds. The `check` target runs
only `run_routes.py` with temporary receipts and cleans them afterward; use the
Python command above for durable receipts. Do not directly build
`selftest.exe`: the SML fixture requires the driver's `Paired` bootstrap.
Private launcher builds additionally use `--no-cache`, `--no_prereqs`,
`--no-project`, and explicit `--holstate=.../bin/hol.state0`. They seal and
check the fresh process's runtime, heap, private paths, and generated
dependencies.

## Contract

- Exact, unnormalized `pp_ssfrag` output at widths 40 and 80, emitted as escaped
  full strings: named/anonymous rewrite names, theory-qualified/local names,
  keyed/unkeyed conversions, AC pairs, duplicate/anonymous opaque reducer
  names, update reversal, duplicate merge, persistence. Printing must not run
  reducers.
- `ssfrags_of`: newest-first original fragment content, duplicate named and
  anonymous retention; `ssfrag_names_of`: legacy last-occurrence dedup order.
  Deletion history events must not appear as fragments.
- Original filter mechanism: a fragment's own payload bypasses its filter;
  subsequent installations invoke it. Repeated merged payloads/installations
  retain all maker/conversion/collector events. Collectors receive the original
  theorem sequence, including duplicate conclusions and full hypothesis sets.
- AC makers precede ordinary makers; **all** makers precede conversions and
  collectors. A later throwing maker preserves exception identity and prevents
  every conversion/collector. Malformed ordinary bound tags raise `Option`
  before effectful/throwing makers, with and without AC payloads. An invalid
  AC pair's public normalization diagnostic is a sensitivity control: malformed
  tags must prevent even that observable AC effect (with either maker).
- Excluded `++` skips malformed tags, throwing makers/collectors, and history.
  `force_add` reinstalls the name and clears exclusion for subsequent `++`,
  preserving duplicate history. With the event collector, whose `apply` raises
  `UNCHANGED`, the exact legacy proof is closed reflexivity (see below).
  Separate collector-free force/add-again probes must produce `r2`, including
  its nonempty hypothesis set.
- Proof assertions compare the entire conclusion (not only the RHS) and exact
  hypothesis sets. Nonempty-hypothesis rewrite proofs and unchanged proofs are
  included. These checks do not accept extra hypotheses or subgoals.

## Isolation, acceptance, and limitations

`run_routes.py` reuses the parent `run_fragments.snapshot` and compatibility
`run_paired` fixture installation, launcher execution, strict protocol/path
validation and compact evidence helpers. Both sides are temporary private
source trees and fresh processes with private-first loading. No repository
build outputs are modified. Private trees are removed on success/failure;
unique output directories preserve receipts, failures, hashes and manifests.
Only private launchers are built, using already-built shared dependencies.

Acceptance requires the fixed ordered event schema, every counted testutils
check, correct process exit/footer, traced private simplifier sources, stable
source/tool/dependency fingerprints, and **byte-for-byte equality of every
baseline/current observation**, including full rendering strings. There is no
candidate-specific expectation, assertion removal, normalization, timing
allowance, or golden regeneration mode. Python mutation tests supplement (do
not replace) the existing Paired exit/header/path/footer validation.

## Baseline proof diagnosis and validation

The original failure was an incorrect expected theorem, not a missing
hypothesis that should be ignored. The pinned baseline's full result with the
event collector is:

```text
actual:   []        |- (T /\ route_q) = (T /\ route_q)
old r2:   [route_h] |- (T /\ route_q) = route_q
```

The collector's `apply` raises `Conv.UNCHANGED`. Legacy traversal propagates
that after the rewrite, discarding the intermediate proof; `QCONV` returns
`REFL (lhs (concl r2))`. Both force/add-again checks now require precisely that
full theorem, **including its empty hypothesis set**. The unchanged `sameTh`
compares full conclusions with `aconv` and exact `HOLset.equal` hypothesis
sets. Collector-free force/add-again checks separately require precisely `r2`,
including `route_h`. No assertion accepts missing/extra hypotheses. Proof
mismatches print actual and expected conclusions and all hypotheses before the
ordinary failing testutils check.

This is isolated-source compatibility evidence, not independent full builds,
allocation/performance evidence, or proof of every simplifier route. AC order
is observed via a public invalid-pair diagnostic with a positive sensitivity
control, not a production-instrumented entry counter. Valid-pair cases also
check downstream maker/conversion/collector order.
