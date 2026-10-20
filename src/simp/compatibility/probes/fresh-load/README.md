# Fresh-process load-order regressions (TASK_03)

These are legacy-only tests, not extensions/opt-in tests. The same launcher
and control bytes run on pinned develop and the implementation. No scenario
is an xfail: every assertion expresses namespace-neutral loading, and a
load error or warning fails the executable. TASK_10 repairs registration;
the original five targets now pass and run in normal selftest coverage.
TASK_12 also runs a native `syntax-first` scenario and exact handler-record
checks. Retained TASK_03 results still show the original four failures.

## Runnable targets

From `src/simp/src` (use this checkout's absolute path for `$HOLDIR`):

```sh
$HOLDIR/bin/Holmake --no-project --no-cache --no_prereqs -j1 \
  --holstate=$HOLDIR/bin/hol.state0 fresh-load-control
# All six native scenarios, continuing after failures; exits 0:
$HOLDIR/bin/Holmake --no-project --no-cache --no_prereqs -j1 \
  --holstate=$HOLDIR/bin/hol.state0 fresh-load-regressions
```

Individual targets: `fresh-load-{control,attribute-first,set-first,
attribute-after,set-after,syntax-first}`. The aggregate runs under
`HOLSELFTESTLEVEL`.
`fresh-load-selftest.exe` is built with the normal
`$(HOLMOSMLC) -o` recipe, linking **only** this directory's `selftest.uo`.
Library prerequisites ensure dynamic recipes exist; they are not linked.
This directory's Holmakefile selects `hol.state0` explicitly as well.

Paired, audited execution from the repository root:

```sh
python3 src/simp/compatibility/fresh_load.py \
  --branch 62a6bdc3453c29e8f31faa72f2b70a245f44840d \
  --output /tmp/compat-fresh-new-results
```

Choose a nonexistent output directory. `--scenario <name>` selects one
scenario (repeatable); default is the original five. Library sources are staged
from committed revisions, not the working tree. Each lane builds one
clean launcher; **each scenario invokes a new OS process**, with its own
theory and registries. Environment variables select the scenario, absolute
lane-local `simpLib` recipe, and deferred `control.ML`. Output retains raw
combined diagnostics/warnings and ordered, single-line `OBS` records.
`manifest.json` records inputs, source pins, heap/tool/shared-input hashes,
recipes, audits, commands, exits and runtime precondition results. It also
compares every ordered contract observation across lanes. Only `load.path`
is treated separately: each must equal its actual private library path.
Original observations are retained. Exit 1 is a real regression failure,
not an expected-failure success status.

## Why this launcher really is clean

A fresh process is necessary but insufficient. Three checks are combined:

1. `fresh_load.py` recursively audits the launcher's `.uo` **and** `.ui`
   closure, rejecting `simpLib` and `splitLib` anywhere in the recipes.
   All 156 launcher recipe modules are retained in the TASK_03 manifest;
   no staged simplifier/marker module is imported. The separate dynamic
   load audit rejects host fallback for lane-local library modules.
2. Before custom registration or dynamic loading, the launcher asserts
   both `Meta.loaded ()` and `PolyML.globalNameSpace.lookupStruct` lack
   `simpLib`, `splitLib` and `splitPersistLib`. This checks the initial heap plus all
   transitive launcher imports, not just source dependency declarations.
3. Both `ThmAttribute.is_attribute "split"` and
   `ThmSetData.all_set_types ()` must report unclaimed. This also rules out
   offending registration in a heap even if no structure/loader name
   exposes it. Only then is `OBS precondition=clean` emitted.

The launcher imports the kernel, testutils, boolean theory/syntax and
registry APIs, and creates a fresh theory. It does **not** statically refer
to simpLib, splitLib or boolSimps. `Meta.load` receives the lane's absolute
recipe path only after the preconditions and optional custom registration.
`control.ML` is compiled via `Meta.qquse` only after that load succeeds;
its simpLib references cannot become launcher dependencies. The ordinary
control additionally dynamically loads lane-local boolSimps and verifies
`T /\ fresh_control_p = fresh_control_p`, including empty hypotheses.

## Identity, isolation and limitations

- `attribute-first`: registers local/stored handlers only (set registry
  stays absent), exercises both before and after the attempted load, and
  checks the exact callback order and all arguments, including theorem
  conclusion and hypotheses. A no-op or overwritten handler cannot pass.
- `set-first`: registers a foreign `ThmSetData.new_exporter`, saves and
  exports a non-split theorem with one hypothesis, and checks the exact
  singleton ADD delta/name/theorem before and after attempted loading.
  It retrieves `data_exportfns` again and invokes add/remove to verify the
  registry still points to the foreign callbacks, not just stale handles.
  The public legacy exporter necessarily also registers a same-named
  attribute: there is no public set-only constructor/unregister operation.
  This scenario uses a **separate process** from the attribute-only test;
  it proves exporter/data preservation but cannot attribute the collision
  solely to a theorem-set-only ownership conflict. No private
  registry mutation or test-only registration repair is used.
- `attribute-after` / `set-after`: each loads simpLib with no custom owner,
  records **both** registries, runs ordinary simplification, then attempts
  custom registration even if a namespace is already occupied. This
  preserves replacement-warning identities/counts before asserting both
  registries were free and custom registration was silent.
- `control`: normal dynamic load and ordinary simplification, without
  custom ownership. It records but does not assert namespace neutrality;
  this control must pass even while collision regressions remain red.

- `syntax-first` (native only): installs unrelated `Split` and `ExcludeX`
  overloads before loading simpLib, verifies those exact interpretations
  survive, and checks qualified marker constants and unclaimed registries.
  `syntax.ML` is used only after dynamic loading.

Native Holmake targets additionally set `SIMP_COMPAT_IDENTITY_PREFIX` to
load `identity-{before,after}.ML` around the owner-first dynamic import.
These check pointer identity of both handler records. The new attribute
inspection accessor is deliberately absent from the shared launcher's
static dependency closure; pinned develop runs omit these native helpers
and retain their original callback/data assertions.

Observed operations forward every warning to the original sink, then
restore it. Exceptions record constructor plus `Feedback.exn_to_string`
(origin/function/message for HOL_ERR). Owner-first catches the load error
only to check foreign ownership/data afterward, then fails the process.
No retry, error swallowing, registration repair, or extension API is used.

This shares TASK_01's mixed-source provenance limitations: host kernel,
heap, dependencies and generated markerTheory are shared, not independent
repository builds. Runtime checks establish the needed clean state in
this environment; they do not claim an exhaustive dynamic loader trace.
For retained before-fix evidence, results and repair handoff, see
[../../FRESH_LOAD.md](../../FRESH_LOAD.md).
