# TASK_03: genuinely fresh-process load-order regressions

Landing identifier (commit subject):
`[TASK_03] Add clean-heap dynamic-load namespace regressions`.

## Scope and finalized decisions

- Reference: `cccaa27d7099cbadc886983020cbe745db7793f3` (fixed develop).
- Tested implementation: `62a6bdc3453c29e8f31faa72f2b70a245f44840d`.
- Entry HEAD: `ac0c5a1a5` (TASK_02); the two intervening task commits add
  harnesses/evidence only, with no implementation repair.
- Existing branch `simplifier` retained. No branch/reset/merge operation.
- A caller edit to `.agent-files/tasks/PROGRESS.md` clarified TASK_02's
  status/commit ID before this task; it is preserved.
- No simplifier/marker implementation, ordinary selftest, frozen develop
  input or registration behavior changed. Finalized API decisions: none.

Changed files: `probes/fresh-load/{selftest.sml,control.ML,Holmakefile,
README.md}`, `fresh_load.py`, shared `run.py` audit (optional required and
forbidden modules plus recipe-module inventory), compatibility README,
`src/simp/src/Holmakefile` (explicit separate targets), this handoff,
`results/task03/`, and task progress.

All TASK_03 acceptance criteria are satisfied as a **before-repair red
regression task**, not a compatibility repair. No TASK_03 blocker remains.
Four namespace-neutrality tests still fail on the implementation, as
required to expose the defect. They are not counted as passing tests.
The scope does not include persistent opt-in, Context lifetime or theory
replay coverage assigned to TASK_10 through TASK_12.

## Launcher/preconditions and assertions

See [probes/fresh-load/README.md](probes/fresh-load/README.md) for the full
fixture contract, exact targets, assertions and isolation limitations.
The executable uses testutils in fail-fast mode and normal Holmake linking
against `bin/hol.state0`. It does not pipe SML to `bin/hol`.

Static closure auditing records 156 launcher recipe modules in each lane,
rejecting simpLib/splitLib and finding no lane-local simplifier/marker
imports. At runtime **all ten processes** independently confirm both
structures absent from the Poly namespace and loader's loaded-module set,
and both split registries unclaimed, before emitting `precondition=clean`.
Thus a fresh OS process alone is not the asserted precondition. Both the
initial heap and transitive launcher imports are checked. Dynamic loading
uses an absolute lane-local simpLib recipe audited separately for fallback.
The control payload is compiled only afterward, not linked into launch.

Attribute identity is behavioral: exact local/stored callback order,
name/attribute/argument list, theorem conclusion and single hypothesis.
Set identity includes exact singleton ADD delta, kernel name, theorem
conclusion/hypotheses, and add/remove callbacks retrieved anew from the
registry. Checks run both before and after an attempted owner-first load,
including when loading fails. Failures cannot masquerade as a green exit.

Each scenario runs in its own fresh process. The set-first case uses the
public legacy exporter, which necessarily also registers an attribute;
there is no public set-only constructor/unregister API. Its data/ownership
assertions are independent of the attribute-only process, but it does not
isolate the set disjunct of splitLib's combined collision guard. This
public-API constraint is explicit rather than hidden by private mutation.
All inputs are legacy-only and run unchanged on pinned develop.

## Retained before-fix evidence

After the successful routine host build, from the repository root:

```sh
python3 src/simp/compatibility/fresh_load.py \
  --branch 62a6bdc3453c29e8f31faa72f2b70a245f44840d \
  --output src/simp/compatibility/results/task03
```

**Exit 1**, with both library and both launcher builds exit 0. Each of ten
scenario processes has `precondition_clean=true`. The manifest retains
source/input/tool/heap/shared-input hashes, launcher recipes and closures,
exact commands, exits, observations and raw combined diagnostics. Exactly
one redundant final blank line was removed from five logs for whitespace
checks; `results/task03/log-format.json` records their original hashes.
No diagnostic text was changed. Choose a new output directory when
reproducing; records are never overwritten.

| Scenario | Develop exit | Implementation exit | Implementation observation |
| --- | --- | --- | --- |
| control | 0 | 0 | successful load and ordinary simplification |
| attribute-first | 0 | 1 | splitLib.registration HOL_ERR |
| set-first | 0 | 1 | splitLib.registration HOL_ERR |
| attribute-after | 0 | 1 | both registries claimed; replacement warning |
| set-after | 0 | 1 | both registries claimed; replacement warning |

Both owner-first errors are exactly `HOL_ERR` with origin
`splitLib.registration`, message `settype or attribute split already
exists`. No warning accompanies these load failures. Both foreign owners
remain intact after failure: local/stored handlers and exporter data/
callbacks pass their identity checks. Develop loads successfully, preserves
all identities and passes subsequent ordinary simplification.

Both implementation reverse-order probes load successfully, observe
`after-load.attribute=true` and `after-load.set=true`, and pass ordinary
simplification. Custom registration then succeeds but emits exactly one
`ThmAttribute.register_attribute` warning:
`Replacing existing attribute functions for split`. Custom identity/data
checks pass, but the namespace-neutrality assertion fails. Develop leaves
both registries false, and custom registrations succeed silently.
All develop observed operations and both normal controls have zero
warnings and no exceptions. Full warning text and constructor/error
identities are retained, not normalized out of the logs.

Native host target check from `src/simp/src`:

```sh
../../../bin/Holmake --no-project --no-cache --no_prereqs -j1 \
  --holstate=../../../bin/hol.state0 fresh-load-control
../../../bin/Holmake --no-project --no-cache --no_prereqs -j1 \
  --holstate=../../../bin/hol.state0 fresh-load-regressions
```

Control exits 0. Aggregate exits 1 and runs all five scenarios, reproducing
the same four failures and passing control; combined output is retained in
`results/task03/native-regressions.log`. These targets are explicitly
excluded from normal `all`/`HOLSELFTESTLEVEL` until registration is repaired.
No xfail/expected-exception success path has been added.

## Validation, provenance and cleanup

`results/task03/validation.json` records compact receipts for:

- `bin/build -t --seq=tools/sequences/upto-parallel`: exit 0,
  `Hol built successfully.` Normal incremental sanity pass, not full `-F`.
- Existing `run.py` at the same implementation pin: exit 1 with exactly
  TASK_02's eleven known failures; all 26 executable builds exit 0, all
  develop runs pass, both controls and unchanged 73-OK develop suites pass.
  This verifies the shared audit change did not disrupt ordinary coverage.
- Input SHA-256 check, probe `h4pedant`, Python syntax and `git diff --check`:
  exit 0. Holmake recipe TABs are required syntax, not SML source TABs.

These remain mixed-source tests: host kernel, heap, generated theories and
other dependencies are shared, not independently rebuilt develop products.
No broad observational equivalence or full-tree gate is claimed.

Early fixture trials found an uninitialized current theory and an
inappropriate empty-simpset control. The maintained launcher now imports
boolTheory and creates its own theory before registry setup; the deferred
control uses dynamically loaded boolSimps. No product repair was involved.
Trial evidence/copies, redundant ordinary-run results, Python cache and
launcher products were removed after extracting compact receipts. Runner
private libraries/products are automatically deleted on success/failure.
Unrelated/caller-owned artifacts were untouched.

## Handoff to TASK_10 / TASK_12 / TASK_14

- **TASK_10:** repair the two owner-first targets without changing these
  assertions or swallowing registration errors. The clean launcher is
  reusable; it never statically imports simpLib/splitLib. The current red
  identity checks already run after failed loads, exposing corruption too.
- **TASK_10/TASK_12:** repair reverse-order namespace claims/warnings and
  enable these passing assertions in normal regression coverage. Preserve
  the genuinely clean launcher/heap checks; putting this code in the
  ordinary selftest would preload the modules and invalidate the test.
  Add explicit opt-in/lifetime/replay coverage separately as assigned.
- **TASK_14:** rerun `fresh_load.py --branch <repaired-commit> --output
  <new-directory>` alongside `run.py`. All five fresh scenarios must then
  exit 0 on both lanes. The runner has no expected-failure mode. Native
  `fresh-load-regressions` must also exit 0 before normal gating is enabled.

Next unblocked task: TASK_04. TASK_06 and TASK_10 are also unblocked.
