# TASK23 — simplifier-owned split persistence and lifecycle

Landing source identifier: **TASK23-split-lifecycle-v1** (containing commit).
Starting HEAD: `f30a3e9a33b527332cb521cac19e355432e4fabe`.
Pinned develop: `cccaa27d7099cbadc886983020cbe745db7793f3`.
Linux/aarch64, Poly/ML 5.9.2; configured `hol.state0`, one GC thread.
Main checkout initially clean; unrelated nested `.agent-files` state preserved.

**All bounded TASK23 acceptance criteria pass. No TASK23 blocker remains.**
Acceptance manifest: [evidence/task23/validation.json](evidence/task23/validation.json).

## Implementation / API decisions

The existing split boundary and recorded ML dependencies were already correct:
no speculative dependency rewrite was made. All persistence, marker ownership
and reachability remain in simplifier-owned modules. Exact paths, initialization
callbacks, registries and replay/load order are documented in
[split-lifecycle/README.md](../split-lifecycle/README.md).

One lifecycle hole was repaired in `src/simp/src/SplitData.sml`: an already-owned
`initialize` previously accepted a missing private dispatcher without restoring
it, silently disabling later theory replay. `ensure_listener` now reinstalls the
**same** `dispatch` function when absent. It does not change Context, attribute
identity, rules, data witnesses or quotas, or replay ancestors. Foreign listener
replacements still fail before mutation; failed allocation/replay removes only
a newly installed dispatcher. Duplicate initialization with an intact listener
is unchanged. Pinned initialization remains rejected.

No API/type/exception identity changed. `splitLib.sig` and the enable-attribute
docfile document this repair and correct extension-module references. No generic
marker, theorem-set or postkernel source changed. The ten ordinary traversal,
simplifier, congruence and opening/rules source/signature files remain exactly
pinned-develop bytes. Ordinary clients require no migration or opt-in.

The stable private identities remain:

- Context slots `splitLib.registration`, `splitLib.rules`;
- direct attribute `split`, with pointer-identity ownership;
- loadable data `splitLib.persistent.rules.v1`, wrapper `split-rules-v1`;
- dispatcher listener `splitLib.persistence.onload`;
- **no** library-owned generic split theorem set/exporter.

`splitPersistLib` alone opts in on module initialization. The earliest exported
split-bearing parent already records `Theory.add_ML_dependency
"splitPersistLib"`; generated ML opens `simpMarkerTheory splitPersistLib` before
`TheoryReader.load_thydata`. Child/descendant imports retain that ordering and
qualified REMOVE keys. Neither ordinary nor explicit extension loading enables
persistence implicitly. The two split caches cannot initialize on ordinary
loads because both the module loader and structure namespace show `splitLib`
entirely absent after **each** ordinary simp/cong import.

## Maintained coverage

No existing lifecycle fixture, assertion, immutable input or oracle was edited.
The source-tied historical ledger still verifies **2,153 cases**. Fresh native
passes retain **642** native checks, **54** marker checks, **116** registration
checks, **15** replay-order checks, **170** persistence checks across eight
separate scenarios, all six old fresh-load scenarios, traversal/exclusions,
and the integrated extension/proof suites.

New `tests/split-lifecycle/` is wired into selftest-enabled `src/simp/src/all`:

- **20 independent launcher processes**: simp/cong and corresponding extension
  load orders; foreign attribute/set/syntax installed before ordinary loads,
  between ordinary and extension loads, or after extension loads; two clean
  controls. Exact foreign handler/exporter records, callback behavior, data,
  listener identities/order, qualified markers, module absence/reachability,
  warning silence, explicit opt-in/rejection, rewind and local split capability.
  Every load and proof/initialization operation checks zero unsolicited foreign
  callbacks, separately from deliberate callback-liveness probes.
- **Two more independent processes**: freshly import exported descendants with
  no ambient split registration, then save and reload a heap in a different
  launcher. Both sides disable TypeBase and check alias identity, one/all named
  exclusions and a closed persistent-only tactic proof with exact conclusion
  and **full hypothesis set**. Ordinary proof results are also checked before
  and after extension/namespace operations in every matrix case.
- `repair.sml`: standalone dispatcher-removal/reinitialization and foreign
  replacement regression. The private negative changes only the owned-init
  branch back to `check_listener ()`; it builds with exit **0**, executes with
  expected exit **1**, and fails the intended repair assertion, not elaboration.

The new positive suite reports **1,769 checks** (including freshly executed
exporter and standalone repair assertions), 22 matrix/import/reload cases,
and two complete persistent proofs. Coverage mapping is in the new README.

## Fresh validation and evidence

All acceptance runs follow the last compiled-source edit. Commands ran with
the same-checkout configured-path alias archived as `configured-path.sh`;
`HOLDIR`/cwd were `/home/lukasz/dev/HOL/worktrees/simplifier`, bound to this
`/home/lukasz/work/...` checkout, with fresh `/dev`. No config or source path
rewrite or copied production tree was used.

| Command | Exit / compact evidence under `evidence/task23/` |
| --- | --- |
| `bin/build -t --seq=tools/sequences/upto-parallel` | **0**, `routine.log.gz`; complete routine sanity build |
| `python3 -B src/simp/tests/compatibility/run_prior_native.py --output /tmp/task23.GRi9EA/native-acceptance` | **0**, 14 receipts in `native/`; executes selftest-level-1 `all`, including new integrated suite, then exact original lifecycle streams and fresh exports/heap scenarios |
| `python3 -B src/simp/tests/compatibility/run_task23_lifecycle.py --output /tmp/task23.GRi9EA/lifecycle-acceptance` | **0**, `lifecycle/`; newly exported fixture graph, 22 clean-process cases, independent regression, semantic negative |
| `coverage_ledger.py`; `verify_evidence.py` (same compatibility directory, `python3 -B`) | **0**, `coverage.log.gz`, `immutable.log.gz`; 2,153 source-tied cases / 37 immutable artifacts |
| `tools/h4pedant/h4pedant src/simp/tests/split-lifecycle`; `tools/h4pedant/h4pedant --nolinelen src/simp/src` | **0**, `pedant-*.log.gz` |
| Pinned-source / unchanged-fixture audit; `git diff --check` | **0**, `audit.log.gz`, `diff-check.log.gz` |

The lifecycle runner records **actual** traced uses and `Meta.fileDirMap`
inventories, resolves HOL's generated-file mapping, rejects foreign-checkout
or wrong simplifier source paths, and seals **427 resolved source paths** plus
**50 simplifier .uo/.ui loader products**. Its fresh generated theory dependency
observations are retained; requested `Meta.load` paths alone are not used as
execution provenance. Native receipts additionally seal sources, products,
launchers and runtime tools. `validation.json` seals the final source inputs,
commands, runtime/config and compact evidence. No interactive-session import
is claimed as fresh-process coverage.

During test development the new all-ordinary listener oracle initially omitted
`congLib`'s unchanged `computeLib` listeners. Inspection of pinned `congLib` and
its actual import graph established the eight-name schedule now checked. No
original oracle was weakened. A provenance check was also adjusted to use the
existing HOL physical-file resolver for generated `.hol/objs` sources.

## Files and cleanup

Production: `SplitData.sml`; signature comment corrections: `splitLib.sig`;
normal selftest/clean targets: `src/simp/src/Holmakefile`; enable-attribute
API documentation; new lifecycle test sources/README; fresh runner; handoff
and compact evidence. No recorded theory ML dependency change was required.

Drivers remove their private source/fixture/negative build directories and
both saved heaps at last use; normal targets trap heap cleanup on failure.
The new fixture's generated launchers/cache and task-created scratch logs are
removed after evidence sealing. Pre-existing build products and unrelated
nested metadata are preserved. No generated executable, heap or build tree is
committed. Independent whole-repository clean builds/performance and unsupported
platforms are not claimed by this bounded lifecycle task.
