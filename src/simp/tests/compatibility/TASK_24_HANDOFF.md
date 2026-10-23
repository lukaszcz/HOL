# TASK24 — explicit tracked recipes and repository consumers

Landing source identifier: **TASK24-tracked-recipes-v1** (containing commit).
Starting HEAD: `842b29a53`; develop: `cccaa27d7099cbadc886983020cbe745db7793f3`.
Linux/aarch64, Poly/ML 5.9.2, configured hol.state0, one GC thread.
Main checkout initially clean; unrelated nested `.agent-files` state preserved.

**All bounded TASK24 acceptance criteria pass. No internal migration blocker
remains.** This is not external-consumer, full clean-build or performance
acceptance. The external clasimp worktree was neither edited nor built.

## Changes and API decisions

- Added independent `combinSimpsExt` and the explicit later-layer
  `src/boss/trackedSimpDefaults.{sig,sml}` provider. Ordinary BasicProvers and
  PURE/BOOL/COMBIN recipes remain unchanged, with no extension imports.
- Added extension-owned logged-default ingredients in `numSimpsExt`,
  `listSimpsExt`, `pred_setSimpsExt`, `intReduceExt`, `integer_wordLibExt` and
  `realSimpsExt`. Public ordinary conversion procedures are reused where
  available; private immutable theorem/pattern recipes retain original order.
  No ordinary fragment/set is destructed, replayed or promoted. Relational MOD
  constructs from theorem inputs and explicitly lifts its opaque reducer.
- Provider construction is an explicit ordered declaration program. Its fresh
  initial seed matches BasicProvers; theory batches reverse adds into one named
  fragment and then perform ordered removals. TypeBase steps occur only where
  supplied. Callers use typed Fragment/Update steps for logged/custom recipes.
- `value` and `get_of` only retrieve prepared state. Context installation and
  windows store the entire prepared set, retaining source identities and actual
  live/exhausted controls. Absent-provider updates fail precisely. There is no
  first-get rebuild, arbitrary ordinary update adapter, automatic SRW mirror,
  second `simp` owner, blanket listener or process-global provider cache.
- New modules compile/upload normally; all seven new focused suites are wired
  into their owning libraries' HOLSELFTESTLEVEL=1 targets and clean rules.
  Provider availability does **not** add it to boss's hol.state imports.
- [migration/TASK24.md](migration/TASK24.md) closes **every internal row and
  source-factory subrow** of TASK07's consumer table with current source and
  executed evidence. Most caller cutovers already landed in TASK10–23: this
  task audits them rather than perturbing their assertions. No historical
  ledger/input is rewritten. Ordinary nonconsumers stay ordinary.

The provider is intentionally not an automatic catalog of arbitrary ordinary
runtime state. Word/PMATCH ordinary-only producers have no known internal
extension caller and are explicitly dispositioned: clients wanting those
capabilities must supply typed recipes, never silently import an ordinary
closure or have it skipped by a purported automatic mirror. External default
selection/update/type closure is the separate TASK25 isolated migration.

## Fresh validation

Run from the repository root, using the archived `configured-path.sh` wrapper
for the same-checkout `/home/lukasz/dev/HOL/...` configured alias. No config
rewrite, copied production tree or external checkout was used.

```sh
sh src/simp/tests/compatibility/evidence/task24/configured-path.sh \
  python3 -B src/simp/tests/compatibility/run_task24_recipes.py \
  --output /tmp/task24-final
```

**Exit 0.** Final receipt:
[evidence/task24/validation.json](evidence/task24/validation.json).
It seals **313 source inputs**, **40 executed launcher/dependency products**,
runtime tools and all command receipts. Native receipts additionally seal the
actual source-loading products/paths and the historical stream overlay.
`evidence-seal.json` binds the compact receipts, wrapper and style evidence.

| Executed check (all exit 0) | Observation |
| --- | --- |
| `bin/build -t --seq=tools/sequences/upto-parallel` | Routine sanity build succeeds after final compiled-source edits; includes normal-level new suite wiring through boss. |
| Holmake `check` in `src/simp/tests/standard-recipes` | **118** checks: complete PURE/BOOL/COMBIN catalog, direct TypeBase names/order/converters, fresh/replayed identities, history exclusions/limits/maker changes, explicit opaque reducer lifting/private payload/collector/continuation behavior through both actual engines. |
| Holmake `check` in `src/boss/tests/tracked-defaults` | **152** provider checks, including actual BasicProvers min-initialization differential, batch priority/removal order, TypeInfo failures, fresh/shared/exhausted seeds, inert retrieval/projections, snapshots/windows/pins/rollback, SRW isolation, three executed static type rejections. Separate fresh launcher checks extension module/namespace absence after five ordinary library imports and validates three closed proofs. |
| Holmake `check`, `src/num/arith/tests/tracked-recipes` | **91** numeral/MOD checks; ordered ingredients/names, conversion guard, actual relational context lift, limits/exclusions/quotas. |
| Holmake `check`, list and pred_set `tests/tracked-recipes` | **22 / 42** checks; keyed converters, full proof hypotheses, configured/default agreement, exclusion/removal and independent registries. |
| Holmake `check`, integer and real `tests/tracked-recipes` | **116 / 124** checks; original integer patterns and complete real rewrite order, arithmetic/converter/solver callbacks, limits/exclusions and native control sharing. |
| `bin/Holmake --no-project --no-cache -C src/{integer,real} -j1 HOLSELFTESTLEVEL=1 all` (separately) | Both affected later libraries/theories and their normal selftests pass; new suites execute again. |
| `run_prior_native.py --output /tmp/task24-final/native` | **642** native checks, exact traversal/exclusion/marker/registration/replay streams, six fresh ordinary-load processes, eight fresh persistence/export/heap scenarios; integrated simp level-1 target also runs all extension capabilities and split lifecycle. |
| `coverage_ledger.py`; `verify_evidence.py` | **2,153** source-tied historical cases and **37** immutable inputs retained. |
| Runner pinned-source audit | All **17** ordinary core/recipe/BasicProvers files checked are byte-identical to develop. No catalog uses ssfrags_of or ordinary-fragment destruction. No ordinary compiled source changed in this task. |
| h4pedant on seven new test directories; --nolinelen on all affected production directories; runner whitespace/columns; `git diff --check` | All pass. |

The seven new semantic suites contain **665** checks in total (not counting
repeated integrated executions or the fresh ordinary-loading assertions).
Proof comparisons check complete conclusions and hypothesis sets, not just
pretty-printed normal forms. Existing quota/history/context assertions were
not reduced. Source-sensitive consumers construct tracked objects before
installation; late extraction remains late and callback-free.

During development, one fresh-loader fixture initially used PolyML.use on a
quotation-bearing ML file and failed statically. It now uses Meta.qquse; the
final runner executes it successfully. A review caught overstated list/set
coverage prose; the closure table now describes their actual assertions.
No production bug or acceptance blocker remains from either observation.

## Cleanup and scope

Compact evidence occupies approximately 420 KiB. Task-created scratch logs,
new test launchers and test caches are removed after sealing; normal production
build products and unrelated pre-existing artifacts are preserved. Drivers
remove private persistence copies/heaps at last use. No generated executable,
heap, copied build tree or cache is committed.

TASK25 is ready. TASK26 owns physical legacy/extension test separation and
TASK27 exhaustive doc/reference sweeps. Independent clean builds, full
regression/performance gates and unsupported runtimes/platforms are not claimed
by this bounded task. There is no new out-of-scope repair or blocked internal
consumer hidden in those later gates.
