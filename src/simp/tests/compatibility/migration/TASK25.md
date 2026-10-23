# TASK25 — isolated external consumer migration

**Final closure cross-reference:** [TASK27.md](TASK27.md) maps every
EXTERNAL/EXTERNAL_TYPES/MC01–MC14 row to this sealed isolated migration and
actual execution evidence. TASK26 changes only test ownership, not the
consumer's production prerequisites. The source-specific limits below remain
in force; no caller-owned checkout modification or new consumer run is claimed.

The patch in `../evidence/task25/consumer.patch` applies to consumer
`442009a1f7f04366573dc2b649d31650ea7b113b`. It is **not** applied to the
caller-owned `isabelle-tactics` worktree. The simplifier source prerequisite
is `4a0ad8e9160dd911393385d748b3535fc5ce65ba`; subsequent affected source
changes require another consumer run. This is an extension-client migration,
not a change required of ordinary HOL clients.

## Type and construction closure

- `clasimpLib`'s source-sensitive sets, fragments, bundles and handles use
  `simpExtLib`. Strategies, solver contexts and child-first policies use
  `TraverseExt`; permutation helpers and ordinary comparisons remain ordinary.
- `trackedAutoDefaults` prepares an independent `trackedSimpDefaults` provider
  from declaration inputs, before clasimp/aesop configuration or installation
  of source-sensitive rules. It never promotes `srw_ss()`, imports opaque
  ordinary transforms, reconstructs arbitrary history, or builds in a getter.
  Typed local updates/windows and eager derived values travel together through
  Context. Aesop derives independently, without inheriting clasimp splitting.
- Persistent iff callbacks install/capture their typed declaration inputs.
  The context-owned program records iff removals and the bottom-up fragment,
  rather than extracting fragments from a compiled set. Bottom-up theorem
  tables and their installed flag also rewind with Context. Both engines
  retain their separate persistent-iff observations and the same reducer
  closure is explicitly lifted for extension installation.
- `prepare_declarations`/`seedDefaults.prepare` explicitly create fresh tracked
  defaults **before** source binding/quota use. Theory/logged/TypeBase inputs
  precede captured consumer iff/bottom-up inputs in declaration order. This
  named fresh preparation is not transparent preservation of arbitrary live
  local state. Ordinary local changes must be supplied on the typed path;
  neither provider silently mirrors ordinary compiled state. Optional numeric
  recipes are selected in the post-boss consumer, not imported eagerly by
  clasimp (which would change numeric overload preferences).
- `ORDER_ext_ss{,_budgeted}` and `LINARITH_ext_ss{,_budgeted}` explicitly lift
  existing reducers. Their ordinary recipes/destructors stay usable. Solver
  public records use `TraverseExt`; generic claset invocation polymorphism is
  retained. Benchmark translation fragments and all transported/cached sets
  select the extension type before construction.
- Mixed iff helpers and seed tests retain independent ordinary/extension
  conversions. Ordinary seed collections and their literal exclusion tests
  stay ordinary. Exported theory tests, transitive public signatures, inferred
  helpers, Holmake edges and extension-only Docfiles are in the patch.

## Semantic repairs exposed by executed tests

- Classifier consumers use `simpMarkerLib`, but recurse through a bounded
  wrapper **before** deciding whether its payload is a directive. Treating
  every wrapped theorem as a control bypasses the prepared bundle and loses
  shared allowances. Original compile-once and partial/exhausted quota tests
  remain intact and execute successfully.
- Bounded-existential congruences use `threaded_cong_ss`, retaining function
  instantiations discovered in earlier premises. Ordinary congruences remain
  ordinary. Source handles, contextual reducers, lazy prepared views/bundles,
  child-first tactics and actual proof validations are not replaced by stubs.
- Synthetic unregistered theory namespaces use explicit `ExclX "rule:..."`.
  Literal `Excl` keeps develop's strict dotted parser. Benchmark kernel-spelled
  `Thy$Name` exclusions are adapted only at the simplifier marker boundary;
  claset names, guards, corpus goals and exact result sets are unchanged.
- A missing benchmark citation `LIST_REL_cons_I` is expressed using the
  existing `later_cases LIST_REL_rules` recipe: SPEC_ALL, CONJUNCT2, GEN_ALL.
  It is the same general constructor theorem, proved by kernel inference,
  not an extra tactic, problem-specific lemma, or relaxed corpus assertion.
- Explicit fresh post-boss preparation avoids duplicate ancestral batches
  and preserves the seed iff stream's final precedence. Regressions distinguish
  captured declarations from missing compiled fragments and name-matching
  impostors; they check explicit retraction, fresh quotas, inert/exhausted
  getters, bottom-up rewind and Context restoration.

## Exact build prerequisites and isolation

The consumer depends on `takeWhile` declarations absent from the simplifier's
list source. The private core uses the **exact consumer revision's**
`src/list/src/listScript.sml`, recorded separately in the manifest; no list
change is made in this checkout. Its dependent theory closure and heap are
rebuilt, avoiding a new list theorem paired with an old preloaded listTheory.

Four consumer Scripts use numeric theorem attributes unsupported by this
checkout's parser. The driver builds a standalone quote-filter from the
configured core ingredients with only `HOLSourceParser.sml` taken from the
exact consumer commit. It pre-expands those four inputs in disposable build
sources. Canonical/expanded hashes are recorded; generated SML is never part
of the migration patch. All actual theorem proofs/assertions then execute
through normal Holmake-built harnesses. No production parser, generic marker,
postkernel module, heap or caller build product is modified.

The sandbox starts with a read-only host and binds only task-owned scratch
writable. The recorded configured alias is the private core, and `src/auto`
is the isolated migrated consumer. Module-path observations and recursive
source-loading plans seal the loaded sources, not just `.uo` creation.

## Reproduction

From a configured checkout retaining both pinned Git objects:

```sh
python3 -B src/simp/tests/compatibility/test_task25_consumer.py
python3 -B src/simp/tests/compatibility/run_task25_consumer.py \
  --consumer-patch \
    src/simp/tests/compatibility/evidence/task25/consumer.patch \
  --output /tmp/task25-reproduction
```

The default driver prepares archives, applies/checks the patch, configures the
private core, bootstraps its heap, runs the routine selftest-enabled build,
then compiles/executes the complete normal-level consumer scope. It cleans
its copied sources/products even on failure. Explicit `--existing-core` and
`--existing-consumer` permit source-verified task scratch reuse; such receipts
are not independent clean-build claims. Evidence uses this explicit reuse
mode after the separately recorded private-core bootstrap/routine commands.
See `../TASK_25_HANDOFF.md` for executed scope, exits and limitations.
