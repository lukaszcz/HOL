# Split lifecycle boundary (TASK23)

Run from the repository root:

```sh
bin/Holmake --holstate="$PWD/bin/hol.state0" --no-project --no-cache \
  -C src/simp/tests/split-lifecycle -j1 check
python3 -B src/simp/tests/compatibility/run_task23_lifecycle.py \
  --output /tmp/lifecycle
```

`check` is also part of `src/simp/src`'s selftest-enabled `all`. The Python
runner exports the parent/child/descendant fixtures into a newly created
private directory, executes the tests, inspects the generated ML dependency
order, and removes all private products. It additionally builds and executes
a semantic negative using a private `SplitData` with only dispatcher repair
removed. Output directories contain receipts, source/runtime hashes and
compact dependency observations, not build trees or heaps. Actual traced
source uses and `Meta.fileDirMap` inventories are resolved through HOL's
`.hol/objs` mapping, checked against this checkout, and hashed together with
the simplifier's `.uo`/`.ui` dependency products. Requested load paths alone
are not treated as execution provenance.

## Ownership and module graph

All paths below are relative to `src/simp/src/`:

- `simpMarkerScript.sml`: owns `simpMarker$Split` and `$ExcludeX`. Removes
  their unqualified overloads so foreign syntax survives. No persistence.
- `simpMarkerLib.sml`: constructors/decoders and extension argument helpers;
  depends on `simpMarkerTheory` and unchanged generic `markerLib`.
- `splitLib.sml`: pure/local splitting and TypeBase derivation caches;
  `enable_split_attribute ()` explicitly calls
  `SplitData.initialize {validate=ignore o is_asm_split}`.
- `SplitData.sml`: private stream, active-context ownership, handlers and
  dispatcher. Loading it creates context slot handles, **not** loadable
  data operations, a public split attribute, a generic set or a listener.
- `splitPersistLib.sml`: explicit import-time initializer, calling
  `splitLib.enable_split_attribute ()` in its module body.

```text
congLib -> simpLib -> legacy facilities (no modules above)
congExtLib -> congLib + simpExtLib + extension traversal
simpExtLib -> simpMarkerLib + splitLib -> SplitData
splitPersistLib -> splitLib -> SplitData
```

The two `Sref` caches in `splitLib` are `type_split_cache` (derived rules,
validated against the exact tyinfo) and `case_const_index` (validated against
the TypeBase pointer). Absence of the entire module in **each** ordinary
load proves their initialization is not ordinary-client work. No extra heap
or cache module has been introduced.

Private identities:

| Kind | Identity |
| --- | --- |
| Direct attribute | `split` |
| Context slots | `splitLib.registration`, `splitLib.rules` |
| Loadable data | `splitLib.persistent.rules.v1` |
| Encoded wrapper | `split-rules-v1` |
| Dispatcher listener | `splitLib.persistence.onload` |
| Generic split set/exporter | none |

`SplitData.dispatch` is the sole private global listener; each event selects
operations from the active context, with ownership checked by attribute
record pointer identity. No old theory-data witness is captured globally.
Initialization preflights foreign attribute/set/syntax/listener claims;
allocation or ancestor replay errors restore the exact entry Context and
remove only a dispatcher newly installed by that attempt. Duplicate init
preserves records/data. If its listener was removed, explicit init restores
the exact dispatcher without ancestor replay or rule changes. A foreign
replacement is never overwritten.

Ordinary loading adds only develop's generic marker listeners. Loading
`congLib` also adds unchanged `computeLib` listeners; the new matrix checks
all eight exact names/order, and every pre-existing callback's identity.
Full extension loads add no listeners and do not enable split persistence.
Only explicit API/module opt-in adds `splitLib.persistence.onload`.

## Export and replay order

The earliest split-bearing fixture, `../split-persistence/splitParentScript.sml`,
uses `Libs ... splitPersistLib` for script execution and
`Theory.add_ML_dependency "splitPersistLib"` for imports. No dependency
rewrite was needed: this remains the correct owner after the module split.
Its marker theorems additionally record the `simpMarkerTheory` dependency.

Fresh exported imports follow:

```text
splitDescendantTheory -> splitChildTheory -> splitParentTheory
  -> simpMarkerTheory + splitPersistLib initialization
  -> parent .dat decoding -> TheoryLoaded(parent) ordered ADD/REMOVE
  -> child decoding/replay -> descendant decoding/replay
```

Initial opt-in after imports visits ancestors once in reversed
`SymGraph.topological_order` (including diamonds). Later notifications replay
only that theory's ordered stream. ADD resolves/validates a named DB theorem;
REMOVE preserves the key resolved in the writing theory. Invalidated ADDs are
pruned on other theory events; REMOVE and existing live/local rules survive.
Context rewind selects the restored registration, or disables the dispatcher
if no owned registration exists. A cached `Meta.load "splitPersistLib"` need
not rerun its body: after rewind use `enable_split_attribute ()` explicitly.

## Coverage map

Existing assertions and source-tied historical streams remain unchanged:

| Existing suite | Retained contracts |
| --- | --- |
| `../markers/` | Simplifier-owned markers and generic marker cleanup |
| `../fresh-load/` | Clean simp imports, foreign handlers/data/syntax, exact listeners |
| `../split-registration/` | Context rewind/pinning, duplicate init, foreign ownership, failed replay rollback/retry, invalidation and persistent retraction |
| `../replay-order/` | Generic control vs private diamond order, aliases, repeated notifications |
| `../split-persistence/` | Fresh parent/child/descendant/owned imports, foreign attribute/set rejection, exported markers, saved heap + Context/foreign-owner replay |

Additional coverage here (not a replacement for those suites):

- `selftest.sml`, `ordinary.ML`, `extension.ML`: **20 fresh-process cases**.
  Both simp/cong load orders; foreign attribute, set and syntax installed
  before ordinary imports, between ordinary and extension imports, or after
  extension imports; two clean controls. Check both ordinary module boundaries,
  extension reachability, exact listener functions/order, handler pointers and
  callbacks, theorem-set data, qualified markers, warning silence, local split
  capability, explicit registration/rejection, rewind and dispatcher repair.
  Ordinary kernel proof conclusions/hypotheses are checked before and after
  extension use and namespace changes. Every load and proof/initialization
  operation also checks that it made **no unsolicited foreign callbacks**;
  callback-liveness probes cannot erase evidence of load-time interference.
- `persistent.ML`: **two more fresh-process cases**, with no registration or
  simplifier ambient at entry. Freshly import exported descendant theories,
  save, then restore the saved heap in a separate launcher. On both sides,
  disable TypeBase and check imported alias identity, one/all exclusions and
  a fully closed persistent-only tactic proof, including **all hypotheses**.
- `repair.sml`: independently compiled regression. Remove the private
  dispatcher from an owned registration, explicitly initialize, check exact
  dispatcher/Context/rule identity, then reject a foreign replacement. The
  source-isolated negative must compile successfully and fail the repair
  assertion, not a deferred static error.
  A final check replaces the direct `split` attribute with a counting handler
  (the foreign dispatcher removed first) and requires initialization to fail
  as a conflict with that handler and persistent removal to refuse with
  "persistent split registration not owned"; neither calls the handler.
  `repair.sml` imports only `SplitData` from `src/simp/src`: the negative
  rejects any other `src/simp/src` module.

The launcher statically imports only kernel/test helpers. A library build
prerequisite is not a linked import. `Meta.loaded` **and** the runtime global
structure namespace reject ambient ordinary/extension/fixture modules and
private listeners before each process's actual import/heap restoration.
Proof heap files are removed by `Holmake` even on failure.
