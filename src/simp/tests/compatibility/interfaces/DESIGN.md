# Final interface and ownership decisions

Production `.sig` files are the current interface authority; this document
retains the design and prototype contracts, and `graph.json` is a checked
design, not a live import audit. Final production signatures include later
additive APIs such as Cond_rewrExt.prepare/rebind and
TraverseExt.CHILD_FIRST_WITH_ABORT.

Source inspected: `74ddf80bef07bad35e55416786cbfe2ead8eb67f`.
Reference: `cccaa27d7099cbadc886983020cbe745db7793f3`.
This specifies the split; it does **not** implement or pass the production
engine split.

The executable interface is [Task08API.sml](Task08API.sml), with traversal in
[Task08TraverseExt.sml](Task08TraverseExt.sml) and reducer records in
[Task08ReducerTypes.sml](Task08ReducerTypes.sml). Signature-only declarations
are in `.sml` so Holmake gives their *executed elaboration* a `.uo` load plan.
There are no engine stubs. [Task08Clients.sml](Task08Clients.sml) checks consumers
universally as a functor; it is not applied to a fabricated implementation.
[Task08Cutovers.sml](Task08Cutovers.sml) checks the intermediate type bridges.
Two small concrete prototypes implement only lifting and actual-control binding;
`selftest.sml` exercises them with real HOL proofs/conditional rewrite runners.
Neither prototype is installed in `sigobj` or imported by production code.

## 1. Types, traversal and projections

The final public names corresponding to prototype structures are:

| Prototype | Production owner | Contract |
| --- | --- | --- |
| `T` | `TraverseExt` | New reducer datatype/data/config/policy and traversal |
| `C` | `Cond_rewrExt` | Prepared paired runners and configured constructors |
| `O` | `OpeningExt` | Threaded congruence, `Opening.congproc` identity |
| `R` | `TravrulesExt` | Threaded factory, original preorder/travrules types |
| `S` | `simpExtLib` | Tracked fragments, sets, sources, bundles, strategies |
| `G` | `congExtLib` | Extension congruence sets/fragments/conversions/tactics |
| `Pure`, `Bool` | `pureSimpsExt`, `boolSimpsExt` | Extension standard recipes |
| `Default` | `trackedSimpDefaults` | Explicit later-layer seed/update provider |

`Traverse.reducer` returns to the **exact** pinned single-constructor datatype
and signature. The extension reducer type is abstract: it is built by
`lift` of a `Traverse.reducer`, by `CONTEXT_REDUCER` (integer depth) or by
`CONFIG_REDUCER` (option depth); these two are functions, not constructors.
`TraverseExt.lift` is explicit; no reverse conversion exists. An ordinary-looking
extension factory can use `lift (Traverse.REDUCER {...})`; a configured factory
calls `CONFIG_REDUCER` directly. `reducer_data` adapts an explicit int
to `SOME`; `reducer_config_data` preserves `NONE` for CONFIG and samples the shared
live depth only immediately before a CONTEXT callback. Ordinary `dest_reducer`
stays ordinary; extension inspections use `reducer_config_data` (no extension
API that manufactures an ordinary reducer). There is no source field on a
lifted reducer.

Lift construction/extraction calls no collector/apply callback. It preserves
the original context exception payload, closure, solver/conv/relation and stack.
`addctxt` calls the original collector exactly as the original API does. Lifted
opaque reducers may contain inaccessible counters: we **cannot** enumerate,
reset or recover them. Lifting promises callback/context compatibility, **not**
source inventory, view bindings, or private quota reset inside opaque closures.
The prototype executable runs against today's mixed Traverse only for REDUCER
inputs; lifting the two soon-to-be-removed constructors is not a migration path.

Both extension projections have **extension types**:

- `simpExtLib.traversedata_for_ss : simpset -> TraverseExt.traverse_data`:
  default settings, without the simpset's configured strategy.
- `simpExtLib.xtraversedata_for_ss : simpset -> TraverseExt.xtraverse_data`:
  same tracked installed entries plus configuration.

“Legacy-style” does not mean an ordinary `simpLib.simpset`, ordinary reducer list,
or ordinary traversal record. Contextual dprocs cannot fit the original datatype.
Both projections keep the same extension dproc list/installed index and actual
controls. No eligibility test, optional fallback or `legacy_traversedata_for_ss`
remains in the final interfaces. Ordinary `simpLib.traversedata_for_ss` is exactly
the baseline unconditional projection and is unrelated to these two getters.

`TraverseExt.TRAVERSE` preserves the generalized default **construction-once**
context schedule. `XTRAVERSE` and explicit context/root/observer entry points
refresh on **each application**, even with default settings. This distinction is
necessary for native tests at `selftest.sml:5020–5145`; don't token-rename all mixed
TRAVERSE uses to XTRAVERSE. Total simplifier wrappers may deliberately construct
a traversal inside each application; keep that separate from saved raw traversal.
`NONE` condition depth reaches *each native candidate*, not just each net lookup:
a preceding failing conversion can mutate `Cond_rewr.stack_limit` in that lookup
(`simpLib.sml:69–76`). `SOME n` and custom term order remain invocation-local.

## 2. Tracked construction and ownership of controls

`ssfrag`, `simpset`, `rewrite_source`, `rewrite_bundle` are opaque and
extension-owned, distinct from every ordinary type. No polymorphic union or
implicit coercion, `promote`, `import_simpset`, rebuild-from-`ssfrags_of`, runtime
closure inspection, lazy per-ordinary-node companion or global simpset side table
is provided. Construction chooses extension `empty_ss`/PURE/BOOL **before** rules,
makers, AC, converters or dprocs needing tracked behavior are installed.

Extension fragments carry occurrence slots at construction. Installation gives
each event a fresh event identity. `ssf_upd_rewrs` assigns new slots as today;
filtering keeps surviving slots. Native compilation decodes tags, derives AC
components, calls the selected maker in the specified order and prepares a
matcher/paired runners **once**, attaching both to the actual bounded control.
A compiled entry owns `{runners, control, declared, origin option, name, key}`.
`origin option` is needed because collector/internal entries can have controls
without public source handles. No optional field appears in the ordinary net.

| Operation on tracked objects | Mutable-control and callback contract |
| --- | --- |
| Projection extraction, either order, including late extraction | No compilation/makers/collectors/traces/new origins/allowances. May build a shallow traversal record/closure; retains installed index, runner bindings and actual refs, not snapshots |
| Default/configured successful rewrite | Decrement the **same ref** once after success; failed matches/conditions do not spend it; zero remains exhausted |
| `rewrite_source_handles`, `source_rewrite`, `rewrite_sources` | Inspect stored tracked inventory. No compilation or guessed opaque rules. Supplied theorem list decoding is argument inspection, not historical discovery |
| Direct literal/extended exclusion and source suspension | Persistent filtering shares surviving entries/controls with input and existing projections. Removed occurrences and dependent views are absent in result; older immutable sets still work |
| Ordinary `filter_rewrites` / `remove_ssfrags` replay | Existing reset semantics: fresh declared allowances for replayed native groups; retain histories, makers, strategy/limits/excluded names. No-op filter returns exact input; missing remove raises original UNCHANGED |
| `*_preserving_controls` replay/filter | Rebind compatible surviving occurrences to the **input's actual refs**, including zero; old sets/views/projections and replayed result still share. No fresh control can substitute for a compatible survivor |
| Prepared bundle replay | Reuse compiled shapes/matchers; do not rerun maker. Reset replay allocates one new ref per original control group, not per conjunct/view. Preserving replay uses original refs |
| Fresh `++` / fresh argument preparation | New installation event/actual declared allowance; this is construction, not projection |
| Private child-first derivation | Temporarily reset all tracked initial-net bound refs to their declared allowances, deduplicated by ref; restore exact prior values on success, HOL_ERR, foreign exception, interrupt and charge cutoff, including nested scopes |

General native reset replay may legitimately rerun makers/collectors according to
its history schedule; **getters and prepared-event replay may not**. Preserving
native replay can need history reconstruction, but must bind before attempting
rules, preserve exhausted refs, and may not claim that a newly changed maker
output is the same compiled occurrence. Retain the existing maker/callback tests.
The concrete `Task08Controls.reset_prepared` prototype concerns *prepared events*,
not an assertion that arbitrary native history can skip compilation.

Private derivation enumerates all tracked initial-net bound entries, including
entries without public handles; never scope only `native_sources`. An opaque
lifted reducer's private internals are outside this enumeratable control domain.
Do not weaken native tests which exercise unhandled internal tracked entries.
Control scoping uses existing exception/interrupt discipline, not a second global
counter map. Callers must not concurrently mutate one bounded set; this design
does not introduce a new concurrent-quota guarantee.

## 3. Sources, views and bundles

Keep current origin `(event, slot, component, conjunct)` ordering and compatibility:
name, alpha-compatible conclusion, hypotheses and declared allowance, not proof
pointer or equal-valued remaining counters alone. Reinstalling the same fragment
makes different events; duplicate theorem slots and AC's three components remain
distinct. Compatible history replay retains origin; statement/maker changes
invalidate stale handles. Source equality is **not proof of ref sharing**.

Views compile the proposed alias statement at explicit `rewrite_views`/installation
construction and bind only to a compatible active original. They borrow that
original's real control/name; they do not become source handles. Filtering,
suspension and exclusion remove dependent aliases while retaining unaffected
conjuncts, names and sharing. `rewrite_context_changes` detects keys plus opaque
context/traversal changes; unchanged ordered solver identities avoid rebuilding.

`prepare_rewrite_arguments` processes ordinary/extended controls first, retaining
compatible spent native controls. `prepare_rewrite_bundle` compiles supplied
untagged originals once, before view derivation. Bind original occurrences before
constructing aliases. `rewrite_bundle_rules` exposes original-to-handle bindings;
combining bundles retains each binding/event/control, rejects duplicate bindings,
and never refreshes quotas. Installation is once per invocation; the BOUND tactic
receives the already-installed bundle and does not reinstall it during marker
replay, nested consumers or continued fixpoints. Preserve supplied untagged solver
context even where rewriting uses views. Same-shaped unrelated rules cannot steal
a handle; missing/incompatible suspension is an exact no-op.

## 4. Exclusions, names, markers and congruence

Ordinary `Excl`, `-*`, remove/exclude fragments, history parsing and warnings use
the pinned literal strict implementation; no extension namespace scans. Unmatched
nonempty literal deletions stay in ordinary history. Ordinary replay resets its
bounds as develop does. There is **no ordinary migration**.

Extension `Excl` is still literal strict rule/conversion/dproc exclusion. `ExclX`
explicitly supports `rule:`, `looper:`, `solver:`, `split:`, `case:`; bare-name
priority and relaxed rule spelling retain current behavior. Construction makes a
marker only. Resolution stays at processing; strict rule history reparses in the
current theory, explicitly resolved rules/displays retain their resolutions.
Split/case suppression also affects future additions. Keep warning/ambiguity/error
provenance and exact ordered strategy updates. No implicit persistence opt-in.

Keep ordinary Context slot **`simpLib.ssfragDB`** and add typed extension slot
**`simpExtLib.ssfragDB`**. Same display names may occur in both; lookup/SF registers
and FRAG resolves only in the invoking engine, at its original late stage. No
cross-registry fallback or ordinary-fragment recompile. Both use the same Context
module and rewind mechanism. FRAG's string theorem is intentionally not a typed
fragment witness. Extension standard recipes register explicitly in their own
registry when loaded, not on an ordinary import.

`congExtLib.CSFRAG` takes extension reducers. `lift_fragment` destructs the public
ordinary CSFRAG, copies theorem/preorder lists and explicitly lifts its opaque
dprocs, with no collectors/factories at lift time. **No lift of opaque compiled
`congLib.congset`** is offered. Construct a fresh extension congset from fragments
before installation. Configured wrapping uses extension data; ordinary congLib
returns to its baseline eager factories/reflexivity/projection/wrapping path.
Threaded factories use existing `Opening.congproc`, `Travrules.PREORDER/TRAVRULES`
identities, not copies of those datatypes. Rebuilt RHS beta and later-premise
threading remain extension-only.

## 5. Acyclic graph and singleton identity owners

[graph.json](graph.json) is a machine-checked adjacency list (node -> imports).
It contains final ordinary/shared/extension/service layers and the transitional
edge ledger. The validator topologically sorts the graph, rejects unknown nodes,
cycles and any *transitive* ordinary-to-extension/service path, and requires a
bounded removal owner for every transitional edge. Its introduced-node ledger
models availability: the new engine initially calls the existing paired/threaded
APIs (X1/X2), until extraction in 12/13. Those real early signatures also
elaborate in Task08Cutovers; no missing module is replaced by a stub. Generic dependencies omitted
from it are pre-existing kernel/library dependencies, not permitted back edges.

The final core ordering is:

```
ThreadLocal/BoundedRewrites/Context/markerLib/ThmAttribute/ThmSetData
  Trace
  Cond_rewr, Opening
  Travrules
  Traverse
  simpLib -> pureSimps -> boolSimps/combinSimps -> BasicProvers
  congLib -> simpLib

Cond_rewrExt -> Cond_rewr, Trace
OpeningExt -> Opening, Trace
TravrulesExt -> Travrules, OpeningExt
TraverseExt -> Traverse, Cond_rewr, Travrules, Trace
simpExtLib -> TraverseExt, Cond_rewrExt, TravrulesExt,
              simpMarkerLib, splitLib [not splitPersistLib]
pureSimpsExt -> simpExtLib
boolSimpsExt -> pureSimpsExt, simpExtLib, shared theorem producers
combinSimpsExt -> simpExtLib
congExtLib -> simpExtLib, TraverseExt, OpeningExt, shared congruence facilities
trackedSimpDefaults -> extension recipes, explicit declaration inputs
splitPersistLib -> splitLib -> SplitData [explicit opt-in only]
```

No `simpExtLib -> boolSimpsExt/congExtLib/BasicProvers` recipe back edge.
Put later tracked-default service/recipe catalogs above basicProof; the core
simp build must not depend on later libraries to get an extension bool_ss.

| Identity | Final single owner / access; implementation owner |
| --- | --- |
| Condition depth | Existing `Cond_rewr.stack_limit` ref; both engines reference it directly, not a copied/re-exported ref value; 09/12 |
| Trace | Existing `Trace.action`, level ref, hook/listener/registered controls; both use same structure; 09/12/13 |
| Rewrite tracking | The one extent stays in `Cond_rewr` (its `.sml` is develop's, unchanged): its ThreadLocal slot, `note_rewrite` and polymorphic `with_tracking`. The only signature change is the spec `val note_rewrite : thm -> unit`, so `Cond_rewrExt` reports into the same extent; `simpLib.track` and `simpExtLib.track` are both `Cond_rewr.with_tracking` and see both engines' rewrites in firing order. No second slot or module. Preserve nested/exception restoration and top-level-only reports; 12 |
| Bounds | Existing `BoundedRewrites.control` datatype and actual refs; declared allowance extension-side only; 12/14 |
| Origins | One source serial/slot allocator owned by simpExtLib; ordinary allocators removed 15/16; no duplicate allocator in recipe modules |
| Structural congruence types | Existing Opening and Travrules types/constructors, shared aliases in prototypes; 13 |
| Context, TypeBase, Sref | Existing modules/identities; only explicitly loaded extension state gets a distinct typed slot, not duplicate Context/TypeBase registries; 23/24 |
| Marker directives | One simpMarker theory/simpMarkerLib.directive wrapping the original markerLib.directive through Legacy. No generic marker changes; 20/23 |
| Split persistence | One SplitData witness/tag/handler/rules/ownership slots and TheoryLoaded listener; one splitLib cache keyed by actual TypeBase/tyinfo. splitPersistLib alone initializes transactionally; 23 |
| Exceptions | Existing Conv.UNCHANGED, Feedback.HOL_ERR, Portable.Interrupt, Basis and user callback exceptions. Neither engine wraps a new lookalike constructor. Engine-private exceptions may differ only if they cannot escape/match across the boundary; 09–13/18/22 |
| Named/default registries | Two deliberately different typed fragment slots; ordinary BasicProvers state/update log stays ordinary; tracked default gets its own opt-in provider slot; 10/24 |

Relocation alone must not change existing diagnostic origin/function labels,
callback exception payloads or handler scopes, even when a new implementation
module has a different name.

The tracking spec adds no per-rule inventory or new ordinary dispatch. Its
signature line is costed by the startup gate; sharing identity is not itself a
performance waiver. Do not move stack_limit to the extension, duplicate
tracking/Trace modules, or copy split persistence.

## 6. Standard recipes and the default-provider boundary

Recipes share **immutable ingredients**, not already-built ordinary fragments,
simpsets or closure layouts. No conversion of pureSimps.pure_ss/boolSimps.bool_ss.
Initial PURE/BOOL recipes land in 10, complete catalogs/provider in 24:

1. Extension EMPTY then ordered PURE maker setup; explicit CONG versus threaded
   CONG fragments. BOOL composes `PURE -> BOOL -> NOT -> CONG -> UNWIND` exactly.
   ETA is separately available; no silent switch of ordinary BOOL to threaded.
2. COMBIN, NORMEQ, ABBREV, LABEL_CONG, HIDE; named/custom-maker/AC/conversion,
   TypeBase and relational factories use extension constructors from the start.
3. Later default seed matches BasicProvers's initial recipe and its per-theory
   finalizer batching/order, TypeBase fold, and explicitly typed logged recipes.
   Theorem producer boolSimpsContextTheory stays shared and ordinary-load-safe.
4. Consumers construct clasimp and aesop *separately*: clasimp weak
   CONG/depth 40, splitting/filter/removals/list conversions/ORDER/LINARITH/
   solvers; aesop weak
   congruence/ETA and explicit solver replacement, without inheriting splitting.
   Static and budgeted ORDER/LINARITH variants explicitly lift ordinary reducers
   once at factory construction. External seed/bench/subject fragments have
   extension variants only where consumed by extension code; ordinary variants
   remain ordinary.

### Explicit provider, not an automatically mirrored srw_ss

`Default.recipe` is an ordered **declaration/construction** program, never an
ordinary compiled set or `(simpLib.simpset -> simpLib.simpset)` transform.
`build` invokes the seed and folds steps, thereby installing tracked rules before
any source use. Its cost/callbacks are explicit; declaration-installed controls are **new**,
not recovered from BasicProvers. An explicitly supplied seed may intentionally
reuse an existing tracked set's controls; build does not reset that seed. `value`/`get_of` only retrieve an already-prepared provider;
`get_of` returns NONE if absent. No deriving suspension or first-get rebuild.
`map`, `map_of`, context install and windows accept extension-typed transforms.
`map_of`/windows fail with a precise unprepared-provider HOL_ERR rather than
falling back to srw_ss. Context copies/rewinds retain the whole prepared provider
and matching derived source state; no global strong-reference provider cache.

The step representation is implementable from public inputs:

- `TheoryBatch (thy, ds)` means BasicProvers's finalizer algorithm: partition adds
  and removes in order, reverse adds into a named tracked fragment, apply that
  fragment then removes in its original finalizer order. Do not reduce a batch
  to just a theorem set or replay old compiled fragments.
- `LocalDelta` is an explicit ordered temporary ADD/REMOVE.
- `Fragment`, `TypeInfo`, `Update` are already extension-typed. Fold TypeBase items
  in the same order as BasicProvers init; supply them at the appropriate point in
  the construction program, not automatically after every batch.
- Catalogued logged recipes use the known producer's immutable theorem/conversion
  ingredients and original ordering, not BasicProvers's opaque logged closures.
  A producer without a typed recipe must be supplied one explicitly by its
  extension caller; it is not silently skipped or translated.

An optional **explicit preparation** helper may capture ambient persistent
`ThmSetData.theory_data/raw_delta` for requested theories and TypeBase inputs,
then assemble this recipe. It is rebuilding declaration state, not importing
ordinary runtime state or preserving its callbacks/quotas. It must not register
a second owner for settype `simp`, install blanket theorem-set/postkernel hooks,
claim arbitrary-context theorem-data reads, or hide Context.with_context pins.
No automatic listener on ordinary simplifier updates is added. Persistent
snapshot preparation is outside getters and occurs before source binding.

**Behavioral migration decision:** extension defaults no longer accept arbitrary
ordinary `srw_ss` state as their authority. Ordinary local changes, opaque logged
transforms and `Proof` context windows cannot be inferred from a persistent
snapshot. Source-sensitive callers must supply/install the explicit provider and
route each such update through its typed path; callers needing both engines
supply both operations. The complete external producer/type/update closure
covers default factories, temp_setsimpset, map/window/attribute paths and
cached/derived state, which must move together. No migrated caller may still
feed an arbitrary ordinary transform to a tracked getter or silently ignore
that transform. The recipe catalog and interface supply the explicit provider
paths, and each migrated consumer is validated in isolation.
The arbitrary-state automatic mirroring contract is deliberately **not offered**;
this is the necessary branch-only API change, not an unresolved promise.

## 7. Final migration coverage

[migration/final-apis.tsv](../migration/final-apis.tsv) resolves **every**
API row (`migration/apis.tsv`) with final module/type, construction decision,
prototype witness and owner. The final table is additive over `apis.tsv`.
Existing APIs in B1/C2, the `existing` rows of T1, and the `existing` rows of
F1 (below) explicitly retain their ordinary versions; only branch extension
callers move to the parallel types.

F1 covers the extension counterparts of the develop `*Simps`/`*Reduce`/
`integer_wordLib` libraries that the other groups do not reach: `boolSimps`,
`combinSimps`, `pureSimps`, `intReduce`, `listSimps`, `numSimps`,
`pred_setSimps`, `realSimps` and their `...Ext` modules (`integer_wordLib` has
`integer_wordLibExt` but shares no name with it). Each row maps `M.name` to
`MExt.name`, an opt-in value of type `simpExtLib.ssfrag`/`simpset` (or a
`thm`/`term -> thm` with a distinct definition) whose loading changes no
default simpset. The witness is the extension's own signature. Owners are the
stages that introduced the modules in `graph.json`: 10 for `boolSimpsExt` and
`pureSimpsExt`, 24 for the rest (the stage-24 commit "Complete explicit
tracked recipes" added them; there is no earlier TASK prefix in the log).

Special resolutions: delete `legacy_traversedata_for_ss` (no replacement optional
promotion); extended `traversedata_for_ss` returns T data; external output/helper
names stay external with extension-typed inputs/outputs where required.
SplitData/ThmAttribute/simpMarkerLib/splitLib keep one identity and their
current owning modules. No legacy client must change.

Completeness does not depend on hand-picking. For each pair of develop module
M and extension module M' listed in `MODULES` in `check_design.py` (which also
names the extension signature in the repo), every name that develop's `M.sig` (pinned
in `inputs/develop/`, from the base revision) exports and that the extension's
`M'.sig` also declares needs either a row with old name `M.name`, or an entry
in [migration/shared-exports.tsv](../migration/shared-exports.tsv) with a
one-line justification that the extension binds the identical value or type.
`check_design.py` enforces this: a missing name fails, and an entry that also
has a row or is not a shared export (stale) fails. Names are read from the
signatures by the comment-stripping parser of `check_task27_docs.py`, per
namespace (a type and a value of the same name are different declarations).
Names that `include Abbrev` brings in are excluded: they are the shared basic
types, identical in both signatures. `MODULES` itself is checked: a tracked
extension signature (`MExt.sig`, or `pExtLib.sig` for `pLib`, outside `tests`
directories) whose develop `M.sig` exists at the base revision, and which
`MODULES` does not list, fails. The pinned develop signatures of every listed
module are in `inputs/develop/`.

No free retrospective metadata promise remains in this design.
