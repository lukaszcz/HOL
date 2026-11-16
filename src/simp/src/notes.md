# Simplifier engines, construction and migration

## Ordinary develop clients: no migration

Keep `simpLib`, `congLib`, `Traverse`, `Cond_rewr`, `Opening`, `Travrules`,
`pureSimps`, `boolSimps` and `combinSimps`. Their ordinary types, callbacks,
construction stages and literal exclusions remain the develop interfaces.
In particular, `Traverse.reducer` has exactly the original `REDUCER`
constructor. `simpLib.traversedata_for_ss` always returns ordinary traversal
data; there is no eligibility scan or extension dispatch.

Ordinary fragments hold rewrite/AC theorems, conversions, congruences,
reducers and a rewrite-maker filter. Ordinary simpsets compile these into
rewrite nets and traversal rules, retaining history, limits and exclusions.
They contain **no** strategy records, source handles, paired runners,
tracking inventories or extension companions. Importing ordinary `simpLib`
or `congLib` does not import the extension engines, markers, splitter,
private split registrations or tracked default provider.

Do not change literal `Excl`/`-*` names because they contain `rule:`,
`solver:`, `looper:`, `split:` or `case:`. These prefixes acquire no namespace
meaning in ordinary exclusions. Strict dotted-name parsing, ancestry checks,
unmatched deletion history and current-theory reparsing on replay remain.

## Branch-only migration: choose types before installing rules

The earlier mixed branch APIs are not develop APIs. Their final owners are:

| Earlier branch use | Final module/type/construction |
| --- | --- |
| `Traverse.CONTEXT_REDUCER`, `CONFIG_REDUCER`, configuration/solver/policy types, `XTRAVERSE`, root/observed/child-first traversal | `TraverseExt`; use `TraverseExt.reducer` at the reducer factory. |
| Paired/context/configured conditional constructors | `Cond_rewrExt`; ordinary `Cond_rewr.COND_REWR_CONV` stays direct. `Cond_rewrExt.is_var_perm` is its own copy of Cond_rewr's unexported predicate (tested to agree); `Cond_rewr.sig` is develop's plus the `note_rewrite` spec. |
| `Opening.THREADED_CONGPROC`, `Travrules.mk_threaded_travrules`, `simpLib.threaded_cong_ss` | `OpeningExt`, `TravrulesExt`, `simpExtLib.threaded_cong_ss`. Ordinary congruence factories are unchanged. |
| Extended `dproc_ss`, `SSFRAG`, fragments/sets/weakener data | `simpExtLib.ssfrag/simpset`, with `TraverseExt.reducer`, from the first relevant construction. |
| Configured `congLib` calls | `congExtLib`; construct its distinct congset before installation and pass an extension simpset. |
| Strategy fragments/setters, loopers, safe/unsafe solvers, subgoaler/depth/order | `simpExtLib`, with `TraverseExt.ssolver/subgoaler` types. |
| `Split`, `ExclX` | `simpExtLib`; marker inspection/recursive processing is `simpMarkerLib`, not generic `markerLib`. |
| Source handles/views/bundles, filtering/preserving replay, child-first preparation | `simpExtLib`; start with tracked ingredients before source-sensitive rules, makers or reducers are installed. |
| Configured `GEN_*`, global/child-first/BOUND tactics | `simpExtLib`, taking its simpset and `TraverseExt` policy. BOUND requires the bundle already installed. |
| Configured extraction from an earlier mixed set | `simpExtLib.xtraversedata_for_ss` returns the full pair for `TraverseExt.XTRAVERSE`. |
| Optional `legacy_traversedata_for_ss` | Removed, not a conversion API. Use total `simpLib.traversedata_for_ss` for an ordinary set, or `simpExtLib.traversedata_for_ss` for a tracked set. |
| PURE/BOOL/COMBIN for extension consumers | `pureSimpsExt`, `boolSimpsExt`, `combinSimpsExt`, before installation; do not pass ordinary fragments to an extension set. |
| Source-sensitive use of BasicProvers defaults/updates | Explicit `trackedSimpDefaults` recipes and extension-typed updates/windows; ordinary BasicProvers remains ordinary. |

These replacements are not transparent compatibility wrappers. No operation
promotes an arbitrary ordinary simpset/congset, recovers an opaque reducer's
source inventory, or translates an already-applied ordinary update closure.
`ssfrags_of` is inspection, **not** reconstruction: it omits exclusions,
limits, maker changes and history. Rebuilding a fresh recipe creates fresh
identities and allowances and may run makers/collectors again. It cannot
preserve previously consumed controls. Bind sources before consumption.

Only two one-way public adapters exist: `TraverseExt.lift` wraps an ordinary
reducer while retaining its context/callbacks; `congExtLib.lift_fragment`
lifts public ordinary fragment data. Neither imports an opaque compiled set.
There is no reverse adapter into ordinary traversal.

## Executable tracked construction and projections

Load extension modules explicitly (or list them in a Script's `Libs`).
For example, after loading `boolSimpsExt`:

```sml
val tracked : simpExtLib.simpset =
  simpExtLib.++ (pureSimpsExt.pure_ss, boolSimpsExt.BOOL_ss);
val default_data : TraverseExt.traverse_data =
  simpExtLib.traversedata_for_ss tracked;
val configured_data : TraverseExt.xtraverse_data =
  simpExtLib.xtraversedata_for_ss tracked;
```

Both projections belong to `TraverseExt`, **not** ordinary `Traverse`.
The default projection omits simpset strategy settings and uses
construction-once private contexts with `TraverseExt.TRAVERSE`; configured
`TraverseExt.XTRAVERSE` refreshes contexts per application. Extracting either
projection does not recompile, invoke collectors or reset actual counters.
Both retain the tracked object's installed bounded controls, including zero.

`boolSimpsExt.bool_ss` is the parallel tracked BOOL recipe; threaded CONG and
ETA remain explicit choices. Further typed catalogs are `numSimpsExt`,
`pred_setSimpsExt`, `listSimpsExt`, `intReduceExt`, `integer_wordLibExt` and
`realSimpsExt`. `trackedSimpDefaults` (in `src/boss`) installs an ordered
recipe/provider explicitly. Its getters only retrieve prepared state;
missing-provider updates fail instead of falling back to `srw_ss()`.
Ordinary local/logged/window updates are not automatically mirrored.

Typed construction, reducer/public-fragment lifts, paired projections and
actual bundle/view sharing are executable in
[`Documentation.sml`](../tests/api-audit/Documentation.sml).
Configured/global/child-first tactic witnesses are in
[`APIExamples.sml`](../tests/simp-ext/APIExamples.sml). Run them through:

```sh
bin/Holmake --holstate="$PWD/bin/hol.state0" \
  -C src/simp/tests/api-audit check
bin/Holmake --holstate="$PWD/bin/hol.state0" \
  -C src/simp/tests/simp-ext check
```

### Sources, views, replay and private derivation

- `rewrite_sources`/`rewrite_source_handles` inspect installed native rules;
  they neither compile supplied rules nor discover inside opaque reducers.
  Directives must first pass through `prepare_rewrite_arguments`.
- `prepare_rewrite_bundle` compiles supplied originals once, before binding
  views. `install_rewrite_bundle` and attached `rewrite_views` reuse their
  actual controls/matchers. `combine_rewrite_bundles` retains existing events
  and rejects duplicate bindings; it does not refresh quotas.
- Origin order (`rewrite_source_compare`) alone is not compatibility;
  `same_rewrite_source` also checks compiled statement compatibility. Removal,
  suspension or changed source statements invalidate dependent views while
  surviving conjuncts retain their own identities/sharing.
- Ordinary extension history removal/filtering resets declared allowances;
  `remove_ssfrags_preserving_controls` and
  `filter_rewrites_preserving_controls` explicitly keep surviving live refs,
  including exhaustion. Neither accepts an ordinary simpset.
- `prepare_child_first`/`prepare_child_first_observed` create reusable private
  derivations. Every application uses declared private allowances and restores
  the caller's exact prior counters on success, HOL errors, arbitrary
  exceptions and interrupts. This includes native bounded entries without
  handles, but cannot inspect/reset a lifted opaque reducer's internals.

## Context, solving, congruences and controls

Reducers carry exception-valued private contexts. Ordinary `Traverse.TRAVERSE`
initializes contexts at conversion construction and eagerly constructs its
congruence/weakener factories at the original stage. There is no mixed-state
or all-REDUCER eligibility branch. Extended `TRAVERSE` retains the default
schedule; configured/context/observed entry points explicitly refresh.
`TRAVERSE_WITH_CONTEXT` separates reducer facts from solver-only facts;
solver facts also protect binders but do not install rewrites a second time.

`TraverseExt.simp_prover_ctxt` contains `{stack, context_thms, recurse}`.
Unsafe solvers handle conditions; safe solvers are final solvers selected by
safe tactics, not replacements for the unsafe condition list. Root rewriting
omits descent only at entry; its side conditions still use full traversal.
Child-first policies charge before work and can preserve abstractions.
Observer/policy callback aborts retain original exception identity, including
through nested solver/congruence continuations.

There is one `Cond_rewr.stack_limit` ref. `NONE` in configured native depth
reads it at each candidate check; `SOME n` is local and never changes it.
A `CONTEXT_REDUCER` samples an integer immediately before its callback;
`CONFIG_REDUCER` retains the option. Term order is passed explicitly and
otherwise defaults to `Cond_rewr.ac_term_ord`. No temporary global setting
implements configured invocation.

`OpeningExt`/`TravrulesExt` share the original structural congruence/preorder
identities while threading earlier results into later premises and
beta-reducing rebuilt RHS terms. Ordinary factories do no such extra work.
Both engines use the same original `Trace` action/hook/ref and registered
`simplifier` knob; rewrite tracking is one extent, owned by `Cond_rewr`
(develop's, byte-identical apart from the `note_rewrite` spec added to its
signature). `Cond_rewrExt` reports through `Cond_rewr.note_rewrite`, and
`simpExtLib.track` is `Cond_rewr.with_tracking`. `simpLib.track` and
`simpExtLib.track` are therefore the same extent: either sees the rewrites
of both engines in the order they fired. A nested extent of either kind
reports only its own rewrites and the enclosing extent does not see them,
as on develop; exceptions restore the enclosing extent.
Existing `BoundedRewrites.control`, `Conv.UNCHANGED`, `Feedback.HOL_ERR` and
`Portable.Interrupt` identities are not copied. Named-fragment registries are
intentionally **different typed Context slots**, `simpLib.ssfragDB` and
`simpExtLib.ssfragDB`: SF syntax is shared, but lookup is late and solely in
the consuming engine's registry, with no fallback to the other.

## Extended arguments and exclusions

Only explicit extension entry points interpret strategies, Split and ExclX.
There is no goal-time promotion/strategy dispatch in ordinary tactics.
Supplied extension rules bind once per invocation after abbreviation
pretactics succeed; label/FRAG lookup keeps its documented late stage.
GEN global passes share one invocation's rules and looper budget across
fixpoint reentry/siblings; saved tactic reuse starts a new invocation.
BOUND consumes its already-installed bundle without reinstalling/recompiling.
NoAsms/IgnAsm apply to both bound and unbound paths.

`ExclX` supports `rule:`, `looper:`, `solver:`, `split:` and `case:`.
`rule:` accepts relaxed dotted/kernel `$` names. Bare names use the strict
parser, preferring rules/dprocs before strategy fallback. Missing/ambiguous
targets fail at processing, not construction. Resolved history retains keys
rather than resolving again. Split/case suppression blocks later split
additions and ambient persistent/TypeBase split rules, not user loopers with
colliding display names. Other deletions are point-in-history operations:
later additions can reinstall a target. Bounds on directives qualify their
payload, not a bounded deletion; genuine bounded rewrite controls remain.

## Persistent split rules: separate explicit opt-in

Loading ordinary libraries, `splitLib`, or extension libraries and querying
split rules claims no `split` namespace. Local `Split`/`add_split` and
TypeBase `split_ss` work without persistent registration. A split-bearing
Script includes `splitPersistLib` in `Libs` **before** declarations and calls
`Theory.add_ML_dependency "splitPersistLib"` for fresh exported imports.
Put this dependency on the earliest split-bearing parent; a child's ML
initialization cannot repair an already-loading parent. An explicit prelude
calling `splitLib.enable_split_attribute ()` before loading the entire graph
is also supported.

`splitLib.exclude_split "Thy.Name"` persistently retracts a named ancestor
rule (not its DB theorem). Unqualified names resolve in the writing theory;
exported REMOVE keys cannot remove a descendant's same-named rule. This is
not local `del_split`/`ExclX`. Foreign ownership causes initialization/removal
to fail, never replacement. Registration follows `Context.restore`, but the
ML loader is global: after rewind before opt-in, explicitly initialize again;
loading an already-loaded module need not rerun it. Initialization is serial,
not an operation during concurrent proofs or arbitrary late-segment replay.

Persistence uses one private ordered event stream,
`splitLib.persistent.rules.v1`, one direct attribute and one private listener;
there is no generic ThmSetData split set/exporter. Generic markerLib,
ThmSetData and postkernel ownership remain unchanged. Query
`splitLib.split_thms`/`named_split_thms`. Fresh-process export, rewind,
ownership repair and heap-reload fixtures are normal selftests:

```sh
bin/Holmake --holstate="$PWD/bin/hol.state0" \
  -C src/simp/src split-persistence split-lifecycle
```

Rebuild **branch-extension** theories/heaps from their scripts: private
persistence format changed and `marker$Split`/`marker$ExcludeX` moved to
`simpMarker$Split`/`simpMarker$ExcludeX`. Rebuild extension theorem consumers
and compiled ML clients against the distinct new types. No old mixed-branch
binary/heap compatibility is promised. Ordinary develop source clients and
generic marker formats need no migration.

## Tests

`MANIFEST` gives module ownership. Fresh ordinary load paths,
initialization callbacks, shared controls and executable examples are checked
in `../tests/api-audit`; the complete extension integration suite is
`../tests/native-extension`, separate from the ordinary `selftest.sml`.

