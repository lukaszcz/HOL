# TASK24 internal consumer closure and standard recipes

**Final ownership overlay:** [TASK27.md](TASK27.md) resolves every row here
and in the historical consumer ledgers. Native constructions below now live
byte-for-byte in `tests/native-extension/selftest.sml` (TASK26, M6 closed),
not ordinary src/selftest.sml. TASK25's isolated migration is complete within
its sealed scope; final documentation/plan-wide limits are stated in TASK27.

This is a current-source closure overlay on [CONSUMERS.md](CONSUMERS.md), not
an overwrite of TASK07's sealed inventory. Historical line ranges below are
**row identifiers**, not current source coordinates. TASK10's checked relocation
map still binds all 630 original native cases (642 with registry additions).
`run_task24_recipes.py` executes the current suites and seals source inputs;
`run_prior_native.py` verifies the historical stream and the actual loaded
products. No original assertion, oracle, source fixture or case ID changed here.

## Explicit recipe/provider boundary

- `pureSimpsExt`, `boolSimpsExt` already implement the complete PURE/BOOL catalog.
  `combinSimpsExt` now supplies COMBIN from named theorem inputs. The standard
  catalog test compares all exported fragment rewrites in order and exercises
  each fragment, including congruences, conversion closures and opt-in ETA.
- `simpExtLib.tyi_to_ssdata`, `type_ssfrag`, `relsimp_ss`, AC/maker/conversion
  constructors remain tracked at the factory. TypeBase tests check reversed
  rewrite order, stored/fallback names, fresh versus replayed identities and
  original converter callbacks/stacks. They do not invent sources for opaque
  lifted procedures or conversions.
- `src/boss/trackedSimpDefaults` is an opt-in later-layer provider, above
  basicProof. It is built/uploaded for clients but **not linked into hol.state**.
  It neither registers a `simp` owner/listener nor observes BasicProvers state.
  Its seed installs PURE/BOOL/NOT/CONG/UNWIND/COMBIN/NORMEQ/ABBREV/LABEL_CONG/HIDE
  freshly, in order. `build` runs explicit ordered declarations: TheoryBatch
  reverses additions into one named fragment, then performs removals in their
  supplied order; LocalDelta is sequential. TypeBase steps occur only where
  requested, in listItems order. These follow BasicProvers's finaliser and
  initialization, not a reconstruction of an arbitrary compiled set.
- `Fragment` and `Update` accept only extension types. A caller needing both
  engines supplies both typed operations. Opaque ordinary updates cannot be
  translated automatically. `value`/`get_of` are retrieval only; absent `map_of`
  and windows fail precisely rather than falling back to srw_ss. No lazy source
  discovery or first-get preparation exists. Windows/rewinds preserve the
  installed provider binding and actual controls; they do not rewind spent
  allowances. A deliberately reused tracked seed shares even exhausted controls.
- Preparation may deliberately run makers and create new installation events.
  It does not claim transparent promotion, preservation of an ordinary set's
  runtime history, or automatic mirroring of ordinary local/Proof updates.
  No catalog reads `ssfrags_of`, destructs ordinary fragments, or imports a
  compiled ordinary set. Inspection-only uses in tests compare recipe order.

### Explicit logged-default catalog

Install the following as `trackedSimpDefaults.Fragment` steps at the declaration
program's corresponding logged-update positions; ordinary registration order
is retained. These are ingredients, not getters into BasicProvers's opaque log.
All new catalogs have independent extension-registry entries. Public ordinary
conversion **functions** may be reused: their callbacks/contexts remain opaque,
and dependency direction stays extension to ordinary, never the reverse.

| Ordinary producer | Tracked recipe, installation order | Executed tests |
| --- | --- | --- |
| `numSimps`, numeral | `numSimpsExt`: REDUCE, ARITH_RWTS, MOD | `src/num/arith/tests/tracked-recipes`: 91 checks; complete theorem ingredients/names/order, ground guard, relational MOD lift, limits/exclusions, exhausted bounds |
| `pred_setSimps`, pred_set | `pred_setSimpsExt`: SET_SPEC, GSPEC_SIMP | `src/pred_set/tests/tracked-recipes`: 42 checks; original keyed converters, independent lookup, literal exclusions, named removal and complete proofs |
| `listSimps`, list | `listSimpsExt.LIST_EQ_ss` | `src/list/tests/tracked-recipes`: 22 checks; list equality, exact name, exclusions, named removal, hypotheses and registry independence |
| `intReduce`, integer | `intReduceExt.INT_REDUCE_ss` | `src/integer/tests/tracked-recipes`: 116 checks jointly with integer_word; exact patterns, all operations, non-ground guard, hypotheses and native-control sharing |
| `integer_wordLib`, integer_word | `integer_wordLibExt.INT_SIZES_ss` | Same suite; all three size patterns, type instantiation, registry separation, excluded/limited conversion behavior |
| `realSimps`, real | `realSimpsExt`: REAL_REDUCE, RMULCANON, RMULRELNORM | `src/real/tests/tracked-recipes`: 124 checks; complete literal rewrite order, all converter keys, canonicalization/relations, used hypothesis sets, limits/exclusions/spent controls |

`wordsLib` and `patternMatchesLib` are ordinary logged producers, **not internal
extension consumers**. No tracked word/PMATCH default is implicitly promised or
silently skipped by this provider: callers wanting those capabilities must
supply explicit typed Fragment/Update recipes, just like any custom producer.
In particular a PMATCH conversion closing over ordinary srw_ss is not a tracked
provider mirror. No known internal extension caller requires either producer.
The external producer/type closure is TASK25's separate isolated migration,
not an invitation for this service to import arbitrary ordinary closures.

## Implementation/library rows in CONSUMERS.md

All following rows are closed. Paths before the arrow identify the historical
consumer; paths after it are the actual current owner. No implementation row
still requires a mixed-type adapter or a late arbitrary-set reconstruction.

| Historical row | Current construction/source and executable evidence |
| --- | --- |
| Traverse 36–129,616–783 | `TraverseExt.{sig,sml}` owns CONTEXT/CONFIG/LIFTED and XTRAVERSE; ordinary Traverse is pinned. `tests/traverse-ext` plus standard-recipes' private exception-payload/collector/continuation tests run lifts through both actual engines. |
| Cond_rewr 177–290 | `Cond_rewrExt` prepares shared paired runners; ordinary direct constructor is pinned. `tests/cond-rewr-ext`, `tests/simp-ext/tracked.sml`, native late/exhausted projection cases. |
| Travrules 128 | `TravrulesExt` uses OpeningExt.THREADED_CONGPROC; ordinary Travrules is pinned. `tests/congruence-ext` and native threaded/ordinary differential cases. |
| simpLib 22–162,276–345 | `simpExtLib` opaque SSFRAG/compile/native origins and its own registry before installation; ordinary source allocation removed. `simp-ext/tracked.sml`, registry static negatives/APIExamples, native R4. |
| simpLib 590,616,1628,1681–1925 | `simpExtLib` replay/suppression/filter uses tracked controls, `TravrulesExt` compiler; ordinary bodies restored. `simp-ext/exclusions.sml`, `sources.sml`, native R4–R8 source/replay/maker assertions. |
| simpLib 2049–2150 | `simpExtLib` total extension-typed traversal projections; neither calls makers/collectors nor rebuilds. `simp-ext/tracked.sml`, `lifetimes.sml`, native final projection cases. |
| simpLib 2174–2422 | `simpExtLib` prepares markers/bundles/child-first quotas from tracked sets. `simp-ext/{tactics,sources,derivation}.sml`, all native bounded/global/source cases. |
| simpLib 2566–2570,2925,3048–3054 | Explicit configured/global/child-first/root tactics live only in simpExtLib. `simp-ext/{strategies,tactics,derivation,lifetimes}.sml`; ordinary tactic staging suite stays ordinary. |
| simpLib 3088–3114,3124–3148 | `simpExtLib.tyi_to_ssdata/type_ssfrag` constructs tracked ingredients directly. `standard-recipes/selftest.sml` TypeBase mixed names, original conversion closures, replayed/fresh identities. Ordinary builders remain pinned. |
| congLib 178–205,271–306 | `congExtLib` owns extension CSFRAG/congset and configured SIMP; `lift_fragment` explicitly lifts public ordinary reducers, not a compiled congset. `tests/congruence-ext`, native configured congruence/collector tests. Ordinary congLib pinned. |
| simpMarkerLib | Simplifier-only directives/recursive processing preserved; generic markerLib unmodified. `tests/markers`, native boundary/directive matrix and `simp-ext/tactics.sml`. |
| SplitData/splitLib/splitPersistLib | One explicit opt-in owner; source construction already tracked at use. `tests/split-registration`, `split-persistence`, `split-lifecycle` and `replay-order`, fresh exports/heap reload. TASK23 dependency/identity receipt retained. |
| ThmAttribute/selftest | No type migration; exact supplied/ambient handler records retained. Routine build executes src/1 tests; split-lifecycle checks foreign ownership/callback identity. No generic machinery edit. |
| BasicProvers provider dependency | BasicProvers is unchanged and ordinary. `trackedSimpDefaults` supplies explicit typed seed/updates/windows separately; `boss/tests/tracked-defaults` has 152 checks including actual min-initialization differential, batching/removal/maker order, seed/projection quotas, rollback, absent-provider errors and three static negatives. Its separate fresh ordinary launcher loads BasicProvers, num/list/set recipes and bossLib, checking extension namespace/module absence after each import and three closed proofs. |

## Native consumer rows (historical range identifiers)

Every listed construction is still in `src/simp/src/selftest.sml`. The top-level
aliases select `simpExtLib`, `pureSimpsExt`, `boolSimpsExt`, `TraverseExt` and
`congExtLib` **before** the corresponding fragments/rules/strategies are built.
Ordinary local scopes remain ordinary. `run_prior_native.py` executes and checks
the complete exact stream, not a lower test count or a regenerated oracle.

| CONSUMERS.md row | Construction/evidence disposition |
| --- | --- |
| 114–220 threaded congruence | Extension Boolean base and extension threaded factories; native proof/beta/premise checks plus congruence-ext. |
| 621–729 strategy SF/counts | Extension empty before strategies/SF; native late dispatch/count comparisons plus strategies.sml. |
| 730–1533 configured contexts/congruence | Extension PURE/BOOL and CONFIG/CONTEXT constructors; native depth/live-order/solver/refresh proofs plus traverse-ext and congruence-ext. |
| 1534–1899 mutation/clear/filter | Extension bases before strategy/rule installation; native setter/clear/maker/history assertions plus exclusions/strategies. |
| 1900–2488 solver/looper/exclusions | Tracked named rules before strategies; native safe/unsafe/namespace/strict literal/history tests plus strategies/tactics/exclusions. |
| 2489–2995 split integration | Extension BOOL before split_ss; native TypeBase/local/suppression proofs plus registration/persistence/lifecycle. |
| 2996–3591 Split/global/bounded/root | Tracked PURE/BOOL at invocation construction; native complete validations plus tactics/derivation/lifetimes. |
| 3592–3870 directive boundary | Tracked boundary base before rule and argument preparation; native collision/ordering/proof assertions plus tactics/exclusions. |
| 3871–5019 sources/views/bundles | Tracked factories detailed below; native assertions plus sources/derivation/exclusions. |
| 5020–5145 projections/congruence | Explicit ordinary versus extension factory scopes; native once/collector/context assertions plus tracked/lifetimes/congruence-ext. |
| 5146–5597 late FRAG/maker/tactics | Independent tracked registry/sets before rules; native late lookup, makers, malformed tags and stage checks. Ordinary staging scopes stay ordinary. |
| 5598–5902 facts/live controls | Tracked strategy/marker fixtures; native binder/fact/depth/exception assertions. Ordinary reflexivity factories remain ordinary. |
| 5903–6301 projections | Installation is tracked; late extraction remains late. Native no-compilation/collector/exhaustion/use-order assertions plus tracked/lifetimes. |

### Source-sensitive factory subtable (all rows retained)

| Historical fixture row | Actual tracked boundary and fresh test evidence |
| --- | --- |
| Abstraction 3873–3970 | Tracked base before named-source addition; native full/partial/binder/source-tail assertions and derivation.sml. |
| Prepared normalization 3971–4039 | Tracked base before Once/keyless reducer; native private quota/restoration/opaque pretest plus derivation.sml. |
| Observer 4041–4120 | Tracked base before conditional rule; native observer/charge/errors plus traverse-ext/derivation. |
| Views 4122–4312 | Extension fragment/install/PURE factories; native duplicate/event/AC/conjunct/quota compatibility assertions plus sources.sml. |
| Suspension 4315–4469 | Tracked install before source handles; native sibling/alias/no-op/exhaustion assertions plus sources/derivation. |
| Preserving replay 4472–4550 | Tracked native/bundle preparation before consume/replay; native reset versus preserving controls plus sources/exclusions. |
| Bound global 4553–4697 | Tracked maker/base before bundle; native compilation-once/invocation-wide quotas/solver facts/validations plus tactics/sources. |
| Bound arguments 4700–4755 | Tracked base before bounded survivor; native exact tags/pointers/spent controls/directive handling plus sources/exclusions. |
| Prepared replay 4758–4859 | Tracked maker/base before bundle; native no-maker-rerun/origins/conjunct sharing plus sources/exclusions. |
| Preserving filter 4862–4930 | Tracked install before consume/filter; native surviving exhausted aliases/no-op/reset distinction plus sources. |
| Combined bundles 4933–4992 | Tracked bases before preparation; native duplicate bindings/reinstall rejection/event controls plus sources. |
| Context changes 4994–5018 | Tracked configured base before solver mutation; native ordered solver identity/rebuild assertions plus lifetimes. |

## Focused/dependency/nonconsumer rows

- `markers`: unchanged simplifier/generic identity inspection, no promotion.
- `split-registration`: extension BOOL before split_ss; exact historical stream.
- `replay-order`: no simpset import; exact private replay/listener stream.
- `fresh-load`: remains ordinary; six clean processes check exact foreign
  handler/listener records. The lifecycle suite adds both extension load orders.
- `split-persistence`: verify.ML chooses extension BOOL before split construction;
  all eight fresh scenarios still execute, including separate saved-heap reload.
- `splitParentScript`, `splitChildScript`, `splitDescendantScript`: earliest parent
  still records splitPersistLib before thydata replay. No dependency changes
  required; freshly exported copies are exercised by the native driver.
- `simpMarkerScript`: its qualified marker constants retain their own theory;
  ordinary markerTheory is not repurposed. Native/markers/lifecycle exercise it.
- `boolSimpsContextScript`: unchanged ordinary shared theorem producer; both
  catalog recipes consume its theorem inputs, never one another's sets.
- Holmakefiles: new recipes build normally; each new suite is included at
  HOLSELFTESTLEVEL=1 in its owning library. Existing extension targets and
  exported dependency wiring remain intact. No extension is added to boss's
  hol.state dependency list or an ordinary recipe import.
- Immutable signatures, baseline clients and the original develop selftest do
  not migrate. Coverage ledger and evidence verifier retain all 2,153 IDs and
  37 immutable inputs. Ordinary SatisfySimps/patternMatches/quantHeuristics
  dproc callers remain ordinary; routine build compiles/runs their libraries.
  Ordinary temporal congLib callers and unrelated lexical homonyms require
  no migration; their underlying pinned interfaces/bodies remain unchanged.
- Docfiles/examples retain TASK27 ownership; physical interleaved test layout
  retains TASK26 ownership. External clasimp/aesop/seed/bench callers and their
  recipe selections retain TASK25 ownership in an isolated checkout. None are
  counted as internal implementation passes here. The external worktree was
  neither edited nor built by TASK24.

**No internal migration-table row remains blocked or dropped.** This closes
TASK24's bounded recipe/internal-consumer requirements, not the external,
exhaustive documentation, independent-build or performance gates.
