# Extension API and migration inventory — TASK_07

**Final closure overlay:** [TASK27.md](TASK27.md) resolves every family and
consumer row to production ownership and concrete evidence, including all
temporary rows (M6 closed by TASK26). TASK25's isolated consumer patch/build
gate is complete within its recorded normal-level scope. The snapshot below
remains historical inventory/design input, not a current export list or an
unresolved-work list. TASK27 states documentation/validation limits explicitly.

Inventory source: `50cfa5d709a306298991b113c7ac63e426f8aabd`.
Develop: `cccaa27d7099cbadc886983020cbe745db7793f3`.
External source: `442009a1f7f04366573dc2b649d31650ea7b113b`.

This is an inventory/design input, **not an engine migration or compatibility
pass**. TASK_08 has finalized the names/types in
[the interface design](../interfaces/DESIGN.md),
[compile-checked prototypes](../interfaces/Task08API.sml) and
[final-apis.tsv](final-apis.tsv). The TASK_07 snapshot below remains the
source-tied caller inventory, not an implementation claim.
**TASK_10 additive implementation update:** [TASK10.md](TASK10.md) and
[task10-relocation.json](task10-relocation.json) separately record the actual
in-place native caller cutover, original/current source anchors and hashes,
630-to-642 ordered case mapping, ordinary pins, typed optional-eligibility
changes and named temporary dependencies. The TASK_07 tables below remain
historical; they were not regenerated as implementation evidence.

Every current symbol is indexed in [apis.tsv](apis.tsv); every lexical reference
has a file, line and task owner in [references.tsv](references.tsv). Actual
callers, including construction sites, are classified in
[CONSUMERS.md](CONSUMERS.md) and [EXTERNAL.md](EXTERNAL.md).
[IDENTITIES.md](IDENTITIES.md) records identities that cannot be copied casually.

## Coverage and reproduction

The whole-tree signature diff has six changed pre-existing production
signatures and three new ones. Across the six, there are **68 added values,
11 added ordinary types, one added datatype and two added constructors on the
existing reducer datatype**. `congLib.sig` is unchanged; its implementation and
reducer dependencies are not. Nothing originally exported was removed.

The three new signatures contribute a further 31 values, one ordinary type,
two datatypes and five constructors. `apis.tsv` also deliberately includes
baseline construction/cooperation APIs whose mixed domains need splitting.
`splitPersistLib.sml` has no named signature or exported operation: loading it
explicitly invokes `splitLib.enable_split_attribute ()`. `simpMarkerScript.sml`
exports the two simplifier marker constants; it is not a second generic marker
registry. These module/theory dependencies are in the consumer ledger.

```sh
# Read-only; checks actual signature deltas and all source/hash references.
python3 -B src/simp/tests/compatibility/migration/inventory.py
# To inventory a different external location/revision, regenerate explicitly
# and review provenance/table changes (the snapshot pins its inspected path):
python3 -B src/simp/tests/compatibility/migration/inventory.py \
  --external /path/to/isabelle-tactics --write
python3 -B -m unittest discover \
  -s src/simp/tests/compatibility/migration -p 'test_*.py'
# Search a symbol or its callers without opening old build logs:
rg 'rewrite_source_handles|xtraversedata_for_ss|dproc_ss' \
  src/simp/tests/compatibility/migration/{apis,references}.tsv
```

`inventory.py --write` explicitly regenerates the snapshot, not its policy.
Review changes against these tables; do not regenerate to hide missing callers.
The scanner compares declarations (including datatypes/constructors) against
Git's baseline, rejects unclassified changed production signatures, and binds
all scanned inputs and matched files to SHA-256. It reads tracked source,
docfiles, build manifests and maintained harnesses in both checkouts; it never
executes their ML or writes to the external checkout. Generated `.hol`/theory
ML, binaries, evidence logs and ignored `.agent-files` contents are not scanned
as independent consumers. Their maintained producers/dependencies are listed.
A second producer-output sweep follows default/working/bound sets, fragments,
public/opaque cached types and mixed helpers (D1). It catches ordinary-looking
`SIMP_*` uses with extension-valued operands that an added-token search misses.

The cross-reference is a **lexical superset**, not SML name resolution: it
includes declarations, comments, doc examples and unqualified names. A symbol
appearing under two modules has two possible rows, not two proved calls.
`lexical-homonym-or-ordinary` rows are explicitly resolved in CONSUMERS/EXTERNAL;
legacy callers are not instructed to migrate. In particular `default_config`,
`Split`, `SPLIT_TAC`, `split_thms` and `ThmSetData` data operations collide with
unrelated names. Source line numbers refer to the recorded SHA-256 inputs.
The manifest pins both scanned input digests and the external dirty state.
`inventory.py` also checks EXTERNAL_MARKERS.md's actual-consumer entries against
every direct external classifier use: old/replacement APIs, earliest boundary,
assertions and TASK_25 ownership are mandatory, not just lexical references.

## Migration table

The `group` key joins all three tables. Every member of each family is listed
individually in `apis.tsv`; this table supplies the replacement **type**, earliest
construction, and assertions that a mere module rename would miss. Every actual
caller is assigned a completion owner in CONSUMERS/EXTERNAL. TASK_08's final
interfaces are linked above; TASK_10/11 retype active test dependencies before
constructor removal, TASK_26 owns final test relocation; TASK_27 owns docs/dependency closure
for every family, in addition to the implementation owners below.

| Group / old module, type, API | Replacement module/type | Caller and earliest tracked construction | Semantic assertions / owners |
| --- | --- | --- | --- |
| T1: `Traverse.reducer` additions `CONTEXT_REDUCER`, `CONFIG_REDUCER`; `reducer_config_data`, `reducer_data`, `reducer_config_data` accessor; `simp_prover_ctxt`, `ssolver`, `subgoaler`; `traverse_config`, `xtraverse_data`, `default_config`; `child_first_policy`, `traversal_policy`, `ParentFirst`, `ChildFirst`; all extended traversal/root/observer/argument entry points | `TraverseExt.reducer`, configuration/data/policy types and entry points; explicit lift of an ordinary `Traverse.reducer`. Ordinary `Traverse.reducer` returns to exactly `REDUCER` | `simpLib` compiler/tactics, configured `congLib`, native tests, external clasimp/aesop/linarith signatures. Choose extended reducer at its factory and tracked set before dproc installation | Preserve exception-valued contexts, collector schedules, per-application refresh, solver facts/binder protection, live `NONE` vs explicit depth, custom order, observation and charges. Lift does not invent source inventory. **09–11**, completion **22/24/25** |
| R1: `Cond_rewr.is_var_perm` (TASK_31: no longer exported; `Cond_rewrExt.is_var_perm` is its own tested copy), `COND_REWR_CONVS`, `COND_REWR_CONV_WITH_CONTEXT`, `COND_REWR_CONV_WITH_CONFIG` | `Cond_rewrExt` constructors/pure helper; paired runners created only by extension compiler | `simpLib.sml:126`, native paired/conditional tests; external `clasimpLib.sml:2051`. Prepare once when installing a tracked rule, never when extracting its second projection | Same matcher and actual bounded ref; live depth checks within candidate sequence, exact trace/tracking/exception behavior. Ordinary `COND_REWR_CONV` direct again. **12**, integration **14**, external **25** |
| C1: `Opening.THREADED_CONGPROC`, `Travrules.mk_threaded_travrules`, `simpLib.threaded_cong_ss` | `OpeningExt`, `TravrulesExt`, `simpExtLib.ssfrag`; share structural ordinary congruence/preorder types where implementable | `Travrules.sml:128`, `simpLib.sml:1628`, native congruence cases `:114–220`. Extension PURE/BOOL and extension fragment before `++`, merge or `SF` | Thread results into later premises, preserve root/LHS and rebuilt RHS beta reduction; ordinary factories keep baseline staging. **10/13/14**, caller completion **24** |
| C2: existing `congLib.CSFRAG`, `congset`, `CONGRUENCE_*` with configured simpsets/reducers | `congExtLib` with extension-typed dprocs and simpset; legacy entry points/types remain ordinary | `congLib.sml:178–205,271–306`; `selftest.sml:1482–1531,5031–5142`. Tracked PURE before contextual reducer installation | Configured solver/subgoaler/depth/order; ordinary reflexivity/factory exception stage unchanged. No opaque `congset` promotion: `congExtLib.lift_fragment` explicitly lifts public CSFRAG data; construct the extension congset anew before installation. **08/11/13** |
| B1: existing `simpLib.dproc_ss`, `SSFRAG.dprocs`, `weakener_data`, `add_weakener`; existing construction, named-fragment, AC, conversion, TypeBase and relsimp APIs | Ordinary APIs retain original `Traverse.reducer`, `simpLib.ssfrag/simpset`; parallel `simpExtLib.ssfrag/simpset` constructors consume `TraverseExt.reducer` | All extension factories/tests/default recipes and external public type surfaces. Select extension empty/PURE/BOOL recipe **before** first relevant fragment/rule/maker/dproc installation | No implicit reverse adapter, source slots/counters in legacy constructors, callback duplication or `ssfrags_of` promotion. Keep ordinary dproc consumers unchanged. **10/14–16/24**, external **25** |
| P1: `legacy_traversedata_for_ss`, `traverseconfig_for_ss`, `xtraversedata_for_ss`; existing `traversedata_for_ss` cooperation | Extension-owned default/configured projections of one tracked object; `TraverseExt` data. Ordinary `traversedata_for_ss` remains unconditional original data; ordinary eligibility/fallback removed | `simpLib.sml:2095–2150`, configured `congLib`, native `:6010–6297`, external config reads. Track before installing the bounded rules even when extracting **after** consumption | No maker/collector/trace at extraction; same actual counters after partial use/exhaustion in either extraction/use order. Both projections return **TraverseExt data**, never ordinary reducers/sets; delete the optional legacy eligibility API. **10/11/14**, legacy removal **16** |
| S1: `looper_ss`, `solver_ss`, `safe_solver_ss`; `add_looper`, `del_looper`, `set_looper`; `add_split`, `del_split`, `split_ss`; `add_unsafe_solver`, `add_safe_solver`, `set_unsafe_solvers`, `set_safe_solvers`, `remove_solver`; `set_subgoaler`, `set_cond_depth`, `set_term_ord`, `mk_tactic_solver`, `clear_rules` | `simpExtLib` operations on extension simpsets/fragments; solver/context identities in `TraverseExt` | Native strategies/SF tests and external clasimp/aesop/benchmark recipes. Tracked base before installing strategy fragments or rules; clearing preserves configuration/history | Ordered replacement/removal, safe/unsafe distinction, live depth vs explicit, no context rebuild for identical solver identities, goal-time FRAG resolution, split suppression and loop limits. **TASK20 decision:** strategy examples use `simpExtLib`, `TraverseExt` solver/context types and `boolSimpsExt` recipes from construction; solver contexts contain untagged facts. Invocation-local replay preserves all installed controls, including ambient bounded rules. Extension-only strategy docfiles move to `simpExtLib.*`; ordinary callers/docs remain ordinary except stale extension links. Documentation/examples are not final validation evidence. **10/20/24**, external **25** |
| M1: `simpLib.Split`, `ExclX`; `simpMarkerLib` marker/inspection/recursive-processing API and directive datatype | Public extension entry points in `simpExtLib`; keep one simplifier-owned `simpMarkerLib.directive`, `simpMarker` theory and generic `markerLib.directive` identity | Native/focused marker tests, all Split/ExclX docfiles, exported marker theories, external old `markerLib.Split` callers and actual classifier/forwarding/inert-fact consumers in EXTERNAL_MARKERS.md (MC01–14). Extension set/registry selected before interpretation; marker construction/classification itself stays pure, no tracking required on the no-simpset fact path | Literal legacy `Excl` never becomes namespace resolution. Preserve wrapper ordering, late lookup, callback/exception provenance, strict/resolved replay distinction; no implicit persistent registration. **TASK20 decision:** nested bounds qualify content directives instead of becoming rewrites; genuine rewrites retain their original bound hypotheses and initially selected allowance. Requirements retain their checks. `Split`/`ExclX` documentation is extension-owned; generic `markerLib` constructors, classification and datatype identity remain unchanged. External claset forwards controls unchanged with a simpset, discards inert controls without one, unwraps content-bearing wrappers to facts; retain generic datatype identities via Legacy and all exact fact/bucket assertions. **18/20/23**, external **25** |
| E1: `remove_ssfrags_preserving_controls`, `filter_rewrites`, `filter_rewrites_preserving_controls` | `simpExtLib` replay/filter operations on tracked sets; ordinary removal/exclusion uses baseline history/net only | Native replay/filter fixtures, external decision stripping/cache invalidation. Input already tracked before original install; no rebuilding arbitrary legacy input in filter | Preserve exhausted/partially spent actual controls for preserving variants, ordinary reset replay remains distinct, exclusions/limit/maker/strategy retained, no-op pointer and UNCHANGED contracts. **17/19/21** |
| V1: `rewrite_source`, `rewrite_bundle`; `rewrite_sources`, `rewrite_source_handles`, `prepare_rewrite_arguments`, `source_rewrite`, `same_rewrite_source`, `rewrite_source_compare`, `rewrite_views`, `prepare_rewrite_bundle`, `combine_rewrite_bundles`, `rewrite_bundle_rules`, `install_rewrite_bundle`, `suspend_rewrite_sources`, `rewrite_context_changes` | `simpExtLib.rewrite_source/rewrite_bundle` tied to tracked compiler objects, not legacy simpsets | Native source/bundle fixtures and external clasimp source tables/views/runtime. Track at fragment slot/compilation and supplied-rule preparation before any quota use; default tracked seed before theory/TypeBase rule installations | Duplicate occurrence, slot/event/conjunct and AC identities; name/statement/proof compatibility; no stale aliases; compile once; partial/exhausted sharing; exact suspension; context invalidation; combining retains bindings/events. **14/19/21**, external **25** |
| A1: `simp_mode`, `xsimptac_config`, `GEN_SIMP_TAC`, `GEN_SIMP_TAC_CHILD_FIRST`, `GEN_GLOBAL_SIMP_TAC`, `GEN_GLOBAL_SIMP_TAC_CHILD_FIRST`, `GEN_GLOBAL_SIMP_TAC_CHILD_FIRST_BOUND` | `simpExtLib` tactics taking extension set/bundle and `TraverseExt` policy | Native global/safe/bound fixtures, doc examples, external clasimp/aesop. Prepare tracked invocation, directives, originals/bundle once before binding views/normalizing | Full fixpoint flags, subgoal/proof order, safe/unsafe solvers, requirement and abbreviation stages, counted passes, invocation-wide shared supplied quotas. **TASK20 decision:** non-global explicit GEN binds supplied rules once invocation-wide across looper branches, recursive passes and solver `recurse`, only after abbreviation pretactics succeed; label resolution remains before pretactics. Solver contexts are untagged. Local replay preserves all installed controls, not only supplied quotas. BOUND consumes an already installed bundle and never reinstalls or recompiles it; attached views reuse cached matchers. One global invocation shares its looper budget across conclusion/fixpoint reentry and siblings; saved reuse starts a fresh budget. `NoAsms`/`IgnAsm`, including wrapper-qualified forms, are respected in both global bound and unbound paths. Compile-checkable examples explicitly select configured/global/child-first/bound entry points; source-tied validation is recorded in `../TASK_20_HANDOFF.md`. **10/18/20**, bundle completion **21** |
| H1: `SIMP_CONV_CHILD_FIRST`, `prepare_child_first`, `prepare_child_first_observed` | `simpExtLib` on tracked extension sets, `TraverseExt.child_first_policy` | Native private-quota/observer fixtures, external clasimp normalization. Track ambient roots before rules installed; prepare once per chosen runtime | Fresh declared private allowances restored after HOL_ERR, arbitrary exception, interrupt/cutoff; root-preserving arguments; conservative opaque pretest; failed conditions observed. Control scope includes bounded net entries **without handles**, not merely source inventory. **10/22** |
| D1: external clasimp/aesop default, working/bound-set outputs; ORDER/LINARITH/seed/benchmark fragments and mixed iff helpers (listed in apis.tsv) | External module names mostly retained; output/input types become extension-owned **where consumed by extension code**; ordinary producers/helpers remain separately usable | All direct and transitive callers in EXTERNAL.md's producer-output closure. Tracked base before factory; split/parameterize helpers that currently take both `srw_ss()` and `clasimp_ss()` | Preserve ordinary-versus-extension comparison assertions, persistent iff reload/removal, prepared runtime/quota sharing, and generic claset invocation polymorphism. **25**, interface/recipe prerequisites **08/24** |
| I1: `ThmAttribute.attribute_fns_of/attribute_fns`, `SplitData` API/datatype, `splitLib` API/type; explicit `splitPersistLib` initialization | Retain these shared modules/types, not copies in simpExtLib. Extension-only loading reaches splitter/persistence explicitly | `src/1/selftest.sml:1617–1647`, splitter and focused tests, exported split theories, native split integration, external split theory consumers | Exact handler/listener/data/tag identities, transactional opt-in/retry, TypeBase cache identity, Context rewind, ordered private ADD/REMOVE and fresh import/heap lifecycle. Generic infrastructure unchanged. **23**, boundary audit **27** |

## No hidden promotion: complete disposition of late discovery

All discovered paths are accounted for below. A getter may be late; **tracking
may not be late**. Late goal-dependent labels, FRAG lookup, requirements, supplied
argument handling and context refresh are distinct staging contracts, not a
reason to replay arbitrary legacy history.

| Path | Required earlier decision | Responsible tasks |
| --- | --- | --- |
| In-repo native `rewrite_sources/handles/views` and bundles built from ordinary-looking `empty_ss`, `pure_ss`, `bool_ss` | Change each fixture's base/fragment factory at the exact construction points in CONSUMERS, before its maker/rules/AC slots/dprocs. Never adapt only the getter | 14/19/21/22 algorithms; **24** callers; **26** relocation |
| Native late public/configured extraction after consumption/exhaustion | Start tracked at `selftest.sml:6014–6017,6054–6057,6090–6091,6123,6183,6239,6272`; extraction remains late and allocation/callback-free | **14/21/22**, 24/26 callers |
| `congLib` chooses extended data from an arbitrary mixed `simpset` | Separate configured entry point/input type and extension PURE recipe; keep ordinary clients ordinary | **08/11/13/24** |
| External explicit clasimp `derive_simpset`, source getters/table/cache and working states | Public input types become already tracked sets; constructors and tests use extension recipes before install | **25**, primitives 14/21/22 |
| External clasimp/aesop default derives source state from BasicProvers ordinary `srw_ss()` | New explicit extension-owned seed/update recipe starts before theory/TypeBase additions; typed extension update path. Ordinary derived-value callback cannot recover live closures/counters | **08** interface; **24** provider design/recipes; **25** external implementation/validation |
| External `temp_setsimpset`, context transforms/windows, arbitrary `(simpset -> simpset)` logged updates | Do not infer source metadata from their already-built ordinary result. Extension-facing callers must supply typed tracked transforms/sets. Ordinary update path remains ordinary; rebuilding import, if offered, is explicit and not used for sharing claims | **08/24/25**; dependency audit **27** |
| External supplied-rule converse detection, deferred views, callback-adapted CS operations | `prepare_rewrite_arguments` then compile original tracked bundle **once** before view binding; reuse binding/runtime through all nested/continued consumers | **21/22/25** |
| Existing `ssfrags_of` use for names/transport/inspection | Keep read-only inspection; it is **not** a reconstruction recipe. No inventory getter may replay these fragments to invent controls/origins | **24/25/27** audit |
| Opaque ordinary reducer installed in extension set | Explicit lift preserves callback/context; only extension-owned compiled rewrites get origin metadata. No claimed inventory inside opaque closures | **08/09/14/22**, 24/25 callers |

There is no unexplained in-repository production late source getter: aside from
configured `congLib`, production source-sensitive operations are internal to the
mixed implementation, while external source-sensitive library consumers live
in the separate worktree. All getter callers are listed in references.tsv and
classified in the two consumer documents. No transparent `promote` is proposed.

## Required extension-owned recipes

Recipes construct **new explicitly tracked objects**, not replay arbitrary old
sets. Their ordinary counterparts must not import extensions, allocate extension
metadata, or subscribe every ordinary update to tracking.

1. Empty + PURE: `pureSimps.sml:6–15`, including ordered rewrite-maker setup.
2. BOOL: `boolSimps.sml:204`, ordered `PURE → BOOL → NOT → CONG → UNWIND`.
   Expose individually needed BOOL/ETA fragments; configured/threaded congruence
   is an explicit variant, not a change to the ordinary CONG recipe.
3. Named/custom-maker/AC/TypeBase/relational/conversion fragments used by tests:
   tracked slots are chosen at construction, compilation produces both runners.
4. COMBIN, NORMEQ, ABBREV, LABEL_CONG, HIDE + TypeBase recipe/update ordering for
   the extension default corresponding to BasicProvers's initial simpset
   (`src/basicProof/BasicProvers.sml:1156–1178,1244–1317`). Existing update closures
   are opaque; do not invoke them twice or silently reinterpret ordinary sets.
5. External clasimp (`clasimpLib.sml:500–597`): weak CONG replacement, depth 40,
   split, ETA/SUC filter, APPEND_ASSOC removal and `list EQ` exclusion, list
   conversion, permutation dproc, ORDER/LINARITH, arithmetic AC, solvers/subgoaler.
6. Explicit static **and budgeted** ORDER/LINARITH fragment recipes, lifting their
   ordinary reducers once; conversion/factory/collector effects retained.
7. External aesop (`aesopData.sml:51–77`): weak congruence/ETA, explicit safe and
   unsafe solver replacement; do **not** accidentally inherit clasimp splitting.
8. External weak-congruence, invocation-subject/bottom-up, benchmark translation
   fragments and optional seed collection fragments where actually consumed by
   extension code. Their ordinary producers remain usable without migration.

Initial parallel recipes: **TASK_10**; tracked compiler: **14**; complete
in-repository recipes and typed default-provider boundary: **24**; downstream
recipes/producer variants and public signatures: **25**, isolated only.
**TASK_08 decision:** `trackedSimpDefaults` builds an explicit ordered typed
recipe before source use. Its getters only retrieve prepared state; they never
translate ordinary BasicProvers state/closures. Ordinary temporary/logged/window
updates require explicit extension-typed counterparts in extension callers.
No automatic mirroring or arbitrary-state import is offered. See DESIGN.md §6
for batch order, TypeBase inputs, unprepared-provider errors and update ownership.

## Acceptance boundary

All API/consumer paths have a subsequent task owner and a construction decision.
TASK_08's finalized interfaces/cutovers are in ../interfaces; its handoff records
executed prototype checks, not an engine migration. TASK_25 still has to build
the actual external migration in an isolated checkout. No implementation
migration is claimed complete by this inventory. No compiled source, frozen fixture,
existing assertions or external worktree was changed here.
