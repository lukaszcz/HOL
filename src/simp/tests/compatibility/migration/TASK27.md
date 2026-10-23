# TASK27 — final migration closure and module ownership

## Status and interpretation

Audit base: `c707baca802d7e0d22e7e8045a0dc5d3567bd7a9` (TASK26).
Ordinary reference: `cccaa27d7099cbadc886983020cbe745db7793f3`.
External input: `442009a1f7f04366573dc2b649d31650ea7b113b`.

**All implementation-consumer and temporary-transition rows are closed,
including M6.** No required production capability was found unresolved in the
bounded TASK07–26 migration. This is not release, performance, independent
clean-build, optional corpus or cross-platform acceptance. Documentation and fresh final validation are recorded below; ownership
assignment alone is never an executable pass.

This is an additive closure overlay. CONSUMERS, EXTERNAL, EXTERNAL_TYPES,
EXTERNAL_MARKERS, IDENTITIES and MIGRATION retain their historical coordinates,
assertions, counts and provenance. Read their future-tense requirements as
historical, then use this ledger for disposition. Neither `apis.tsv`,
`final-apis.tsv`, `references.tsv`, `manifest.json`, relocation JSON, frozen
inputs nor old receipts have been regenerated. `final-apis.tsv` is the 193-row
TASK08 design decision table, not a complete current-signature inventory or
193 separately executed clients.

### Evidence keys

Paths below are relative to `src/simp/tests/compatibility/`, unless stated
otherwise. Evidence is source-specific; later affected code requires rerunning
its gate. This documentation audit does not relabel old execution as fresh.

| Key | Concrete evidence and scope |
| --- | --- |
| E11 | `migration/TASK11.md`, `TASK_11_HANDOFF.md`: exact ordinary Traverse/congLib restoration, frozen complete signatures and clients, ordinary versus configured lifetime checks. |
| E12 | `migration/TASK12.md`, `evidence/task12/{paired,native,conditional-control,conditional-candidate}/`, `audit_task12.py`: paired matcher/actual-control/tracking correspondence and 103 conditional checks. |
| E13 | `migration/TASK13.md`, `evidence/task13/validation.json`: pinned Opening/Travrules, shared structural identities, threaded premise/RHS-beta proof checks. |
| E14 | `migration/TASK14.md`, `evidence/task14/`, `tests/simp-ext/tracked.sml` (under `src/simp/`): authoritative installed runners, inert extraction, actual shared controls and internal entries without handles. |
| E15 | `migration/TASK15.md`, `TASK_15_HANDOFF.md`, `audit_task15.py`: original eight-field ordinary fragments, no source-slot allocation and ordinary constructor/TypeBase/merge correspondence. The installation adapter described there is historical and removed by E16. |
| E16 | `migration/TASK16.md`, `task16-source-manifest.json`, `audit_task16.py`: exact ordinary simpLib restoration and 231-node/446-input conservative source closure. Historical source seals are not a current whole-tree runtime audit. |
| E17 | `../exclusions/evidence/task17/validation.json`, `TASK_17_HANDOFF.md`: literal deletion/replay, 929-check original stream and 42 supplemental checks per side; no extension namespace scan. |
| E18 | `../tactics/evidence/task18/validation.json`, `TASK_18_HANDOFF.md`: strict original 43-scenario/60-check staged matrix, 307 supplemental checks/116 validations per side; original callback reds repaired. |
| E19 | `evidence/task19/validation.json`, `TASK_19_HANDOFF.md`: 159 extension exclusion checks, actual surviving controls and independent split/user-looper namespaces. |
| E20 | **`evidence/task20/repair/validation.json`**, `TASK_20_HANDOFF.md`: 186 strategy checks/63 validations and 88 tactic checks/18 validations; corrected Abbr-before-FRAG and nested-bound contracts. The older top-level TASK20 receipt is not final acceptance. |
| E21 | `evidence/task21/validation.json`, `migration/TASK21.md`, `../simp-ext/sources.sml`: 407 source/view/bundle checks, dependent-view invalidation, negative compatibility/order controls. |
| E22 | `evidence/task22/validation.json`, its `repair/`, `dispatch/` and `congruence/` receipts, `migration/TASK22.md`: 1,392 derivation and 315 lifetime checks; callback-abort, restoration and continuation intersections. |
| E23 | `evidence/task23/validation.json`, `TASK_23_HANDOFF.md`, `../split-lifecycle/README.md`: exact ownership/listener identities, explicit opt-in, fresh imports/exported dependencies, saved-heap reload and dispatcher repair. |
| E24 | `evidence/task24/validation.json`, `evidence-seal.json`, `migration/TASK24.md`: 118 standard-recipe and 152 provider checks; numeral/set/list/integer/real recipe suites and ordinary import-absence launcher. |
| E25 | `evidence/task25/{manifest.json,summary.json,evidence-seal.json,consumer.patch,logs.tar.gz,log-archive.json}`, `TASK_25_HANDOFF.md`: isolated 93-file patch, all 39 commands exit 0, 1,407 normal-level consumer checks and theory proofs. |
| E26 | `evidence/task26/{validation.json,evidence-seal.json,native/manifest.json,legacy/manifest.json,post-list-full.log.gz}`, `migration/TASK26.md`: physical separation, all 2,153 frozen cases plus 12 additions, strict full 642-check native execution and ordinary import absence. |
| E27 | `TASK_27_HANDOFF.md`, `evidence/task27/validation.json`, `source-audit.json.gz`, `docfiles/accepted/`, `doc-scan/scan.json`; `../api-audit/evidence/20261023T084819Z-7b0ad6ac/`: fresh live 478-input source gate, actual defining dependencies and ordinary paths, eight fresh load/control scenarios (1,374 assertions), one-sided registry negatives, compiled examples and final documentation scan/48+30 polyscripter runs. |

For E25 the patch SHA-256 is
`6a0a8f54dcb1af06a1b824f56453619195a11d321f97851bcc7b61149166ad1a`.
It applies to the pinned external input, **not** to the caller-owned worktree.
Its simplifier prerequisite is `4a0ad8e9160dd911393385d748b3535fc5ce65ba`;
TASK26 changed test ownership, not that API/implementation. E25 uses the exact
external listScript prerequisite and a private numeric-attribute quote-filter,
with canonical/expanded input seals. It is not an unqualified claim that the
unpatched older consumer builds in this checkout.

## Final public ownership

Production signatures, not prototype spelling, are authoritative. Core paths
in this table are under `src/simp/src/`; the provider is in `src/boss/`.

| Owner | Final responsibility and boundary |
| --- | --- |
| `Traverse.{sig,sml}` | Original single `REDUCER`, `dest_reducer`, ordinary `traverse_data` and `TRAVERSE`; no contextual/configured constructors or strategy dispatch. |
| `Cond_rewr.{sig,sml}` | Direct ordinary compiler, sole `stack_limit` ref, ordering and ordinary helpers. `is_var_perm` remains exported here as well as in Cond_rewrExt; callers need not migrate this pure ordinary helper. |
| `Opening`, `Travrules` | Ordinary eager congruence factories and original `congproc`, `PREORDER`, `TRAVRULES` identities. |
| `simpLib`, `congLib` | Original opaque fragments/sets/congsets, ordinary reducers, literal exclusions, ordinary tactics and unconditional ordinary projection. No reverse extension adapter. |
| `pureSimps`, `boolSimps`, `combinSimps`, `BasicProvers` | Ordinary recipes/default state and update log remain ordinary; no automatic tracking or migration. |
| `TraverseExt.sig` | Distinct `LIFTED`, `CONTEXT_REDUCER`, `CONFIG_REDUCER`; configuration/solver/policy types, refreshing/root/context/observer/child-first traversal and `CHILD_FIRST_WITH_ABORT`. Explicit `lift` retains original callbacks and exception-valued context. |
| `Cond_rewrExt.sig` | Paired/configured constructors; opaque `prepared`, `prepare`, inert `runners`, and explicit matcher-preserving `rebind` onto an actual compatible control. |
| `OpeningExt.sig`, `TravrulesExt.sig` | Threaded factories returning the original structural types; later premises see earlier results and rebuilt RHS beta reduction stays extension-only. |
| `simpExtLib.sig` | Distinct opaque `ssfrag`, `simpset`, `rewrite_source`, `rewrite_bundle`; tracked installation, sources/views/bundles, strategies, configured tactics, preserving replay and private derivation. |
| `congExtLib.sig` | Extension `CSFRAG`, opaque congset and conversions/tactics accepting `simpExtLib.simpset`; one-way `lift_fragment` of public ordinary fragment data, never an opaque compiled congset. |
| `pureSimpsExt`, `boolSimpsExt`, `combinSimpsExt` | Independent tracked catalogs built from ingredients, not ordinary installed sets. Ordinary CONG is not silently replaced by threaded CONG; ETA remains explicit. |
| Later tracked catalogs | `numSimpsExt`, `pred_setSimpsExt`, `listSimpsExt`, `intReduceExt`, `integer_wordLibExt`, `realSimpsExt`: explicit typed logged-default ingredients (E24), not a mirror of arbitrary ordinary closures. |
| `src/boss/trackedSimpDefaults.sig` | Explicit ordered `recipe`/`step` construction, opt-in Context-owned provider, typed updates/windows. `value`/`get_of` retrieve only; missing-provider updates fail, never fall back to `srw_ss`. Not linked into the ordinary hol.state. |
| `SimpTracking`, `Trace`, `BoundedRewrites` | One shared tracking extent/reporter, original trace identities and original bounded-control datatype/actual refs. Extension declared allowances and origins do not enter ordinary records. |
| `simpMarkerTheory`, `simpMarkerLib` | One simplifier-owned Split/ExcludeX vocabulary. `Legacy` wraps the original `markerLib.directive`; generic classifiers/constructors are unchanged. Classification alone needs no tracked set. |
| `SplitData`, `splitLib`, `splitPersistLib` | One private data/ownership/handler/listener instance and one splitter/cache module. Loading splitPersistLib explicitly initializes persistence; ordinary and extension imports alone do not. |

Direction is **extension → ordinary/shared**, never the reverse. Core simpExtLib
has no dependency on boolSimpsExt, congExtLib, BasicProvers or the later provider.
`interfaces/graph.json` remains the checked *design*, including historical
introduced-node/transition decisions; it is not rewritten into a runtime audit.
E27 regenerates defining-source dependencies and checks exact live inputs
against narrow reviewed baseline deltas, separately from its fresh actual
runtime path and identity checks. E23/E24/E26 preserve lifecycle/provider/
coverage evidence; no historical graph or mutation fixture alone is the final
dependency gate.

### Per-family closure

Every row in MIGRATION's family table is resolved here. Ordinary APIs in B1/C2
remain available with their original types; no ordinary caller is told to rename.

| Family | Final disposition / concrete evidence |
| --- | --- |
| T1 | TraverseExt owns extension reducers/data/configuration/traversal; explicit ordinary lift, no reverse adapter or opaque source discovery. E11, E22, E26 traverse-ext 131. |
| R1 | Cond_rewrExt owns paired preparation/configured calls; ordinary direct constructor retained and shared reporter/depth preserved. `is_var_perm` available in both. E12, E14, E26 conditional 103. |
| C1 | OpeningExt/TravrulesExt/simpExtLib threaded fragment; original structural types shared. E13, E26 congruence 4 ordinary + 57 extension and native premise/beta checks. |
| C2 | congExtLib constructed from typed fragments before install; only public fragment lift, no congset promotion. E11, E13, E26. Inventory's lexical `CONGRUENCE_EQ_SIMP_RULE` means actual `CONGRUENCE_SIMP_RULE`. |
| B1 | Parallel typed factories/registries chosen before makers/rules/dprocs; ordinary fragments/net restored. E14–E16, E24 recipe suites, E26 public/static-negative/import tests. |
| P1 | Both tracked projections return TraverseExt data and retain actual controls; default omits settings, configured refreshes on application. Optional `legacy_traversedata_for_ss` is deleted, not renamed into promotion. E14, E22, E26 late/exhausted/native cases. |
| S1 | simpExtLib strategies and TraverseExt solver/context types; independent tracked BOOL seed, untagged solver facts, local replay preserves ambient controls. E19, E20, E24, E26. |
| M1 | simpExtLib constructors/simpMarkerLib classifier, unchanged generic datatype via Legacy. Literal Excl unchanged; ExclX explicit namespaces; pure classification/no-simpset fact path needs no tracking. E20, E23, E25 MC01–14, E26 markers 54. |
| E1 | Tracked reset versus preserving filter/removal explicit; preserving paths keep partial/zero actual refs and aliases, no-op/UNCHANGED exact. E17 ordinary control, E19, E21, E26. |
| V1 | simpExtLib origins/views/prepared bundles/context deltas; compile once before view binding, no getter reconstruction. E14, E21, E25 source-sensitive consumers, E26 sources 407 and original native assertions. |
| A1 | Explicit configured/global/child-first/BOUND tactics; one binding per invocation after pretactics, BOUND never reinstalls, saved reuse starts a fresh invocation budget. E18 ordinary stages, E20 repaired stages, E26 strategy/tactic validations. |
| H1 | Tracked preparation scopes every initial-net native bound, including no-handle entries; restores exact prior values on all exits and nested aborts. E14, E22, E25, E26 derivation/lifetime suites. |
| D1 | Isolated consumer types/providers/producer variants and mixed helpers migrated together; ordinary seed recipes and independent comparisons retained. E24 provider prerequisite; E25 complete normal-level closure. |
| I1 | Same ThmAttribute/SplitData/splitLib identities; explicit earliest exported splitPersistLib dependency and transactional ownership/dispatcher repair. E23, E25 split theories, E26 fresh exports/heap reload. |

## Every repository consumer row

Historical ranges below are **row identifiers**, not current source lines.
For all native rows, executable owner N is
`src/simp/tests/native-extension/selftest.sml`. TASK10's typed overlay composed
with `task26-relocation.json` preserves exact bodies, anchors, IDs and order
(E26); referring to N does not mean the old mixed ordinary path still exists.

### Implementation/library rows (CONSUMERS)

| Historical consumer | Closed disposition and evidence |
| --- | --- |
| Traverse 36–129,616–783 | TraverseExt extraction; ordinary Traverse restored. E11, E22, E26 traverse-ext. |
| Cond_rewr 177–290 | Cond_rewrExt paired compiler; direct ordinary constructor retained. E12/E14. |
| Travrules 128 | TravrulesExt → OpeningExt; E13/E26 congruence. |
| simpLib 22–162,276–345 | simpExtLib owns tracked slots/paired compilation and separate registry. E14/E16/E26 tracked and R4. |
| simpLib 590,616,1628,1681–1925 | Ordinary destructor and baseline replay restored; extension threaded/filter/preserving replay retained separately. E13/E16/E19/E21. |
| simpLib 2049–2150 | Total extension projections, ordinary unconditional getter, no eligibility/fallback. E14/E16/E22/N final projection cases. |
| simpLib 2174–2422 | Tracked marker preparation/bundles/quotas; E19/E20/E21/E22/N. |
| simpLib 2566–2570,2925,3048–3054 | Explicit extension global/child-first/root tactics; E20/E22/N. |
| simpLib 3088–3114,3124–3148 | Typed TypeBase recipes before install; ordinary printers/builders restored. E16/E24 standard-recipes. |
| congLib 178–205,271–306 | Separate congExtLib input/construction; E11/E13/E26 configured congruence. |
| simpMarkerLib | Same simplifier-only datatype/recursive processing; E20/E23/E26 markers. |
| SplitData/splitLib/splitPersistLib | Same explicit persistence owner/cache, no ordinary dependency; E23/E26 lifecycle. |
| ThmAttribute/src/1 selftest | No relocation/type migration; exact supplied/ambient handler-record checks retained, routine build and E23 foreign-owner tests. |
| BasicProvers provider sites | BasicProvers stays ordinary; explicit trackedSimpDefaults seed/typed steps/windows, not a source getter on its result. E24 provider 152 and ordinary import guard; E25 downstream provider. |

### Native ranges and source-sensitive factories (CONSUMERS)

All factories choose tracked types **before** relevant installation. Ordinary
local controls stay ordinary; late extraction remains late.

| Historical range | Concrete preserved execution |
| --- | --- |
| 114–220 threaded congruence | N premise/RHS-beta/LHS checks, E13, E26 congruence. |
| 621–729 strategy SF/counts | N late dispatch/legacy/count comparisons, E20 strategies. |
| 730–1533 contexts/configured congruence | N once/depth/order/live/refresh/child-first checks, E22, E26 traverse/congruence. |
| 1534–1899 mutation/clear/filter | N setters/history/maker retention, E19/E20. |
| 1900–2488 solvers/loopers/exclusions | N safe/unsafe/namespace/priority/limit assertions, E19/E20. |
| 2489–2995 split integration | N TypeBase/proof/order/suppression/replay, E23/E26 registration/persistence. |
| 2996–3591 Split/global/bounded/root | N invalid/unnamed/bounds/root/datatype/validation checks, E20/E22/E23; E26 strict post-list 642 gate includes all option/pair/list checks. |
| 3592–3870 directive matrix | N collision/inspection/preparation assertions, E19/E20. |
| 3871–5019 sources/views/bundles | N and every factory row below, E21/E22. |
| 5020–5145 contexts/projections/congruence | N construction-once versus refresh, total wrappers, collectors and configured congruence; E11/E22/E26. |
| 5146–5597 late FRAG/maker/factory/markers | N late lookup/malformed/maker/AC/exception staging, E18/E20. |
| 5598–5902 facts/live controls | N binder/fact order/live depth/exact exceptions and ordinary reflexivity controls; E13/E20/E22. |
| 5903–6301 paired/projections | N both use/extraction orders, late exhaustion, zero compilation/collectors and dproc identity; E12/E14/E22. |
| Abstraction 3873–3970 | N binder/source-order/tail sharing and removal, E22 derivation. |
| Prepared normalization 3971–4039 | N fresh private quotas/root/opaque pretest/restoration, E22. |
| Observer 4041–4120 | N failed-condition dependencies/charges/exceptions, E22. |
| Views 4122–4312 | N actual quota sharing/duplicate slots/AC/stale compatibility, E21 sources. |
| Suspension 4315–4469 | N exact conjunct/dependent aliases/sibling/no-op pointers, E21/E22. |
| Preserving replay 4472–4550 | N reset versus partial/exhausted sharing/missing name, E19/E21. |
| Bound global 4553–4697 | N compile once/budgets/solver facts/NoAsms/IgnAsm/proofs, E20/E21. |
| Bound arguments 4700–4755 | N exact pointers/tags/spent controls/directives, E19/E21. |
| Prepared replay 4758–4859 | N no maker rerun/origins/conjunct sharing, E14/E21. |
| Preserving filter 4862–4930 | N compile once/no-op/alias partial and zero sharing/reset distinction, E19/E21. |
| Combined bundles 4933–4992 | N origins/events/spent controls/no recompile/duplicate rejection, E21. |
| Context changes 4994–5018 | N identical ordered solver identity versus replace/remove/reorder, E21/E22. |

### Focused suites, theories and nonconsumer rows (CONSUMERS)

| Historical row | Final owner/evidence |
| --- | --- |
| markers/selftest | Same owner; 54 original checks, E26; generic/simplifier identities also E20/E23. |
| split-registration/selftest | Extension BOOL before split installation; all 116 original checks, E23/E26. |
| replay-order/selftest | No simpset promotion; original 15 private ordered/diamond/retraction checks, E26. |
| fresh-load/selftest/control/identity-before/identity-after/syntax | Six separate original scenarios, exact foreign handler/listener identity/order; explicit simpMarkerLib load in syntax after ordinary absence guard. E16 reviewed overlay, E23/E26. |
| split-persistence/selftest/optIn/heapSave/heapVerify/verify | Tracked BOOL in verify before integration; eight fresh scenarios, saved-heap reload, 170 original assertions including scripts, E26. |
| splitParentScript | Earliest splitPersistLib Libs/add_ML_dependency retained before data replay; fresh exports E23/E26. |
| splitChildScript/splitDescendantScript | Ancestor initialization/qualified REMOVE/same-name survival retained, fresh exports/import/heap E23/E26. |
| simpMarkerScript | Own qualified constants/dependency; generic markerTheory not repurposed. E23/E26. |
| boolSimpsContextScript | Shared ordinary-safe theorem producer, not an extension consumer; E24 recipe differential and ordinary load test. |
| simp/src/Holmakefile and focused Holmakefiles | Independent ordinary/extension launchers, no ordinary splitLib link prerequisite; post-list check-full mandatory at level 1. E26 routine and native receipts. |
| Seven signatures/nine public clients | Immutable, original types; E26 legacy 18 client checks, separate original-scope guard and six quota checks. |
| TASK06 ledger/paired/prior/performance baselines | All 2,153 frozen IDs retained; physical path overlay only. Historical baselines never mechanically renamed into extension tests. E26 and fresh ledger/integrity checks below. |
| SatisfySimps/patternMatchesLib/quantHeuristicsLibBase ordinary dprocs and TraversalContracts/ExclusionParsing/LegacyFailures | Stay ordinary REDUCER clients; baseline signatures/bodies and ordinary 47/929/6 suites retained. E11/E16/E26 and routine build; no migration required. |
| temporal_deep ordinary congLib clients | Stay ordinary, not compiled downstream-extension claims; pinned congLib interface/body and public compatibility E11/E26 establish no API migration. No separate whole temporal example build is claimed. |
| genUseScript.default_config, refute Canon.split_thms, local hoare-triple SPLIT_TAC and lexical Split/ThmSetData/directive/exclude/initialize hits | Resolved homonyms or unchanged generic operations, not extension callers. Historical references/provenance retained; no false migration or generic namespace expansion. |

## Every external consumer row

All following are closed by the **isolated** E25 patch and executed normal-level
closure. Paths abbreviate `src/auto/`; S/T/I mean clasimp implementation,
selftest and signature as in EXTERNAL. E25's manifests/source inventories,
patch and compressed command logs are the concrete evidence, not a claim that
the old caller-owned checkout was edited. Suite counts are 188 clasimp,
148 aesop, 147 rules, 25 order, 149 linarith, 52 linarith-instances,
74 seeds, 166 benchmarks, 250 classical and 208 blast. All 67 consumer Scripts
were forced through rebuilding/execution, including 16 clasimp theory tests.

### EXTERNAL API rows

| Historical API row | Patch construction/typed owner and executed evidence |
| --- | --- |
| rewrite_sources | simpExtLib installed inventory; tracked derive/default/runtime factories; clasimp source-table tests. |
| rewrite_source_handles | simpExtLib handle type throughout caches/public I; clasimp exact-source/conjunct tests. |
| source_rewrite | simpExtLib source inspection; clasimp origin/support/role tests. |
| same_rewrite_source | simpExtLib compatibility; clasimp stale/equal-statement/identity tests. |
| rewrite_source_compare | simpExtLib stable ordering, separate compatibility; clasimp indexed versus linear metadata checks. |
| rewrite_views | Typed ambient/supplied/fact fragments before install; clasimp lazy-view/actual-quota tests. |
| rewrite_context_changes | Tracked generations/cache invalidation; clasimp incremental versus fresh tests. |
| prepare_rewrite_arguments | Explicit controls before supplied binding; clasimp marker/requirements/order tests. |
| prepare_rewrite_bundle / rewrite_bundle_rules | Compile originals once, carry typed bindings; clasimp bundle/continuation tests. |
| install_rewrite_bundle / combine_rewrite_bundles | Same compiled event/control, chosen by first consumer; clasimp multi-consumer tests. |
| suspend_rewrite_sources | Exact handles/sibling/alias controls; clasimp converse suspension/cycle tests. |
| remove_ssfrags_preserving_controls | Tracked decision removal retains spent controls; clasimp working-state tests. |
| filter_rewrites / preserving | Typed decision/abstraction filtering; clasimp cutoff/policy/control tests. |
| mk_tactic_solver | TraverseExt solver record; clasimp/benchmark solver proof tests. |
| set_cond_depth / split_ss | Tracked clasimp factory depth 40/splitting; clasimp and splitIntegration proofs. |
| set_safe_solvers / add_unsafe_solver | Tracked solver/context types; clasimp safety/budget tests. |
| set_subgoaler / remove_solver | Typed factory/update path; clasimp contextual and wrapper tests. |
| prepare_child_first_observed | Tracked preparation; clasimp failed-condition/dependency/charge tests. |
| prepare_child_first | Tracked runtime before normalization; clasimp private-quota/cutoff tests. |
| SIMP_CONV_CHILD_FIRST | Explicit extension conversion; clasimp head/eta/argument/lazy-view tests. |
| GEN_GLOBAL_SIMP_TAC_CHILD_FIRST / BOUND | Extension invocation/bundle; clasimp six-driver shared-runtime/continuation proofs. |
| xsimptac_config | Explicit typed configured global flags; clasimp wrappers and benchmark drivers. |
| CONTEXT_REDUCER / dproc_ss | TraverseExt constructors or explicit lift at factory; clasimp opaque reducer/collector tests. |
| charge_only / traverseconfig_for_ss | TraverseExt policy and tracked settings; clasimp budget/depth tests. |
| clear_rules | Tracked fixture/default before clear; clasimp retained strategy/history checks. |
| Cond_rewr.is_var_perm | Pure ordinary helper remains legal; no type migration required. Clasimp permutation/converse tests execute. |

Explicit public `rewrite_source`, bundle, policy, solver, context, simpset and
ssfrag propagation in I/S is included, not just import renaming. S:2592's
ordinary reducer closure is lifted for the extension bottom-up variant, not
duplicated. Weak CONG replacement chooses a tracked/threaded fragment where
premise instantiations require it. Ordinary comparisons/permutation sets stay
ordinary. E25 normal-level proofs retain these paths.

### EXTERNAL late-discovery/construction rows

| Historical row | Closed disposition in E25 |
| --- | --- |
| Default S:1682–1692/BasicProvers provider | trackedAutoDefaults explicit declaration program/provider before configuration; no promotion of derived callback input. |
| Explicit derivation S:843–854/cache 943–1116 | Extension public inputs selected at construction; typed caches retain controls. |
| Native converse 1296–1318/working 1644–1710/extensionality 1885 | Typed source owner through generations; inert late getters, compile-once assertions retained. |
| Supplied originals 1127–1138,1146–1147 | Prepare originals/bundle once, install once before views; quota-sharing tests. |
| Early converse/suspension 1296–1390/deferred 1398–1565/runtime 1572–1602 | Runtime/original selection before lazy views; detection does not spend quotas. |
| Directives 1807–1831/callback 1834–1851/process 3094–3122 | Prepare first, exact processed-set dynamic scope and exception cleanup; no promotion cache. |
| Bundle combination 3585/first consumer 3594–3620 | One runtime/budget and compiled bundle across consumers. |
| ssfrags_of S:865,3019/benchLib:702/benchGuards:240 | Inspection/names/transport only, not provider reconstruction; patch preserves this boundary. |
| Private permutation set 430–439 | Remains self-contained ordinary conversion state; extension installation explicitly lifted. |
| BasicProvers temporary/logged/window/update sites | Ordinary state untouched; explicit extension-typed updates/windows and eager derived defaults in trackedAutoDefaults. No hidden automatic mirror. |

### EXTERNAL transitive rows and EXTERNAL_TYPES producer closure

| Historical consumer/row | E25 typed decision and concrete executed suite |
| --- | --- |
| aesopData.sml and .sig | Independent tracked provider before weak congruence/ETA/solver install, no clasimp splitting; aesop 148 and reloaded attribute theories. |
| aesopRule.sml/.sig, aesopLib.sig/.sml sessions | Extension sets through contextual/safe/raw helpers and APIs; generic invocation type remains polymorphic; aesop proof/NoAsms/session checks. |
| aesop/selftest explicit factories (including unsafe-base sentinel and all listed no-aesop_ss sites) | Typed seed before fragments/clear/split/solvers, unchanged cutoff/resume/context/sentinel assertions; aesop 148. |
| orderLib.sml/.sig and ORDER static/budgeted uses | New ORDER_ext_ss variants explicitly lift original reducer; ordinary ORDER recipes/destructors retained; order 25, clasimp 188 and linarith 149. |
| linarithLib.sml/.sig and solver-record calls | LINARITH_ext_ss variants lift once; TraverseExt solver context, same certified budget closure; linarith 149, instances 52, clasimp and examples. Ordinary projection/destructor clients retained. |
| linarith/selftest Split sites | Simplifier-owned constructor/classifier and deliberate ordinary projection retained; original P-form/SIMPLE/full/hoisted tests plus first-error regression execute. |
| benchLib/benchGuards/named translation registry | Extension typed fragment registry and transported/derived sets from construction; typed exclusion adapter, same guards/names/solved sets; benchmarks 166. |
| seedCollections.sml/.sig algebra_ss/field_ss | Ordinary producers unchanged; ordinary empty/field/literal-exclusion tests retained in seeds 74. |
| splitIntegrationScript | Explicit splitter/persistence dependency, tracked BOOL before split_ss; rebuilt imported/local TypeBase proofs. |
| splitAttrScript | Explicit earliest dependency, ExclX for intended extended suppression, same ownership/inventory/proofs; fresh execution. |
| External Docfiles and Holmake edges | Canonical changes in consumer.patch, including aesop/clasimp/linarith and new ext recipe docs; all owning normal-level directories execute through explicit extension dependencies. |
| parityTranslationScript:7764 | Extension tactic on tracked default, supplied congruence/premise order retained; Script rebuilt/proved. |
| benchmarks/selftest:2212–2227 | Typed default closure, same negative symmetric_def and positive named bound assertions; benchmarks 166. |
| seeds/selftest:400–407,624–633 | Extension conversions on clasimp output; independent IMAGE/conditional-transitive proof assertions retained, seeds 74. |
| seeds/selftest:1088–1100,1280,1307,1456 | Typed bound/conversion inputs; reversal/append/bounded quantifier/narrow body assertions retained. |
| seeds/selftest:984,1001,1030 reverse boundary | Explicit tracked ordinary-default preparation, not clasimp configuration; independent FILTER/ZIP/set premise-order tests. |
| iffTestSupport:16–31,90–100 | Separate/parameterized ordinary and extension conversion paths; paired default observations retained. |
| iff_fragment_count:78–87 | Remains ordinary where consumed by iffBatchChild; not blanket extension-only. |
| Mixed rewrite_changes/renests/bottom-up comparison helpers | Typed ordinary and extension paths, both assertions retained; clasimp 188 and iff theory tests. |
| Pure iff theorem derivation 1080–1156 | Stays ordinary theorem computation; no extension-valued set returned. |
| iffBatch/iffBatchChild | Rebuilt original one-batch/independent-default proofs; typed observation helper. |
| iffBottomUp/iffBottomUpChild | Explicit typed bottom-up producer and shared original reducer closure; higher-order/bottom-up shape proofs. |
| iffDiamondChild | Rebuilt ancestry removal and independent default observations. |
| iffRoundTripBase/iffRoundTripChild | Captured typed declaration inputs/removals, fresh reloaded/default proofs and original ordinary observations. |
| iffWithinRemove/iffWithinRemoveChild | Qualified/local removals, same-name rule survival and both defaults; rebuilt/proved. |
| working_original/working_full/working_decision/plain_decision outputs | Opaque working state contains extension sets; every alias/callback path consumes typed outputs; clasimp lazy/generation/pointer tests. |
| install_supplied_rules/views, add_supplied_views, supplied_converse_working outputs | Extension inputs/outputs/bindings throughout supplied fixtures, not tactic-only renaming; clasimp actual-control tests. |
| bound_simplification_simpset/extend_invocation outputs | Typed bound state through all drivers and callbacks; compile-once/runtime/fact-role/continuation assertions execute. |
| Earliest clasimp fixtures 22–174;178–291;294–482 | Extension factories at the historical 70/116/162,198/268,322–327,365–378 boundaries, before preparation/install; E25 clasimp oracle/context/callback assertions. |
| Earliest fixtures 3998–4218;4220–4301 | Typed bases/named helper before install (4050/4181;4239–4241/4254); E25 clasimp abstraction and dependency assertions. |
| Earliest fixtures 4303–4551;4554–4842 | Typed helper/bases before compilation (4326–4328/4380/4509–4510;4568/4571/4745–4746); E25 incremental/bundle/control assertions. |
| Earliest fixtures 4845–5113;5116–5349 | Extension inputs before source handles/runtime (4869–4873/4917/4922/4993/5063;5134–5138/5215/5221/5233); E25 suspension/generation assertions. |
| Earliest fixtures 5352–5514;5515–5641 | Typed base/helper before preparation (5370–5375;5529–5533), including empty-set pointer check; E25 policy/metadata assertions. |
| Earliest fixtures 5644–5861;5864–6052 | Typed bases before reducer/bundle binding (5664–5667/5681–5688;5883–5884/5950/5971); E25 early binding/runtime retry assertions. |
| Earliest fixtures 6055–6185;6188–6398 | Typed bases/fragments before pipeline/fact preparation (6073–6075/6113–6115/6169;6207/6356–6358); E25 wrapper/role/driver assertions. |
| Earliest fixtures 6401–6479;6482–6665;6668–6785 | Typed bases before derivation/binding (6428–6429/6443–6446/6453;6500/6521/6582/6606;6697–6700/6725/6754–6756); E25 extensionality/transport/continuation assertions. |
| Additional explicit clasimp input list (934–3894 in EXTERNAL_TYPES) | Extension fixture aliases/factories before install for every listed input, not only added-API token sites; E25 clasimp 188 executes the original assertions. |
| normalised_subject_fragment/bottom_up_fragment | Separate typed producers; same live table-reading reducer closure lifted, not snapshotted; clasimp/benchmarks/iffBottomUp proofs. |
| weak CONG/list conversion/permutation | Explicit tracked fragment factories; private ordinary permutation set retained; clasimp tests. |
| ambient/supplied/fact view fragments | Extension constructors before install; lazy source/bundle tests. |
| benchmark translation_frag distribution and derived-set flow | Typed registry/marker/clean_simpset/callback/premeasurement sets through all ordinary-looking SIMP consumers, including Blast preprocessing; same exact benchmark results and no compile-time registry mutation. |
| Public/opaque/cached type sites, aesop caches and claset invocation polymorphism | Signature propagation in patch; compiled clients/theory proofs and classical/blast unit instances execute, no global specialization. |
| seeds ordinary table/local/persistent tests and arithmetic/integer/real seed Scripts | Ordinary producer semantics, theorem names and literal exclusions retained; seeds 74 and rebuilt Script closure. |

### EXTERNAL semantic assertion rows

Each is retained in E25's executed clasimp suite, not represented by a new
smaller substitute. Source inventories/patch and archived clasimp launcher
receipts bind them to the pinned input and migrated product.

| Historical range | Preserved contract |
| --- | --- |
| 22–174 | Indexed converse equals linear oracle; cold/warm charges and genuine validation. |
| 178–291 | NoAsms/IgnAsm/context selection and early abbreviations/labels. |
| 294–482 | Compile-once public/contextual/callback scope, nested cleanup and quotas. |
| 3998–4218 | Effective abstraction policy/filter/removal/identity/typed cutoff. |
| 4220–4301 | Failed-condition dependencies, exact charges, no native rediscovery of views. |
| 4303–4551 | Incremental/fresh metadata, precise invalidation and failed-cache retry. |
| 4554–4842 | Actual Once/Ntimes sharing, duplicate events, exhausted attachment/bundles. |
| 4845–5113 | Exact conjunct suspension/siblings/conditions and quota-free detection. |
| 5116–5349 | Lazy generations/pointers, preserving removal/exhaustion/Context restore. |
| 5352–5641 | Ambient/supplied policy, aliases/precedence and no quota revival. |
| 5644–5861 | Early binding without ambient reducer/view queries; table identity/retry. |
| 5864–6052 | Runtime/original install once; shared contexts/budget; provider retry. |
| 6055–6185 | FAST/depth/SAFE/CLARIFY one-bundle wrappers, untagged originals once. |
| 6188–6398 | Simp/Iff roles/fact IDs/support/requirements/labels, six drivers. |
| 6401–6479 | Effective extensional reading and discarded-rule exclusion. |
| 6482–6665 | Native origin/support/role and restored private quotas on cutoff. |
| 6668–6785 | Proper-argument views, continuation proofs and spent controls. |

### EXTERNAL_MARKERS MC01–MC14

| Row | E25 closure and executed evidence |
| --- | --- |
| MC01 | linarith classifier uses simpMarkerLib.DSplit; original P-form provenance, SIMPLE rejection/full consumption and new malformed/first-error ordering regression, linarith 149. |
| MC02 | claset extension-aware classification preserves Simp/Iff precedence and all bucket theorem identities/order, rules 147. |
| MC03 | simpMarkerLib wrapper stripping then classification on no-simpset route; content payload facts retained, controls inert, rules/classical tests. |
| MC04 | Same polymorphic invocation interface, forwarded unstripped controls once outside facts; explicit new ordered identity/fact-environment regression, rules 147; classical/blast unit instances execute. |
| MC05 | All original same_list conjuncts retained, extension Split/ExclX added to mixed bucket matrix, rules 147. |
| MC06 | Independent generic marker assertion retained, simplifier classifier exclusion added; rules 147. |
| MC07 | Explicit Split/ExclX and nested qualified controls inert without a simpset; same_rules/null rules/exact facts and positions retained, rules 147. |
| MC08 | Generic Req0/ReqD/Once construction/recognition retained, recursive payload stripping and exact fact theorem equality, rules 147. |
| MC09 | Generic DNoAsms identity after simpMarkerLib wrapper stripping; aesop NoAsms safe/conclusion-only assertions, aesop 148. |
| MC10 | Recursive bounded payload test before directive classification/bundle compilation; Split/ExclX skipped, genuine bounded rewrite retained; clasimp compile-once/partial/exhausted tests. |
| MC11 | Generic four tactic controls retained, extension partition elsewhere; clasimp requirement/Abbr/label/argument tests. |
| MC12 | Generic NoAsms/IgnAsm assumption predicate retained, not Split/ExclX; clasimp safe/raw policy assertions. |
| MC13 | Extension-aware classification rejects non-Split controls before assuming facts; linarith malformed/control/first-error tests. |
| MC14 | Classify before installing only simp_rules in tracked aesop base, forward controls once/in order; aesop rule/NoAsms/context tests. |

## Identity ledger and all temporary rows

Each IDENTITIES row has one deliberate final disposition, not an equal-valued
copy. The table closes dependency/identity requirements; it does not promise
concurrent access to mutable quotas or introspection of opaque closures.

| Historical identity row | Final owner/evidence |
| --- | --- |
| stack_limit | Sole Cond_rewr ref, live NONE per candidate/explicit SOME local, E12/E22/N. |
| Tracking extent | Single SimpTracking ThreadLocal slot; Cond_rewr aliases reporter/extent, both compilers report there, E12 source/nested-exception checks. |
| Trace | Original action/ref/hook/listener reused, E12/E13 source correspondence and callback tests. |
| BoundedRewrites controls | Original datatype/actual refs; paired/native/view/bundle/preserving paths share partial and zero, E12/E14/E19/E21/N. |
| Private quota scope | All initial tracked-net bounded entries, not just handles; Portable.finally and callback-abort restoration, E22 derivation/lifetimes. |
| Source serial/slot/origin | simpExtLib-only state; ordinary fragment/net allocation removed E15/E16, duplicate/conjunct/AC/order tests E21/N. |
| Named registry | Distinct `simpLib.ssfragDB` and `simpExtLib.ssfragDB` typed slots, not duplicate same-name slots; E24/E26 registry controls. |
| SF/late DFRAG | Engine-local registry at original late stage, replacement/rewind; N R4 and late-FRAG checks, E18/E20. |
| Context/Sref/TypeBase | Existing identities; opt-in provider slot only, pointer invalidation/rewind/factory order; E23/E24/E25. |
| BasicProvers state/log/derived registry | Remains ordinary; explicit tracked provider/typed updates, no mirroring/import; E24/E25. |
| ThmAttribute records/slots | Original exact records/functions, supplied/ambient read-only queries; src/1 retained plus E23 foreign-owner tests. |
| SplitData witness/tag/slots/handler/listener | Single private owner, transactional initialize/repair/retry/replay; E23/E26. |
| splitLib TypeBase/case caches | One splitter keyed by actual tyinfo identity, no implicit persistence; E23/N. |
| Marker constants/directives | One simpMarker theory and Legacy-wrapped generic datatype; no generic Split/ExcludeX restoration; E20/E23/E25 MC rows. |
| Travrules/Opening structural types | Original types/constructors shared by extension aliases; E13 signatures/type clients/proofs. |
| Traverse exception context/reducer | Original ordinary REDUCER; explicit extension lift keeps original payload/closure, E11/E22/E24 private-payload tests. |
| UNCHANGED/HOL_ERR/Interrupt/Option/user/searchBudget exceptions | Existing constructors/scopes retained, private policy-abort guard rethrows original failure; E12/E13/E18/E22/E25 cutoff/context tests. |

| Transition | Final status and concrete closure |
| --- | --- |
| X1 | **Closed 12:** simpExtLib calls Cond_rewrExt.prepare/runners, E12/E14. Historical graph edge is not a surviving import. |
| X2 | **Closed 13:** threaded compiler routes through TravrulesExt/OpeningExt, E13. |
| M0 | **Closed 11:** exact ordinary Traverse and congLib, E11. |
| M1 | **Closed 16:** no ordinary configured types/companions/bridge, E16 and ordinary runtime guard E26. |
| M2 | **Closed 16:** direct ordinary conditional compiler, no Cond_rewrExt import, E16. |
| M3 | **Closed 15/16:** threaded fragment edge removed 15; ordinary primitive/compiler baseline, E13/E15/E16. |
| M4 | **Closed 15/16:** no ordinary slots/origins/inventories/installation adapter, E15/E16. |
| M5 (graph M5a/M5b) | **Closed 16:** no ordinary strategy/simpMarker/split code or import, E16 plus E23/E26 fresh-process absence. |
| M6 | **Closed 26:** exact native file relocated to native-extension; ordinary selftest restored in full, independent launchers/explicit extension prerequisites and strict post-list full test, E26. Embedded ordinary comparisons in extension integration are intentional controls, not temporary ordinary library imports. |

## Documentation consumer disposition and limits

The required owner is part of closure even where no dedicated Docfile existed.
The definitive type/construction migration is published above and in
`src/simp/src/notes.md`; maintained compiled witnesses are
`../simp-ext/APIExamples.sml`, `../standard-recipes/selftest.sml` and
`src/boss/tests/tracked-defaults/selftest.sml` (repository paths under src/simp
for the first two). Documentation text alone is not executable evidence.

| Every CONSUMERS Docfile row | Final documented owner/decision |
| --- | --- |
| ExclX; Split; GEN_SIMP_TAC; GEN_GLOBAL_SIMP_TAC | `simpExtLib.*`, tracked PURE/BOOL before installation; marker construction remains pure. |
| add_looper; del_looper; set_looper; looper_ss | `simpExtLib.*`, tracked looper/fragment types. |
| add_safe_solver; add_unsafe_solver; set_safe_solvers; set_unsafe_solvers; remove_solver; mk_tactic_solver; safe_solver_ss; solver_ss | `simpExtLib.*` with TraverseExt solver/context, independent tracked recipe; no ordinary solver API promised. |
| set_cond_depth; set_subgoaler; set_term_ord | `simpExtLib.*`, invocation-local settings/shared live default distinction. |
| add_split; del_split; split_ss | `simpExtLib.*`, explicit tracked BOOL and separate persistence opt-in. |
| clear_rules; filter_rewrites; threaded_cong_ss | `simpExtLib.*`, tracked history/controls and explicit threaded factory. |
| legacy_traversedata_for_ss | Removed optional API; use total simpExtLib.traversedata_for_ss on an already tracked set; no ordinary-set conversion. |
| xtraversedata_for_ss | `simpExtLib.*` → TraverseExt.XTRAVERSE; complete configured pair, not default projection. |
| simpLib.Excl; simpLib.traversedata_for_ss | Retain ordinary literal strict deletion/unconditional original data; no migration or namespace behavior. |
| Cond_rewr.COND_REWR_CONVS | `Cond_rewrExt.COND_REWR_CONVS`; ordinary direct compiler and pure is_var_perm remain legal. |
| splitLib.SPLIT_TAC; enable_split_attribute; exclude_split | Keep singleton splitLib; direct splitting versus local extension tactic versus explicit persistent removal clearly distinct. |
| src/simp/src/notes.md | Ordinary/extension ownership, source/view/bundle/child-first construction and provider/update limitations; not mixed runtime dispatch. |
| No prior dedicated source/view/bundle/child-first Docfiles | These are simpExtLib APIs, covered by this final family/construction ledger and maintained typed examples; no retrospective import promise. |
| Cross-links/comments/example lexical rows in references.tsv | Historical navigation only; actual owner determined by operand type, not blind module substitution. Ordinary examples stay ordinary. |

**Documentation rows are closed by E27.** The filter/threaded Docfiles moved
to simpExtLib, the retired optional-projection Docfile was removed, new typed
construction/source/bundle Docfiles were added, and all affected cross-links,
examples, SSFRAG types and load preludes were checked against final signatures.
notes.md, README and MANIFEST now describe separate engines instead of mixed
representation/eligibility/goal-time dispatch. The reusable checker verifies
835 references across 83 current documents, including later typed catalogs
and provider signatures; 48 Docfiles process together and 30 extension/split
examples also execute in independent processes. The typed runtime examples
validate proofs and shared exhausted controls. Pandoc rendering is not claimed
on this host. The external patch's canonical Docfiles remain separately sealed
by E25, not silently replaced with main-checkout help output.

No actual required implementation capability is unresolved. Explicitly **not
offered**: promotion/import of arbitrary ordinary simpsets or congsets;
automatic mirroring of ordinary local/logged/Proof updates; source enumeration
or private-quota reset inside opaque lifted reducers; new concurrent-quota
safety. There is no implicit tracked wordsLib/PMATCH catalog: an actual caller
requiring one must supply an explicit typed recipe (E24); no inventoried
internal consumer requires it. These are deliberate boundaries, not completed
capabilities hidden behind an unchecked fallback.

## Historical inventory checks and final reconciliation

Read all migration supplements, the five consumer/identity ledgers,
MIGRATION, DESIGN, CUTOVERS, README, graph.json, final-apis.tsv and final
ordinary/extension core/provider signatures. Reviewed E25's actual patch
paths/marker regressions and E25/E26 final execution handoffs/receipts.
Those ledger-only checks did not execute HOL proofs or performance probes;
E27's subsequent executable/runtime and routine-build evidence is distinct.

Fresh offline checks at the audit base:

- `coverage_ledger.py`: **2,153 source-tied cases**, pass.
- `verify_evidence.py`: **37 immutable artifacts**, pass; expressly no HOL
  elaboration/benchmark inferred.
- Compatibility Python discovery: **151 tests**, pass.
- Interface Python discovery: **15 tests**, pass.
- Migration Python discovery: **12 tests attempted, seven errors** because
  its historical manifest hard-codes the now-moved external worktree path
  `/home/lukasz/dev/HOL/worktrees/isabelle-tactics`. This is an environment/
  reproduction-path limitation, not a missing engine API. The real pinned
  worktree is now under `/home/lukasz/work/HOL/worktrees/isabelle-tactics`
  (also recorded by E25). Do not regenerate historical provenance or call
  this default invocation a pass.
- A read-only relocation diagnostic subsequently passed **all 12 migration
  tests**: in memory only, remap that one old external prefix to the current
  prefix for `Path.open` and `inventory.git`, then execute the unchanged
  unittest suite. Every original source hash/anchor and marker-negative
  assertion remains checked. A file-read-only remap first exposed six Git
  cwd errors; remapping both read routes resolves them. No provenance,
  production/test source or external file was changed. This diagnostic does
  not make the default hard-coded-path invocation portable.
- `git diff --check`: pass after the ledger/notice edits.

Final E27 reconciliation reruns all 196 current compatibility Python tests,
15 interface tests and the 12 unchanged historical migration tests. For the
latter, a private read-only bind exposes the relocated external worktree at
its recorded historical path; no source/hash/anchor/provenance is regenerated.
The default test invocation then passes inside that documented namespace.
E27 also runs the live source gate, documentation gate, actual runtime
launchers, all ordinary/extension normal-level targets and the routine build.
The handoff retains commands, statuses and the resolved reproduction-harness
failures; there is no remaining documentation or external-path blocker.

Plan-wide remaining independent clean builds/full regressions, expanded
performance/allocation/statistical gates, optional level-2 external corpus and
other platforms are **not** certified by this migration documentation. E25's
optional pre-final corpus timeout is not counted as a pass. Numerical parity
is not inferred from the bounded source/identity/consumer closure.
