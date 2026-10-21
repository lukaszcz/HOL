# Repository consumer ledger

Paths/lines refer to inventory source `50cfa5d70`; `manifest.json` seals exact
bytes. API groups refer to [MIGRATION.md](MIGRATION.md). Every actual extension
caller below has implementation and final migration owners. All doc/example
migration is **TASK_27**; test separation is **TASK_26**, with the original
TASK_06 case IDs/assertions retained. No ordinary caller needs migration.

## Implementation and library consumers

| Caller | API/group and construction decision | Owner |
| --- | --- | --- |
| `src/simp/src/Traverse.sml:36–129,616–783` | T1 definitions/adapters and configured dispatch. Extract to distinct engine; lift ordinary reducers explicitly, preserving exception-valued context. No control/trace module copy | 09; ordinary restoration 11 |
| `src/simp/src/Cond_rewr.sml:177–290` | R1 paired preparation, live depth and configured wrappers; ordinary constructor must no longer prepare/discard configured runner | 12 |
| `src/simp/src/Travrules.sml:128` | C1 consumes `Opening.THREADED_CONGPROC`; extension construction only | 13 |
| `src/simp/src/simpLib.sml:22–162,276–345` | V1/B1 origin slots, paired compilation and fragment registry/construction. Move extension allocation behind distinct tracked types before fragment/rule install | 10/14; ordinary cleanup 15–16 |
| `simpLib.sml:590,616,1628,1681–1925` | T1 name inspection; C1 threaded compilation; E1 preserving replay, filters, clear, context deltas. Ordinary name inspection uses baseline destructor; extension history keeps origins/actual controls | 10/13/19/21; ordinary 16–17 |
| `simpLib.sml:2049–2150` | P1/T1 native configured reducer and projections; no callbacks at extraction; remove mixed eligibility/fallback from ordinary path | 10/11/14/16 |
| `simpLib.sml:2174–2422` | M1/V1/H1 marker dispatch, supplied argument preparation, quota scope and derivation; typed tracked set chosen before directives/rule installation | 19–22 |
| `simpLib.sml:2566–2570,2925,3048–3054` | A1/T1 global/child-first traversal and root context. Extension tactics only | 18/20/22 |
| `simpLib.sml:3088–3114,3124–3148` | B1 TypeBase fragment creation, printer inspection. Ordinary path allocates no source slots or configured adapters; explicit extension TypeBase recipe | 15–16/24 |
| `src/simp/src/congLib.sml:178–205,271–306` | C2/P1 uses `reducer_config_data`, configured wrapping, optional projection and `XTRAVERSE`. Separate configured module/input from ordinary `congset/simpset` before installation | 08/11/13/24 |
| `src/simp/src/simpMarkerLib.sml` | M1 recognizers, wrapper stripping and recursion over shared generic directives. Keep simplifier-only Split/ExclX interpretation | 20/23 |
| `src/simp/src/SplitData.sml`, `splitLib.sml`, `splitPersistLib.sml` | I1 registry/data/caches/explicit initializer; extension loading reaches them without putting persistence into ordinary simp dependency scope | 23/27 |
| `src/1/ThmAttribute.sml:87–88`, `src/1/selftest.sml:1617–1647` | I1 read-only handler lookups; actual non-simp test caller. Retain exact record pointer, supplied/ambient context and no callback/mutation assertions; **no relocation/type migration required** | 23/27 audit |

`src/basicProof/BasicProvers.sml` builds an **ordinary** default set. It is a
construction-provider dependency, not a source getter. Its seed/update/derived
state sites (`:1156–1178,1244–1317,1349–1388,1484,1499–1522`) matter because the
external clasimp default currently discovers sources there too late. **24** owns
the explicit extension provider/recipe design; **25** the external migration.
Ordinary BasicProvers update semantics and loading remain ordinary. See EXTERNAL.

## Native `src/simp/src/selftest.sml`

Ranges include legacy pins interleaved with extension cases. Never move a whole
range indiscriminately and weaken its ordinary control. The sealed TASK_06
ledger maps exact cases/anchors; these ranges are migration navigation.

| Lines / current caller | Earliest tracked construction | Assertions retained / owners |
| --- | --- | --- |
| 114–220, threaded congruence | Fragment factories 127–137,175–176,202 and extension Boolean base before add/merge/SF | Ordinary versus threaded results, later premises, RHS beta rebuild/LHS unchanged; **13**, migration **24/26** |
| 621–729, strategy-bearing SF and counted passes | Extension empty at 655–656, before strategy fragment install | Late strategy dispatch vs legacy/counting comparisons; **20/24/26** |
| 730–1533, contextual/configured traversal and congruence | Extension PURE/BOOL before reducer/rules; configured congruence fixture 1482–1531 must migrate as one unit | Solver/subgoaler calls once, depth 29/order, generic context, refresh, live/explicit/nested depth, child-first; **09–14/20/22**, callers **24/26** |
| 1534–1899, strategy mutation/clear/filter | Extension bases 1572,1612,1629,1656,1686,1744,1764,1818,1880 | Every strategy setter/removal; maker/history retained through clear/filter; **19/20/24/26** |
| 1900–2488, final solvers/loopers/exclusions | Tracked base before named rules and strategy installation | Safe/unsafe distinction, namespace collisions, strict Excl vs ExclX, priority/history/limits; **17/19/20/24/26** |
| 2489–2995, split core and integration | Direct split conversions need no simpset promotion; integration uses extension BOOL before split_ss/add_split | TypeBase cache replacement, proof/subgoal order, local/persistent suppression/replay; **23/24/26** |
| 2996–3591, Split/global/bounded/root | Extension PURE/BOOL at invocation construction | Invalid/unnamed markers, counted fixpoints, supplied bounds, root contexts, option/pair/list integration, real validations; **20/22/23/24/26** |
| 3592–3870, directive namespace matrix | Boundary base 3625–3626 before boundary_rule | Conversion rejection/inspection, prepare_rewrite_arguments, all collisions; **19/20/21/24/26** |
| 3871–5019, source/view/bundle/private quota | Detailed factory table below | **19/21/22**, callers **24/26** |
| 5020–5145, contexts/projections/congruence | Split ordinary vs extension factories at 5033–5037,5042–5048,5100–5142 | Once lifetime, total wrappers, collector and configured congruence stages; **11/13/20/22/24/26** |
| 5146–5597, late FRAG/maker/factory/markers | Tracked extension registry/sets before rules; retain ordinary cases separately | Lookup remains late; malformed tags/maker/AC and exception order remain exact; **16/18/20/24/26** |
| 5598–5902, inspection/generic facts/live controls | Extension builders for marker/strategy/context cases; ordinary reflexivity/factory fixtures stay ordinary | Binder protection, fact order, mutable depth, exact exceptions/primitives; **13/18/20/22/24/26** |
| 5903–6301, paired/projection/fallback | 6014–6017,6054–6057,6090–6091,6123,6183,6239,6272 before install | Late/exhausted projection extraction, no compilation/collectors, both use orders, shared quotas/views/replay; **12/14/21/22/24/26** |

### Source-sensitive fixture factories (no late discovery left unassigned)

| Fixture / lines | Construction to change, before installation/consumption | Semantic assertions / algorithm owner |
| --- | --- | --- |
| Abstraction policy 3873–3970 | Base 3901, before named source add 3924 | Full/partial abstraction, binder exceptions, charges, source prepend/tail pointer sharing; exclusion/filter/clear remove sources; conversions omitted. **21/22** |
| Prepared normalization 3971–4039 | 3984 before Once reducer; empty/keyless 4015–4021 | Root-preserving arguments, fresh private declared quotas/restoration on cutoff, ambient exhaustion unchanged, opaque pretest. **22** |
| Observer 4041–4120 | 4056 before conditional install | Unchanged/failed conditions observed, same charges, exact observer/charge/HOL exceptions. **22** |
| Views 4122–4312 | frag/attach 4150–4156; conjunct PURE 4205; duplicate/raw/merge/support/stale/AC 4220–4291 | Actual quota sharing in both engine/use orders; duplicate slot vs install; proof-sensitive identity; replay/filter origins; conjunct names/stale views/three AC components. **21** |
| Suspension 4315–4469 | fragment/installed 4333–4348; roots 4396–4408,4449 | Exact occurrence/conjunct and dependent views removed; sibling names/identity/quota survive; no-op pointers, duplicate handles/event groups, exhausted/partial controls, opaque facts. **21/22** |
| Preserving replay 4472–4550 | installed 4497–4499; bundle base 4532–4535 | Ordinary replay resets; preserving replay shares exhausted/partial controls and source identity; missing name UNCHANGED; exhausted views stay exhausted. **19/21** |
| Bound global 4553–4697 | 4589–4593 before maker/bundle; subsequent bases 4598–4674 | Compile once, invocation-wide bounds/saved reuse/marker replay, deferred solvers/untagged facts, NoAsms/IgnAsm, root context and real proofs. **20/21** |
| Bound arguments 4700–4755 | base() 4713–4716 before bounded survivor | No-directive pointer identity, exact theorem/tag pointer, spent survivor controls, ExclX deletion/SF addition. **19/21** |
| Prepared replay 4758–4859 | 4777–4785 before maker/bundle | No maker rerun under remove/suspend/marker/filter; exact origins and sharing, reset replay retains conjunct relationships. **19/21** |
| Preserving filter 4862–4930 | 4879–4885; ambient 4913–4914 | Compile once, aliases share source quota, precise removal/no-op pointer, ordinary reset vs preserving exhaustion. **19/21** |
| Combined bundles 4933–4992 | 4949–4955 before preparation/consumption | Origins/events/spent controls retained; duplicate bindings/reinstallation rejected; no recompilation. **21** |
| Context changes 4994–5018 | configured() 4999 before solver configuration | Same ordered solver identities do not rebuild; replace/remove/reorder does. **21** |

Factories/call sites above complete under **TASK_24**, with algorithm contracts
owned by the indicated tasks and relocation under **26**. Late extraction at
6010–6110 must remain late: tracking moves earlier, not extraction. Preserve
zero compilation traces and maker count one after exhaustion, collector-free
extraction through 6297, exact dproc identity, default public projection omitting
configuration, and configured fallback collector stages `[0,1,2]`.
`rewrite_source_compare` has no direct nonimplementation repository caller;
external clasimp does call it, so it is not dead API.

## Focused suites and exported theory dependencies

Paths below are relative to `src/simp/tests/` unless stated otherwise.

| Consumer | Construction/dependency and invariant | Owner |
| --- | --- | --- |
| `markers/selftest.sml:1–364` | Simplifier vs generic directive identities, wrapper order, all-byte string recognizers, pure inspection and recursive processing; generic marker APIs unchanged | 20/23/26 |
| `split-registration/selftest.sml:1–460` | Extension BOOL at 77–99; exact handlers/listeners, rollback, pruning, ownership and retry; no implicit opt-in | 23/24/26 |
| `replay-order/selftest.sml:1–89` | Private ordered replay/diamond ancestry, alias/theorem identity and writing-theory REMOVE names | 23/26 |
| `fresh-load/selftest.sml`, `control.ML`, `identity-before.ML`, `identity-after.ML`, `syntax.ML` | Six fresh processes, exact handler/listener pointer/order assertions, foreign attribute/set/syntax before/after, no ordinary load claiming persistence. Update module-load assertions to final graph, not weaker ownership predicates | 23/26/27 |
| `split-persistence/selftest.sml`, `optIn.ML`, `heapSave.ML`, `heapVerify.ML`, `verify.ML` | Eight fresh scenarios including actual saved-heap reload; verify.ML:32 chooses extension BOOL before split_ss; alias exclusions 38–43, DB pointer/marker ancestry 49–53 | 23/24/26 |
| `split-persistence/splitParentScript.sml:1–22` | `Libs: splitPersistLib`; earliest-parent add_ML_dependency at 7; split declarations 9–11, REMOVE 13–14, exported markers 21–22 | 23/27 |
| `split-persistence/splitChildScript.sml:1–21`, `splitDescendantScript.sml:1–12` | Ancestor dependency initializes before replay without descendant opt-in; qualified REMOVE and same-name descendant survival | 23/27 |
| `src/simp/src/simpMarkerScript.sml:1–13` | Qualified Split/ExcludeX theory constants and non-invasive overloads; keep theory ML dependency where constants escape | 20/23/27 |
| `src/simp/src/boolSimpsContextScript.sml:1–46` | Ordinary shared theorem producer for both recipes, **not** a configured extension consumer | 24/27 audit |
| `src/simp/src/Holmakefile:14,16–45,64–101` and focused Holmakefiles | Keep normal selftest-level wiring after module/test separation; explicit dependencies on new modules only for extension suites | 26/27 |

## Docfile consumers (all owned by TASK_27)

Every listed file is under `help/Docfiles/`. For the following, prefix names with
`simpLib.` and suffix `.smd`:

- `ExclX`, `Split`, `GEN_SIMP_TAC`, `GEN_GLOBAL_SIMP_TAC`.
- `add_looper`, `del_looper`, `set_looper`, `looper_ss`.
- `add_safe_solver`, `add_unsafe_solver`, `set_safe_solvers`,
  `set_unsafe_solvers`, `remove_solver`, `mk_tactic_solver`, `safe_solver_ss`,
  `solver_ss`.
- `set_cond_depth`, `set_subgoaler`, `set_term_ord`.
- `add_split`, `del_split`, `split_ss`, `clear_rules`, `filter_rewrites`,
  `threaded_cong_ss`, `legacy_traversedata_for_ss`, `xtraversedata_for_ss`.

Related boundary files: `simpLib.Excl.smd`,
`simpLib.traversedata_for_ss.smd`, `Cond_rewr.COND_REWR_CONVS.smd`,
`splitLib.SPLIT_TAC.smd`, `splitLib.enable_split_attribute.smd`,
`splitLib.exclude_split.smd`, and `src/simp/src/notes.md`.

Examples beginning with ordinary `bool_ss` must choose the tracked BOOL recipe
before rules/strategies; ExclX's PURE/named-rewrite example needs tracked PURE.
Keep legacy examples legacy when documenting unchanged ordinary APIs. There
are currently no dedicated source/view/bundle or child-first docfiles: **27**
must document these construction/type migrations, not just rename existing
files. `references.tsv` includes cross-links, comments, notes and exact lines.

## Preserved legacy inputs and resolved lexical nonconsumers

- TASK_04's seven immutable signatures and nine sealed public clients remain
  unchanged. Their original reducer/dproc/congset type identities do not migrate.
  TASK_05's independent stage/proof suite remains baseline-only, including late
  labels/FRAG but early requirements/abbreviations. **26/27** audit preservation.
- TASK_06's `coverage-ledger.json.gz` retains **2,153 IDs**, including **630 native**
  checks. Native 0491–0502 each contain many invariants. **26** must preserve
  bodies, matrix rows and IDs, not merely counts. Paired/prior/performance
  baseline fixtures are not branch extension consumers to mechanically rename.
- Existing ordinary `dproc_ss` clients include `SatisfySimps.sml:16`,
  `src/pattern_matches/patternMatchesLib.sml:53`,
  `src/quantHeuristics/quantHeuristicsLibBase.sml:2990–3004` and the maintained
  TraversalContracts, ExclusionParsing and LegacyFailures fixtures. Their
  ordinary `REDUCER` values stay ordinary. **11/24/27** audit, no migration.
- Ordinary `congLib` clients under
  `examples/logic/temporal_deep/src/{examples,translations,model_check,
  deep_embeddings,tools}/` use ordinary congruences. Full paths/lines are in
  references.tsv; **11** restores their path, **24/27** audit, no migration.
- `developers/genUseScript.sml`'s `default_config`, `src/refute/Canon.sml:486–498`'s
  local `split_thms`, and
  `examples/machine-code/hoare-triple/set_sepScript.sml:60`'s local `SPLIT_TAC`
  are unrelated names, not extension calls. `Split` also appears as a term,
  theorem name, prose, local helper or unrelated datatype in examples/Manual.
  `ThmSetData`'s `current_data/theory_data/raw_delta`, generic marker
  `dest_directive/is_directive`, and prose `exclude/initialize` likewise do not
  call the new modules. Those lexical rows are explicitly **not migration
  requirements**; **27** final sweep checks qualification before edits.

There is no unclassified source-sensitive production library elsewhere in this
repository at the inspected revision. The additional external consumers and
legacy upstream source differences are separately recorded in EXTERNAL.md.
