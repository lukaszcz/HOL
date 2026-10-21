# External marker-classification boundary

Continuation of [EXTERNAL.md](EXTERNAL.md), at the same read-only external
revision `442009a1f7f04366573dc2b649d31650ea7b113b`. Paths below are relative to
that checkout. These are **actual consumers**, not dispositions of lexical
`Split` homonyms. **TASK_25 owns every row**, including assertion-preserving
migration, dependency changes and execution in an isolated checkout only.
TASK_08 finalizes interfaces; TASK_20 supplies the extension marker boundary;
TASK_27 audits the final dependencies. No external source was changed or run.

## Type and ownership decision

The older external checkout puts `Split`, `DSplit` and `strip_wrappers` in
`markerLib`. The inspected simplifier instead keeps Split/ExclX recognition in
`simpMarkerLib` (public extension constructors via `simpExtLib` after cutover).
Its `directive` is a **different datatype**:

- `simpMarkerLib.Legacy d` contains the unchanged `markerLib.directive`.
- `simpMarkerLib.DSplit th` and `DExclX name` are simplifier-owned controls.
- `simpMarkerLib.is_directive` recognizes both vocabularies. Generic
  `markerLib.is_directive` must NOT be extended to recognize Split/ExclX.
- `simpMarkerLib.strip_wrappers` strips Req0, ReqD and bounded wrappers using
  the shared generic constructors, recursively; it does not unwrap Split into
  a fact. The current generic signature has no `strip_wrappers` export.

Consequently a blanket module rename is wrong too: generic-only tests and
matches may retain `markerLib.dest_directive` and its constructor identities.
Where a match must recognize both vocabularies, wrap its generic patterns in
`Legacy` and handle extension controls explicitly. No generic marker provider,
postkernel machinery or global directive registration is to be changed.

Marker classification itself needs **no source tracking or simpset promotion**.
Construct the extension marker before classification; when controls reach a
simpset-aware consumer, its input must already be the tracked set/recipe in
EXTERNAL_TYPES.md, before relevant rule/counter installation. The no-simpset
classical path must remain usable without building a tracked simpset. TASK_08
must settle an explicit classification adapter/dependency if loading
`simpMarkerLib` directly from generic claset code conflicts with its load
boundary; neither an adapter nor a direct dependency may turn these controls
into assumptions or specialize `'a invocation_simpset` to an extension type.

## Consumer migration table

The MC IDs and exact source ranges are checked by `inventory.py`. Each row
records old API/type, replacement, earliest decision and assertions, rather
than counting a lexical reference as a migration entry.

| ID | External caller/source range | Old module/type/API | Replacement module/type/API | Earliest construction/boundary | Assertions to preserve | Owner |
| --- | --- | --- | --- | --- | --- | --- |
| MC01 | `src/auto/linarith/linarithLib.sml:117–122` | classify_split_argument: markerLib.dest_directive / markerLib.DSplit | simpMarkerLib.dest_directive / simpMarkerLib.DSplit; other directives still fall through to plain_argument's rejection | Build simpExtLib.Split before simple_argument/full_arguments; no tracked import needed for arithmetic classification | check_asm_split P-form validation precedes accepting OR rejecting Split, with original function/error provenance; SIMPLE rejects valid Split, full LINARITH consumes it; left-to-right first-malformed error and fact/split order remain | TASK_25 |
| MC02 | `src/auto/rules/clasetLib.sml:1186–1208` | simp_arg_bucket / classify_simp_args: markerLib.is_directive; simp_arg_split theorem-list buckets | simpMarkerLib.is_directive or explicit equivalent extension-aware classifier boundary; simp_arg_split remains thm lists | Select classifier before bucket/extend/assumption insertion; pure recognition, no simpset construction | Simp/Iff payload precedence unchanged; generic AND Split/ExclX controls go to SimpControl, never Plain; each bucket retains theorem identity and input order | TASK_25 |
| MC03 | `src/auto/rules/clasetLib.sml:1231–1246` | invocation_facts: markerLib.strip_wrappers then classify_simp_args | simpMarkerLib.strip_wrappers then extension-aware MC02 classification | Strip content-bearing wrappers before classification, only in no-simpset invocation_facts; do not strip controls on the forwarding path | Req0/ReqD/bounded payloads become facts with hypotheses intact; Split/ExclX and other inert controls are discarded, not assumed or executed; Simp/Iff and Aesop-only marker diagnostics retained | TASK_25 |
| MC04 | `src/auto/rules/clasetLib.sml:1694–1717` | with_invocation_fact_env_raw: classify_simp_args at 1703, simp_controls forwarded to body | MC02 classifier; same polymorphic 'a invocation_simpset and theorem-list controls, extension set only at extension-aware instantiations | With simpset: classify before extend, process_claset_tags and create_environment; tracked base chosen by caller before rules/counters; without simpset use MC03 | Forward controls unstripped/in order exactly once to body; never place them in leftovers/fact environment; Simp/Iff reach extend, classical tags still processed, no-simpset path stays inert and generic unit instances stay valid | TASK_25 |
| MC05 | `src/auto/rules/selftest.sml:2914–2940` | bucket-order test uses classify_simp_args and generic Excl/bounded control theorems | MC02 classifier; retain generic marker constructors and add extension Split/ExclX coverage | Construct both vocabularies before mixed argument classification; no tracked set | Keep all four same_list assertions, theorem identity and bucket order; extension controls must also be forwarded in order, never become rest facts | TASK_25 |
| MC06 | `src/auto/rules/selftest.sml:2943–2948` | generic markerLib.is_directive excludes claset markers | Keep generic assertion; add simpMarkerLib.is_directive exclusion assertion at the extension boundary | Recognition-only test; no generic datatype/provider change | Every claset marker remains outside both directive vocabularies; do not replace the independent generic check | TASK_25 |
| MC07 | `src/auto/rules/selftest.sml:3064–3094` | inert generic marker test: markerLib.Split at 3071; List.all markerLib.is_directive at 3085 | simpExtLib.Split (or simpMarkerLib.Split); simpMarkerLib.is_directive for mixed list, plus ExclX control coverage | Construct extension marker before invocation_claset; no simpset/tracking required | Retain same_rules baseline equality, null rules, both ListPair.allEq fact equalities and plain theorem's position amid controls; all controls recognized, no directive theorem or marker hypothesis leaks into facts | TASK_25 |
| MC08 | `src/auto/rules/selftest.sml:3098–3111` | content-bearing wrapper test uses generic Req0/ReqD/Once and markerLib.is_directive | Keep generic recognition/constructors; invocation_claset follows MC03 strip/classify boundary | Nested wrappers built before invocation; strip recursively, not just outer wrapper | Retain generic is_directive assertion, null rules and exact same_thm payload fact equality; do not drop wrappers with their content as though inert controls | TASK_25 |
| MC09 | `src/auto/aesop/aesopRule.sml:327–330` | is_no_asms: markerLib.dest_directive (markerLib.strip_wrappers theorem) / DNoAsms | markerLib.dest_directive (simpMarkerLib.strip_wrappers theorem) / same generic DNoAsms; alternatively Legacy DNoAsms through explicit extension classifier | Strip before NoAsms test; tracked aesop recipe already selected before simp rule installation | NoAsms selects safe conclusion-only GEN_SIMP_TAC rather than global assumption traversal; do not change generic constructor identity or mistake Split for NoAsms | TASK_25 |
| MC10 | `src/auto/clasimp/clasimpLib.sml:1116–1121` | marker_skip: markerLib.dest_directive / DBounded recursive payload test | simpMarkerLib.dest_directive, Legacy (markerLib.DBounded (body,_)) recursion; all other recognized directives skipped | Partition controls before prepare_rewrite_bundle compiles originals, not after supplying views | Split/ExclX never compiled as original rewrites; bounded ordinary rewrite remains original, bounded directive remains control; classical marker skip and order unchanged | TASK_25 |
| MC11 | `src/auto/clasimp/clasimpLib.sml:1793–1799` | is_tactic_control: markerLib.dest_directive / DNoAsms, DIgnAsm, DAbbr, DLabel | Keep generic recognizer/patterns; extension controls handled by prepare_rewrite_arguments and MC10, not here | Select controls before prepare_invocation_rules strips requirements and binds originals | Exact four generic control classes retained; Split/ExclX must not become assumption/tactic policy or be applied twice | TASK_25 |
| MC12 | `src/auto/clasimp/clasimpLib.sml:1801–1806` | is_assumption_control: markerLib.dest_directive / DNoAsms, DIgnAsm | Keep generic recognizer and same datatype constructors | Test assumption policy independently of extension control partition | Only NoAsms/IgnAsm qualify; Abbr/Label/Split/ExclX do not; preserve recursive safe/raw assumption policy | TASK_25 |
| MC13 | `src/auto/linarith/linarithLib.sml:94–111` | plain_argument: clasetLib.classify_simp_args / simp_controls | MC02 extension-aware classifier; existing plain/marker rejection | Classify before assuming a supplied fact; no simpset construction | Reject Simp, Iff and non-Split simplifier controls under original function name, then other claset markers; only singleton plain rest can become a fact | TASK_25 |
| MC14 | `src/auto/aesop/aesopRule.sml:347–358` | simp_rule: clasetLib.classify_simp_args / simp_controls | MC02 classifier; tracked aesop set and extension tactic in simp_rule_with | Classify before installing simp_rules into already tracked aesop recipe | Only simp_rules compiled as rewrites; controls forwarded in order with identity intact to simp_rule_with, including NoAsms and extension controls | TASK_25 |

`clasetLib.sig:153–159`'s public `simp_arg_split`/`classify_simp_args` retains
its theorem-list representation; the classification vocabulary changes, not
the theorem type. Its dependency/adapter is part of MC02, not a second registry.

## Executable assertions required of TASK_25

In addition to MC05–08's **unchanged original conjuncts**, retain linarith's
`selftest.sml:1883–1898` SIMPLE marker rejection, `:2312–2325` full LINARITH
per-call Split success versus no-Split failure (real validation), and
`:3833–3858` hoisted Split/table-update behavior. The P-form check, first-error
order and malformed-Split rejection in MC01 remain obligations even though the
existing listed tests alone do not establish every one of them.

Retain `rules/selftest.sml:3025–3040,3045–3060` classical-marker pass-through
and mixed leftover order, `:3098–3111` wrapper payload preservation, and the
Simp/Iff/Aesop-only rejection tests immediately before MC05. Extend the mixed
controls matrix to Split/ExclX on **both** routes: no simpset discards controls;
with a simpset forwards them unchanged once, leaving only plain facts for the
environment. aesop's `selftest.sml:1014–1048` NoAsms observations and clasimp's
supplied bundle/requirements/assumption-policy assertions remain independent.
Do not weaken `same_thm`, `same_rules`, proof/hypothesis checks or order checks
into counts, and do not classify extension controls as Plain to avoid adding
the explicit dependency/adapter.

This inventory records the required isolated migration and assertions, not a
claim that these old consumers currently compile against the new boundary or
that TASK_25's migration/build gate has passed.
