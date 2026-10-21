# External producer-output and type-boundary closure

Continuation of [EXTERNAL.md](EXTERNAL.md), same pinned external revision.
**TASK_25 owns every external caller/migration below**, including compilation,
assertion-preserving tests, signatures, inferred helper types, docs and build
edges. TASK_08 finalizes type interfaces and TASK_24 supplies standard tracked
recipes/provider boundaries. These callers often use **ordinary API spellings
on future extension-typed values**, so a direct added-API token search alone
would miss them. D1 indexes producer/helper references in references.tsv.

All paths below are relative to the external checkout; short filenames are
under `src/auto/` unless stated otherwise. The generic-to-simplifier-owned
**marker classifier** boundary is a separate actual-consumer table in
[EXTERNAL_MARKERS.md](EXTERNAL_MARKERS.md): linarith Split extraction, claset
bucket/forwarding/inert-fact paths, their tests and generic-only dispositions.
It needs no late source promotion; all isolated migration belongs to TASK_25.

## Direct downstream uses of default outputs

| Caller | Required type/construction decision and assertions |
| --- | --- |
| `benchmarks/parityTranslationScript.sml:7764` | `source_set_zip` passes clasimp_ss() to ordinary SIMP_TAC. Use extension tactic on tracked default; retain ZIP/set characterization, supplied reverse conjunction congruence and premise/context order |
| `benchmarks/selftest.sml:2212–2227` | simp_closes closes over clasimp_ss(). Keep both negative symmetric_def and positive benchNames "sym_def" moved-bound assertions |
| `seeds/selftest.sml:400–407,624–633` | FULL_SIMP_TAC/SIMP_CONV take clasimp_ss(). Retain universal IMAGE-through-implication and conditional transitive side-condition proof (AUTO would mask this regression) |
| `seeds/selftest.sml:1088–1100,1280,1307,1456` | Bound asm_full_simp and additional explicit conversions on clasimp default. Retain reversal/append, conditional IMAGE, both bounded-cons quantifier reductions and narrow-scope normalized-body rewrite |
| `seeds/selftest.sml:984,1001,1030` | **Reverse boundary:** ordinary srw_ss() passed to extension-facing asm_full_simp. Supply tracked ordinary-default recipe, not the differently configured clasimp default; retain flattened-set, ZIP-prefix and FILTER premise-order checks |
| `clasimp/iffTestSupport.sml:16–31,90–100` | rewrite_changes and rewrites_to infer one simpset type but consume both srw_ss() and clasimp_ss(). Split ordinary/extension helpers or parameterize by conversion; never erase either independent default check |

Complete named `clasimp_ss` consumer paths: `benchmarks/benchGuards.sml:240`,
`benchmarks/benchLib.sml:702,730`, both benchmark sites above,
`clasimp/iffTestSupport.sml:31,100`, `clasimp/clasimpLib.sml:3968,4041`,
`seeds/selftest.sml:405,628,1088,1280,1307,1456`, and
`clasimp/selftest.sml` (all exact lines in D1 references.tsv). Internal producer
hook: clasimpLib.sml:1683,1700. `aesopData.sml:49` is a comment, not a call.

`aesop_ss` producer/cache: `aesop/aesopData.sml:35,51–91,94–120` (late base read
110). Consumers: `aesopLib.sml:207,215`, `aesopRule.sml:353–357`,
`aesop/selftest.sml:42,57,65,72,75,96,102,122,126,3547,3614,3620,3624`,
`aesop/theory_tests/aesopSimpRoundTripBaseScript.sml:26` and
`aesopSimpRoundTripChildScript.sml:15`. Helper closure includes selftest:16–19's
rewrite_rhs, aesopRule:332–340's simp_rule_with, :531–538 contextual assembly,
aesopLib:27–54,114–121,162–197 sessions/safe/raw/invocation code. Track base
before weak congruence/ETA/solvers/theorems; retain depth 40, safe solver,
update/Context.restore and attribute invalidation, absence of inherited clasimp
splitting, ETA matching, unsafe-base sentinel and immediate/reloaded attribute
behavior.

Explicit aesop inputs also need tracked construction (no aesop_ss call):
`aesop/selftest.sml:861–864,3239–3241,3249,3262–3264,3806–3808,3851–3853,
3874,3882,3890,3895,3903,3966,3969,4008,4011,4268–4269,4379–4383,4444–4448,4483`.
Retain safe replay, supplied contextual set, cutoff/resume accounting and splits.

## Mixed iff helpers and exported theories

`clasimp/iffTestSupport.sml:78–87`'s iff_fragment_count currently has an ordinary
consumer only (`theory_tests/iffBatchChildScript.sml:22`); do not mechanically
make every helper extension-only. `clasimp/selftest.sml:1186` aliases
rewrite_changes, with paired ordinary/extension uses at 1218–1219,1230–1232,
1406–1407,1418–1420,1545–1546,1556–1557. `renests:3536–3541` likewise takes both
defaults: retain ordinary renesting vs clasimp non-renesting with typed paths.

Mixed bottom-up/child-first comparison inputs occur at selftest:1350–1367,
1472–1511,1573–1578, including normalised_subject_fragment. Split ordinary
comparison vs extension construction before fragment addition. Pure theorem/rule
iff derivation at 1080–1156 can remain ordinary; it returns no extension set.

Transitive helper users, all under `clasimp/theory_tests/`:

| Script | Helper lines / retained contract |
| --- | --- |
| iffBatchScript.sml; iffBatchChildScript.sml | 41; 15,22 — one-batch fragment and independent defaults |
| iffBottomUpScript.sml; iffBottomUpChildScript.sml | 43,46,65,74,76; 17,20,24 — higher-order/bottom-up shapes |
| iffDiamondChildScript.sml | 15,19 — ancestry removal |
| iffRoundTripBaseScript.sml | 24,56,90,94,115,138,164,188 — declaration/removal and shape |
| iffRoundTripChildScript.sml | 41,45,49,53,57,59,63,67,107 — reloaded/default observation |
| iffWithinRemoveScript.sml; iffWithinRemoveChildScript.sml | 21,53,72,120; 10,23,31,39 — qualified/local removal and independent same-name rules |

Keep both ordinary and extension observations; the extension migration must not
replace proof of ordinary persistent behavior with a test of the other default.

## Derived outputs, caches, aliases and captured sets

These clasimpLib API results become extension sets even though their consumers
may call only baseline SIMP_CONV/inspection APIs:

| Producer | clasimpLib.sig lines | clasimpLib.sml lines |
| --- | --- | --- |
| working_original / working_full_simpset | 89 / 91 | 1633 / 1635 |
| working_decision_base / working_plain_decision_base | 92–93 / 94–95 | 1636 / 1638 |
| install_supplied_rules / install_supplied_views | 114–115 / 145–146 | 1146–1147 / 1165–1169 |
| add_supplied_views / supplied_converse_working | 148–149 / 162 | 1172–1178 / 1393 |
| bound_simplification_simpset / extend_invocation | 183–184 / 309–312 | 1604 / 2830 |

Follow aliases `full`, `decisions`, `plain`, `get`, `ss`, `converted`, `#stripped`
and callback-captured sets, not just qualified producer calls. Downstream uses
are in clasimp/selftest.sml:4612–5002 (supplied installations),
5119–5323,5535–5629,5794–5795 (working state outputs), 5707,5720,5752 (early
converse), 5899,6118,6440–6453,6537,6629 (bound outputs). Their exact producer
reference lines are in D1; source constructions below fix the typed inputs.

Earliest tracked fixture factories, **all in clasimp/selftest.sml**:

| Fixture | Change factory before first install/preparation |
| --- | --- |
| 22–174; 178–291; 294–482 | 70,116,162; 198,268; default update 322–327 and fragments 365–378 |
| 3998–4218; 4220–4301 | 4050,4181; named helper 4239–4241 and base 4254 |
| 4303–4551; 4554–4842 | named helper 4326–4328,4380,4509–4510; 4568,4571,4745–4746 |
| 4845–5113; 5116–5349 | 4869–4873,4917,4922,4993,5063; named helper 5134–5138,5215,5221,5233 |
| 5352–5514; 5515–5641 | 5370–5375; 5529–5533 (including extension-empty pointer check 5628–5630) |
| 5644–5861; 5864–6052 | 5664–5667,5681–5688; 5883–5884,5950,5971 |
| 6055–6185; 6188–6398 | 6073–6075,6113–6115,6169; 6207,6356–6358 |
| 6401–6479; 6482–6665; 6668–6785 | 6428–6429,6443–6446,6453; 6500,6521,6582,6606; 6697–6700,6725,6754–6756 |

Additional explicit extension inputs outside those fixtures:
934,951,968,1719,1743,1757,2011,2034,2048,2070,2090,2130,2917,2929,
3652–3654,3801–3803,3841–3842,3862–3865,3892–3894.
Semantic assertions are the per-range table in EXTERNAL.md: actual-counter
sharing, origin/context identity, lazy compile-once runtime, proof validation
and exception/budget restoration must remain intact through these type changes.

## Fragment producer closure

| Producer | All named use sites / disposition |
| --- | --- |
| ORDER_ss / ORDER_ss_budgeted | clasimpLib:572,1763; clasimp/selftest:5182,5235,5584,5599,5610; order/selftest:396,447,476,507; linarith/selftest:2700. Ordinary standalone recipes remain; explicit extension variants/lifts for clasimp |
| LINARITH_ss / LINARITH_ss_budgeted | clasimpLib:583,1768; same clasimp selftest sites; linarith/selftest:2553,2742,2756; linarith/instances/selftest:794; examples/linarithExamplesScript:175. Same ordinary/extension recipe split |
| normalised_subject_fragment / bottom_up_fragment | Factory clasimpLib:2591–2616; first install/table update 2620–2632; public sig:297; uses clasimp/selftest:1489,1508,1577 and benchLib:956. Keep ordinary-default installation at 2624 and explicit extension-default recipe, sharing live table-reading closure rather than snapshotting/duplicating callback |
| weak CONG/list conversion/permutation | clasimpLib:351–360,484–491; 392–405; 469–481. Extension fragment factories at use; private permutation normal-form set 430–439 can remain ordinary inside opaque conversion |
| ambient/supplied/fact view fragments | clasimpLib:1037–1038,1587–1588,1177–1178,1596–1597,3161–3162. Extension factories before view install |
| benchmark translation_frag | benchLib:217–223 constructs/names/registers/SF; simp_controls:574–575 distributes it to 1243,1253,1259,1322,1372,1486,1492,1499,1511,1516. Extension typed registry/marker, not a late tactic-only rename |
| seedCollections.algebra_ss / field_ss | Factories seedCollections.sml:14–30, public sig:8–9. Only executable uses seeds/selftest:25,26,442–445,478,479; field installed in ordinary empty set and literal exclusion 438–459. Keep both producers ordinary unless an actual extension installation is introduced |

ORDER/LINARITH ordinary reducer/destructor clients remain ordinary, notably
linarith/selftest:2464,2592,2700–2705's deliberate ordinary traversal extraction.
Preserve admission screens, certified contexts, relevance gating **before**
charges and zero-budget typed cutoff. Direct solver-record calls also need new
solver/context types: linarith/selftest:2509,2777,2802,2895,3353,3386,3663,3780,3903;
linarithLib.sml:1657,1666–1671 and sig:49,57–58. Do not copy budget/context closures
just to produce two superficially equivalent fragment types.

Seed table/local/persistent tests remain ordinary: seeds/selftest:410–434,
438–459,463–479; arithmeticAutoSeedScript:76–94, integerAutoSeedScript:29–89,
realAutoSeedScript:29–530. Keep kernel theorem names and ordinary literal field
exclusion, not an extended namespace substitute.

Benchmark derived-set flow: benchLib:727–734 clean_simpset; 757–761 callback;
952–956 subject fragment; 1213–1224 equality pass; 1235–1516 Simp/Auto/Blast/Force/
Fastforce/Clarsimp/Aesop; 1532–1557 recipe reuse; 1662–1674 preparation before
measurement. Blast preprocessing also calls SIMP_TAC:1322 and SIMP_CONV:1371 on
extension inputs despite the final engine being claset-only. Preserve analogue
exclusion, APPEND_ASSOC history, shared prepared sets/timing placement and no
registry mutation during compilation (benchmarks/selftest:625–631).
`benchLib:699–702`, `benchGuards:240`, `clasimpLib:865,3019` inspect fragments only.

## Public/stored type and dependency closure

`clasimpLib.sig` simpset inputs/outputs at
32,37,44,61,66,75,88–95,101,106,112–115,145–149,159,162,181–184,201–202,
220,234,248–254,309–320,325–338,346,356–364, plus source/policy/fragment types in
EXTERNAL.md. Opaque containers carry these identities: lhs_view_table:68,
working_simpset:81, supplied bindings:103,117,152, bound state:169.
Stored implementation type sites include clasimpLib.sml:60,191,206,687,712,722,
886–896,1124,1152,1193,1286–1301,1568–1569,1629–1630,1835,2852,2871,3521.

Aesop public types: aesopData.sig:3, aesopLib.sig:17,19,24,
aesopRule.sig:95,132; caches aesopData.sml:35,82–84 and solver annotations
selftest:3601,3610. Preserve **polymorphic** clasetLib `'a invocation_simpset`
(sig:166–170,180,197; sml:1680). Instantiate extension set at aesopLib:186 and
clasimpLib:3396, but keep tableauLib:31 and classicalLib:445 unit instances;
never specialize the shared generic type globally.

External docfiles require actual isolated patch updates under TASK_25 and final
TASK_27 audit: aesopLib.CS_AESOP{,_SAFE}_TAC; clasimpLib.CS_AUTO_TAC,
CS_BESTSIMP_TAC, CS_CLARSIMP_TAC, CS_FASTFORCE_TAC, CS_FORCE_TAC, CS_SLOWSIMP_TAC,
add_safe_simp_wrapper, add_simp_wrapper; linarithLib.linarith_solver.
Keep ordinary LINARITH_ss and seedCollections algebra_ss/field_ss examples.

Build edges: clasimp/Holmakefile:2–8,14–17; aesop/Holmakefile:2,15,17–20;
benchmarks/Holmakefile:1; seeds/Holmakefile:1–4,9–12;
examples/Holmakefile:1; linarith/instances/Holmakefile:1,9. Add explicit extension
ML dependencies where required without changing generic claset-only consumers.

No migration or execution of these consumers occurred in TASK_07. This closes
the inventory's transitive type-boundary obligations, not TASK_25's build gate.
