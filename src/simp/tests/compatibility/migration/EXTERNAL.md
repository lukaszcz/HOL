# Read-only external consumer provenance and migration ledger

**Final closure overlay:** [TASK27.md](TASK27.md) resolves every API,
construction, transitive-consumer and semantic-range row below using
[TASK25's isolated migration](TASK25.md) and sealed patch/execution receipts.
The caller-owned checkout remains unmodified. The old inspected path moved
from `/home/lukasz/dev/HOL/worktrees/isabelle-tactics` to
`/home/lukasz/work/HOL/worktrees/isabelle-tactics`; original provenance is
retained below, not regenerated. Future-tense TASK25 requirements below are
historical, not unresolved implementation work. See TASK27 for limits.

## Exact inspected checkout

- Path: `/home/lukasz/dev/HOL/worktrees/isabelle-tactics`.
- HOL HEAD: `442009a1f7f04366573dc2b649d31650ea7b113b`, branch
  `isabelle-tactics`, upstream `origin/isabelle-tactics`, +55 / -0.
- Merge parents: `601e4a143`, `8d2bbc856`; merge-base with inventory simplifier
  source: `8d2bbc8565672b44c759d86e0cd467466cff8c7a`.
- Last clasimp implementation/selftest commit:
  `ff212e3e18184e916fe6cdda47ee1c1c84ef64ac`.
- HOL tracked/index state clean; no nonignored untracked files. Unstaged and
  staged binary diffs both zero bytes, checked before/after inspection.
- Porcelain-v2 branch/status SHA-256:
  `4086a8c20270099fc971b5a0b9142963153141193cc00d45565f66697a84df71`.
- `HEAD:src/auto` tree: `c265800e385b3770d9cfb18807f5dad9534de00c`;
  `HEAD:src/auto/clasimp`: `1047b2965d329fb04872f512e5fdb6f580c62b53`.

**Clean HOL is not a claim that every nested/ignored file is clean.** The ignored
nested `.agent-files` repository is at
`38466dba8324e99cb4ef10db0989d25d2e294df3`, branch main (+31 / -0), with no
tracked/index modifications and **6,576 untracked files** (6,509 fixes_perf,
22 fixes_prototype, 13 historical review files, 32 other documents). Its
porcelain-v1 status SHA-256 is
`18af4580a2ec1e406234a0ee219de201b3e5fc8ee81b26a3c717c6b15b1b4bef`.
These are caller-owned; nothing was removed, edited or adopted as acceptance
evidence. Ignored heaps, `.hol` files, selftest.exe and old logs were untouched.

`manifest.json` records exact status, SHA-256 for every matched source, and
an aggregate hash of all scanned tracked inputs. Principal hashes:

| Path under external checkout | SHA-256 |
| --- | --- |
| src/auto/clasimp/clasimpLib.sml | 7e3c3e61ab5e9a3cbfd667932370614329c1db5a0c969a761efa9b5f95451f67 |
| src/auto/clasimp/clasimpLib.sig | 3b173a79510e02e90f7b0452e7dc003929d120eb0fcfcbcca85dae17532ba102 |
| src/auto/clasimp/selftest.sml | e1f93bedf3f8b4cbfdb9d64912bf27323d9a13b40ea39cd11f3e4ae2d7880c2d |
| src/auto/clasimp/Holmakefile | ede44e209add856561b94ef8748e678029b06d97d022663b5f30c02b5116cd1b |
| src/auto/clasimp/NORMALIZATION_CONTRACT.md | 08b3cc17f6555304aa0b244d8420e2ec94a903d94e36a56251035c7dd3596b04 |

No external migration patch, compilation or test pass is claimed. **TASK_25**
owns *all* actual downstream edits and executable validation in an isolated
checkout, including transitive public types, tests, docfiles and build manifests.
**TASK_24** owns the repository-side recipe/provider boundary; **08** its typed
interface. Never patch or build the inspected user's checkout incidentally.

## clasimp API callers

Paths in the next tables abbreviate `src/auto/clasimp/clasimpLib.sml` as S,
`selftest.sml` as T and `clasimpLib.sig` as I. Exact reference lines, including
ordinary constructors and type declarations, are searchable in references.tsv.
All these callers' final migration owner is **25**; implementation prerequisites
are the migration-family tasks in MIGRATION.md.

| API/family | S lines | T lines |
| --- | --- | --- |
| rewrite_sources | 703,845,1053,1145,1311,1339,1383,1435,1688,1885 | 5565,6121 |
| rewrite_source_handles | 849,854,945,1111,1309 | 117,137,4292,4520,5001,5019,5626,5708,5709,6545 |
| source_rewrite | 823,913,950,1025,1135,1184,1221,1252,1258,1351,1365,1451,1457,1495,1541,1592,3225 | 127,128,154,4519,4885,5006,5008,5481,5624,5703,6539 |
| same_rewrite_source | 959,1001,1091 | 150,4352,4708,4910,5025,5044,5299,5445,5761,5780 |
| rewrite_source_compare | 906 | — |
| rewrite_views | 1038,1178,1588,1597,3162 | 4267,5408 |
| rewrite_context_changes | 980,1066 | — |
| prepare_rewrite_arguments | 1812 | 6451 |
| prepare_rewrite_bundle / rewrite_bundle_rules | 1131 / 1136,1333,1465,1593,3181 | 124 / 123 |
| install_rewrite_bundle / combine_rewrite_bundles | 1147,1168 / 3585 | — |
| suspend_rewrite_sources | 1169,1173,1326,1430,3182 | 4522,4527,4532,4953,5493 |
| remove_ssfrags_preserving_controls | 870 | — |
| filter_rewrites / preserving variant | 2951 / 2953 | 4057,4403,4757 / — |
| mk_tactic_solver | 24 | — |
| set_cond_depth / split_ss | 503 / 504 | 4427,4663,5255,5281 / — |
| set_safe_solvers / add_unsafe_solver | 595 / 596,1772 | — |
| set_subgoaler / remove_solver | 597,3963 / 875 | — |
| prepare_child_first_observed | 766 | 5430 |
| prepare_child_first | 2882,3190 | — |
| SIMP_CONV_CHILD_FIRST | 2879 | 1367,4269,4895,4929,5411,5555,5723,6547 |
| GEN_GLOBAL_SIMP_TAC_CHILD_FIRST / BOUND | 1854,2210 / 2154 | — |
| xsimptac_config | 1736,2200 | — |
| CONTEXT_REDUCER / dproc_ss | — | 4498,4738,5674,6147,6561 / 4510,4746,5686,6167,6574 |
| charge_only / traverseconfig_for_ss | — | 1368,4270 / 836 |
| clear_rules | — | 516,2139,2185,2231,2264 |
| Cond_rewr.is_var_perm | 2051 | — |

Explicit public type propagation is required, not just import renaming:

- `rewrite_source`: S:722,886,887,890,893,1152,1193,1288,1294;
  I:51,136,166. `rewrite_bundle`: S:1124.
- `Traverse.ssolver`: I:10. `subgoaler`: I:20,24; S:60,206.
  `simp_prover_ctxt`: S:191.
- `Traverse.child_first_policy`: I:113,140,164,186;
  S:687,1568,2871,3521.
- `simpLib.simpset` propagates through I:32–364's bindings/caches/contextual and
  standalone tactics/processors; ssfrag at I:297 also needs an extension type.
- S:2592–2604 constructs an ordinary REDUCER at 2596; explicitly lift it when
  installing in an extension fragment. Preserve the closure/collector, not a
  newly duplicated callback implementation.
- Weak congruence: schemas/proofs S:213–349; fragment S:352–360; replacement of
  existing named CONG S:484–491. Requires the tracked CONG recipe/registry.

The external revision predates simplifier-owned marker cleanup.
[EXTERNAL_MARKERS.md](EXTERNAL_MARKERS.md) records actual classifier consumers:
linarithLib:117–122, clasetLib:1186–1236,1703 and rules/selftest:3064–3094,
plus their wrapper/generic-only and forwarding closure. All belong to
**TASK_25**. Recognizing Split/ExclX requires the simplifier-owned directive
boundary, not restoring generic constructors; controls remain forwarded with
a simpset and inert on the classical fact path. The ledger retains the exact
bucket/fact/order/identity assertions and earliest classification decisions.
`markerLib.Split` at T:1988,4724 must become the explicit extension marker.
`Excl "rule:boundPipelineFixture.reducer"` at T:6109 and bare split suppression
in splitAttrScript.sml:29–30 require deliberate extended-exclusion migration,
not weakening restored literal Excl. No direct external non-provider caller of
`ExclX`, `CONFIG_REDUCER`, `xtraversedata_for_ss`, `XTRAVERSE`, observer/root entry
points or `ssf_upd_rewrs` was found in the tracked-source sweep. Their capabilities
are reached through the higher-level prepared/child-first interfaces above.

The full transitive producer-output/public-type closure, including ordinary-looking
SIMP calls, mixed iff helpers, aesop sessions, all fragment producers and exported
iff theories, is in [EXTERNAL_TYPES.md](EXTERNAL_TYPES.md). Those are additional
**TASK_25** consumers, not incidental lexical hits.

## Late discovery and earliest construction points

| Current path | Construction/migration decision (TASK_25 unless noted) |
| --- | --- |
| Default S:1682–1692 derives from BasicProvers.make_simpset_derived_value | Construct an independent extension default seed **before its own** counterparts of BasicProvers's additions/TypeBase/theory deltas, not by promoting this callback's ordinary input. Provider boundary/recipes **08/24**, external integration **25** |
| Explicit derivation S:843–854; incremental tables/cache 943–1116 | Public arguments already tracked; change constructors/callers, not just source getter qualification |
| Native converse inventory 1296–1318; working-state wrapping/cache 1644–1710; extensionality 1885 | Same tracked input ownership through cached generations/context; late metadata reads must not recompile or reset counters |
| Supplied originals S:1127–1138,1146–1147 | Prepare/compile originals once and install once; reuse bundle/actual controls before deriving views |
| Early converse/suspension 1296–1390; deferred binding 1398–1565; runtime 1572–1602 | Retain order: runtime and originals chosen before lazy views; detection must not consume quota |
| Directives 1807–1831; scoped callback adaptation 1834–1851; process_clasimp_args 3094–3122 | Apply directives before binding; keep exception-safe exact processed-set dynamic extent, not a persistent promotion cache |
| Bundle combination 3585; first CS consumer 3594–3620 | First consumer chooses runtime/budget; later consumers reuse compiled bundle and spent controls |
| ssfrags_of at 865,3019; benchLib:702; benchGuards:240 | Names/transport/guard inspection only. No general reconstruction found; I:16–19 already warns about losing subgoaler. Keep inspection, never turn it into import |
| Private permutation set 430–439 | Fresh self-contained recipe; select extension construction where installed, not arbitrary-set promotion |

External `src/basicProof/BasicProvers.sml:1156–1173` builds the seed;
`:1175–1178,1244–1317` install deltas/fragments/TypeBase;
`:1499–1522` derive after compilation. Context transforms/windows
`:1349–1388`, arbitrary `temp_setsimpset:1484` and opaque logged updates need
typed extension-facing alternatives. Merely mirroring their already-built
ordinary result is not tracking-preserving. Any explicit rebuilding operation
must be named as such and cannot satisfy actual-counter sharing. See recipes
4–8 in MIGRATION.md. TASK_08 resolves this in
[DESIGN.md §6](../interfaces/DESIGN.md): explicit typed recipe/provider and
update paths, no arbitrary-state automatic mirroring or lazy rebuild in getters.
Persistent declaration preparation does not recover local ordinary transforms;
TASK_25 must migrate those consumers and their contexts/windows together.

## Transitive external consumers (all migration/validation owned by TASK_25)

| Consumer | References and construction obligations |
| --- | --- |
| `src/auto/aesop/aesopData.sml` | set_cond_depth:59, set_safe_solvers:64, set_unsafe_solvers:65; derived default 73–77, late raw-base read 110. Choose tracked base before these; do not inherit clasimp splitting |
| `aesopRule.sml` | GEN_SIMP_TAC:338; clasimp safe tactics; split utilities 261–278 and registered inventory 304 |
| `aesop/selftest.sml` | config:42,3611; GEN_GLOBAL:51; clear_rules:57; split_ss:126; solver types 3601,3610, solver_ss:3618. Keep 3588–3640's unsafe-base sentinel |
| `aesopData.sig`, `aesopLib.sig`, `aesopRule.sig` | simpset at 3; 17,19,24; 95,132 respectively. Public extension input/output type migration |
| `src/auto/order/orderLib.sml` / `.sig` | Ordinary REDUCER 234–239, named fragment static/budgeted 242–251; ssfrag exports 22,23. Explicit extension recipes/lifts without duplicated collectors |
| `src/auto/linarith/linarithLib.sml` / `.sig` | REDUCER 1549–1554, fragment 1556–1561, budgeted closures 1563–1568, solver type 1657; exports reducer 47,54, fragment 48,56, solver 49,58 |
| `linarith/selftest.sml` | Legacy projection 2703 stays ordinary if ordinary reducer/set; old Split at 1894,2323,3844 migrates explicitly |
| `src/auto/benchmarks/benchLib.sml` | mk_tactic_solver:711; filter:728; depth/safe/unsafe/subgoaler 731–734; old Split:830,933; named translation registry 217–223 needs typed recipe/registry decision; transitive ordinary-looking tactics/derived outputs below |
| `seedCollections.sml` / `.sig` | Ordinary fragments 29–30; exports 8–9. Actual algebra/field consumers currently remain ordinary; preserve named exclusions. See producer closure below |
| `clasimp/theory_tests/splitIntegrationScript.sml` | split declaration 11, inventory 19–24, split_ss 28, imported/local TypeBase proofs 26–59 |
| `clasimp/theory_tests/splitAttrScript.sml` | Libs dependency 3, named ownership 17–23, exclusion 29–37, actual split proof 39–42 |
| External `help/Docfiles/` | clasimp/aesop/linarith/simp extension type/API examples and cross-links appear in references.tsv; **25** updates the isolated patch, **27** audits final public docs/dependencies |

The producer-output/type closure below also includes external benchmark theory
scripts, seed selftests, iff test support and their exported theories; they are
actual extension consumers even where no added API token occurs.
Other tracked lexical hits outside src/auto/src/simp are ordinary uses or
homonyms as classified in CONSUMERS.md, except documentation and the explicit
BasicProvers construction-provider path above. Generic marker source in this
older external revision is a **provider difference**, not authorization to
restore generic Split/Excl behavior in the simplifier branch.

## Semantic assertion preservation for the isolated migration

All ranges below are external clasimp selftest. Retain assertion bodies, proof
validation and ordered charges, not merely displayed labels or aggregate counts.

| Lines | Contracts TASK_25 must execute with migrated APIs |
| --- | --- |
| 22–174 | Indexed converse detection equals independent linear oracle, abstraction/wildcards, cold/warm charges, genuine validation |
| 178–291 | NoAsms/IgnAsm across raw/viewed/safe passes, context selection without removing proof hypotheses, abbreviations/labels resolved before binding |
| 294–482 | Public/standalone/contextual/callback tactics compile once; citations/quotas, nested callback scope and exception cleanup |
| 3998–4218 | ETA protected by effective generic abstraction positions; filter/removal/exclusion affects policy; kernel identity vs name reuse; typed cutoff |
| 4220–4301 | Failed conditions retained as dependencies, exact rejection/charges, views not rediscovered as native |
| 4303–4551 | Incremental metadata equals fresh derivation; precise invalidation for rules/conversions/strategy/AC/congruence/context/suspension; retry failed cache |
| 4554–4842 | Once/Ntimes original/view sharing, duplicate occurrences, exhausted late attachment, unique install/no premature priming, compile-once bundles/memo charge replay |
| 4845–5113 | Suspend exact converse conjuncts, retain siblings/conditions/scope; typed longer-cycle limit; detection spends no quota |
| 5116–5349 | Lazy working states/generations/pointers, one view fragment, preserving decision removal/exhaustion, default updates and Context.restore identity |
| 5352–5641 | Ambient/supplied effective abstraction policy and exact adjusted tables; stripping decisions cannot revive spent rules |
| 5644–5861 | Early binding does not query ambient reducers/build views; original/masked table accepted, unrelated table rejected; interrupted groups retry |
| 5864–6052 | Runtime/originals installed once; raw/viewed/safe/cascade share quota/context/budget; supplied priority, failed provider retry |
| 6055–6185 | FAST/depth/SAFE/CLARIFY wrappers retain one bundle, runtime reducers receive untagged originals exactly once |
| 6188–6398 | Simp/Iff roles, fact IDs/support/requirements/labels; all six drivers retain compile-once consumption |
| 6401–6479 | Extensional reading uses effective aliases/precedence and excludes discarded rules |
| 6482–6665 | Fact/rule transport keeps native origin/support/role; no alias without compiled origin; private quota restored on cutoff |
| 6668–6785 | Proper-argument LHS views usable; continuation retains raw proofs and spent quotas |

TASK_25 acceptance must bind both source revisions, isolated migration patch
hash, source/product/loaded paths, actual launcher exits and these assertions.
This task only records the exact read-only consumer provenance and requirements.
