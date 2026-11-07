# Prior traversal, exclusion and load contracts

This is a coverage freeze, **not a simplifier repair or performance pass**.
Pinned develop is `cccaa27d7099cbadc886983020cbe745db7793f3`.

## Test ownership

The reviewed 630 native cases and 12 registry repeats execute in
`tests/native-extension/selftest.sml`; `src/selftest.sml` is the complete
unchanged 73-check develop input. Every old ID/anchor/assertion survives
(`task26-relocation.json`). Public clients and the six quota checks have an
ordinary-only native normal entry. The post-list level-1 `check-full` requires
all 642 native checks and 11 aggregate vectors.

### Typed relocation

[migration/task10-relocation.json](migration/task10-relocation.json) is the
separately sealed typed mapping.
The original ledger and IDs are unchanged: its 630 native checks map in order
to 642 current checks, with exactly 12 extension-registry R4 repeats. The
verifier checks old Git blobs and current hashes/anchors for the four explicitly
relocated sources; all other sources and non-native streams remain exact.
Ordinary destructor/R6/R7/reflexivity pins remain ordinary. Type-driven tracked
projection/optional-eligibility predicate changes are explicit, not hidden by
renaming labels. The tables below are not rewritten.

## Actual case map (paths relative to `src/simp/`)

### Legacy-equal differential inputs

| IDs/count | Maintained assertion sources and actual cases |
| --- | --- |
| `original:0001–0023` (23) | `tests/compatibility/inputs/develop/selftest.sml:1–284`: AC termination/permutation; bounds including branches, loop bypass, variables and derived-rule sharing; abbreviations; conditional congruence; SimpL; UNCHANGED removal; Satisfy; T/F rewrites; conditional rewrite maker shapes. |
| `original:0024–0040` (17) | Same file `:286–365`: eight direct deletions (COND suffixes, BETA, UNWIND/replay), two Excl routes, four ExclSF cases, three fragment-removal cases. |
| `original:0041–0052` (12) | Same file `:374–425`: Req0/ReqD, conditional success/failure, Once/Twice and SF composition. |
| `original:0053–0069` (17) | Same file `:428–491`: abstraction, tactic exclusion in goals/assumptions, both oldestfirst orders, NoAsms/IgnAsm and six rewrite-priority competitions. |
| `original:0070–0073` (4) | Same file `:494–518`: Req0/ReqD refused by conversions; NoAsms/IgnAsm dropped. Immutable original **73**, not the expanded native file. |
| `traversal:0001–0009` (9) | `tests/contracts/TraversalContracts.sml:1–181`: warning preconditions; raw/cong QCONV construction-time collectors versus total-wrapper application-time collectors; rewriter/dproc and fact ordering; recursive private context reuse; empty context. |
| `traversal:0010` (1) | Same file `:183–203`: extracting before/after partial consumption and exhaustion shares the installed two-use quota. |
| `traversal:0011–0028` (18) | Same file `:205–302`: high/low/aborting reducer schedules, relation/congruence/weakener factory order, refresh on reuse, cached rejected factory, exact root exception payload, foreign factory rejection and Interrupt. |
| `traversal:0029–0032` (4) | Same file `:304–333`: live default depth changed by an earlier failed candidate; flag restoration; saved conversion at depth zero/one. |
| `traversal:0033–0043` (11) | Same file `:335–377`: raw HOL_ERR versus public UNCHANGED, delayed foreign payload identity, congruence total boundary, callback frequency; HOL_ERR/UNCHANGED/foreign/Interrupt solver failures and error provenance. |
| `traversal:0044–0047` (4) | Same file `:379–416`: malformed bound before makers, installation-only maker frequency, exact warning/collector stages. Original **47 checks / 273 OBS events**; entire callback/trace/warning sequence is compared. |
| `exclusion:0001–0004` (4) | `tests/contracts/LegacyFailures.sml:start`: warning/fail-fast/control preconditions and full control theorem. |
| `exclusion:0005–0374` (370) | Same file `prefix_checks`/`prefix_stores`, `RunExclusionContracts.sml`: five literal prefixes (`rule:`, `solver:`, `looper:`, `split:`, `case:`) × missing/installed × 37 checks. Each has conversion/rewrite/dproc stores, overlapping survivor, Excl/operator routes, replay, callbacks, silence and full theorems. |
| `exclusion:0375–0398` (24) | `tests/contracts/ExclusionHistory.sml`: repeated, unmatched-before-add, interleaved add/delete, batched operator, removed dummy fragment replay, ancestry disappearance/restoration and exact errors. |
| `exclusion:0399–0929` (531) | `tests/contracts/ExclusionParsing.sml`: four setup rules (8); 13 parser rows × (2 silent constructors + 4 rules × 4 direct/replay routes × 2 checks) = 442; seven dproc names × (2 constructors + 3 routes × 2 checks) = 56; four malformed names × 2 routes × 2 checks = 16; actual current-theory change and four replay attempts = 9. Total original **929 checks / 2,703 OBS events**. |
| `limits:0001–0006` (6 new) | `tests/compatibility/paired/PriorLimits.sml`: zero/one/two allowances; failed side solver consumes a rewrite then fails EQT_ELIM; rollback permits both root rewrites; exact failed-attempt callbacks; a failed conditional rewrite does not steal an enclosing sibling's allowance. Uses baseline APIs only. |

Strict parser rows preserve compiled suffix overlap (`stem`, `stem.1`,
`bool.stem`, `bool.stem.2`), unknown three-component theory spelling, literal
`$`, absent tails, empty/trailing-dot/`.1`/`a..1` spellings and missing names.
Malformed two-component non-ancestor, leading-dot and too-many-dot names keep
`-*` provenance/messages. Dprocs compare **original full strings**, not rewrite
suffix matching. Replay reparses strict names in the current naming context.
No unmatched nonempty history entry is dropped by these fixtures.

### Native/extension coverage (not a develop differential claim)

All **630** current `src/selftest.sml` cases execute, with the exact historical
native ordered label stream. This preserves legacy pins embedded among branch
extension tests; it does not claim their new APIs exist on develop.

| Native IDs | Source block / contracts retained |
| --- | --- |
| `0001–0086` | `src/selftest.sml:1–620`: original functionality plus higher-order/congruence-result/beta-rebuild pins. |
| `0087–0106` | `:621–729`: legacy tactic dispatch versus counted-pass engine. |
| `0107–0159` | `:730–1533`: conditional failures/rollback; live/default/explicit/nested depth and order; configured/generic contexts; child-first budgets; exception controls; configured congruence. |
| `0160–0180` | `:1534–1899`: strategy merges/removal, clear/filter rules, maker/history retention, tactic solvers, explicit depth/order, fragment congruences. |
| `0181–0231` | `:1900–2488`: safe/unsafe final solvers, loopers, context facts, literal versus extended collisions, strict/resolved replay and limits. |
| `0232–0313` | `:2489–2995`: splitter proofs/cleanup/subgoal order, explicit registration, caches/TypeBase replacement, local/persistent splits, exclusions, private replay and limits. |
| `0314–0349` | `:2996–3591`: invalid/unnamed markers, global/fixpoint policies, supplied bounds/context, root assumption rebuilding; actual option/pair/list cases (all five later-theory tests execute). |
| `0350–0490` | `:3592–3870`: conversion directive boundaries and complete branch-only namespace/collision matrix. |
| `0491–0502` | `:3871–5019`: child-first private quota scopes; normalization/observation; source/view/conjunct identity; suspension/filter/removal; preserving replay; prepared/combined bundles and shared controls. Each check contains multiple invariant assertions. |
| `0503–0547` | `:5020–5268`: ordinary versus contextual/configured lifetimes, total wrappers, Once refresh distinction; late FRAG/context lookup; malformed-tag and AC/maker/conversion staging. |
| `0548–0581` | `:5269–5597`: legacy eager factory schedule versus explicit lazy/root behavior; marker callback/count/error-order and goal-time context pins. |
| `0582–0616` | `:5598–5902`: branch-only pure inspection; binder protection/solver fact order; live weakener-to-reducer controls; exact congruence reflexivity-before-factory primitives and foreign payload identity. |
| `0617–0630` | `:5903–6301`: paired runners, live NONE versus explicit SOME controls, failure wrapping/Interrupt, late/exhausted projections without compilation, shared quotas/views/replay, public projection purity and configured fallback collectors. |

### Loading, markers and persistence

| Ledger suite / actual checks | Sources and executable obligations |
| --- | --- |
| `markers` / 54 | `tests/markers/selftest.sml`: 16 directive identities, five rejections, wrapper stripping, all-byte string matrices (271 strings per predicate), disjoint recognizers, recursion and requirement-list ordering quirks, once-only Abbr and re-filtered assumptions. Matrix predicates are retained inside their aggregate assertions. |
| `replay-order` / 15 | `tests/replay-order/selftest.sml`: diamond ancestry with sibling removals/duplicate aliases, initialization versus repeated TheoryLoaded, private ordered replay, distinct equal-theorem names and writing-theory REMOVE keys. |
| `split-registration` / 116 | `tests/split-registration/selftest.sml`: pure pre-opt-in use, exact Context rollback, private ADD/REMOVE, exact unrelated listener identity/order, idempotence/rewind, foreign handlers/exporters/ancestry, invalid declarations, stale binding/type/constant pruning, failed replay/retry, listener conflicts, reserved words/abbreviations, pinned contexts. |
| `fresh-control` / 11 | `tests/fresh-load/selftest.sml` + `control.ML`: clean initial module/registry checks and ordinary dynamic loading/simplification. |
| `fresh-attribute-first` / 23 | Same launcher plus `identity-{before,after}.ML`: original local/stored callbacks; **exact handler record pointer**, all old listener function pointers/order, exact permitted five unchanged generic marker listener additions, no private persistence listener. |
| `fresh-set-first` / 26 | Same, plus exact foreign exporter data/add/remove behavior and exporter record pointer. Both first-owner identity files really execute (four identity assertions per process). |
| `fresh-attribute-after` / 17, `fresh-set-after` / 19 | Loading leaves both namespaces free; later custom owners and exact callback arguments/data work without warnings. |
| `fresh-syntax-first` / 17 | Launcher + `syntax.ML`: foreign `Split`/`ExcludeX` overloads survive; both qualified simplifier marker constants remain accessible; no split registry claim. |
| `persistence` / 170 | `tests/split-persistence/`: **four fresh script assertions**, then eight fresh launcher scenarios: parent/child/descendant/owned/foreign-attribute/foreign-set/heap-save/heap-reload. `verify.ML` checks named DB theorem pointer identity, serialized REMOVE provenance, idempotence, actual splitting/alias exclusion and marker dependencies. `heapSave.ML`/`heapVerify.ML` exercise saved contexts/owners/handlers, rewind, live removal, cached opt-in, explicit retry and dispatcher replay in a different process. The temporary heap is removed on exit. |

The ledger counts **1,440 focused-suite** checks (929 + 47 + 54 + 15 + 116 +
113 + 166 = 1,440), which do **not** include the 630 native selftest checks.
Fresh theory exports add four script checks, so the ledger holds
1,444 focused + 630 native + 73 original + 6 new = **2,153 distinct
occurrences**. Differential repetitions are not additional case identities.

## Reproduce (new output directories required)

From the repository root, after building configured prerequisites:

```sh
bin/Holmake --no-project --no-cache --no_prereqs \
  --holstate="$PWD/bin/hol.state0" \
  -C src/simp/tests/compatibility -j1 \
  PAIRED_OUTPUT=/tmp/prior-current prior-contracts
bin/Holmake --no-project --no-cache --no_prereqs \
  --holstate="$PWD/bin/hol.state0" \
  -C src/simp/tests/compatibility -j1 \
  PAIRED_OUTPUT=/tmp/prior-control prior-baseline-control
python3 -B src/simp/tests/compatibility/run_prior_native.py \
  --output /tmp/prior-native
```

Both paired selections run original/traversal/exclusion/limits suites in fresh
processes through source/path/hash/exit/footer audits. Only final original
process-ending driver calls become completion checks; assertion bodies and
immutable original input stay unchanged. The native driver forces actual
launcher execution, not cached selftest logs; exported theories are built from
fresh fixture sources in a private temporary directory. All six fresh-load and
eight persistence scenarios execute.

Build timing, testutils CPU/GC displays, ANSI and terminal padding are not
semantic differences. Full raw diagnostic streams remain in receipts; every
OBS callback/warning/error event and ordered assertion is compared without
normalizing expected failures. Traversal observations match exactly. Exclusion
semantic observations match exactly; only theory build times differ in raw
successful output. Native monitor primitive serials are not a cross-version
contract; callback/count pins inside assertions still execute unchanged.

## Expected-red probes are diagnostic

The separate original signature and requirement probes, run against a candidate
that still has the added constructors or the changed printer behavior, are
diagnostic expected-candidate-red results, **not legacy-equal successes**: the
driver exits **1** with both added-constructor errors, and the requirement
probe sees `0/1/2` printer calls and a saved `PrinterFailure` rather than
develop's `1/1/1` and a remaining goal. Expectations of the public and staging
fixtures are never changed to accommodate a candidate. The strict staging gate
(`--staging-only --candidate-behavior baseline`) must exit **0** on restored
sources; a candidate with 57 checks against the 60-check baseline contract
exits **1**. Construction, exclusion, storage and performance behavior are
gated separately and are not waived here.

Scope: configured Linux/aarch64 Poly/ML 5.9.2, state0, one GC thread. Paired
results isolate selected sources on shared dependencies; native results use
current products. Neither is an independent clean-build, performance, full
regression or cross-platform acceptance claim.
