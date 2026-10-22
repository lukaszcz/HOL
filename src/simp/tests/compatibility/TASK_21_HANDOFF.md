# TASK21 — tracked sources, views and prepared bundles

Landing identifier: **TASK21-source-views-bundles-v1** (containing commit).
Starting HEAD: `05ab17ac34b8ffcca423acd8c3f399fe9afc3e58`.
Develop: `cccaa27d7099cbadc886983020cbe745db7793f3`.
Linux/aarch64, Poly/ML 5.9.2; configured `hol.state0`; isolated launchers
use one GC thread. Main checkout initially clean; pre-existing nested
`.agent-files` changes preserved.

## Acceptance and implementation

**All bounded TASK21 criteria pass. No blocker or unfinished TASK21 work
remains.** This does not claim whole-plan performance, independent clean builds
or external consumer integration.

The remaining in-scope callers were already migrated by TASK10/14: the native
selftest aliases extension modules before all fixture construction, and focused
fixtures, API examples and interface clients construct extension-owned objects
explicitly. TASK21 audits those earliest construction points rather than
inventing another migration or replaying an ordinary simpset. The original
native fixture and its coverage ledger are unchanged. The caller/API closure
is in [migration/TASK21.md](migration/TASK21.md); the historical consumer table
now points to that current audit.

New intersection tests exposed a real `rewrite_context_changes` defect:
structural history identity alone misses a view disappearing when its source
is suspended, deleted, filtered, removed or made incompatible by a maker.
The extension getter now compares **active compatible view dependencies and
compiled view statements**, respecting installation order. Two necessary edge
contracts prevent superficially plausible but incorrect fixes:

1. Removing a bundle and reinstalling it after its surviving old view event
   restores compatible handles, but does **not** retroactively install that
   view. Final source membership alone is insufficient. A new explicit view
   attachment works and shares the actual original controls.
2. Separate installations of the same prepared bundle can have different
   attached views with equal event/source/index. Their compiled conclusions
   and complete hypotheses must differ observably. Different proofs or
   redundant generalization of the same compiled statement do not invalidate
   the view.

The observation enumerates existing event/handle/cache data only. It neither
replays history nor compiles, invokes makers/collectors, creates origins,
refreshes controls or installs a global cache. Cached rejected shapes and
inactive stale handles contribute no installed view. Quota consumption alone
and compatible replay remain non-invalidating. Native rewrite differences
remain separately inspectable through handles, not reported as arbitrary
conversion keys.

No ordinary simplifier, generic marker, postkernel service, split ownership,
registry or public shared-control identity changed. Ordinary `simpLib.sml`
and `.sig` remain byte-identical to develop; the evidence manifest asserts
and records their exact hashes. There is no legacy import/promotion API.

## Coverage

`tests/simp-ext/sources.sml` adds **407 executed checks**, including three real
Poly/ML static type rejections. It is built **and executed** by normal
`simp-ext/check` at selftest level 1, outside ordinary selftest imports.

- Exact source/conjunct/name/AC-component order; duplicate merged slots and
  installation events; native handles versus installed-view inventory.
- Native and prepared invalidation matrices, both projection/use orders,
  partial and exhausted controls, dependent view removal, surviving sibling
  identities and actual quota sharing through preserving replay. Saved old
  projections observe new consumption, not just equal handle labels.
- Changed maker conclusion, hypotheses and declared bound versus a compatible
  different proof; stale handles cannot suspend replacements or revive aliases.
- Nested/disjoint bundle composition with partially consumed conjuncts,
  exhausted independent bindings and live bindings; complete grouping and
  installation order; duplicate composition/overlapping installation rejection
  before collectors; preserving versus declared-reset replay and sibling/view
  sharing. Old saved controls are never refilled by reset replay.
- Successful/rejected cached view replay, foreign handles, extraction after
  consumption, both extraction/application orders, and the two ordering/
  alternative-installation edge contracts above.
- Getters/composition produce zero successful **or rejected** compilation
  traces and invoke no makers/collectors; callbacks are made to throw if used.
  Prepared originals and attached views replay without compilation.
- Opaque exception payload identity and complete surviving collector facts;
  exact keyed conversion additions/deletions/replacement keys, keyless and
  opaque rebuilds, and precise compatible versus invalidated view contexts.
- Ordinary objects passed to source handles, source inventories or bundle
  preparation are rejected by the actual distinct simpset types. The real
  ordinary module is loaded first; diagnostics confirm type mismatch, not an
  undeclared structure, missing file or permissive stub.

Conversion checks compare complete conclusions and hypothesis sets of returned
kernel theorems against kernel-derived expected proofs. Existing tactic suites
still call returned validations with real residual proofs. All original quota,
trace, identity, callback, context and replay assertions remain intact.

Retained coverage: **642 native checks**, **88 focused + 174 tracked + 159
exclusion + 186 strategy + 88 tactic checks**, including **63 + 18 executed
tactic validations**. The frozen ledger still verifies **2,153 source-tied
cases**. The additive coverage map is in `tests/simp-ext/README.md`.

## Fresh source-tied validation

Exact sources, runtime/tool/heap hashes, argv, exits, receipt/log hashes and
negative-control procedures are in
[evidence/task21/validation.json](evidence/task21/validation.json).
All final acceptance commands below exit **0**:

| Command | Evidence under `evidence/task21/` |
| --- | --- |
| `bin/Holmake --holstate="$PWD/bin/hol.state0" --no-project --no-cache -C src/simp/tests/simp-ext -j1 check` | All six launchers execute; new 407-check suite passes; `focused.log.gz` |
| `bin/build -t --seq=tools/sequences/upto-parallel` | Complete final routine sanity build; `routine.log.gz` |
| `python3 -B src/simp/tests/compatibility/run_prior_native.py --output /tmp/task21/native` | 14 receipts; integrated `HOLSELFTESTLEVEL=1 all`, actual native/traversal/exclusion/marker/registration/replay/fresh-load launchers and fresh split exports/heap lifecycle; `native/manifest.json.gz` |
| `python3 -B src/simp/tests/compatibility/run_paired.py --candidate HEAD --candidate-signature pass --candidate-behavior baseline --prior-contracts --public-contracts --staging-contracts --negative-controls --output /tmp/task21/paired` | 44 receipts; old signatures/public clients, callback reproducers, frozen 73/47/929/limit streams, unchanged staging contracts and fail-closed controls; `paired/manifest.json.gz` |
| `coverage_ledger.py`; `verify_evidence.py`; `audit_task14.py` | Original cases, 37 immutable inputs and inert getter/shared-control/cached-matcher structural contracts pass |
| Compatibility unittest discovery, `-p test_task14.py` | Both tests pass, including the existing 15 fail-closed mutations; `mutations.log.gz` |
| `tools/h4pedant/h4pedant src/simp/tests/simp-ext`; `tools/h4pedant/h4pedant --nolinelen src/simp/src`; `git diff --check` | Pass; dedicated compact logs |

The native driver seals and executes final working-tree extension sources and
new assertions. The paired runner selects starting committed HEAD
`05ab17ac3`, whose **ordinary** sources are identical to final sources. Those
receipts establish ordinary compatibility, not execution of the extension fix.
The routine/native/paired checks were rerun after the last executable change;
no earlier provisional result substitutes for final acceptance.

Three isolated semantic negative controls build successfully (exit **0**) and
execute with expected exit **1** against the final test fixture:

- Starting implementation fails `context change observes incompatible view
  dependency`: `baseline-red*.log.gz`.
- Final code with only event-order membership disabled fails `lost view is
  observed despite returning compatible source`: `order-negative*.log.gz`.
- Final code with only compiled-view statement comparison disabled fails
  `same event/source/index cannot hide changed view statement`:
  `statement-negative*.log.gz`.

Each failure is checked as a semantic assertion failure, not a static error.
The manifest pins fixture/mutated source hashes, mutation text and local module
load paths. Local copies of `pureSimpsExt` prevent transitive loading of the
production `simpExtLib`; dependency caches start empty. Exploratory fixture
corrections (identity versus conjunct maker, SML precedence/type syntax, and
explicitly loading the ordinary module for negative clients) are not counted
as acceptance. No original oracle was changed to accommodate them.

## Files, cleanup and next task

- `simpExtLib.sml`: dependency/compiled-statement observation repair only.
- `simpExtLib.sig`: document dependent-view invalidation and native-key boundary.
- `tests/simp-ext/sources.sml`, three `negative/*.ML` clients and both
  Holmakefiles: maintained contracts, normal execution and clean integration.
- Focused README, caller audit/migration supplement, this handoff and compact
  source-tied evidence; actual progress status updated separately.

Private copied build trees and negative-control products are removed after
archiving compact receipts. Paired/persistence runners clean their own trees
and heaps. Task-created new source-test launcher/cache products and scratch
logs are removed after their last use. Pre-existing caller products, caches
and unrelated nested-repository changes are preserved; no copied tree, binary
or heap is committed.

TASK22 is next. Its private child-first lifetime scope, TASK23 persistence,
TASK24 recipes and TASK25 external integration remain the pre-existing later
tasks, not unfinished work deferred from TASK21. No new follow-up is needed.
