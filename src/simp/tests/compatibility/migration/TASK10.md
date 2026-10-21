# TASK_10 typed native-test relocation supplement

[task10-relocation.json](task10-relocation.json) is an **additive overlay** on
TASK_06's frozen `../coverage-ledger.json.gz`, not a replacement freeze.
TASK_07's `manifest.json`, `apis.tsv`, `references.tsv`, historical inputs and
all original stream receipts remain unchanged. Old line numbers in those
inventories refer to their sealed historical source, not today's source.

## Case and source decisions

All `native:0001` through `native:0630` retain their IDs and order. Each row
maps to its current check number, a typed body decision and explicit old/current
source anchors. The native stream now has **642 checks**: the 630 original
checks plus **12 repeated R4 assertions** on the independent extension fragment
registry. Duplicate labels remain distinct occurrences. The original complete
637-event stream (including seven warnings) remains an ordered subsequence of
the current 649-event stream. No arbitrary extra checks/warnings are allowed.

The migration is in place in `src/simp/src/selftest.sml`; TASK_26 still owns
final physical suite separation. Selecting the extension aliases before
constructing sets/fragments is intentional: this is not late promotion of an
ordinary installed set. Ordinary REDUCER probes are explicitly lifted where
needed. COMBIN/SATISFY fixtures remain ordinary. In particular:

- `dest_reducer`, baseline R6 schedules, baseline R7 printer/decoder/staging
  pins and congruence reflexivity exception pins stay genuinely ordinary.
- Original R4 bodies execute against the ordinary registry, then repeat against
  the extension registry with an explicit prefix. Both restore Context.
- The two explicit R6 root/lazy-traversal checks stay extension-owned.
- Tracked default extraction is total and has `LIFTED (Traverse.REDUCER _)`
  shape; its configured companion remains `CONFIG_REDUCER`. Former `valOf`
  routes use the total getter without replaying/rebuilding installed state.
- Ordinary optional eligibility remains checked on ordinary inputs, including
  conservative rejection, acceptance, zero callbacks and ordinary pointer
  identity. Context/config dprocs cannot inhabit the restored ordinary type.
  Their former optional-NONE predicates explicitly become total tracked
  shape/exact-dproc/configuration checks. Existing collector schedules, proof
  hypotheses, quota sharing and configured invocation controls are retained.
  The supplement records this type-driven predicate change; it does **not**
  claim unchanged optional semantics for extension inputs.

The focused split-registration imports and persistence dynamic-load/verification
imports also select `boolSimpsExt`/`simpExtLib`. Their assertion bodies and
streams remain exact. Ordinary fresh-load scenarios still load ordinary
`simpLib`; they are not redirected to the extension library.

## Verification and execution

`coverage_ledger.py` verifies the original ledger and the overlay together.
Only the four explicitly listed relocated files may differ from the freeze.
For each it checks the frozen hash/size, the pinned old Git blob, the current
hash/size and old/current import/body and case anchors. All other source seals
and anchors remain exact. No snapshot is regenerated to accommodate a move.

`run_prior_native.py` seals both the verifier and supplement as run inputs,
verifies source integrity before building, then compares the complete current
native stream exactly. It also verifies the original ordered subsequence and
historical native oracle. Every other suite retains exact frozen comparison.
Exported persistence theories are still rebuilt privately; cached logs do not
count as execution. The runner never updates an oracle.

```sh
python3 -B src/simp/tests/compatibility/coverage_ledger.py
python3 -B -m unittest discover \
  -s src/simp/tests/compatibility -p 'test_*.py'
python3 -B src/simp/tests/compatibility/run_prior_native.py \
  --output /tmp/task10-native-new-directory
```

TASK_07's inventory reproduction intentionally still describes its own source
revision. Its current-tree signature/source checks can report drift after
TASK_09/10; do not regenerate historical tables or relax signature coverage to
turn that into a historical compatibility pass. TASK_10's current source/case
migration evidence is this separately verified supplement and fresh runner.

## Temporary dependency ledger (not completion claims)

| Current dependency | Completion owner / boundary |
| --- | --- |
| `simpExtLib` uses `Cond_rewr.COND_REWR_CONVS` and paired native checks still use shared `Cond_rewr` constructors | TASK_12 moves extension conditional constructors to `Cond_rewrExt`; ordinary constructor staging remains ordinary. |
| `simpExtLib` uses `Travrules.mk_threaded_travrules`; `congExtLib` still uses shared `Opening`/`Travrules` primitives | TASK_13 supplies `OpeningExt`/`TravrulesExt` and finishes configured congruence separation. Shared ordinary preorder/travrules identities are not copied. |
| Mechanically relocated tracked compiler/default projections | TASK_14/16 finish tracked compilation and ordinary representation cleanup; TASK_10 does not establish ordinary overhead removal. |
| Shared Trace/tracking/bounds/marker/split identities and temporary `simpLib` diagnostic origin strings | Keep intentional identities; TASK_18/20/23 complete extension tactic/strategy/split ownership; TASK_27 audits final dependencies. |
| Parallel PURE/BOOL/congruence recipes | TASK_24 owns complete repository recipes and typed default-provider boundary; TASK_25 external callers; TASK_26 final test layout. |

### Exact surviving ordinary mixed locations (M0–M6)

The original production `.sig`/`.sml` bodies other than `selftest.sml` are
unchanged from `397a10fab`; these are intentional intermediate dependencies,
not the final architecture. Locations below refer to that unchanged source.

| ID | Location and current dependency | Removal owner |
| --- | --- | --- |
| M0 | `Traverse.{sig,sml}` extended constructors/entry points and mixed dispatch; `congLib.sml:178–205,290–306` configured wrapping/projection; `tests/traverse-ext/diagnostics.sml:28` deliberate old-engine diagnostic | **11** restores ordinary datatype/body and congLib. `congExtLib` has already landed here to keep configured tests independently typed. |
| M1 | `simpLib.sml:185–238,2059–2150,2346–2422,2925` configured reducer/config/solver plumbing | **11** retypes private cooperation to TraverseExt; **16** removes it. No public promotion is added. |
| M2 | `simpLib.sml:126` paired compiler | **12** retargets to Cond_rewrExt; **16** removes ordinary paired preparation. |
| M3 | `simpLib.sml:1628` threaded travrules factory | **13** retargets to TravrulesExt; **15/16** removes ordinary threaded fragment/compiler fields. |
| M4 | `simpLib.sml:22–45,102–252,1681–1925` old source allocator, slots, inventories, companions and replay histories | **15** restores ordinary fragments; **16** restores ordinary net/compiler/storage and deletes the temporary allocator. New extension serials are private to a distinct source type, never interchangeable with old mixed handles. |
| M5 | `simpLib.sml:943–1051,2154–2162,2174–2422,2562–2583` strategy/split/extended marker helpers and corresponding signature exports | **15** removes ordinary fragment fields; **16** removes remaining imports/code. **17/18** own full exclusion/tactic revalidation. |
| M6 | `src/selftest.sml:1–23` interleaved typed aliases and ordinary local scopes; split-registration imports and split-persistence dynamic verification imports | **11** updates remaining ordinary cooperation pins at datatype cutover; **26** finalizes physical test separation. No callback/proof/quota assertion is deferred. |
| X1 | `simpExtLib.sml:131` paired preparation through existing Cond_rewr | **12** retargets to Cond_rewrExt with the single SimpTracking extraction. |
| X2 | `simpExtLib.sml:1634` existing threaded Travrules factory, and `congExtLib.sml:65–70,98,244–310` shared congruence factories | **13** isolates extension primitives; structural identities stay shared. |

New engine diagnostic labels still name `simpLib`/`congLib` deliberately:
relocation must not change error provenance. `Trace`, `Cond_rewr.stack_limit`,
`Cond_rewr.with_tracking`, BoundedRewrites controls, Context/TypeBase,
simpMarkerLib, splitLib and SplitData are referenced, not cloned. The two
fragment registries have deliberately different Context slot names. There is
no ordinary-to-extension wrapper/import added to ordinary production modules.

Compiled current API examples live in `../../simp-ext/APIExamples.sml`;
eight actual cross-type negative clients live in `../../simp-ext/negative/`.
Their executed fixtures are separate from TASK_08's universal prototypes.

A passing native run is current-product regression evidence, not independent
clean-build, develop differential, performance or final boundary acceptance.
