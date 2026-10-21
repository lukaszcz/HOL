# TASK_10 handoff — extension-owned simplifier relocation

Landing identifier: **TASK_10-ext-simpset-v1** (commit containing this file).
Start HEAD: `397a10fab770eb4d4188612a19401b8f71625d03`.
Develop: `cccaa27d7099cbadc886983020cbe745db7793f3`.
Runtime: Linux/aarch64, Poly/ML 5.9.2, configured `hol.state0`.
The main worktree started clean; unrelated nested `.agent-files` state and
unrelated `/tmp` trees were preserved.

## Acceptance and API decisions

**All bounded TASK_10 criteria are satisfied; no TASK_10 blocker remains.**
This is mechanical type/module extraction, not final ordinary datatype/storage,
tactic staging, performance, external consumer or clean-build acceptance.

- `src/simp/src/simpExtLib.{sig,sml}` independently seal extension fragments,
  simpsets, sources and bundles. The mixed representation/compiler/replay/view/
  strategy/child-first algorithms are relocated, not delegated to `simpLib`.
  There is no arbitrary-set promotion, history import, reverse adapter or new
  ordinary wrapper. Ordinary production `.sig`/`.sml` files other than selftest
  are byte-identical to start HEAD (47 seals in validation.json).
- All extension reducer/config/solver fields and traversal calls use
  `TraverseExt`. Default native rewriting explicitly lifts an ordinary REDUCER
  over this extension object's own tracked net; relational reducers are lifted
  explicitly too. Context/config reducers remain genuinely extension-typed.
- Both getters return extension traversal data and share this object's actual
  installed controls. Default extraction omits configuration; configured
  extraction retains it. No optional `legacy_traversedata_for_ss` exists in the
  extension API. Default construction-once and configured refresh schedules
  remain distinct; tactic-only settings do not switch schedules.
- `pureSimpsExt` and `boolSimpsExt` construct tracked recipes from original
  theorem/conversion ingredients, in order. BOOL remains
  PURE/BOOL/NOT/CONG/UNWIND, ETA remains opt-in. The full bool catalog is supplied
  because the active fixtures need its fragments. AC, makers, TypeBase and
  relational factories construct extension fragments directly.
- `congExtLib` is extracted now to move the immediate configured caller/test
  closure together. Its types are independent; `lift_fragment` explicitly lifts
  public ordinary CSFRAG ingredients without invoking callbacks. No compiled
  ordinary congset promotion exists. Ordinary congLib restoration remains 11.
- Only the new typed registry uses **simpExtLib.ssfragDB**. The old
  simpLib.ssfragDB remains unchanged. Same-name lookup, SF late dispatch,
  replacement and Context rewind are tested in both; there is no fallback.
- Trace, condition-depth ref, tracking extent, bounds datatype/actual refs,
  Context/TypeBase, marker directives, splitter/persistence and public exceptions
  retain their existing owners/identities. Diagnostics deliberately retain
  simpLib/congLib origin labels. Nested tracking across engines is exercised in
  both directions, including foreign exceptions; no competing singleton exists.

## Caller and coverage migration

`src/selftest.sml` selects tracked modules **before construction** using explicit
local aliases. Ordinary dest_reducer, COMBIN/SATISFY, R6 eager scheduling, R7
baseline staging and congLib reflexivity pins retain ordinary local scopes.
Extension contextual/configured constructors no longer refer to the old mixed
Traverse datatype. Focused split-registration and persistence verification also
construct extension sets; fresh ordinary-load tests remain ordinary.

All **630 original native assertions** retain their messages and order; **12**
additional R4 registry checks give **642**. Proof, hypothesis, quota, collector,
maker, exception and replay assertions are retained. Type-driven changes are
explicit: tracked native shape is LIFTED REDUCER; tracked getters are total;
ordinary optional eligibility/pointer checks stay ordinary, and contextual
rejection cases become tracked shape/exact-dproc/configuration checks. Unlike-
type list pointer comparisons are not fabricated.

`migration/task10-relocation.json`, `task10_relocation.py` and
`test_relocation.py` add a checked overlay on the immutable TASK_06 ledger:
630 case IDs, old/current hashes and anchors, exact 649-event current stream,
637-event original ordered stream and the twelve permitted additions. Only four
explicitly relocated files may differ. `coverage_ledger.py` and
`run_prior_native.py` validate the overlay without regenerating historical
inputs/oracles. Negative Python tests reject stale/missing/extra mappings,
changed observations, missing cases and unrecognized additions.

`tests/simp-ext/APIExamples.sml` elaborates actual-module clients. Its separate
88-check runnable suite covers configured depth, lift/context callbacks,
source handles, partial/exhausted late projections, views/preserving replay,
bundles, parent/child-first overlaps, private quota restoration, registry and
shared tracking controls. Eight actual static negatives reject reducers,
sets, fragments and congsets crossing either type boundary. The production
Holmakefile runs this suite at selftest level 1; physical separation of the
interleaved native cases remains M6, not deferred execution.

## Fresh validation

From repository root; exact argv/cwd/exits/log hashes are in
`evidence/task10/commands.json`. All commands completed with expected exits.
Receipts, source/runtime seals and executed launcher/load plans are retained
under that directory; no heaps/binaries/copied build trees are committed.

| Command/check | Exit / result |
| --- | --- |
| `bin/Holmake --holstate="$PWD/bin/hol.state0" --no-project --no-cache -C src/simp/tests/simp-ext -j1 check` | 0; **88** checks, including eight static rejects |
| Same launcher with accepted negative body / missing negative file | 1 / 1; originals restored and final focused suite rerun |
| `python3 -B .../run_prior_native.py --output /tmp/task10-native-final` | 0; **642** native checks; exact frozen traversal/exclusion, marker, registration, replay and fresh-load streams; eight privately rebuilt persistence/heap scenarios; level-1 target also runs 131 TraverseExt checks and the new focused suite |
| `python3 -B .../run_paired.py --prior-contracts --negative-controls --candidate HEAD --output /tmp/task10-paired-final` | 0; original **73**, traversal **47**, exclusion **929**, limits and ordered observations match develop; fail-closed controls verified |
| `python3 -B .../interfaces/check_design.py --run --negative-controls --output /tmp/task10-interfaces-final` | 0; 193 decisions, 29 HOL checks, eight prototype static rejects; accepted/missing controls each exit 1 |
| Compatibility / interface unittest discovery | 0 / 0; **62 / 15** tests |
| `coverage_ledger.py`; `verify_evidence.py` | 0 / 0; **2,153** original case IDs and **37** immutable inputs intact |
| `bin/build -t --seq=tools/sequences/upto-parallel` | 0; **Hol built successfully**, after final compiled-source edits |
| `tools/h4pedant/h4pedant` on production, focused and migrated fixture directories; `git diff --check` | 0 / 0 |

The paired HEAD selection intentionally checks the unchanged ordinary source
closure; it is not evidence for the newly extracted engine. Current-product
native/focused executions, with their own source seals/load plans, exercise the
actual new engine. Original ABI rejection and reviewed tactic-staging behavior
remain diagnosed, not repaired or waived here. No performance claim is made.
TASK_07 inventory tables remain historical snapshots; their current-tree drift
is not repaired by rewriting the snapshot. TASK_10 uses its explicit overlay.

## Remaining owners and cleanup

`migration/TASK10.md` gives exact locations and removal owners for **M0–M6,
X1/X2**, extending TASK_08's cutover ledger. In brief:

- **11** restores ordinary Traverse/congLib and retypes surviving private mixed
  simpLib cooperation; **12/13** extract paired/threaded primitives and the one
  tracking service. New simpExtLib currently calls the existing real paired and
  threaded implementations, not future modules or stubs.
- **14** completes authoritative tracked compilation/projections; **15/16**
  remove old ordinary fragment slots, allocator, inventories, configured net/
  strategy fields and extension imports. No temporary mixed cost is final.
- **17–23** own expanded exclusion/tactic/source/bundle/child/split algorithmic
  gates; **24–27** complete default recipes, isolated external migration,
  physical test layout and final documentation/dependency audit.

Task-owned temporary validation outputs, prototype/focused caches and launchers
are removed after their compact evidence is retained. Normal production build
products remain available; unrelated artifacts are untouched. Next: **TASK_11**.
