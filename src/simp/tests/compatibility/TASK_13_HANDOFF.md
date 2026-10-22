# TASK_13 handoff — separate congruence primitives

Landing identifier: **TASK_13-congruence-split-v1** (containing commit).
Start: `efae77781e40a0bd98775ae3d2bd670eaefdb7c0` (clean main worktree).
Pinned develop: `cccaa27d7099cbadc886983020cbe745db7793f3`.
Validation snapshot: `b5f3a9a94c0c5c26267b83dcfed409bf9cefd235`.
Runtime: Linux/aarch64, Poly/ML 5.9.2, configured hol.state0; paired processes
use one GC thread. No production or SML fixture changed after that snapshot.
The final audit scripts add only structural controls after the snapshot.
Unrelated nested `.agent-files` state was preserved.

## Bounded acceptance

**All TASK_13 acceptance criteria are satisfied; no TASK_13 blocker remains.**
This is not whole-plan loading, compiler/storage or performance acceptance.

- All four `Opening.{sig,sml}` / `Travrules.{sig,sml}` files are **byte-identical
  to pinned develop**. Ordinary CONGPROC has the original direct constructor,
  result-variable list/classification, subgoal processing, assumptions,
  closures, exception scopes and traces. There is no false-branch dispatch,
  result-predicate adapter, threaded scanning, beta rebuilding or Ext import.
  Ordinary traversal-rule construction is the original eager map/lookup.
- `Traverse` and `congLib` remain entirely pinned. Fresh paired original
  signature/public clients and traversal observations match the baseline,
  including eager factories, weakener setup, callbacks and failures. Ordinary
  primitives also execute in a separate fresh process which checks the loaded
  inventory: no simplifier extension, simpLib or congLib is loaded.
- `OpeningExt` owns the entire former threaded implementation specialized to
  threaded=true. Intermediate results can feed later contextual premises;
  rebuilt RHS beta cleanup leaves the original LHS, including its own redexes,
  unchanged. Ordinary result classification/beta behavior is not upgraded.
- Explicit `congExtLib` congruence construction and its relation/equality
  bridge use OpeningExt. Existing equation wrappers, default private-context
  reuse, configured per-application context refresh and solver contexts remain
  intact. Saved conversions and failed attempts have complete proof checks.

## Files, API and identity decisions

New `OpeningExt.{sig,sml}` exports `THREADED_CONGPROC`, removed from Opening.
New `TravrulesExt.{sig,sml}` exports `mk_threaded_travrules`, removed from
Travrules. Structural types are aliases to the actual original congproc,
preorder and travrules types. The factory calls the original `find_relation`
and constructs the original TRAVRULES, in the existing eager map order.
No new context registry, mutable public control, exception, trace hook or
listener is created. The one threaded ref is still the original *per-call*
lazy conclusion-genvar cache. The public Trace action/listener identity is
exercised across both primitives. HOL_ERR, UNCHANGED and Interrupt retain
existing constructors and their original rejection/propagation scopes.
`congLib.CONVNET` and `congExtLib.CONVNET` remain intentionally separate private
exception-valued net contexts inside their independent opaque congsets; neither
is public or used to transport contexts across engines. The existing Context
service is shared; the two typed fragment registries keep their distinct
`simpLib.ssfragDB` / `simpExtLib.ssfragDB` slots and rewind behavior. No new
registry/registration is added by these primitives. The exact-body caller audit
and repeated native R4/rewind assertions check this unchanged ownership.

`simpExtLib` explicitly calls TravrulesExt for threaded fragments. Normal
CONG fragments and ordinary standard recipes keep ordinary semantics.
The old mixed `simpLib` branch-only threaded route now explicitly calls
TravrulesExt too: this is ledger **M3**, already assigned to TASK_15/16
(removal no later than 16), not a new generic hook or a claim that ordinary
simpLib loading is already isolated. **X2 is closed.** Existing M1/M2/M4-M6
owners remain unchanged; M0/X1 stay closed. No new repair is deferred.

Only the focused test integration in `src/simp/src/Holmakefile`, Task08
cutover client, final module graph/design and migration supplement change.
The complete native selftest and existing suites/oracles remain unchanged.
No generic marker, theorem-set or postkernel machinery changed.
See [migration/TASK13.md](migration/TASK13.md) for the API/ledger delta.

## Fresh validation and evidence

[`evidence/task13/validation.json`](evidence/task13/validation.json) seals
53 source/input files and 76 artifacts. `commands.json` records exact commands,
exits, elapsed times and compressed logs. Paired/native manifests contain
source revisions/blobs, input/runtime/tool hashes, loaded paths and individual
execution receipts. All final commands exit **0**:

| Command/check (repository root) | Result |
| --- | --- |
| `bin/Holmake --holstate="$PWD/bin/hol.state0" --no-project --no-cache -C src/simp/src -j1 HOLSELFTESTLEVEL=1 all` | All integrated suites pass, including congruence-ext |
| `bin/build -t --seq=tools/sequences/upto-parallel` | Complete successful routine sanity build |
| `run_paired.py --public-contracts --prior-contracts --negative-controls --candidate <snapshot> --candidate-signature pass --output <fresh>` | 42 executed receipts, original signature and nine public clients; 73 original / 47 traversal / 929 exclusion / six limit checks; frozen streams and 12 intended fail-closed controls |
| `run_prior_native.py --output <fresh>` | 642 native checks; marker, registration, replay, fresh-load and persistence/heap scenarios |
| `Holmake ... -C src/simp/tests/compatibility/interfaces -j1 check` | 29 design checks, eight static rejections |
| `Holmake ... -C src/simp/tests/congruence-ext -j1 check` | Four ordinary fresh-load + 57 extension checks |
| Python unittest discovery, compatibility / performance | 94 / 30 checks; includes 19 TASK_13 structural mutation tests |
| `audit_task13.py`; `coverage_ledger.py`; `verify_evidence.py` | Whole-file/core correspondence, 2,153 frozen cases, 37 immutable inputs |
| `tools/h4pedant/h4pedant src/simp/src src/simp/tests/compatibility src/simp/tests/congruence-ext`; `git diff HEAD --check` | Pass |

The new maintained `tests/congruence-ext` executable compares conclusions and
hypothesis sets against independently kernel-derived expected proofs, not just
pretty-printed terms. It exercises intermediate/later premises, local context,
RHS-only beta cleanup with an unreduced LHS, reflexivity fallback, UNCHANGED,
side-condition failures before descent, callback counts, foreign payload and
Interrupt identity, saved conversions, exact weakener factory/context schedules,
configured congruence selection/refresh, solver context, and shared Trace actions.
Existing separate 131 TraverseExt, 88 simpExtLib and 103 conditional-extension
checks also pass in the integrated run. No assertions were removed or relaxed.

The offline source audit checks the *entire* pinned ordinary implementation,
the *entire* specialized threaded core, shared type declarations and exact
caller deltas (including M3). Mutation controls reject changed callback/work,
missing result/beta logic, duplicate state/exceptions, altered assumptions,
wrong factory order and fallback/ordinary routes. This structural evidence
establishes no additional work/import in the ordinary primitives; this task
does not claim a new statistical timing/allocation gate or measurements on
other runtimes/platforms. Whole-plan gates retain their existing owners.

## Cleanup

Private paired trees/heaps are removed by the maintained runners. Final
receipts are archived compressed; task-created temporary logs/extracted files,
new fixture caches and launchers are removed after archiving. No copied source
build trees, heaps or generated binaries are committed. Existing ordinary build
products and unrelated caller files are preserved. TASK_14 is next.
