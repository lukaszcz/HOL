# TASK_14 handoff — tracked compilation and shared projections

Landing identifier: **TASK_14-tracked-compiler-v1** (containing commit).
Start HEAD: `d87be0699` (main worktree clean; unrelated nested `.agent-files`
state preserved). Pinned develop: `cccaa27d7099cbadc886983020cbe745db7793f3`.
Validation source snapshot: `953e6a6757228d80e738b56da1fe56ff207b34c1`.
Runtime: Linux/aarch64, Poly/ML 5.9.2, configured hol.state0; isolated paired
processes use one GC thread. No production or SML fixture changed after the
successful routine build. Source/tool/artifact seals and commands/exits are in
[`evidence/task14/validation.json`](evidence/task14/validation.json).

## Bounded acceptance

**All TASK_14 acceptance criteria are satisfied; no TASK_14 blocker remains.**
This is not ordinary compiler/storage/performance restoration or exhaustive
TASK_19/21 view/suppression validation.

- Explicit extension fragments/installation own slots, events, AC components,
  conjunct identities, inventories, prepared paired matchers and actual controls.
  Ordinary representations receive no new metadata or wrappers in this task.
- Both extension-typed projections use those installed runners and controls.
  Tests alternate applications in both orders, extract before use, after partial
  use and after exhaustion, and exercise old saved projections against filtered
  and control-preserving replayed sets. Actual consumption/exhaustion, not just
  equal source handles, establishes sharing. Duplicate occurrences/installations
  remain distinct; conjuncts share their one parent control.
- Projection/configuration/inventory getters do not rerun makers/collectors,
  compile, trace compilation, allocate identities or reset quotas. Native
  inventories remain retained lists. Explicitly lifted opaque reducers retain
  callback/context behavior without claiming inaccessible source inventories.
- Cached prepared replay now really retains matchers when binding controls.
  Preserving replay retains actual partial/zero refs; ordinary reset replay
  allocates fresh declared groups while retaining sharing between conjuncts.
  Changed maker statements are incompatible even with the same origin.
- Installation retains decode -> AC -> all makers -> conversion -> existing
  collector ordering, tagged original context order, and the contract that new
  opaque reducers are already primed. Malformed tags and throwing makers reject
  at the original earlier stages. Argument preparation no longer performs a
  second gratuitous replay after directive processing.
- No source-sensitive path imports or replays an arbitrary ordinary simpset.
  Both getters return TraverseExt data, not implicitly converted ordinary sets.

## Files and API decisions

See [migration/TASK14.md](migration/TASK14.md) for the full bounded migration.

- `Cond_rewrExt.{sig,sml}`: retain the unbound matcher shape alongside bound
  runners; add explicit `rebind : prepared -> control -> prepared`. It binds
  the supplied actual ref without preparation/reset/traces, and rejects changing
  bounded status (which affects permutation checking). Legacy Cond_rewr and all
  public shared control/trace/tracking/exception identities are unchanged.
- `simpExtLib.{sig,sml}`: retain prepared bindings in extension conversion data;
  use them for cached reset and preserving replay. Native history may still run
  its makers/collectors as specified, but only once per argument removal.
- `rewrite_sources` is now an inspection getter, not hidden construction. It
  rejects directives with HOL_ERR. Call `prepare_rewrite_arguments` explicitly,
  then inspect its returned set/rules. Untagging supplied rules creates no
  throwaway bounded ref. Directive-free callers need no change. The native
  metadata fixture explicitly prepares its exclusion, retaining all assertions.
- `tests/simp-ext/tracked.sml`: **174** additional executed checks; its launcher
  runs beside the unchanged **88**-check focused suite through normal
  `HOLSELFTESTLEVEL=1` integration. Both Holmakefiles include/clean it.
- `audit_task14.py` and `test_task14.py`: structural complements plus **15**
  fail-closed mutations. The TASK_13 audit accepts only exact reviewed TASK_14
  seals for the two intentionally changed files and still checks the identical
  threaded factory/merge slice. Its existing mutation tests remain intact.
  The TASK_10 overlay updates only current seals/anchors/decision text. Frozen
  source/oracle/assertion mappings and historical inputs are not regenerated.
- README, migration supplement and this handoff document the construction/API
  boundary. No generic marker, theorem-set, postkernel, registry or external
  user-worktree change. Existing M1-M6 removal owners stay TASK_15/16; no new
  transitional edge or newly deferred repair.

## Fresh validation

All final checks below exit **0**. Exact argv, elapsed times and compressed logs
are in `evidence/task14/commands.json`; manifests retain loaded paths, input/tool
hashes and individual process receipts. These are executed launchers, not merely
successful `.uo` generation.

| Command/check from repository root | Result |
| --- | --- |
| `bin/build -t --seq=tools/sequences/upto-parallel` | Complete successful sanity build through the required sequence |
| `bin/Holmake --holstate="$PWD/bin/hol.state0" --no-project --no-cache -C src/simp/src -j1 HOLSELFTESTLEVEL=1 all` | Normally integrated native and separate extension suites pass |
| Same Holmake flags, `-C src/simp/tests/simp-ext -j1 check` | 88 existing + 174 tracked compiler checks; eight static type-boundary rejections |
| Same flags, `-C src/simp/tests/compatibility/interfaces -j1 check` | 29 design checks and eight static rejections |
| `run_prior_native.py --output .../native-final` | 642 native checks, frozen traversal/exclusion streams, markers, replay, registration, fresh-load and persistence/heap scenarios |
| `run_paired.py --public-contracts --prior-contracts --negative-controls --candidate 953e6a... --candidate-signature pass --output .../paired` | 42 receipts; old signature/nine public clients, 73 original / 47 traversal / 929 exclusion / six limit checks, frozen streams and 12 intended fail-closed controls |
| Python unittest discovery, compatibility / performance | 96 / 30 tests pass, including existing TASK_13 mutations and 15 new mutation cases |
| `audit_task14.py`; `coverage_ledger.py`; `verify_evidence.py` | Structural contracts; 2,153 source-tied cases and 37 immutable inputs intact |
| `tools/h4pedant/h4pedant src/simp/src src/simp/tests/simp-ext src/simp/tests/compatibility`; `git diff --check` | Pass |

Proof checks compare complete conclusions and hypothesis sets, including open
conjunct proofs. Private normalization of non-inventoried alias entries restores
partial/exhausted caller quotas after success, HOL_ERR, foreign exceptions,
Interrupt, nesting and nested charge cutoffs. No new timing/allocation claim is
made; final ordinary compiler/performance gates retain their planned owners.

Exploratory checks were correctly red and then resolved: the first routine
attempt caught an 81-column new comment; the first native receipt audit caught
mutable test-generated scratchTheory source/data among pre-existing product
seals. After formatting and removing those task-generated exports, respectively,
the complete commands were rerun successfully. No library-product hash check,
assertion or historical oracle was weakened. Final receipts remain distinct from
those failed attempts. The initial compatibility Python run also rejected the
intentional native fixture change under TASK_13's old whole-file pin; the exact
reviewed seals and unchanged threaded slice now distinguish that migration from
unreviewed mutations. See `evidence/task14/attempt-notes.json`.

## Cleanup and next task

Paired/persistence scratch trees and heaps are removed by their maintained
runners. Task-generated scratch exports, new tracked fixture launcher/cache,
redundant failed native receipts and temporary exploratory logs are removed
once final evidence is archived. Existing caller build products/unrelated files
are preserved. No copied source tree, heap or generated executable is committed.
**TASK_15 is next.**
