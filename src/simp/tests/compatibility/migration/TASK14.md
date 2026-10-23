# TASK_14 tracked compiler boundary

**Final status:** [TASK27.md](TASK27.md) publishes final production owners
and evidence for every family/consumer. All transitional ordinary helpers and
imports mentioned below were removed by TASK16; M6 closed in TASK26. The
tracked object/control contract below remains the extension boundary.

The authoritative extension object is `simpExtLib.simpset`, constructed from
`simpExtLib.empty_ss` or an explicitly tracked recipe **before installation**.
There is no ordinary-simpset promotion, rebuilding import, closure inspection,
ordinary-history replay, or reconstruction from `ssfrags_of` in this API.
Ordinary clients and representations are unchanged by this task.

## Installation and projections

Fragment slots distinguish input occurrences; each installation has its own
event. Native compilation adds component/conjunct identities, names, statements,
inventories and the actual bounded controls. All ordinary tags are decoded,
then AC components derived, then all makers run, then conversions compiled,
then existing decision procedures collect original tagged context rules. Newly
supplied opaque decision procedures are assumed already primed. Explicit lifting
preserves their callback/context behavior, not inaccessible source inventories.

Each accepted rewrite retains one `Cond_rewrExt.prepared` binding with paired
runners and their common matcher. Both extension projections select these
installed runners and actual controls. They return `TraverseExt` data, **not**
ordinary `simpLib.simpset` or ordinary traversal data. Default traversal retains
construction-time private context initialization; configured traversal refreshes
private contexts per application. Extraction itself invokes neither schedule.
Getters may allocate shallow traversal records/closures, never new source
identities, rewrite preparation, collector calls, compilation traces or quotas.
Partially spent and zero controls remain actual shared refs, not snapshots.

## API decisions and caller migration

- **`Cond_rewrExt.rebind : prepared -> control -> prepared`** explicitly binds
  an existing matcher shape to a supplied actual control. Bounded status cannot
  change because it affects permutation checking; misuse raises `HOL_ERR`.
  No matching preparation, tracing, counter allocation or reset occurs here.
  Cached prepared replay now retains matcher shapes. Reset replay deliberately
  allocates one fresh declared control per old group, shared by its conjuncts;
  preserving replay retains actual surviving controls, including zero.
- **`simpExtLib.rewrite_sources ss thl` is inspection only.** It inspects the
  installed inventory and untags supplied rules without allocating controls.
  Directives raise `HOL_ERR`; it no longer hides installation/history replay.
  Call `prepare_rewrite_arguments ss thl` explicitly first, then pass its
  returned set and supplied rules to the getter. The native source-metadata
  fixture now does exactly this, preserving every original assertion. The
  TASK_10 relocation overlay updates only the current seal/explicit anchors;
  the frozen TASK_06 ledger, oracle streams and historical source stay intact.
  Existing directive-free extension callers need no change. The known external
  migration must use this explicit boundary as it adopts tracked construction;
  no separate user worktree was edited here.
- **`prepare_rewrite_arguments` is construction**, not a getter. Native removal
  now binds compatible survivors during that removal's one history replay,
  rather than reconstructing all history again afterward. Direct exclusion
  already retains installed entries. Original marker-processing order and its
  empty Cong/AC collector priming remain intact. Ordinary reset marker paths
  still use reset removal; this does not change default replay semantics.

No transitional ordinary import/allocation edge was added or removed here.
M1/M2/M3/M4-M6 still have the existing TASK_15/16 owners; X1/X2/M0 stay closed.
The already-planned exhaustive suppression/view/bundle/traversal matrices retain
TASK_19/21/22 ownership; no newly found repair is deferred to those tasks.

## Maintained validation

`tests/simp-ext/tracked.sml` executes alongside the existing 88-check suite at
normal selftest levels. It independently tests duplicate/reinstallation and AC
identities, conjunct groups, both projection orders, early/partial/exhausted
extraction, persistent filtering and preserving replay, cached matcher replay,
explicit reset, opaque collector staging, malformed tags, throwing makers,
directive preparation, changed-maker incompatibility, and private alias control
restoration after success/HOL_ERR/foreign exceptions/Interrupt/nested cutoffs.
Proof comparisons include the full hypothesis set. `audit_task14.py` complements
execution with bounded structural checks and fail-closed mutation controls.
See `TASK_14_HANDOFF.md` and `evidence/task14/` for source-tied final receipts.
