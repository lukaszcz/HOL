# TASK_11 datatype cutover supplement

This supplements, rather than rewrites, TASK_08's cutover ledger and
[TASK10.md](TASK10.md). Historical inventory line numbers remain historical.

## Completed boundary

- **M0 closed:** all of `Traverse.{sig,sml}` and `congLib.{sig,sml}` are
  byte-identical to pinned develop. Traverse owns only the original REDUCER,
  record, collectors and native engine. No extension import, discriminator,
  eligibility scan, projection or configured dispatch remains in Traverse.
- `congLib` uses `simpLib.traversedata_for_ss` and the original equation
  wrapper, with eager ordinary constructors. Configuration is not inspected.
  Configured clients construct `congExtLib.congset` and `simpExtLib.simpset`
  before calling `congExtLib.CONGRUENCE_*`. These are separate types; no
  installed congruence-set promotion or extension-to-ordinary reducer adapter
  exists. `congExtLib.lift_fragment` remains explicitly one-way.
- `TraverseExt` alone supplies contextual/configured reducers, configuration,
  refreshing/root/observed/child-first traversal. Its `LIFTED` alternative
  explicitly carries an ordinary reducer, without discovering source metadata.
- The obsolete mixed-engine diagnostic was removed from
  `tests/traverse-ext/diagnostics.sml`; ordinary/default/refreshing extension
  diagnostics keep their original proof and exact callback assertions.

## Surviving temporary dependencies (not final acceptance)

| ID | Actual current dependency | Removal owner |
| --- | --- | --- |
| M1 | `simpLib.{sig,sml}` strategy/history/solver fields explicitly name `TraverseExt`; configured projection builds `TraverseExt.CONFIG_REDUCER` and maps `TraverseExt.lift` over stored ordinary dprocs. Extended tactic/root/context/child-first helpers call TraverseExt. The optional ordinary getter checks conversion settings only, never a reducer discriminator. | **16** removes mixed APIs, strategy storage, projection and dispatch. Ordinary public `SSFRAG`, `dproc_ss`, `weakener_data`, dproc storage and `traversedata_for_ss` retain baseline Traverse types now. |
| M2/M3 | Ordinary mixed paired compilation and threaded congruence factories remain unchanged. | **12/13** separate primitives; **16** deletes mixed compiler cooperation. |
| M4/M5 | Old ordinary slots, source inventories, configured companions, split/strategy/history fields and extended marker helpers remain. Loading simpLib still reaches extensions through this temporary closure, not through Traverse or congLib logic. | **15/16** remove representation/import costs; **17/18** revalidate exclusions/tactics. |
| M6 | Native selftest remains interleaved; its ordinary eligibility pin now checks explicit one-way lifting into the temporary configured projection. It cannot test extension constructors inside an ordinary type. All 630 original cases plus 12 registry cases and their ordered stream remain. | **26** physical separation; no assertion execution postponed. |
| X1/X2 | `simpExtLib` paired preparation and `simpExtLib`/`congExtLib` shared threaded congruence primitives remain real current implementations. | **12/13**, then **14** tracked compiler closure. |

The temporary `simpLib.reducer_data` alias now means
`Traverse.dest_reducer`; its domain is ordinary reducers only. Removed branch
Traverse APIs are not kept as wrappers. Native extended tests already select
TraverseExt before construction. All public baseline value declarations remain
compatible; public frozen clients are executed, not just compiled to `.uo`.

## Cost attribution

TASK_11 restores the *entire* native traversal source, not merely an algorithm
with equivalent outputs. Full source identity includes context allocation,
factory setup/evaluation, exception scopes and limit rollback. Direct ordinary
reducer timing excludes mixed simpLib nets and conditional compilation. The
broader fixture is retained as a diagnostic: construction/reuse/projection
costs of current mixed objects must not be mistaken for traversal dispatch.

The measured fragment/merge/exclusion/compiler/projection costs remain genuine
plan blockers owned by their existing tasks, not waived or averaged against
traversal results. TASK_11 makes no legacy storage, loading, tactic-stage or
whole-plan performance acceptance claim. See ../TASK_11_HANDOFF.md for commands,
source seals, raw timings, per-workload interpretation and measured scope.
