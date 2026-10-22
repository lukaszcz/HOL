# TASK_13 congruence primitive cutover

This supplements TASK12.md; historical inventories/oracles stay immutable.

## Completed APIs and work boundary

- `Opening.{sig,sml}` and `Travrules.{sig,sml}` are byte-identical to pinned
  develop `cccaa27d7099cbadc886983020cbe745db7793f3`. No threaded discriminator,
  result predicate adapter, whole-conclusion scan, beta reduction, companion,
  extension import or new registry remains in either ordinary primitive.
- Branch-only `Opening.THREADED_CONGPROC` moves to
  `OpeningExt.THREADED_CONGPROC`. Its entire implementation is the task-start
  mixed implementation specialized to threaded=true, without changing its
  matcher, reprocessing, lazy result discovery, beta scope or exception work.
- `Travrules.mk_threaded_travrules` moves to `TravrulesExt`. Its factory keeps
  the original eager map order and relation lookup. `Opening.congproc`,
  `Travrules.preorder` and `Travrules.travrules` remain the actual shared
  types (no cloned datatype, registry, exception, trace hook or control cell).
- `simpExtLib.threaded_cong_ss` explicitly selects this builder; ordinary
  extension `CONG` fragments still select ordinary semantics. Selecting a
  configured traversal alone does not silently opt ordinary rules into beta
  cleanup. No standard ordinary recipe is changed.
- Explicit `congExtLib` congruence-set construction selects the threaded
  primitive, including the relation/equality bridge. This is an extension-only
  contract: intermediate results can supply later contextual premises, and
  rebuilt beta redexes are removed only on the RHS. `congLib` remains pinned.
  The existing default versus configured collector lifetimes, per-application
  refresh and equation-reducer wrappers are otherwise unchanged.

## Dependency ledger

**X2 closed.** The extension compiler calls TravrulesExt; ordinary Opening
and Travrules never import extensions. **M3 activated explicitly:** the old
mixed simpLib threaded fragment route temporarily calls TravrulesExt until
TASK_15/16 removes its branch-only storage/compiler; removal owner is still
**16**. This replaces already-present threaded work, not a new ordinary
congruence hook. M0 and X1 remain closed; M1/M2 and M4-M6 keep their existing
owners. Ordinary simpLib/congLib whole-loading closure is not claimed here.
The final module graph now records congExtLib -> OpeningExt. Task08 cutover
clients reference the real new APIs. No generic marker, theorem-set or
postkernel source changed.

## Validation

See ../TASK_13_HANDOFF.md and ../evidence/task13/validation.json. The source
correspondence audit compares full pinned ordinary files and the entire
specialized threaded implementation, all shared type declarations and exact
configured/compiler routing deltas. Mutation tests ensure these gates fail
on changed work, missing beta/result logic, duplicated identities and wrong
routes. Frozen native/selftest sources remain unchanged.
