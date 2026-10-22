# TASK_12 conditional primitive cutover supplement

This supplements [TASK11.md](TASK11.md) and [TASK10.md](TASK10.md).
Historical inventories and frozen contracts are not regenerated.

## Completed boundary and source correspondence

- `Cond_rewr.sml` is byte-identical to pinned develop
  `cccaa27d7099cbadc886983020cbe745db7793f3`, except that the original
  tracking block is replaced by one comment and two `val` aliases.
  `SimpTracking.sml` contains that exact original block, including nested
  extent restoration and exception cleanup. There is one production
  `ThreadLocal.new` slot, not one per engine.
- Direct `Cond_rewr.COND_REWR_CONV` is the entire pinned constructor.
  Construction/application stages, solver callbacks, traces, errors, loop
  checks and live depth lookup remain exact. It does not construct a pair,
  project a configured runner or allocate an extension control wrapper.
- `Cond_rewrExt` owns paired/configured/context constructors. Its paired
  bodies and adapters are extracted from task-start HEAD
  `640f5a1cbcb6d38ee08093cf2d007e14f0fb923a`, with only explicit shared
  imports qualified and the obsolete direct adapter removed. Both bodies
  share one lexical `instth` and one `HO_PART_MATCH` construction.
- `prepare` binds the actual supplied `BoundedRewrites` control once.
  There is no shadow allowance: both runners retain the same reference;
  only successful application decrements it. `runners` only projects the
  prepared pair, without matching, rebuilding or rebinding controls.
- `Cond_rewr.stack_limit` remains the sole default-depth reference.
  Configured `NONE` reads it live; `SOME n` remains invocation-local.
  Trace, theorem, exception-origin and bound identities are not cloned.
- Neither `Cond_rewr` nor `SimpTracking` imports an extension module.
  The frozen original signature remains baseline-compatible, checked by
  executed complete ascription/public clients. Legacy `is_var_perm` stays
  a public helper; exposing it does not introduce an extension dependency.

## Dependency ledger delta

- **X1 closed:** `simpExtLib` uses `Cond_rewrExt.prepare` and `runners`;
  local paired bound wrapping is removed. **14** still owns tracked
  compiler closure beyond this primitive.
- **M2:** the paired primitive is extension-only. Ordinary mixed `simpLib`
  explicitly calls `Cond_rewrExt.COND_REWR_CONVS` through its existing
  `appconvs`. This is temporary cooperation, not an ordinary boundary
  claim. **16** removes the mixed compiler/net and this Ext call.
- **M3/X2:** threaded Travrules and configured congruence primitive
  dependencies remain with **13**, unchanged.

M0 stays closed. M1 and M4–M6, and all other ownership/removal assignments,
remain as recorded in TASK11/TASK10. The explicit temporary ordinary Ext
call adds no new paired preparation cost: the mixed compiler already
constructed both runners before this move. Its existing costs are not
waived. This task does not establish final ordinary loading/storage,
fragment/compiler, tactic-stage or whole-plan performance acceptance.

## Validation and evidence status

Validation passes: 103 focused conditional checks, all `src` HOLSELFTEST
checks, the routine build, 75 Python compatibility tests, 30 performance
schema/audit tests and 29 interface checks. Frozen paired public/prior
contracts and 642 native checks pass with original observations preserved.

The final control and subsequent candidate timing runs each contain ten
fresh process pairs. Both are archived below. Candidate selections use
validation snapshot `06927a63d9796d33d6cc98f936c2cab27f3b66a5`; production
has not been edited after that snapshot. Control selects pinned develop on
both sides. Source seals, not merely a revision label, bind receipts to
landing files. These are direct conditional diagnostics, not mixed simpLib
or whole-plan acceptance evidence. See `../TASK_12_HANDOFF.md` for decisions,
commands, noisy timing intervals and generated-allocation correspondence.

Final archive layout:

```text
src/simp/tests/compatibility/evidence/task12/
  conditional-control/
  conditional-candidate/
  paired/
  native/
```

`../audit_task12.py` fails closed on structural/source drift. It compares
whole source regions, including all constructor stages/callback bodies,
imports and bound wrappers; allocation/projection checks are not inferred
from timings. It always runs structural checks first. Missing Git pins,
missing files or incomplete requested evidence fail; no timing/build rerun
or oracle update is attempted.

```sh
python3 -B src/simp/tests/compatibility/audit_task12.py
python3 -B src/simp/tests/compatibility/audit_task12.py \
  --evidence src/simp/tests/compatibility/evidence/task12
# The evidence folder may instead be supplied positionally.
```

Optional evidence mode requires all four subdirectories. It checks input
and selected-source seals, frozen signature/prior observations, native
coverage/streams and every conditional performance receipt's provenance.
It recomputes summaries from archived receipts, including pair order, and
requires exact agreement with `summary.json`; it never measures timings.
Without a folder it reports structural success only, not evidence success.

The audit passes against the current sources and all four archived final
receipt directories. Twelve in-memory source mutations (constructor,
callback, matcher, tracking, control, projection and dependency drift) and
an altered evidence source seal were rejected. Additional graph/native
allocation evidence and 13 fail-closed parser controls are maintained in
`../allocation/` and `../evidence/task12-allocation/`.
