# TASK_09 handoff — separate extended traversal

Landing identifier: **TASK_09-traverse-ext-v1** (commit containing this file).
Start HEAD: `f1d95a7f0c859b3749b7c0aeee29ef876c18244b`.
Develop: `cccaa27d7099cbadc886983020cbe745db7793f3`.
Runtime: Linux/aarch64, Poly/ML 5.9.2 Release, configured `hol.state0`.
Source/runtime/tool hashes, executed load plans, commands/exits and receipts:
[`evidence/task09/validation.json`](evidence/task09/validation.json),
[`commands.json`](evidence/task09/commands.json). Initial main worktree was clean;
unrelated dirty/untracked nested `.agent-files` state was preserved.

## Acceptance

**All bounded TASK_09 criteria are satisfied. No TASK_09 blocker remains.**
This is additive extraction, not datatype restoration, migration of mixed
simpsets, independent clean-build acceptance or a legacy performance claim.

- New `src/simp/src/TraverseExt.{sig,sml}` implement the TASK_08 interface with
  distinct `LIFTED`, `CONTEXT_REDUCER`, `CONFIG_REDUCER` constructors and explicit
  `lift`. The actual engine elaborates against the complete TASK_08 signature.
  No reverse reducer/data adapter or ordinary-engine delegation exists.
- Configuration/context records, generic prover pipeline, root selection,
  observer/abort handling, binder capture protection, child-first charge/eta
  policies and per-application refresh execute in the separate engine. Shared
  preorder/travrules/congruence types and exceptions keep their original identity.
- `TRAVERSE` initializes reducer contexts once and retains eager per-context
  factories. `XTRAVERSE` and explicit root/context/observer entries refresh on each
  application, even with default configuration, and retain lazy factory attempts.
- Lifting/record extraction invokes no collector/apply callback, does not discover
  source inventories, and forwards the original exception payloads and closures.
  Explicit `addctxt` invokes the existing collector once. During this mixed step,
  lifting is supported for ordinary `Traverse.REDUCER`, not the old extension
  constructors scheduled for removal.
- `NONE` reaches native candidates unchanged, including after an earlier failed
  candidate mutates the shared default depth; contextual integer callbacks sample
  immediately before invocation. `SOME n` and custom order remain local.
- Trace and condition-depth controls are references to their existing owners,
  not duplicated implementations/registrations. The new engine creates no context
  registry, tracking slot, bounds service or fragment registry. Diagnostics retain
  the original `Traverse` origin labels; exception constructors are not cloned.
- Every pre-existing production `.sig`/`.sml` file, including mixed Traverse and
  native selftest, is byte-identical to start HEAD (hashes in validation). Only
  production `Holmakefile` wiring changes: the separate extension suite runs at
  selftest level 1 without becoming an ordinary selftest/library import.

## Fresh validation

All commands ran from the repository root except explicit launcher cwd entries.
Full argv/exits are in commands.json; logs/receipts are compressed, not binaries.

| Check | Exit / observation |
| --- | --- |
| `bin/Holmake --holstate="$PWD/bin/hol.state0" --no-project --no-cache -C src/simp/tests/traverse-ext -j1 check` | 0; **131** executed checks, actual engine signature witness, two real static cross-type rejections |
| Same launcher with accepted negative body / missing negative file | 1 / 1; neither can masquerade as successful static rejection; original file restored and final suite rerun |
| `python3 -B .../run_paired.py --prior-contracts --negative-controls --candidate HEAD --output /tmp/task09-paired` | 0; 24 audited receipts; original 73, traversal 47, exclusion 929 and six limit checks match develop; all 273 traversal OBS events unchanged |
| `python3 -B .../run_prior_native.py --output /tmp/task09-native` | 0; 14 receipts; all 630 mixed native checks and complete original ordered streams unchanged, plus loading/markers/registration/persistence; build target also executes the 131 new checks |
| `python3 -B .../interfaces/check_design.py --run --negative-controls --output /tmp/task09-interfaces` | 0; 193 decisions, 29 HOL checks, eight static rejects; accepted-body/missing-file controls each exit 1 |
| Compatibility / interface-validator unittest discovery | 0 / 0; **48 / 15** tests |
| `bin/build -t --seq=tools/sequences/upto-parallel` | 0; **Hol built successfully**, rerun after final compiled-source edits |
| `coverage_ledger.py`; `verify_evidence.py` | 0 / 0; 2,153 source-tied cases and 37 immutable inputs unchanged |
| `tools/h4pedant/h4pedant src/simp/src src/simp/tests/traverse-ext`; `git diff --check` | 0 / 0 |

Paired HEAD selection deliberately isolates the **unchanged old implementation**;
the actual new engine is exercised by the current-product focused suite and
signature witness, with their load plans/hashes retained separately. The old ABI
probe still exits 1 for added constructors, and old requirement staging remains
the diagnosed reviewed behavior. Neither is claimed repaired by this task.

`tests/traverse-ext/README.md` maps additive assertion blocks to TASK_06 IDs/body
anchors. No original test was moved, reduced, or re-oracled. Focused coverage
includes payload/continuation identity, all reducer lifetimes, exception stages,
proof conclusions/hypotheses, exact factory and callback schedules, rollback,
solver proof transport/order, generic facts/binders, root/child-first overlap,
eta selection, failed-condition observation, charge counts, and original
HOL_ERR payload/foreign/Interrupt identity through conditional wrappers.

Early executable iterations caught fixture setup issues (a quantified rewrite
needed SPEC_ALL, HOL_ERR identity must compare its payload rather than a runtime
exception wrapper, and a lazy-factory count was one, not two). Explicit load-plan
prerequisites were also needed for structures passed as functor arguments. These
were fixed before final execution; no existing assertion was weakened or source
oracle changed.

## Separate construction/reuse observations

`diagnostics.sml` retains and exercises 20,000 constructed conversions separately
from saved-conversion reuse; every proof and exact callback count is consumed.
It ran after all concurrent builds stopped. See `diagnostics.log.gz`.

| Engine | Construction user CPU / initial collectors | Reuse user CPU / collectors / apply callbacks |
| --- | --- | --- |
| Ordinary default | 0.002 s / 20,000 | 0.008 s / 1 / 40,000 |
| Separate default | 0.002 s / 20,000 | 0.026 s / 1 / 40,000 |
| Old mixed refreshing | 0.000 s / 0 | 0.012 s / 20,000 / 40,000 |
| Separate refreshing | 0.000 s / 0 | 0.010 s / 20,000 / 40,000 |

Wall/system fields remain in the log. These are single-process scheduling/cost
**diagnostics**, not calibrated performance comparisons or acceptance ratios.
The separate default intentionally uses the generalized engine; ordinary sources
and execution have not changed. No loading, allocation or final legacy-runtime
claim is made here.

## Files, cleanup and pending cutover

- Added engine signature/implementation and `tests/traverse-ext/` focused
  selftest, signature witness, two negative clients, diagnostic, build/README.
- Updated `src/simp/src/Holmakefile` with separate selftest/clean wiring.
- Added this handoff and compact `evidence/task09` receipts/seals.
- Updated only TASK_09/10, next-task and one completion entry in the existing
  ignored progress file; unrelated nested-repository changes remain untouched.
- Removed task-owned temporary runner outputs/logs and focused/interface test
  caches/launchers after retaining their unique evidence. No copied build trees,
  heaps or generated test binaries are committed.

**Pending datatype cutover (M0):** TASK_10 retypes the extension simpset/caller
closure to TraverseExt. TASK_11 then removes old mixed Traverse constructors,
entry points, eligibility/projection dispatch and configured congLib wrapping,
and restores the exact ordinary datatype/body. Keeping those old paths here is
the explicit additive scope boundary, not a remaining TASK_09 criterion.
