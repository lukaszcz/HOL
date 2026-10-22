# TASK22 — child-first derivation and solver/context lifetimes

Landing identifier: **TASK22-child-first-lifetimes-v1** (containing commit).
Starting HEAD: `fef39229ccd854bf5936174c4f0b31010a4f0f0a`.
Develop: `cccaa27d7099cbadc886983020cbe745db7793f3`.
Linux/aarch64, Poly/ML 5.9.2, configured `hol.state0`.
Initial main-tree state: only the task-related untracked `derivation.sml`
draft; completed that draft. Unrelated nested `.agent-files` changes preserved.

**All bounded TASK22 acceptance criteria pass. No TASK22 blocker remains.**
This is not whole-plan performance, independent-clean-build, persistence,
recipe or external-consumer acceptance.

## Repair and API decisions

Private derivation already snapshots the actual installed native/view/bundle
counters, uses their declared allowances in a `Portable.finally` scope, and
restores enclosing/private/public values on exit. Migration had left one
policy callback unprotected: `keep_abstraction` could raise HOL_ERR after a
bounded rewrite, only to disappear into eta fallback or conversion rejection.

- `simpExtLib.sml` now protects that callback alongside charge/observation.
  This is also necessary when descent creates an eta candidate: the first
  policy check then runs inside the configured native ETA entry, not the
  traversal's head-preservation pass.
- `TraverseExt.sml` protects its head-policy callback using its existing
  application-local abort state. Standalone `NORMALIZE_ARGUMENTS` likewise
  retains policy errors across eta fallback/TRY_CONV and rethrows the original
  exception. Its state is application-local, so saved/reentrant calls recover.
- Successful callback order/counts, charge points, proof construction,
  congruence selection, traversal limits and ordinary HOL_ERR candidate
  rejection remain unchanged. Ordinary reducer/solver/collector HOL_ERR is
  **not** reclassified as an abort. Interrupt and foreign payloads propagate.
- Signatures document the guarantees; public types/entry points are unchanged.
  The [caller closure](migration/TASK22.md) records tracked construction and
  explicit opaque lifting. There is no ordinary import/promotion/replay API.

Only extension code changes. Ordinary `Traverse`, `simpLib`, `Opening`,
`Travrules`, and `congLib` sources/signatures retain their exact develop bytes;
other ordinary sources remain unchanged from starting HEAD. No control cell,
registry, marker, postkernel service, ordinary loading path or storage changes.

## Coverage and integration

`tests/simp-ext/derivation.sml`: **846 executed checks**:

- Native/bundle/alias/conjunct/composed groups, partial and exhausted caller
  counters, fresh declared quotas on saved normalize/arguments reuse, exactly
  declared shared uses, argument-only root preservation versus normalization.
- Same-object reentry after consumption: nested success, HOL_ERR, foreign
  exception and Interrupt; caught inner failures restore the partially spent
  outer counter, then outer exit restores the actual caller counter.
- Observer, charge and abstraction-policy errors **after** bounded consumption,
  including late native ETA checks. Original HOL_ERR payload pointer/provenance,
  opaque foreign payload identity and Interrupt checked; saved objects recover.
- Unchanged children and failed conditions remain observed, without extra
  charges or different proofs. A failed conditional candidate cannot spend
  its sibling's private shared allowance (checked inside the scope).
- Opaque lifted reducer, unsafe solver and congruence collector failures after
  consumption: normal HOL_ERR rejection, arbitrary exception/Interrupt abort,
  restored exhausted counters and successful saved reuse.
- Inert prepare/save/pretest, exact maker/collector refresh counts for whole
  normalization versus each argument/pass, no installed-rule recompilation
  or public allowance refresh.

`tests/simp-ext/lifetimes.sml`: **60 executed checks**:

- Exact single-root priority/fallback, no descent/fixpoint, fresh private
  collector payloads, solver-only facts excluded from opaque collectors.
- Nested generic solver pipelines using the same data, saved recurse closures
  retaining their original contexts/generations after later applications and
  failures; exact stack/context/apply/collector traces and complete proofs.
- Live saved head policy with selected congruence descent; successful unchanged
  congruence blocks fallback; eta policy errors through direct/observed/argument
  entries keep identity, do not call the callback again, and recover on reuse.

Both launchers build **and execute** from normal `simp-ext/check` and
`HOLSELFTESTLEVEL=1 all`; clean targets include their products. The README maps
additive checks to the original assertions, none of which were removed.

Retained fresh coverage: **642 native**, **131 TraverseExt**, **88 focused +
174 tracked + 159 exclusion + 186 strategy + 88 tactic + 407 source/view/bundle**
checks, with **63 + 18 executed tactic validations**. Existing fixtures retain
live default depth, custom order, solver safety/validation, counted global
passes, looper limits, root-condition recursion, capture avoidance, exact
factory staging and observation callback counts. Frozen legacy streams remain
**73 original / 47 traversal / 929 exclusion**, plus limit contracts; the
coverage ledger still verifies **2,153 source-tied cases**.

## Source-tied validation

[evidence/task22/validation.json](evidence/task22/validation.json) pins final
sources/fixtures, runtime/tools/heap, exact commands/exits, evidence hashes and
the path-alias wrapper. Final required commands all exit **0**:

| Command | Evidence under `evidence/task22/` |
| --- | --- |
| `bin/Holmake --holstate="$PWD/bin/hol.state0" --no-project --no-cache -C src/simp/tests/simp-ext -j1 check` | All eight launchers execute, including 846/60 new checks; `focused.log.gz` |
| `bin/build -t --seq=tools/sequences/upto-parallel` | Complete routine sanity build; `routine.log.gz` |
| `python3 -B src/simp/tests/compatibility/run_prior_native.py --output /tmp/task22/native` | 14 receipts, final working-tree sources, integrated selftest-level-1 `all`, actual native/traversal/exclusion/load/listener/marker/replay launchers and fresh split export/heap lifecycle; `native/manifest.json.gz` |
| `python3 -B src/simp/tests/compatibility/run_paired.py --candidate HEAD --candidate-signature pass --candidate-behavior baseline --prior-contracts --public-contracts --staging-contracts --negative-controls --output /tmp/task22/paired` | 44 receipts; ordinary source ABI, staging, traces, construction/reuse and fail-closed controls; `paired/manifest.json.gz` |
| `python3 -B src/simp/tests/compatibility/run_task22_negative.py --output /tmp/task22/negative` | Four isolated semantic negative controls; `negative/manifest.json.gz` |
| `coverage_ledger.py`; `verify_evidence.py`; `audit_task14.py` | 2,153 cases, 37 immutable input hashes, tracked getter/control contracts |
| `tools/h4pedant/h4pedant src/simp/tests/simp-ext`; `tools/h4pedant/h4pedant --nolinelen src/simp/src`; `git diff --check` | All pass; dedicated compact logs |

The paired runner selects starting committed HEAD `fef39229c`; its ordinary
sources equal final ordinary sources. Those receipts establish ordinary
compatibility, **not execution of the extension repair**. Final focused,
routine, negative and native runs execute/seal the final extension sources.
No performance acceptance or asynchronous signal-timing coverage is claimed:
interrupt paths deterministically raise the actual shared Interrupt constructor
from callbacks after witnessed bounded consumption.

Each negative control builds successfully (exit **0**), executes with expected
exit **1**, and fails on the intended semantic assertion, never static errors:

1. Starting sources fail `normalize/keep_abstraction/HOL_ERR`.
2. Removing only preparation's predicate guard fails
   `normalize/native ETA/HOL_ERR` (descent-created eta candidate).
3. Removing only traversal's predicate guard fails
   `child/HOL_ERR: exact policy abort`.
4. Removing only standalone argument guard fails
   `arguments/HOL_ERR: exact policy abort`.

The maintained runner pins mutations, copied source hashes and actual local
module dependency paths, uses empty private products, and removes each private
build tree immediately. It runs the final 846-check derivation fixture, not an
older red draft. Initial draft corrections (opaque HOL_ERR accessors, stack
versus theorem context, recursive solver input, sticky reentry witness, proper
conjunction maker/hypotheses, exact argument refresh counts and term typing)
are not counted as implementation failures or weakened oracles.

This checkout's compiled configuration still names
`/home/lukasz/dev/HOL/worktrees/simplifier`, while the checkout now resides under
`/home/lukasz/work`. Validation uses a temporary `bwrap` bind alias to this
**same** checkout, with a fresh `/dev`, configured cwd/HOLDIR/PATH and no source
or config rewriting. Two provisional validation attempts failed on mount-device
permissions and mixed configured/caller launcher paths; corrected runs pass.
No permission workaround, private library copy or environment failure is counted
as a source acceptance result.

## Files, cleanup and next task

Changed production files: `TraverseExt.{sig,sml}`, `simpExtLib.{sig,sml}` and
`src/Holmakefile`. Added/completed the two focused fixtures, their normal test
rules, negative runner, coverage/caller documentation and this compact evidence.
Progress has one completion entry using the landing identifier above.

Task-created private build trees, copied inputs, new fixture executables,
dependency/lock products, redundant scratch logs and agent caches are removed
after their last use. No copied tree, binary or heap is committed. Pre-existing
caller products and unrelated nested repository files are preserved.

TASK23 is next. Its persistence scope and the existing TASK24/25 recipe and
consumer scopes are unchanged; no new repair/follow-up or deferred TASK22 work
is needed.
