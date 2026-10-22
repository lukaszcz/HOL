# TASK22 — child-first derivation and solver/context lifetimes

Landing identifier: **TASK22-child-first-lifetimes-v2** (containing commit).
Repair starting HEAD: `a6c21c9d745cc88b55e67200c9bc1dc4286f42fa`.
Develop: `cccaa27d7099cbadc886983020cbe745db7793f3`.
Linux/aarch64, Poly/ML 5.9.2, configured `hol.state0`.
Initial main-tree state: only the supplied untracked `evidence/task22/review/`.
Pre-existing nested `.agent-files` changes were preserved.

**All bounded TASK22 criteria now pass, including both review failures.**
The v1 completion claim was incorrect: its passing tests missed pretest
poisoning and direct late native-ETA exceptions. The original v1 manifest
(`evidence/task22/validation.json`) is historical, not current acceptance.
The supplied red reproducer and result remain unchanged in
[`evidence/task22/review/`](evidence/task22/review/validation.json).
Current source-tied acceptance is
[`evidence/task22/repair/validation.json`](evidence/task22/repair/validation.json).

## Implementation and control contracts

- `simpExtLib.sml` factors the existing callback-abort protection into private
  helpers. Each call saves, clears and finally restores its enclosing abort
  state, rethrowing the original exception even after conversion combinators
  have swallowed/wrapped it. This works for HOL_ERR, opaque foreign payloads
  and the actual shared Interrupt constructor.
- `may_reduce_arguments` now uses this callback-only scope. A failed nonopaque
  pretest cannot poison later pretests or an enclosing derivation. It neither
  resets allowances nor charges/observes/collects/compiles anything. Opaque
  pretests still short-circuit without invoking the policy.
- `SIMP_CONV_CHILD_FIRST` passes the **same protected policy** to traversal and
  the configured native ETA entry, with an application-local abort scope
  outside TRY_CONV. A descent-created ETA candidate therefore cannot turn
  policy HOL_ERR into ordinary candidate rejection. Saving a conversion is
  still inert; reuse starts clean.
- Prepared normalize/arguments retain their private fresh-declared quota
  scope. Callback state and quota restoration remain independent: nested
  pretests preserve partially spent outer counters, nested derivations restore
  outer allowances, and every outer exit restores actual caller counters.
  Direct conversions still spend actual caller allowances; aborting one does
  **not** refill them.
- Ordinary reducer/solver HOL_ERR remains candidate rejection, not an abort.
  No charge point, successful callback schedule, context refresh, traversal
  order, proof rule, congruence selection, public type or entry point changes.
  `simpExtLib.sig` documents the direct/pretest guarantees. There is no hidden
  promotion/replay API or new global cache/control/registration.

Only extension production code changed in this repair. Ordinary `Traverse`,
`simpLib`, `Opening`, `Travrules` and `congLib` source/signature bytes still
match pinned develop; all other ordinary sources are unchanged from the repair
starting HEAD. The existing v1 `TraverseExt` and standalone argument guards
are retained and freshly tested. Caller ownership is recorded in
[migration/TASK22.md](migration/TASK22.md).

## Maintained coverage

`tests/simp-ext/derivation.sml` now executes **1,116 checks** (846 retained,
270 added). New intersections cover:

- Nonopaque plain/observed pretests, partial/exhausted actual counters,
  immediate recovery and recovery after successful normalization, repeated
  failures, exact callback counts and no charging/observation/quota reset.
- Pretests nested in normalize/arguments after witnessed bounded consumption:
  caught HOL_ERR/foreign/Interrupt restore the outer callback scope and leave
  its partially spent quota intact; outer proofs still use the second quota.
- Direct descent-created native ETA checks after a bounded rewrite: exact
  exception payload/provenance, one callback before abort, successful saved
  reuse, complete kernel-derived proofs/hypotheses, and no public quota refill.

Retained derivation cases cover native/bundle/view/alias/conjunct/composed
controls; fresh declared uses after public exhaustion; nested success and
exceptions; observer/charge/head-policy aborts; unchanged children and failed
conditions; ordinary lifted reducer/solver/collector failures; inert setup,
exact per-application/per-child collector counts and failed-candidate quotas.
`lifetimes.sml` still executes **60 checks**: single-step roots, opaque lifting,
retained generic recurse contexts across nesting/failure/reuse, exact context
and callback traces, live head policy and congruence-selected descent.

Fresh retained coverage: **642 native**, **131 TraverseExt**, **88 focused +
174 tracked + 159 exclusion + 186 strategy + 88 tactic + 407 source/view/bundle**
checks; **63 + 18 tactic validations**. These retain live default depth, custom
order, solver safety/validation, counted global passes, looper limits,
root-condition recursion, capture avoidance and construction/reuse contracts.
The immutable legacy streams remain **73 original / 47 traversal / 929
exclusion**, plus limits. The ledger verifies **2,153 source-tied cases**.
All eight simp-ext launchers still execute from normal `check` and
`HOLSELFTESTLEVEL=1 all`; no original assertion was removed or weakened.

## Fresh validation

All commands below exit **0**; exact argv, source/input/runtime/tool/heap
hashes, log hashes, receipts and observations are in the repair manifest.

| Command | Evidence under `evidence/task22/repair/` |
| --- | --- |
| `bin/Holmake --holstate="$PWD/bin/hol.state0" --no-project --no-cache -C src/simp/tests/simp-ext -j1 check` | Eight executed launchers, 1,116 derivation and 60 lifetime checks; `focused.log.gz` |
| `bin/build -t --seq=tools/sequences/upto-parallel` | Complete routine sanity build; `routine.log.gz` |
| `run_prior_native.py --output /tmp/task22-repair/native` | 14 successful receipts; final working-tree sources, normal selftest-level-1 integration, traversal/exclusion/marker/replay/load/listener and fresh split lifecycle; `native/` |
| `run_paired.py --candidate HEAD --candidate-signature pass --candidate-behavior baseline --prior-contracts --public-contracts --staging-contracts --negative-controls --output /tmp/task22-repair/paired` | 44 receipts, ABI/staging/legacy streams and fail-closed controls; `paired/` |
| `run_task22_negative.py --output /tmp/task22-repair/negative` | Six isolated semantic negative controls; `negative/` |
| Supplied review `Holmakefile`/`selftest.sml`, copied unchanged to a private directory, built **and executed** with `check` | Five assertions pass, `REVIEW_FAILURES=0`; `review.log.gz` |
| `coverage_ledger.py`; `verify_evidence.py`; `audit_task14.py` | 2,153 cases, 37 immutable inputs, tracked compiler/getter/control audit |
| `tools/h4pedant/h4pedant src/simp/tests/simp-ext`; `tools/h4pedant/h4pedant --nolinelen src/simp/src`; `git diff --check` | All pass |

Python drivers above are under `src/simp/tests/compatibility/`, run with
`python3 -B`. The paired driver selects committed starting HEAD `a6c21c9d7`,
whose **ordinary** sources equal final sources. It establishes ordinary
compatibility, not execution of this extension repair; focused/native/routine,
review and negative runs execute the final working-tree extension sources.

Each negative control builds successfully (exit **0**) and executes with
expected exit **1**, failing the intended semantic assertion, never a static
error. The four v1 controls still reject missing preparation/traversal/argument
protection. Two new independent mutations remove only the pretest scope or
only the direct native-ETA predicate guard. They fail, respectively,
`pretest/false/HOL_ERR: pretest recovers immediately` and
`direct/native ETA/HOL_ERR: exact abort after descent`. Private module paths,
source hashes, mutation text and finished-fixture markers are recorded.

One initial new-fixture run incorrectly expected a recovered pretest to return
false despite its eta-contractible argument. Corrected to the existing true
contract; no production change or original assertion weakening was involved.
All final checks run after the last executable change. Interrupt paths raise
the shared constructor deterministically after consumption; asynchronous
signal-timing, whole-plan performance and independent clean builds are not
claimed by this bounded task.

This checkout's compiled configuration names `/home/lukasz/dev/...`, while it
now resides under `/home/lukasz/work/...`. As in v1, commands use a temporary
`bwrap` same-checkout path alias, fresh `/dev`, and configured cwd/HOLDIR/PATH;
no config/source rewrite or copied production library. The wrapper is preserved
in the manifest. Private source/build/negative trees are removed immediately
by their runners. New task-created launcher/cache products and scratch logs
are removed after evidence archival; caller-owned pre-existing products and
unrelated nested changes are preserved. No copied tree, binary or heap is
committed.

Changed files: `simpExtLib.{sml,sig}`, maintained `derivation.sml`, negative
runner, focused coverage README, migration audit, this handoff and compact
review/repair evidence. Progress gets one TASK22 completion line. No bounded
TASK22 work remains. TASK23 is next; its persistence scope and TASK24/25's
recipes/external consumer scopes remain separate, not deferred TASK22 repairs.
