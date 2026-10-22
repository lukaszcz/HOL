# TASK22 — child-first derivation and solver/context lifetimes

Landing identifier: **TASK22-child-first-lifetimes-v4** (containing commit).
Starting HEAD: `2ec9d5c1bf712b6ded94c1c8317fc9701ad653fc`.
Develop: `cccaa27d7099cbadc886983020cbe745db7793f3`.
Linux/aarch64, Poly/ML 5.9.2, configured `hol.state0`.
Initially only supplied untracked `evidence/task22/review3/` in the main tree;
unrelated nested `.agent-files` changes were preserved.

**All bounded TASK22 acceptance criteria pass. No TASK22 blocker remains.**
The v1/v2/v3 completion claims missed callback staging. Their manifests are
historical, not current acceptance. Supplied red evidence is preserved
unchanged in `evidence/task22/{review,review2,review3}/`. Current acceptance is
[congruence/validation.json](evidence/task22/congruence/validation.json).

## Final repair

`TraverseExt.apply_congproc` now guards **invocation of each returned
conversion**, not only factory construction. Factories are collected before
selected descent. If a selected conversion aborts in a child with policy
HOL_ERR, `FIRSTCQC_CONV` catches it as rejection; the next invocation must
check the pending abort before entering the fallback callback. The same
wrapper protects weakening conversions. Factory construction and successful,
unchanged and ordinary-rejection callback order are unchanged. No exception
identity is replaced and no generic conversion/search combinator changes.

The maintained selected-child regression fails on the starting implementation
and passes with the invocation guard. It covers all three child-first drivers,
both failing and successful fallback congruences, repeated aborts and saved
recovery. Complete conclusions and hypothesis sets are checked against
kernel-derived proofs. The independent mutation removing only the invocation
guard builds successfully and fails this semantic assertion.

Only `TraverseExt.sml` changes in production in v4; no signature/API, counter,
quota, charging, observation, traversal policy or solver lifetime changes.
All ten ordinary traversal/simplifier/congruence source/signature files remain
byte-identical to pinned develop. No legacy import, reverse adapter,
retrospective promotion, cache, registration or persistence change.

## Retained implementation contracts

- Native child-first candidate search transports policy failures outside
  `tryfind`; enclosing searches and solver continuations consult the same
  application-local abort check. Ordinary conversion rejection still tries
  later candidates; ordinary Interrupt still propagates immediately.
- `CHILD_FIRST_WITH_ABORT` remains an additive driver hook; existing entry
  points retain local protection and use an inert external check. No client
  migration or successful policy/observer/charge callback was added.
- Standalone argument normalization checks abort state before user children.
  Preparation/pretest state remains application-local and reentrant.
- Prepared derivation uses fresh **declared** quota scopes and restores actual
  caller counters via `Portable.finally` on success, HOL_ERR, foreign exception
  and Interrupt. Nested calls restore enclosing private counters and failure
  state. Derivation neither spends nor depends on invocation allowances.
  Direct conversions still spend caller allowances and never refill on error.

Caller/API decisions are in [migration/TASK22.md](migration/TASK22.md).

## Maintained coverage

`derivation.sml`: **1,392 checks** retained unchanged. `lifetimes.sml`:
**315 checks**, all 63 previous assertions plus **252** new checks:

- Generic, observed and abort-hook entries; HOL_ERR payload identity, foreign
  payload identity and Interrupt; two aborts per saved conversion, failing and
  successful fallback variants, zero post-abort congruence/policy/charge/
  observer calls, inert construction and exact factory schedules.
- Without a policy abort, HOL_ERR still invokes rejecting then successful
  fallback in order; foreign/Interrupt stop immediately; UNCHANGED blocks
  fallback; successful saved reuse invokes only the selected congruence.

Retained suites cover native/bundle/view/alias/conjunct/composed private quotas,
exhaustion, nested scopes, unchanged terms and failed side conditions, exact
charges/observers/collectors, opaque lifting, saved contexts and generic recurse
lifetimes. Retained passes: **642 native**, **131 TraverseExt**, **88 focused +
174 tracked + 159 exclusion + 186 strategy + 88 tactic + 407 source/view/bundle**
checks, including **63 + 18** real tactic proof validations. These retain live
default condition depth, custom order, solver safety, counted global passes,
loop limits, head/abstraction/eta policy, selected descent and construction/reuse.
The immutable legacy streams remain 73 original / 47 traversal / 929 exclusion
plus limits; the ledger verifies **2,153 source-tied cases**. No original
assertion was removed or weakened. Coverage map: `tests/simp-ext/README.md`.

## Fresh validation

Exact source/input/runtime/tool/heap hashes, commands, exits, receipt/log seals
and configured-path wrapper are in `evidence/task22/congruence/validation.json`.
All acceptance commands exit **0**:

| Command (Python drivers under `tests/compatibility/`, with `-B`) | Evidence under `congruence/` |
| --- | --- |
| `bin/Holmake --holstate="$PWD/bin/hol.state0" --no-project --no-cache -C src/simp/tests/simp-ext -j1 check` | Eight executed launchers; `focused.log.gz` |
| `bin/build -t --seq=tools/sequences/upto-parallel` | Complete routine sanity build; `routine.log.gz` |
| `run_prior_native.py --output /tmp/task22-congruence.lu90Zh/native` | 14 receipts; final working-tree sources, integrated selftest-level-1 `all`, native/traversal/load/listener/split lifecycle; `native/` |
| `run_paired.py --candidate HEAD --candidate-signature pass --candidate-behavior baseline --prior-contracts --public-contracts --staging-contracts --negative-controls --output /tmp/task22-congruence.lu90Zh/paired` | 44 receipts; ordinary ABI/staging/traces and fail-closed controls; `paired/` |
| `run_task22_negative.py --output /tmp/task22-congruence.lu90Zh/negative` | Eleven isolated semantic negatives, 22 build/run receipts; `negative/` |
| Three supplied review fixtures, copied unchanged with `review/Holmakefile`; `Holmake --no-project --no-cache --no_prereqs -C "$tmp" -j1 check` | `REVIEW_FAILURES=0`, `REVIEW2_FAILURES=0`, `REVIEW3_FAILURES=0`; every post-abort count zero; `review*.log.gz` |
| `coverage_ledger.py`; `verify_evidence.py`; `audit_task14.py` | 2,153 cases, 37 immutable inputs and tracked-control structural audit |
| `tools/h4pedant/h4pedant src/simp/tests/simp-ext`; `tools/h4pedant/h4pedant --nolinelen src/simp/src`; `git diff --check` | Pass; compact logs |

Paired receipts select committed starting HEAD `2ec9d5c1b`, whose **ordinary**
sources equal final sources; they do not claim final extension execution.
Focused/native/routine/review/negative runs execute final working-tree code.
All final acceptance runs follow the last executable edit.

Each negative builds with exit **0**, executes with expected exit **1** and
fails its intended semantic assertion, never a deferred static error. The ten
prior controls remain intact; the eleventh removes only conversion-invocation
checking. Private loaded paths, source hashes and mutations are recorded.

An exploratory direct launcher invocation from the repository root failed
because its relative `.ui` paths require the fixture cwd; actual acceptance
uses Holmake `check`. The new factory-count expectation was corrected before
final validation: abort occurs before entering the child's factory schedule,
so only the parent's complete factory list runs. The independent semantic
negative uses the final assertion set. No original oracle changed.

## Files and cleanup

Production: `TraverseExt.sml`. Tests: `simp-ext/lifetimes.sml`, negative driver,
focused README, caller migration audit, this handoff and compact evidence.
Deterministic Interrupt injection is tested; asynchronous signal timing,
whole-plan performance and independent clean builds are not claimed here.

The configured build path remains `/home/lukasz/dev/...`, while the checkout
is `/home/lukasz/work/...`. The archived temporary `bwrap` wrapper aliases the
same checkout with fresh `/dev` and configured cwd/HOLDIR/PATH. No production
source/config rewrite or copied production libraries. Runners remove private
source trees, caches and heaps. New focused test products and scratch logs are
removed after evidence archival; pre-existing products and unrelated changes
are preserved. No generated executable, copied tree or heap is committed.

Progress has one TASK22 completion line using the v4 landing identifier.
TASK23 is next; its persistence scope and TASK24/25's recipes/external consumer
scopes remain separate, not deferred TASK22 work.
