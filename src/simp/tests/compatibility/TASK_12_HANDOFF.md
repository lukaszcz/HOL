# TASK_12 handoff — direct conditional rewriting and paired compilation

Landing identifier: **TASK_12-conditional-split-v1** (containing commit).
Start HEAD: `640f5a1cbcb6d38ee08093cf2d007e14f0fb923a`.
Pinned develop: `cccaa27d7099cbadc886983020cbe745db7793f3`.
Measured snapshot: `06927a63d9796d33d6cc98f936c2cab27f3b66a5`.
Runtime: Linux/aarch64, Poly/ML 5.9.2, configured hol.state0; paired
launchers use one GC thread. Production sources did not change after the
snapshot. Source/input/tool seals are in `evidence/task12/validation.json`,
the four subdirectory manifests, and `evidence/task12-allocation/manifest.json`.
The main worktree started clean; pre-existing nested `.agent-files` changes
and unrelated temporary files were preserved.

## Bounded acceptance

**All TASK_12 acceptance criteria are satisfied; no TASK_12 blocker remains.**
This is not final ordinary simpset/compiler/storage/loading restoration,
whole-plan performance acceptance or an independent clean-build comparison.

- Ordinary `Cond_rewr.COND_REWR_CONV` is the **entire pinned direct constructor**,
  not paired construction followed by projection. All matcher preparation,
  curried closures, application, solver/trace/tracking stages, loop checks and
  exception handlers are unchanged. The entire implementation file is pinned
  develop except the exact tracking-block extraction described below.
- Explicit `Cond_rewrExt` owns paired/configured/context preparation. Both
  runners share one lexical `instth` / `HO_PART_MATCH` preparation. Opaque
  `prepared` binds the supplied actual `BoundedRewrites.control` once;
  `runners` only projects stored bound closures. There is no counter snapshot,
  replacement ref, allowance reset, recompilation or callback on projection.
  Failed matches/conditions/orders do not spend; success decrements once;
  alternating and late projections share partial consumption and zero.
- Ordinary Cond_rewr loading has **no extension dependency**. Both fresh
  timing and allocation processes audit the complete loaded inventory and
  reject Traverse, simpLib and extension modules. New shared `SimpTracking`
  is a lower-level internal facility, not an extension registration.

## APIs, identities and caller migration

`Cond_rewr.sig` retains every baseline declaration and the public
`is_var_perm` helper. Branch-only `COND_REWR_CONVS`, `WITH_CONFIG` and
`WITH_CONTEXT` move to `Cond_rewrExt`, retaining their signatures/behavior.
`Cond_rewrExt.prepare` / `runners` add the actual-control binding interface.
The extension compiler uses it, deleting its duplicate local bound wrappers.
The temporary mixed ordinary simpLib compiler explicitly names the extension
paired primitive until TASK_16 removes that compiler/net; it does not make
ordinary Cond_rewr depend on extensions. No fragment/net representation
changes were made here.

`SimpTracking.{sig,sml}` owns the **exact original tracking block**, including
its one ThreadLocal slot, nested extents and exceptional cleanup. Cond_rewr
uses direct `val` aliases, not forwarding functions; both runners call the
same reporter. `Cond_rewr.stack_limit` remains the sole depth ref. Configured
NONE reads it live per candidate, SOME fixes invocation-local depth. Term
ordering uses the original helper unless explicitly supplied. Trace actions,
listeners, bound datatype/refs, theorem types, HOL_ERR and Interrupt identities
remain the existing ones. Diagnostic origins remain `Cond_rewr`, deliberately.
As on develop, STRUCT_WRAP converts foreign callback exceptions to HOL_ERR
with their message/origin; it does **not** preserve their foreign constructor.
Interrupt is rethrown unchanged. Outer `with_tracking` preserves its caller's
exception identity. Tests distinguish these contracts.

Changed callers: the four native selftest paired/configured calls, four
TraverseExt test calls, Task08 control/cutover clients, notes and the renamed
`Cond_rewrExt.COND_REWR_CONVS` docfile. Original baseline inputs and assertions
are unchanged. Only current anchors/hash/API decisions in the additive native
relocation overlay change. [migration/TASK12.md](migration/TASK12.md) closes X1
and records M2's TASK_16 removal owner; threaded M3/X2 still belong to TASK_13.
No new deferred repair or transparent legacy promotion was introduced.

## Behavioral/build validation

Evidence: [`evidence/task12/`](evidence/task12/), plus allocation evidence
below. `commands.json` and each manifest retain exact commands, exits,
load paths and seals. Commands below are from repository root; all final
commands exit **0**. Failed exploratory/default-flag attempts are identified
in commands.json and are not counted as passes.

| Check | Result |
| --- | --- |
| `Holmake --holstate="$PWD/bin/hol.state0" --no-project --no-cache -C src/simp/src -j1 HOLSELFTESTLEVEL=1 all` | Native and normally integrated suites pass, including new cond-rewr-ext |
| `bin/build -t --seq=tools/sequences/upto-parallel` | Two complete passes; final pass after all SML fixtures |
| `run_paired.py --public-contracts --prior-contracts --negative-controls --candidate <snapshot> --candidate-signature pass --output <fresh>` | All nine public clients, original signature, 73 original / 47 traversal / 929 exclusion / six limit checks; exact frozen streams; 12 fail-closed controls |
| `run_prior_native.py --output <fresh>` | 642 native, focused markers/registration/replay, fresh-load streams and persistence/heap scenarios |
| `Holmake ... -C src/simp/tests/compatibility/interfaces -j1 check` | 29 executable design checks and eight static rejections |
| Python unittest discovery, compatibility / performance | 75 / 30 checks |
| `coverage_ledger.py`; `verify_evidence.py` | 2,153 frozen cases and 37 immutable input seals intact |
| h4pedant on production, compatibility, performance, conditional and extended traversal directories; `git diff --check` | Pass |
| `audit_task12.py evidence/task12`; `performance/audit_evidence.py <control> <candidate>` | Whole-body/source correspondence and all 40 final timing receipts pass |

New `tests/cond-rewr-ext/selftest.sml` has **103** checks: saved live/fixed
depth, condition stacks/order/substitution, matching and alpha conversion,
side-condition failures and incorrect proofs, conditional/AC rules, custom
order callbacks, bounded bypass, actual counter exhaustion/refill, alternating
runners and late projections, construction/application errors, arbitrary
callback/Interrupt behavior, exact shared Trace streams, nested/exceptional
tracking and complete theorem/hypothesis validation. `src/Holmakefile` runs it
at the normal selftest level, without making it an ordinary library import.
Existing separate TraverseExt **131** and simpExtLib **88** checks also pass.

## Timing and structural allocation decision

`ConditionalPerformance.sml` directly measures ordinary constructor/application
work, without mixed simpLib/net costs. Escaping construction results are saved
at the matcher boundary and exercised after each batch. Application results,
hypotheses and solver-call consumption are checked. Runner/schema tests reject
missing/wrong events/counts, failed processes, wrong source/fixture binding,
cross-suite substitution and extension-loaded inventories.

Final baseline/baseline control ran before the final candidate comparison.
Each has ten alternating AB/BA pairs, five calibrated 0.25-second samples per
fresh process, consumed results, no outlier removal. CPU includes GC; wall
and GC are reported separately, not added again. Raw measurements, counts,
20,000-resample median CIs and full source provenance are archived.

| Workload | Control CPU ratio | Candidate CPU ratio [95% CI] |
| --- | ---: | --- |
| Conditional constructor | 1.0062 | 0.9878 [0.9615, 1.0027] |
| Unconditional constructor | 0.9761 | 0.9548 [0.9345, 0.9859] |
| Conditional reuse | 0.9579 | 0.9682 [0.9447, 0.9969] |
| Conditional complete | 0.9582 | 0.9813 [0.9468, 1.0036] |
| AC constructor | 0.9777 | 1.0302 [0.9568, 1.1492] |
| AC reuse | 1.0022 | 1.0295 [0.9995, 1.0793] |

Wall follows CPU; GC remains in each summary. These noisy intervals alone
are **not equivalence or a permitted regression budget**. No workload has a
reproducible measured slowdown, but the AC intervals require structural
inspection rather than being declared statistical passes.

That inspection is maintained in [allocation/README.md](allocation/README.md)
and [allocation/ASSEMBLY.md](allocation/ASSEMBLY.md), with source-bound
compiler listings and graph evidence in `evidence/task12-allocation/`.
`task12_allocation.py` builds/exercises both exact versions in fresh private
processes; **24 executable checks per version**, **13** fail-closed Python
controls. No opaque closure-layout casts or production instrumentation.

- The entire direct constructor and application source are unchanged; there
  is no extra pair, configured closure, record or discarded-runner allocation.
- At 0, 1, 8, 64, 256 and 1024 rules, constructor/solver-bound/stack-bound
  retained graph slopes are respectively **23→22, 13→12, 14→13 words/rule**
  for unconditional, conditional and AC cases. All adjacent differences are
  exact; proof-result slopes remain 3 / 32 / 3. A fresh-cell positive control
  measures exactly 5n words on both sides.
- Generated closure reservations shrink **72→64, 80→72, 88→80 bytes**. All
  **28** application allocation sites retain identical ordered sizes; indirect
  call counts are unchanged. Tracking is still inlined across the opaque
  module boundary: no extra reporter/adapter call. Normal untracked reuse
  with no tracking slot executes no extra instructions or loads. The moved
  key is loaded from a literal pool instead of captured in each closure.
- Native listings are **not byte-identical**: four extra static instructions
  concern existing-entry/new-entry tracking paths; an existing slot containing
  NONE adds one address instruction. These are documented, not hidden. They
  add no new application allocation/call and no per-rule retained storage.

Together the direct baseline bodies, shared exact tracker, generated-work
inspection and fresh probes close the bounded constructor/application concern;
no paired-preparation overhead remains on ordinary Cond_rewr. This is not a
claim of identical nanosecond timing on every machine, cumulative allocation,
RSS/lifetime equivalence or final simplifier storage acceptance. Other runtimes
and architectures were not measured. Existing mixed compiler/fragment/net and
tactic regressions remain owned by the already-planned later tasks, not waived
by these results.

## Cleanup

Private paired/allocation trees are automatically removed by their runners.
Task-created pilot outputs, copied evidence, temporary sources/logs and new
conditional-test caches/launchers are removed after archiving the unique
final receipts. No copied build trees, heaps or generated binaries are
committed. Ordinary build products and unrelated caller artifacts are left
alone. TASK_13 is next.
