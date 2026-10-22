# TASK_16 handoff — baseline ordinary compiled core

Landing identifier: **TASK_16-legacy-core-v1** (containing commit).
Start HEAD: `6d768feceae9033eb1ae8d34fb331b372f126384`; ordinary worktree
was clean. Pre-existing independent `.agent-files` state was preserved.
Pinned develop: `cccaa27d7099cbadc886983020cbe745db7793f3`.
Validation snapshot: `456b2f8d529040bd5228c3b15f90331b846974ae`.
All final production sources and the two migrated native fixtures match that
snapshot. Subsequent additions are offline evidence/assembly analysis, tests
and documentation, not changes to measured production or SML workload sources.
Runtime: Linux/aarch64, Poly/ML 5.9.2; paired runs use one GC thread and the
same sealed hol.state0/shared dependencies.

Commands/exits/seals: [`evidence/task16/`](evidence/task16/), particularly
`commands.json`, `validation.json`, and the native/paired manifests. Detailed
cost/storage attribution: [`compiled-core/RESULTS.md`](../compiled-core/RESULTS.md)
and its linked raw receipts/compiler listings.

## Bounded acceptance

**All TASK_16 acceptance criteria are satisfied; no TASK_16 blocker remains.**
This is structural ordinary-core restoration, not final acceptance of the
whole performance plan or exhaustive TASK_17/18 semantics/performance audits.

- `simpLib.sml` **and its entire signature** are byte-identical to pinned
  develop. The net contains only `{thypart,ci}`; its conversion info contains
  only `name,conval`. The seven-field simpset and three-constructor history
  have baseline constructors/updates. Ordinary construction/lookup retains
  no extension resource, optional state, discriminator, companion, inventory,
  source serial/slot, metadata cell, strategy or hidden table.
- The direct `++` body and its helpers are baseline, including strict
  ordering of tag decoding, AC derivation, **all** rewrite makers, conversion
  creation/net insertion, relsimp work and existing dproc priming. Focused
  event logs/proof gates match develop, including malformed/throwing earlier
  stages, empty/excluded additions, original tagged collector context,
  limits, maker changes, history, printing, registration and TypeBase routes.
- Ordinary dependency closure is extension-free: a sealed 231-module,
  446-source transitive audit, and actual fresh imports of simpLib, boolSimps
  and congLib, reject extension engines and simpMarker/split services/stores.
  No extension preload, flag, warm-up or implicit promotion is used.
- Cost recovery is supported by **exact emitted local work**, not by treating
  uncertain timing as parity. All 43 selected native bodies and 29 optimized
  trees match, including compiler, net insertion folds, wrappers and limit
  updaters. Reservation sizes/calls/field loads/branches are identical. Only
  the previously shared tracking function's exported constant differs in
  selected backend/ICode initialization; no local compiler overhead survives.
- Every graph point and adjacent per-rule slope through 10,000 rules is no
  larger than develop. At 1,000 rules, incremental compiled retained storage
  is **82,072 vs 83,071 words**; at 10,000, **791,753 vs 801,752**. The last
  adjacent slope is **78.853444 vs 79.853444 words/rule**. Zero-rule intercepts
  match. Smaller closure capture is consistent with TASK12's shared tracking
  extraction, not a new simpLib algorithm. Graphs are not cumulative bytes/RSS.
- Extension source/signature pairs are untouched. Normal integration freshly
  executes the **88 + 174** extension compiler/projection checks, along with
  traversal, congruence, bounded-control and static type-boundary tests.

## Timing evidence and its limits

`../compiled-core/evidence/` contains four complete experiments, each with
**ten fresh AB/BA pairs**, all 11 consumed-result workloads and behavior/graph
checks: initial current/control (three samples, >=0.2-second calibration), then
longer current/control (five samples, >=0.5 seconds). No concurrent task builds
or benchmarks; no outlier removal or workload averaging. CPU/wall/non-GC/GC
are separate. No matched-heap/default-environment modification was needed.

No current CPU/wall/non-GC workload interval is significantly slower in either
campaign. Numerical parity nevertheless remains **inconclusive**, not a pass:
finite intervals overlapping one do not prove equality. The independent exact
source/codegen/layout inspection resolves the bounded compiler-work concern,
including temporary allocation sites, rather than waiving that uncertainty.
The initial slower GC intervals (reuse and compile+apply) do not reproduce in
the longer run; pure compilation GC improves in both. Identical-source control
runs themselves show isolated slower CPU rows. Full individual decisions and
intervals remain visible in `analysis.json`; no positive row conceals another.

The old TASK15 full-module red timing rows remain historical, not retroactively
accepted. This task restores the remaining ordinary module/compiler machinery;
it does not claim that all old 90 fragment timings, independent clean builds,
or TASK29/37's expanded final statistical gates have been completed.

## Files, APIs and mechanical adjacent changes

See [`migration/TASK16.md`](migration/TASK16.md) for exact decisions.

- `src/simp/src/simpLib.{sml,sig}`: full baseline pair. Every develop API remains
  unchanged; branch-only strategies, source handles/views/filtering/preserving
  replay, configured/child-first getters/tactics and Split/ExclX are extension
  interfaces only. Their distinct extension types and tracked builders remain.
  No reverse adapter, retrospective source discovery or transparent promotion.
- Adjacent baseline bodies were necessary to remove the mixed record/types:
  literal `-*`/remove_simps and name parsing; build_from_history;
  remove/exclude_ssfrags, force_add, limit/weakener/relsimp updates; rewriter,
  traversal getter; process_tags, conversion/rule/&& paths; all ordinary
  tactic entry points, psr/allasms/global_simp_tac; printers. **TASK_17 reviews
  exclusions/replay exhaustively; TASK_18 reviews tactic/marker staging
  exhaustively.** These are original bodies, not new redesigns or placeholders.
- `selftest.sml`: the temporary ordinary optional/configured projection block
  becomes checks for the baseline total/inert getter, dproc/travrule pointer
  preservation and limits. All tracked strategy/configured cases remain.
  Native stream/count remains 642 (630 frozen + 12 earlier additions).
- `tests/fresh-load/syntax.ML`: first reject extension modules after ordinary
  loading; then explicitly load simpMarkerLib for the original qualified
  marker/foreign-syntax assertions. Those original assertions/labels remain.
- `tests/compiled-core/`: baseline-focused public proofs, route/limit reuse,
  graph/slope positive controls, fresh paired runner and codegen evidence.
  Holmake integrates behavior/storage at `HOLSELFTESTLEVEL=1`; measurement
  products stay private/temporary. Offline receipt/slope/statistical audit
  distinguishes uncertain numerical results from structural work acceptance.
- TASK13/15 historical auditors accept only the exact reviewed restoration,
  not arbitrary extension-free replacements. Historical mutation controls,
  source inventories, frozen 2,153-case ledger and all 37 immutable inputs
  remain. Relocation supplements identify the two reviewed native fixture
  changes without changing original source oracles/assertion mappings.

CUTOVERS **M1–M5 are closed**; X1/X2/M0 were already closed. M6 remains its
existing TASK26-owned interleaved **test** integration, not ordinary library
plumbing. No new transitional dependency, out-of-scope repair, registry/control
copy, generic marker/postkernel change or external-worktree edit was introduced.

## Fresh validation

All final commands exit **0**; executable launchers were actually executed.

| Check | Result / evidence |
| --- | --- |
| `bin/build -t --seq=tools/sequences/upto-parallel` | Final integrated complete routine sanity build; `routine.log.gz` |
| Holmake with hol.state0, `--no-project --no-cache -C src/simp/src -j1 HOLSELFTESTLEVEL=1 all` | Ordinary, separate extension, fragments and new compiled-core gates; `native/build-focused.json.gz` |
| `run_prior_native.py --output /tmp/task16-native-final` | 14 successful build/native/traversal/exclusion/marker/replay/registration/fresh-load/persistence receipts; native 642 checks; `native/` |
| `run_paired.py` on snapshot above, public/prior/staging/negative controls | 44 receipts: old signature, nine public clients, frozen original/traversal/exclusion/limits, construction/use/proof staging and intended fail-closed controls; `paired/` |
| Four compiled-core timing/control runs | 80 measured fresh processes plus focused behavior/graph processes; exact graphs/slopes and all consumed-result proofs; `../compiled-core/evidence/` |
| Two compiler-emission runs | Current and identical-source control; 43 native bodies, optimized/backend/ICode evidence; `../compiled-core/assembly/evidence/` |
| Python compatibility / interfaces / migration | **135 / 15 / 12** pass |
| Python performance / fragments / routes / fragment assembly | **30 / 36 / 7 / 15** pass |
| Python core / core assembly | **9 / 10** pass |
| Source/receipt audits; immutable verifier; coverage ledger | Byte-exact core, unchanged extension compiler, complete graph/slope receipts; 37 inputs / 2,153 cases intact |
| h4pedant; `git diff --check` | Pass |

Resolved exploratory failures and the first routine tool timeout are recorded
in `attempt-notes.json`, not counted as passes. In particular, final native
product seals pass after removing task-generated scratchTheory exports before
the rerun; no library-product integrity check was weakened.

## Cleanup and next task

Task-created private trees/heaps, caches, scratch theory exports, copied input
scratch files and redundant exploratory receipts/logs are removed after keeping
compact unique evidence. No build tree, generated executable or heap is
committed. Unrelated caller-owned build products and `.agent-files` state are
preserved. **TASK_17 is next.**
