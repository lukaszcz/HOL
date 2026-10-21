# TASK_08 handoff — separate interfaces and buildable cutovers

Landing identifier: **TASK_08-interfaces-v1** (the commit containing this file).
Inspected/start HEAD: `74ddf80bef07bad35e55416786cbfe2ead8eb67f`.
Develop reference: `cccaa27d7099cbadc886983020cbe745db7793f3`.
External consumer remains `442009a1f7f04366573dc2b649d31650ea7b113b`;
no external source/build/worktree was changed or executed. Poly/ML 5.9.2 Release.
Final file/tool/runtime hashes, external state, commands/exits and artifact seals
are in `evidence/task08/{validation,commands,design-check}.json`.

## Bounded acceptance

**All TASK_08 acceptance criteria are satisfied.** This is a finalized,
compile-checked design, not implementation of TASK_09–16, an external migration,
or a legacy behavior/performance pass. Production `src/simp/src` and `src/1`
remain unchanged from the reviewed candidate. No remaining TASK_08 blocker.

- `interfaces/DESIGN.md` settles reducer/data types, explicit opaque lifting,
  tracked fragment/set construction, both extension projections, actual mutable
  controls, sources/views/bundles, exclusions/named lookup and standard recipes.
  Both tracked projections return **TraverseExt** data, never restored ordinary
  reducers/sets. Construction-once and per-application-refresh schedules stay
  distinct. Partial/exhausted controls are actual shared refs; preserving replay
  retains them, reset replay remains separate. No getters recompile or invent
  opaque source inventories.
- `interfaces/Task08{ReducerTypes,TraverseExt,API}.sml` are executable signature
  prototypes, including complete parallel simpset and congruence interfaces and
  an explicit typed default-provider boundary. `Task08Clients.sml` elaborates
  positive consumer functors; `Task08Cutovers.sml` checks critical intermediate
  type plumbing. No fabricated engine implementation or permissive stub exists.
- `Task08Reducers.sml` concretely implements only lifting/configuration adapters;
  `Task08Controls.sml` concretely implements only actual-control binding/private
  scoping/prepared-event rebinding, using the real paired matcher. Executed
  selftests validate callbacks/context payloads, live/explicit depth, real HOL
  proofs, late/exhausted extraction, alias/filter/reset sharing, both use orders,
  exception/interrupt restoration and nested tracking. Native history and source
  algorithms remain later implementation requirements, not prototype claims.
- Eight genuinely static negative clients reject reducer/set/fragment misuse
  in both directions, an extension congset in ordinary congLib, and an ordinary
  set as a tracked provider seed. Accepted-body and missing-file negative controls
  both fail the executed gate. Missing completion, stale loaded paths and missing
  static observations fail Python validation too.
- `interfaces/graph.json` is acyclic in the final and all eight declared
  intermediate states. Ordinary/shared imports cannot transitively reach an
  extension/service in the final graph. Singletons retain explicit owners:
  existing Cond_rewr depth ref, Trace, BoundedRewrites, Context/TypeBase, markers,
  SplitData/splitLib and existing exceptions. Internal **SimpTracking** will own
  the one extracted thread-local reporter; ordinary with_tracking aliases it.
  Typed fragment registries intentionally have distinct slot names.
- `migration/final-apis.tsv` finalizes **193** API decisions joined to TASK_07's
  actual consumer/construction/owner ledgers. Scoped signature export checking
  binds core entries to prototypes and shared entries to their current owners.
  External rows bind to the typed provider boundary, **not 193 compiled external
  migration clients**. Actual downstream migration/build remains TASK_25.
- `interfaces/CUTOVERS.md` bounds every TASK_09–16 compile/test cutover and
  transitional removal owner. Active extension-test/consumer closure migrates
  in 10/11 before ordinary constructor restoration; final recipes/test placement
  in 24/26 do not permit broken intermediate builds. Mixed ordinary imports,
  metadata and slot adapters end by 16; 27 independently audits closure.
  The initial extension engine uses existing paired/threaded APIs until 12/13;
  explicit X1/X2 edges, module-availability checks and early compiled API witnesses
  prevent forward references to not-yet-extracted primitive modules.
- The BasicProvers boundary is resolved, not postponed: an explicit ordered
  typed recipe/provider constructs its own tracked seed before its extension
  installations. Getters retrieve only prepared state. Ordinary arbitrary
  transforms/windows/local updates require typed counterparts at extension
  callers; automatic arbitrary-state mirroring is **not offered**. Persistent
  declaration preparation is explicit rebuilding, not a metadata-preserving
  import or a getter. No generic theorem-set/postkernel hooks or overhead on
  ordinary updates. TASK_24 implements the catalog/provider; TASK_25 migrates
  the complete external typed update/cache/context closure already inventoried.

## Fresh validation

Commands below ran from the repository root. Exact argv, actual exits and output
hashes are in `evidence/task08/commands.json`; executed module paths and all
29 check observations are in `interfaces.log`. The generated `.hol`/launcher
products were removed after their last use; these logs are unique compact proof
of execution, not committed binaries/heaps.

| Check | Exit / result |
| --- | --- |
| `python3 -B .../interfaces/check_design.py --run --negative-controls --output .../evidence/task08` | 0; signatures and both consumer/cutover functors elaborated, 29 HOL checks, eight expected static rejections; accepted-body/missing-file controls each exit 1 |
| `bin/Holmake --holstate="$PWD/bin/hol.state0" --no-project --no-cache -C src/simp/tests/compatibility/interfaces -j1 design-check` | 0; standalone runnable integration target |
| Interface validator unittest discovery | 0; **15 tests**, including missing decisions, wrong signature scope, missing provider boundary, cycles, indirect imports, missing/unbounded transitions, incomplete/stale observations |
| TASK_07 migration unittest discovery | 0; **12 tests**, source anchors and original marker closure unchanged |
| Existing compatibility unittest discovery | 0; **48 tests** |
| `python3 -B .../coverage_ledger.py` | 0; **2,153 source-tied cases unchanged** (integrity, not a fresh run of all cases) |
| `python3 -B .../verify_evidence.py` | 0; **37 immutable artifacts unchanged** |
| `bin/build -t --seq=tools/sequences/upto-parallel` | 0; **Hol built successfully**, final compiled prototype sources; `routine.log.gz` |
| `tools/h4pedant/h4pedant .../interfaces .../migration` | 0 |
| `git diff --check`; `git diff --cached --check` | 0 |

The initial prototypes caught and fixed launcher/signature-only load planning,
a theorem-specification namespace/quantification error, and a scoped witness
mapping for threaded_cong_ss. An attempted new link/target in the old top-level
README/Holmakefile changed TASK_07's sealed source-reference anchors: its test
correctly failed. Those two files were restored exactly; new runnable commands
live entirely in interfaces. No prior inventory assertion was weakened or old
snapshot regenerated. All final checks above were rerun after those fixes.

Two read-only design reviews found no unresolved interface/identity/cycle blocker.
The final review distinguished declared-graph checking from future production
import auditing and external decisions from compiled external clients; the gate
and documentation explicitly maintain those boundaries. Scoped export/provider
checks were strengthened accordingly. No new out-of-scope repair was required.

## Files and next owner

- Added `interfaces/`: DESIGN/CUTOVERS/README, full signature/consumer/cutover
  prototypes, two concrete boundary prototypes, selftest/Holmake target, eight
  negative ML clients, graph/checker and 15 validator tests.
- Added `migration/final-apis.tsv`; updated MIGRATION, IDENTITIES, EXTERNAL and
  EXTERNAL_TYPES with finalized decisions/links (historical TSV/manifest intact).
- Added this handoff and compact `evidence/task08` receipts/logs.
- Updated only TASK_08/09/next-task/completion status in the already-dirty ignored
  `.agent-files/tasks/PROGRESS.md`; unrelated nested-repository state preserved.

**Next: TASK_09**, additive separate traversal. Follow CUTOVERS.md and retain all
existing semantic assertions. No engine performance or final source-compatibility
claim is made here; those known regressions remain implementation tasks.
