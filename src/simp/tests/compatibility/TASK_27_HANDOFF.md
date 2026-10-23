# TASK27 — final documentation and dependency/control audit

Landing identifier: **TASK27-documentation-audit-v1** (containing commit).
Starting HEAD: `c707baca802d7e0d22e7e8045a0dc5d3567bd7a9`, root clean.
Develop reference: `cccaa27d7099cbadc886983020cbe745db7793f3`.
Runtime: Linux/aarch64, Poly/ML 5.9.2, standard kernel, `hol.state0`.

**All bounded TASK27 criteria pass. No TASK27 blocker remains.** Every
inventoried consumer and temporary row is closed, documentation agrees with
compiled interfaces, fresh ordinary loads exclude extensions, and deliberate
extension use shares the promised controls by identity. TASK28 is ready.
This is not release approval, performance/allocation acceptance, independent
clean-build or full-distribution/cross-platform acceptance.

## Changes and API decisions

- Replaced `src/simp/src/notes.md`'s stale mixed representation/dispatch
  account; modernized `src/simp/README` and completed `src/MANIFEST`.
  **Develop clients need no migration.** Branch-only callers choose distinct
  `simpExtLib`/`TraverseExt` types and tracked recipes before installation.
- Moved filter/threaded Docfiles from simpLib to simpExtLib; deleted the
  nonexistent optional `legacy_traversedata_for_ss` Docfile. Added typed
  construction, source-handle and prepared-bundle reference entries.
  Fixed SSFRAG types/examples, ordinary projection claims, cross-links,
  dependency preludes and related split/FCP examples. Explicit rebuilding,
  quota-reset/preserving replay and branch theory/heap caveats are documented.
- Published [migration/TASK27.md](migration/TASK27.md): final per-family,
  **every consumer-row**, marker-consumer, identity, module-ownership and
  temporary-cutover closure. M6 is closed by TASK26's exact physical move;
  historical ledgers/prototypes have clear final-overlay notices, not new
  generated or weakened oracles. TASK26 remains the detailed coverage map.
- Added `audit_task27.py`/negative mutation tests: a live source gate rather
  than relabelling TASK16's historical snapshots. Added a reusable final
  signature/Docfile checker and reproducible private polyscripter driver.
- Added independent `../api-audit` testutils launchers and typed executable
  documentation. `src/Holmakefile` integrates `api-audit` at normal selftest
  level, with separate extension prerequisites, never an ordinary import.

No production `.sig`/`.sml`, generic marker, theorem-set or postkernel code
changed. Final signatures already express the intended split and were read
and checked, not churned to change comments. The TASK25 consumer's production
API/implementation prerequisites are unchanged: its isolated 93-file patch,
1,407 checks and 67 theory-builder evidence remain source-specific, not a
claim that the caller-owned worktree was patched or rebuilt here.

## Live source/dependency and ownership gate

`evidence/task27/source-audit.json.gz` records fresh holdeptool observations,
its executable hash, the complete defining-source graph and exact live hashes:

- Conservative ordinary runtime closure: **231 modules / 446 defining
  inputs**, including signatures, scripts/templates, platform and preload
  inputs. Fresh analysis cross-checks their defining dependencies, recording
  build-time/template mappings separately from runtime imports.
- **478 audited live inputs** including extension/control owners and ordinary
  BasicProvers/bossLib sentinels. Ordinary simpLib, Traverse, Opening,
  Travrules, congLib, PURE/BOOL/COMBIN and Trace signatures/implementations
  are byte-identical to pinned develop. All transitive ordinary inputs are
  pinned develop except six explicitly reviewed shared-identity inputs:
  ThmAttribute's read-only lookup pair, Cond_rewr's helper/tracker pair and
  new SimpTracking pair. Twelve later extension deltas are individually
  pinned to TASK26, not granted blanket HEAD permission.
- No ordinary-to-extension/provider/marker/split path, late arbitrary-set
  promotion, cross-registry fallback, duplicate public type/exception,
  duplicated trace/depth/tracker or hidden ordinary registration remains.
  Whole-file equality rejects computed dynamic loads and aliases that a
  lexical dependency analyzer cannot resolve. Negative mutations test them.

Ownership: Cond_rewr owns the sole live stack_limit, original Trace owns the
registered simplifier knob/ref/action/hook, SimpTracking owns one thread-local
reporter, and BoundedRewrites owns actual controls. Structural congruence
aliases retain original types. Exception/context identities are shared.
Named fragment registries are deliberately separate typed Context slots;
SF syntax is shared, lookup is only in the consuming engine. SplitData,
splitLib and explicit splitPersistLib remain single simplifier-owned modules.
The source gate states its limits: the boss sentinel is not an exhaustive
boss graph; fresh runtime evidence is separate from source equality.

## Actual fresh paths, callbacks and control identity

Final runtime receipt:
`../api-audit/evidence/20261023T084819Z-7b0ad6ac/receipt.json`.
It seals fixture sources, exact commands/environment, tools/heap/runtime,
eight complete compressed outputs and **420 actual used/loaded files**.
Generated theory paths resolve to `.hol/objs`, with real hashes, not nulls.
Requested paths alone cannot satisfy the runner; all ordinary/extension core
signature and implementation uses must be the actual native source paths.

Eight fresh processes cover simpLib/congLib in both orders, foreign split
attribute/exporter owners before/after ordinary imports: **1,374 assertions**.
Ordinary paths include the actual configured checkout's
`src/simp/src/{simpLib,congLib,Traverse,Cond_rewr,Trace,SimpTracking}.{sig,sml}`;
the compressed logs retain all paths, with entry/per-import/pre-extension
maps separate from the final extension closure. No sigobj copy substitutes
for those native sources. The configured historical root is privately bound
to this exact checkout, not a copied tree.

- Entry, every ordinary import and ordinary recipes check both loaded module
  names and global bindings; no extension catalogs/provider, marker theory,
  splitter/persistence modules, strategy heaps or private caches appear.
  This explicitly covers combinSimpsExt and trackedSimpDefaults omitted by
  older fixed-name guard lists.
- Ordinary imports retain exact prior listener pointers/order and only the
  eight known legacy additions (compute and marker/suspension listeners).
  No private split listener or registration appears. Foreign attribute/
  exporter records/data/callbacks retain exact identity. **Zero unsolicited
  foreign initialization callbacks**, including after extension imports/use.
- Saved ordinary and extension conversions observe mutations through the
  original stack_limit ref. Configured explicit depths stay local. Feedback's
  trace setting and the original Trace ref work in both directions; one
  original listener observes actual rewrites from both engines.
- Nested tracking in both directions isolates/restores extents, including
  exact arbitrary-exception payloads and empty-scope cleanup. Checks compare
  full kernel conclusions/hypotheses, not just printed output.
- One-sided fragment names prove opposite lookup **and SF consumption** fail
  with the precise missing-fragment error, without populating the other slot.
  Own-registry proofs work and Context is restored.
- `Documentation.sml` executes typed recipes, one-way reducer/public-fragment
  lifts, prepared bundle reuse and views with actual remaining/exhausted
  allowances. Existing normal-level suites also execute all eight static
  type-rejection clients, source/view/quota/traversal/lifecycle assertions.

## Documentation and preserved coverage

The reusable checker scans **835 qualified references in 83 current
documents** against actual signatures (including later catalogs/provider),
rejects unknown members, retired titles and stale ownership claims, and
retains explicit historical/private-name exclusions. Final static receipt:
`evidence/task27/doc-scan/scan.json`.

`docfiles/accepted/execution.json` records a fresh privately built standard
process_docfiles/polyscripter executable, exact prelude/tool inputs/options,
a **48-Docfile combined pass** and **30 independent example processes**,
all exit 0 with complete processed outputs and no static errors. Its compact
processed archive is retained. Pandoc is unavailable; no generated .txt/HTML
rendering or full-documentation build is claimed. All maintained source
Docfiles and compiled example/API gates required here pass.

The frozen original inputs/37 hashes and all **2,153** coverage IDs remain
unchanged. No assertion moved/deleted/weakened here. The routine gate reruns
the original 73-check ordinary suite, full post-list 642-check native suite,
focused extension suites, independent legacy/type/quota contracts and fresh
split persistence/lifecycle checks through their normal entries. TASK26's
source/coverage ledgers are not regenerated to fit a smaller result.

## Commands and exits

From repository root. `W` below means
`sh src/simp/tests/compatibility/evidence/task26/root-wrapper.sh`; this host
moved from `/home/lukasz/dev/HOL/...` to `/home/lukasz/work/HOL/...`. The
wrapper makes the configured path name this exact checkout. No foreign
products or copied build tree are substituted.

| Command | Exit / retained observation |
| --- | --- |
| `python3 -B .../compatibility/audit_task27.py` | 0; live 478-input gate, source-audit.json.gz |
| `W bin/Holmake -C src/simp/tests/api-audit check` | 0; standalone pass; repeated by final routine build, final eight-process receipt above |
| `python3 -B .../check_task27_docs.py --execute-examples --output .../evidence/task27/docfiles/accepted` | 0; fresh portable private driver, 48+30 complete passes |
| `python3 -B .../check_task27_docs.py --output .../evidence/task27/doc-scan` | 0; final static docs/signatures, no unknowns/errors |
| `python3 -B -m unittest discover -s src/simp/tests/compatibility -p 'test_*.py'` | 0; **196 tests**, including source/runtime receipt/doc failure controls |
| Interface discovery in `compatibility/interfaces` | 0; **15 tests** |
| Migration discovery in `compatibility/migration` | 0; **12 tests**, historical external path exposed read-only (below) |
| `W bin/build -t --seq=tools/sequences/upto-parallel` | 0; routine.log.gz, normal `api-audit`, legacy/extension/lifecycle/provider and strict post-list check-full all pass |
| `coverage_ledger.py`, `verify_evidence.py`, original `sha256sum -c` | all 0; 2,153 IDs / 37 immutable artifacts |
| `W tools/h4pedant/h4pedant --nolinelen --unicodeok src/simp/tests/api-audit` | 0; no diagnostics |
| `git diff --check` | 0 |

Exact migration namespace command after `W`:
`bwrap --bind / / --dev /dev --ro-bind
/home/lukasz/work/HOL/worktrees/isabelle-tactics
/home/lukasz/dev/HOL/worktrees/isabelle-tactics -- python3 -B -m unittest
discover -s src/simp/tests/compatibility/migration -p 'test_*.py'`.
It runs the unchanged default test invocation at its sealed historical paths;
no external edits or inventory/hash regeneration. The earlier in-memory
relocation diagnostic is not used as final acceptance.

Resolved harness failures are compactly retained in `development.json` and
`docfiles/development.json`: the portable read-only sandbox needed writable
/tmp for SAT proof replay and a disposable cwd for Poly export/linking with
polyscripter's exact relative preludes; a nested bind needed fresh /dev; one
pedant command named its directory rather than executable. No failed attempt
counts as a pass, and no production workaround was introduced.

## Evidence, cleanup and remaining scope

`evidence/task27/validation.json` and `evidence-seal.json` tie commands,
observations, final changed input hashes and all retained receipts/logs to
this landing. Historical inventories and TASK25 patch/seals remain intact.
Agent-created scratch executables, temporary copied Docfiles, private heaps,
new api-audit products/caches and superseded receipts/logs are removed after
sealing. Pre-existing caches/build products and caller-owned files, including
the nested .agent-files worktree's unrelated state, are preserved.

No required capability or repair is deferred. Explicit non-capabilities
(arbitrary promotion, automatic ordinary-update mirroring, opaque source
recovery, new concurrent quota safety) are documented design boundaries, not
unimplemented migration rows. TASK28 onward retains its independently defined
expanded statistical/per-workload/clean-build/release gates.
