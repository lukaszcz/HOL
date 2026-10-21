# TASK_07 handoff — extension consumer and migration inventory

Landing identifier: **TASK_07-consumer-inventory-v1** (this commit).
Inspected source HEAD: `50cfa5d709a306298991b113c7ac63e426f8aabd`.
Develop: `cccaa27d7099cbadc886983020cbe745db7793f3`.
External consumer: `442009a1f7f04366573dc2b649d31650ea7b113b`.
Production simplifier/ThmAttribute sources remain unchanged from reviewed
`cf1f863b4e5a9712ce1b179f18274eb3451f3954`; this task changes only inventory,
Python inventory checks, documentation and compact evidence. TASK_04–06
handoffs/ledgers were read, not substituted for fresh inventory validation.

## Bounded acceptance receipt

**All TASK_07 acceptance criteria are satisfied.** This is inventory and design
input, not implementation migration, engine compatibility or a performance pass.

- `migration/apis.tsv` has **193 searchable rows**: every added signature API,
  types/constructors, relevant existing construction/cooperation APIs, and the
  external producer-output/helper closure. Whole-tree signature-delta checking
  reconciles all six changed original and three new production signatures;
  unchanged `congLib` is included for its mixed implementation/type dependency.
- `migration/references.tsv` has **9,915 source-line references**, each with API
  family, category and subsequent owner. These are deliberately a lexical
  superset, including declarations, comments and homonyms; actual consumers and
  nonconsumer dispositions are in the linked consumer ledgers, not inferred
  from hit counts. The seven-column format round-trips through CSV checks.
- Inventory scans **6,447 repository and 6,671 external tracked source/doc/build/
  harness inputs**. Their aggregate content digests, all **641/680 matched-file
  hashes**, baseline signature deltas and output hashes are in
  `migration/manifest.json`. Generated products/old logs are not consumers.
  A whole-tracked-text alternative-extension sweep found only the already
  preserved review log/result JSON outside the scanned input extensions.
- `migration/MIGRATION.md` maps every API family to replacement module/type,
  caller, earliest tracked construction, invariants and task ownership. Includes
  dproc_ss, projections, Split/ExclX, **all** strategy setters, global/child-first
  tactics, source/view/bundle APIs and configured congruence. Ordinary clients
  remain ordinary; sealed baseline clients are never mechanically migrated.
- `migration/CONSUMERS.md` enumerates native fixture factories, focused tests,
  exported theories/ML dependencies, docfiles, standard builders and ordinary
  library controls. TASK_06's **2,153 IDs**, including **630 native cases**, remain
  intact; TASK_26 owns later assertion-preserving separation.
- `migration/EXTERNAL.md` records exact read-only provenance and direct clasimp/
  selftest usages, transitive libraries, source hashes and semantic assertions.
  HOL tracked/index state is clean, no nonignored untracked files, binary diffs
  empty before/after. The ignored nested `.agent-files` repository is separately
  reported: HEAD `38466dba8`, **6,576 untracked files**, no tracked modifications;
  its exact porcelain-v1 hash is retained, not misreported as a clean tree.
- `migration/EXTERNAL_TYPES.md` follows producer outputs and public/opaque/cache
  types through ordinary-looking SIMP calls, mixed iff helpers, seed/benchmark
  consumers, aesop sessions, fragments, exported iff theories and generic claset
  invocation records. D1 indexes the producer/helper names. Every actual external
  migration, including transitive interfaces/tests/docs/build edges, belongs to
  **TASK_25**, only in an isolated checkout.
- Every late-discovery path has an earlier construction decision and owner.
  In particular external clasimp/aesop defaults derive metadata **after** ordinary
  BasicProvers installation; they require a typed extension seed/update recipe
  **before** the relevant additions. Opaque legacy updates cannot be translated
  for free; no hidden replay/promotion in getters, ssfrags_of reconstruction or
  closure inspection is proposed. TASK_08 finalizes this typed provider boundary,
  TASK_24 supplies repository-side recipes, TASK_25 migrates external callers.
- `migration/IDENTITIES.md` records sharing/separation for bounded controls,
  stack_limit, tracing/tracking, named registries, Context/TypeBase/default state,
  split ownership/private replay/caches, marker/congruence types and exceptions.
  Projection types and access to the currently private tracking reporter are
  explicit TASK_08 decisions. Child-first private quota scope includes bounded
  net entries **without** public source handles.

## Validation and evidence

Fresh commands, exits, compact observations, inspected/source/input/tool hashes
and artifact seals are retained in `evidence/task07/validation.json`. No HOL
launcher, external build, tactic migration or benchmark ran in this task.

| Command/check (from repository root) | Exit / observation |
| --- | --- |
| `python3 -B src/simp/tests/compatibility/migration/inventory.py --write` | 0; explicit source-bound snapshot generation |
| Same inventory command **without** `--write` | 0; complete recomputation agrees; external status unchanged before/after |
| `python3 -B -m unittest discover -s src/simp/tests/compatibility/migration -p 'test_*.py'` | 0; **9 tests**, including missing/invented API and unknown-signature rejection, nested-comment/constructor parsing, owner/table coverage, exact file/hash/line checks and unqualified-reference retention |
| `python3 -B src/simp/tests/compatibility/coverage_ledger.py` | 0; all **2,153** source-tied cases unchanged |
| `python3 -B src/simp/tests/compatibility/verify_evidence.py` | 0; all **37** immutable review artifacts unchanged |
| `tools/h4pedant/h4pedant src/simp/tests/compatibility/migration` | 0 |
| `git diff --check`; `git diff --cached --check` | 0 |
| Production diff from reviewed revision (`src/simp/src`, `src/1`) | Empty |

Two read-only reviews checked the consumer/type closure and then reran inventory
and Python tests. The first review caught an intermediate stale eight-column TSV,
an incorrect manually transcribed nested status hash, and missed **transitive**
external producer-output consumers. These were corrected (seven-column snapshot,
measured v1 hash, EXTERNAL_TYPES/D1) and all final checks rerun. No incomplete
intermediate inventory is offered as acceptance evidence. An overlapping edit
request was rejected by the edit tool before modification and reapplied as one
combined edit; no source/worktree side effect resulted.

Routine `bin/build -t --seq=tools/sequences/upto-parallel` is **not required here**:
there are no compiled-source edits. Python/runtime/Git hashes and actual exits
bind this inventory receipt; prior Poly/ML results are not claimed as new tests.
TSV tabs are intentional data separators, not source indentation. No task-created
build trees/heaps/products/caches remain; temporary unit-test directories were
automatically removed. Caller-owned ignored products and nested files were not
touched.

## Changed files, API decisions and next task

- Added `migration/{MIGRATION,CONSUMERS,EXTERNAL,EXTERNAL_TYPES,IDENTITIES}.md`.
- Added `migration/{apis,references}.tsv`, `manifest.json`, `inventory.py`,
  `test_inventory.py`; README links the inventory; this handoff and compact
  validation receipt record acceptance.
- `.agent-files/tasks/PROGRESS.md` records actual status/one landing entry in
  the separate ignored task repository; unrelated files there are preserved.
- No production API/type/registry/control or external source changed. Replacement
  names are provisional; only the separate-type/tracked-construction requirements
  and migration ownership are fixed here. No callback/assertion was weakened.

No blocker remains for TASK_07. **TASK_08 is next**: finalize type-checked
interfaces, shared identity access and buildable cutovers using these inputs.
TASK_25's actual migration/build validation is future task scope, not a result
claimed by this inventory. No new out-of-scope repair/follow-up was needed.
