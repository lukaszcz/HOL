# TASK_04 handoff — complete frozen public source contracts

Source/evidence identifier: **TASK_04-public-contracts-v1**, this landing commit.
Starting/measured HEAD: `8b1e8c69f5dd819d1fbe8b75cf5755f21b450499`.
Develop: `cccaa27d7099cbadc886983020cbe745db7793f3`.
Reviewed candidate: `cf1f863b4e5a9712ce1b179f18274eb3451f3954`.
Production diffs (`src/simp/src`, `src/1`) from reviewed to measured HEAD and
working HEAD are empty. This commit changes fixtures/harness/coverage records
only; the measured production sources are consequently also the landing ones.

## Bounded acceptance receipt

All TASK_04 acceptance criteria are satisfied. **Source compatibility is NOT
restored**: the constructor break remains an executed, maintained red regression.
No original signature or sealed baseline client was adapted to accept it.

- Whole-tree signature inventory covers all SIX changed baseline signatures:
  `ThmAttribute`, `Cond_rewr`, `Opening`, `Travrules`, `Traverse`, `simpLib`.
  Unchanged `congLib` has full dependency-sensitive coverage too. New branch-only
  signatures are separately classified, not mistaken for baseline clients.
- All seven complete original signatures are immutable real SML inputs.
  SHA-256/size/Git-blob/revision pins are in `public/references.json`; every run
  verifies the exact bytes against Git. The sole installed transformation is
  renaming the signature declaration to `Legacy*`, never changing its contents.
- Nine new baseline-only client sources are sealed in `public/clients.json`.
  Complete ascriptions check 116 explicit values, 18 ordinary types, four
  datatypes, four constructors, plus all inherited `Abbrev` aliases.
- Baseline executes every client successfully. Candidate passes every other
  complete signature, while both the complete `Traverse` ascription and
  complete-signature functor application reject BOTH added constructors.
- Replication retains the actual original reducer type identity on both sides;
  the unchanged exhaustive `REDUCER` match acquires a precisely source-scoped
  warning on candidate. This is recorded red despite process exit 0, not
  misreported as a static rejection or ignored because its runtime check passes.
- All reducer record/callback fields and all `traverse_data` fields are covered.
  Positive clients exercise ordinary reducers across `simpLib` and `congLib`,
  record aliases, opaque-type identities and proof-producing operations without
  importing any extension APIs.
- The original review signature/ascription, original `Traverse.sig`, original
  develop selftest and all 37 TASK_01 artifacts remain unchanged. TASK_02's
  staging/signature fixtures and six executable negative controls still run.

[`PUBLIC_CONTRACTS.md`](PUBLIC_CONTRACTS.md) is the full client/contract mapping,
initial outcome table, non-break classification and reproducible command guide.
`public/surface.json` lists every original export/type and its ascription client.
No full runtime/behavior/performance equivalence claim follows from static
coverage and the intentionally small smoke checks.

## Fresh validation and source binding

Evidence is under `evidence/task04/`. Full commands, exits, source/input/runtime
hashes, per-client outcomes and receipt fingerprints are in `validation.json`.
Both experiments use fresh isolated source trees/processes; they are NOT
independent clean repository builds. Each manifest resolves actual Git refs,
records source blobs, generated fixture/product hashes, actual loaded paths,
initial/final source maps, launchers, heap options and Poly executable/version.

| Command/check | Exit | Evidence |
| --- | ---: | --- |
| Maintained Holmake `public-contracts`, explicit candidate HEAD/reject/reviewed | 0 | `current-head-final/manifest.json`, `current-head-final.log.gz` |
| Maintained Holmake `public-baseline-control`, both selections develop/pass/baseline | 0 | `baseline-control-final/manifest.json`, `baseline-control-final.log.gz` |
| `bin/build -t --seq=tools/sequences/upto-parallel` | 0 | `routine.log.gz`, after final compiled-fixture edits |
| 23 Python protocol/public-client controls | 0 | Both final Holmake logs |
| Eight existing performance-validator tests | 0 | `validation.json`; no timing workload run |
| Immutable verifier, all seven references and nine client seals | 0 | `validation.json`; 37 prior artifacts unchanged |
| `tools/h4pedant/h4pedant src/simp/tests/compatibility` | 0 | `validation.json` |
| Working/staged `git diff --check` | 0 | `validation.json` |

Each final comparison executes **22 normal fixtures and 12 negative controls**,
with all controls rejected for their intended reason. Thus 68 actual process
launches, plus four ordinary and four minimal-heap build receipts, are retained.
The baseline-control records 44 checks; baseline/current records 41, because
three signature elaborations are explicitly expected to fail before checks.

Initial candidate public outcomes:

- `PublicThmAttribute`: 3 checks, exit 0, pass.
- `PublicCond_rewr`, `PublicOpening`, `PublicTravrules`, `PublicSimpLib`,
  `PublicCongLib`: 2 checks each, exit 0, pass.
- `PublicTraverseAscription`, `PublicTraverseFunctor`: 0 checks, exit 1,
  expected-candidate-red with exact constructor errors.
- `PublicTraverseClient`: 3 checks, exit 0, expected-candidate-red with its
  nonexhaustive match warning; replication/field/interoperability checks pass.

The separate original signature rejects candidate as before. Original staging
still observes baseline printers 1/1/1 and saved goals=1 versus candidate
0/1/2 and PrinterFailure; these unchanged findings are NOT repaired here.

A final archived receipt audit checks every selected source against its Git
bytes, every private loaded source against selected/fixture/product inventories,
all final maintained input/tool hashes, all 68 exits and expected acceptances.
No missing receipt or unexecuted launcher counts as coverage. A review found
that two expected constructor errors could mask a third static error; validation
now permits exactly the two source-attributed compiler errors, and a dedicated
negative unit control proves additional errors are rejected. Final experiments
were rerun after that Python-only tightening.

## Harness changes and API decisions

- `public/*.sml`, `inputs/develop/*.sig`, `public/{references,clients,surface}.json`:
  frozen original surface, full consumers and compact coverage/provenance.
- `public_contracts.py`, `test_public_contracts.py`, `run_paired.py`:
  opt-in public cases, complete inventory checks, exact signatures/diagnostics,
  source-path enforcement, seal checks and fail-closed controls.
- `paired/{Paired,runner,CheckSupport}.sml`, both Holmakefiles:
  minimal bootstrap and deferred, actually executed public clients. Explicit
  dependencies force frozen-signature loading: the dependency scanner alone
  misses names appearing only in some module aliases/ascriptions.
- `ThmAttribute` cannot be tested honestly by reloading it over state0's
  existing Context slots. Its dedicated Holmake-built launcher uses state.min
  on BOTH selections and requires fresh selected `.sig`/`.sml` elaboration.
  Testutils is loaded after private-first tracing starts. No source/slot rename,
  registry workaround, shared-source substitution or production change is used.
  Normal clients retain state0 and their normal preloaded early libraries.
- `holproject.toml`: disable only line-length checks under immutable
  `inputs/develop/`, preserving original `congLib.sig` long lines. All other
  style checks remain active, including on new clients/harness SML.
- README/schema/mapping/this handoff/evidence and task progress record actual
  coverage. No public API, datatype, type identity, exception, mutable control,
  registry behavior or legacy/extension implementation was changed.

`development.json` retains compact development commands/exits and unique
failures, not acceptance results. Redundant pilot/final-pre-tightening receipts,
private trees, copied products, scratch logs and task-created Python caches
were removed after their last required use. Pre-existing ignored artifacts and
unrelated files in the separate `.agent-files` repository were preserved.

## Remaining scope

No blocker remains for TASK_04. TASK_05 and TASK_06 are the next ready tasks;
TASK_07 still requires both. Original datatype restoration belongs to TASK_11,
and branch-only interface design/migration remains TASK_07–08. No out-of-scope
repair was attempted or hidden behind a weaker client.

Measured scope: Linux/aarch64, configured Poly/ML 5.9.2, one GC thread, shared
prebuilt runtime/dependencies, exact selected implementation sources. There is
no independent-build, downstream, loading-cost, lifetime, performance or other
platform certification here.
