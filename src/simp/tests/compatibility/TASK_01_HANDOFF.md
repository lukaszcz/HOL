# TASK_01 handoff — pins and durable evidence

Evidence/source identifier: **TASK_01-pins-v1**, the commit adding this file.
Starting source HEAD: `cf1f863b4e5a9712ce1b179f18274eb3451f3954`.
Baseline: `cccaa27d7099cbadc886983020cbe745db7793f3`.
Reviewed candidate equals starting HEAD; no tracked/nonignored dirty changes.
The separate ignored `.agent-files` repository and existing build products
were already present; its initial untracked state is recorded, not erased.

## Delivered / acceptance receipt

- `initial-state.json`: actual starting HEAD, pinned references, dirty state,
  branch/reference drift, Poly/ML 5.9.2 on aarch64/Neoverse-V2, one-GC-thread
  launcher configuration, heap/build options, environment and current
  runtime/heap/configuration hashes; 78 reviewed simplifier/test file hashes.
- `evidence-manifest.json` and `SHA256SUMS`: origins, SHA-256 and sizes for
  **37 immutable artifacts**, 134,857 bytes: all 35 compact supplied review
  files plus the two exact develop Git inputs. No supplied input was missing.
- `inputs/develop/{selftest.sml,Traverse.sig}`: unchanged baseline files,
  recovered directly from the pinned Git objects, with Git blob identities.
  ABI source was also verified as that complete signature plus rename/wrapper.
- `../performance/review-20261021/`: unchanged `staging.sml`, `abicheck.sml`,
  `bench.sml`, `detail.sml`, `memory.sml`, `reproduce.py`, original JSON and
  compact unique logs/compressed observations. Colocation preserves the
  original script's relative file lookups. No old archive/build trees copied.
- `COVERAGE.md`: maintained native/contract/fresh-load/marker/registration/
  persistence/replay coverage and prior shared-infrastructure cleanup boundary.
- `README.md` and `../performance/README.md`: provenance, bundle map,
  historical findings, explicit limitations and reproduction checklist.
- `verify_evidence.py`: read-only standard-library integrity check, **not**
  the paired executable runner. `validation.json` records exact validation
  commands, exits, compact output and metadata/source hashes.

All bounded TASK_01 acceptance criteria are satisfied: durable inputs,
original differential input, hashes, provenance, initial-state manifest,
coverage inventory and reproduction prerequisites exist. No unrelated source
was changed, no historical result was fabricated and no repair or performance
pass is inferred. TASK_02 is next; this does not complete P01 as a whole.

## Validation

Run from the repository root. Fresh preservation validation is recorded in
`validation.json`; historical native/paired successes remain historical only.

| Command/check | Exit | Observation |
| --- | --- | --- |
| `git status --porcelain=v1 --untracked-files=all` before writes | 0 | Empty main-repository initial status; actual HEAD exactly reviewed candidate. |
| `poly --version` | 0 | Poly/ML 5.9.2 Release. |
| `sha256sum -c src/simp/tests/compatibility/SHA256SUMS` | 0 | All 37 immutable artifacts match. |
| `python3 src/simp/tests/compatibility/verify_evidence.py` | 0 | Exact baseline Git inputs and ABI derivation; historical JSON/log counts, stages, equality and retained words agree; 78 source fingerprints match pinned candidate. |
| Exact original `/tmp` versus preserved bytes | 0 | All 35 originals unchanged; no missing supplied input. |
| Current runtime/heap/config fingerprints versus snapshot | 0 | Fingerprinted products/configuration unchanged by TASK_01. |
| Shared marker/ThmSetData/postkernel baseline diff | 0 | Matches develop; exact command in `initial-state.json`. |
| `git diff --check` and `git diff --cached --check` | 0 | No whitespace errors in landed changes. |

During verifier development an initial assertion-count regex failed (exit 1):
ANSI color codes prevented a word-boundary match. The verifier now strips ANSI
codes before counting `OK`; the historical inputs were never modified.
Final validation is successful. No HOL probes, launchers, broad benchmarks or
builds were run. No production/compiled implementation or build rules changed;
the SML additions are immutable, unbuilt differential inputs. Therefore the
compiled-source routine sanity-build requirement is not triggered here.

## API/control and ownership decisions

No production API, representation, scheduling, mutable-control or test
assertion changes. Ordinary versus extension separation remains future work.
New evidence directories do not enter current Holmake dependency scopes.
The local historical-log ignore exception admits only these preserved logs;
fresh measurements must use a separate source-tied output directory.

## Known limitations / next prerequisites

No blocker remains for preservation. Missing historical process exit-status
receipts and binary/heap hashes are **unknown**, not reconstructed from log
contents or from today's hashes. The supplied script's expected exit codes
are documented as expectations only. This provenance gap prevents treating
copied logs as fresh acceptance, not completion of this evidence task.

TASK_02 owns a fail-closed runner, actual launcher execution/elaboration,
loaded-path evidence, complete schemas and failure controls. TASK_03 owns
fresh four-finding measurements and baseline variability. In particular:

- Explicitly override/record effective paths: inherited `HOLDIR` differs from
  configured `Systeml.HOLDIR`. Existing products are not certified clean builds.
- Preserve the original script but do not treat it as the acceptance runner:
  it does not reject missing observations or prove module-path isolation.
- New benchmark fixtures must retain and exercise projection/construction
  results; historical ignored return values remain visible and unchanged.
- Record fresh exits and runtime/heap hashes, independent-build versus
  isolated-source scope, calibrated iterations, CPU/wall/GC accounting and
  graph-word units. Never relabel historical results as new passes.

No task-created temporary tree, heap, cache or executable remains. Caller-owned
`/tmp` review inputs, generated build products and unrelated ignored files
were untouched. `.agent-files/tasks/PROGRESS.md` is updated only for this
bounded task and its newly unblocked dependent, with one completion line.
