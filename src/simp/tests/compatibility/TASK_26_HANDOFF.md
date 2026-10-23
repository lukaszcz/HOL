# TASK26 — coverage-preserving test ownership and normal integration

Landing identifier: **TASK26-test-ownership-v1** (containing commit).
Starting HEAD: `4c26cbcdc21d10531a4b38c6c539f821acad42a3`, root clean.
Pinned develop: `cccaa27d7099cbadc886983020cbe745db7793f3`.
Runtime: Linux/aarch64, Poly/ML 5.9.2, `hol.state0`, one launcher GC thread.

**All bounded TASK26 acceptance criteria pass.** There are no remaining
TASK26 blockers, deleted assertions, weakened predicates or deferred repairs.
This is test ownership/integration, not final performance, independent clean
build, full-distribution regression or cross-platform acceptance.

## Physical separation and invariant coverage

- `src/simp/src/selftest.sml` is the **complete unchanged pinned develop
  input**, SHA256 `f3618db1b09fa05d0212bc4e4f3a3b1309d50acbc726389148e58f841d8cf7a9`
  (19,385 bytes). Its 73 checks execute as the ordinary selftest. The preserved
  differential input remains untouched and verified directly against Git.
- The former mixed file moved **byte-for-byte** to
  `tests/native-extension/selftest.sml`, SHA256
  `fea5caee9ba8a9c0d0375ed88711874101382934528c2cc2916716cc90772c52`
  (274,909 bytes). All 630 reviewed cases, 12 mapped registry repetitions,
  seven warnings, embedded genuinely ordinary controls and original execution
  order survive. No assertion or setup/exception/quota/proof body changed.
- The frozen 2,153-case TASK06 ledger and TASK10 typed relocation JSON are
  unchanged. `task26_relocation.py` composes a sealed physical destination
  overlay, retaining every case ID, current check number, line and anchor.
  The verifier still checks the historical Git bytes and both original and
  current assertion seals; it never generates a smaller oracle.
- Full native execution checks **642 checks, seven ordered warnings, all
  11 original aggregate vectors and their 128 Boolean fields**. The 73-check
  ordinary execution is additional/separate, not a reduced native pass.
- New ordinary `legacy-contracts` executes all nine frozen source clients
  (18 checks), all six unchanged quota/rollback checks and one original-import
  closure check. Each process rejects loaded **and bound** extension modules,
  marker/split/persistence owners, and records actual native module paths.
  Only the already-reviewed signature-header renaming is generated; no
  assertion bodies are rewritten. Scratch inputs/products are disposable.

The full one-to-one ownership map, including every incrementally migrated
family and its normal entry, is [migration/TASK26.md](migration/TASK26.md).
There are no newly renamed native cases. The 12 registry repeats retain their
previous documented names; signature module names alone are generated.

## Normal test-level integration

`src/simp/src/Holmakefile` removes the ordinary selftest's `splitLib` link
prerequisite. Ordinary traversal/exclusion targets no longer depend on the
mixed selftest. Extension/marker/persistence targets have explicit independent
prerequisites and separate launchers. Building both families in `all` does not
import extensions into an ordinary process.

The mixed suite's unchanged five option/pair/list cases need later theory
exports. On a clean bootstrap its early smoke execution has 637 checks; that
is **not accepted as complete coverage**. A new test-only `base-hol` sequence
entry after `src/list/src` runs `native-extension/check-full` at normal level 1.
It executes the launcher, rejects missing datatype checks, verifies the entire
mapped stream and original aggregate observations. The routine build freshly
executed this post-list gate successfully. No optional-case waiver remains.

The normal level also executes the public clients and quota suite, all focused
extension suites, six fresh-load scenarios, original persistence exports and
eight reload/heap scenarios, and the newer split-lifecycle matrix. Completeness
checks in `normal_integration.py` require every focused launcher footer/count,
not merely `.uo` creation or a successful subprocess.

| Supplementary focused owner | Fresh checks |
| --- | ---: |
| TraverseExt / Cond_rewrExt | 131 / 103 |
| ordinary / extended congruence | 4 / 57 |
| simp-ext basic / tracked / exclusions | 88 / 174 / 159 |
| strategies / tactics | 186 / 88 (63 / 18 actual validations) |
| sources / derivation / lifetimes | 407 / 1,392 / 315 |
| standard recipes | 118 |
| split lifecycle | 1,762; 22 completed scenarios, saved/reloaded heap and repair |
| **Supplementary focused total** | **4,984** |

The prior matrix separately executes original 73, native 642, traversal
47/273 OBS, exclusions 929/2,703 OBS, markers 54, replay 15, registration 116,
fresh-load 11/23/26/17/19/17 and persistence 170 (including four fresh Script
assertions). Together with the six quota cases these preserve all **2,153
frozen occurrences plus 12 additions**. Counts across overlapping proof suites
are not claimed to be distinct new semantic cases.

## Bounded harness repairs

Broad Python discovery exposed historical TASK13/15/16 whole-source audit
mutation tests still being applied to deliberately changed later extension
sources, plus the physical native move. Their original mutation assertions
now run on their exact TASK15/TASK16 source snapshots; whole-source seals and
all negative mutations remain intact. Live ordinary fragment/source equality
is still checked. The historical audit commands are not relabelled as final
live dependency/performance acceptance. All **151** Python tests now execute
in the normal legacy-contract entry as well as independently.

Execution controls prove that an extension import and a wrong completion count
fail at their intended guards (both process exits 1). Other controls reject
lost/changed labels, missing/foreign module paths, missing completion/footer,
missing later-theory cases, missing native vector fields and truncated output.
The public paired target now requests repaired pass/baseline expectations;
old reject/reviewed receipts remain immutable.

## Fresh commands, exits and evidence

Durable evidence: [evidence/task26/validation.json](evidence/task26/validation.json),
`native/manifest.json`, `legacy/manifest.json`, compressed complete receipts and
`evidence-seal.json`. The manifests bind actual source bytes, command arguments,
process exits, environments, product/launcher/runtime hashes and loaded paths.
Every input seal was rechecked against the final code before archival.

This host relocated the configured checkout from `/home/lukasz/dev/HOL/...`
to `/home/lukasz/work/HOL/...`. Commands ran through the archived
`evidence/task26/root-wrapper.sh` (`sh ... command`), which binds this exact
checkout at its configured path; no copied source tree or foreign products
substitute for it.

| Command (repository root, wrapper where needed) | Exit / evidence |
| --- | --- |
| `python3 -B src/simp/tests/legacy-contracts/run.py --negative-controls --output /tmp/task26-evidence/final-legacy` | 0; 11 positive launches/25 checks, two intended negative exits 1; `legacy/` |
| `python3 -B src/simp/tests/compatibility/run_prior_native.py --output /tmp/task26-evidence/final-native` | 0; all 15 commands exit 0, including actual `Holmake -C src/simp/src -j1 HOLSELFTESTLEVEL=1 all`; `native/` |
| `bin/build -t --seq=tools/sequences/upto-parallel` | 0; `routine.log.gz`, including post-list strict `check-full`; `post-list-full.log.gz` |
| `python3 -B -m unittest discover -s src/simp/tests/compatibility -p 'test_*.py'` | 0; 151 tests; `python-tests.log.gz` |
| `coverage_ledger.py`, `verify_evidence.py`, original `sha256sum -c` | all 0; 2,153 IDs and 37 immutable artifacts verified |
| h4pedant `--nolinelen --unicodeok` on both new SML fixture directories | both 0; empty pedant logs |
| `git diff --check` | 0 |

`validation.json` retains compact development failures too: wrapper invocation,
prototype native dependency/path issues, a transient host disk-full partial
run, and the stale historical audit tests. None was counted as acceptance;
complete final reruns pass. No unrelated files were deleted to obtain space.

## Changed files, API decisions and cleanup

- Restored ordinary selftest; new `native-extension/{selftest.sml,Holmakefile,
  check.py,README.md}` and post-list sequence entry.
- New `legacy-contracts/{Holmakefile,run.py,selftest.sml,Paired.sml,
  OriginalScope.sml,README.md}` and parent targets.
- Physical overlay/verifier, complete focused-output validator, updated native
  launcher driver, failure controls and historical mutation-test ownership.
- Current coverage/migration notes, this handoff, compact evidence and actual
  progress status. Historical ledgers, sources, expectations and receipts are
  not regenerated.

No production simplifier signature/implementation, shared control, generic
marker or postkernel source changes. TASK25's migrated consumer API/code inputs
are unaffected; this task makes no new downstream/performance claim. The later
plan-wide gates retain their defined scope, not missing TASK26 work.

Task-owned prototype evidence, temporary fixture directories, launchers,
new-directory `.hol` products and scratch logs are removed after sealing.
Ordinary build products and pre-existing caller-owned artifacts are preserved.
**TASK27 is ready; no TASK26 blocker remains.**
