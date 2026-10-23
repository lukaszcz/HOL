# TASK26 — executable test ownership

The immutable [TASK06 ledger](../coverage-ledger.json.gz) still contains all
2,153 case IDs, assertions, matrix rows and ordered streams. The immutable
[TASK10 mapping](task10-relocation.json) still describes every incremental
native type/constructor/projection migration and its 12 added registry checks.
[TASK26's physical overlay](task26-relocation.json) composes **only a path
change**, with an exact whole-file hash. Every native anchor retains its line,
case ID, current check number, literal and typed decision. Nothing is renamed,
generated away, deleted, reordered or re-oracled.

| Case family | Executable owner | Normal entry |
| --- | --- | --- |
| `original:0001–0073` | `simp/src/selftest.sml`, byte-identical to pinned develop and `inputs/develop/selftest.sml` | `simp-selftest.log` in `simp/src` |
| `native:0001–0630`, 12 registry repeats | `tests/native-extension/selftest.sml`, byte-identical to TASK25's mixed suite, including all embedded ordinary controls | `check-full` in the level-1 test directory scheduled after `list/src`; early `simp/src` target `native-extension` is bootstrap smoke only |
| `traversal:0001–0047`, `exclusion:0001–0929` | unchanged `tests/contracts/` | `traversal-contracts`, `exclusion-contracts` in `simp/src` |
| `limits:0001–0006` | unchanged `compatibility/paired/PriorLimits.sml`, installed natively without modifying its assertions | `legacy-contracts` in `simp/src` |
| markers 54, replay-order 15, registration 116 | unchanged focused owners | `simp-marker-tests`, `replay-order`, `split-registration` in `simp/src` |
| six fresh-load scenarios: 11/23/26/17/19/17 | unchanged `tests/fresh-load/` | `fresh-load-regressions` in `simp/src` |
| persistence 170 (four script checks and eight process scenarios) | unchanged `tests/split-persistence/` | `split-persistence` in `simp/src` |
| frozen seven-signature source surface, nine clients / 18 checks | unchanged `compatibility/public/` and `inputs/develop/*.sig` | `legacy-contracts`; only generated signature headers are renamed |
| new original import scope / 1 check | `tests/legacy-contracts/OriginalScope.sml` plus namespace guard in its launcher | `legacy-contracts` |
| new ordinary staging, fragments, compiled core, exclusions | existing dedicated `tests/tactics`, `fragments`, `compiled-core`, `exclusions` | `ordinary-tactics`, `fragment-contracts`, `compiled-core`, `literal-exclusions` in `simp/src` |

The 73-check ordinary input and 642-check integration suite are **separate
executions**, not a replacement of 642 by 73. All 2,153 frozen occurrences plus
12 additions execute in their owners. Native output also compares all 11
aggregate vectors (128 Boolean fields) to the preserved reviewed output, not
merely the aggregate `OK` labels.

## Supplementary extension ownership (all in normal level 1)

| Parent target / owner | Complete launcher observations |
| --- | --- |
| `traverse-ext` | 131 |
| `cond-rewr-ext` | 103 |
| `congruence-ext` | ordinary 4 + extension 57 |
| `simp-ext` | basic 88, tracked 174, exclusions 159, strategies 186 (63 validations), tactics 88 (18 validations), sources 407, derivation 1,392, lifetimes 315 |
| `standard-recipes` | 118 |
| `split-lifecycle` | 1,762: twenty matrix scenarios / 1,698 checks, export-save 31, export-reload 30, dispatcher repair 3; 22 pass observations and saved/reloaded heap observations |

`normal_integration.py` checks all counts and unique launcher footers, including
lifecycle scenario completeness; `run_prior_native.py` archives these fresh
phony-target outputs. Assertion source hashes and actual launch receipts remain
part of the run manifest. Supplementary focused assertions do not replace the
reviewed native assertions with similar-looking smaller tests.

## Dependency and lifetime boundary

Ordinary `selftest.exe` no longer has a `splitLib.uo` link prerequisite. Ordinary
contract targets depend on ordinary modules, not the mixed selftest. Extension,
marker and persistence targets have explicit separate prerequisites and execute
separate processes. Ordinary source clients and the original import-closure
fixture reject extension bindings at runtime and record actual module paths.
`all` builds both library families, but building an extension is not importing
it into the ordinary launcher. No production API, type, control or callback is
changed by this task.

`HOLSELFTESTLEVEL=1 all` in `simp/src` executes every early focused target;
`base-hol`'s later test-only directory makes all five original option/pair/list
assertions mandatory once their exports exist. A 637-check bootstrap is never
accepted as the full 642-check regression. The full checker fails closed if
later dependencies are absent; no new production configuration flag is needed.

The public paired target now requests repaired pass/baseline expectations,
not the obsolete reject/reviewed mode. Historical red receipts remain unchanged.
Historical TASK13/15/16 mutation unit tests now use their exact old source
snapshots where whole-file extension seals deliberately ceased to describe the
current tree. Every old mutation assertion remains executable; live ordinary
restoration remains checked. Final live dependency and performance audits retain
their separate plan owners, rather than relabelling old snapshots as current.
