# TASK_09: exclusion contract matrix

Landing identifier: `[TASK_09] Complete exclusion contract coverage`.
Entry/source-library revision: `cd5c9241258e44c30c23452cd455ea213a004de5`.
The existing `simplifier` branch and caller's TASK_08 progress corrections
were preserved. No production library or marker source changed: the tests
found no additional bounded exclusion defect.

## Maintained coverage matrix

Paths below are relative to `src/simp/`. **L** means legacy-only input,
executed unchanged on pinned develop and this branch, as well as normally.
**X** means branch-only tests in `src/selftest.sml`; these are NOT submitted
to develop. Every listed check passed in the final runs. Existing tests
are retained, not xfailed or weakened.

| Contract | Passing maintained test / fixture |
| --- | --- |
| L literal `rule:` installed / unmatched | `probes/legacy/excl-rule-{installed,unmatched}.sml` |
| L literal `solver:` installed / unmatched | `probes/legacy/excl-solver-{installed,unmatched}.sml` |
| L literal `looper:` installed / unmatched | `probes/legacy/excl-looper-{installed,unmatched}.sml` |
| L literal `split:` installed / unmatched | `probes/legacy/excl-split-{installed,unmatched}.sml` |
| L literal `case:` installed / unmatched | `probes/legacy/excl-case-{installed,unmatched}.sml` |
| L each of those ten, conversions, named rewrites AND decision procedures | `LegacyFailures.prefix_checks` / `prefix_stores`, shared by those launchers and normal `exclusion-contracts` |
| L overlapping longer name survives; active-before preconditions | `rewrite/dproc before`, `Excl`, `operator`, `Excl.replay`, `operator.replay` in `prefix_stores` |
| L Excl agrees with `-*`: deletion, complete theorems, callbacks, silent unmatched names | All ten prefix fixtures; `probes/legacy/exclusion-parsing.sml` |
| L bare/qualified dotted, numeric suffix and sibling selection | `ExclusionParsing.run`: `parse parser_stem`, `parser_stem.1`, `bool.parser_stem`, `bool.parser_stem.2` |
| L three-component non-ancestor dotted names remain positional | `parse parser_unknown_ancestor.dotted.part` |
| L bare `Thy$Name` is literal, NOT qualified syntax | `parse bool$parser_stem`; `dproc exact Excl/-* bool$parser_stem` |
| L strict unknown ancestor, nonnumeric dotted, empty theory, too many dots | `bad Excl` / `bad -*` rows in `ExclusionParsing.run` |
| L empty string, empty/numeric suffix, missing bare/qualified target are silent | `parse` rows for `""`, `parser_stem.`, `.1`, `a..1`, `missing`, `bool.missing` |
| L dprocs use original complete spelling, not rewrite patterns or descendant prefixes | `dproc exact Excl`, `dproc exact -*`, `dproc exact replay` (seven spellings) |
| L repeated exclusions and unrelated-removal replay | Every parser row applies twice and replays both APIs; prefix store replay; `ExclusionHistory.run` |
| L unmatched delete before add, interleaved delete/add | `ExclusionHistory.run`: `unmatched deletion before addition`, `addition after deletion`, `interleaved add delete` |
| L actual current-theory change and restoration during strict replay | `parser replay really changed current theory`, `new theory strict Excl/-* replay`, `restored theory Excl/-* replay` |
| X prefixed literal rewrite AND dproc vs installed extended targets in all five namespaces | `literal collision rule:matrix_rule`, `looper:matrix_shared`, `solver:matrix_shared`, `split:scratch$matrix_split`, `case:bool` |
| X literal collision direct Excl, `-*`, repeated/replayed Excl preserve the extended target | Each collision's `deletes both literal stores` AND `preserves the extended target`; active rewrite/dproc preconditions |
| X unmatched literal Excl / `-*` / replay do NOT fall through to installed extended targets | Each of the five collisions' `unmatched literal preserves extended target` checks (warning-sensitive) |
| X `rule:` success and same-named looper preservation | `qualified rule exclusion leaves a same-named looper`; `rule: ExclX takes the kernel Thy$Name spelling` |
| X `looper:` really deletes the looper, not a same-named solver | `qualified looper really removes only the looper` |
| X `solver:` deletes both safe/unsafe named solvers, not a same-named looper | `qualified solver really removes only the solver`; `qualified solver suppresses safe/unsafe callbacks` |
| X `split:` local, persistent, conclusion and assumption targets | `ExclX split: suppresses a named split looper`; `persistent split exclusion history`; `persistent assumption split exclusion replay` |
| X `case:` TypeBase target | `ExclX case: suppresses TypeBase splits`; `case exclusion history` |
| X relaxed `rule:` dotted / kernel spelling, unloaded theory | `Thy.Name rule: ExclX of a rewrite from an unloaded theory`; corresponding `Thy$Name` test |
| X relaxed numeric suffix preserves sibling, including replay | `relaxed suffix sibling preservation matrix_nonancestor.suffix.1` and `matrix_nonancestor$suffix.1` |
| X bare ExclX initially retains strict parsing | `bare ExclX keeps strict initial parsing`; `bare dotted looper/solver retains strict parsing` |
| X explicit strategy namespaces accept dotted displays and whitespace without rule parsing | `qualified looper/solver accepts a relaxed dotted display`, with active-before controls |
| X rule/dproc priority vs strategy fallback | `mixed literal/extended exclusions resolve in order`; `adjacent extended exclusions see pending rule deletions`; theorem-named looper control |
| X ambiguity and explicit disambiguation | `shared strategy ambiguity`; `qualified solver then bare looper ordering`; `qualified looper then bare solver ordering` |
| X warning-sensitive unmatched errors in every namespace AND bare form | `warning-sensitive missing {missing,rule:missing,looper:missing,solver:missing,split:missing,case:missing}`; each expected error is also checked silent |
| X repeated ordinary strategy deletion is unmatched, unlike repeated literal deletion | `ordinary repeated looper/solver is unmatched` (also warning-sensitive) |
| X ordinary looper/solver replay; later re-addition remains effective | `ordinary looper/solver exclusion replay`; `ordinary looper/solver later re-addition replay` |
| X split/case replay and repetition; exclusions before/after additions | TASK_08's `case exclusion history`, `case exclusion before fragment`, `repeated case exclusion history`, `split exclusion before re-add`, `around fragment add`, `after add` |
| X mixed strict, resolved and strategy history; unrelated removal/filtering/Context restoration | TASK_08's `mixed strict extended strategy history`, `mixed strict/resolved batch reparses only strict names`, and split/case Context checks |
| X bounded/requirement precedence and inspection staging | `ExclX` / `Once ExclX` / `Ntimes ExclX routes without leaking marker hypotheses`; `Req0` / `Req0 Once` / `ReqD ExclX`; `R7 pure ExclX inspection` wrapper table |
| X requirement actually suppresses an active rewrite on an unsolved goal | `Req0 ExclX suppresses the active rewrite on an unsolved goal`; corresponding `Req0 Once` test |
| X marker identity, arbitrary bytes, malformed arguments, wrapper classification | `../marker/selftest.sml` ExclX table and focused tests; TASK_06 marker coverage unchanged |

Named rewrite compilation appends `.1` even for a single equation. The
numeric rows intentionally cover this: deleting `parser_stem.1` deletes
both the compiled `parser_stem.1` entry and descendants of the overlapping
source `parser_stem.1`, but not `parser_stem.2.1`. Decision-procedure names
instead match exactly. These develop quirks are pinned, not simplified
into a nicer parser. Exception checks retain full HOL_ERR fields, including
`-*` as the strict parser's origin function. Ordinary directive/history
representation differences are not compared as public semantics.

Warning instrumentation forwards to the original sink and restores it
on exceptions. Legacy and branch matrix setup check warnings are enabled and not
promoted to errors. Unmatched successes AND expected errors must be silent;
raw logs retain load-time output and diagnostics. The new strategy tests
use VALID and invoke the actual validation, checking conclusions and
hypotheses as well as subgoals. There are no marker integration gaps left
from the audit: TASK_06's wrapper/classification tests and TASK_07's routing
checks still pass; the two Req0 observations above strengthen integration.

## Validation and reproduction

Receipts/source hashes: `results/task09/validation.json`.
Native raw logs: `marker-native.log`, `simp-selftest.log.gz`,
`exclusion-contracts.log.gz`, `traversal-contracts.log.gz` in that directory.
Paired manifest/raw output: `results/task09/differential-final/`.
The two parsing run logs and routine log are losslessly gzip-compressed
because theory export/build output contains trailing spaces; no observable
was normalized out of the comparison. Manifest commands describe original
uncompressed output filenames.

Final commands, from the repository root, all exit **0**:

```sh
bin/Holmake --no-project --no-cache -j1 -C src/marker \
  --holstate="$PWD/bin/hol.state0" HOLSELFTESTLEVEL=1
(cd src/marker && ./selftest.exe)
bin/Holmake --no-project --no-cache -j1 -C src/simp/src \
  --holstate="$PWD/bin/hol.state0" HOLSELFTESTLEVEL=1
bin/build -t --seq=tools/sequences/upto-parallel
python3 src/simp/compatibility/run.py \
  --branch cd5c9241258e44c30c23452cd455ea213a004de5 \
  --output src/simp/compatibility/results/task09/differential-final
tools/h4pedant/h4pedant src/marker src/simp/src \
  src/simp/compatibility/probes
(cd src/simp/compatibility && sha256sum -c inputs/SHA256SUMS)
git diff --check
```

Use a new output directory when reproducing; after landing, its commit
can replace the source-library revision. Library sources are unchanged
from that revision. The runner snapshots working probe/support bytes,
whose manifest hashes match the final sources; no temporary source commit
was needed. Branch-only assertions run in native selftest, never in the
reference lane.

- Native marker **70 OK**; simplifier **629 OK** (122 added assertions),
  exclusion contracts **929 OK**, traversal contracts **47 OK**. Native
  marker was up-to-date in Holmake and explicitly rerun. Native simplifier
  was rebuilt and ran after its final edit; contract targets also ran in
  final Holmake and the routine build.
- Reference `cccaa27d7099cbadc886983020cbe745db7793f3`: both library builds,
  all **32** executable builds and all **32** runs exited 0. Each prefix
  fixture: **41 OK**, **133 equal ordered OBS** on each lane. New parsing
  fixture: **535 OK**, **1357 equal ordered OBS**. All other instrumented
  comparisons also agree (3055 total ordered OBS per lane). Unchanged
  develop suite: **73 OK** each; its empty OBS comparison remains null.
- Routine upto-parallel sanity build: **exit 0**, ending
  `Hol built successfully.` This is not the later full `-F` gate.
- Whitespace/pedant and frozen-input integrity checks: **exit 0**.

During development, three fixture issues were corrected: an unavailable
`isNone` helper (compilation), selecting the first OR_CLAUSES conjunct
instead of the third, and initially overlooking the compiler's
`.1` suffix in an expected deletion set. Each was corrected, then native
and paired final runs passed. No legacy assertion was removed or weakened,
and no failing production behavior was reclassified as expected.

## Handoff to TASK_13 / TASK_14 / TASK_17

Changed executable inputs: `src/selftest.sml`, shared
`LegacyFailures.sml`, new `ExclusionParsing.sml`,
`RunExclusionContracts.sml`, and new legacy `exclusion-parsing.sml`.
Documentation/index/progress and task09 evidence accompany them. No public
API decision changed; literal Excl strings stay literal, ExclX alone opts
into extended namespaces. No mechanical migration was made.

All TASK_09 acceptance criteria are satisfied; no TASK_09 blocker remains.
TASK_13 should preserve this parser/repetition distinction in documentation
and use the matrix to avoid migrating genuine literal strings. TASK_14
can rerun all maintained legacy inputs with the normal harness; explicit
new-only tests must remain native/branch-only. TASK_17 should retain this
matrix and the following limitations in its final report:

- The paired harness is **mixed-source**, sharing the host heap, generated
  markerTheory and dependencies, NOT independent repository builds.
- Finite exclusion tests do not establish universal callback equivalence,
  complete load-time equivalence, or whole-plan compatibility. Existing
  fresh-load/persistent-registration work and full-tree gates remain in
  their assigned tasks; none is claimed complete here.
- Passing normal incremental builds is not a clean bootstrap or full
  `bin/build -t -F` result.

Runner-owned private libraries/products were automatically removed.
Redundant intermediate logs/results were removed after final validation;
only compact unique evidence is retained. No copied build tree, temporary
index or agent-created cache remains. Normal checkout build products and
unrelated/caller-owned artifacts were left intact.
