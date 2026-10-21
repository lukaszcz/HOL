# TASK_16: full selftest-enabled regression gate

**PASS.** From the repository root, executed exactly:

```sh
bin/build -t -F
```

Exit **0**, ending `Hol built successfully.` One attempt; no failed target,
source repair, assertion change, ignored required failure or remaining gate
blocker. UTC start/end: **2026-10-21 08:31:12 / 08:48:24**; elapsed
**1031.48 seconds**. This certifies the full incremental level-1 sequence,
not a clean rebuild, every optional dependency, or universal compatibility.

## Candidate and environment

Tested revision: `34ba6e1740831d147a7e0cac1bace57bc9628abe`.
Git tree: `dff6b1ecf9b3b56b4dd80e1b8ea7f07b5e2b07bd`.
The only pre-existing worktree edit was the caller's TASK_15 progress/commit
correction, preserved here. The receipt's initial status additionally shows
the task-created evidence directory. No implementation source was dirty.

Linux aarch64, kernel `7.0.0-1011-aws`, Poly/ML **5.9.2 Release**, standard
kernel (`stdknl`), 32 CPUs, 123 GiB RAM, no swap; 84 GiB disk available at
start. Exact environment, absolute working directory, argv, tool/early-heap
hashes, revision/tree, initial diff, timestamps, PID and exit status are in
[`results/task16/validation.json`](results/task16/validation.json).
No competing build was running at start; this command owned shared products.

`candidate-files.json.gz` records SHA-256 for tracked candidate files except
agent metadata and historical result directories. All those bytes were
checked again after execution: **no changes during the build**. The revision
and initial diff identify excluded tracked metadata. The final task commit
adds only documentation, evidence and progress/index updates, not compiled
sources or test inputs.

## Full-scope and fresh-execution evidence

Evidence root: [`results/task16/`](results/task16/).

- `full.log.gz`: complete, unnormalized stdout/stderr, including terminal
  escapes; its uncompressed SHA-256 is in the command receipt.
- `scope-audit.json`: recursively expanded default `tools/build/build-sequence`
  and included sequence hashes, Poly/ML/stdknl/level-1 conditions, and actual
  directory visits. **All 87 expected visits match in order**, from kernel
  and core through `src/parallel_builds/core` and both emit theory-test
  directories. `bin/hol` is the driver's phase switch, not a directory visit.
  Level-2 and Moscow ML-only entries are correctly outside this invocation.
- The log records **786 started jobs**, **346 directory scans** (including
  help processing), and **34 freshly executed selftest log targets**. Their
  output mtimes fall within this invocation, not an older partial build.
  `fresh-selftest-logs.json.gz` preserves each raw output with path, mtime
  and hash; the audit independently lists the targets and hashes.
- Fresh suites include floating point/native, n-bit, rational, finite maps,
  analysis, probability, HolSmt, transfer, coalgebras, monads, strings,
  TeX, cv_compute automation and numerous examples. LSP protocol/integer/
  sorting report **185 / 7 / 2 passed**, each with **0 failed, 0 skipped**.
- `theory-build-times.log.gz`: the driver's new `stdknl-t1` receipt with
  **650 theory timing entries**, also hashed in the audit. It is supporting
  evidence, not a substitute for the process exit/full output.
- Full help processing ran: polyscripter pass, chapter lists, Help DB
  (**46709 entries**) and signature HTML/index generation. There is no
  reduced-sequence/help-suppression warning.

`-F` explicitly overrides the previous partial sequence; the parser sets the
sequence to the default full file. `-t` selects level 1, passed to Holmake as
`HOLSELFTESTLEVEL=1` and to children as `SELFTESTLEVEL=1`. The actual full-only
visits and fresh jobs above corroborate both options. Normal up-to-date
products were reused; the cached marker/simplifier log targets are **not**
claimed freshly executed here. TASK_15 independently regenerated those
suites and the focused compatibility/load/registration/persistence targets.
This full invocation also executed the simplifier's phony focused checks.

## Triage and limitations

No introduced compatibility defect, unrelated failing target, or resource
blocker was encountered. No repair or post-repair integration rerun was
necessary. Non-fatal diagnostics and conditional scope are explicit:

- Existing virtual targets `src/update/link-to-sigobj` and
  `src/TeX/theory_tests/check_gh248` warn that their successful commands do
  not create same-named files. Both Holmakefiles are byte-identical to the
  fixed develop reference; their recipes succeeded. No failure was ignored,
  and strict-output checking was not enabled or changed.
- HolSmt's fresh output has four pre-existing non-exhaustive-match compiler
  warnings in `Alethe_ProofReplay.sml`. That source is unchanged since the
  predecessor gates. Its existing configuration checks disable external
  **cvc5, Yices and Z3** cases when unconfigured; those solver cases are
  **untested**, not passes. Built-in AUTO and unit tests ran successfully.
  External solver configuration is optional in the maintained level-1 gate.
- Optional **pandoc** and **dot** are absent: the driver explicitly reports
  skipped pandoc text/per-entry HTML and theory-graph rendering. Processed
  Markdown/help DB/signature HTML were generated. These optional products
  are not required failures of this build command.
- Higher selftest levels, other ML systems/kernels, arbitrary user callbacks
  and independent clean repository builds remain outside this receipt.
  Green regression tests do not establish universal observational equivalence.

## Predecessor continuity and TASK_17 handoff

TASK_14 tested implementation pin `5b5f07df2`; its landing `4d7bf126d` added
probe/helper/reporter coverage and evidence, not a library/API repair. Those
inputs were included in TASK_14's successful retests. TASK_15 tested
`4d7bf126d` and landed `34ba6e174`, adding only reports/evidence/index/progress.
**No compiled source or test input changed after TASK_15's tested tree.**
The audit lists exact changed paths from both predecessor pins to this
candidate; all **118 TASK_15 input hashes** still match after this full run.
Thus the paired, focused/downstream/routine and full results
apply to the same implementation. TASK_16 makes no API decision or source
change that would invalidate those gates.

Final input-integrity, simp/marker project pedant and changed-text/diff
whitespace checks pass (`final-checks.json`). Task-created orchestration and
uncompressed scratch logs were removed after recording evidence. No copied
build tree, cache, downloaded dependency or temporary heap was created.
Caller-owned caches and normal checkout build products were left intact.

Handoff: **TASK_16 has no remaining blocker**; TASK_17 may perform final
acceptance using this receipt together with `PAIRED_VALIDATION.md` and
`DOWNSTREAM_VALIDATION.md`. This gate is not itself final compatibility
sign-off. Changed files are this report, `results/task16/`, and the task
index/progress; all API and test assertions remain unchanged.
