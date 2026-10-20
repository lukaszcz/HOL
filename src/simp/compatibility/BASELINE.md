# TASK_01 baseline and handoff

Landing identifier (commit subject):
`[TASK_01] Pin compatibility baseline and harness`.

## Pins and initial state

- Implementation HEAD: `62a6bdc3453c29e8f31faa72f2b70a245f44840d`.
- Audited HEAD: the same full revision. `git log <audited>..HEAD` is empty;
  there are no subsequent implementation changes to review.
- `git status --porcelain=v1 --untracked-files=all`: empty at task entry.
  Existing ignored `.agent-files`/build artifacts are not implied absent.
- Existing branch: `simplifier`. No new branch, reset, merge or cherry-pick.
- Fixed reference: `cccaa27d7099cbadc886983020cbe745db7793f3`.
  `origin/develop` resolved to this value at entry; the harness does not
  resolve that moving ref. The git object, not a downloaded tree, is used.
- Host: Linux aarch64; Python 3.12.3; configured Poly/ML checkout.

The final paired run's own working-tree snapshot is in
`results/task01/manifest.json`: it contains the new evidence files, not
uncommitted implementation changes. Only the pinned committed library
sources are tested. No compatibility repair or expectation weakening is
part of this commit.

## Frozen inputs

`inputs/develop/selftest.sml` is byte-identical to:

```sh
git show cccaa27d7099cbadc886983020cbe745db7793f3:src/simp/src/selftest.sml
```

- Source git blob: `236c43518d6e1436939e4183b5db80c7ebd32e7b`.
- SHA-256:
  `f3618db1b09fa05d0212bc4e4f3a3b1309d50acbc726389148e58f841d8cf7a9`.
- Original length: 519 lines. No edits, wrappers or injected assertions.

The investigation directory `/tmp/hol-simp-compat.H6G7y2/` was present.
Preserved in `inputs/investigation/`:

- README with original revisions, method and limitations;
- compatibility and namespace selftest reproducers;
- the two paired compatibility logs and two namespace logs, preserving
  detailed failures rather than only pass counts.

All files were copied byte-for-byte except `branch-namespace.log`: one
redundant final blank line was removed to satisfy `git diff --check`.
Its original SHA-256 was
`01bc8f0f012f73e470de40623585d50b6992aad919cfa707017e422337ffa8fb`;
no diagnostic text changed. All retained input hashes are in
`inputs/SHA256SUMS`. The historical
README reports the original develop suite as exit 0 / 73 OK on both sides;
its two repetitive suite logs were not copied because this task reruns
that exact input and retains fresh results. The original omitted logs had
these SHA-256 values:

- `branch-legacy-suite.log`:
  `dceea2a3db33a05038641ec25a05444a3035d98a9c19f6f8b8fe42ad4a96fa35`.
- `develop-legacy-suite.log`:
  `29545a9eacd9ccbbcb5e15149b72c58c50c952174e257b26db0a8387d3de1c78`.

The historical logs are attributed evidence, not independently rebuilt
results. No temporary binaries or copied trees were present there; the
caller-owned original directory was left untouched. Promotion/strengthening
of the failure probes belongs to TASK_02/03, not this preparation task.

## Reproduction and completed validation

See [README.md](README.md) for full commands, generated Holmakefiles,
heap selection, result format and isolation limitations. The retained
paired result is `results/task01/`, produced by:

```sh
python3 src/simp/compatibility/run.py \
  --branch 62a6bdc3453c29e8f31faa72f2b70a245f44840d \
  --output src/simp/compatibility/results/task01
```

The output directory must be absent when reproducing; use a new directory
rather than overwriting evidence. The final invocation defaulted `--branch`
to HEAD, which resolved to the exact revision above. All executed expanded
Holmake targets and executable commands are recorded in `manifest.json`.

| Check | Reference | Implementation |
| --- | --- | --- |
| Private library Holmake build | exit 0 | exit 0 |
| Control Holmake build / run | 0 / 0, 4 OK | 0 / 0, 4 OK |
| Unchanged develop suite build / run | 0 / 0, 73 OK | 0 / 0, 73 OK |
| Control ordered OBS results | equal | equal |

Control observations cover simplification conclusion/empty hypotheses,
one unchanged-conversion callback, and a tactic's actual validation theorem.
No control warning or exception was emitted. The unchanged suite emits no
OBS records: its comparison is explicitly `null` (assertions passed, not a
claim that all internal observables were compared).

The loader audit confirms each lane uses its own simplifier/marker library
modules, and local Q where required, not the host simpLib. The manifest
records 42 reference and 44 implementation source hashes plus shared input
and tool fingerprints. The host's generated markerTheory is intentionally
shared. This is a **mixed-source** differential run, not two independent
repository builds and not a full compatibility gate.

Routine validation:

```sh
bin/build -t --seq=tools/sequences/upto-parallel
```

Exit 0, ending `Hol built successfully.` The first invocation was terminated
by the command harness's 300-second timeout during num/cv_compute tests;
it was not counted as a pass. The command was rerun with an 1800-second
allowance and completed successfully. It reused normal incremental build
products, as usual; the second invocation need not rerun successful tests
from the first. The final differential run above was performed **after**
this host build. Compact command/output receipts and style/input integrity
checks are recorded in `results/task01/validation.json`. The routine build
is not `bin/build -t -F`, and no full-tree result is claimed.

All runner-created private copies/products have been removed automatically.
Only compact inputs, manifests and text logs are retained; temporary routine
build logs were reduced to the validation receipt and removed. Normal host
build products and unrelated/caller-owned artifacts were not deleted.

## Handoff / acceptance boundary

Changed files: this directory's runner, legacy control, preserved inputs,
documentation and task01 results; `.agent-files/tasks/TASK_INDEX.md` and
`.agent-files/tasks/PROGRESS.md`. No existing compiled implementation source
or ordinary selftest changed. Finalized API decisions: **none**.

All TASK_01 criteria are satisfied: pins/state/hashes and commands are
recorded; unchanged develop tests are preserved; the Holmake harness builds
and runs an ordinary control on both versions; maintained legacy inputs,
branch-only tests, fresh-load fixtures and future result records have named
locations. There are no TASK_01 blockers. No red compatibility probe was
rerun or reclassified as green here; the preserved investigation findings
remain open for TASK_02/03 and the subsequent repairs. Wider lifetime,
namespace, warning and callback contracts are not established by this
control. Next unblocked task: TASK_02; TASK_06 is also now unblocked.
