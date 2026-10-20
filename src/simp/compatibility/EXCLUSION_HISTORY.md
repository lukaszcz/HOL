# TASK_08: faithful exclusion history replay

Landing identifier (commit subject):
`[TASK_08] Preserve split and case exclusion history`.
Entry HEAD: `7d3eaccc9`, existing `simplifier` branch; no reset or branch
change. Caller progress clarifications for TASK_07 were preserved.

## Representation and audit

History remains newest first; `build_from_history_with` folds its reverse.

- `DELETE_EVENT of rule_exclusion list` is unchanged. Strict `Excl` and
  `-*` entries retain `{original, pattern, strict=true}` and replay calls
  `exclusion_of_name original` in the *current* ancestry. Unmatched strict
  deletions still record events. Extended rule targets retain their resolved
  pattern (`strict=false`), including relaxed `rule:` and resolved bare
  ExclX names. The original spelling still identifies decision procedures.
- Adjacent strict/extended rule deletions remain ordered batches, flushed
  before strategy exclusions. Deletion is a point-in-history operation:
  later rule additions may reinstall a deleted rule. No parser, pending
  mask, callback or bounded-control implementation changed in this task.
- New private `EXCLUDE_LOOPER_EVENT of string`, inside `STRATEGY_EVENT`,
  incrementally adds one resolved split/case display to `excl_loopers`.
  `apply_strategy_event` implements it; `strategy_op` both applies and
  records it. This avoids capturing unrelated strategy state or replacing
  the accumulated exclusion set. It does not resolve names or inspect
  ambient stores on replay. Repetition is idempotent.
- Split exclusions still record existing local `DEL_LOOPER_EVENT`s first,
  then the suppression event. Case exclusions record the suppression event
  directly. The set suppresses both subsequent local additions and ambient
  persistent split / TypeBase rules. Ordinary looper/solver deletion keeps
  its existing point-in-history semantics.
- `build_from_history_with`, fragment removal/exclusion, rewrite filtering,
  and control-preserving rebuild paths already replay strategy events.
  They need no special final-state copy or new resolution stage. The only
  unrecorded exclusion-set mutations were the two repaired ExclX branches.
  `SET_EXCL_LOOPERS_EVENT` / `SET_STRATEGY_EVENT` semantics are unchanged.

Changed production file: `src/simp/src/simpLib.sml` (private event and its
application/recording only). Tests: `src/simp/src/selftest.sml`, new shared
`probes/support/ExclusionHistory.sml`, its new legacy launcher
`probes/legacy/exclusion-history.sml`, and `RunExclusionContracts.sml`.
Notes: `src/simp/src/notes.md`, compatibility README and this handoff.
No exported API, marker inspection, native-source controls, load-time
registration or fragment-resolution behavior was redesigned.

## Focused test names for TASK_09 / TASK_14

Native `selftest.sml` adds 47 checks, retaining all existing assertions:

- `case exclusion history`, `case exclusion before fragment`, and
  `repeated case exclusion history` each check direct use, unrelated
  fragment removal, fragment exclusion and rewrite-filter replay.
- `split exclusion before re-add`, `split exclusion around fragment add`,
  and `split exclusion after add` check those same four paths.
- `persistent split replay control really splits` establishes an active
  persistent rule with TypeBase case splitting separately excluded.
  `persistent split exclusion history` covers repeated persistent split
  exclusions through all rebuild paths; assumption splitting is checked by
  `persistent assumption split exclusion replay`.
- `mixed strict extended strategy history` and
  `mixed strict extended rule batch survives strategy replay` interleave
  unmatched strict, resolved rule, strict rule, split and case deletions.
- `case exclusion after Context.restore`,
  `local split exclusion after Context.restore`,
  `persistent split exclusion after Context.restore`, and
  `restored persistent split exclusion` cover replay before and after
  restoring an ambient split registration. A simpset replayed with the
  target absent stays excluded when the registration is restored.
- `mixed strict/resolved batch reparses only strict names` fails after
  removing a temporary ancestor; `mixed batch replays after restoring the
  naming context` succeeds when that ancestry is restored. Existing strict
  Excl/`-*` rejection and resolved bare/`rule:` preservation checks remain.

`ExclusionHistory.run` is legacy-only, shared between normal
`exclusion-contracts` and the paired `exclusion-history` suite. It checks
complete conversion theorems (conclusion and hypotheses), repeated strict
batches, unmatched deletion before addition, deletion/addition interleaving,
`-*`, and two-way naming-context restoration. It records full exception
fields and warning counts. The pinned develop and branch lanes agree on
all **72 ordered OBS**, with **28 OK** each. Thus strict dotted replay is
pinned independently of branch-only resolved-name tests. No xfails or
weakened legacy expectations were introduced.

## Validation

Compact receipts and hashes: [`results/task08/validation.json`](results/task08/validation.json).
Full paired manifest/raw logs: `results/task08/differential/`.
Final commands, from the repository root, exit **0**:

```sh
bin/Holmake --no-project --no-cache -j1 -C src/marker \
  --holstate="$PWD/bin/hol.state0" HOLSELFTESTLEVEL=1
(cd src/marker && ./selftest.exe)
bin/Holmake --no-project --no-cache -j1 -C src/simp/src \
  --holstate="$PWD/bin/hol.state0" HOLSELFTESTLEVEL=1
bin/build -t --seq=tools/sequences/upto-parallel
python3 src/simp/compatibility/run.py \
  --branch 189cdea5900fbb2724f2232dd844d9151597e5be \
  --output src/simp/compatibility/results/task08/differential
tools/h4pedant/h4pedant src/marker src/simp/src \
  src/simp/compatibility/probes
(cd src/simp/compatibility && sha256sum -c inputs/SHA256SUMS)
git diff --check
```

Choose a new output directory when reproducing. After landing, the landing
commit can replace the validation-only source snapshot above. That snapshot
used a temporary index and `commit-tree`, without moving HEAD or modifying
the caller's index. Receipt hashes verify its five changed executable
source files match the final working sources.

- Native marker: **70 OK**. Its Holmake target was already up-to-date;
  the built executable was explicitly rerun, with its own raw run receipt.
- Native simplifier: **507 OK**, traversal contracts **47 OK**, exclusion
  contracts **158 OK** (134 prefix assertions plus 24 history assertions).
  Existing bounded replay/quota, context, callback-staging, pure marker
  inspection and simplifier assertions all pass unchanged. Existing
  intentional warnings remain enabled and visible.
- Routine upto-parallel sanity build: **exit 0**, ending
  `Hol built successfully.` Raw output is losslessly retained in
  `sanity.log.gz` (the build emits trailing spaces). It is not the later
  full `-F`/help-doc gate.
- Paired reference: `cccaa27d7099cbadc886983020cbe745db7793f3`.
  Both library builds, all **30** executable builds and all **30** runs
  passed. Every instrumented suite has equal ordered OBS: history 72,
  prefix cases 41 each, traversal 273, reducer 15, control 8. Unchanged
  develop selftest: **73 OK** on each lane; its empty OBS comparison is
  null, not a universal trace-equivalence claim. This remains the existing
  **mixed-source** harness, sharing host heap/generated dependencies, not
  independent complete repository builds.
- Discriminating negative control: temporarily omitted recording only
  `EXCLUDE_LOOPER_EVENT`, leaving direct application intact. Executable
  build succeeded, run exited **1** with **30 failures**, beginning with
  `case exclusion history: remove fragment`. Raw logs are `no-event.*`.
  The normal recording implementation was restored before final native,
  sanity and paired runs. One earlier fixture compilation failed because
  `ListPair.allEq` needed an uncurried predicate and `filter_rewrites`
  passes a named-theorem pair; corrected without changing the oracle.
  Its unique diagnostics are retained in `fixture-type-errors.*`.

## Cleanup and remaining scope

TASK_08 acceptance is satisfied; no TASK_08 blocker remains. TASK_09 owns
the broader exclusion matrix and TASK_14 the later final paired validation;
this task does not claim their completion or whole-plan equivalence.

Harness-owned copied libraries/executables were removed by its temporary
workspace cleanup. The temporary git index was removed by its shell trap.
No copied repository, scratch build tree or agent cache remains. Normal
Holmake products stay in the existing checkout; compact unique receipts,
negative-control evidence and runnable fixtures are retained. Unrelated
and caller-owned artifacts were not removed.
