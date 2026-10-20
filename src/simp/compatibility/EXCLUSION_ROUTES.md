# TASK_07: literal and extended exclusion routes

Landing identifier (commit subject):
`[TASK_07] Separate literal and extended exclusion routes`.

Entry HEAD: `d536a8893` (TASK_06), on existing `simplifier` branch. No
branch/reset/merge operation. Caller edits clarifying TASK_05/06 statuses
and landing IDs in task progress were preserved.

## Implementation and API decisions

- `simpLib.Excl` is always literal. Every `DExcl` becomes a
  `LiteralExclusion`, parsed with `exclusion_of_name` / develop's
  `munge_simpset_name`, then applied with `delete_exclusions`, exactly the
  helpers used by `ss -* names`. No rule-membership test, extended-store
  lookup, namespace interpretation, ambiguity check, warning or fallback
  occurs on that route. Unmatched names still record strict deletion.
- `simpLib.ExclX : string -> thm` aliases `markerLib.ExclX`.
  `DExclX` uses the existing extended resolver and its five namespaces:
  `rule:`, `looper:`, `solver:`, `split:`, `case:`. `rule:` retains relaxed
  dotted/kernel spellings, including non-ancestor theory names. Bare
  extended names still use the strict parser initially, preferring installed
  rules/dprocs over strategy targets, then detecting strategy ambiguity.
  Every unmatched ExclX target now errors, including bare names: explicit
  opt-in does not create an unmatched strict legacy deletion event.
- Extended rule targets, including bare ones, record resolved patterns with
  `strict=false`; literal Excl and `-*` record `strict=true`. Strict replay
  reparses in the current theory context; resolved replay does not.
- A single ordered request list carries both directive kinds. Adjacent
  rule deletions are batched in original order, with pending patterns
  masking rules during later extended resolution. The batch is flushed
  before any non-rule exclusion, preserving rule/strategy history order.
- `destExclX` recognizes bounded ExclX payloads in the existing `DBounded`
  arm. Once/Ntimes do not bound an invocation control. Requirement
  classification still wins, remains tactic-only, and strips at the old
  tactic stage. No wrapper recognition order or legacy bounded directive
  handling changed. The temporary unsupported rejection is gone.
- `strategy_free` is unchanged: no eager directive proof decoding, fragment
  resolution or callbacks were added to inspection. Explicit operations
  `del_looper`, `remove_solver` and `del_split` remain available unchanged.

Changed production/API files: `src/simp/src/simpLib.{sml,sig}`;
`src/marker/markerLib.sig` and `src/simp/src/splitLib.sml` have comment-only
updates. Documentation: new `simpLib.ExclX.smd`, restored literal
`simpLib.Excl.smd`, marker ExclX and immediate looper/solver/split docfiles,
and `src/simp/src/notes.md`. No ordinary example script needed migration.

## Normal regression coverage and migration review

`src/simp/src/selftest.sml` retains genuine legacy expectations: ordinary
rule/dproc deletion, same-named looper preservation, unmatched silence,
strict dotted parsing, bare kernel-spelling no-op, and strict replay after
Context.restore. Branch-only extended solver/looper/split/case, relaxed
rule-name, ambiguity, unloaded-theory and bounded-argument expectations
now use ExclX without weakening their meaningful assertions. The early
kernel-spelling table row was migrated to a separate ExclX convtest, not
removed. Temporary TASK_06 rejection tests were replaced by routing tests.

Additional assertions cover mixed directive order, masking pending
extended rule deletions, no literal fallback to ambiguous strategies,
resolved bare ExclX replay after Context.restore, explicit split namespace,
missing targets in all namespaces and bare ExclX, and bound/requirement
precedence. The R7 tests pin missing-label/FRAG error winners and proof
counts for saved tactic construction/inspection across bare, Req0, ReqD,
Once, malformed bound and Req0/Once ExclX. They forbid early decoding or
resolution; original R7 callback/Context assertions remain unchanged.

All ten TASK_02 fixtures join normal `HOLSELFTESTLEVEL` coverage through
`exclusion-contracts` in `src/simp/src/Holmakefile`, using the shared
`LegacyFailures.prefix_checks` and new `RunExclusionContracts.sml` launcher.
They retain every real-conversion/callback setup check, complete theorem
check and warning assertion. Each now additionally compares direct `-*`
deletion and verifies no conversion callback. Standalone paired launchers
still initialize their own theory, run the same checks and fail on any
unexpected exception/warning; there are no xfails. Support Holmakefile,
compatibility README and this handoff describe the native target.

## Validation and provenance

Final receipts/source hashes: [`results/task07/validation.json`](results/task07/validation.json).
Unique routing assertions: `results/task07/exclusion-routing.log`.
Full paired manifest and raw logs: `results/task07/differential-final/`.
Commands from repository root, all final exits **0**:

```sh
bin/Holmake --no-project --no-cache -j1 -C src/marker \
  --holstate="$PWD/bin/hol.state0" HOLSELFTESTLEVEL=1
bin/Holmake --no-project --no-cache -j1 -C src/simp/src \
  --holstate="$PWD/bin/hol.state0" HOLSELFTESTLEVEL=1
bin/build -t --seq=tools/sequences/upto-parallel
python3 src/simp/compatibility/run.py --branch <source-snapshot> \
  --output src/simp/compatibility/results/task07/differential-final
tools/h4pedant/h4pedant src/marker src/simp/src \
  src/simp/compatibility/probes
(cd src/simp/compatibility && sha256sum -c inputs/SHA256SUMS)
git diff --check
```

- Native marker **70 OK**, simplifier **460 OK** (all five later-datatype
  availability-guarded checks included), traversal **47 OK**, prefix
  contracts **134 OK**. All ten prefix cases are silent; their warning
  counters are zero and no raw load warning occurs. Existing ordinary
  SF-registration warnings and the traversal fixture's intentional warning
  remain visible in their own suites; warnings were not disabled.
- Routine build: **exit 0**, `Hol built successfully.` A first invocation
  was externally terminated at the command's 200-second time limit during
  downstream theory rebuilding, not counted as a pass. A longer rerun and
  a final post-comment-edit rerun both completed. This is the incremental
  upto-parallel sanity gate, not the full `-F` or help-documentation gate.
- Paired reference `cccaa27d7099cbadc886983020cbe745db7793f3`; implementation
  `<source-snapshot>` is the validation-only git commit recorded in the
  manifest/receipt. It was made with a temporary index and `commit-tree`
  without moving HEAD or touching the caller's index, so uncommitted source
  edits were not accidentally omitted by the commit-only harness. Its
  staged library bytes match the landing sources; their hashes are in the
  manifest. Reproduce after landing with `--branch <landing-commit>`.
- Both library builds, all **28** suite executable builds and all **28**
  runs exited 0. Each prefix probe has **17 OK**, with **41 ordered OBS**
  equal across lanes. Control **4 OK**, reducer **7 OK**, traversal **47
  OK** with **273 equal ordered OBS**, unchanged develop suite **73 OK**.
  Its empty OBS comparison is null, not a universal trace-equivalence
  claim. Frozen input SHA-256 checks and style checks pass.

The paired harness remains **mixed-source**, sharing host kernel/heap,
generated theories and dependencies, not two independent repository
builds. No fresh-load registration repair, expanded TASK_09 matrix, full
build or whole-plan equivalence is claimed by this task.

Development-only failures were fixture issues: a nonexistent Thm.eq_thm
helper, an initially omitted signature alias, missing runtac application,
one overlooked overloaded table row, and ReqD tested on a closed goal
(where zero subgoals satisfy it). Each was corrected and rerun; no failed
oracle was discarded or counted as a pass. Redundant intermediate paired
results, temporary indexes and scratch logs were removed after extracting
final compact evidence. Runner-owned copied trees/products were removed
by the harness. Unrelated/caller-owned artifacts were left intact.

## TASK_08 handoff: history representations and remaining replay cases

TASK_07 acceptance is satisfied, with no remaining TASK_07 blocker.

- `rule_exclusion = {original, pattern, strict}` is stored in
  `DELETE_EVENT of rule_exclusion list`. `original` also names dprocs;
  do not substitute the parsed rewrite pattern for it. History is newest
  first; `build_from_history_with` reverses it, calls `replay_exclusion`
  per element, and applies `delete_exclusions` in batch order. The new
  contiguous batching flushes before non-rule events.
- Ordinary looper/solver removal is replayable through `STRATEGY_EVENT`
  (`DEL_LOOPER_EVENT`, `REMOVE_SOLVER_EVENT`). `strategy_op` both applies
  and records it. Existing `SET_EXCL_LOOPERS_EVENT` and
  `SET_STRATEGY_EVENT` can carry exclusion state, but extended split/case
  application currently does not record the needed set update.
- Specifically, `exclude_split_display` records deletion of each local
  split looper, then mutates `strategy.excl_loopers` using `map_strategy`.
  `ExcludeCase` only mutates that set. Persistent split/case suppression
  can therefore disappear on unrelated fragment removal/rebuild. This is
  the explicitly assigned TASK_08 replay-state repair, not a repaired
  TASK_07 contract. Decide whether to reuse a set event or add a narrow
  incremental event without disturbing later additions/clear behavior.
- Extend focused tests around `mixed literal/extended exclusions resolve
  in order`, `adjacent extended exclusions see pending rule deletions`,
  unmatched filter-removal/exclusion replay, strict Excl/`-*` Context
  restore errors, relaxed `rule:` and resolved bare ExclX Context restore,
  and direct named split/TypeBase case suppression. TASK_08 must exercise
  split/case replay after unrelated removal and restoration, repeated and
  interleaved deletions/additions, preserving existing bounded controls
  and callback staging. TASK_09 owns the larger parser/namespace matrix.

Next lowest unblocked task: TASK_08 (TASK_10 remains independently unblocked).
