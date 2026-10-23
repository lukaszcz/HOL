# TASK25 — isolated clasimp consumer migration

Landing identifier: **TASK25-isolated-consumer-v1** (containing commit).
Simplifier source: `4a0ad8e9160dd911393385d748b3535fc5ce65ba`.
Consumer base: `442009a1f7f04366573dc2b649d31650ea7b113b`.
Linux/aarch64, Poly/ML 5.9.2, one GC thread per consumer launcher.

**All bounded TASK25 acceptance criteria pass.** The isolated migrated
consumer compiles and the complete normal-level consumer closure executes
successfully. There is no missing required input or unchecked migration left.
This is not final release/performance or optional whole-corpus acceptance.

## Durable patch and provenance

- Patch: [evidence/task25/consumer.patch](evidence/task25/consumer.patch),
  93 files, 269,217 bytes; SHA256
  `6a0a8f54dcb1af06a1b824f56453619195a11d321f97851bcc7b61149166ad1a`.
- [manifest.json](evidence/task25/manifest.json): all **39** driver commands
  exit 0, exact options/runtime tools, source and product hashes, proof-test
  observations, module paths and canonical versus expanded inputs.
- Source inventories seal 10,805 core inputs and 1,929 migrated consumer
  inputs; 3,082 source-loading dependency entries and 350 executed consumer
  products are recorded. The independent path fixture emits actual
  `Meta.fileDirMap`/`findMod` observations, including both simplifier engines,
  tracked recipes/provider and clasimp. `.uo` generation alone is never a pass.
- Complete compact logs are in `logs.tar.gz`; `log-archive.json` verifies each
  original log's hash. Extract into a disposable directory to inspect them.
  `evidence-seal.json` binds receipts, patch, logs and maintained driver sources.
- [migration/TASK25.md](migration/TASK25.md) records construction/type/API
  decisions, the full transitive consumer closure and reproduction commands.

The old recorded `/home/lukasz/dev/HOL/worktrees/isabelle-tactics` path no
longer exists on this host. The same pinned worktree is now at
`/home/lukasz/work/HOL/worktrees/isabelle-tactics`. It was inspected read-only;
all migration and builds used task-owned archives/snapshots.

## Changes and contracts

The patch selects `simpExtLib`/`TraverseExt` types before source-sensitive
construction, propagates them through clasimp/aesop/public caches, supplies
explicit ORDER/LINARITH lifted fragments, and migrates markers, tactics,
standard recipes, benchmark transport, iff helpers, docs and build edges.
Ordinary seed collections, ordinary fragment recipes and independent ordinary
comparison assertions remain ordinary. Generic invocation polymorphism stays
polymorphic. No production simplifier, generic marker or postkernel source
changes are made in this task.

`trackedAutoDefaults` owns an explicitly prepared typed provider, local
updates/windows and eager derived defaults. Getters do not rebuild, promote
ordinary sets, reset controls or discover metadata retrospectively. Persistent
iff/bottom-up inputs are captured at installation in a context-owned declaration
program; bottom-up tables and installation state rewind too. Post-boss fresh
preparation uses those **inputs**, never `ssfrags_of` reconstruction. Its new
controls are deliberate and documented: prepare before binding/consumption,
not as a transparent import of arbitrary live ordinary state.

The executed original assertions exposed and fixed these migration issues:

- A bounded ordinary rewrite must not be classified as a directive before
  recursively checking its payload; otherwise it bypasses bundle sharing.
- Bounded-existential congruences require the explicit threaded opener.
- Optional numeric recipes must not eagerly change pre-boss overloads.
- Post-boss defaults install ancestral batches once, with captured consumer
  iff inputs last; the unchanged INJ negative/positive tests now terminate.
- Literal exclusions need dotted names, not kernel `$` spelling. Explicit
  synthetic namespaces use `ExclX`; claset guards/names remain unchanged.
- Split persistence explicitly loads its owner. A nonexistent LIST_REL cons
  citation uses the same general constructor from `LIST_REL_rules` via genuine
  kernel inference. No tactic strengthening or corpus assertion relaxation.

New regressions additionally check declaration capture versus compiled-state
impostors, fresh versus exhausted quotas, inert retrieval, retractions,
Context rewind, bottom-up restoration and both benchmark exclusion routes.
All original source, prepared-bundle, contextual, bounded and child-first
proof assertions remain active.

## Exact prerequisites, not hidden compatibility claims

The private core uses the exact consumer commit's `src/list/src/listScript.sml`
(SHA256 `20c788b2b7819d816ef4030b1f61252da07060870d85be82ceb869527f5fee68`)
for its required takeWhile declarations. Its theory closure/heap were rebuilt.
The simplifier modules themselves are exactly the pinned simplifier sources.
No list prerequisite is installed into this checkout or the caller's products.

Four numeric-attribute Scripts are pre-expanded with a standalone quote-filter:
configured core ingredients, with only `HOLSourceParser.sml` from the exact
consumer commit. Canonical and expanded hashes are both sealed. Generated SML
is confined to disposable build inputs; actual theorem proofs and assertions
execute through Holmake. Neither production parser nor canonical patch source
is rewritten to accommodate the test harness.

## Fresh final validation

The source-verified final run used:

```sh
python3 -B src/simp/tests/compatibility/run_task25_consumer.py \
  --consumer-patch /tmp/task25-final-consumer.patch \
  --output /tmp/task25-final3 \
  --existing-core /tmp/task25-core \
  --existing-consumer /tmp/task25-isolated
```

**Exit 0**, including actual `HOLSELFTESTLEVEL=1` launchers after each `all`
build, with `--no-project --no-cache --rebuild=mtime -j1`. All 67 consumer
Script inputs were forced through dependency rebuilding/execution, including
16 clasimp theory tests and six examples. The reused private core had already
been reconfigured and its prerequisite closure rebuilt; this is explicitly
not an independent clean-build claim.

| Actual standalone normal-level suite | Passing checks |
| --- | ---: |
| rules / order / linarith | 147 / 25 / 149 |
| classical / blast | 250 / 208 |
| clasimp / aesop | 188 / 148 |
| linarith instances / seeds / benchmarks | 52 / 74 / 166 |
| **Total (not counting repeated integrated executions)** | **1,407** |

All rules, linarith, clasimp, aesop and seed theory-test directories execute
successfully, including phony fresh reload/state-replay checks. Exact
benchmark normal-level solved sets and A6 hashes pass. Tests validate actual
tactic justifications/hypotheses, not merely printed normal forms.

Additional checks, all exit 0:

- Private core configuration, bootstrap and
  `bin/build -t --seq=tools/sequences/upto-parallel`.
- The same routine sanity build in the main checkout, using the archived
  configured-path wrapper. No external consumer products are in that build.
- Eight driver controls: nonzero exit, zero-exit static failure, missing
  observation, source drift/missing source, invalid launcher, positive output
  and legitimate negative-test labels. Fresh archive/patch prepare-only mode
  also succeeds and removes its scratch.
- h4pedant `--nolinelen --unicodeok` on the canonical migrated consumer;
  whitespace checks and `git diff --check`.
- All durable file/source/log seals rechecked after copying the evidence.

Optional whole-corpus level-2 report/battery acceptance is not claimed. An
exploratory pre-final run exceeded 1,800 seconds; no timeout is counted as a
pass. The bounded gate here is the complete normal level plus all required
source/bounded/child-first and persistence contracts. Whole-distribution clean
builds, full regressions, final performance gates and other platforms remain
the plan's separately defined later tasks, not deferred TASK25 requirements.

## Caller preservation, cleanup and handoff

`caller-state.json` records unchanged HEAD, tracked/index diffs, root status and
nested caller-owned `.agent-files` status. Root porcelain SHA256 remains
`4086a8c20270099fc971b5a0b9142963153141193cc00d45565f66697a84df71`;
nested state matches its session-start hash. Caller ignored products were
never used or writable in any task build. Read-only bindings protect them,
including during private dependency rebuilding.

Task-owned copied cores/checkouts, heaps, parser binaries, expanded sources,
launchers, caches and superseded logs are removed after evidence sealing;
`cleanup.json` records this. Only the unique patch and compact source-tied
receipts/logs remain. Ordinary main-checkout build products and unrelated
caller/nested state are preserved.

**TASK26 is ready.** No bounded TASK25 blocker remains. Subsequent affected
simplifier/API/build changes invalidate this source-specific consumer result
and require a new run; this handoff does not pre-approve later revisions.
