# TASK_13: final API inventory and migration sweep

Entry revision: `fa2099c07` (TASK_12), existing `simplifier` branch.
Landing identifier: `[TASK_13] Complete API documentation and migration sweep`
(commit subject). Caller-owned TASK_12 progress corrections are preserved.

## Final API inventory (handoff to TASK_14 through TASK_17)

**Legacy clients require no migration and no extension opt-in.** These
contracts, rather than universal equivalence, are the documented boundary:

- `simpLib.traversedata_for_ss : simpset -> Traverse.traverse_data` is the
  unconditional legacy projection. Its native rewriter is `REDUCER`;
  supplied dproc constructors are unchanged. It carries equality, traversal
  rules and limit, not simpset-specific traversal configuration.
- `legacy_traversedata_for_ss` is the optional, pure dispatch helper, not
  a replacement legacy API. It rejects configured conversion settings and
  non-`REDUCER` dprocs; eligible results use the same default builder.
- Branch clients needing configured extraction use
  `xtraversedata_for_ss : simpset -> Traverse.xtraverse_data`, the pair
  `(traverse_data, traverse_config)` with a native `CONFIG_REDUCER`.
  Normally pass the complete pair to `Traverse.XTRAVERSE`. `#1` extracts
  configured reducer data alone; it discards the configuration.
- Extraction invokes no collectors, recompiles no installed rewrites and
  resets no quotas. Both projections share installed bounded controls.
  Raw `TRAVERSE data facts` initializes private contexts at construction;
  `XTRAVERSE pair facts` refreshes them per application, even with default
  settings. Total SIMP/congruence wrappers delay raw construction until
  application. See `TRAVERSAL_LIFETIMES.md` for factory staging, live
  defaults, exceptions and shared-control tests; opt-in is not a promise
  of identical callback schedules.
- `simpLib.Excl` / `markerLib.Excl` remain strict literal deletion, as with
  `-*`. No namespace prefix or strategy fallback exists for any old string.
  The dots-only parser retains develop's ancestry/suffix quirks; `$` is
  literal, not theory qualification. Dprocs match exact strings. Missing
  names are silent but retained in history; replay reparses strict names
  in the current theory context.
- `simpLib.ExclX : string -> thm` aliases `markerLib.ExclX`, backed by the
  distinct `marker$ExcludeX`. `destExclX : thm -> string option` and
  `DExclX of string` recognize it separately. Construction stores a variable
  name, not a HOL string or a prefix hidden in an `Excl` payload.
  Neither `marker$ExcludeX` nor `marker$Split` installs a new unqualified
  parser mapping; use the ML APIs or qualified constants.
- Only `ExclX` resolves `rule:`, `looper:`, `solver:`, `split:` and `case:`.
  `rule:` accepts relaxed `Thy.Name` / `Thy$Name`; bare names first use the
  strict parser and rule/dproc priority, then strategy fallback. Missing
  targets and cross-kind ambiguities fail when processed, not constructed.
  Solvers are removed from both lists. Bounded wrappers do not count
  exclusions; requirement-wrapper precedence is unchanged.
- Extended rule history keeps resolved patterns, including for bare names.
  Ordinary rule/looper/solver deletions are point-in-history operations;
  later additions can reinstall them. Split/case suppression retains the
  resolved displays through fragment replay and Context restoration and
  suppresses later matching local additions. Replaying suppression is
  idempotent, but a newly processed exclusion still needs a target: an
  already removed local-only split does not match, whereas a retained
  ambient persistent/TypeBase target can. See `EXCLUSION_MATRIX.md`.
- Ordinary `simpLib`/`splitLib` loading does not claim persistent `split`
  ownership. `split_thms ()` and `named_split_thms ()` return `[]` before
  owned initialization or under foreign ownership; queries do not initialize
  or adopt a foreign set. Pure conversions, local `Split`/`add_split`, and
  TypeBase-driven `split_ss` need no opt-in.
- `splitLib.enable_split_attribute : unit -> unit` explicitly claims both
  attribute and exporter, preflighting public-name/listener conflicts.
  Repeated owned initialization is a no-op. Ownership/data follow Context;
  foreign replacements invalidate ownership, and pinned contexts reject
  writes. After restoring before initialization, call the API again:
  cached `splitPersistLib` loading need not rerun its initializer.
- Persistent producers load `splitPersistLib` in `Libs` and record
  `Theory.add_ML_dependency "splitPersistLib"` on the **earliest**
  split-bearing theory, before `[split]`. A descendant's own dependency
  is too late for loading parents. Alternatively explicitly initialize in
  a loader prelude before importing the entire graph. Ordinary simplifier
  imports are insufficient. This is serialized theory setup, not concurrent
  initialization or arbitrary late/current-segment replay.
- `splitLib.exclude_split : string -> unit` persistently retracts
  `[Thy.]Name`, resolving in the writing theory and exporting a fixed
  `Thy$Name` REMOVE key. Missing names are harmless and the DB theorem
  survives. It requires owned, unpinned registration. Local `del_split`
  and per-call `ExclX "split:..."` do not retract persistent data.
  See `SPLIT_PERSISTENCE.md`, `SPLIT_LIFECYCLE.md` and `LOAD_AUDIT.md`.

## Search/disposition record

`results/task13/search.json` records the exact whole-file regex queries,
per-file matched line numbers (counts for historical files), source hashes
and dispositions. Enumeration
uses `git ls-files -z`, not ignored build trees or caches. Searches cover
all tracked paths, including examples, manuals, release notes and editor
fixtures; multiline/combined attribute lists are included. Broad `Excl`
searches include nonliteral arguments (`map Excl`, `Excl name`), not just
quoted namespace strings. Additional review covered split-store/registration
references and constructor assertions near each extraction call. The record
covers **277 files** including historical evidence; excluding archival,
staged-handoff and task-specification categories, traversal/exclusion/
persistence queries cover **10 / 105 / 24** active files respectively.
The supplementary persistent-claim query covers **20** active files.

All relevant hits have these dispositions (the JSON expands path groups):

| Group | Disposition |
| --- | --- |
| `src/simp/src/congLib.sml` | Keep optional legacy / explicit extended dispatch. |
| `src/simp/src/simpLib.*`, `splitLib.*`, `splitPersistLib.sml` | Keep implementations; align signature comments. |
| `src/marker/markerLib.*`, marker selftest | Keep distinct constructors and literal round trips. |
| Simplifier selftest | Keep literal collision/strict parser tests; extended expectations already use explicit APIs. |
| `probes/support/{LegacyFailures,TraversalContracts,ExclusionHistory,ExclusionParsing}.sml` and legacy launchers | Keep unchanged legacy contracts, including literal prefixes and expected errors. |
| `probes/split-{registration,persistence}/`, fresh-load fixtures | Keep explicit producer ordering and intentional unowned/foreign-owner scenarios. |
| All other `src/` and `examples/` Excl clients | Keep literal theorem/conversion/dproc deletions; no strategy fallback dependence. |
| `src/refute/Canon.sml` | Unrelated local function `split_thms`, not the persistent set. |
| `help/Docfiles/` | Finalized APIs; qualify new ExclX examples and add lifetime/replay details. |
| Manual simplifier chapter and cheatsheet | Correct legacy theorem/conversion examples; no opt-in needed. |
| Editor mode test scripts / expected strings | Literal `Excl "lift_disj_eq"`, not extension clients. |
| Release notes / context-passing discussion | Historical legacy examples and staging discussion, not new API promises. |
| Compatibility handoffs, inputs and results | Versioned investigation/evidence; retain historical red probes and superseded stage descriptions. |
| `.agent-files/tasks/` | Task specifications/progress, not clients; add final handoff pointer. |

In particular, `Excl "NUM_ARITH_DP"`, `REAL_ARITH_DP`, `BETA_CONV`,
`NORMEQ_CONV`, `SET_SPEC_CONV`, normalization names and qualified
`list.APPEND_ASSOC` remain literal. The ten prefixed legacy probes and
marker round trips must **not** be mechanically converted to `ExclX`.
There are no production `[split]` producers outside the explicit
persistence fixtures, nor remaining configured extraction assumptions.

Supplementary search of ignored top-level `.agent-files/*.md` reviewed
81 lines, including false positives for “Exclusive”. These are old plans,
performance/review records, not exported docs or active clients. In
particular `R3.md`, `SCHEDULE.md`, `REVIEW.md` and `TIMING-SCRATCH.md` describe
superseded overloaded Excl/fallback behavior. Their historical statements,
old copied-source trees, and archived inputs/results are intentional
non-migration exceptions; do not rewrite evidence as if it used current
APIs. `PLAN_compatibility.md` and task specifications describe the repairs.
No known active client still relies on the superseded extension contracts.

## Changes and checks

Changed public docs: `markerLib.ExclX`, `simpLib.{Excl,ExclX,Split,add_looper,
add_split,split_ss,traversedata_for_ss,xtraversedata_for_ss}` and
`splitLib.enable_split_attribute` under `help/Docfiles/`.
Also changed `src/simp/src/{notes.md,simpLib.sig,splitLib.sig}`, compatibility
README, task index/progress, this handoff and compact task13 evidence.
No executable library or caller behavior changed; no splitter algorithm
redesign or new-only issue was folded into this sweep.

`results/task13/validation.json` records commands, statuses, source/tool/heap
hashes and log receipts. Final checks all exit **0**:

- Routine `bin/build -t --seq=tools/sequences/upto-parallel`: ends
  `Hol built successfully.` Signature edits were present for this build.
- Early-heap Holmake focused targets: `selftest.exe`, `split-persistence`,
  `split-registration`, `fresh-load-regressions`, `traversal-contracts`,
  `exclusion-contracts`; standalone normal simplifier/marker selftests:
  **630 / 72 OK**. Focused contracts: registration **101**, traversal **47**,
  exclusion **929 OK**; all six fresh-load and eight persistence/heap
  scenarios pass, including the deliberate foreign-import rejections.
- Rebuild `help/src-sml/process_docfiles` against the updated `hol.state`.
  Run it on isolated temporary copies of all **15** related docfiles,
  evaluating examples and rendering **15 text + 15 HTML** files. Also run
  each entry in its own fresh process to exclude inter-entry binding
  dependencies. Evaluated source/transcripts are retained in
  `doc-transcripts.md.gz`; rendered/copy trees were deleted after checking.
- `tools/h4pedant/h4pedant src/simp/src src/marker`;
  explicit tab/trailing-whitespace checks on every changed text file;
  frozen-input `sha256sum -c inputs/SHA256SUMS`; `git diff --check`.

The first docfile pass exposed preexisting unqualified `ExclX` examples:
`bossLib` does not re-export it. All four executable example sites now use
`simpLib.ExclX`; no ambient `open simpLib` or new bossLib alias was added.
Final batch and independent doc passes succeed. The documented expected
`UNCHANGED` transcript in `add_unsafe_solver` remains intentional.

Pandoc was absent from PATH; the initial mirror-only run was not counted
as a rendering check. A task-owned temporary Pandoc 3.6.4 release extraction
was used for the final full render and independent checks, then removed.
The manifest records its URL and executable hash. No system installation,
copied build tree, saved heap, new cache or temporary download remains.
Normal checkout build products and unrelated/caller-owned artifacts stay.

## Gate boundary

No TASK_13 acceptance blocker remains. TASK_14/TASK_15 are unblocked, not
claimed complete. TASK_14 must rerun the paired legacy matrix; TASK_15 owns
representative downstream validation; TASK_16 owns `bin/build -t -F`;
TASK_17 owns final sign-off and cleanup. Those are separate acceptance gates,
not deferred TASK_13 work. Existing paired evidence is mixed-source (shared
host heap/dependencies/generated theories), not independent clean builds.
Finite tests and this static sweep do not prove universal observational
or callback equivalence. All predecessor limitations remain visible.
