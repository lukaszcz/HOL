# TASK_12: split lifecycle and load audit

Landing identifier: `[TASK_12] Validate split lifecycle and audit loading`
(commit subject). All bounded TASK_12 acceptance criteria are satisfied;
no lifecycle or registration-audit blocker remains. TASK_13 is unblocked.
This is not the paired-differential or full-build compatibility sign-off.

The explicit registration/syntax inventory, ownership decisions and bounded
repair are in [LOAD_AUDIT.md](LOAD_AUDIT.md). Prior storage and exported
initialization contracts remain in [SPLIT_REGISTRATION.md](SPLIT_REGISTRATION.md)
and [SPLIT_PERSISTENCE.md](SPLIT_PERSISTENCE.md).

## Phase 4 lifecycle matrix

All rows were rerun, not inferred from TASK_10/TASK_11 results. Commands,
source/tool hashes, assertion counts and compressed logs are recorded in
`results/task12/validation.json`. Every final command exits **0**.

| Scenario | Maintained fixture / verified observation |
| --- | --- |
| Custom attribute first, then simpLib | `fresh-load/attribute-first`: exact local/stored handler record survives loading, callback arguments/order survive, no replacement warnings. |
| Custom theorem set first, then simpLib | `fresh-load/set-first`: exact exporter and attribute records, singleton named ADD/theorem/hypotheses and callbacks survive, no warnings. |
| simpLib first, then custom owner | `fresh-load/{attribute-after,set-after}`: both registries remain free after ordinary simplification; custom registration succeeds silently. |
| Plain simpLib load | `fresh-load/control`: ordinary theorem/hypothesis control passes. Each launcher asserts no preloaded/bound simpLib, splitLib or splitPersistLib and both registries free. |
| Foreign syntax first | New `fresh-load/syntax-first`: unrelated Split/ExcludeX overloads survive ordinary loading; qualified marker constants still work, neither split registry is claimed, no warnings. |
| Explicit opt-in success | `split-registration`: pure queries initially empty; enable claims both names; stored `[split]` handler records an ADD and queries return the saved theorem. |
| Repeated opt-in | `split-registration`: whole-Context pointer unchanged; both handler identities, named/query data and delta history unchanged, silent. Also tested after fresh import and heap reload. |
| Foreign-owner rejection before mutation | `split-registration`: attribute-only, exporter/attribute, replaced exporter only, reserved word, ordinary/cyclic abbreviations and foreign listener conflicts; exact error identity, whole-Context nonmutation, no adoption or partial registry. |
| Restore before initialization | `split-registration`: free registries and empty queries; explicit reinitialization works; original and new theory-data witnesses remain distinct. |
| Restore after initialization | `split-registration`: original handle, named theorem/data, persistent removal handle and actual TheoryLoaded replay recover. |
| Restore foreign ownership | `split-registration`: foreign attribute, exporter and ancestry exporter snapshots; empty library queries, exact foreign records/data, live callbacks and replay, explicit conflicts stay silent and nonmutating. |
| Pinned Context | `split-registration`: snapshot-selected queries; owned enable is a no-op; unowned enable/removal reject without modifying live Context. |
| Local Split before opt-in | `split-registration`: SPLIT_CONV and local Split tactic change the goal with no public namespace claim. |
| TypeBase before opt-in | `split-registration`: split_ss changes the goal independently of persistent registration. |
| Extended exclusions before opt-in | New `split-registration` assertions: case:bool disables TypeBase, split:<local-name> disables a local rule without disabling TypeBase, unmatched split:absent raises the precise process_tags error without Context mutation. Registries and persistent queries stay empty. |
| Theory export/import | `split-persistence/{parent,child,descendant}`: each is a separate clean process importing actual exported theories, with no splitter, opt-in module, simplifier or fixture theory preloaded. |
| Ancestor additions/removals | Parent writes two retained aliases and removes a transient; child removes the parent's drop, adds its own drop and removes its own ephemeral; descendant keeps exactly splitChild$drop and splitParent$keep. Keys are resolved in the writing theory, removed DB theorems remain available, imported theorem pointers equal DB entries. |
| Already-owned import | `split-persistence/owned`: exported initializer preserves both exact handler records and the same replay/query result, silently. |
| Foreign-owner import | `split-persistence/{foreign-attribute,foreign-set}`: fails at enable_split_attribute in the explicit dependency, before parent decoding/replay; foreign records/data/callbacks survive and no replacement warnings occur. Expected loader error diagnostics are retained. |
| Saved-heap reload | New `split-persistence/{heap-save,heap-reload}`: separate executable processes save and actually load a Poly/ML state; details below. |

The native-only `identity-{before,after}.ML` helpers inspect the newly
exposed handler accessors. Their environment opt-in is supplied by native
Holmake targets, not by `fresh_load.py`; the shared legacy launcher still
compiles without statically depending on branch-only inspection APIs.
The original five differential scenarios retain their callback/data checks.

## Actual heap boundary

`heap-save` dynamically imports the descendant using TASK_11's exported
`splitPersistLib` dependency, runs all ordinary import assertions, then
`heapSave.ML` saves three Context snapshots: before initialization, owned
with descendant rules, and foreign-attribute-owned. It returns to owned
state and calls `PolyML.SaveState.saveState`.

A **new** `selftest.exe` process first checks its clean initial namespace,
then calls `PolyML.SaveState.loadState` and runs `heapVerify.ML` in the
restored global namespace. It checks:

- exact restored attribute/exporter record pointers and DB theorem pointers;
- exact descendant names and idempotent opt-in;
- a live persistent removal handle;
- rewind before initialization: free registries and empty queries;
- cached `Meta.load "splitPersistLib"` does not rerun its initializer;
  calling the explicit API does initialize the rewound Context;
- restored foreign ownership rejects enable before any Context mutation,
  returns no library rules, preserves its record and callable handler;
- restoring the owned snapshot recovers the live exporter, and actual
  TheoryLoaded routing replays ADD/REMOVE without stale-witness errors;
- no replacement warnings anywhere in the reload lifecycle.

This is heap serialization, not another dynamic import in the saving
process. The fixture deletes any old heap before running and traps exit
to remove the generated heap even when a scenario fails. `EXTRA_CLEANS`
also covers an interrupted run. No binary heap is retained as evidence.

## Registration/syntax repair

The audit explicitly disposes of persistent split ownership and indirect
slots/data/listeners, local fragments/caches, shared ThyDataSexp dispatch,
inspection APIs, Split/ExcludeX constants and parser mappings, OpenTheory
calls, other new module state, existing registrations and test-only setup.

The only production repair is in `src/marker/markerScript.sml`: remove the
new marker constant's unqualified ExcludeX mapping, exactly as for Split.
It does not erase unrelated same-spelled overloads. Marker selftests now
check ExcludeX-as-variable and qualified access; the fresh syntax scenario
checks foreign overload preservation through real ordinary loading.
All constructor/recognizer and extended exclusion tests remain passing.
The markerLib.ExclX docfile records qualified syntax availability.

No registration API/storage format or dependency-order decision changed:
ordinary simpLib/splitLib must not import splitPersistLib. Earliest
split-bearing theories must load/export that explicit dependency before
split data replay. After restoring a pre-init Context, call the explicit
API rather than assuming a cached module body executes again.

## Commands and results

From the repository root, serially (configured dependencies required):

```sh
# Clean and rebuild actual exported theories plus eight fresh processes:
bin/Holmake --no-project --no-cache --no_prereqs -j1 \
  --holstate="$PWD/bin/hol.state0" \
  -C src/simp/compatibility/probes/split-persistence cleanAll
bin/Holmake --no-project --no-cache -j1 \
  --holstate="$PWD/bin/hol.state0" \
  -C src/simp/compatibility/probes/split-persistence check

HOLSELFTESTLEVEL=1 bin/Holmake --no-project --no-cache --no_prereqs -j1 \
  --holstate="$PWD/bin/hol.state0" -C src/simp/src \
  split-persistence split-registration fresh-load-regressions \
  traversal-contracts exclusion-contracts
(cd src/simp/src && ./selftest.exe)
(cd src/marker && ./selftest.exe)
bin/build -t --seq=tools/sequences/upto-parallel

tools/h4pedant/h4pedant src/marker src/simp/src \
  src/simp/compatibility/probes/fresh-load \
  src/simp/compatibility/probes/split-persistence \
  src/simp/compatibility/probes/split-registration
(cd src/simp/compatibility && sha256sum -c inputs/SHA256SUMS)
git diff --check
```

| Final check | Outcome | Log (`results/task12/`, append `.gz`) |
| --- | --- | --- |
| Clean theory rebuild; parent / child / descendant imports | 20 / 21 / 21 OK | `clean-rebuild.log` |
| Already-owned / foreign attribute / foreign exporter | 23 / 15 / 16 OK | `clean-rebuild.log` |
| Heap save / separate reload | 22 / 23 OK | `clean-rebuild.log` |
| Native fresh-load scenarios (six) | all pass; 11 / 20 / 23 / 17 / 19 / 17 OK | `focused-final.log` |
| Registration / traversal / exclusion contracts | 101 / 47 / 929 OK | `focused-final.log` |
| Normal simplifier / marker selftests | 630 / 72 OK | `native-{simplifier,marker}.log` |
| Routine sanity build, final source overlay | `Hol built successfully.` | `sanity-final.log` |
| Pedant / preserved-input hashes / diff whitespace | pass | `pedant.log` / `inputs.log` / manifest |

All six fresh-load scenarios, registration and persistence (including both
heap processes) are in normal `HOLSELFTESTLEVEL` coverage. These were
formerly red load-order targets, not xfails or manually tolerated errors.
The final sanity build also passed the normal marker/simplifier gates.
Parent clean rules now cover the dynamic fixtures' executables and `.hol/`
products (including generated theories), plus the temporary saved heap;
fixture-local cleanAll and a real clean rebuild were exercised.

Early fixture development incorrectly expected an unmatched extended
split exclusion to succeed, then checked the rejection before tactic
application. Those tests failed as they should; the final tests separately
assert matched success and exact unmatched application-time failure.
The first routine sanity invocation was therefore red, not certified as
passing. Both final focused and routine runs use the corrected sources.
Superseded trial logs were removed; no production exclusion semantics were
changed to accommodate the tests.

## Handoff, provenance and cleanup

Changed files: marker script/selftest and ExclX docfile; native simplifier
Holmake wiring; fresh-load launcher/native identity/syntax helpers;
registration pre-opt-in exclusion assertions; persistence launcher,
heap helpers and cleanup; audit/lifecycle docs, README, task index/progress
and compact `results/task12/` evidence.

The manifest pins base `c8b193b98`, tested source overlay/tool/heap hashes,
actual generated theory ordering, commands/statuses and log hashes. Tests
ran against native configured worktree products, not independent clean
repository builds. Static source inventory is against pinned develop with
merge-base attribution explained in LOAD_AUDIT.md. No new paired comparison,
full `-F` gate, universal observational equivalence or concurrent
initialization guarantee is claimed by this bounded lifecycle gate.

TASK_13/TASK_17 receive the complete matrix and explicit audit dispositions.
No open bounded blocker remains. Task-owned fixture caches, executables and
saved heap are removed after their final required use; compact unique logs
and ordering evidence remain. Unrelated/caller-owned artifacts are kept.
