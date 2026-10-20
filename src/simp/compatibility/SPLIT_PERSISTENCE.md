# TASK_11: opt-in split persistence and theory clients

Landing identifier: `[TASK_11] Integrate explicit split persistence`
(commit subject). All TASK_11 acceptance criteria are satisfied; no blocker
remains. TASK_12 is unblocked. This is the persistence integration gate,
not the full lifecycle/load audit.

## Supported API and initialization ordering

- `splitLib.enable_split_attribute : unit -> unit` retains TASK_10's
  context-local ownership, conflict and idempotence contract. Ordinary
  `simpLib`/`splitLib`, pure queries, local splitting and TypeBase splitting
  have no dependency on the new opt-in module.
- New `splitPersistLib.sml` is an explicitly loaded, side-effect-only
  structure calling that API. No reverse dependency on `simpLib` exists.
- An exporting theory must both load the module for its script and record
  the import-time dependency, **before** its first `[split]` declaration:

  ```sml
  Theory mySplits[bare]
  Libs
    HolKernel Parse boolLib splitLib splitPersistLib

  val _ = Theory.add_ML_dependency "splitPersistLib"
  ```

  Put the dependency on the earliest split-bearing theory. A child's
  dependency is too late for its already-loading parents. Descendants need
  only their normal ancestor dependencies. The fixture's Holmake includes
  resolve the actual local simplifier modules, not an exporting heap.
- Generated `splitParentTheory.sml` opens `boolTheory splitPersistLib`
  before `TheoryReader.load_thydata`, and calls `Theory.load_complete`
  afterwards. The exported `.uo` recipe also lists the module dependency.
  Thus the decoder/ancestry listeners exist before loading split data;
  theorems enter DB before raw ADDs are cooked at `TheoryLoaded` replay.
  No storage/serialization format or replay listener order was changed.
- New `splitLib.exclude_split : string -> unit` updates the owned global
  store and records a REMOVE using the private ancestry handle. It accepts
  `[Thy.]Name`; resolution occurs in the writing theory. Persisted keys
  use `Thy$Name` and are never reinterpreted in a descendant. An absent
  name is harmless; the theorem stays in DB. This differs from local
  `simpLib.del_split` and per-call `ExclX "split:Thy$Name"` filtering.
  It requires explicit owned registration, rejects pinned writes, and
  never initializes or adopts foreign data. Its handle follows Context
  restore just like the getter and handler witnesses.

An explicit importing prelude calling `enable_split_attribute ()` before
loading the entire graph is also supported. A script's one-off API call
alone is **not** exported initialization. Merely loading ordinary `simpLib`
or `splitLib`, or querying rules, is insufficient. Late/current-segment
registration is not the supported replay contract.

Registration is serialized theory initialization, not a concurrent proof
operation. The module loader's loaded-module table is process-global:
after restoring a Context predating registration, explicitly call the API
again; reloading an already-loaded module need not rerun its body. TASK_10's
restored contexts/listener witnesses remain supported. Heap save/reload and
broader Context/lifecycle permutations belong to TASK_12's explicit gate;
this task does not infer them from fresh executable imports.

## Client audit and changed files

A tracked-repository audit found **no pre-existing theory scripts using
`[split]`**, including combined/multiline attributes. Existing persistent
selftests in `src/simp/src/selftest.sml` already explicitly initialize
registration (TASK_10). The registration fixture's public attribute calls
already opt in. Foreign-owner fresh-load fixtures intentionally do not opt
in and were not converted to library ownership. Immutable baseline inputs,
historical results and `.agent-files` artifact copies were not migrated.

All new persistent theory clients use explicit exported ordering:

- `probes/split-persistence/splitParentScript.sml`: three named additions,
  current-theory removal, absent-name removal, exported module dependency.
- `splitChildScript.sml`: fresh parent replay, qualified ancestor removal,
  identically named child addition, current-theory addition/removal.
- `splitDescendantScript.sml`: fresh descendant import without a script-time
  registration call, preserving exactly `splitChild$drop` and
  `splitParent$keep`.
- `selftest.sml`, `optIn.ML`, `verify.ML`, and `Holmakefile`: only a clean
  launcher is linked; six separate executable processes dynamically import
  parent, child, descendant, already-owned descendant, foreign attribute,
  or foreign exporter. Each checks both registries and verifies that neither
  the splitter, opt-in module, simplifier nor fixture theories are preloaded.
  Holmake builds dynamic controls as prerequisites without linking them.
- `probes/split-registration/selftest.sml`: focused persistent removal,
  Context restore, uninitialized/foreign/pinned rejection and malformed-name
  nonmutation tests, retaining all prior assertions.
- `src/simp/src/{splitLib.sml,splitLib.sig,splitPersistLib.sml,Holmakefile}`:
  API/storage integration and a normal `HOLSELFTESTLEVEL` persistence target.
- Maintained docs: `splitLib.enable_split_attribute.smd`, new
  `splitLib.exclude_split.smd`, `simpLib.{split_ss,del_split}.smd`, simplifier
  `notes.md`/`MANIFEST`, compatibility README, task index/progress, this file.

## Reproduction commands and evidence

Run from the repository root, with configured dependencies through the
simplifier. Do not run competing builds against shared products.

```sh
# Routine kernel/library/selftest gate (not the full -F gate):
bin/build -t --seq=tools/sequences/upto-parallel

# Explicit fixtures and unchanged neighboring contract suites:
HOLSELFTESTLEVEL=1 bin/Holmake --no-project --no-cache --no_prereqs -j1 \
  --holstate="$PWD/bin/hol.state0" -C src/simp/src \
  split-persistence split-registration fresh-load-regressions \
  traversal-contracts exclusion-contracts
(cd src/simp/src && ./selftest.exe)
(cd src/marker && ./selftest.exe)

# Direct theory-chain build and six genuinely fresh importer processes:
bin/Holmake --no-project --no-cache -j1 \
  --holstate="$PWD/bin/hol.state0" \
  -C src/simp/compatibility/probes/split-persistence check
# Or one fresh scenario, after building the fixtures:
(cd src/simp/compatibility/probes/split-persistence && \
  SPLIT_PERSIST_SCENARIO=descendant ./selftest.exe)

tools/h4pedant/h4pedant src/simp/src \
  src/simp/compatibility/probes/split-persistence \
  src/simp/compatibility/probes/split-registration
(cd src/simp/compatibility && sha256sum -c inputs/SHA256SUMS)
git diff --check
```

All final commands above exit **0**. Evidence lives in `results/task11/`:
`validation.json` records exact commands, statuses, source hashes, base
revision `613d7d8e1`, tool/heap hashes, generated-data hashes and ordering
excerpts. The source hashes identify the tested working-tree overlay on
that base; the landing commit's compiled sources/fixtures are identical.
Logs are losslessly gzipped; append `.gz` to the following names.

| Check | Outcome | Log |
| --- | --- | --- |
| Clean-built theory chain and focused targets | pass | `focused.log` |
| Fresh imports: parent / child / descendant | 20 / 21 / 21 OK | `direct.log` |
| Already-owned / foreign attribute / foreign set | 23 / 15 / 16 OK | `direct.log` |
| Registration, including new removal contracts | 97 OK | `focused.log` |
| Namespace-neutral fresh loads | five scenarios pass | `focused.log` |
| Traversal / exclusion contracts | 47 / 929 OK | `focused.log` |
| Native simplifier / marker | 630 / 70 OK | `native-{simplifier,marker}.log` |
| Routine sanity build (`upto-parallel`) | `Hol built successfully.` | `sanity-final.log` |
| Pedant / immutable input hashes | pass | `pedant.log` / `inputs.log` |

The initial sanity build also exited 0; the recorded final build was rerun
with all final sources, including the pinned-removal guard. Early fixture
trials exposed SML declaration/import mistakes, corrected before these
runs. Review also caught that Context slot modification writes the live
context even under a pinned read: removal now explicitly rejects pins,
with a whole-live-Context nonmutation regression. No expected failure was
reclassified as a successful import.

Superseded trial logs, the new theory fixture's generated objects/executable,
and the registration fixture's agent-created cache/executable were removed
after use. Compact generated ordering evidence survives in the manifest;
fixtures rebuild from maintained sources. Unrelated pre-existing artifacts
and the caller's TASK_10 progress clarifications were preserved.

The importer verifies exact named rule lists, actual DB theorem identity,
serialized qualified REMOVE keys, and silent idempotence. It also disables
TypeBase splitting to show that imported persistent rules actually split;
excluding every imported alias stops splitting, while excluding one equal
alias leaves the other active. Local exclusions leave the persistent store
unchanged. Foreign imports are expected to raise exactly
`splitLib.enable_split_attribute: settype or attribute split already exists`
while loading the opt-in dependency, not later during decoding/replay.
Handlers/data remain identical, callbacks remain usable, and no replacement
warnings are allowed. These expected loader diagnostics are retained.

Finite native fixtures do not establish universal compatibility. No new
paired differential run or full `-F` gate is claimed for this task.
