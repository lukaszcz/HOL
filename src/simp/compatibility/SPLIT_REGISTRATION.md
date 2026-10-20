# TASK_10: explicit, context-safe split registration

Landing identifier: `[TASK_10] Make persistent split registration explicit`
(commit subject). All TASK_10 acceptance criteria are satisfied; no blocker
remains. TASK_11 is the next unblocked task. This is core registration and
focused lifecycle validation, **not** the later theory-client/import gate.

## Changes and ownership contract

- `splitLib.{sml,sig}` removes the top-level collision guard and exporter
  construction. The new `enable_split_attribute : unit -> unit` explicitly
  registers both names. No exception from the former guard is suppressed.
  There is no automatic initialization in `simpLib`, queries, pure split
  operations, local `Split`/`add_split`, or TypeBase-driven `split_ss`.
- A private `Context.Data` slot contains an optional handle: the ancestry
  getter and the exact attribute/exporter handler records installed by
  `ThmSetData.export_with_ancestry`. This is not a process-global initialized
  flag. An empty session slot claims neither persistent namespace.
- `ThmAttribute.attribute_fns{,_of}` and
  `ThmSetData.data_exportfns_of` provide read-only registry inspection.
  Ownership means physical identity of **both** installed handler records,
  not a matching name, theorem shape, or mere presence of the private handle.
  Reinstalling the exact library handler is still library ownership; these
  tokens are an ownership convention, not a security boundary.
- Queries read the handle, both registries, and the ancestry global value
  from one snapshot. Missing handle or either foreign owner yields `[]`;
  queries never adopt a foreign set, initialize, or use an obsolete getter.
  Explicit initialization rejects either foreign registry before mutation.
  Owned initialization is a silent no-op, preserving handlers and data.
  Reserved words/abbreviations and foreign persistence-hook listeners are
  also preflighted. New initialization in a pinned read-only context is
  rejected rather than writing registration into another context; an owned
  registration remains an idempotent no-op even under a pin.
- Restoring before opt-in restores unclaimed registries/no handle. Opt-in
  can then construct a new ancestry instance; restoring an older owned
  snapshot selects that snapshot's original getter/witnesses and data.
  Replacing either registry without rewinding invalidates queries too.

### Why the theory-data listener change is necessary

`AncestryData.fullmake` allocates context slots and loadable-data operations.
Previously `ThyDataSexp.new` also registered a process-global listener that
captured that particular instance's UniversalType witness. Rewind and
re-opt-in failed on duplicate listener registration. Simply replacing that
listener would break restoration to the first instance instead.

`src/postkernel/ThyDataSexp.{sml,sig}` now keeps instance-specific hooks in a
Context slot. Each theory-data name has one permanent process listener
that dispatches to the hook in the current context, or does nothing if that
context predates registration. The process table retains **only stable
routing closures**, not data-instance handles/ownership. A foreign listener
under the reserved onload name is rejected, not overwritten.
`check_registration` allows splitLib to check both hook names before
allocating ancestry slots. Ordinary `new` also preflights its own hook.

Listener position remains process-first-registration order, as with the
existing listener API; restoring/re-registering does not reorder permanent
dispatchers. Registration is a serialized theory-initialization operation,
not a concurrent proof operation. The split delta loader is a no-op and the
parent loader drives replay, so these two dispatchers do not require a
changed ordering. TASK_11 must keep initialization before split-bearing
imports, not depend on reordering existing listeners.

## Replay inspection and TASK_11 handoff

The storage is unchanged `ThmSetData.export_with_ancestry`:

1. `AncestryData.fullmake` registers serialized `split.deltas` and
   `split.parents`, context slots `ancestry.split.global` and
   `ancestry.split.values`, and a parent replay callback. Deltas store ADD
   kernel names and REMOVE strings. The data-map's public name is `split`.
2. `ThyDataSexp.new` registers decoding and theory-event handling. During
   construction ancestry scans can run before fullmake's merge hook has
   been installed; fullmake's final topologically sorted ancestry scan runs
   after installation. Parent replay merges parents, applies deltas to the
   per-theory value, and applies their side effects to the global value.
3. Generated theory structures (`TheoryPP.pp_struct`) open parent theories
   and explicit `mldeps` **before** `TheoryReader.load_thydata` reads `.dat`.
   The reader binds theorems before installing encoded theory data, allowing
   raw ADD names to be cooked through DB. The generated structure finally
   calls `Theory.load_complete`, which emits `TheoryLoaded` and runs replay.
4. Therefore TASK_11 can use an explicitly named opt-in module whose body
   calls `splitLib.enable_split_attribute ()`, and explicitly add it with
   `Theory.add_ML_dependency` to the earliest split-bearing exported theory.
   It must be a real Holmake/loader dependency and must execute before that
   theory's `.dat`/`TheoryLoaded`, including when importing descendants.
   An explicit importing prelude that runs opt-in before dynamically loading
   the whole theory graph is another supported ordering.
5. A script's one-time call is **not** automatically exported as import-time
   initialization. Depending on ordinary `simpLib`/`splitLib` is insufficient.
   Do not introduce a reverse `splitLib` -> `simpLib` dependency. Module
   loader state is process-global: after Context rewind an already-loaded
   opt-in module may not execute again; call the API explicitly as needed.
6. Pending encoded data can be decoded by `LoadableThyData.new`, and ancestry
   scans support already-imported ancestors, but this task does not promise
   arbitrary late registration/current-segment replay. Initialize before
   imports. Real parent/child ADD/REMOVE export/fresh-import fixtures,
   explicit dependency encoding, and persistent theory-client migration
   remain TASK_11's specified acceptance scope.

REMOVE keys remain fully resolved where written; replay must not reinterpret
an unqualified name in the descendant theory. No serialized format, local
split algorithm, TypeBase policy, or split exclusion identity changed here.

## Tests and evidence

Final sources were captured in git object
`d26c40bfd55dde9140e43bde89427ec30bcf2335` (validation-only commit-tree,
parent `e9b6cd09d`), without moving the working branch. The landed compiled
sources and focused fixture are byte-identical to that snapshot;
`results/task10/validation.json` records their hashes. Reproduce against
the landing commit with `--branch <landing-commit>`; both paired manifests
record the exact tested snapshot, host inputs, commands and audits.

From the repository root, all final commands exit **0**:

```sh
bin/build -t --seq=tools/sequences/upto-parallel
HOLSELFTESTLEVEL=1 bin/Holmake --no-project --no-cache --no_prereqs -j1 \
  --holstate="$PWD/bin/hol.state0" -C src/simp/src \
  split-registration fresh-load-regressions \
  traversal-contracts exclusion-contracts
(cd src/simp/src && ./selftest.exe)
python3 src/simp/compatibility/fresh_load.py --branch <snapshot> \
  --output src/simp/compatibility/results/task10/fresh-load-final
python3 src/simp/compatibility/run.py --branch <snapshot> \
  --output src/simp/compatibility/results/task10/differential-final
tools/h4pedant/h4pedant src/1 src/postkernel src/simp/src \
  src/simp/compatibility/probes
(cd src/simp/compatibility && sha256sum -c inputs/SHA256SUMS)
git diff --check
git diff --cached --check
```

- New `probes/split-registration/selftest.sml`: **89 OK**. Covers explicit
  success, stored/local attributes, ADD/REMOVE, silent idempotence including
  whole-Context identity, both conflict kinds and whole-Context nonmutation,
  handler/data identity, foreign ordinary and ancestry exporters, missing
  initialization, and local/pure/TypeBase splitting. Restoration goes to
  before opt-in, a second independent opt-in, the first opt-in, and foreign
  ownership. Binding events and synthetic `TheoryLoaded` dispatch verify
  restored theory-data witnesses, not only getters. A set-only mismatch
  reinstalls the library attribute while leaving a foreign exporter, so the
  theorem-set disjunct is independently tested. Three deliberate public
  replacements emit their expected, unsuppressed warnings; opt-in/conflict
  operations themselves are checked silent. Cyclic abbreviation conflicts
  are rejected without expansion. Pinned reads select the pinned ownership
  and data, owned opt-in stays a no-op, and new pinned initialization fails
  without changing the live context.
- Native selftest **630 OK**, traversal contracts **47 OK**, exclusion
  contracts **929 OK**; their retained logs include expected diagnostics.
  Existing persistent selftest setup now opts in explicitly. Original
  assertions are preserved, with a new unclaimed-loading check.
- TASK_03 launcher/control bytes remain unchanged. All **ten** paired
  scenarios (five per lane) exit 0, independently assert clean preconditions,
  and preserve foreign callback/data behavior. Ordinary loading leaves
  both registries false; custom registrations have zero replacement
  warnings. Native aggregate passes too. Both clean-load and registration
  targets are now enabled under normal `HOLSELFTESTLEVEL` coverage.
- Full differential harness: **32/32** suite builds and runs pass across
  sixteen suites per lane. All fifteen instrumented OBS traces match; the
  unchanged develop suite has 73 OK in each lane, not an OBS comparison.
- Routine sanity build reaches `src/parallel_builds` and reports
  `Hol built successfully.` This is not the full `-F` gate.

The paired runs remain mixed-source: host kernel/heap/generated theories
and registry implementation are shared, not independently built develop
products. The native sanity build exercises the actual compiled registry
and listener changes. No universal compatibility or full persistence gate
is inferred from finite focused tests.

Early trials exposed ordinary fixture compilation mistakes and the real
process-global listener defect described above. One sanity attempt was
interrupted by the command time limit after progressing into num theories;
subsequent complete runs exited 0. The initial file-argument pedant command
was invalid (pedant expects directories); the directory invocation above
passes. These are not counted as passing attempts. Final logs replace
superseded trial logs; all retained logs are losslessly gzipped (append
`.gz` to log filenames in the paired manifests). Runner private
build trees, the new fixture's executable/object cache, and runner bytecode
created here were removed after use. Unrelated artifacts and the caller's
pre-existing progress clarifications were preserved.

API docs: new `help/Docfiles/splitLib.enable_split_attribute.smd`, updated
`splitLib.SPLIT_TAC.smd`, `simpLib.split_ss.smd`, and signatures. Additional
changed setup/docs: `src/simp/src/{selftest.sml,Holmakefile}`, compatibility
README, fresh-load README, task index/progress, and this handoff.
