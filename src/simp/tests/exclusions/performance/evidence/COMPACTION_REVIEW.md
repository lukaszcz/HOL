# Offline compactness and bounded TASK17 review

No builds, HOL launches or new measurements. No production source change.
The pre-existing `src/simp/src/Holmakefile` selftest-integration edit is
caller-owned and untouched. All review edits are in this performance subtree.

## Cleanup and preservation

Pre-cleanup inventory hashes and the original raw/codegen recheck passed.
The subtree initially contained **19,187,411 file-content bytes** (about 19 MB).
After compaction it contains about **8.3 MB**; no final observation was dropped.

- Four full final compiler extents: 8,054,036 bytes of separate gzip files
  replaced by **652,824 bytes** of solid xz. Every original text byte survives,
  including non-selected compiler output. Original gzip artifact seals are
  also verified by in-memory reconstruction.
- All 20 exploratory timing receipts and both exploratory build receipts:
  **246,344-byte** shared archive, not discarded. The original manifest and
  all protocols, measurements, raw durations, environments and source seals
  survive. These are never substituted into final inference.
- Sixteen byte-identical source/native/tree copies: explicit aliases to one
  retained copy. This includes the failed attempt's duplicate source products.
  Unique selected final native/optimized/backend/ICode records remain exact.
  The identical preparation source-audit JSON also aliases the final audit
  instead of retaining a second copy (17 aliases in total).
- Failed 2,133,849-byte `codegen-current/baseline-assembly.json.gz`: removed
  redundant bulk diagnostics only. `failure.json.gz` retains the exact rejected
  optional-body assumption, command, exit, stdout hash/length, environment,
  emitted names and complete protocol/result metadata. The original failing
  manifest survives. Its redundant 16,388-byte derived native product is also
  removed with an original seal; final selected native records are untouched.
  This failed raw receipt is **not** reconstructible; no report now claims
  otherwise. The earlier failed derived-extent removal is
  preserved as historical compaction evidence.
- All 40 final raw timing receipts, final analysis/summary, final collection
  manifests, 18 GC follow-up receipts and their summary remain byte-identical.

`archive-compaction.json` is the relocation/removal authority; collection
manifests retain their original paths and hashes. Archive members are plain
text/JSON at original paths minus `.gz`, not nested gzip files. Recheck reads
members without filesystem extraction, validates uncompressed seals, restores
original gzip bytes in memory, and checks original manifest artifact seals.
`previous-inventories.json.gz` preserves both old checksum lists; refreshed
`SHA256SUMS` / `GC_SHA256SUMS` describe current physical files, not deleted paths.

## Independent acceptance assessment

Reviewed `.agent-files/tasks/TASK_17_restore_legacy_exclusions_and_replay.md`,
the semantic fixture/validator, source audit, final analysis and GC follow-up.
This is the **bounded literal-exclusion/history task**, not the unrelated
postkernel final-acceptance task with the same number.

Its performance requirement is removal of the reported threefold cost with
no extra ordinary scan; it does **not** require proving numerical parity.
Whole ordinary `simpLib.sml/.sig` bytes match pinned develop. The final
current CPU/wall point ratios and intervals support removal of that large
cost for this focused fixture: the largest current CPU family95 upper bound
is **1.123962**, at `dproc_only.10000` (wall **1.123901**), far below three.
This is source-isolated/shared-dependency, finite-workload evidence, not an
independent clean-build or universal runtime result.

That bounded finding is consistent with **43/44 unresolved CPU/wall family
intervals**, four original GC-slower intervals, and non-identical retained
heap/adaptive-GC state. The four-pair longer GC follow-up does not reproduce
a stable four-row slowdown; it neither cancels the original intervals nor
proves allocation/runtime parity. No performance uncertainty is relabelled
as parity or silently waived by native-code correspondence.

The separate semantic fixture targets unmatched history across theory changes,
callback order/counts, limits/exclusions, declared-bound reset, conversions and
reused tactic validations. It is not replaced by the timing fixture. This
review ran no semantic HOL campaign and does not independently certify those
external receipts, routine build gates, task landing or whole-plan completion.
A bounded TASK17 conclusion must cite those separately; broad final performance
acceptance remains outside this review. Task-status files are not changed.

## Offline checks after cleanup

- Enhanced `recheck.py`: lossless archive/alias/failure checks; all 40 final
  and 20 exploratory timing protocols; exact final analysis; both final
  codegen comparisons; exact GC summary recomputation from 18 receipts.
- Existing 13 performance and 2 adapter Python tests; source audit.
- Both current physical-file checksum inventories and whitespace checks.

Commands/outcomes are retained in `cleanup-checks.log` and `recheck.log`.
