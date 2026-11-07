# TASK17 focused exclusion-performance handoff

Authorized exclusive window completed on 2026-10-22; **released**.
No edits outside this new subtree and no commit.

Final current then baseline-control: **10 fresh pairs each**, three samples
plus fixed calibration for all 44 keys, same `final-iterations.json`.
All final timing receipts and both final compiler inspections pass.

See **`evidence/RESULTS.md`** for results, failures/fixes/reruns, source/codegen
links, interpretation limits and exact archive inventory. Raw evidence is
compressed, with failed/exploratory attempts separated from final campaigns.
Offline compaction retains every final raw timing/GC receipt and exact
selected codegen record. Four full compiler extents share one lossless xz
archive; exploratory receipts also share one lossless archive. Exact duplicate
source/record copies use explicit aliases. Only rejected bulk compiler
output was pruned; unique failure/protocol metadata and manifests survive.
See `evidence/archive-compaction.json` and `evidence/COMPACTION_REVIEW.md`.
Offline recheck:

```sh
python3 -B src/simp/tests/exclusions/performance/evidence/recheck.py
```

Key findings:

- Total CPU/wall family intervals unresolved for 43/44 current workloads;
  control unresolved for all 44. **No numerical parity claim.**
- Four GC-only slower rows remain visible, also in independent contrasts:
  `replay.1000`, `missing.10000`, `matching.10000`, `qualified.10000`.
- Whole ordinary source/signature bytes match pinned develop. All 25 selected
  native occurrences match after narrow pool-relocation normalization;
  exact whole-initializer tree/ICode tracking-reference differences retained.
  This does not establish runtime parity or waive GC-only slower results.
- Fixed unchanged-proof conversion failure in `ExclusionInputs.sml`; final
  timing campaigns rerun fresh. Fixed codegen adapter's erroneous expectation
  of a standalone `build_from_history` body; both final inspections rerun.
- Final tests: 13 performance + 2 adapter offline tests; source audit and
  raw/archive recheck pass. Post-compaction recheck additionally validates all
  exploratory timing and GC diagnostic receipts without extracting files.
  Current physical-file hashes are in `evidence/SHA256SUMS`; pre-cleanup
  inventories survive in `evidence/previous-inventories.json.gz`.
  Private temporary trees/heaps cleaned.

The original README describes the preparation/initial schedule and reproduction
protocol; actual completed results and the longer final schedule are here.
This focused performance evidence does not replace main's separate semantic
suite or assert whole TASK17/whole-plan completion.
