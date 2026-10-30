# TASK29A layout-randomized two-stage grid (INCONCLUSIVE; disposed: PASS)

The full rerun predeclared in `TASK_29A_numerical_attribution_closure.md`
("Fail attribution: code layout"). The candidate is `6f62229c0` and the
baseline is develop. Policy version 2 applies: a 3% margin on CPU and wall,
with GC reported only. Every cell uses 5 samples and the predeclared counts
(`../iterations.json`).

- `stage1/`: `task29a_grid.py run --pairs 20 --samples 5 --layout-seed
  task29a-grid-1`, all 162 cells. Result: 124 pass, 38 inconclusive,
  0 fail.
- `stage2/`: `task29a_grid.py extend` on `stage1/` (seed
  `task29a-grid-1-ext`). It remeasures the 35 cells whose develop/develop
  control was outside the window, with 40–120 pairs each.
  `stage2/decisions.json` is the grid decision: 144 pass, 18
  inconclusive, 0 fail.
- `run.sh` is the driver script and `run.log.gz` its complete log.
  `replay-stage1.log` and `replay-stage2.log` record the offline replay.

The run went from 2026-10-26 17:14 to 2026-10-30 09:42 UTC. It was
interrupted four times, and each time it resumed with `--resume`. Each
resume replayed every recorded cell exactly before measuring went on. A
cell that was not yet recorded was measured again from scratch, and no
recorded cell was dropped or repeated.

1. Cell 11 of stage 1 (`frag_named/1000`) died with ENOSPC when the shared
   root disk filled up. From then on, per-cell temporary trees went to the
   sandbox's private `/dev/shm` (`TMPDIR`). This changes only where scratch
   files are stored.
2. Cell 27 (`frag_update/10`) died because another host process deleted
   `/tmp/hol4-performance-UID.lock`.
3. A planned stop came after 64 rows, so that commit `9ee8d00bd` could move
   that lock into `.agent-files/`. `stage1/inventory.json` records the new
   driver and acceptance seals under `"resumed"` with `after: 64`. Neither
   change touches measurement or analysis.
4. Stage-2 cell 21 (`frag_named_merge/10000`) died with ENOSPC while its
   archive was being written. The unrecorded 0-byte archive was removed and
   the cell was measured again.

Replay (each step takes minutes):

    python3 -B task29a_grid.py replay --output evidence/task29a/grid/stage1
    python3 -B task29a_grid.py replay --output evidence/task29a/grid/stage2

The second command also verifies `stage1/` through the relative path and
seals stored in `stage2/inventory.json`. Both exit 2 (inconclusive).

Disposition (2026-10-30, by the policy owner; see
`TASK_29A_numerical_attribution_closure.md`, "Attribution and
policy-owner disposition"):

    python3 -B task29a_grid.py dispose --output evidence/task29a/grid/stage2

It replays both stages, then classifies the 18 open cells as 13
unresolvable on this host and 5 attributed, with no blocking cell and no
fail. It checks the result against `stage2/disposition.json` (written with
`--record`) and exits 0. `dispose.log` records that run.
