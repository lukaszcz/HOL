#!/usr/bin/env python3
"""TASK30 timing gate: the exclusion and history cases, paired and layout
randomized, under the confirmed equivalence policy.

This is the TASK30 table for timing_grid.py (read that module, and the
"Shared timing grid and the TASK30 table" section of PROTOCOL.md, for the
method): 24 matrix cases at six sizes, 144 cells. Nothing here changes the
policy: a 3% margin on inclusive CPU and wall, GC reported and not gated, no
outlier removal, a second stage whose pair counts come from the
develop/develop control alone.

Pairs (20), samples (5) and the layout seed are fields of the table below,
sealed with this driver; `predeclare` copies them into the counts file and
`run` refuses a file or a value that differs. Every cell runs a predeclared
batch count from task30_iterations.json. That file is produced from a
develop-only pilot (`pilot`, then `predeclare`) and committed before any
candidate observation; it names the baseline, the seals of the pilot and of
the sealed files, and each cell's batch seconds. The ten direct deletions
are tiny operations; their batches are calibrated to a longer time. A cell
the first grid rejected as "fixed calibration too short" may have its count
rescaled in a new file (`predeclare --revises PREVIOUS --rescale CELL ...`,
listed in the table's revisions), and then the whole grid is run again at a
new candidate commit. A candidate whose source files on the path of these
operations (see task30_cases.SOURCES) differ from the baseline's never
passes, unless the file is a reviewed difference pinned in
task30_cases.PINNED. `run`, `extend` and `replay` take the pilot the counts
derive from (`--pilot DIR`, derived again in full) and an append-only
attempts ledger outside the repository (`--attempts FILE`).

The exit status is zero only when every cell passes. Failed, inconclusive,
control-limited and protocol-failed cells are listed separately and none is
excused here; a disposition, if one is ever made, is a separate reviewed
decision.

  pilot       develop-only cells for the counts          (needs a window)
  predeclare  counts file from a pilot, or a revision of the last file
              (--revises PREVIOUS --rescale CELL [CELL ...])
  verify-counts  the counts file against its pilot
  run         first stage (--pilot, --attempts)          (needs a window)
  extend      second stage for the cells the control left open
  replay      recompute every archived decision offline (--pilot,
              --attempts)
"""
import sys

sys.dont_write_bytecode = True
import acceptance as a
import task30_cases as cases
import timing_grid as tg

# As the TASK29A run used: 20 pairs of 5 samples per cell. `predeclare` writes
# these and the layout seed into the counts file; a second run under the same
# settings is a new draw, recorded in the attempts ledger (see PROTOCOL.md).
PAIRS, SAMPLES = 20, 5
LAYOUT_SEED = "task30-layout-1"
SECONDS, LONG_SECONDS = 0.3, 1.0
COUNTS = a.HERE / "task30_iterations.json"
TABLE = tg.Table(
    "task30", "TASK30", cases.CASES, __file__, COUNTS, seconds=SECONDS,
    seconds_by_case={c: LONG_SECONDS for c in cases.DELETIONS},
    fixed_seconds=True, pairs=PAIRS, samples=SAMPLES, seed=LAYOUT_SEED,
    baseline=a.BASE, engine=True, engines=(), tree="src",
    sealed=("task30_cases.py", "task29_gate.py", "matrix_schema.py",
            "performance_schema.py", "evidence_bundle.py",
            "MatrixSupport.sml", "MatrixPerformance.sml"),
    sources=cases.SOURCES, pinned=cases.PINNED, require_seed=True,
    allocation="the separate gate of allocation_matrix.py --task task30, "
    "all 24 cases at six sizes")
ENGINE = tg.Grid(TABLE, doc=__doc__)


def main(argv=None):
    return ENGINE.main(argv)


if __name__ == "__main__":
    sys.exit(main())
