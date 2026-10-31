#!/usr/bin/env python3
"""TASK30 timing gate: the exclusion and history cases, paired and layout
randomized, under the confirmed equivalence policy.

This is the TASK30 table for timing_grid.py (read that module, and the
"Shared timing grid and the TASK30 table" section of PROTOCOL.md, for the
method): 24 matrix cases at
six sizes, 144 cells. Nothing here changes the policy: a 3% margin on
inclusive CPU and wall, GC reported and not gated, no outlier removal, a
second stage whose pair counts come from the develop/develop control alone.

Every cell runs a predeclared batch count from task30_iterations.json. That
file is produced from a develop-only pilot (`pilot`, then `predeclare` with
the layout seed, pairs and samples of the run) and committed before any
candidate observation; it names the baseline, the seals of the pilot and each
cell's batch seconds, and `run` takes every setting from it. The ten direct
deletions are tiny operations; their batches are calibrated to a longer time.
A candidate whose source files on the path of these operations (see
task30_cases.SOURCES) differ from the baseline's never passes.

The exit status is zero only when every cell passes. Failed, inconclusive,
control-limited and protocol-failed cells are listed separately and none is
excused here; a disposition, if one is ever made, is a separate reviewed
decision.

  pilot       develop-only cells for the counts          (needs a window)
  predeclare  counts file from a pilot (--layout-seed, --pairs, --samples)
  verify-counts  the counts file against its pilot
  run         first stage                                (needs a window)
  extend      second stage for the cells the control left open
  replay      recompute every archived decision offline
"""
import sys

sys.dont_write_bytecode = True
import acceptance as a
import task30_cases as cases
import timing_grid as tg

# As the TASK29A run used: 20 pairs of 5 samples per cell, the defaults of
# `predeclare`, which writes them into the counts file.
PAIRS, SAMPLES = 20, 5
SECONDS, LONG_SECONDS = 0.3, 1.0
COUNTS = a.HERE / "task30_iterations.json"
TABLE = tg.Table(
    "task30", "TASK30", cases.CASES, __file__, COUNTS, seconds=SECONDS,
    seconds_by_case={c: LONG_SECONDS for c in cases.DELETIONS},
    fixed_seconds=True, pairs=PAIRS, samples=SAMPLES, engine=True,
    engines=(), sealed=("task30_cases.py", "task29_gate.py",
                        "matrix_schema.py", "performance_schema.py",
                        "evidence_bundle.py"),
    sources=cases.SOURCES, require_seed=True,
    allocation="the separate gate of allocation_matrix.py --task task30, "
    "all 24 cases at six sizes")
ENGINE = tg.Grid(TABLE, doc=__doc__)


def main(argv=None):
    return ENGINE.main(argv)


if __name__ == "__main__":
    sys.exit(main())
