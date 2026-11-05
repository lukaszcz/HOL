#!/usr/bin/env python3
"""TASK30 follow-up: the two cells the TASK30 grid left inconclusive, measured
again (policy decision of 2026-11-05).

This is a table for timing_grid.py (read that module, and the "TASK30
follow-up" section of PROTOCOL.md, for the method). It replaces the cells
`exclude_partial-1` and `exclude_tactic_reuse-0` of the TASK30 grid, which
its second stage left inconclusive, and nothing else: the policy, the cases'
batch seconds, the samples, the baseline, the sources and the pins are the
TASK30 table's (task30_grid.py), and the TASK30 grid is replayed in full by
that table's own engine before anything here is derived from it or measured
against it.

What is new is the draw and the schedule, both declared here. The layout seed
is another than the TASK30 grid's and its second stage's. The schedule is
`warmup`, the default of a new table (PROTOCOL.md): one recorded warm-up batch
of N, then the samples of N, with the counts of a pilot of these two cells
alone (`pilot`, `predeclare`, as for any table; the counts file does not
exist until that pilot has been made). The pairs of a cell are not a number
of this file: they are what the second-stage rule gives for the TASK30 grid's
first-stage develop/develop control of the cell, twice its 20 pairs at the
least and 120 at the most (`Grid.followup_pairs`). `predeclare` records them
in the counts file, and `verify-counts`, `run`, `extend` and `replay` derive
them again from the replaced grid and refuse a file that differs.

The follow-up has its own second stage (`extend`, seed `SEED-ext`) for a cell
whose control is outside the window, and a decision of its own over its two
cells: any outcome but pass blocks (a fail is final). Beside it the run
writes `final.json`, the TASK30 decision with these two cells in place of the
replaced ones, which `replay` derives again. Attempts go into the TASK30
ledger (`.agent-files/evidence/task30/attempts.jsonl`), which is the same
hash chain.

  prepare     configure, build and stamp the checkout    (takes the lock)
  pilot       develop-only cells for the counts          (needs a window)
  predeclare  counts file from the pilot (--replaces GRID --replaces-pilot
              DIR: the grid replaced and its pilot)
  verify-counts  the counts file against its pilot and the replaced grid
  run         first stage (--pilot, --replaces, --replaces-pilot)
  extend      second stage if the control left a cell open
              (--pilot, --replaces-pilot)
  replay      recompute every archived decision offline
              (--pilot, --replaces-pilot)
"""
import sys

sys.dont_write_bytecode = True
import acceptance as a
import task30_cases as cases
import task30_grid as base
import task30_pins as pins
import timing_grid as tg

CELLS = ("exclude_partial-1", "exclude_tactic_reuse-0")
CASES = ("exclude_partial", "exclude_tactic_reuse")
LAYOUT_SEED = "task30-followup-1"
COUNTS = a.HERE / "task30_followup_iterations.json"
# The seconds of a case are those of the TASK30 table, the ten direct
# deletions' being longer. The first-stage pairs (the floor of the pairs of a
# cell) are twice the TASK30 table's.
TABLE = tg.Table(
    "task30f", "TASK30-FOLLOWUP", CASES, __file__, COUNTS,
    cells=CELLS, family="task30", replaces=tg.Replaces(base.TABLE),
    seconds=base.SECONDS,
    seconds_by_case={c: base.LONG_SECONDS for c in CASES
                     if c in cases.DELETIONS},
    fixed_seconds=True, schedule="warmup", pairs=2 * base.PAIRS,
    samples=base.SAMPLES, seed=LAYOUT_SEED, baseline=a.BASE, engine=True,
    tree="src", sealed=base.SEALED, sources=cases.SOURCES,
    pinned=pins.PINNED, pin_file="task30_pins.py",
    pin_history=pins.PIN_HISTORY, require_seed=True,
    allocation=base.TABLE.allocation)
ENGINE = tg.Grid(TABLE, doc=__doc__)


def main(argv=None):
    return ENGINE.main(argv)


if __name__ == "__main__":
    sys.exit(main())
