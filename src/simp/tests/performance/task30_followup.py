#!/usr/bin/env python3
"""TASK30 follow-up: the two cells the TASK30 grid left inconclusive, measured
again (policy decision of 2026-11-05).

This is a table for timing_grid.py (read that module, and the "TASK30
follow-up" section of PROTOCOL.md, for the method). It replaces the cells
`exclude_partial-1` and `exclude_tactic_reuse-0` of the TASK30 grid, which
its second stage left inconclusive, and nothing else: the policy, the cases'
batch seconds, the samples, the baseline, the sources and the pins are the
TASK30 table's (task30_grid.py), and the TASK30 grid is replayed in full by
that table's own engine before the counts are derived from it, and again by
`replay`; `verify-counts`, `run` and `extend` bind it by the seals the counts
file records while the replay code is that of `predeclare`, and replay it in
full when that code has changed (PROTOCOL.md).

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
cells: any outcome but pass blocks (a fail is final). Combining it with the
TASK30 decision is the disposition step's (`task30_grid.py dispose`), not
this table's. Attempts go into the TASK30 ledger
(`.agent-files/evidence/task30/attempts.jsonl`), the same hash chain, each
line naming its table; the build stamp and the prepare log are this table's
own (`build-stamp-task30f.json`, `prepare-task30f.log`).

  prepare     configure, build and stamp the checkout    (takes the lock)
  pilot       develop-only cells for the counts          (needs a window)
  predeclare  counts file from the pilot (--replaces GRID --replaces-pilot
              DIR: the grid replaced and its pilot)   (replays that grid)
  verify-counts  the counts file against its pilot and the replaced grid
              (--replaces; by the seals of the counts)
  run         first stage (--pilot, --replaces)
  extend      second stage if the control left a cell open (--pilot)
  replay      recompute every archived decision offline
              (--pilot, --replaces-pilot; replays the replaced grid too)
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
# Seals of the code that earlier records of this table were made by, as
# TASK30's (task30_grid.py): empty until a change is made after this table's
# first record (its pilot). Then, in the same commit, append the seal the
# records were made by: the old timing_grid.py to ENGINES, acceptance.py to
# ACCEPTANCE, this file to DRIVERS, and (a reviewed change that alters
# nothing measured, only after `run`) the old task30_grid.py to
# SEALED_HISTORY["task30_grid.py"]; edit test_task30_grid.py, which pins them
# empty, too. Per file a later change needs: timing_grid.py the ENGINES entry,
# acceptance.py the ACCEPTANCE entry, task30_followup.py the DRIVERS entry
# (every record of this table carries those seals), task30_pins.py a
# PIN_HISTORY entry; summarize.py, audit_evidence.py and runtime_metrics.py
# none (no record carries them; the counts' `replaces.code` is compared with
# the commit of the counts, not with the current code). `run` compares the
# counts' sealed files exactly, so between the pilot and `run` only a fresh
# pilot absorbs a change to a sealed file. The
# disposition code is landed before the pilot, in a module of its own
# (task30_dispose.py) in neither table's seals, so task30_grid.py stays as
# it is from Z0 on. TASK30's own set of sealed names is frozen by its Y
# records: do not add a file to task30_grid.INSTALLED or SEALED.
DRIVERS, ENGINES, ACCEPTANCE = (), (), ()
# task30_grid.py is sealed like the helpers of the cases: this table takes
# its constants (SECONDS, PAIRS, SAMPLES, SEALED) and replays the TASK30
# grid through its table, so a change to it alters what is measured or
# replayed and binds the counts (a change that does not is a reviewed entry
# of SEALED_HISTORY). TASK30 treats its own file as its driver and lists the
# earlier ones in DRIVERS; here it is another table's driver.
SEALED = base.SEALED + ("task30_grid.py",)
SEALED_HISTORY = {}
# The seconds of a case are those of the TASK30 table, the ten direct
# deletions' being longer. The first-stage pairs (the floor of the pairs of a
# cell) are twice the TASK30 table's.
TABLE = tg.Table(
    "task30f", "TASK30-FOLLOWUP", CASES, __file__, COUNTS,
    cells=CELLS, family="task30", replaces=tg.Replaces(base.ENGINE),
    seconds=base.SECONDS,
    seconds_by_case={c: base.LONG_SECONDS for c in CASES
                     if c in cases.DELETIONS},
    fixed_seconds=True, schedule="warmup", pairs=2 * base.PAIRS,
    samples=base.SAMPLES, seed=LAYOUT_SEED, baseline=a.BASE, engine=True,
    tree="src", sealed=SEALED, sources=cases.SOURCES,
    pinned=pins.PINNED, pin_file="task30_pins.py",
    pin_history=pins.PIN_HISTORY, require_seed=True, drivers=DRIVERS,
    engines=ENGINES, layout_acceptance=ACCEPTANCE,
    sealed_history=SEALED_HISTORY, allocation=base.TABLE.allocation)
ENGINE = tg.Grid(TABLE, doc=__doc__)


def main(argv=None):
    return ENGINE.main(argv)


if __name__ == "__main__":
    sys.exit(main())
