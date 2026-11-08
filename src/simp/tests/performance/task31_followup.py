#!/usr/bin/env python3
"""TASK31 follow-up: the cells the TASK31 timing grid left open, measured
again by the shared engine (the method of task30_followup.py).

This is a table for timing_grid.py (read that module, and the "TASK30
follow-up" and "TASK31" sections of PROTOCOL.md). It replaces the cells of
CELLS, which a policy decision names after the first grid (and its second
stage) left them inconclusive, and nothing else: the policy, the batch
seconds, the samples, the baseline, the sources and the pins are the TASK31
table's (task31_grid.py), whose grid is replayed in full by that table's own
engine before the counts are derived from it, and again by `replay`. The
layout seed is another than the first grid's and its second stage's, the
pairs of a cell derive from the first grid's develop/develop control
(`Grid.followup_pairs`), and the attempts go into the TASK31 ledger.

CELLS is empty until a decision names cells; with none, this module has no
engine and refuses every command. To declare a follow-up, set CELLS to
the cell names (a subset of task31_cases.SAMPLE), choose a counts file name
below COUNTS, and commit before any observation of the follow-up. The
commands are the engine's (`prepare`, `pilot`, `predeclare --replaces GRID
--replaces-pilot DIR`, `verify-counts`, `run`, `extend`, `replay`), and
task31_dispose.py takes the follow-up (`--followup`, `--followup-pilot`).
"""
import sys

sys.dont_write_bytecode = True
import acceptance as a
import task31_grid as base
import timing_grid as tg

CELLS = ()
LAYOUT_SEED = "task31-followup-1"
COUNTS = a.HERE / "task31_followup_iterations.json"
# The first grid's sealed files and its driver (this table takes its
# constants and replays its grid through its table).
SEALED = base.SEALED + ("task31_grid.py",)


def table(cells):
    """The follow-up table of `cells` (a non-empty subset of the sample)."""
    cells = tuple(cells)
    names = tuple(dict.fromkeys(c.rsplit("-", 1)[0] for c in cells))
    return tg.Table(
        "task31f", "TASK31-FOLLOWUP", names, __file__, COUNTS, cells=cells,
        family="task31", replaces=tg.Replaces(base.ENGINE),
        seconds=base.SECONDS, seconds_by_case={
            c: base.LONG_SECONDS for c in names
            if c in base.TABLE.seconds_by_case},
        fixed_seconds=True, schedule="warmup", pairs=2 * base.PAIRS,
        samples=base.SAMPLES, seed=LAYOUT_SEED, baseline=a.BASE,
        engine=True, tree="src", sealed=SEALED, sources=base.SOURCES,
        pinned=base.TABLE.pinned, pin_file=base.TABLE.pin_file,
        pin_history=base.TABLE.pin_history, require_seed=True,
        allocation=base.TABLE.allocation)


TABLE = table(CELLS) if CELLS else None
ENGINE = tg.Grid(TABLE, doc=__doc__) if CELLS else None


def main(argv=None):
    if ENGINE is None:
        print("REFUSED: no TASK31 follow-up is declared "
              "(task31_followup.CELLS is empty)", file=sys.stderr)
        return tg.REFUSED
    return ENGINE.main(argv)


if __name__ == "__main__":
    sys.exit(main())
