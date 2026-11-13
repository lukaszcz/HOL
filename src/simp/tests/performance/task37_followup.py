#!/usr/bin/env python3
"""TASK37 follow-up: the cells a timing shard left open, measured again by
the shared engine (the method of task31_followup.py, whose precedent this
module keeps: the follow-up declaration is apart from the shard tables, so
declaring one changes no seal of task37_grid.py and voids no pilot, counts
file or record of a shard).

A table for timing_grid.py (read that module, and the "TASK37" and "TASK31
follow-up" sections of PROTOCOL.md). The follow-up of shard KEY replaces the
cells of CELLS[KEY], which a policy decision names after the shard's grid
(and its second stage) left them inconclusive, and nothing else: the
policy, the batch seconds, the samples, the baseline, the sources, the
pins and the seals are the shard's (task37_grid.py), whose grid is replayed
in full by the shard's own engine before the counts are derived, and again
by `replay`. The layout seed is another than the shard's and its second
stage's, the pairs of a cell derive from the shard's develop/develop
control (`Grid.followup_pairs`, twice the pairs of the shard), and the
attempts go into the shard's ledger.

With CELLS empty there is no follow-up and no engine: every command is
refused. To declare one, enter the shard key and its cells (a subset of the
shard's part, `task37_grid.PARTS`) in CELLS, and commit before any
observation of the follow-up. The follow-up table of shard `matrix-2` is
`task37-matrix-2-followup`, its counts file
`task37_matrix_2_followup_iterations.json` (made by `pilot` and
`predeclare --replaces GRID --replaces-pilot DIR`, committed alone).

  task37_followup.py SHARD COMMAND ...

with the engine's commands (`prepare`, `pilot`, `predeclare`,
`verify-counts`, `run`, `extend`, `replay`). GRIDS holds the engines
declared, by table name; task37_dispose.py takes them with
`task37_grid.GRIDS` (`--followup SHARD=DIR`, `--pilot`,
`--followup-pilot`).
"""
import sys

sys.dont_write_bytecode = True
import acceptance as a
import task37_cases as cases
import task37_grid as base
import timing_grid as tg

# The cells of the follow-up of each shard, by shard key (`matrix-2`),
# declared by a policy decision after the shard's grid; none yet.
CELLS = {}
# The shard's sealed files and its driver (this table takes its constants
# and replays its grid through its table).
SEALED = {k: base.SEALED[base.KIND[k]] + ("task37_grid.py",)
          for k in base.SHARD_KEYS}


def name_of(key):
    """The table name of the follow-up of a shard."""
    return base.name_of(key) + "-followup"


def file_of(key):
    """The counts file of the follow-up of a shard."""
    kind, number = key.split("-")
    return a.HERE / ("task37_%s_%s_followup_iterations.json" % (kind,
                                                                 number))


def table(key, cells, replaced):
    """The follow-up table of shard `key` for `cells` (a non-empty subset
    of its cells), replacing the grid of the engine `replaced`."""
    cells = tuple(cells)
    kind = base.KIND[key]
    a.require(cells and set(cells) <= set(base.PARTS[key]),
              "a follow-up measures cells of its shard")
    first = replaced.t
    found = tuple(dict.fromkeys(cases.split(c)[0] for c in cells))
    return tg.Table(
        name_of(key), "TASK37-%s-FOLLOWUP" % key.upper(), found, __file__,
        file_of(key), cells=cells, family=first.family,
        replaces=tg.Replaces(replaced), seconds=base.SECONDS,
        seconds_by_case={c: base.LONG_SECONDS for c in found
                         if c in base.LONG[kind]},
        fixed_seconds=True, schedule="warmup", headroom=1,
        pairs=2 * base.PAIRS, samples=base.SAMPLES,
        seed="%s-layout-1" % name_of(key), baseline=a.BASE, engine=True,
        engines=base.ENGINES, drivers=base.DRIVERS,
        layout_acceptance=base.ACCEPTANCE,
        sealed_history=base.SEALED_HISTORY, tree="src",
        sealed=SEALED[key], require_seed=True, sources=first.sources,
        pinned=first.pinned, pin_file=first.pin_file,
        pin_history=first.pin_history, allocation=first.allocation)


def declare(key, cells, grids=base.GRIDS):
    """The (table, engine) of the follow-up of shard `key`, or None for no
    cell."""
    if not cells:
        return None
    built = table(key, cells, grids[base.name_of(key)])
    return built, tg.Grid(built, doc=__doc__)


TABLES, GRIDS = {}, {}
for _key, _cells in CELLS.items():
    _found = declare(_key, _cells)
    if _found is not None:
        TABLES[_found[0].name], GRIDS[_found[0].name] = _found


def commands():
    """The engines by the name a command line gives them (`matrix-2`)."""
    return {n[len("task37-"):-len("-followup")]: g for n, g in GRIDS.items()}


def main(argv=None):
    argv = list(sys.argv[1:] if argv is None else argv)
    found = commands()
    if not argv or argv[0] not in found:
        print("REFUSED: no such TASK37 follow-up is declared (declared: "
              "%s; task37_followup.CELLS): task37_followup.py SHARD "
              "COMMAND ..." % (",".join(found) or "none"), file=sys.stderr)
        return tg.REFUSED
    return found[argv[0]].main(argv[1:])


if __name__ == "__main__":
    sys.exit(main())
