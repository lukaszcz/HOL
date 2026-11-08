#!/usr/bin/env python3
"""TASK31 gate 3: the timing of a stratified sample.

This is the TASK31 table for timing_grid.py (read that module, and the
"Shared timing grid and the TASK30 table" and "TASK31" sections of
PROTOCOL.md): the 28 cells of task31_cases.SAMPLE, the warmup schedule,
20 first-stage pairs of 5 samples, the policy and second stage of TASK30
(3% on inclusive CPU and wall, GC reported, no outlier removal, a second
stage whose pair counts come from the develop/develop control). Its counts
file task31_iterations.json is made by `pilot` and `predeclare` and
committed before any candidate observation. The table names `sources`
(task31_cases.SOURCES, the files the cells elaborate) and pins the reviewed
blobs of those of them that task31_attributed.json lists. The file is sealed
in every record but not in the counts, and its entries outside the sources
(the shared heap and the build files) are not the table's: adding one alters
no sources record, and a grid made before it replays by the file's history.
A source that differs without a current pin never passes, and `run` refuses
to measure it. The difference below src/ is published by the table's `tree`.

Gate 1, the identity of every cell, is task31_identity_grid.py, which imports
this module and is not imported by it: a change there alters no seal of a
timing grid. The disposition (task31_dispose.py) joins the gates. The
commands are the engine's:

  prepare, pilot, predeclare, verify-counts, run, extend, replay
"""
import sys

sys.dont_write_bytecode = True
import acceptance as a
import task30_grid as base30
import task31_attribution as attr
import task31_cases as cases
import timing_grid as tg

PAIRS, SAMPLES = 20, 5
LAYOUT_SEED = "task31-layout-1"
# The batch seconds of a cell. The six singleton traversal operations are
# sub-microsecond, as TASK30's direct deletions are: they take TASK30's longer
# batch, to stand clear of the per-batch overhead. A predeclared field of the
# table, so the pilot measures it and `predeclare` copies it.
SECONDS, LONG_SECONDS = 0.3, 1.0
COUNTS = a.HERE / "task31_iterations.json"
# The files installed into the private directories of every process are
# TASK30's, less the fixture this table never installs, plus the client
# fixture and its dependencies; a test installs the fixtures and compares.
PAIRED = base30.PAIRED
INSTALLED = tuple(n for n in base30.INSTALLED
                  if n != "MatrixPerformance.sml") + (
    "ClientPerformance.sml", "client_dependencies.py")
SEALED = ("task31_cases.py",) + base30.SEALED[1:5] + INSTALLED
# Seals of the code that earlier records of this table were made by, as
# TASK30's (task30_grid.py): empty until a change is made after this table's
# first record (its pilot). Then, in the same commit, append the seal the
# records were made by: the old timing_grid.py to ENGINES, acceptance.py to
# ACCEPTANCE, this file to DRIVERS, and (a reviewed change that alters
# nothing measured) an old sealed file to SEALED_HISTORY[name]; edit
# test_task31_grid.py, which pins them, too. The identity gate is another
# module (task31_identity_grid.py, importing this one): a change to it, to
# task31_identity.py, task31_attribution.py or the reviewed table touches no
# seal of this table.
DRIVERS, ENGINES, ACCEPTANCE, SEALED_HISTORY = (), (), (), {}
# The reviewed table: read once. Its file is not among SEALED (the counts
# are not bound to it); every record seals it. The table's sources are the
# files the cells elaborate (task31_cases.SOURCES), and it pins the reviewed
# blobs of those of them the file lists; the entries for the shared heap and
# the build files are the identity gate's.
ATTRIBUTED = attr.load()
SOURCES = cases.SOURCES


def table(document):
    """The timing table with the pins of a reviewed document."""
    return tg.Table(
        "task31", "TASK31", cases.CASES, __file__, COUNTS, seconds=SECONDS,
        seconds_by_case={c: LONG_SECONDS for c in cases.TRAVERSAL_SINGLETON},
        fixed_seconds=True, schedule="warmup", headroom=1, pairs=PAIRS,
        samples=SAMPLES, seed=LAYOUT_SEED, baseline=a.BASE, engine=True,
        engines=ENGINES, drivers=DRIVERS, layout_acceptance=ACCEPTANCE,
        sealed_history=SEALED_HISTORY, tree="src", sealed=SEALED,
        cells=cases.SAMPLE, require_seed=True, sources=SOURCES,
        pinned=attr.pins(document["entries"], SOURCES),
        pin_file=attr.FILE.name,
        pin_history=attr.pin_history(document, SOURCES),
        allocation="the separate gate of allocation_matrix.py --task "
        "task31; task31_dispose.py joins the gates")


TABLE = table(ATTRIBUTED)
ENGINE = tg.Grid(TABLE, doc=__doc__)


def main(argv=None):
    return ENGINE.main(argv)


if __name__ == "__main__":
    sys.exit(main())
