#!/usr/bin/env python3
"""TASK37 timing: the client table and the matrix table of the final gate.

Two tables for timing_grid.py (read that module, and the "TASK37" section of
PROTOCOL.md, with the "Shared timing grid" and "TASK31" sections), made by
the method of task31_grid.py: the warmup schedule (count rule, headroom 1),
20 first-stage pairs of 5 samples, alternating AB/BA and a B/B control per
round (the validation of TASK_30A), 3% on inclusive CPU and wall, GC
reported, no outlier removal, a second stage whose pair counts come from the
control. The policy is the engine's; nothing here changes it.

  task37-client  the client timing sample of task37_cases.CLIENT_SAMPLE (the
                 28 cells of TASK31's sample, its three follow-up cells being
                 among them, and the 11 downstream cells), measured by the
                 client fixture ClientPerformance.sml. Counts:
                 task37_client_iterations.json.
  task37-matrix  the matrix timing sample of task37_cases.MATRIX_SAMPLE,
                 measured by the matrix fixture MatrixPerformance.sml.
                 Counts: task37_matrix_iterations.json.

Both counts files are made by `pilot` and `predeclare` of the measurement
stage and committed before any candidate observation; neither exists until
then. Each table has its own seals (the files below), its own counts file,
ledger (`.agent-files/evidence/<table>/attempts.jsonl` below the checkout),
build stamp and layout seed, so two tables can run at once from two clones
(see "Concurrency" in PROTOCOL.md). DRIVERS, ENGINES, ACCEPTANCE and
SEALED_HISTORY are empty: no record of these tables predates this file; when
a change is made after a table's first record (its pilot), append the old
seals there in the same commit, as task31_grid.py describes.

The reviewed differences are those of task37_attributed.json (the format of
task31_attributed.json, read by task31_pins.py, which is sealed): the tables
pin the entries of their sources. The matrix sources are task30_cases.SOURCES
without the deleted SimpTracking files (task37_cases.MATRIX_SOURCES); the
client sources are task31_cases.SOURCES.

The command is the engine's, with the table named first:

  task37_grid.py {client,matrix} COMMAND ...

  prepare, pilot, predeclare, verify-counts, run, extend, replay
"""
import sys

sys.dont_write_bytecode = True
import acceptance as a
import task30_grid as base30
import task31_grid as base31
import task31_pins as reviewed
import task37_cases as cases
import timing_grid as tg

PAIRS, SAMPLES = 20, 5
SECONDS, LONG_SECONDS = 0.3, 1.0
FILE = a.HERE / "task37_attributed.json"
COUNTS = dict(client=a.HERE / "task37_client_iterations.json",
              matrix=a.HERE / "task37_matrix_iterations.json")
NAMES = dict(client="task37-client", matrix="task37-matrix")
LAYOUT_SEEDS = dict(client="task37-client-layout-1",
                    matrix="task37-matrix-layout-1")
# The files installed into the private directories of every process: the
# matrix table installs the matrix fixture and the client table the client
# fixture and its dependencies (the lists of the tables they derive from).
INSTALLED = dict(client=base31.INSTALLED, matrix=base30.INSTALLED)
# The modules the cell sets derive from are sealed with the table, so that
# a change to a sample's source voids its records. task29_gate.py,
# matrix_schema.py, performance_schema.py and evidence_bundle.py are
# TASK30's seals; task31_pins.py computes the pins.
DERIVED = dict(
    client=("task31_cases.py", "task31_followup.py", "task31_grid.py"),
    matrix=("task29_gate.py", "task29a_grid.py", "task30_cases.py"))
SEALED = {k: ("task37_cases.py", "task31_pins.py") + DERIVED[k] +
          base30.SEALED[1:5] + INSTALLED[k] for k in COUNTS}
# Seals of earlier code: empty until a change is made after a table's first
# record (see the docstring).
DRIVERS, ENGINES, ACCEPTANCE, SEALED_HISTORY = (), (), (), {}
# The reviewed table, read once; its file is not sealed with the counts
# (every record seals it).
ATTRIBUTED = reviewed.load(FILE)
SOURCES = dict(client=cases.CLIENT_SOURCES, matrix=cases.MATRIX_SOURCES)
# The cases of a table, the cells it measures and the cases with a long
# batch (the sub-microsecond operations).
CASES = dict(client=cases.CLIENT_SAMPLE_CASES,
             matrix=cases.MATRIX_SAMPLE_CASES)
CELLS = dict(client=cases.CLIENT_SAMPLE, matrix=cases.MATRIX_SAMPLE)
LONG = dict(client=cases.LONG_CLIENT, matrix=cases.LONG_MATRIX)
LABELS = dict(client="TASK37-CLIENT", matrix="TASK37-MATRIX")


def table(kind, document=ATTRIBUTED):
    """The timing table `kind` ("client" or "matrix") with the pins of a
    reviewed document."""
    found = CASES[kind]
    return tg.Table(
        NAMES[kind], LABELS[kind], found, __file__, COUNTS[kind],
        seconds=SECONDS, seconds_by_case={
            c: LONG_SECONDS for c in found if c in LONG[kind]},
        fixed_seconds=True, schedule="warmup", headroom=1, pairs=PAIRS,
        samples=SAMPLES, seed=LAYOUT_SEEDS[kind], baseline=a.BASE,
        engine=True, engines=ENGINES, drivers=DRIVERS,
        layout_acceptance=ACCEPTANCE, sealed_history=SEALED_HISTORY,
        tree="src", sealed=SEALED[kind], cells=CELLS[kind],
        require_seed=True, sources=SOURCES[kind],
        pinned=reviewed.pins(document["entries"], SOURCES[kind]),
        pin_file=FILE.name,
        pin_history=reviewed.pin_history(document, SOURCES[kind]),
        allocation="the separate gate of allocation_matrix.py --task %s; "
        "task37_dispose.py joins the gates" % NAMES[kind])


TABLES = {kind: table(kind) for kind in COUNTS}
ENGINES_BY_KIND = {kind: tg.Grid(TABLES[kind], doc=__doc__)
                   for kind in COUNTS}


def main(argv=None):
    argv = list(sys.argv[1:] if argv is None else argv)
    if not argv or argv[0] not in ENGINES_BY_KIND:
        print("REFUSED: name the table first: task37_grid.py {%s} COMMAND ..."
              % ",".join(ENGINES_BY_KIND), file=sys.stderr)
        return tg.REFUSED
    return ENGINES_BY_KIND[argv[0]].main(argv[1:])


if __name__ == "__main__":
    sys.exit(main())
