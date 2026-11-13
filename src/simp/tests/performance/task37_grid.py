"""TASK37 timing: the sharded client and matrix tables of the final gate.

Tables for timing_grid.py (read that module, and the "TASK37" section of
PROTOCOL.md, with the "Shared timing grid" and "TASK31" sections), made by
the method of task31_grid.py: the warmup schedule (count rule, headroom 1),
20 first-stage pairs of 5 samples, alternating AB/BA and a B/B control per
round (the validation of TASK_30A), 3% on inclusive CPU and wall, GC
reported, no outlier removal, a second stage whose pair counts come from the
control. The policy is the engine's; nothing here changes it.

Two samples are measured, each as a fixed number of disjoint shards that run
concurrently, each shard in its own clone (design decisions 12 and 14):

  client   task37_cases.CLIENT_SAMPLE (the 28 cells of TASK31's sample, its
           three follow-up cells being among them, and the 11 downstream
           cells: 39 cells), measured by the client fixture
           ClientPerformance.sml, in SHARDS["client"] = 2 shards
           `task37-client-1` and `task37-client-2`.
  matrix   task37_cases.MATRIX_SAMPLE (87 cells), measured by the matrix
           fixture MatrixPerformance.sml, in SHARDS["matrix"] = 4 shards
           `task37-matrix-1` ... `task37-matrix-4`.

A shard is a `timing_grid.Table` with `cells=` its part of the sample. The
partition (`partition`) is fixed and deterministic: the cells of the sample
in sorted order, the cells of the long-batch cases (the sub-microsecond
operations) first, dealt out round-robin over the shards by one running
count, then the other cells continuing it. Two cells of the sample are in
different shards or the same one, never both; the shards' cell counts differ
by at most one, as do the counts of their long-batch cells. No un-sharded
table exists: nothing needs the whole sample as one table (the disposition
joins the shards, task37_dispose.py).

Each shard has its own counts file (`task37_matrix_1_iterations.json`, ...,
`task37_client_2_iterations.json`), layout seed (`task37-matrix-1-layout-1`),
ledger (`.agent-files/evidence/<table>/attempts.jsonl` below the checkout),
build stamp and prepare log, so that shards run at once from their clones
share no path (see "Concurrency" in PROTOCOL.md). The counts files are made
by `pilot` and `predeclare` of the measurement stage and committed before any
candidate observation; none exists until then. DRIVERS, ENGINES, ACCEPTANCE
and SEALED_HISTORY are empty: no record of these tables predates this file;
when a change is made after a table's first record (its pilot), append the
old seals there in the same commit, as task31_grid.py describes.

Follow-ups are in task37_followup.py (as TASK31's task31_followup.py is
apart from task31_grid.py): declaring one changes no seal of these shard
tables, whose records and counts it must not void.

The reviewed differences are those of task37_attributed.json (the format of
task31_attributed.json, read by task31_pins.py, which is sealed): the tables
pin the entries of their sources. The sources are the boundary lists of
task37_cases.py: the matrix shards' MATRIX_TIMING_SOURCES (task30_cases.
SOURCES without the deleted SimpTracking files) and the client shards'
CLIENT_TIMING_SOURCES (task31_cases.SOURCES). They are not the elaborated
closures that the identity tables need (task37_sources.py, which no shard
seals): identity accounting proves every differing loaded file attributed,
so the correctness of a timing table does not depend on its list
(design decision 19).

The command is the engine's, with the shard named first:

  task37_grid.py {client-1,client-2,matrix-1,...,matrix-4} COMMAND ...

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
FILE = cases.REVIEWED_FILE
# The shards of each sample (design decision 14).
SHARDS = dict(client=2, matrix=4)
# The files installed into the private directories of every process: the
# matrix tables install the matrix fixture and the client tables the client
# fixture and its dependencies (the lists of the tables they derive from).
INSTALLED = dict(client=base31.INSTALLED, matrix=base30.INSTALLED)
# The modules the cell sets derive from are sealed with the table, so that
# a change to a sample's source voids its records. task29_gate.py,
# matrix_schema.py, performance_schema.py and evidence_bundle.py are
# TASK30's seals; task31_pins.py computes the pins.
DERIVED = dict(
    client=("task31_cases.py", "task31_followup.py", "task31_grid.py"),
    matrix=("task29_gate.py", "task29a_grid.py", "task30_cases.py"))
SEALED = {k: tuple(dict.fromkeys(
    ("task37_cases.py", "task31_pins.py") + DERIVED[k] +
    base30.SEALED[1:5] + INSTALLED[k])) for k in SHARDS}
# Seals of earlier code: empty until a change is made after a table's first
# record (see the docstring).
DRIVERS, ENGINES, ACCEPTANCE, SEALED_HISTORY = (), (), (), {}
# The reviewed table, read once; its file is not sealed with the counts
# (every record seals it).
ATTRIBUTED = reviewed.load(FILE)
SOURCES = dict(client=cases.CLIENT_TIMING_SOURCES,
               matrix=cases.MATRIX_TIMING_SOURCES)
# The cases of a sample, its cells and the cases with a long batch.
CASES = dict(client=cases.CLIENT_SAMPLE_CASES,
             matrix=cases.MATRIX_SAMPLE_CASES)
CELLS = dict(client=cases.CLIENT_SAMPLE, matrix=cases.MATRIX_SAMPLE)
LONG = dict(client=cases.LONG_CLIENT, matrix=cases.LONG_MATRIX)


def shards(kind):
    """The shard keys of a sample, `kind-1` ... `kind-N`."""
    return tuple("%s-%d" % (kind, i + 1) for i in range(SHARDS[kind]))


SHARD_KEYS = tuple(k for kind in SHARDS for k in shards(kind))
KIND = {k: kind for kind in SHARDS for k in shards(kind)}


def partition(kind):
    """The cells of each shard of a sample, a tuple per shard (in the order
    of `shards(kind)`), each in sorted order: the cells of the long-batch
    cases first, then the others, in sorted order, dealt round-robin by one
    running count."""
    count = SHARDS[kind]
    every = sorted(CELLS[kind])
    long = [c for c in every if cases.split(c)[0] in LONG[kind]]
    rest = [c for c in every if cases.split(c)[0] not in LONG[kind]]
    found = [[] for _ in range(count)]
    for i, cell in enumerate(long + rest):
        found[i % count].append(cell)
    return tuple(tuple(sorted(each)) for each in found)


PARTS = {k: part for kind in SHARDS
         for k, part in zip(shards(kind), partition(kind))}


def name_of(key):
    """The table name of a shard key (`matrix-2`)."""
    return "task37-" + key


def file_of(key):
    """The counts file of a shard."""
    kind, number = key.split("-")
    return a.HERE / ("task37_%s_%s_iterations.json" % (kind, number))


def table(key, document=ATTRIBUTED):
    """The timing table of a shard key (`matrix-2`) with the pins of a
    reviewed document."""
    kind = KIND[key]
    cells = PARTS[key]
    found = tuple(c for c in CASES[kind]
                  if any(cases.split(x)[0] == c for x in cells))
    return tg.Table(
        name_of(key), "TASK37-" + key.upper(), found, __file__,
        file_of(key), seconds=SECONDS, seconds_by_case={
            c: LONG_SECONDS for c in found if c in LONG[kind]},
        fixed_seconds=True, schedule="warmup", headroom=1, pairs=PAIRS,
        samples=SAMPLES, seed="%s-layout-1" % name_of(key),
        baseline=a.BASE, engine=True, engines=ENGINES, drivers=DRIVERS,
        layout_acceptance=ACCEPTANCE, sealed_history=SEALED_HISTORY,
        tree="src", sealed=SEALED[kind], cells=cells, require_seed=True,
        sources=SOURCES[kind],
        pinned=reviewed.pins(document["entries"], SOURCES[kind]),
        pin_file=FILE.name,
        pin_history=reviewed.pin_history(document, SOURCES[kind]),
        allocation="the separate gate of allocation_matrix.py --task "
        "task37-%s; task37_dispose.py joins the gates" % kind)


TABLES = {name_of(k): table(k) for k in SHARD_KEYS}
# The engines of the shards by table name (those of the follow-ups
# declared are task37_followup.GRIDS).
GRIDS = {name_of(k): tg.Grid(TABLES[name_of(k)], doc=__doc__)
         for k in SHARD_KEYS}


def commands():
    """The engines by the name a command line gives them (`matrix-2`)."""
    return {n[len("task37-"):]: g for n, g in GRIDS.items()}


def main(argv=None):
    argv = list(sys.argv[1:] if argv is None else argv)
    found = commands()
    if not argv or argv[0] not in found:
        print("REFUSED: name the table first: task37_grid.py {%s} COMMAND "
              "..." % ",".join(found), file=sys.stderr)
        return tg.REFUSED
    return found[argv[0]].main(argv[1:])


if __name__ == "__main__":
    sys.exit(main())
