"""The TASK37 cases: what the final gate's cell sets are, derived.

Data and its derivation only, so the timing tables (task37_grid.py), the
matrix identity gate and the allocation matrix cannot disagree about which
cells are in scope (see the "TASK37" section of PROTOCOL.md for the scope
decision: stratified, user decision of 2026-11-13). Nothing here edits a
sealed TASK29-31 module: the cases of TASK29 and TASK30 are reused, and the
view of the final candidate (its source set) is stated here.

The cell sets, with their counts (a test pins them):

- the matrix, MATRIX_CELLS: the 27 TASK29 cases (task29_gate.CASES) and the
  24 TASK30 cases (task30_cases.CASES) at the six sizes of their `rules`
  size set, 162 + 144 = 306 cells, from matrix.json (by matrix_schema);
- the client cells, CLIENT_CELLS: task31_cases (278 cells), of which the
  33 of INFEASIBLE (the heavy size-10000 tactic cells: identity only) are
  not allocated, so CLIENT_ALLOCATED has 245;
- the downstream cells, DOWNSTREAM_CELLS: `downstream_arithmetic` and
  `downstream_reduce` at 1, 10, 100, 1000 and 10000 and `downstream_boss`
  at 0, 11 cells whose workloads are those of ClientPerformance.sml (the
  `downstream` function, selected by PERF_CASE and PERF_SIZE like the
  traversal and tactic cases).

The timing samples (design decision 4 of TASK_37_design.md):

- MATRIX_SAMPLE: every matrix case at size 1000 (a case without 1000 at its
  nearest size at or below 1000, a singleton at its one size; every
  matrix.json case of the matrix has 1000), the eleven cells the history
  flagged (FLAGGED), and every cell of the dispositions of the earlier
  grids that the final run tests again instead of assuming:
  CONTROL_LIMITED (the 13 cells TASK29A left unresolvable: B/B control
  outside the window after the second stage), ATTRIBUTED_29A (its 5
  attributed cells) and ATTRIBUTED (the 13 cells TASK30 attributed by
  structural evidence);
- CLIENT_SAMPLE: the 28 cells of task31_cases.SAMPLE and its follow-up cells
  (task31_followup.CELLS, which are cells of that sample, so the two lists
  add 28 cells), and the 11 downstream cells.

The source lists. The timing tables pin the boundary lists
MATRIX_TIMING_SOURCES and CLIENT_TIMING_SOURCES (below: the rule is stated
there). The identity tables need the exact elaborated closure of their
cells and use task37_sources.py, which only they seal (PROTOCOL.md, TASK37
identity).
"""
import sys

sys.dont_write_bytecode = True
import acceptance as a
import matrix_schema as ms
import task29_gate as gate29
import task29a_grid as grid29a
import task30_cases as cases30
import task31_cases as cases31
import task31_followup as followup31

# The reviewed differences from the baseline at the final candidate (the
# format of task31_attributed.json): the one table every TASK37 gate is
# judged by.
REVIEWED_FILE = a.HERE / "task37_attributed.json"
# The size the matrix timing sample takes of every case.
SAMPLE_SIZE = 1000

MATRIX_CASES = tuple(gate29.CASES) + tuple(cases30.CASES)
CLIENT_CASES = tuple(cases31.CASES)
DOWNSTREAM_SIZES = {"downstream_arithmetic": (1, 10, 100, 1000, 10000),
                    "downstream_reduce": (1, 10, 100, 1000, 10000),
                    "downstream_boss": (0,)}
DOWNSTREAM_CASES = tuple(DOWNSTREAM_SIZES)


def name(case, size):
    return "%s-%d" % (case, size)


def split(cell):
    """(case, size) of a cell name."""
    case, size = cell.rsplit("-", 1)
    return case, int(size)


def sizes(case):
    """The sizes of a matrix.json case, from the size sets of the ledger."""
    return tuple(ms.SIZE_SETS[ms.EXPECTED_CASES[case]["sizes"]])


def cells_of(cases):
    """Every cell of `cases`, in order."""
    return tuple(name(c, n) for c in cases for n in sizes(c))


def at_or_below(case, limit=SAMPLE_SIZE):
    """The size a sample takes of `case`: `limit`, or the nearest size of
    the case below it, or its singleton."""
    below = [n for n in sizes(case) if n <= limit]
    return max(below) if below else min(sizes(case))


def merged(*lists):
    """The cells of several lists, once each, in the order of first
    occurrence."""
    return tuple(dict.fromkeys(c for each in lists for c in each))


MATRIX_CELLS = cells_of(MATRIX_CASES)
CLIENT_CELLS = cells_of(CLIENT_CASES)
# The heavy size-10000 tactic cells that do not fit the identity process
# timeout (TASK31 policy D2): identity only, derived from the measured cells
# of their case, and not allocated.
INFEASIBLE = tuple(cases31.INFEASIBLE)
CLIENT_ALLOCATED = tuple(c for c in CLIENT_CELLS if c not in INFEASIBLE)
# The same cells as (case, size) pairs (the form allocation_matrix.Task
# takes).
CLIENT_INFEASIBLE_CELLS = tuple(cases31.INFEASIBLE_CELLS)
# The case-list modules the allocation harness seals for the TASK37 tasks
# (besides task29_gate.py and task30_cases.py, which every task binds).
FILES = ("task37_cases.py", "task31_cases.py")
DOWNSTREAM_CELLS = tuple(name(c, n) for c, found in DOWNSTREAM_SIZES.items()
                         for n in found)

# The eleven cells the design (TASK_37_design.md, decision 4) names as
# historically flagged in the TASK29/30 grids; the final run measures them
# again.
FLAGGED = (
    "frag_record-0", "compile_collector-10000", "frag_named_merge-10000",
    "frag_create-10000", "frag_named-10000", "frag_named_rules-1",
    "frag_named_rules-10", "exclude_partial-1", "exclude_tactic_reuse-0",
    "exclude_literal_exact-10000", "exclude_dproc-10000")

# The 13 cells of the TASK29A grid left control-limited ("unresolvable") after
# its second stage. Source: the `unresolvable` list of that grid's
# `disposition.json` (task29a_grid.dispose), kept outside the repository at
# .agent-files/evidence/perf-evidence-83d2501460/src/simp/tests/performance/
# evidence/task29a/grid/stage2/disposition.json (counts: pass 144,
# unresolvable 13, attributed 5, blocking 0, fail 0). No module of the
# repository holds this list, so it is copied here; a test pins its size
# and its membership in the matrix.
CONTROL_LIMITED = (
    "frag_create-0", "frag_create-10000", "frag_named-0",
    "frag_record-10000", "frag_update-1000", "frag_update-10000",
    "frag_duplicate-10000", "frag_ac-0", "frag_ac-1", "frag_ac-10",
    "frag_ac-100", "frag_ac-1000", "compile_bounded-10000")
# The 5 cells TASK29A attributed after examining each (derived).
ATTRIBUTED_29A = tuple(sorted(grid29a.DISPOSITION["attributed"]))
# The 13 cells TASK30 attributed by structural evidence (the policy owner's
# decision of 2026-11-05): task30_dispose.DISPOSITION["attributed"], and
# `attributed` of .agent-files/evidence/task30/followup-r2/disposition.json.
# That module imports the allocation matrix, which the allocation gate of
# this task may in turn import this module from, so the list is copied here
# and a test compares it with task30_dispose's.
ATTRIBUTED = (
    "exclude_batch-10000", "exclude_dproc-10000",
    "exclude_literal_exact-10000", "exclude_literal_namespace-1",
    "exclude_marker-10000", "exclude_marker_reuse-10000",
    "exclude_matching-10000", "exclude_missing-10000",
    "exclude_mixed-10000", "exclude_qualified-10000",
    "exclude_tactic_complete-10000", "exclude_tactic_reuse-10000",
    "history_excluded-10000")
D4 = merged(CONTROL_LIMITED, ATTRIBUTED_29A, ATTRIBUTED)

MATRIX_SAMPLE_BASE = tuple(name(c, at_or_below(c)) for c in MATRIX_CASES)
_SAMPLED = set(merged(MATRIX_SAMPLE_BASE, FLAGGED, D4))
# In the order of the matrix.
MATRIX_SAMPLE = tuple(c for c in MATRIX_CELLS if c in _SAMPLED)

# The follow-up cells of TASK31 are cells of its sample; the union is stated
# so that no cell is counted twice.
CLIENT_SAMPLE = merged(cases31.SAMPLE, followup31.CELLS, DOWNSTREAM_CELLS)
# The client table measures these; its cases are those of the cells, in the
# order of the sample.
CLIENT_SAMPLE_CASES = tuple(dict.fromkeys(split(c)[0]
                                          for c in CLIENT_SAMPLE))
MATRIX_SAMPLE_CASES = tuple(c for c in MATRIX_CASES
                            if any(split(x)[0] == c for x in MATRIX_SAMPLE))

# The boundary source lists the timing tables pin (timing_grid.Table
# `sources`; task37_grid.py). Rule: a timing table pins the boundary list of
# the table it derives from, the files a pin can bind, and its correctness
# does not depend on the list being the elaborated closure: identity
# accounting proves that every differing loaded file is attributed (design
# decision 19). The matrix shards pin TASK30's list less the deleted
# SimpTracking.{sig,sml} (the final candidate has neither, and nor does the
# baseline); the client shards, whose sample also holds the downstream cells,
# pin task31_cases.SOURCES. The identity tables need the exact elaborated
# closures and use the lists of task37_sources.py, which no timing table
# seals.
DELETED_SOURCES = ("src/simp/src/SimpTracking.sig",
                   "src/simp/src/SimpTracking.sml")
MATRIX_TIMING_SOURCES = tuple(p for p in cases30.SOURCES
                              if p not in DELETED_SOURCES)
CLIENT_TIMING_SOURCES = tuple(cases31.SOURCES)

# Batch seconds: the sub-microsecond operations take a longer batch, as in
# the tables they come from (task30_grid, task31_grid).
LONG_MATRIX = tuple(cases30.DELETIONS)
LONG_CLIENT = tuple(cases31.TRAVERSAL_SINGLETON)
