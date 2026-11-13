"""TASK37 identity source lists: the files the identity cells elaborate.

Only the identity tables (task37_identity.py) read and seal this module.
The timing tables do not: they pin the boundary lists of task37_cases.py
(MATRIX_TIMING_SOURCES, CLIENT_TIMING_SOURCES), so filling a list here
voids no pilot and no counts file (design decision 19 of TASK_37_design.md;
PROTOCOL.md, "TASK37 identity").

An identity grid needs the exact elaborated closure of its cells:
task31_identity_grid.decide calls a grid not conclusive when a file a cell
elaborated is in no list (`uncovered`) or a listed file is elaborated by no
cell (`unused_sources`, full grids). The lists are therefore derived, never
chosen: elaborated sets as the runs saw them, printed by `sources`.

  CLIENT      the 278 cells of task31_cases. TASK31's identity grid
              (task31_identity_grid.py, `cases.SOURCES` with `cases` =
              task31_cases) used task31_cases.SOURCES for these same cells
              (task31_cases.ELABORATED, sorted: the elaborated closure that
              grid measured), so it is the starting list, taken from there
              and not copied. The one-cell diagnostic of the client table
              is still run at the final candidate: it shows any file the
              final candidate elaborates that TASK31's closure lacked.
  MATRIX      the 306 matrix cells (TASK29 and TASK30 cases). No identity
              grid has seen them as such, so the list is `()` until it is
              derived (below).
  DOWNSTREAM  the 11 downstream cells. `()` until derived (below).

Deriving a list (a tooling commit of this file alone, before the full
identity grids; pilots do not depend on it):

  1. in any checkout at the final candidate, one diagnostic cell:
       task37_identity.py identity --table T --output DIR --candidate C
           --authorize-measurements --only CELL
     (the matrix's one cell is also the first time the matrix fixture's
     receipts go through task31_identity.cell);
  2. `task37_identity.py sources --output DIR` prints the files the cell's
     sides elaborated; the closure is expected to be the same in every cell
     of a table (the full grid checks it and every cell against the list:
     a file it finds elsewhere is `uncovered`, a listed file nothing
     elaborates is `unused_sources`, and either makes it not conclusive);
  3. enter the printed list below, review it, commit this file alone.

A full grid of a table whose list is empty is refused with this procedure.
"""
import sys

sys.dont_write_bytecode = True
import task31_cases as cases31

CLIENT = tuple(cases31.SOURCES)
MATRIX = ()
DOWNSTREAM = ()
