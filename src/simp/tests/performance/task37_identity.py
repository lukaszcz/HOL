#!/usr/bin/env python3
"""TASK37 gate: source identity of every client, matrix and downstream cell
of the final gate.

This is task31_identity_grid.py (read its docstring and the "Gate 1" section
of PROTOCOL.md) applied to three cell sets, with nothing of the method
changed: one fresh process per side through the real paired runner
(task31_snapshot.py), compared by task31_identity.py, the same pair, sample
and batch-second settings (task31_identity_grid.ID_*), the same refusals, the
same inventory, decisions, archives, ledger lines and exit statuses
(0 identical or attributed, 1 different, 2 not conclusive, 3 refused). The
records of a grid are exactly those of task31_identity_grid, with the same
keys, so that one reader reads them all: the grids differ in the cells they
list, in the seals of the code they were made by (this module is among them)
and in their table in the attempts ledger.

All three tables are judged by the committed reviewed table of the final
candidate, task37_attributed.json (the format of task31_attributed.json), and
by no other: the TASK31 table holds blobs of three files (ThmAttribute.sig,
ThmAttribute.sml and src/simp/src/Holmakefile) that moved after TASK31, so
task31_identity_grid cannot run a full grid at the final candidate. The
TASK31 module and its data are not edited. `--attributed FILE` names another
reviewed table in a diagnostic (`--only`) run only.

The tables (`--table`), whose cells are those of task37_cases.py and whose
sources are those of task37_sources.py (the one place each is defined):

  client       `task37-client-identity`: the cells of task31_cases (278), as
               TASK31's grid had them, with its INFEASIBLE rule (below).
  matrix       `task37-matrix-identity`: the 51 cases of TASK29 and TASK30
               (MatrixPerformance.sml) at every size of their size set: 306
               cells, the 162 of TASK29 and the 144 of TASK30. The runner
               takes the fixture from the cell (matrix_schema.get_case).
  downstream   `task37-downstream-identity`: downstream_arithmetic and
               downstream_reduce at 1, 10, 100, 1000 and 10000 and
               downstream_boss at 0 (11 cells), which the runner takes from
               ClientPerformance.sml (the workloads of `downstream`).

Nothing is edited in the sealed TASK31 module. Its functions read module
names (`cases`, `attribution`, `ENGINE`, `IDENTITY_TABLE`, `IDENTITY_CODE`,
`CODE_HISTORY`, `report`, `measure`); a command of this module runs them with
those names bound to the chosen table for the duration of the command
(`bound`), so the engine, the ledger and the replay are the TASK31 code
itself, with an engine (`Placed`) that keeps its evidence in the table's own
place. The binding is one at a time per process (a second, nested or
concurrent, is refused) and is undone whatever happens. A change to
task31_identity_grid.py is in the seals of this module's grids (IDENTITY_CODE
here extends that of TASK31 with this file, task37_cases.py,
task37_sources.py and task30_cases.py: the modules a decision or a cell set
derives from; a test keeps the import closure of this module sealed, or
reached only by a reviewed exempt edge); CODE_HISTORY is the place for
the earlier seals of a file once a grid recorded by this module outlives a
reviewed change to one.

Cells that exceed the process timeout. INFEASIBLE of a table is the set of
its cells that do not fit the 1800 s timeout; such a cell is not run and its
identity derives from the measured cells of its case by the rule of
task31_identity_grid.derived (the closure is the same in every measured cell
of the grid, and every other cell of the case was measured; its anchor is the
size-0 cell of its case). The client table has the 33 of TASK31
(task31_cases.INFEASIBLE, in task37_cases.INFEASIBLE); the matrix and
downstream tables have none: no cell of either has been shown to exceed the
timeout. A cell that does is added to its table here with the reason.

Evidence of a table (checkout-relative, `Placed`). The attempts ledger, the
build stamp of `prepare` and its log are below
`<checkout>/.agent-files/evidence/<table>-identity/` with <table> the
ledger name `task37-client-identity`, `task37-matrix-identity` or
`task37-downstream-identity`: `attempts.jsonl`, `build-stamp.json`,
`prepare.log`. TASK31's `.agent-files/evidence/task31/` is never read or
written. `prepare --table T` stamps the checkout for table T, so each
table is prepared (and its ledger kept) apart, in its own clone or, in one
checkout, one after the other. task37_dispose.py takes the ledger of each
table as `--identity-ledger KIND=FILE` (KIND client, matrix or downstream).

SOURCES. The sources of a table are the files its cells elaborate, which the
full grid requires exactly (`uncovered`, `unused_sources`; PROTOCOL.md): a
listed file no cell elaborates, or an elaborated file in no list, makes the
grid not conclusive. They are task37_sources.py's CLIENT (TASK31's elaborated
closure, which TASK31's identity grid used for the same 278 cells), MATRIX
and DOWNSTREAM (empty until derived). Only this module's grids seal
task37_sources.py; the timing shards do not (they pin the boundary lists of
task37_cases.py), so filling a list voids no pilot or counts file. To derive
a list run `identity --table T --only CELL` on one cell (any checkout),
print `sources --output DIR`, enter the list in task37_sources.py and commit
it alone, before the full identity grids. A full grid of a table with no
sources is refused with this procedure. The one-cell diagnostic of the
matrix is also the first time the matrix fixture's receipts go through
task31_identity.cell.

Parallel cells (`--jobs N`, default 1). With N > 1 the cells run N at a time
in threads of the one parent, which holds the lock and passes its descriptors
to every runner (`Pool`). A job has its own scratch directory and output
folder; the parent alone writes the archives, the inventory, the decisions
and the ledger, in the grid's cell order, so that the records equal those of
a `--jobs 1` run apart from timestamps and the attempt identifier. After a
failure the cells after the failed one in the grid's order do not start,
jobs already running are waited for (never killed: a runner keeps the lock
in a session of its own), the cells before the failed one run and are
recorded, the failed one is set aside and refused as in a serial run with
its real error, and `--resume` measures the rest. Infeasible cells and their
anchors are the grid's, unchanged. Paths: the scratch directories are
fresh `mkdtemp`s named `task37-identity-*` with `--jobs` > 1 (the same
prefix for every table; a serial run uses TASK31's own `task31-identity-*`),
and every other path is below the output or the checkout, so grids in other
checkouts or outputs share none.

TASK37 usage (the design is TASK_37_design.md, decisions 2 and 13):

  prepare           --table T   configure, build and stamp the checkout for
                    T (takes the lock)
  cells             print the cells of --table, one per line
  identity          --table T --output DIR --candidate COMMIT
                    --authorize-measurements [--only CELL ...] [--resume]
                    [--jobs N]
  identity-replay   --table T --output DIR [--ledger FILE]   (offline)
  sources           print the files the grid's cells elaborated
                    (--output DIR [--heap])

The three tables are run at the final candidate in the candidate's checkout
(or in one clone each, which share no path), each alone in its checkout.
"""
import argparse
import concurrent.futures as futures
import contextlib
import copy
import io
from pathlib import Path
import shutil
import sys
import tempfile
import threading
import types

sys.dont_write_bytecode = True
import acceptance as a
import task31_cases as cases31
import task31_identity as idt
import task31_grid as timing31
import task31_identity_grid as idg
import task37_cases as cases
import task37_sources as lists
import timing_grid as tg

THIS = "task37_identity.py"
# What this module adds to TASK31's seals: itself, the cell sets
# (task37_cases.py, which takes the matrix cases from task30_cases.py, so
# that is sealed too) and the source lists (task37_sources.py, which no
# timing table seals). task29a_grid.py and task31_followup.py, which
# task37_cases.py imports for the timing samples, are not sealed: no identity
# cell is derived from them (a test names the two exempt import edges).
EXTRA_CODE = (THIS, "task37_cases.py", "task37_sources.py",
              "task30_cases.py")
IDENTITY_CODE = idg.IDENTITY_CODE + EXTRA_CODE
# Per file of IDENTITY_CODE, the seals it had when a grid of this module was
# recorded, once it has changed since (see task31_identity_grid.CODE_HISTORY).
CODE_HISTORY = {}


class Table:
    """One cell set: its name in the attempts ledger, its cases, the cells
    that are not run, the files its cells elaborate and the constant of
    task37_sources.py those files are entered in."""

    def __init__(self, key, ledger, cases, sources=(), infeasible=(),
                 constant=""):
        self.key, self.ledger = key, ledger
        self.cases = tuple(cases)
        self.sources, self.infeasible = tuple(sources), tuple(infeasible)
        self.constant = constant

    def cells(self):
        """Every cell, in order: (case, size)."""
        return [cases.split(cell) for cell in cases.cells_of(self.cases)]

    def names(self):
        return list(cases.cells_of(self.cases))

    def view(self):
        """What task31_identity_grid reads from task31_cases."""
        a.require(set(self.infeasible) <= set(self.names()),
                  "infeasible cells that are no cell of the table")
        return types.SimpleNamespace(
            CASES=self.cases, INFEASIBLE=self.infeasible,
            SOURCES=self.sources, PROCESS_TIMEOUT=cases31.PROCESS_TIMEOUT)


def tables():
    """The tables: the cells and the cells not run are those of
    task37_cases.py, the sources those of task37_sources.py (each defined
    there once)."""
    return {
        "client": Table("client", "task37-client-identity",
                        cases.CLIENT_CASES, lists.CLIENT,
                        cases.INFEASIBLE, "CLIENT"),
        "matrix": Table("matrix", "task37-matrix-identity",
                        cases.MATRIX_CASES, lists.MATRIX,
                        constant="MATRIX"),
        "downstream": Table("downstream", "task37-downstream-identity",
                            cases.DOWNSTREAM_CASES, lists.DOWNSTREAM,
                            constant="DOWNSTREAM")}


def table_of(args):
    found = tables()
    a.require(args.table in found, "unknown table: %s" % args.table)
    return found[args.table]


def attribution(args, diagnostic):
    """The reviewed table of a command: task37_attributed.json, and its
    seal. `--attributed` names another file in a diagnostic (`--only`) only,
    as in task31_identity_grid.attribution, of which this is the TASK37
    form."""
    path = getattr(args, "attributed", None)
    a.require(path is None or diagnostic,
              "--attributed is for diagnostics (--only); a full grid and "
              "the disposition use the committed task37_attributed.json")
    return idg.attr.load(cases.REVIEWED_FILE if path is None
                         else Path(path))


class Placed(tg.Grid):
    """The engine of TASK31's table (task31_grid.TABLE: the same checkout,
    stamp and lock rules, the same `archive`) keeping its evidence in the
    directory of one TASK37 identity table instead of TASK31's. The
    ledger, the build stamp of `prepare` and its log are below
    `<checkout>/.agent-files/evidence/<table.ledger>/` (`attempts.jsonl`,
    `build-stamp.json`, `prepare.log`): TASK31's own
    `.agent-files/evidence/task31/` is never touched, so a checkout that
    holds TASK31's evidence keeps it, and the three tables, each in its
    own directory, share no path."""

    def __init__(self, table):
        own = copy.copy(timing31.TABLE)
        own.name = own.family = table.ledger
        super().__init__(own, doc=__doc__)
        self.place = table.ledger

    def ledger_path(self, repo):
        return (Path(repo).resolve() / ".agent-files" / "evidence" /
                self.place / "attempts.jsonl")


def engine_of(table):
    """The engine task31_identity_grid runs with for `table`."""
    return Placed(table)


# One binding at a time in a process: the names are those of a module.
BINDING = threading.Lock()


@contextlib.contextmanager
def bound(table, pool=None):
    """Run task31_identity_grid with the names it reads bound to `table`'s,
    and restore them after, whatever happens (an exception in the body or
    while binding, a failing `pool.close`). With a `pool`, its cells run by
    the pool (`Pool.measure`), which is closed at the end. The names belong
    to one module for all threads of the process, so a binding while another
    is in force (nested or from another thread) is refused, not silently
    mixed."""
    a.require(BINDING.acquire(blocking=False),
              "task31_identity_grid is already bound to a table (one "
              "command at a time in a process)")
    try:
        original = idg.report
        names = dict(cases=table.view(), attribution=attribution,
                     ENGINE=engine_of(table), IDENTITY_TABLE=table.ledger,
                     IDENTITY_CODE=IDENTITY_CODE, CODE_HISTORY=CODE_HISTORY,
                     report=lambda decisions: report(table, decisions,
                                                     original))
        if pool is not None:
            names["measure"] = pool.measure
        saved = {n: getattr(idg, n) for n in names}
        try:
            for name, value in names.items():
                setattr(idg, name, value)
            yield
        finally:
            try:
                if pool is not None:
                    pool.close()
            finally:
                for name, value in saved.items():
                    setattr(idg, name, value)
    finally:
        BINDING.release()


class Failure:
    """What a job that did not end well leaves: the error, and the archive
    of its cell if it was made (to be set aside as evidence of nothing)."""

    def __init__(self, error, archive, scratch):
        self.error, self.archive, self.scratch = error, archive, scratch


class Pool:
    """The cells of one `identity` command run `jobs` at a time.

    The parent (the thread that runs task31_identity_grid.identity) alone
    records: the cells are asked for in the grid's order, `measure` waits
    for the one asked for, moves its archive to the output, appends its run
    to the inventory, checkpoints and prints, as task31_identity_grid's
    `measure` does for one cell. The records are those of a `--jobs 1` run,
    in the same order, apart from timestamps and the attempt's identifier.

    A job is the first half of that `measure`: the runner of the cell in a
    scratch directory of its own (a fresh `mkdtemp`, named for this module,
    so that the jobs of this table and those of another grid, in another
    checkout or in this one, share no path) and the identity row, derived
    from the cell's folder; it touches neither the inventory nor the
    output. The lock was taken once by the parent, which passes its
    descriptors to every runner (acceptance.run_logged).

    A job that fails makes the jobs of the cells after it in the grid's
    order, that have not started, skip their cell; the cells before it
    still run, so that they are recorded and the failure is the first
    thing the parent meets in the grid's order: it raises that failure (the
    real error, with the failed cell's archive set aside), never the skip
    of an earlier cell. A job still running is waited for, not killed: the
    runner holds the lock in a session of its own, so killing the job's
    group would leave the runner behind. The cells that ended after the
    failed one are not recorded: a resumed run measures them again. Of two
    failures the earlier cell's is the one raised. `close` waits for every
    job and removes every scratch directory.
    """

    def __init__(self, jobs, prefix="task37-identity-"):
        a.require(isinstance(jobs, int) and jobs >= 1,
                  "--jobs needs a positive number")
        self.jobs, self.prefix = jobs, prefix
        self.stop = threading.Event()
        self.order = {}
        self.failed = None
        self.pending = {}
        self.executor = None
        self.scratches = []
        self.lock = threading.Lock()

    def scratch(self):
        path = Path(tempfile.mkdtemp(prefix=self.prefix))
        with self.lock:
            self.scratches.append(path)
        return path

    def job(self, args, name, inventory, fds):
        """One cell, run: a (folder-derived row, archive, files) result, or
        a Failure, or None for a cell skipped: closed before it started, or
        after the failure of an earlier cell of the grid's order."""
        with self.lock:
            after = self.failed is not None and \
                self.order.get(name, 0) > self.failed
        if self.stop.is_set() or after:
            return None
        print("IDENTITY %s" % name, flush=True)
        case, size = name.rsplit("-", 1)
        size = int(size)
        scratch = self.scratch()
        archive = None
        try:
            options = argparse.Namespace(
                repo=args.repo, baseline=args.baseline, pairs=idg.ID_PAIRS,
                samples=idg.ID_SAMPLES, batch_seconds=idg.ID_SECONDS,
                timeout=args.timeout)
            folder = scratch / name
            command = a.matrix_command(options, case, size, args.candidate,
                                       folder)
            command[1] = str(a.HERE / "task31_snapshot.py")
            log = scratch / (name + ".log")
            ran = idg.run_one(command, log, fds, None)
            failed = ran["exit"] != 0 or ran["timed_out"]
            if folder.is_dir():
                shutil.copy(log, folder / "runner.log")
            archive = scratch / (name + ".json.xz")
            files = idg.ENGINE.h.archive(folder, archive, scratch) \
                if folder.is_dir() else None
            why = idg.runner_failure(folder) \
                if failed or files is None else None
            a.require(not failed and files is not None,
                      "identity runner failed: " + name +
                      (": " + why if why else ""))
            row = idt.cell(folder, case, size, args.baseline,
                           args.candidate, idg.ID_SAMPLES,
                           inventory["attributed"]["table"])
            if not inventory["diagnostic"]:
                a.require(row["head"] == args.candidate and
                          not row["dirty"],
                          "the cell ran in another checkout than the "
                          "candidate's, or a dirty one: " + name)
        except BaseException as error:
            with self.lock:
                here = self.order.get(name, 0)
                self.failed = here if self.failed is None else min(
                    self.failed, here)
            return Failure(error, archive if archive is not None and
                           archive.exists() else None, scratch)
        return dict(row=row, archive=archive, files=files)

    def start(self, args, root, inventory, fds):
        recorded = {idg.name_of(r["case"], r["size"])
                    for r in inventory["runs"]}
        todo = [n for n in idg.feasible(inventory["expected"])
                if n not in recorded]
        self.order = {n: i for i, n in enumerate(todo)}
        self.executor = futures.ThreadPoolExecutor(
            max_workers=self.jobs, thread_name_prefix="identity")
        self.pending = {n: self.executor.submit(
            self.job, args, n, inventory, fds) for n in todo}

    def measure(self, args, case, size, root, inventory, fds):
        """The replacement of task31_identity_grid.measure."""
        name = idg.name_of(case, size)
        if self.executor is None:
            self.start(args, root, inventory, fds)
        a.require(name in self.pending, "a cell the pool was not given: " +
                  name)
        found = self.pending.pop(name).result()
        a.require(found is not None, "the cell was skipped (this is a "
                  "defect: only cells after a failed one are skipped, and "
                  "the failure is raised first): " + name)
        archive = root / (name + ".json.xz")
        if isinstance(found, Failure):
            if found.archive is not None:
                shutil.move(str(found.archive), str(archive))
                tg.set_aside(archive, "failed")
            raise found.error
        shutil.move(str(found["archive"]), str(archive))
        inventory["runs"].append(dict(
            case=case, size=size, archive=archive.name, seal=a.seal(archive),
            files=found["files"], row=found["row"]))
        tg.checkpoint(root / "inventory.json", inventory)
        print("END %s %s" % (name, found["row"]["status"]), flush=True)

    def close(self):
        """Stop what has not started, wait for what has, remove every
        scratch directory."""
        self.stop.set()
        try:
            if self.executor is not None:
                self.executor.shutdown(wait=True, cancel_futures=True)
        finally:
            for path in self.scratches:
                shutil.rmtree(path, ignore_errors=True)


def report(table, decisions, original):
    """The report of task31_identity_grid, under this table's name."""
    out = io.StringIO()
    with contextlib.redirect_stdout(out):
        original(decisions)
    text = out.getvalue().replace(
        "TASK31 identity:", "TASK37 %s identity:" % table.key, 1)
    print(text, end="")


def identity(args):
    table = table_of(args)
    a.require(args.only or table.sources,
              "the %s table has no sources yet: run one diagnostic cell "
              "with --only (any checkout), print `sources --output DIR`, "
              "and enter the list in task37_sources.%s, committed alone "
              "before the full grids (see this module's docstring)"
              % (table.key, table.constant))
    a.require(args.jobs >= 1, "--jobs needs a positive number")
    pool = Pool(args.jobs) if args.jobs > 1 else None
    with bound(table, pool):
        return idg.identity(args)


def prepare(args):
    """`prepare` of the table's own stamp and log (see `Placed`)."""
    with bound(table_of(args)):
        return idg.prepare(args)


def identity_replay(args):
    with bound(table_of(args)):
        return idg.identity_replay(args)


def listing(args):
    for name in table_of(args).names():
        print(name)
    return 0


def sources(args):
    return idg.sources(args)


def attempt_counts(table, path, candidate):
    """(identity attempts, those of the candidate) of a table in a
    ledger."""
    with bound(table):
        return idg.attempt_counts(path, candidate)


def parser():
    repo = a.HERE.parents[3]
    p = argparse.ArgumentParser(description=__doc__)
    sub = p.add_subparsers(dest="action", required=True)
    pick = dict(choices=sorted(tables()), required=True,
                help="the cell set: client (278 cells), matrix (306) or "
                "downstream (11)")

    build = sub.add_parser(
        "prepare", help="configure and build the checkout and stamp it "
        "for the measuring commands of the table")
    build.add_argument("--table", **pick)
    build.add_argument("--repo", type=Path, default=repo)
    build.add_argument("--timeout", type=int, default=tg.BUILD_TIMEOUT,
                       help="seconds each of the two commands, configure "
                       "and the build, may take")

    names = sub.add_parser("cells", help="the cells of a table")
    names.add_argument("--table", **pick)

    run = sub.add_parser("identity", help="every cell of a table")
    run.add_argument("--table", **pick)
    run.add_argument("--output", type=Path, required=True)
    run.add_argument("--baseline", default=a.BASE)
    run.add_argument("--candidate", required=True)
    run.add_argument("--only", action="append", metavar="CELL",
                     help="diagnostic subset in any checkout; never a "
                     "grid decision")
    run.add_argument("--resume", action="store_true")
    run.add_argument("--authorize-measurements", action="store_true")
    run.add_argument("--repo", type=Path, default=repo)
    run.add_argument("--timeout", type=int, default=1800)
    run.add_argument("--jobs", type=int, default=1, help="cells run at "
                     "once (the records are those of --jobs 1)")
    run.add_argument("--attributed", type=Path, help="the reviewed "
                     "table, if not task37_attributed.json (a diagnostic "
                     "run only)")

    again = sub.add_parser("identity-replay", help="re-derive the "
                           "decisions of a grid offline")
    again.add_argument("--table", **pick)
    again.add_argument("--output", type=Path, required=True)
    again.add_argument("--repo", type=Path, default=repo)
    again.add_argument("--attributed", type=Path, help="the reviewed "
                       "table a diagnostic grid was made with")
    again.add_argument("--ledger", type=Path, help="require that this "
                       "attempts ledger holds the opening of the grid")

    listed = sub.add_parser("sources", help="the files the cells "
                            "elaborated")
    listed.add_argument("--output", type=Path, required=True)
    listed.add_argument("--heap", action="store_true",
                        help="add the files of the initial heap")
    return p


HANDLERS = {"prepare": prepare, "cells": listing,
            "identity": identity, "identity-replay": identity_replay,
            "sources": sources}


def main(argv=None):
    """The status of the command, or `REFUSED` (3) with one line on the
    standard error for one that decided nothing (as task31_identity_grid's
    `main`, whose error wrapper this follows)."""
    with tg.terminating_as_interrupt():
        try:
            args = parser().parse_args(argv)
            return HANDLERS[args.action](args)
        except Exception as error:
            text = str(error)
            if not isinstance(error, ValueError):
                import traceback
                traceback.print_exc()
                text = "%s: %s" % (type(error).__name__, text)
            print("REFUSED: " + " ".join(text.split()), file=sys.stderr,
                  flush=True)
            return tg.REFUSED


if __name__ == "__main__":
    sys.exit(main())
